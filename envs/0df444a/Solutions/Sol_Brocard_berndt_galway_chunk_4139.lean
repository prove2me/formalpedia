-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4139
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:40:51.353184+00:00
-- url     : https://prove2.me/submissions/bee03ae9-004f-4ef4-98fa-fd16ac23c777

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 744244604 ≤ n < 744424460 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 744245854 1250 744244604 744244607
    0x150c110609070302280f031104090c0303050705070e010810050a0615140d0c050406121509090206040801020304080408152a0702130c0207090603050d2a050d090501 72
    0x94111186010798012140410042c2480d20582d6a0f505480b511804800038509600e41c9101c010783c001c400020411a0030800d10032003020001800030159814440c5510365101d0b00606000c0b448000d081100010301c58003400000d112850242c90b10306062239295942e0000103070740701000008202d4451425000c83e14410441c42504101e0b50303e1890700802d0502c0a105075000d02d413103542c4d0721007100304000140c1d600503140f03d4001000f5140d200d045d2200d00744440100b0702481c0055000f040380c60640103052840c1c0484002d001c866004001040e1030000d0b101044260165511441e607560000c070a010800c94000c0107802942c1c4074804882e0070b91443d001c140d1580c2d1090b621409115202c8003000c10703072100c05125000001d0840451480d14031241c2c045417070342c4910781480d0102680c03401d40444550f0705014117130047c4103c207000d0148600350b4990544a1880101540c2071010450012511140d060f15617001440b0305c80ca594889160307420196180c6150760a003500040700880041102d6 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 744247104 1250 744245854 744245863
    0x10911041206020c07080601180c050306090103080f090d140609030a08061306030506040f050705030d021b03070b030a020301030b0708091b06130b1201320a03150c11 73
    0x890103035654422032016a1101402503014444131507490254410100d0004010802c0740c0c020009c80c10401480d03a000e8111108440c0580202010408200240480c036a90040414150b030340180d01c07665034101c2d084031880c00b0300c90700c0416a0880350f4180403800f4081c0b420407000c044190f83d019103000703980b48040300e43c8a1050041c0403011480c100e000c1015030810009022410003c21000110030f603e80c1c9545160000c112001c4400d080000d03094007c00c0340900036980102020780040c210b50804007000794a8950100c1c075100f00d00441c0300e5001a0b540d04110000081850a061ba0340d42d00300184444041d40c02400252500710012001c07072040361140840501c00c3e840c20014200e00306503400184202144034019a5109c0c4040c081d101c0701c0b124501d43c500c0102640803046a441800c90201040172805a110702440500b03148000f00741200c1602d03e580030b420848000c110405a4070010703c0c5520503420282c4401c501c140003450841c020390141d0103025890326a40b50000260031280d50f00d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 744248354 1250 744247104 744247109
    0x3190c05070311220e013e0904020301030c0314210a030905030a0e01030e0307080a1209080d0c12110f0d02071e1407060503010608090a0210050301091104 68
    0x8560010750108007044440150340c280d56070050265940d0052180d920341c08800319121070000e0742d0740704100f02c1817120900c10b8a13440040500e0800c0950502c6480f144900410300140182d91020701000c80d1800034201202e111000041085481c0c0d61241042046040c080c0402c40300804801c0e1101b211880c0022102d1001510b006000d000c40c40c88554051503410080781c04043c1a201c9800000040c1d0a0026052640c610340e40d1291000006000405642d203108201019410170850329000c190100104c402c038400ca42056140c5010390819030000b050a890050910400414440c2000c540c42e00503ea0000603aa5103140300444c0c1004001120555440e5560881041000d034007194070810181c44079040303140006040c0603160b2501d480c42032494000c0d891040c0c2985001042100701c642d110b000340244001054040d042ca07501408910060280005000100001654030f030410031030051025805090909444903100c1d001c0c020350000e014002c1e507030341080164407031034940c401500c04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 744249604 1250 744248354 744248363
    0xa061a01170c0a050a1107031b05060301081c09120c1701290a090e0102070c12080915070f232b05090306010803031902040302010c0209060102010e0f03190c 69
    0x26003c201d040c1580d0b0340d80001c03180d209014042001e1060988203100c010b000314000ca071403100d90f502c11010315140d9041a080544540f800b4001800240c5001500d05110350080d11036100300c08501c0c43c190340c0440703030740e101200710003d9a104a003040401b080c0074044640449445000e0383c0d002d0780722400ea03041e0070300c0b0842c8414041007400348030021589600c1c0b2a4400303051580700b1602d0340c0704003003956404408410b55a400003420410403661186510050101c4080200c1c0741281354ae501031701c0c1c0304100d50240f080d8882c004410100481c84216031810381c1c4407840110448143c94140d00c17601c00303a910000700c50f80080c0310300408880030851440501c000304030310794070350445070b0711703c4480b100c0940c00d000304882070010401a4404228507400b030000400110780303900d065a451442070408103005100781307005210800051360843d25072031280e5412100111160f80e4100102c0c0100700500c0304424611400c240c01d000200044024441d040d5407c5d94640300350070b40481960300d14905c001c01407 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 744250854 1250 744249604 744249607
    0x9060c09060e130e030c03070b011e0b03061507140f210c19051501051507020409052503150c02070e043008090706120e0a061a01170c 59
    0x40c10b25000c04101c03000609008001070300140744c491946543c000003020003640c3d00020f42c0209100c40c5103841c90040c800510240001e0114541081924072203204584410a010003c640c0b0350b56141030440d031120006001a81350002821b2580f070102c1c0101820050303015512001d14111030104606c9240894444104501810090307005c07200d41c8110281304040c003403030b404140c4440c2e003022490505405000204800300e020b003004c1502e00010307031240e40300710f4000904c181d2116040040da20855012200064002d546007000c5007000b40190712010503070040c035101203034804688610350649001e0a0039618074021580c0c0c1404480720001c014025034000706040280c89004070032541c2c0a0b00c10300803d6001c05241500c941a903014070780e0200d4002018001c1800c00e0341c48038886038040358040045c0703e181d103820703130241801403024034000e801601c902400c916588208240005d442d4030000412501642d01c079507440074401e00000900080507000307006070031607054401c43c0c003030070b064246075 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 744252104 1250 744250854 744250877
    0x40819171302150d021c02040317030403030b090109050702010c020a02090a050402150a0306140123032d0f07090317070c09050a06030c0503010905030904020903150a09060c0906 78
    0x30324100d041c425040b81c0c00b05803076504a9001c03001d0300141c07444066000b005600c2d02c2181400b0311903092024a5890098814001040401c814007c0241c00b01204a2490354a88036814100d01a150a504050b0030018540001416041c01e520852280f469507000f00094180d8000898440700307000f001a510003042800308028a9060784500d80051008280c40641400600400740517080314aa4001084d52140200b00c00c1404075158000c40c142443c108001c00440403100c004131240300002e1404207000b100259841e10513040035080c0880142883c2900d00d11008005132400c802c0b201300702030403048008038200030b004540030410341c0d41c05200209442c40c24071000b40e5a80245030142c650014090001520307081d50b00c0380b00e004803580350b0007040301400d6081140b107450259000380d0084e1f240c00d00f42c90125602100340d07818038070102c41c056a5900402d0000e8501a002e6100d1300d403103c000c6043c48110503041c0c5c4800d2550340301c0d5006000341c50f4064800c0d2000c01d11441043c011175001d4004 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 744253354 1250 744252104 744252121
    0x16030e0d1d0f0d060b0102070b030f040303050c0d111e0403050a0f020609040f050610090b0a0c080405310921121503020307140a03081303060504081917 67
    0x7500e44001c0d0071020300c403040400041c10090402815a021135544060b03400e556810700c0140040c15810114a195040180740b55003201c900402c007808169440c0c01090742608480e0450b1000c085409007800f03c014001c17a00e00850340080d00d24083d094280b0601c1451001103800d480480760040080d1400e541d0a46175034441d0350740a40126407020003044503c1c5180e03141d124480c03a044441d000054145000800c0c80008100c4000b180181705454608021045011044a003000b4961900081c044454503000301d00e8061074001e1940318540c880a103140c04041020843e01e01c0d104c1502d40c01c80b5070303a1088101214041c65014042640d012100c441001444884d03419101ca00d00e004803018000603d2103088850050111140a000005c20000c0d803800300800c03000b5080640480d4514490800050202030581c0300040c40c20a001c03c0d0001707901100051a002075400881c01e00a0340303494506505070360701c504280782c003421901c000c004501d80f142480d1071156804942d140741c607071961a01c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 744254604 1250 744253354 744253397
    0x3020303091e04050c0c25050f0a0510020303061e060301050f01050d0603030f021005010e040f0c030c080d11010b220605030312060406061103070602030c090916030e0d 74
    0x2040000c28111a034069203c0d19244621489019060b6106840302007541c0c040c0c1c2001c801c900520386a80242103000c0841810f07162043c00c42e081100d0210205030300d80081400c80d280c5600045d400b4440300c00c00d071900c07500031000394401c80017240c0407001d0300b03019003034002051f944941c0b0b6a00240c0900040c0000d042142e24021106414100f0b14100100d980c0c00100343c81990300101d0010b00d09164151a840d01003040c0840800445001d2100307605102d29291900342c010710103070080084140d00d105100403e030b169070295801c006e0f0003c400e921191059515a1114501c0001071115440d4031042c1d1810300c20aa070115004220540b2040f851605a40c60701420b00c401c41c0d455503954000610341d80400080000c0380b4072a600c102c0500e401c01c204400c5510316070050b424019000400100984084121110b05502040040e140d456030056110740d401550304240d0400d02c0802407081d800006d50313401043e4402ca81d01405801001d4000988525031507203030001240c00702d040218595039002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 744255854 1250 744254604 744254629
    0x7080408070b220501060f090b060913020f0d061e1d1018090605060315040b040317040b040615050102070501030e101d0d140d0e010e060c0d0e070302030309 69
    0x440030b0410000c0340030103490f4411803080403501d41e990769804015065946251100070700c0d031110b007008281c204c8004200f00c1d20541251a00c5280c0c03d00841e8070007078040d41596080e44041d40c3d0386466001802c1020010805070003a20f8000440c0d45c1014039480d1342d0f45900d001e640424030b8200076000039050143c01080f02400c1104240d000c8240450400320320b80011300f440c19015804200c0e04000e007840c2c012101d019141e0b50081d04003810801c604401100c09942003540886000029566030504031100109003030800c201c1c4030302030b0601050100318a40320b03002c0c1e0b00034070702000684144400800d1480b1680301d4079004d0303040100200b103290b0095100c0c10360314034044140c1e9100102c1540803c102c4a032803848085408054907507451912041101e01d080c20210b0920303010981700300301410310380d020710b070540c4042988400030aa10b00b07800390050b0410400103012180c1c0750500640354595500030114182c000383c502509110601d80c0010030008413134000d40a07500e400c03000018450542e0710709 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 744257104 1250 744255854 744255871
    0x60b090609100e10050a09080304060806060a0e04140402040b040c0e060a02011b03020c101404020f0316080303070f020106030b130c0f03030c02010813111212180907080408070b 78
    0x9a654080f640314282c0c401184102951030b55568001000050000041908030000591090105000c11030700801800e4100c90100c5c3c10315100d83c414141214285000380042d41c0182c1042415204241d404c0c01080c01244211028080196007200380070440d016941164002103c101009106041c600024401c10201e0320020400a00c0d00403419010b8040005240c00203a0000b07400070001018440214200000c0c4011711004201160800007000301600c0a17205528150300125a541c00b0041162032414944c050603042750b444c00c11075100d40040b10a8030106040b06890140c0c0f038410300c40c41c003e503980300c202900c0ea600da60b00150300d030001003541100c03001b2003c070001c5640002c04c580c460045100390f03600d0107008131910004000d01c10103040000e1000c03080c0180d10000e10404000114043c061380e6050100105049039440c10b0301100b034041c5442c0f80066030242d0385480000c10801014141d8161001d5250410200c03003c690803980904403490600402c070021b441c2028050300107052 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 744258354 1250 744257104 744257117
    0x20315060d090b252c0a152a0f0f0305041e1d0f06040b04061802040f050a0e04060b0d0c12200102071802210703060b09060910 56
    0x141e030795010b40041c29102a404102e0f0503880b801441c07542000b001d1454040d1401442e1805055040e0110710901100c407401980941100344554542054003401015800c001e03c003520082c1002402c403401420b40700003c601c0031030301503c02c03510b40070302415600e274007519074044045261202c1100102d2030380e0032003c005041200240d40070b00c04407881078210b0680381c001758940c43c1041e0b80300903440d0304100c00c03100a1000204170f440c488140940e5401a000e45002c11307040070000004008080681146804064041c004540562158058000c0d50009800340300195180e8040110b189000d01c40c16042d04805400500011000d412141079407001030041a80484250348041600540740c100301310000b0070f0b80c6240f00340f040704c0c546c1900c101c90710000d81c0c20704403890b030000351078180500900340b99450607017260150201d030f941165840e03014008002d08151540b00c1c6101102025500000068140900800c1c1c1c240706104a8500d0180200301915200c011820311620b807024100c0802031010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 744259604 1250 744258354 744258371
    0xc040b060c06090607020f0c0f0d061b020106031e0b220b180105070e03030901051b06070e090709050f0d030e1203041d04080307081b040b070c0603020315060d 70
    0x20800046014480620140207103280c840b1780249800340a500c2401154040d1190422035145c0041c0c804a900c401e8403001c01c50082410418098000c0412900a980c4a0051510480d0f419800303401a40c0c824502c1c00d0203003044244801f0014440c02c00505140e205002192895030039014540c480550000c1c400c100590988407200c402c142142e034a0100041035222481701c1000388500c6a100b041410803050414110010a07a2802449100b0b0706010b000107540f04d440d903041600405640d000c20813520540380c0030000825108208960f2805105014081900c250080c200541510006012541c10f041200c00f000500e207040c99056061288126070710940d51245005503841f0322a040003190b80c5c034508850a9600c2c400260740c0041460340c00e0070301c4001103a12003101e805c0740d200e00e08809076031100b0b0180c10310352000c0364224001c1003000600281000d0482c000d0305a0600441c22001d040741d403648150140d103c121404200058110244a081d1801d8405090011590f050008402c01e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 744260854 1250 744259604 744259627
    0x120a081902161e083013180c0207150e06160c0e0a1413060b030f0d0201060b040605190e040f0b040c030b01020a060908091e0f010201020c0c040b06 65
    0x41941100d50456200d0051070540034030108083d000789030403c000d10604114003c01004102e60040c0031300250190504406400c58a5041d10884801840c8071500c03240c2d01c0e070880d0780b4071a88041d906400d80c2407104103034145002040d9031084485e03020120844120782d6004880000d11354404d42c2e4840d1040c040ea1a006603005c0150391240d11442d0701c02c5500d0f0070180c40441c180300050400400074202078001c02600d408085a980101c100708080c01118460726061000d003030a00c04450701032003584481400c88000184241c44442c103500200100c549507425186144503a0055401044e020000502032500c0111181c11f0403080d4904542d2a44080d00040c3c15901d0182500203400e4491140e807019107498414049506c1003420101300f45101c040020751120030350200900303010766400303164007404541002c40340c5040c4010500710002c66510a0b2500b03d80b074108806018025074190100154014400ca0347d248429200400300e4004603010800036200f40c480f0150041018020081e409 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 744262104 1250 744260854 744260893
    0x506130501060b0a2003090105091201110c060f07020106150f1106070504140901030b0f04050f01090b0403031401050a1413060b04060f0503100303050a031d0705120a081902 76
    0x2240703907101d2201c5d00c603500c0032854a01c02106841041d4200b0800c0c03d6140e03030080c2c00c4a4500c003094901e843c082c00305000c100e00414010400a40d520710003d014145048007054452007070152403610032040e1283c020480c00c817201802640310a00524840040701070099040b04000507851030188140b409920b0214100300083d0b41d4100411804a414071040b9018028241351800c10340302c4d05030075031450315804023a460280001449079660703408902401b40511040740700040c00b900900140c40c2c5440d20008a806c2100c082d00000d01d40a0005c509100c0e030b41c01207048a02c002c1c0312039610750408660714190125414040d500c0b90003113840020010880c01110018180c44140c16159441e140000d45406080c0810500704801042040443c164100701030b008d59030189807081e250100d6107401d1303000700390005060f05040e0080000055814001410006480c400e03201c01041c18207400e176107030b40c6072030020b00140800b400b440600d00d15a00444280720302c0140c2e00c100d580d80c910500150203d03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 744263354 1250 744262104 744262117
    0x5121b030a0e011d100608010218010e01020a0602030705120603010c1202090118030b0103050c15070b040f0204051906230f0d0c03210e031c0e03030f0d14040506130501060b 76
    0x280c20030801e0417509601481054024100c41e0003c0d45024184e90600340701c180704126880c140600c1c070100500c181d10030055141075590000342103689003498900640300d90488100d06c2441040c28001461505040c010b40c107000540351290500c1c030040c0d41c40e42002e50030900d10241048010041c0c85403140800114400860081141040550450910300e04103010f407801e650143c210708800d40c018031040000c60b080076810110501254840d403411600c09515260041d520604103000d02c40030030b8007500510521290450b0421800d996200908000250754075480f0440d44000c2e1840c0882c01c01c07038100502114000c2450b5001c0c282c542d115484c0d402d49420035124547c0b6400c0c00c1c3c0c41400741740c50000b10046c00b410280c2d001c0140a0019644070080c080d41c480b0009182d0400703101d64040d005404542c1c40c02010341e41c84804e56840c0700042d4004880202c10107081600c0854101e8200300d040f80180d8001014003015510704070032142c000340d920320403511590b81c0d02c0e0000f1910040c4018081 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 744264604 1250 744263354 744263411
    0x60f1003090204180f0605040c1802130614090d060612051c020a0f030f0e0604080c040b09100312050f0706060e310f020405010605121b030a0e01 64
    0x10645000d005100c100c0300309003c034648640b480c84c401c01c04200701c0e2045160b0a0f42c40b213000700d01c83d41c0e1841c0c440c9204031154400c0301e804090084d0b16184845d03980203002011148200821a10303610b54040350420f6004034080341c0d4074001c0090314201e04168000c40b1104c0c0c01000c01042c000d40d42d12003042d0002c08000705135010b42010b2603d86940d44000240121528207100070901c401c4a603c41180300514500014107110355142076054885c025000c02c0140e0400030700303143c5c0b540d43e01d07000c060300c3c1d594101342c2c503224900d06101079510f45040d50081d0b010b010401001545c03642599103181c0000395404110302408428401031244052000c000c1122038403420001c50562f1030015180e0f2804006840c0000c108031480880400b0082c2c011400f180030340060491454101c9810001d061880e6440c0183d0000e051500202e0003e030803400400313402ca0380c10f43c04006941e4410701040150032641d09150f00e00c5040010440041282c2c0007400c50140c8500001100d141803070304080d00a080010268 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 744265854 1250 744264604 744264611
    0x504032010031a01030e010b1818012c10060b040e0c0924041a0307020d18050f0a0b070308070807022b020f1e0709020901050a0305060f1003 62
    0x801401d2604801c031981039203080c10b008109a00300181c0d08240410786013810076070340340c50200340d1308001d410004031400040c01440052804061078000b642c0c00300d60080b038074034140c4240340414a0520501926100c00044000b0742403041405105101e41c405000105125841140c0c8000c03010303201d880010803481c1403003507659140000820304030500505c62185810280508106600e54050589030a25001c07072103c1d211078582140801070180ba00325100b44801d41c500301c41d85900f118021402059541c0860300c2d003284000d41102c020100e0680200136001100d0208003a081001c14549100c000608404001d41c54039040c00c800d4001d80410b400040c611000e1009107500003078000c1e0088940e202810b14034040c5031800000e484001010321718200d0700c982c1b803840b8620074020005194044005d89108003010101025441c0b04104021580c0c05002000a810b848a1007200c41d03098042e103c1c1c030f0800511100039001008002c0c10303245c000403a60741c103c1003540da030680b00300100740303685000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 744267104 1250 744265854 744265913
    0xf010b0f06030408090420130e060604030201090b03071b211409012106030f1106120a09030e150d060e0108060c032a0a020f210a050403 60
    0x42058000d84400d402890304000380004074000c20115030ba00a001d40b8085000a0b0b16160a0a2202500603190b454140401c800b00d00c07100c1400054111260003000c04003e4484008101d01031145200080c08611814005c100c07008914024540c044042d0a0a400420105086000c0f07a0500b400403101d00c0451800c4034480825407150803442103086c54003d00301140070300b40d200c03544030301280641031110b4082e2254440d90302c42e9540851685007881446501d80e2803904100d001d9202000703d60410003c0384034911814410142c515440a03c80510711326200c5014510041c148948142c040101c032540800c103032348a1110003a544035031841c86642d0b500308858508221034030360700120100740340000108003265001400c0c0d5004110315000559985400e20b2948500c20303a6050030030550304c1450f1480f8040140000f0b07105040598080e07610810000c41e00c02e450340180700902c10394001100f44407444004200290005205a041851825880b500c60444001c03814130210507000711040c94 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 744268354 1250 744267104 744267109
    0x71718210a030c0b070e0a06030b0f0d0c0303080705070305070f050f120a030c1407080a17070c0201080619060e030f010e01050105030708060714090406120308061f020a230f010b 78
    0x81503221920307241405031031001e640000c0e4020100c0c40344102705612840524400da5481c000b0850300c0c1307401840b144198040d40b5010104041c544000d40201d800c0f0000a5410340c05103007101c100503410784d02d0314603001c5a540c41092141c3d10160a0762240b080700001099000b08200340182017100151483d190550f017100203080d607501d072981d241001440e500ca4440d049110050326107055000700f01a8581222240c102e44414002d2108a41000400305010180d03030004100480f40f8000c2e80d0316445681c5070000d000c0070031300404c030904104403841010003e55100e40c0205d80003c00040980f6204070b45c4880c1c890948110010355003260755140010001c41c81c0401001c0014049200680401e1070805005040844101103072100c101c400140d5003810b541ea80d0101000c1c101110f5403002c44041c5050090011804680c11030260004040c444032a80075110440b5100703075036500414260030135030b85001d00364400101003404004108000b1840481c14454046480c500d0000050484500c408 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 744269604 1250 744268354 744268373
    0x82205030c03062e090b13020f09041e0603140d0c0506160e0928020f0711060c0105090f0714090610111002071718210a030c 55
    0x1150303229034004011807116440104801d03070301480d80d070030000d9000000c00040d002c402c50790700782070040c07152504040b07070b991003d500c031590005c804d0351150a0818801c503014101e00c00ca0f00d514030241810300480c110f6160540004401c2c00724200c2003a10180544905030503510a5001110814200108140c265100300528078601059185c030881d89e00c0d04c0c1d114152100c034042c0c100c19131510300308480311a03a8011500703001050805880c1c004070740b81450001110301c245084004000300014003601843306d9900036038150a402c1094240303405010b64868500801006080c0d070004020311404107102001e115562040c3c0c0944060010861040003071400c10f005e9401107920030301c41701d000000c2c3e0384030400c2483d800391054038504060b204071881515452030306180d9072054454080700f4855607150b40c0180a44520450740c10304080107920002c0e07118000c881001e841c40054600d1020107160094080090f40584c10340b0816640c111a06141008a86078060f030101b50101c0e001c4041102498 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 744270854 1250 744269604 744269609
    0x102010e01090c1a04030f0b0711070509130c03082802010c09270c021f0e120304080f0a08040b0a05040506060402030a0e07030c1a03131506030822 65
    0xc00801c5141031550714244401007602540b519404681c0032400e81c460150700321405590807821a03c4229641c1c40c0079407610070202d50750700010b01100300e003000404000400304180c5400070b20b04861982d441015206045101c0810f4515960380040000403507403000c0100040e840401110341000a2400c4060112240c4001c060031a0700d000140000a5071008211055605400100074007920a411413082c4840c2c09150501c03d0b031a290f4003940d8a500003030f0441038408004621110030305452041c5044501031014001250400c540401c4c892000c44021580244a00f0b002030400750510b0f80c01500303420503074001c000f00f003e02d0f0901c0300b4440708140c3c44e98401c80c0d0318070174004c5150603654291518406031841e801b8680200125640e0a526042000140d01322011520402d41e01e0801e4400125140304650003400440c1301c08410500143c100d078495624030303071960580b0366540d40b5031400c541c030400456041c41d651000030002410b880d0013011580482440490b0807100303070a05000b40b100c1035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 744272104 1250 744270854 744270881
    0x51f030c09080303010302130207020907090515130e0c0c0a0f0c0909081b0309100507020a0e0c0f0c0304050402030a05041b1a0702030c06030106120e1f18060f0b010201 74
    0x6040402c842040001141d0640340d0555490041d0001008103a02070300690600035402074290040110166101804d01c0c101c40c0d0440e03070000c00e035103100020303002d42c89020700101a804031540213010242602c0c0080d50840550b000307492030920044e070b10b107040048046045440c1007a880101003802030010044001c0c01c446e820402065900d42d403002814400d03e0810200e04c0140c0342c500d01880403d00c01c1c0c880c02113000c1c103281415400300c1001425139000f00400ca00c1040c4900c0c02082c03a007140240e080c8221000032030380340350540b00c001c0000d280c0c000030041c2c1c0d401c0c03000300030100744dc1c0c80e140061400390b154040089800d00702450415541c600400c020300300b00ca10004100a59103003005469202e420004078169034548500103c1d080c00350341c1c84000e410600c00400080c0f15039108140712042c1d80100420400d402c1941601505d94614058843e11040301c0b00322644c403d80f042d4041c2c10802e11604080001d0103059072080c09545c40b40340e500c524195a4440000256020f004445464906 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 744273354 1250 744272104 744272117
    0x50d0b01060810271e020c060c030f0c07080c1902130506030d0c06140915160e060a0e0909010b0112060b03041b09150311030606100e0604051f030c 65
    0x28400e440c11100010240d1a04000b00b49683d00924001076001c8001480345829403591998005c11220195010008200c050310501e0000341a000310141564055600e2007500c03140c07a11034080b0709071a5040000203880080c0b003040340000c10541008190071040da000da0081e6038290b01d0040001d50840061041401414071081118a5401068110080406007828010303407140d4103102c0000c0a24036012000c0071001b0081c006182c0d400604201d418030004240040c0790fa901c8a140004c010707030780d01480421201c064030081494104c0142010214a24250841d0031000c0000b60001d02c3c20703104d1542d86c0c1d64be000c02616959000303e5400c03c0b031841e004140104ca1038134440d90101d00c001080038100420800d14810b0852901b00d11a000b032100e50710502448401040080d0a000d40c1e00c021500ca07108001c520100303040225100d40306810080481d94408054881618800781e0480025800101040b000c41c050360b451440c940e103c4d4880400306081e180030070b0701030300b25804100380c0c40c00e1211 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 744274604 1250 744273354 744273359
    0x1060c030825032f0d0e030c07030222050f0f1e01180204030803010e09100e06041407120602130e06101211040306050f0604020a090e060307050d0b01060810 69
    0x100580304030500a080c5000180c4480101d071041500c02814085181109810b0481009000d80b401030240b810b5045c0701000811200d0403030981d60702c1744e41407500e00c54010002c2000907251809011500000c584200c000c03040980d4029011500122440d0b00d03c0c810500a01a0a2850260490340480041d5150302907001c0040413062032401480307903141c04200d40080c3c03904c003603e6405403030003964042003254913561030341620308490a080b1891410380c03049441902d80031015000d520b0006003a000544200d4545071201100010b50a03003c2c0b140b4850f105002a980b11600c1e0713409581c0303024400060b1100390a1302035480c1400a980f2079010714041600307025860355462102494004d20b0b04203043d00300c10400180d40905062081c0030341d851004034000050202682245205003a800c00f03081243d56501e0400c012030040c1c98049001031382046091046102c041d102a4200360000e04864000d0b540c0c50000b461410b12840c211a1148100c004210142c0c0004d0b5058001800f01c100030406070 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 744275854 1250 744274604 744274651
    0xb01030c090e0c0c160315050c030c030603010e06090a030e10021f15150e01081b0a0302040302040207030c120503094b1615080c0c030301060c0308 65
    0x818020b20040e0502880400d042114800896940800c04801e0383c2c840c1180005c1074040642c0c9201c00d4540c0744010a003e034544480e0f10a81e40f05004901d41c042c1541c950320301d6205942c000400e019010f6582d030211000c0b04204014036846202420001c040741900f80c50006c0c03400c00c49601d800c3c010a04040700b28100794010420b4a50000310300c3c00d030511608680240c6c40a4620102c0070b040c401d0b1742000200b503048110b013802005110907221080207101c20001140c84031004c40300c465144400e0442070300c220b80300d04000d10140c0d03d90315000d81400e2b240d80000b82260301004045000c0b410aa0401d000c22024103a51a0040d4281c10500c2c190714142d884141c68a1030b600c0e0b081d1901100d0400d061031a80c0301c483c3c00001091200209001020703138042c002c1e188445850f24031241c810400c1c0781c4a0301d05007104100540d0394400c81c0e000b984545070001e07950f1080240c1950010344e018000f6000000c0d04101a500802d482c3d5510002c090503414094010200508100310210089407285510b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 744277104 1250 744275854 744275867
    0x90a14030a080f0409050405060a0c020c0f06160b0c0d0e0a030203160c0e091605190918020612010e070e03030702120c03032b09031d041103070507060b01030c 70
    0x1a5000303030025640d14550000f11aa0784999045142400d2400c01403106228002407924410021810100141c1400c828140d83d98209030000076440b194001d03440703041d07040c41c0014080400c0041c04114905220781d03a22040504101c81c4501d25420108419061640c280190020200303200003404210701c0e0790318025204d10513440300f041694540e43e0311030100451a02a2401003102203a00d140e24145408415126460448184641340c44440c01140d1803501c406040b40c030b414100954407105140ca82e01d400035211305407450f40b8415a840c003400168460500501c0c0d24852080032030540e604040c081880c0544c06000401042645208407030715440000440d100b00707404030b541d00600030b2a40342040c60030106400e225018003000c60103030382e87c14040351a04401110040304200c07030304c081c401210881c1c880440c080c000500c030b01c0811205010f90087c1c0c003810707080038102107280008a4000700042d4400e40721400040e5000607400180b00980c40344100c003c2003403905106075003130400000c14130b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 744278354 1250 744277104 744277123
    0x50102070311180711010b0a05010e01200a03020d031b0503010e10080f0d08060306090a0311120f030603010506010e0a170f07060c021c0302030301090914060c090a1403 74
    0x20503845898062481ea00c0c9183c0390444011040c10700c1c91480c2034080207000c04120041e082d095820a05500c4252514a0f00c4005031003040e524400c0a00303d004c011100315061000c400f031440010040307501c000006200114210740660024a040c4038103031030003401c8071046031808200c0d07890304500c0120203500c076084030b044908007113000051741c40304001100002c0c602d41c80101d50f4882c402c00714104040100303500520340307640d031120800c03aa41c60041c59126101264641c44ca0341221502c040080d00545800403075420a030100c8403000301e1080e400e00642c1c03000141c05049400070003017107030600d000d001d2658040401c0c40c184156440000104038000210f000f0010040050401c1380c41d42c9108002170a041e04404088030900d0b940e80d00b0192100e606010300342d0156402c0129500079a000c4001c41301041d6040d0700031071a5a180001c948014400b010080320302c01d45100e01d402e078080c070801080d40604420541940e4820803c0104108800131f94824580112012000c0783c160350046000302d503 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 744279604 1250 744278354 744278363
    0x32001140c0a081c06090e0f190201260c040e130f12020c1302120601050a17370c020d020709020f07020d14060f091902060f040e100b040501020703 65
    0x2c41301126103510f4a10144040108095882d050b80042c0a2803e6040340c0da56081e08425078542c8103841407003a449480f248560b800040c3e880385c0d4500107510948038000c51101c83e103448806c045d43e550b00003000e0401a2011117040c00082400c8c016101c8011520740c1021442004040520030f0f80e0320701001c0f0311212000f404401d441c1110041003070092046003260304000b0701180300d40050b5000b01e80203400c50b4a40303035144404003000441c1e0b0350042040700c07032400365501c413101071901c203c003000c407680001440360041c0f03084200c0e01d01c1100005204815070021071740c802d5001c954502210f0302284c0c03980c1080011988800c40902000740c02007400380656031904400b580d00d2401d07002a10f098811a50029000354011303102034140140312400d20a0b40c5c42200903075007070740c40d4000d4141c40c450f0240ca04915541004000500c0c5e80d608910300380c42c50384090311860401c5a921500440f0b44c01ca54000c6003489200010460783c01207880705800641400800d0714101030038040000e59441282c0402803 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 744280854 1250 744279604 744279607
    0x50709140f1e06070c030506070e01050324040903030c17240d0f0503130501030b06030a020714060109091b0303210b030d0e010e0f031f06032001140c0a08 68
    0x200b081c0200b100010401c1c405041c00e983e5002526040301d8a000500c4240d400f8043da0010880440c402e00c015401d45105039030700341c219220311140d0142080c142031419440d008596000303849407114050080c08a000e5180020904c10a84000d8640740e42003e1114400d54064108001704070710f20a000e46260a10a410001041c000c011440ca02d0080030082d0007100c411004000f0000000f004151920311407120000c0507a84500540070365150102080d4803260a01c0001d0190965a015103040741c050303100800035005044901341086002e8019905481d2209070400c10700005205031103004420904000d031480c51070700c0c02810b084d00400d0901d40301511031529200c590041e004803070052001415107400703400c0000060651090303030043d1070200300c0d01c0300d40440620b08031504007860200a8054280141c003120380c4059443e1210000300303131560340c200100c003041552036a1303d4441c500d850060324403048000050071b24079980300080203144c1c0070040c080c10100003007103160486500c109040e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 744282104 1250 744280854 744280879
    0x604091e031b05031b03070f061e150812090906090402031614090a1407140c0106090e0610030f080d020415020a150e0307020f0d1203050709140f 64
    0x403182c2c004281d850820702c00b580d40c40726061080100c010f22a03c10788501450420640d02500c4ea1240101107002d00b080d400340454001040d00758100854844452200543c90001e01094604403000380702d0701c00180f0a0140300b0310130607000f081544020b62141c103407030b0b0a00c0102000240311100040a2500510255001c1030464a08000d412101440c104144418649500400351030003800c0c07034240e2040c443e00c070101c0d00c24401c40c071640140b4041209030540950b11070340280d800142468020704840b80402c2120082e41080c4113030800f03080d074050301040c0007480c0d44030380b494414054000c0170001d1005d03000300005401903002d680c0540d800080b040e1180003074017810000740140d503c180741c4203024000b0701c403200d17902165030344c030452040000c0d0541d1701400c064a0200c4d4000702803c400d03903000308a00005450210f03110030810400400e044034000030b42e0748409855405031020b01c04070b0340725018400f040360811900000741001512601c040a107020000d01c0c0e040307407803400c0d40c020500140f22 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 744283354 1250 744282104 744282107
    0xc030709110d0e01021605010b01180303020318030c040606020a051204080d0e010c06021206010f030501140f04020409090507090b19061808070609030311030313020613090f02030f0604091e03 84
    0x46c0c88680f000110303050824119030814034060140e01c802030340001d00c03c414441001800e01603850079207030158019410251140c640381d4449500382c50565042c49440b82e00c28855803607004040203000c3d20390142405110314030740785107450480ca40c501e00703c0328103100a002d10170001511000400c41440c05044000c0c412005175022080c00001511440c0002202d03004c072110461802d01072107003079a902516a010860860840d06c00b8003c0890380c1081801c51a0300e071412403401170000100500c01803030240d481245e0400c55100540403036003600703e210104840840d9200d0200007450984400829056000c4040e0203400c1c1c5010b40010300894003520200000055a060060721260080714240c5880d418054004001c5105c2100024803215802d44030210201c192400b4140703541002502d0480da07804c005075030300000046c480c1081017000c005903d84580c00ba084e80d00c01e418800503aa401c1882071681c0480b4000c0140c0c0c001c6042c840a0b1002680280d0800280d40c40c80c50110001c0002d8a030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 744284604 1250 744283354 744283357
    0x30901081e0a09020f041407112a0a120203100203040809040923070302100c050a06020d0507030c11060f10120b0709061d010c1a090c030709110d0e0102 67
    0x3050750500c01c0310070440d88104a0380003540c00c43c000c4645070100000701c0104400c0e980100c0213469051022008034000c18061190008491440000c3d04c2140302000700b656081000c20315a21051040208030003194108920001c0280080f81d40752501420250003103582c540f0b0b44c129140c0416400400a01408054401d8a0032014018814810040c844c205004954200c8800001d05001412000c50804001982c01c040741c3d8094a40307400b80950354425582e41e02c0128080d1a03901481c40004001a041d1000b0704518a04003c0000c02c2e0030001002000c0b20b40d44500802800b11064040144002c0040c10035802070304109010a503641d0069030083c600300c0ca81c0821013401c010f0301d0a100f00500d0312002071103000607a0b2084211541d5000840d45000b8081200a11032101c003070701441544100862424035000316079458016100d900241c0d81c4c81d4003168421415084103006031041d01e800d21500000b028103030418003640195181002039031050b1201d410300c2e50782e5007181d0000c0060030340 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 744285854 1250 744284604 744284641
    0x105040302061314040207020a0506030403111005040c17150c1306050304060b030304060f0c05070f06020a0302010f050c090105180d0f05010c02071401180e0a0623010203090108 78
    0x349240e8440202c99840c2880c481c0300e00403003040c151410004c1e1440e05041c82903490060f00104440f04152400b8180011a400908180d017001200642048400010050641c04918440c0c0c00075007840c1508048083c5100d54200400140340324400c40400c1d0030010b03600034004010540180e4540b141c84001c4024400c226020b21003001c0c1e61000600d40b1781103000746101c1d6018120034011084041704040c0c130380c40340d80501404200100c45851500d80700d4500203000074814804c403244541c0300d01d2809408100c80d405140164001d8001030704055080c01505180d030b401e03205c28010342c02c0c0060b9408844c010442014100440030621001003402d004900f0003184001c0d240d1001c2403414203200c42c45aa1450017030381c00d9130034206004241d07171000402008940804075044284801e51004441d21103414a0540c80c003040180c01003002d000d90b8000074000e102200d4001b84044c50289511500c0d001d201c007401c8810b00b00705c4140d0291360040221008103900346494550f55441a6a0171000103416 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 744287104 1250 744285854 744285859
    0x90411100c12090905010b040501020a0b1306060f060314010302011e030f02040e0714040b0a11030712020d0215010509010b0c120d060603320a111204020906011803110105040302 78
    0x104102c40800d400c50020000d6800005041c0041ea8a40c14002034500c1282704c1c05005900641d020f6001c41c0d1030031015a00301446410740340000c0400d0b240c28060f0391082d040a034044403001c2e0200805030f090f108036480480c5401242259601d1600041c01441d6028a0341d5031444030116020a01c038441c1d403009031070020800c0e085440381e0711602030000025080320400003003070b60200b011303c02e410140203517030442c1d11030284c880c985001c410341240d8211a818900585100a00800c0c0000c0c175000c09a0055005950050107110b4800c2002483c0c80c11611030344540324407003070050001d515085640380c19100300030142c540c2c0d80c5078443d0b42e0745080d10ba04e204403510540410744100c03200c840e40044040340c2107940d081c4a03980309079203254840192400281d000201c84c40022003000401c0c1c06441c1e102c2c4007c0f500140c1e11580400320074995105101c0580748a80d2441004110310b48480ca513904144286011000040d0f070003102e012410460101412071011080c0100580e031052040f5005103902 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 744288354 1250 744287104 744287123
    0x11e0e0d080313020906031501260a03360e130512120c091f05090303121008062202030109080d0f0501060807120504230a03030b090411100c 62
    0x110282c1e4102c1200c4543c202c0c82801c070324001c1070b070514001681c203400d0b11021203c62200e910b04000541540c0c0031425000c4404041000e500c48a03000348032890785c26009403508045c002e4100811070900074000d81154183d0095004821418807a0211030705590522042031843e03141c0807681e0500783c038010b40c002d2043c400c3c905108008603106010380501c14280e1003481407038a446104800c2c9009001095800000041d03035050701c0c0600c6d0f14101d514100c03900301145050820360200342107902003000c00c1e212010714818080c140b42158841801080210f0251001d418604694505074003109031440320303030300d10100060a55600b98070600005a0104481d0b949003480e40241c0041c1010b038403010589840c0800001d0740318045c0305681d116207090750f00c100001c41428451802031074080e1085d1884942c0c464480682c1440c00c0f048212a03e2100003003a00490f81d1500074281e0b00d00c0d807050f5008007549014080000c00101210080308001c482d149080415000200c5240d081d00388081c00380c048 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 744289604 1250 744288354 744288361
    0x81204030c0b06040b090f0403140a030b01090801020702060f0d1b0309030206070f081b090a06050c0f03070309050f0d1b06090b1314060c0f0102090f011e0e0d0803 72
    0x1004050710780100e102c0c41521200703598850400c0205c4070909035098204107500e000511a030102807580740d00a109040103850902003040300722454004402d0800425516400c111a03581c0103d0040d00920401000b98071700f40301035010491a014405540c4440c49020980c448817050b2034110141c680242900000705807075400f4010040c20300383c00d080d000f50249030301154200e4800c002c0e514030145262510265900d6140c08004242140c011b0440305001c24002110300c0c1c0c0d1103070380750001802190340b03094440148502503070400c5a1540b1180311580200903100000b900600c681084403021211000f500c200107000c11040c204001e0024002a4421450591a80f1640364030b01540c406990301c000160b240d507017010075031040300070022618074803080030850401207000464041402610407420541c541421916014100100b03190076500030880802a0519010040310100300340f07042c0101180016200340101050384866040003016034001e201030f11940e00070700c00341e40c0c0700c9041e641d6440e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 744290854 1250 744289604 744289607
    0xa0b031e2d06090c040b0d120f030e0118050f03030714090604050d060516030e03090402070606030210020319080402010e0d03022401031401020f03180c2101110418050408120403 78
    0x1350b159110718412450050314030611704014101114069000e0400c0a400035540000d44072800799200060800d0780301c90444903110403c1c01a0200c0c485c1582030f0381601200392614509091403c00e814129a106104021f4550b900c90669005c641c050681c0c541d480340310038045401c0d4816600100d801a07444500d0008101d03403a4001c0b44241c0c051140c42e030200f0a008012401d441e4017031401c18440d48148030303e20143c9000c2d4010410342e4130071031000440b980e07070b030703022400c41c054201d40c4d0800340e08080f542002540d030902c0d2044c06000b03649403c3e6880c0c03805030b00180607400004040c90081e2207030342e941c10403d4020448500c0042d880007107a10000c0c4002070b01440d8440901048a18014900b00007290b540140243c0d10500280d01502d0f09607900c4429139030141c22080580184c51040c0c2c40441540d84440c22000d801080031004a070440c500301b100142524001c50714041ca03040300704010811040d090302c0ba40950b42c0c564001191603103a50610204500420001200e81c0140005100406 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 744292104 1250 744290854 744290863
    0x18030d0e0c012706110115030318091e021b0f160e010506040e0a02040506130e0f09030a0f0903020a0f0e07030203010b03010302010507020310050a0b031e2d0609 71
    0x30400f640c0c0c206601c07540c14481e44180c0110903001200d01c2060f030061100500400345001584240c20000800c2400b100d20220b08032410b50055010500900140440e9400d080441c00581400b81042c81001e03a001812000c8200c501500c500c00d590101e0401c020803060405110754013040c41c221241003600e0807101e44c489640c880b4141641c08890710014034a05440b03017a81c101c500003000c0a060509d4103000e10b1554900400107170030180d0030403000c0380b00d945046c09030030b42404001e4000741071801e1901c3c403074600b10094203600c1410314100411032024000812a4601d0040d468040001c00240d50165048426604001e507c1354415401180c61090170540a041341c00d40308105000b9140c00d03c0a4003248000e01980d00d03003803010401400554000e400406d02c1910107811030f0741c030030303041c0d10242c1c1120750558504010649841420505290400642c0100d004e0001e04650142c3c4c01c0d4a001cad5242d14080006603901819160400c86182e84885074258104000c282c0c0d50782e1910042190301ca = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 744293354 1250 744292104 744292123
    0x4060c1b032715030908040e0a060f06030b2206030c09092102030708030c160501060806060f010801260a1103070f030210030f0b0d0f021002010504030818030d0e 71
    0x12000c9209080d24a0801e0b00d0307450100c580b80c800144410350704000032005032108400540c1c03031134000c100000e08950305c07020302c502c07c03c00744c1000140c0030308207103212130090781940c82076040506040c09060742c3e0359205804240880224624000c40780400d0514020b801658400b0f80601110600007902d080d85400885445d0301c1442c908140101850000203542102004540107a000388049400182071000654104003d25009c0f4102100220802041c2c80000801c47d0141d4490b44208072a050400166030005400ca4840700703081070314000200a0a8148208078881c020010780c000e580c0300c55000d4040f101d11803005d40782c5521180c02c14880200324045014004e200f1010001650b40c1011803040030b9a034000c0818402c1442070504801805611401014183d03032000400b820707036149440354044038490009107540b59005e00400241400020361030041d64105010000041d07800a48036600c08004110006009011004140b07140240a80c4c040c2c20761511445504d02040014581d0302c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 744294604 1250 744293354 744293387
    0x6010c05100c02060f07080118050c1b0109050f010c0e06071e031d09040308040303050907080f0c0a0e01032402071b080606030109030917010908120403090b0306030604060c1b03 78
    0x20359141c001b003c41c0c50721024441c0d00c00d00410300581b05110a5260016900082200314807400c00341003502d00c0000e0b190a11441c82c071695654042e4082110a11904404d100790100810400c2810b2001034040071940c080e03c3e10940740002c61004000a6400071034410b107003001078005200c05e903d800b900001c0c0b444040307203407400001d00d0b07030505191112000d84100d0703050b503500b44103840d00d6406502074500600a540b0078000d41d880891024020001c400c0724058142c001c02000e000f540900c0300f41c1540d80c001c02403c0040340010b2002c1119010100013030500030060014212198103040000e00400200400760b80d1003800b51102400708442e0141901c07100350503100303a0340b9648109400c035040440c0080100304481000c1184410f2110f00d211122109800882d400b491603880140940c40803400810110f03200b03090005141c0c0c42900e0300003a1007043c041e94a1401c148000079540d950040c4018111074407100c0c01002244a0903500b040c100c102c010a00406800c3c0c5005805107010061100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 744295854 1250 744294604 744294631
    0x1140423010e220618050a060c0f020c030c0d1505270a03020a0b1003081908010611060c0306060c10050f060a03020f0906040608030d29030606010c05100c0206 70
    0x380d4801c000c0c012001c0d0940c0081022980048903560080540b07569010320071140250780c282c05c04600d050155499262003810005084084440081c02c9010440014400c5511600900949403000136014140d0a001c40c0e800c50401168984960108220b0110b80d013224200030a112111804441860311128180e501c081040b0891135000d0f0389007002d02c00038006910501c0014003040e0003a400030b400c11024502d4480c42a00ca88039411168441e0310850700e1821044188200a580b02c15118090705461400700740039007149046940d189006002d240f44186e0002c046240c42e1f8508003110180d07900001501c03030600100c04403000800e4211101080c80041c0c03800243e10f0302e0030740303100c400341ca0340146081e24503c00001440405603000740742a800980d10341001c5403100c01000901504207201c0c00119103110701d52a25080c4a00005008200c0781e02120107032515500460038a5000c40280703040b0150603044d0030440d1038400d81207031200d00e061078514000720140d07010841a105000c100400e6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 744297104 1250 744295854 744295861
    0xb01020106060806131d0a1a010e070206151c05060601021209180402040f060e1e0114090624070c0e100315020909070c0b1006050301140423010e 64
    0x40c0c43c14001111501c0d8403098100000c3c1505d140d60f44800f03800d00310b961ba17004554000c22122842d1490b544002d480189240c81c0141148140d001114050300c0e51950b049158200918041c2d43c4103006040090300b0210494283c4107a02d484445004a42000124075030380d04481c1070503034a4030010380c0d04a0050180b0030780e031251f02a42c507041f00e1200d8000391800049048903500e070282188054422a4820340702c0322078030030003080780c0110300207084070b0803008600f070800c000110780b003039081030591400c4100e00d401081511014610320a02c00c10a464a40f015503032030b800585100c2c1d41c1c001081c2031320502d420211484500e44080c1c0000791050420051140e00d41d5070348100782c0303000c0b41d4215a0011a00c003d00015441e42400313506500c0e03003040582441036001c00181c5480048410f100002c803003140c0441403014100320700703410000c1401d50000403401c040c0000e01c14031050183c2c001400c03000301427401945403a4171041003403022840d02da08109807070042c0e41001c8000c2c8030b00d07104074000ea80032 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 744298354 1250 744297104 744297107
    0xf03020a080f0301061805010f0c050709020c0d17190c0507120e041a03060c13091b030b0d050c12070305030d09060c18091505040e01090627060905010e030d0b0102010606 75
    0x158151f0b00161a112011010664200c4101c0e02c0180c0440341c2c0d01848070001a441850f001400710070700a10080e103000161600020084040e042c002050044103005202400c52507150034081c403c000364000c500f01503402c0d07040d0345910894000501062508126488159000c401c03d50032440440c0c0501855060364100d4015032044103242d03034075030094408581500c1d141d000401201c0d08100c110000690744000500c01c0760031601c4011003407003644811607209a070611403880c00030412101c110403040c043e161150f0310541c0c45407260290043c404240076032001000700c000190f50100c1101d60303452480b16520040c02d01040d044403102c0c1401160207542c2e004120450010040d041003075802c3d440c1035000e9018120782224146100200358000c5001e4035180600c450b2050f001c4000b0440e1142864030310f00b282e640c400700c448000c5868414084501c0c46528030647c0c2600320f14040342752086414114010061860500003a21002505034941c48194012290040d001d8000300842c43d9a500c0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 744299604 1250 744298354 744298397
    0x60f0f0d0c0224010b0a0201060f1d1b0d0b19092717030c0d020706090209010b0a022104080a0c0e07020d300f060e1e040f03020a080f030106 62
    0x10402800074000d40107004144411020300004006c0b8400400d02d5940c0d03030701941c10090907421114600800348082c0c41840303114070790f46030000d2160b07079101c480c0c104928009559005040c1d030010b4164807a807940b0031680c0c030350100c1b070715038050000420300d00b42d42c1e004901c0040000c504183e610031200c0e0760244100d0845e600800c610358001c3d40443c41080c50305000d5401e540020409413042d02c0a01c06031500a1a40c4003030402c5520030b0100040d02c243e14010401c0c2c003141640943c0350b50000b0496807041c03a070f0204290b00714103160010f9060342c854001602c10180126040803880d440703500a0003041c0704612040900311048601e0413a496200c010b0101d8030354044894010100c5e0402c00328458500030504040d00307420030201c00e150b041d800300b00c0c020160b40b0141c810240712602e400c001c0c01110005000c0c55005113142803a6012100030309864076503040028005007654010104070030515009200700c00340c05611822107651b40d440900001c4440c2c10a008400001301c82d01032815800300d40d0300 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 744300854 1250 744299604 744299653
    0x1801050c2d2107030b0f0a0501120207050a051f27060e2521020906060708070f03030c081e070201142406070f02060f0f0d0c02 56
    0x51600380000464810146000d01c0700c1c0405810402500404400c80c1c220000a0040c4001041d064107003440c0050a80d2400d0801510842c06041d602516a44140f06801140c0c070a003494001005d014005d0002401080c0c030291084c0a40d609040c2001808a040d1503603021400d5819460303040280b8040c02c9520b1050810141420940311a2400010455605949100e080b0101d0009000d802c481d08201051004140740044100002c480e0400304c040880900002107009092680b0001030300c3b801c1c4111000a80210114004074010307846640403594000d40105170155184824075041400c840042000e5000a20304100106103500c1254458010403c0184c1d40200c000800d82401c0c10742c0000d052a01559605c5150001c00b14806002c940303c0c0940110040c0210f1541003d60354119000c80703103a103d4442048a000010b59280302282c1264054a43c1511118400c01040d000c1c4034802038104190004260041158002d400001c6414100d0f800e896040c4181400c80b8904120314 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 744302104 1250 744300854 744300877
    0x408040b091309030206270733050901031103010503060417090a0b03060a080d09061b020409142808180603040f03080105010507020f0607030311031801050c 69
    0x100010080e424465029260050000740300118008102d44030500302c0d00c0981c3c1c1100580c111904021100301c1c50f0204034407090340246030403134a1030000030072902e4000901a000c1a03042c80c0c00d02611340d404039620101030075000d9129005920480700040d2443d001403441d60f000a0520701c140343c00c000d02c1c2043d24100c842c058010001074480740d0300e17012840e0072903555801210090001066968500c400c2200405200c08016940e041035001d010784480b00b0380041010354003440308040d40303a9100e928802141c51500d000380791120010b04000c084100000060f500c241001448001d005086104e2024000b4940c22a050010355041381004000108580854103042d4100c90303010071400b900500000640040300031007000d0541c0081e01c190403e850035103810b00290202d0003015040f2440a0241009003049410302456500003240c810301c0403125170040700042100c108050294000e4000c080e0141862034484c239011303004440014858131601c00719800c21012480440624040b5903810809 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 744303354 1250 744302104 744302107
    0x50f090a020a0e060301060e12010203071e021006060818070609092301030302060415140106110c040e01150b0f03010509090717060103020f090f01090b040b1206010312080408 77
    0x9040340e0200a401080c01407082c882403811041440c3d589070002c4d1302030000b030348515407005020402d2091111242000002c143c0c410003e000c1d000b41c01400d01810404d2066080200d203c0740101207007003106218141590b141400800319031960000b045901c260f50036045510207400b80001305648064a00c60b81300490021003050281c0100ca4111a5021100309030400d00b0b1040080c00e50985c010992050f401070b000003081c001000000d401101c3c000e08400c100748406d600c0320050070036000c03040c8a2a42845a607521131125480c1c28840707100040700007402040030440e9000c009000e0040f50300605045a580400402d200707070101d00359100714480318007a50440e800c0c03c081c48400e81002d0502d0a03a4410100c000a448810700c0f030600d8503043e2480504400c0d49184144810104021034051052011400704070a1108d491005811104080c0c004101644240c001c2002030402c0e202e00d503007241300c02c0d898608421000500c64102c911840304084141c11101d021100408140c8004040620 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 744304604 1250 744303354 744303361
    0x110102010213090c05040321170c0a0c03120e0606150c0307020d050f030a0507111503040b060f060a03061401020606150d18110f0616140c030102040b0310050f09 71
    0x81d40e00200c1c4c0d151141c100790380784c59180c0d1031707542407600d6082c1c408220483d44905502081d5210440c01d500020b4042203400358108007000c10024011241803c2c200601182c046c000d243c41b64144692031401d0f24010400f0280400806440395011a0041c0c0100102e40009148580340c1d804c41d001d105444000d9402c0a0443c0c2c01c2104840c0140015100c42c4a03178810071130142401d00003003041003030075103505954807a40d02e400d0b880401009105449184140400d6205000340c00890764000d42c40b8051081580c0c4420010700d04648004115030800f1011070b81784003090309079000c14140c44000c081e4500401804004a0766902c046401d290025804a100f1100c20640c0740a81304a01d034140c0040382208980f60011030304d0400ca00181c858010f0f0011070720950030803c5240300107107070070744e070786450243c0e035500b05c942003003009070014031030010407128901d041800d004081880710010002e55883e5075903840318410f40c1050314814600118500e0000e05883e014845412548018001102c0c0c0e54 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 744305854 1250 744304604 744304619
    0x240603070b0c0715080a0b010c0b0f0a0908030c120f070c08070c080307060c031503020a180209120313171c0e0406080f0106060c020303090909030f04090504110102010213 75
    0x4011401c0310682d0b201d05003021a040252031652804403e0542c1e480400d0f1400c031642205071006201c0640c1401b040502c0d00000c20680342d01940d11520031080e21900b0344914130400c006104c0c601001e040e25001109000e92a0a4000180b02c000c0c0385000012750b40e03c42c2000e8003140343c0103589200116032080804d1000489c8040a0100c41d80182c44904c10650750303000c0c0318110b5105460884182c0d80e03800038140d84c985c15220349205c00710045900666207045502264840106009120f0304400d9401611f9100752650102e030300c1c000d4094000004005940c0c844c658a070040620b07800d205140e9000822081c1007048203c080e80d5100d4010120659822170090b900c0c2c6104448004100c031021795a4500c0d11503004210080115800030101902a19280c81c215920394101c2410040e8500100c00075a03800010340f1921402110121259192101001d145100d400030707031100100c0100e0001481e001e40d5029503c10740c05030701e41c0c2e103000401170b00480c00c0f0300c5420940d4210044044046c4041c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 744307104 1250 744305854 744305857
    0x201270f050a0f510509010c0201271202090606030c0a030b2701030302010c020a030c0b09070e0c090f011106040303200c010f0b01051306080a0f0608240603070b 71
    0x5101151800803480c01d0103802004010444c20b258000420040850740007050303541c0451007034a010724005090005910000b0040615241e01a0400034401c04c10041d55042e6110a205200048046145107548401441403440e2038082a84100c41e110f0006140341407040c1243d204860608030079140c07140791042a8010f06180003c1da03005030031a40990a403130741800610040d510004007410556146140c000d094039102a0300b60b0454100502c4800001d40103801c0702d40540d40421806c10690310b5080b020b00e04515075200d0f05c101080c1c58240442c2449490003005541c0b819200103002a5081c001511040540418420154040000540460f01c60ba01400f00301c141003c000710b03501503046010000741c002c4040003009940d50500b040519507140b04694042d582800e116051a5007000201044080c610500c024480b00d840050141c2a0340e5202400d00b0f40041740c100031251321882840c0c3d9a4068840040a200341405020244a0560b00d664440c920090007410f425090410044a9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 744308354 1250 744307104 744307139
    0x80705070602040e0406090b01050415061d04110d1802061c110a030606081308030f1305070909031808100209030a0506010914011703030708040201270f050a0f 70
    0x1610b41c02c1c080881c00300c1e44682c1d03060180d40508408100142c042c104010080c806a03c150300c07407850172034000c019241c020303032040031650700d82082c115441d25402c1030110100c4200e54158440d10b010031180d100e810074000350002e1451002c041040c45040303440c0d85d08180030640040d40c00384040c0702d440c2212019903500c501c66951103102203041101044a9585a00103030348000c0400d4a8030428802194001403007688546603901100e04820b0321b4542d0381a5200190050744002c89541c00610140307596036556189035400340c2200d9402d1364442c02c65000f064020002c50025142032000c0c01040300b9038110005030307060800901828038100309030030000d60000900581600901030010040ba40900c111402818030180128102568a22141c065031050b004000301d080c0d43c0b26032040d011000401c0d80d9009015061800203074940e4001a0b6200780e445a041602c10000b0400d12044070034603d42000b00d072491011402229185c4041004188150149049440040388100182c64012408409 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 744309604 1250 744308354 744308363
    0xa12020d02190503010510090e1501170705180907020c04020c07050411090307080312070810090c11060a092a1205030c191a04210c11010f08070507 65
    0x3800c1081105004114580d014102c0840c01c044010006030906841d003520303544241ca00012118246000504100c1010300a41d4501580070002051640218442d54040c600a2601c03001c51506e44401800e9903c0212460f88441c011300c40e2070200d007449528640071700d5440e0007820b0250801f01c107000c025040725a04280d54072600c04001001e4445200d410002ca2522804954603410441498501001984254450360003001040701513821085019080b1b141407400038140d8840e5840105619103941282c0052403405100c448641e0b000000700d00d84c000194180c8000381d5800070904107e45071003902401c0100d165188000710386802c05051909043c0c40724210710651184043c580d500011403003203605510005001612200802807042e040000e031104c19580384d076903503648880e1490300042402e00381c000d0012030100b0000d21070391000700d07145032428a0366162002c40105002d124030b07010707181c440c110f00743d480086d44aa4940c40490f0780710307212a00b443c1ca6210b0101c4056022042c00e48 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 744310854 1250 744309604 744309607
    0x7021003180c03120f17040614090105040b090606030a060209130c0504030302010b041b0806030a061b091a030105010f17010b0703110a02130f180c0810020a12020d02 73
    0x1c4040441c58000038401e40941200000c075821460118001940c1c0070341241440b2941100e82c82d0554030042400d5819044030703410405858070714209003e0900401103645100c04034040008501055220360f04c0740f0300600d000c12464030388030580740d15561b090f102150190400c1c1c030080c0118055800a041080c000f908040040310010002e0003142d02c280f01e5240041c00000d010824103509009041e42504201c0d0700f00444500003a080003200020744240c0b0a001112000030016a0144600b8401513000305040c0714201001100c0050f5103004400c80011540300302d40400e51b0040702c640110285480d108540c916400c100055800c00d075038a000c07804001038042e00708800300391040c5130f6000700000040b291303d64001c0c0ca0081d00b0025202505607540d4030110080000d40e68079030200008210700c1c10001002c849074805e0b0700c050b020514000e80c0001400e00d8000400c04c58003070000445081000361100c620901710000c040c0e100e000c09100020b4a000808001c240302540101010f05489078010b = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 744312104 1250 744310854 744310871
    0x12210c0806210a141b1c06022b0e030c0d140c0718050a0e07210b0c0c0613050c1009150c0606050a0e0f0c0c030301030f060c1407021003 60
    0x303503d410351812040b21000e84104003490b9641d020400580540c0c800b041841129001c40013042c0c0c4408808100001100c1201001d824003086a04032422010f11001045440303181d1410601090511400095102c3c07030034100c400d2015000c02030311004810080940080c903228002101c1841032100705c0724500000300301c1440051010442d140040406040e10855502030070402c1c0101d0704014001c1031075904040104a030300034081003110950768181401d81c0840da90426290060050401c02030840b40c0003418800c808146102410a284020301150103e5540c1451010750f040050402491580300070111002c030710340508002d01c280c042346803600405560720700010728125041100b50108000c960108207001f920302a10000d41000d0702d503031980341d1a0480c91914100010222404038401c000413504441d401030485043c810f00360b080306c0d16541c6a0524402d0000a900e08866031443c1c408000b1025016482041c15007814844030350070002503400340002d101d4210418820503580f155079 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 744313354 1250 744312104 744312169
    0x216030201202b0e0f01080415024e0a020d11121b03071209050c040e15011508070c0303291302040e061c12210c0806 52
    0xa04100f9940c10201041c2e0ba56540030180a410300a00c210f400b03501712000484007640c0103c0c0a40d00143c0c0803140d102105102c04024000f4020034040c40381100280540300151504284441e00702144e40540340102c0420340010308402e03428070034003c44084140c0004a200c241980603140b080b0440c00d000c1145004482102c416030b10040c00890031001e5041032103114202d040680c10100984000c3c42c1c5541040e0501505e8950556510348110703840d109540c4c10080f09018442c3e08150282c01030042401c084456034441d00f03109058102c21012000000e06e14011711610b408082860304c0340c0483c0d0f1903000c0100e0300640201405d900303040c1c460403510040c10a090400581951076191088522030340300400c06030f00e0b0328020210907a8010b2000b0b0000d08420403006410080032682c032445044c8466204250766200c9001400c40d00c8a02c07060728040d600101001e00000c00c5020004400e1080f401326021103401845007000105c666000620904007605025240d5040c01c0c07400e1a0309000d8440b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 744314604 1250 744313354 744313393
    0x403030b09042f030c0d0201091214100b01090308031e0703050a0c0903051e120c0604020a09021206060915190f0207030b060d0819090303021603020120 67
    0x7000c4440f0262510300410040000016400d80c10098000e010494540d0b40040c0e500e094040c20b5910982040740e0881c116030007143d02000900108030f0106952405040000c0e2510818003060820b0080c004c2c40fa00c84045446801d6088034161240742c446030554545080c0d50704000c00b103024811800a4036a050300b5810303802e42c460030055502091074a007402d010403c3d11074141201d020b12a81c06003d100044021036075000040d4440720000d044034070300828a01e018820b5426003028030b4001180c080880e00845d0862080c0e009541102d2910b43d42c20000707049108030028052070300100d1011a200385480070003061040402800c6020b040390200d040d2805030b1243c607100c0e950860321385000680d0340e04428001c444030082d0000d4011541386464246803984001e061b00d10039480d4425441c10003100d6003d03541700b01c54209003070b42d1071040440702a20408a41c00f00b40c003d4850600c0c100c08011503401d00340141c9a040e91442c1c509884145e0780040c00d100c19541202c40d0094420101c000700d071040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 744315854 1250 744314604 744314611
    0x705010518032502030316110d0b0f070314011706060117070e010e0301020d0b31020901020a1e030909180f14030a0801090e060c220302060d140f0601170403030b09 72
    0x191310300d0b007d500c0c5004805200142141405808070070707505008a101c45403225405003501003031051341e5a4001d411001084030345001c4130f50007107140000c0b40505800c2c0b400c200c48109002103845070b8462000540b0080b03000d81c90300300c4280c481800039001c1d500c99051442e26103c181040707034484101c02e00003420b98010090042c003180e52810f070000d580c6009003040d0801c4940300c03854910fa0061190b0620501d14180c00307510707411f80025222001e40d20030440c5084494001d24084001c407a2407001303495640c010341096002541038180401c3d0342800f445804402105d255000007159242e9403a50481c0345040d8066035004d14a00f003030140214140300900d00c6c5542d0b540c800181d5810846641c048628071020b421040e402041045041c403207500407030380240790803a18400a4540040688030283e49034000942020001c103210001406a82141c0c1c420b00c194001d01040356665030750460400740032a039841c00581082c1c0940b020030000300050b50403e020380f8021614160b08404200b0014054 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 744317104 1250 744315854 744315877
    0xd09020a0e070f021908040509100302090c040e07030b2803051504021306030c0b071103070305010213091103010303203a080414070e040807050105180325020303 71
    0xc045a100f40b0b541440702400c80c0c182440c01c4000c09144d92114421030141e805107038000e01412010501140c2c00041030360095500500c503c182c1e1400c1e4079650110707085885000c02c400b181101040c0902d00038000d49030070a0010381180e80980070303940d408059161802c0221786140c01060080041071041c4410424403ca0980075022401c140c03043c094824409000901014648a0144000340154440c035044586641078507450302c00341d040c4002246220514541d051150040c004204041074001e440c40f000e2094480002c03d5640003024261464503403c0c1001610410040c00064094020303a00c0200107c409440c803012100e41d920f00c1c19401680d52030b2421000100c1042070492042e0303410790400f070b6195255040144030b8024010040241000701b82e907516103607211560004001207130040006860034505c500342403c000e040d0354403488040d00c882d400d14001071035035907100541c0540750f1210401185030080c64500c2030304141c1e07a1707210f14922170241003820300540c2e800c0000d4404030849 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 744318354 1250 744317104 744317117
    0x405010605120d02060106050d0b190e160c080f070507030f021e0f21030703050c0105010b0c0a0f020102150c0d051006051806041706091002030c0d09020a0e07 70
    0x1840c04000c02d00012070201041c0f03600907546a62000d0b400b05a06046500905001c0d1b20b42c000424110085e02034070b04895001050780300811448010002d03001c1c100c0c1d903503071001c2d8529110558040c1d188880001540040b820103c51000000d64043c0100110980b06540f14100f400554401381442c03220b42c8295078501c00300c4c0aa00075881c0c2000c000c41c0080341e25180d030511510748004520400020303020a44103030360140076201d9401c0020015a9807050b08800d580ea654250714014120742c00034008902c0c00d40c80c1400214013620741c642120070098005000700002c100d103a5601c2107010006404a045001d5651322038004a5818040c9010300541e041403612400d11111110403144000c01c0340ba138880b000a800c0111640040440390549480180e03030b90580751b0000410f40d0391040f58000d01100d5141003ca09403804007090341405005803105540318462400807101c1640001e54610518140410000408807119404480030a102600058a4030b0703407003201c001a442c0031101c1c000071034003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 744319604 1250 744318354 744318359
    0x6050a032105070b010308090a03081638040812041505070305010b0f07030e060408030403021f120b131526150c0f07080403030f080928020904050106 66
    0x10350010480d04040d07a40b51041c102079660b03d403030441c050b041c800030300803400c0014803210315100e20740108061070700403080581ea65400f520301082480ea88070103403418a807584015200e68209281c5a901c410344007150b00c50001e00c2421982102d8010b801224562400c20501307000201190100d0f220b1402440344080740010480341500740d610040001003050304d45401400541400020b550801881c0004030341c45560701d1600341c42881105403456884200810005114180040144180c030b109803101e14048080e5520b00124041c000003060100c0ca2001c450001c08c0e00702c0d4030440b07094000070f0541c580d2104070224582200d901002d880c0c03440b050303e4404c2c88010b03155074a002c1c41e110450400d150400400c980c0c2030301c501e51050718901d820040c10114031040d40c0c0009442c90780d0002c081980e0b0b00c80ea40d16000040303600c140320460118111081404001c1c0c004c0d00070394400c3c8003d40c09400805808a004004103c2c201c82c0d0381c03e801c0d282c0424030050b0321016481c1b48100c1c45000001a100d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 744320854 1250 744319604 744319643
    0x11b030b0a17030433051303051c02010c0908060c0d230603010506011b2a060906081b220902040305100b0d05030703110a02060708092803080d06050a03 67
    0x503071074020300300d06102044e45c4010f008103000080c01d0000b4904180c48a00581b01410340b1001c1d903002030410f00c5201140c1d41c2440c400d8500724a00b40190700204101450450280d8a00580d0721401040c0c0e008080055140c3e01c1082c001c0804842507000014082c807002e0701c0007400e188103840a10f542c4402400c00500341400d1140a82080c42400c04060542000811a0f000108510f000307080521510000c27280c0c80100c400b55000107040c03160120040d4075a100105810482d1269500042c0c0e288041940860010840b00ca41ca017490401c0345002c0659811296032203100392080e4001805100004260380a071011740050b40c8100d01800d01c07280099000300544052200e0f1511803407100d100840003910001c1124041e907410700b85141018901824582080031001001e90040030008404041002c168001c03c2042c0c2e00312034030809241c4000e02aa1640e20510340314072401c07403007107092010070201c40181c22440c2022801280300790b1079002240c00c10000d0340c0308039200010740c040102074a = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 744322104 1250 744320854 744320879
    0x421031505010e10050903010e0102160c060305070c0f0c0513060503060105090f040212100903050a0206092a1212040501140c0a032006070807020708011b030b0a170304 74
    0x148000d00c2d10500f200c800d400002c04040d070042080c2c05005000800d400c1c03d407000c0d00310300c7c0d41d03103901c40c021929008800341c0d80201d6038075500220703a044d90150f070114440340680308060160b03400307940d07119041c60f04d95210350404030600c10a0307a07540010840000e40fa5074044408050380343c5a00c0208a00c2c1c5000c0900d49002d2060304103603c5824000200a01c10300b036006d80c903501c250121030419401001480c9035090808041c0700884890a0540300703400d242d0440004c0c1003510b296400c54070556203e41c90039445410200440c0d8498250300403100c1c8051883c01c00c414a001c00910b034000c40749550740c0350392500c2000c414810034071001007001c00c4150b0f000020001c1d01c15000c0704452528101e80301140e103910846400034203001d400c4003450822841c1504405c940071b203050850314581481070780a032042500302d03441001481401c401041700d01d03060203803882c140036494030a081c440d00c0700ca0a0300900820800740c0c3c6c02c0111041d0001d10746600125441a101224001e03540c0e035414520840080d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 744323354 1250 744322104 744322109
    0x20c1f02010c110a2a060e18040b0f060a050a1e051009150c14060105100201020901120903050c060a0c0f110303060d080d060b1809070f0804210315 65
    0x1d0140020001c84014400308541042d00d502400c11024a048441c1c2e00110b484806010b05c10700140d040003041442c1c10504015004400700c0c0c00303880301100340640d2011894121340090100301c0b20404504600c2280c82416001003000346a00001500c83d4007080c28401241d101c0c80303812010580c016203a80b1210f5001000e49415903074003954114200d000340071010705120f40c075000c400c2c2050710b44496200352045001294483d4400700d8140e1400201a5181828000d0b0b51007420a00c1072265941c0c01442112001c12042e100c002c65081100c0c0380c240245611076050341441350800c640318505806000705841241c40c101c1c0040e43c084214402000c103514601010240000b0501b4608900400000c0c0c03a404201240e1078080d286051600c03080c68020090500c1030181800d0010030b080d2018006402484031b40030b01b03c446050103008101400c142611510042204080004070070707442a2203180c1e006014052405116440980401e0307951000262540003da9482060b5120014800f940e1300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 744324604 1250 744323354 744323357
    0x312021b0a150603031403150a060201020901020106060302180904051e06150102060c0706150b0a05040e0c16121119021311030105100e100512010b03090a0602030601020c1f02010c 79
    0x40130f0440c0c1e03002d010802c0c08421100600c40c0440050303800c144200d10072a00060140442490a549940c064040c0d008551114059424540003007001e51082c0701340c074111105004007103005c0e1504028400703412030140090712540505200d65507003144c01407031042d85071100b00040a80f0b00c1c003a89100075034100500c0c0241150028418080c00032504001c1d0341129400c08400140e0b0002d5070800000d405007540903142540d400319100b001e25801c14040c2c811030304a113036120120780e03c03500b00d190503104601000303403020404c114090200c0e0220b66908a0455542031001501ca5501d09140c130b001c0c43c1c80c599901a0b0420700604045082060795842081242c02e400e10107091094550071303150205020b40f50107944c0a4074101071062103180b034122100c00c05031144040800d1684000d1460380054110424110032100001c0d01d548190112440b80f43c0b0400544001d0015a40741406076001402c0c450440c4156040300640d42d8030018040780014910011406a11003000080d00791032082e4811070 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 744325854 1250 744324604 744324611
    0x402090102161e0603021c050627070e0a030f1202030d110910020c0a2c10050301050105030d05030a0c050d021201050f04020a020a0b06120303070801050418050a0312021b0a15 77
    0x3000342040100135647c940c4500000c52103a50f003501185425001007a91201840d1000000c03910340800a0780c00d00482041e500c540461200f80284102182c182c40300070161110021200c1c045a90310340e600102c80003901c192450103200e6041c14064480204481522100c0020040d0b06490102d06800703038118180050001d1407442400180040564850001c0c8111300c14048001300100e09480b9422680b041190031450403c0b003404285e01d00d180c000d490180d80703008000300d03081c44d0001d420401c4000c00da940c071745180d80e80e20041c0060280060000103111062041801000f9140003400302c5251035a4030b52600d6141504120b0703d652034503000c07405503104012030720b0400d5010402c0044181c00000c0d10f1455190307607012895900496a10747d210b0b000220611000f9940440300f07030b048900c122003d102d400c0e000b80008103203502c1c2601c000c0c11540030340d15850001b03000d601a5090200c00365801401c060042c1f44c015840746008440c07600301d030030560501007001801701d0000000c244503007041 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 744327104 1250 744325854 744325867
    0x90901081b181801110a02010506031203010302030318011b030e010f03050903270901030b07020c0a0b040522060f030311031801120b0d0b0a0f1401050402090102161e060302 76
    0x5030340380d840944080030f080b50300d51080880500c00d4010742000c620403000b4075a030300322407040240280340c180c030424483c0c050340340c0d07041e4003079040400c0e80d041e0ac0e0010040c502e802200c4c08401100d040880b11207050224400b1100c108444890f80e1040c20b0703010703440740e08500041000041041c40121440020300d40740c0001e0103100e074000400c0e610070106940038000c27600540010021741c213504040325540041141e0000c8200410095031502590319074007154042d070100c0d400c00c807051009024100207408240f10400040c505244001c40e040100da00b1204c01c00491003a404c141d035081d40020f892a4510701d401c0040503030280d400c842e504003042c055400c1a02504102121404001c402c07410008840040404031800e50303c40040d48100902c504900d204901d4074141109007101d4400b501f61034403d04070080349090155074040d04140480d85e0050303003007400300002508134540690441c0703d00c07201c1c3d8080321200d22100b4003410b01183c0c80080070712000041888910a40c0141040500600a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 744328354 1250 744327104 744327139
    0x1a0f010f0510031118010921030e061603020718060e04060506061c0902041406030c06030a1d010207060e03070b0103110d1e020a050d0b1308090901081b 67
    0x32000351442210401050842000220050181c2440d0f500c403202c0f0000c0d6111070401c52040305191340400380c0710680d01a65920203041020441e0f2105e0070060302ea40c0c4460b00103807103001d00f00c0b616003008144a08040c80003601c6017010018400c1103025070f10840090095190f6181c40790400490500701741309090402d0254405214003810082049803544081407240d6140070960301184440f4003004030944d20480510050004032070b007680240d140c0508c0c81e00d021411120644101c401030024101c0ca018007090009076400103000391062541c44103041a65103a41d003081c0030f0b81c00401c002507142c0c1e05074144041180c1d20310186514070b1b0700030050600022518008a81140d42002c0d410429020000c082100d072100e2032001886041500c0010003080d500603000c0719840d00039104c0202d600d8544040c0560f9140711140603000191042c0040c0c04650144003c81c04648030300c0002d814401c0b090701107004510280c21030203854002380d80b620b2910804180030102c18104803045941c52800702d08 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 744329604 1250 744328354 744328379
    0x40b07120806030a17161703160801120f0213020d06140909100b011e031401050301110706090206040503061e1b09040207020301060e18060903280306121a0f01 70
    0x580f20000104110750500b01110f408040179801400c0c16091f03008400a40e80e003540215802d100914606000300d4016200d280011b058030801c806d4100114003d448841100008180403640412240903180711107800340041d2205034440c10b008640d031414140e40c45104144942132501070100c480c100729062200082c0310074071801d00c070800980d0010810040f11220501002c0420800840b400c0c100c41035450303880f802c06402d00420764001a43c03180101400c1e00c032505803614030844140580400300e40194842d6103078504c0204090314107540e643c00b2a0412400301c402241861001404070f020001f40031150342d0104002030f038210a090850b4a903540350280784152801641c0c04207000c01152007d50190300681500e010049540ca0314008003100c400000f038240041e4020a00429904c90b0004192204d0720800c140084a03455241031103c0102c8080705d414041644031074001403c840c240d10b4602c030741d60180b9020030a040c0048000b41100001501c0074050403200c00040000c8501c012 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 744330854 1250 744329604 744329633
    0x70812330a0e0421020705100914010e030705010e1201111e030f01060e18090c01030e0105131e0602070b1006080712020a09091b02060115080a020906040b07120806030a 74
    0x18130704a101295030000302c1c81d1200540020b42c11507a00c1d8002c05526420120300001c9801000c0f2049a40500e180112104130000346030a8040e440341006005560262680c0d04101c0001b8200c43c400c034039210011401d5520008605000300c1c8000b40300d01d10000610035102c4815408000c20703140d400d00482068840e001441100c0803c94018035060f5950340d422040801c2b04414403190080c0d007080f000c040c0e121b25440044a01007880d01c0300c8803903908410f014030b074810007603207400c40c00030411900d40c44000011444600884080041840001519031014082c024000d0980a0a51420801d4440c00300410340141003880050303003c0020042d8040300540d144004040c000d40c44100500090341e0898058000c1c0351541d04051080c00410507200a080141d001030f8212135807641d135004565241066200510002082070000556a00c42c42d0002d00c00d60700007400149c9420341d1003944540f282c1044900311f440c820b058450000390769100c814250014001c4024090445140d80ea1001c910181c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 744332104 1250 744330854 744330893
    0xf0615120415020a110d090f05040902030f12120c030105060304060c0513031a0708010e011224020306040c08090a0204150e040c030314070812330a0e04 67
    0x60104501002c0342c01034a100030406548034503484c07401815021140e4a088440e01c120302d00407038040d00c11b20740501112000b0401d0381c2c0d41d504150900000c5c0c50020030507038162040c0394420035600010405139501d403200d10205911004044100d4054101c094011005010b0a00040c0201d503958000c60b41c01582c004030001e030309212210b003a0341720f01502e8844203c45140c16000402d1081e004010031000e0344c0001991003a968940086c2c0722240c0a0042d80d071219024001032180c0f40c040e45c409a40c80b405040c0042d480780c040010040c00b064000f03031420081e9004424051607080c58000d20322550b5090815400074503244000382e9507121402e1000c0d2146803201554a030780d0180312003220140c00d4145109000d890300d402c25215004d000e21080380040d100303240440318400f5080c2502c0441d5413200c2428500310a5101c40809040d020300f032440302e0b009000041d0200c200355010180c007038040d98554609c1045d80c00c200500d480c010350003208035841110070800080c0e005c035010300040c010b4 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 744333354 1250 744332104 744332137
    0x4180504020d02092d1611010e011104060f02010902060a030b060f180117060a03061d1f1a1c0503040e040f060e0a02090a1109060409050f0615 63
    0x40c0c0c00050410400820080d41145140c4240869801611070030000504800c60600803d0080c00005840f0942140d4581401246158402080c0e200c2c0c554289013204000020404009500c0a542101c01484049491260000c1c081080641005a040700060340d80020009950150003040c40e80c41503500304020540d59000c170b10709594a690585030050350342c0088503103980711480c00e003401840c29580607010480700100e5918144030b031101c69100d50000341446540501e10354404025240a8040c03c0280c0e21003e00042441002c120045200c0440081e40f00103040d042c3d4240300301c824a8a01c0740c84002400302c510794a4982920b0040d0159032001180c484d00041c0c1803160440c0030720707081800307175100c40800d00c814400c2c100307203014070513000710010822040203e03181552042c00f003134000e4101601130002815a1195401340311440401644145000071410020359103a210742c120700d030003c2da03803824440700d030710320070300300b41c0d11907001e54a15a103c1680d023405000c601030183c1c02ea020303208 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 744334604 1250 744333354 744333361
    0x112a10021314011716110106080307030e0306010305150604091202060103061a0102030403110a030b040312052d0907151707020109170d0b210c10120e03070f0803010e0c041805 77
    0x1146d00c00e00c2001440304000c102446d141e514840d180c0c3d10900c810b60002d4480c0302d4101040c0340200d91a0304070399200c00101000660360001c01d04402e030092265601655070710150022920795540030307043c0035140c1d01902d010340c110b240601c110b42c1046090094811030300000010b50360000200d405803900040c085190909400000d4540030094000030821505403050104050304078108440c3c0c0070000e80140415581c1200100014039402c410000701e840700d1410039034041d40d03c03407030031340010344041074511003030700c2d24102114440720081c3c03800064402162150680402c458168001050f032000703004031101e84c0c445d80110003200940c4801c0b0b14001030080700c00c2e44030b81c7c032042003030b14040d184c09042203144400206a004102d40a2005d00800d50000520f191a254040081c021910741694400302401440b00418042164111901c810001c031400328a440c41c3c450049807141c02070750b581c0d6061a20480e5809800382c03082042c110113100c10312400c82d54880b03174088002e501c940000c00c4e40c0c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 744335854 1250 744334604 744334607
    0x90a15020d020f03071407031413171b0a0e0c1c110d05130201080a0b04061d010f0b1201030b130c18112a10021314011716 54
    0x4241c030389089070148002400307881c4103a100f015521800450300c41d86001e094940c0f0b0f0303181600c02c1440080c0060445003810000090080282015141c1040e01450341c5880302c40d419a2040c041c041441d65610002e140c0c001d1341c0e00d0a503151401c41c0140d80c03814800d4500741c04184441320203410105a0170000c94010303044900360050074a403540f003070004d011441c0c10681c14041b6178462414852401d00303000005856140315110f241010f58181e441c18640d030f4900300e2a00084c841d580301e0070350040d102c030f40000325035000306a102c41030302064083c80708651500465030100300702540000c82142042c02200d01c0c450a00f684581102d03082981c40f0315581c0c031041c8200840041620040600c1e00c07000000c2840000c040e2003a0701c0b18240c070020404030962031010f45c0f080c06041d141160028840410720b0500350040d900d40c50b05050a02190754020410490600780d0f0096050701740003100700c51042001c4c0b81a00c0204c12803140031308244042704810102c0c8011002e0082054460121050311000001d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 744337104 1250 744335854 744335857
    0x170a0c09020714060f041202060f070513050d0804090c0c2d0816120203070203031921050609060f0603070f0203040b0d0b0a050f0108040609020d080c0d0f08090a1502 73
    0x8403200e0f026104140762070792400703000b80400d032429182c8190034100d81003903d00018000f0300500030300f40007140c0d507070b681c0c0c804803081e501840d10710501c0e4032a4900019141c40d6070310000c104502c03e10700340d91030300d0500e090311080311000c044200c01c0006110700c810105540c0100380541e89da00300e03524050380c008040502c02c08814114018648000010b044251190006520306001d2180130b82010080208104aa071b0b4000e641010394184c20401205607404c0044a4040ca0f11009040031001c882d50102086910b414140f0943c1d40d003900c507001c0040e5032030109072040c1c3c070050840b001002c050864011401c9404020000000c0c0903056600c654110f000300291401400d500241d5503076000241c984101821300b2228071030190041800104d420b240a10300e0310b11030030381030392041d105980b50f0b02c0d080050250010140d07001500c1c5c80c81d103004206114020441103105070000c00e900e02c8001d80040010503903800a008001810080c000098004a908030582d508007440e8501b0107184e0003003030001d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 744338354 1250 744337104 744337133
    0x902030912042402012309010f0207050a0308010911040e040303110f12010506030103020102210f131e0f14040e030415020f01060803270d0c170a0c090207 68
    0x100d010900080d0300c09880f10764210700c6103080c80407076030300c6500708141d0907240d80c0614010b1000781c1c04108015902e4070301003994002d10030000403407804000945107040f070b804150240c6050304408045c0c0c05158005045a004201c4290200107507030441c2040130305801180162a2503050f0322010805042c801d030800c240340500740c45110ba68940190030b024031603101a481052181c00c2c0000013484d4603000c01502d04807601078014000c1c003014407003105001c2500540844500780240305484094480c940903061107140704054021060500301600614606034003540302c08401ca084c01c0c041c01e044140010101c0d101c01c0285100700071075500140190040308822021403001240000d441244000c04d81807000e050740940d040c80382004003007800d0703803c07a0041309100e910401c5040c02d515003e4a4000039100300c119035540100000001034442c6900b04c9041c1ca0b8103502107014020390407411515a2200201c5004040c0300c011550f88543d008124401c40d4921540400d0840c00c0c800c0b004a070284 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 744339604 1250 744338354 744338383
    0x12050a1a060f040b10080402010c0c06030c031802010f0807120e010204060306120b16110a030806040b220209010c080a030e060606251b0602030d0b0a0e0109020309 72
    0x2010440c0100c4242100101c0342030384101e0100c40d0301601401d103131007850b00503003000d0000c0700115600740701500c03c5100a00124108004e1024042c04200700a50110180c40f87c2d94020030f010203000b00040955104550510381d1100b90740c2c0c3d22005030b0300b007000c035504440030b820071124035507131620140c0702c1a0024410000060602d0108006034906500034400c2e60015141003043c5501c130702c0014981d00d0104401014083c1810214840b0050300da074401001800e0701e03216900d10903072200d032820101002c1048000c100e4410902c00189418003501880c00000c0c0c644400c1e60f5045061800e01444844150014650020310401c1c642d10a1070130810440d04124400da541c148008024001c0075078032a403010740c0c022507011940a10b082011510340d0700c0341118030100c0c54201d05056900c80c00c041011600741426140360902000803200f500e0041c00b494026503103454844883c581941e180010300340c130403c14043c2c20b008140c0c208040d981075507002e100042c2c80c0c0e03541c001e40c0352601c41800e89144 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 744340854 1250 744339604 744339623
    0xf090f0f0f192004080309030d030501060503130f02040e1006050102030f0a0813020411120609040f0321050106021b10210f05190e010902030d0e04180503041703030f0112050a 77
    0x2445c56000001050340100c20b904072226003251071021403c86001303016850001341c042002c5000c4518008060302c015008008811040800d036000070215041384050f02d155400c032502d000004038107407003088020403007030001c1c504d00402250018060b110704541a0140141103011410500360103002c21925a40548100042580e840440c0100e402154940401c0980500080e1083c203242081500031076010700351200740c110030f6030142c1e10000c1600d043c40b4024400c10b1390818195142c010380d4028500e6401800a0303080100907104643d44002c0050302841c800910700046a900803222130032182c1e40c1400a5403030741041c4810010708015041811038a083c2000d001c4043c1300c0c6600d4000304550280d0410290380031050ad00e0aa80060314040c0d450f400525121980ea0700840460641c074030300034000a0403140c0d0341c80360b01c010014001c0a84040c0d1001c60140201d000c0380d80480c1c1c0202c1c0c100000c505501d0305001910041c4414011620920311819240d81042010001500e030307140c0c44031510 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 744342104 1250 744340854 744340859
    0x607110c030d021f150504050a090c03080c070b090f10261005030d0c080a0306030609260c070621020318120405010c020f0f090f0f0f192004 62
    0x1d60b00c0e80641c05040a00e5200c9800802c13003411480703481c1c50700c00980c0c400380301e07245003070100001410002d1845914580b80d10940000854a0b16900040d43c80356902135184d0344403545991900a9940002202010402c40c0360f88503501c040460002c02403c807109451140b4040d411036072586038069284046052070307901186801442892031260381d1465036000c0e1560b80340b04044c0d6500829181c00c2c0490300041400000c01c80140c0103004002e51800c021030007598940d5100104c40c0c05a4003928000d02c0c1c080d528801c3c8040501d00e16402d4548005c503800e102d80c02e03c0d46902c03400503110340e0042c8584252158a851040a442c1100e409542c00842d00c03458016055100e10050408202030350041c0603850050005a1003620243c443c103035500d074401f81d1300d0b6003030148a444074403c2c10b41c89800340000707444660344c6007100b61207040381d00030000050900d202c4040008501925030a80d40c0801e01c200000c0020343c00a0305070140c01440302207000e904043d00f5018180e17901188012400340000e01 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 744343354 1250 744342104 744342107
    0x403120c03020c09281805062e060e0414010e060a0608010f0b0c010605090702100515010f05180405090312010e060a1a22180507020607110c030d 64
    0xa400040e406602500c000010301001c0000580f0102c0d128100b1a001001045031080d110300c00156000a01c0000114414401d40d604488a960744044501ea40000b08101c00d01c00700c1307070a6403c040440003a0b1a694489100010400b55290013601d040115031100303010320383c0da2600140d414503a5403e64000650311030583e000311301d41c2126140e0051030b2480c00065040d1164503064100c52134505420051400e18002c0e40c8180e01010204000d503490314000300f9965104c142e0240950442d400400034000b842c5840c4c026a14000c08400d4401c03215004411266048920096840c0181c5000d07030303a5200e02d02c2580020040c50b468513401910380710400030300d1100000100082c4504081b0140246c1e600c01c0701d40849841200c0007500000030302001c110202012034844001c9101211a50801b01209141071781e02c1e0b44544c02c8000001410010407066442e00ea51000321b02e41e0341c1041c00f0602d40b41c2406540c80a01a101c00c040028440c00140d0410081c8070a19940c00024251946856039010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 744344604 1250 744343354 744343367
    0x27070f0312110f06011203090305100203061002011506140d1a0f0406120206070f081603030f1415270f01080f0a0b0c040e041209050102210708040312 66
    0x300104980c2c0540ca00006400285004034120b080014502d0b0ba0825401d1011011000030482c2848070b1540e01000081040c0300304285035035426030040c1c8915101040201d07110384940004296403400007440810b032000c10070001a01e402d401e00340d00101c0c1524800b05184140c2110240140c90a441019030001c4203003c1d0a030540c04072a2044041107001c00c00c0111506072150f0000f00311551441c0d001414410080d1840c50b010380300c1e64024179566100c0d940395031303c0004123a40404c11101d00e102095014401c05070007099100c1d0421400c0c00062209040a001a140032141010155803001076a100320f41c2c0034441c0007561b0120300b13480c047c805082040e9000da680f085074059440c00415003204c0003801140d5004c2501c014050b166050b202e4159180c00a05880c180c40c004100101d20795149000e2240200e01c2100340600d0003044810041480c1040d400c62811900715800c1c0240d0030116801900c65200c082c034603655034010914000d69184200d90000303051111300b082c4180030903006074 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 744345854 1250 744344604 744344633
    0x50115080d05040803040311030f0a0b07180e06040f02090604030303050f0109020901020a060b0303040e041b1509140303041509180902010813030e03030408010606030f0527070f03 79
    0x10121445030720011001d03100d034000c038000d01255070300a000c100045011b1300c0400c103041c00060195480d03004511245400d05810707150564004490710203102019901a92500c004101d00100a2007541021029003108101608541c03080c0d17142c6108a9041e59903030704480c40180010a0f0310780d61647ca2801801400d411902902d13611108000041c01d11164001c07506208016030150031b88890942e600c80c0104040203146425110500010a564020300f2855008900034902d207200d03050302910125910380140c0042d00b00703004c0c5582603050940c00443d0171013034604a4010700402000d49010070b2450180ba0301c0400b007070341010420307400190040c22000640e0401810448000a980341410035240101c500900152424001407030b510300c000301001c946442460070003001110040000d203507030016000700000f41d5440f0404c110807501881000b0525107458414006460201800903180101a0841d418500c0140d0034a20b20380d000d00c4044060000c0d0800c004007282c41e800c0c50701c55112000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 744347104 1250 744345854 744345869
    0x106050109080106080309090a060b0307030608010b0118060e28061e08040201030203180a031d0108010302030309150d020a02211201051c0501240b0a050406030216050115 75
    0x8030780c0402c5454040c00380d141036601c04070096103402c021405110182200800010105503105004250000a0001140511803d42d00424100e0402010901b110080f4070202d06214420300091948a207400508040300c285003808015841e0704400f00f4481440c0d8030314400c841d006030700c50500708240c0c11502e80070780d6030955480d40e4201144588001c0480c0424044004c0341540c80080c00641c401e0700150750124201c081e5801009196413141d00d02040c60b007044001c52021444440c00d00300d42900300311001300900e89106075500d543c012907128851181d90030f00415180c00c002180c0f181c2c1382d0440720460010720b000c650f01c0c050004025120102160900d01c44d008001c010381540051005403650080c803e04030b02a20392038101085203580c2040300c00c0522100c50800381010070420311582d45084d808a00e000c1105a55400e40c0d1401403550304034850b980380c188003444080c2d501000b5601542c44a050040c1d503590442c1d40b40c803151926840c014015800c0c2101c4040c800310811020b000c58182 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 744348354 1250 744347104 744347117
    0x102030c2d0328090509280b0604050f0f0306070c120519120b06161406010612020c1e0109060e1c140403080c060108060a0b061b07090e01060501 64
    0xd503031a07501c0b031140a00c0382002c51410b0a140141d840c4500d1401604003c50428003403090b914408122000e00403203c0c8441210803c2000040003104503140401c1400c0034000c21100c11418001542800f81d801000e0007000d0802846080c1d44541c42c2c00002007000504950360f41c685854028002c0655020446010038100f01c8002c007180140265031141d00b002c050f00b03514a104d440d0482c2c10804500c1c4001d0059195008400d5030345512000340044807060320391907002003450514810348694024044401e0380400010440701e9403046900000084640f8056561603120360703036601d050b035103481007400035800c1c013096036101e4015400340d0b603214406d4405000d170211382c040c081d840d8108039095500f90070034654107408144c490145003141903141a040f81c189601e81d2100e070329541041190b90700c1ca41c40100180503000c02048100c0e48454025802c1c081000e082c0b0220300e4a005a01154000c031a503004229000d001c14070040703004e0905503904104003140e2a0345580079041d58441e041c0070401 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 744349604 1250 744348354 744348433
    0x609080f1b010510050f030a080d0606020c0907020a1b030c09020706050901050f0703090c0e04080a09150903060b0d0b07200c2b050111040f091401140102030c 70
    0x410b000f110700c036082180c1c1050240c1d00c0d00d8240100d584000d42c04075418003a50101000140d0325801030100705012101c009012800c02c40c010b03203000c0c002c068151107000312000f081070840d0f000602c1c112040c0d10508085000802055015045c0c4003904002c000b040d100002080e280080d42c0584050b0780115418013882d00d481040d0707822940240c550018032807001000801e9075010360012410b06200c0c98114030019a200c0c801c84400c00d00342d0b011240400001040340205174402ca261018245041050b04201f0780c008020705415590310005003420f4451032941803c3e82c03195040001a60030110300d401d6480e003004024a00036403c0821100705584048400c0000303000500458403007000b6050f09200304101800c00114948881340c0101817201c0581580013880038003500072907001003c0c00944842c14401e0620003034078660072941d2810314061000000140c0340d2085030440315082c1c164a01c00d1f2591004078154424040c14014034032a6001c3d850758100d821a100302503818801c62240c0480 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 744350854 1250 744349604 744349657
    0x617010b07020d11030c120c0909030c03032205031c06151b02042c07051f0309020411070f170723031201141e13090609080f 55
    0x6800381c00394100c00d1801040000541c286031181025a0040481d841c28107940c0000702200e01680550080380c024030000d40c03050503c2c0769031a800404800c040c60501c180285442e60380d010003407101190030826501c07001080b92801881d10820340090540b96600d051552072800101c448174650b01e92433034120001180c101100403182c09a980703a8401c00001422258481e14800314041682d0269656403016030220a011702074031184008620300c59103001000c04103052280d0307540120b010b4014440d111701000341982d00c41050810905002414549900126008210359180300c510080005409010301a0040848090901c60f41c11958100040300b0025024010302d40300808103001c41030406200c40b000c07040d00354008035480480342883c6107108030f8900e040e0281d001c1e510000406122000b0b43c1003000529080c030f0480746c090050384213520b0220385440100000c0200e00c0b96900e116a0801c51250002c00351a5000300010f5204d401004003036006030310417170f01d0ba4a07210b0b50031045078582 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 744352104 1250 744350854 744350857
    0x2030706050a120902030c0916030c0810060f020f01051306050c040f05060703230405010314010302100f0e180613050402030c09072d0f030608190302160617010b 71
    0xc2259a075014021600c0032a0f050151071440012030b40360084001d200910f80f104a0700500c135048200d16100c60864800d40941240c4140343d41d102000351802c10081802d40b0420713124119009032074a0a17181591802c00c9040810b0130184006950a01d01031168001004940c012210301803c02003020752903662015403140314512442005000f0400c04100610781200038010090090903e10303900c0220b6200d6002d2074440386142d1440400102d001d00c19035905100d2521868480380800301e581d415030300090f4001702550170050800400140410030144a802074005c4044054600c504110700440c90b404602030450358180243d20084449500c0b21843c09010300a54002e40030b0043e0030200000e103e01d10800134603c000f44176616130b507040044041010400c0c0c0d00101101c00c0c0c0070ba201c00b240141148080d580c180109424440244400b8401141c0c2c0c40600080d9030158621603554502641868880d520540070810005030008141e60020410030016507007020004c02681c1320101991503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 744353354 1250 744352104 744352117
    0x20103020c062d0f070c02061606290d1b1205030415020321062b030f020a030909051b0301030605090712030f080a020c07060519020a0b070f051903090203070605 71
    0x34001355201052199014485201c2d545001804480c6000320311184400c500c1f8a25008444641c0c0c2c1d0703c00400843d010741d008038822840301078000b0398240480000303994209043e07409802a14401c10900c3d64581e00300348038008101316161585100003900300a501d07900f00d03129075002c9010000c03055540074800300884070f140440e4080c1c0b91002042602800010000401d07154105030242c1c0342e18404041080b0116024540d03019940c494072207071900500000c10460000195031042c0741c14400290011303407a009564883d170b40001da9a0715205400150f00750440c1c8401c404034000000320500005c3d40145109a9048003102c401b60b658424581000140384806800101101e00d283c1e6158403034142c1940082040d00c000d030501451070071041c10805250301003008201d00142c1031110102007034140189600d10b0025020105480c0c85141003010010210000c110b0840311000340c00d130040d0b01782e406803c004060082203010a41c00500188440001030748030b072286000001d0f80d58071400c111444c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 744354604 1250 744353354 744353371
    0x50f18060c07060609020d0f0e0606010e040e0102040b0705030d0b0114041e05030f0102180411040b0c1c0903020102060f070e2b0605060109080106030f020d020103020c062d 76
    0x1034076550504038240a40200d00112001511040c0024107108240090500b140c00100000707003031014503010804580c00031030f0000041c1c00080030420141e030840404900c0f142c003540d003c1030715503130903032524020b1089400c029546600495180140440080a01040f540302101080a00004401546c100b00d2903100c01d422054100300c148055030300600d01400c142035041c845170710140c645001a007803040720500402c0d035a44c0402d040500c0d2001400c110322900043d0b804004103942c1c800f100585d0b02c03540c000c50305140c200090400a20004000a010704030702d0306c41200c542c0c6880300006000045d00e10050380107100f54404501c0c415100380d5004d000f2801a107501c0c0001e80080280800d4183c0c041c41903400c2e0304d0703540402451400304c40c800c01c8018402c210004452901c000054034020f43e81c0c0014009030f00d4540c0610004140c90708841e0701a03011030714409058900c0c40100c029204e01c0c03108020074081c80091004181258041c515014244140a41c00500d8140e81c2840d08204981c02c2c1d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 744355854 1250 744354604 744354613
    0x60601030e10240f2301021618060506041208071a09060618091c0210020d0e0f0d020c0603060402160c05010f03020a0e151207020309030c040902031509011d01050f18 73
    0x172007540010780c884850020600541d940c03c0940c0744c440181074215481407044100300d9101a2003001d00e880b40c04003500040360340714205230400008040031900400000c3c0306000006440c018088039602c4180788844070002e00c0c0a5141c5030400715180c0b03609540c00c5000e0000024500c0b80d0521103600e16119502e91001050140d120440d10110105070000407415401424000546201640001c155107202e0761808200b40c3c040801c550720f0489814805020b5401a4a031442800e50115000120b02d03030071120300e5142c1d21008000740c000d1040590700112401018480020044e40c1003a4604a4400762142400c5e040a158150268030580326280006070b00460503908601d020030f2a000024641e125850900c1e01007842188c40d00700c20f130303003010140e0301c0031401c801c0a2404021031091900c003943c0c240180e00550b400f196590f1110041036804160003000100d9100d025032002010350320344420320b5280054065101d000b03080540c1d02d031848007000b0000619401c0d40402c8250360700c1041c0c0090 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 744357104 1250 744355854 744355889
    0xb0411090f0109120f020f010c120509010e1819020301120b04050a0606030b0f1b04060305090f0105070c03030b03010b090f04081e1b010e060601030e10240f 69
    0x254034144072081c54107005034400085840012509039074030503403180000c100200d005004105031314941c1c0191034100706000c0f035407000241d011040040700350701c80c1c00c0943d15040f003c40140c0d02d07218032203540358029451a4140d1000d40b04d5040c100c0c090420711601030004410306220320b0991109004081000c1a0310b02440005101d0644181e4494000e2040c0c0e015151035036141c030144d0b0100e500075110502d81c40c05002c9115940303184242c01c41c0a9081c0b01107200c10042802180c2d0040d40300300c005140d07442c00001c040701c02c2485003225402eaa0b60007040f41d45485180600314802d508825000240392050065032800d05105103464008020245815595404100000c0c440001e00450b00b00038140200300c000d06403010100c440c0b4000d01d0056848a005020110700c0811402001103d607041124030f03201c4420100e02160812420301e00494070703101c58589103203400080011740000ca4a48130b281e0303c4c20345e0151000b0287e0180c8040031000580d8640010602900c41d0244101c4415102501c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 744358354 1250 744357104 744357109
    0x50409051b0a0509040204030b10030311010506010801170a120201242d030b042102010b301f1506021902040b060307030b12151308040506030403030e010b041109 71
    0x15020300c0708000c5c4050300e0103440360743e0301d0100b00040c1d6104000406c10801802015040802c01c1080c0010100800c080c2c608540003c01444040c81900503017040350320142c50174207090024800c142d812540365803814030001002070003002000c0d49008921850455000011014500802125000125426610b60000f0082d024100c841c03c100f0407003030f048200100203000592410b11481c016080192414040c0310510090580d14030160216494082909825600c22584e18218201c00e5144058405610810080050080c141039064400c0049007006032500c65080190301030002400c2c0b101034203a40109100c1c030740c0d6001d10350141e0000ca009010113583c1e40d1800503c40d0004002040c5503410386d0114140f40d005661610000b51074026400b0a41001c18150003104040d50040400c0c1003000b48070b0b461640e0160035103905005403448441030080d414165001717860028180703aa41d04051802030000d05640025615035401e0260181c1285451320450031010050a585460103151408 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 744359604 1250 744358354 744358357
    0x311060901020303010915080d0306050a0906030b071215080c03160e0708060406240809061003030c0609060612050d0806060706331d0721060b0307050409051b0a05 72
    0x480300d000c7c0038a00e000501907900b0480056072200d83e03240012550308000c2441352071203440d0003006085050840400c0012550040e03158420241d145c4081442041d010318806003c240300c0c0300700c81090039003010415000c0800c4400d80b03008220201c40d20002c580300c840c004c0c000b1034429074000000c1c400c00504464001e6a240342c1c0000002c00020b07a59440300002c490944501a540304a444440074181c1e140da0404101504154460020640c501d480f2800d14a80180343c0002400c004804c2c41c9181000f00c90b40001c003443e6070040302402040d481d40704083c0d0981c0c40355403c1c4e41912071030941c009010300038498a8000d04d0054511450994140c842170060b049407c542d245160070160641d50011703584620000d4008110742e58002ca501c3d180b4002c116000f61031600481c60040810310001c1034200b201c1075101010308801051750b81c000030b9003070000d01050344007400342580082049812a0f0020090095a0714040704000b01d85a0306103071950112201c001c0c014051b0200414258a4040c00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 744360854 1250 744359604 744359621
    0x12d05130c06180b070809030613050706030b0109091a011e0e0f060c0d05031e010f06081807090c080a14270a0f0b0601050a05090d02210703110609010203030109 71
    0x50725404141c0e40c2c413640038903036002803010f84415201080990003850144502d0341c000e5101013245508084548610340c5408a03480703102c0a165880c4844a40c0b80d0003189800003e02144108118590a0075070a003480c03940c150744580000c4000d00f5001e100d2030600c0030581c1c0140c1a64072684040070700800c3c0302666008265151340920300f403041405230041040101020110396541d03070f4903801c0c00000083d814101484c4003580b240c0f0070006010000c150551036045454516000c80c6989618070980311030000082c08030024060401c000c585502c040e040b02c04824103035a00c4d07240d15510b01803980104e58013943c1060f078482014020421212001941d0760000444000d00d404000055a00c030345040d02d00e140846007100b60603811001c3c0041e4010640c3d00802c2803c08501d05074001100500c0ca01c10034164a101d548141040419911030650098a4050900254500d90014143d196650109100407200f8601e040c3e07070303155141003d509071101d042040c3c006500756400d100ca030801a05084 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 744362104 1250 744360854 744360887
    0x10302070312150302100306031502030a0e0f032d030a09030509040c090e0f0702210409050a020c06330d021c030e0f150903012d05130c06 61
    0x203400b501280d4006126141045100c480d41c903002ca4a548140441850000074100501d854400b0400c042801e4122061207614000300c0180e0741d50360300c0181c0c00100002c111003441f61080d80c202010a80e0000024074202446140007003040d588040da600d00500400340d40c610480090000c83c0c2100c1580e080440070742c0c441d082c46814098130001140c2103420b10024200000e401c45e80c2008010784240750190441c46500c04940b00703152010b80a07542e01c0c9102c81211014a180c0410507241fa01042030707602900d14000148402d040819000d0007940050301018424051400401e00b00c1c0703100d500740404001c032100c0000c9141a0017215954036041400416049005080010016603560300b001450141c0d0131180072203c42c44d4100102021414801180a031101e00e403006201e40c0e881c1c0d40403e100580084c21940c6541580200c0e01400b04100c41e80c0c04041120340022040613402d0b0f42c0324400d15400010041039841c40002440f06443c84005000d54030308060502490b4802e00091100c14244c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 744363354 1250 744362104 744362117
    0x5130506041d01020a26040210031e06140a0806060f06120109020309210f0a02010e0708251214070b0a0201050f0c0a1d0a03060207061a06030c04050103020703 70
    0x605011050482e01c9240003111654002081c06259401c10390495101a040e90b0f00c1c420034100100300c401074100034001921405a981d00550080e05c00d070060705502d001c0300600e040000794600b400d005001d2901403034800c600c0072200c520765428210301c8101210020001040b05403108814000080d50f4000c41d01d401540c00c221156a000c0c0030f644260007051072a4005a5078a4507403030341070400c101204881804001d00c0a070803c8203a02405440d0b901415448031582d800301801d0990051002c052500710b82d0180c002c001529101c042202c015204c945642c40001c500c20032204401040c0134018200044000c04603040070a41008403855040100821a800b00e500d0b000f161a458009070040c1d00181e44070000c1002c419100d8641c203401c01c0350b12401c181030404080000d0909120036001d440264005000d8808aa98a080b00801150000300071990b9040302d0900e100500b0820300c0031540c248081d207240c034090605000701c91040d0034011710341341001d0508004401030740c46000c080e4100000c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 744364604 1250 744363354 744363371
    0xb0309070302031b040e0a11130f0507080604060b04050604091a03030f07050d0807021506240d06270f0906020d0203060103060b13030b130c0f09150513050604 70
    0x30100000132400c1d511140b0040c0d00c440d90300c10081940c21034184003100d9001010001c001941446070a00c80000840311030f4112000d410006008241c00703444140900c0c245001d011342250006803032800340c0001c0d0750a000385600c030910545184070300c2c46890b4010008110801452515a100c0c00c1341400300d00d0200086028440042d02d5074010400408028200013202003c116040003600d0036100c541c03c060741e0720700d41124082d4441a0754081204001000f5001400965030060041c41070b2114540c5014444195580c16032540c00c89440003407001e00d880004103c40d0b00c0f810110910361122070b4507460756640078a10300d0107403040002d036a03603840c0c5800c03010001075400d0029101603102c2500041c0c0340e02d0700900050a43d0030a0b031142c45260f10401200807924602c1d440002aa80c0089100b1110784484480541400380070310050424103804002241240d0345144490841d01518001d2180342c44000092001d03c001d0701c07807981d00c001491480346214900e50405d23070b800f000c0140001140507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 744365854 1250 744364604 744364609
    0x4060906020c0609070f140d050c0a08160e060d030c1a040f031205010b041401050f0d05040311030903030304240903050405040c0305151c0f0f020111160b0309070302 73
    0x200041002c0240340c0088003000741c5801c0030040340c00100142c841d0070004a2600c210880e0b050030252003d8010712100c00d0400a1110802004000e004060811801c0da550303000c5c0f0b41e449042c26030312280600115080010b5a50340c2c000040e0280d80000d00c5043c0c03035001560142d44010824408403a004000c1480c01e860301c481080395841107001c0c1c1005081032031a464000c11900d800d601000e00140340c074005012480c1c0c483d00761400d42e24074166040c03460403000d005840900a0107845086e00000090600240314035400090041348240c45000e00408071520307043e1070b0b0150b20200d58240d4411710004001c1110115101c13414000c1400c40480c040064260300240c8102078416030100e000081c1c2044a4145881031654041c6189804c0059062262085440c440b0b117070f000500c540150105403c04d182e0300701c14020300c180d0040c40d01c4c66000152805086810943c58103038040b07154a071100722540b001240d03840d4043d480c08818100035080c40032900313960704007404110741c0384a500340220058 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 744367104 1250 744365854 744365857
    0x31104050402132f0c0d11010908030a0b030606010507030c081e030f04030f02070609090209030c060c0a0c05090603150403020c03011409070603020405060a0e041e090203120301050102150406090602 87
    0x4182038091303400310310b03403074041c00c1c0800001e11200c0c1034440040001c1800d050001c1a0000d40c4d01c264a0f1000160000000c514050901d40c14050811034001003484840440b691080e110600249d040d83e0460b5076003001507803103003d1540c0c00340102e03003240c8288000903040001040340380f00c000c000c5907245400c88000c07401900219a001d00103518101400b0506800100c00b101401c2188010240c2d02e0415000428907a042d1281034107142d00491040f105030303824407008407030204c0540b840c2e4948039810403090761078500c0c8009440b8a0440c2c1008038081c00c208480394490032002c0c00038040480080001c0c0b0307140b40c0060050b8210f024014030011603035000c0c011814511fa48100c14080350a04e00d80c1c0d00d061469030b50001040c1441080100040e44030007080d40c941c00d42c10b01348240a0603100010802601840d0062880d4021640303164400d00c0d00ca6000d089854002e4084841c0142c00d1414005030b0b00c803c0c001c540c00b40e071041b030103130044445620269600511484020070b03601c10175680c0006031f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 744368354 1250 744367104 744367121
    0x91a0613180c08070501121a03030a0c0b0601020c0a050603180316020103060824220303090b070c02031903020a05030c0607170c030105040e01090512041404050103110405040213 78
    0x1d81280a00540c02d105540c000d00703001c0c1140401400d001ca103000f001030101856111002c0b030050311181304489031003141c0e6086420340c4025058a6482c00305520041c910341100e04100c800319a448085101940300140054640602600c0e6180c3c160400007008410b400040141503070b03035141201004480010300281c0411540700c81d2000e101c02c1e01c2d20002d800c1d155160000d5030f00e6448030f843d2a03990160b040c01151400440d0300104d0307660b11104a0300407140131002c2c80244420b2021220800c25034154080011a80540d442c061240c55111003202e0001c8030b03820107941540300004071420070070445440d0740c1c49407090049904c0d51086548a40c2550041e00700343d0544d0300b047c002c00840c550400405009003018462011181c5041081c040590006000c0d441c0120350f9091903580b142c40940c05540744030380140c101c031580e640c0d007807920030554800d0145a0100e1404c1c0300d45001424070f4000d181c140c950111200d8400e21070b03201480010600144183e900070250106030340350444500c00c0c07552 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 744369604 1250 744368354 744368381
    0x10911071518081306170c090d050d0c030311031b0309190b0601170403020307110604091a040c03090f08130b0a020a06155f0301091a0613 61
    0x104d440070b96480388080d8120358803a2050100c001d400d001070144076581c03950300400581c4900d4850f040240440d5a032a9400b0380104280300c1c20800c51034003a0880b141000c024403940d01808030800b8800140d1443c0401c2d00c800d0141007091446003a04041c0c0c0c4040c5502201075011550202014048041c9a101c0c0490903078200c0c446800380805135900095081c440034100140d180710b400c05d5a80207549100b00d2a020301041c001d03002d1b644d0342c0c0c0e0710041128001c10138494140f1421058030711031480110200c03040351042e40751103000c0051034080d0166001494004c0c0b41c5000e180016181c19000343c1c440f49855540b01181480031a0320450075001d08484200c40d802000d580f12103107841801c841160f000c1c404c0701300702050200440c01c86104803103982540001c12080d0803000354086000a140329150b4180170b80c50300b8020b040d214035880800700e02152041041c00d00801141450700320396041300302a105541803054010040a1000c907a07800100182c2894564492245080100c0306014840344 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 744370854 1250 744369604 744369607
    0x7140f030a1806080106120e030409050a052707031704031b0915360203090c0a1508010b16021003051e0903090418060c050a0801091107151808 63
    0x4000d0001810b048040c0c02241061040c40d4145040506045030382d44000d070200b5101c0c040b05d0480c02090040e10028200c8000512550410040c84005400225281d902e200b4181c0345850045090005c0036500d9060f04000d49005d130b05540303904200702d281506038480c8440411002000620b0784208141c0303615028202601745061103c041c0640d4145141c100c1c640202010034000742200141e40ca0b07001c2100307070030040c0c401c1c07913403144506001c00055a80d103114404020008181e501042c85400750304110340c000711840d281e83c808200300c82140e03001c40000f5030107001070158280c4280145800c074641c050014840016a000a86217005041c1110000752208103000001d160900410708141d4100740ea407013540b40109142e85e99020f198081441181c5501e40000d1200266a18075040d82e0041e80900c900200407402525661020301c003800007400a00c000111340a0078441d0354908440d01d240580750820a0702c6180d007484185603240640c9954158920710001c1500d44060028440c40b03505 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 744372104 1250 744370854 744370877
    0x3030c0102070302100509120309010906050903090102070501170103030f050c0f1e0118170c031201051008040512031e090f07050a0602060609040f0c0305030d0f1107140f030a 77
    0x281404900c0303c03445c10300c1d424002481407081d0003003080076101800004a039102e5982028903030241006201c00f5180d1840c2c9011b200c00303d0004001410a0042230f000c80b4500f0780c0e144011642102200116240b2081302001880041d220350041c18902c0003516100d410000c5805d0024242400d040311008294040f510501d021410020b4204200340c902008001e40861031000c2c400100000f500241010500c80000c516010007000750350006c000c0e101100c5e26a401420046a018820b000303080c0704260191340122210310803407903103100b294400090200040d048034102042d800280078422200761510560710005c0740510344074031a1044070002c1c80800c070000002d030700700111030300500d0060070f07107071406d001164000684c4d6411100c2561441d01a50700c40c2802d1402094600000348141c500007000000e2100000280840310805e4800300b042d03100141c8841c044885500d248001d042c1c060203090041800505141d10342500e2100360350451001d1122035045901158100f0003042c1c102001c03 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 744373354 1250 744372104 744372107
    0x3071b0f06080c1b1002040611010f020c1c2d1103031605180604060906030f0912050901030e0f03070c1523120106170702010c051902010b03030c01020703 68
    0x1800000d04840c104041c01d401c040c508880b0b01c0c41980140315540c54251300c100040803042005550082d0042c50131502e5980f9210001c1141c80054000019903080078903030b40001ca800c3c801c0b150315204420041100701c01180000e404001d003035940009100c080107021501038101400341212190f290820341001b810080068400342014900a0081c0e00900c10058a00780c114030040d000c408074140241c0740c08000d0114000046048051038001c03202050001d002500000e1580a0301d42c2500e0600c2030801403d41d44048907290000908201440f520180c0d4541c004d40040030340200615012078030181c040401442c00d180803800503015400010030342c0500441c005408041d082c0411300580080029070010000256506208003c00821080411a0040c401100c00600e6243ca07032641e1903a6441c4090010001e040d09081c94454810000300c080b4410300c41d070382e2100c00607100e15052000003015071143c4008a60300c1c01c155942d480c44400d00f59001c00c05811402c800400159403010503150 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 744374604 1250 744373354 744373379
    0xc0d0b0402120c101b06020406030507021e0607030b06070c06050a0e0a0e04020906030a0b0a060302040b010f020d1404080303131a010b04030b0c161a060a030314090303071b 76
    0x340341d080740d00815040200f0b552480d40e9050403140501e80f468500107081d0305848003081411008040c148001000070b0b010b0340580045214642a800350380904800e00c402c107030740703500300c90100c861030700454000368296000e50b00071368403005c01401c01c07400d2440300da6030501c4001054101d2000b0401c0420b107004582c0d0b1002c0240b4921200ba0761075155580743c040c200c0700821010303000a204401c4800010300580b020808000321a4005200b02442d00b032040b0310000030990781c04142d005a0401d0034a103c01c1d4040c0340c1c0002d15484590003441343c04041c4030304036400c500400d040b00c100007003000000f54451041001d0350040e21000040c4401e14501d281020440304644540483c40381400c0041005c1f030255030603642100e030041d08803421982c0340c06030810107104007107110300c0080c070342c04100c2c0c180440305a14001d07100c5003d0034141d254460008110889076903200042c00203130004109001e946064002d003100ba41c2c040c040300c0c100222a030301c01082111142c094588000409000c0081020f00103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 744375854 1250 744374604 744374629
    0x20032a06070b01030f050109020618010e0414060d050c130218090906160302390c0d0212031204030c060c0305012409050a0611011b0e120c0d0b0402 65
    0x44000e4581851a51040145001440083c0021000c00c42d00e0b001d124003034010218555008002c00e60350300d4080b003800f15002502c00d200c0d0005400d1405501d44d4101807065074000b500c0186201201d5a881c8100040100c02130411100760060070100c1c6210b40b59061700d5145080b90401c00b5032142e10510450013520120380c00709200700a54010310458010102e501c580100000840e00d0381460400800d130080d00c04c4000c01d01d40f41d28003403c0c4400c0c000c951b4a03805054210322500c0182d002d82030065980d161821070f5540d07407080c01006c048005141041d80189104920710640b407c1108101666900c15004ca400358040351020702a00708001c3e66120304d03800c201c0c450504001d0b950608006100134408515908551280003449001480c01504185c0080100901c25042c203900c07200c004112114043c09010b80d50b080c203d11140340491840d507014540030340d40c1c413615040990000c00c200e100100c0d203000303003c1c000c11100c52039588603c1e0804070340c41c0c041d914135400d85c180380c410300c000703004400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 744377104 1250 744375854 744375859
    0x13080c0402090f01270b09010807020a020901050f0118060201020c1c0203030f04060b0a08010f0c1707080c130312080f15060c1911090903040f0320032a 67
    0x4100b0142c069480642c54000850300707103800c02040c091550241a00900c107070901001070f014000000d40030306d0200c02414180003c7c1e0b40e03a401915078107026a80c0e2100701388000d601c02c00e1000140107034209201344100c59401451306120000b43e07021018014551a0080310040c0d4001480c8251007200300600101d00442e028a2a0003901142e402900c0c0e000c05440798904520400c0030400380200c2d600220b64584005141a4000b5035500d0064024600c2d895170b24405400c03c1d005520090040ca0070650720100401c0048143c0d0f11350350200c40c04580101b94038516242488041001c0100441c48005180710394444e81e184032141d0409401e860004040c85000d5048078200044000030030307070a2040f5a02130b600540c56580c0d12007000d0410303203280065254058030b02915014841d001c6200f03002d89806480c6070180b070311101722075501c80c403c0340034100d01c4052600007080003442240781c035500030582e0840441049840c4000908090300c00c0c8020400406856020300c0c13002129002c1200c00c2001c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 744378354 1250 744377104 744377107
    0x21040b070906020307050d05160203011506090f05130c02190f020a0f21053d0507080f100512150901061802031e040803071106070503040f0f0813080c0402 68
    0x30ba46c41035030322200c1203400c0c8204140420038900d10b0329400e00076445240d00800030300203501741c0a0845030701c0c2c11500c21030b000203890324000038014041010003400d640001d0071100c221100926990094000d0040c60805c510074030390040b964000c01581400d199200b03c465100381c8940740100000844107400c280c15440340400c00f045031249140002000741c44500340100b034000542055406c0c048001c44820b0400400c0101c00341c10451064030085850800c15481301203090f001141048480c12541100031801c1c210118a9040241d8189076000880260b06001d0381d4942d000b09030a0407011591090650000c05411407800c00c0000f02c0758421070a80081103c00d2501c00124840d4001c0880301d0450785d40040070483c001d15081019024501d480c140b800c0900f400d14040c2855441184d140000421801e00c06c4441310380420711074002c07001d681d100c03400e50300c440d220032902c1d8000b00d000301c07040c4898a94100009030304c0e502501d54180408450300f01545001c008030304141509000c184110b10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 744379604 1250 744378354 744378367
    0x813080307035307020703030314040804050d0c050303160302010c030908030c0706110f04420c0f03081e06130507020f03070c14060306030c0621040b0709060203 71
    0x10b1901d05045102860b40000070f50301d900100707201c0d0421140004014110980100400650001849007c4074400d075000c001d034140c1542d0613400d001050300c004100b07600400c07040116180c44050a40c0b018050840e506810b5640c2c80003d2859002400d141e0504001484100505d902881114094461400d0601503180d6581c3c40c0c2c1206d100003400c00e0800c01c0c1c08940c1201780100c9a100703d0411081c0e000c4a9030300e0444160182c5503401a11030340114003c54603d034440c8420300c1c0c0c041d004180d07120980c00d2004e4880d40c121103c501109802c141000300204d26a0041941d0344803824400b4040e854140d41414011544512401c17035001d4411541c4114060003010b03203540442d80c050b00c0d070300040041c464441250407402d01041d081503101c0f901c00403540400f4801d09000f1881100d044c0104111507000041c01c1c042c40740401c0302e242c2d60507000843d402c1664108500145400e01c841c04680c90b0b401c0000c102c0c0440a06c0c00e440c00d491190041080040765608441c200025103082c3c0001c609254 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 744380854 1250 744379604 744379667
    0xf050402130c020c13140430081501030905012d06051f09030f0305030a0f0b063108060603150c0d2c0c0301150b070b04081308030703 59
    0xc19030a070070790280b403405e0f4003205840e140f035010043c40d509070302000d59542810b0070b100c2d204e5100000c240550f40050740940c10150086482424801415200c04004d591003d10019070384110351030307103414940c4450b100c0380021420711440c10141281903004018441c1507140006285600403003810951401c0d00610055940e00d80c44103040c40c01ca03003c0106d0b05c0c090704040f9000c10065000030f10a4403036a00749010980c0100103180325458100c400c020b1044070b0050403050f50306a41c141a04900200690303410a8900c410390f20322003c55003490384600301640000340c1555075640c409211070308640184423080c07509020010b403014660b1000c1d0180d05040c030080907644150300582c132005544071002e4070b00d070404c145072200a4488581c10f00c1c0c0d000d040001c1917200c40b50b005c01240300354038022030540c0d00400855803900303540c42004c1039401c02d4019070b104840c0c40320143c0199004130303042c0490503081d030400200b2000791582d10090740e1203600500e00540300d807003440e144064502d041303200d1250302c4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 744382104 1250 744380854 744380863
    0xc0809030d0203060f04110c0613170a020115060207080f010b0604151e030518070f270c23030405151f030605060a0b040b030c0a020f010f050402130c02 67
    0x520701c40c800140c1e41d454100c00911008040c0c0c4140d5002400e2240403215030408070050240d070030400054610301d40c0c425884519111440c0d1000344854a142c0c0b84121600003640a41001c0f0103900000412440d050b40d1440300554552052005034010b0500b0700000c081805100440440b120084c00264050400a03a01e40600d002d010040004c2680c11009144161044219401c0301e005045501028081c0140a03107811501c80342d000c90301e000200c61408c800a0014116900f096000a8003400c0080e00999070b80091509800703880c901140c000c0201561060100c036940c951580b15050021451500b5201c2c4403100c6000080c07414010040840e0700880c4121100401c000c606c01d2075907951560991003203048110140700c1c65003440110030041c55500c4140140c00854802c0400c81e580c4040c90440d10444c09444805030341031011070f807071381903c0f005408400341500640d801c1c215591509400c5841c8481c17103c10440d25030040c82b003907080801c1d420402e403481403020702002c0c0c070003100a07659 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 744383354 1250 744382104 744382117
    0x30506091602031c15050f010e060c011104080307050d020a0c060c0303020409050f010305010501051e09061807030b010e0105091804020f210f0d020d0f031e0c030c080903 75
    0x100312001100c060003034420b0007190701030b001032118103640520141c4c2003401029408040c2442e00351420b80800d5514015500d24881c4005a440360600c40740c00d41404000e400280b0521155034070340c8210800c450001c0098405000e6100c011511288036040c2986820000c1150b0300654200000c8200401d16480122054500b1750030000b4050328580340890092089a101c01c43ca5842c04c810700c000f4603070101c8060f040300c0c0601c0090140d43d1701d074401c00c20352000070113401c040c0c1c0300c001800f41380b18101014101e0f80010010402442c0c00d08582d4000160441242c000300000d6aa480000f110340e0001500c09008000b07192160801400d071340454105010b9a030108030000e1840e00180443d6030b07861806a182c1e5000e0003188503002842101e05000e04501c1072003100d030140c80c2c2c520003001e5001810301c03c90400b941c001c2904410031001a0345081c440c2401e0002c2603150304201200d40c610540b440c041195000340080d549000c140003d00703c03105a80098104860301c42071080e440d5000041e6000b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 744384604 1250 744383354 744383371
    0xf040803090310061208370f0329060c0a032c0d060b0a030c08031c050f0609090c0406060f0e0301060311150903011b090803091c031803050d030c03050609 68
    0x580d0901d11003180c1c68140c01507841082d5103441009141c8541510704520003184a81d1500e5541c804071000540990341d81c0d5800d610f6214800c00110521000d41800ad80c0449014080a190004442ca85818844014016030100e55200c060340381a07d403a500d8059694071080030388100b038820b9800034521a0750790802921032501da00303900540d592950089402552301c44c1d40b10380e01c6651a0aa1900c036004403202e080341100002d001c52001c02c550103542e01c14008581440641d507142c03410840d030300310054001540c510075980a13003869103d901c00c540c050f02d582d0301c4118992010701d100800d820791014005009906040b410000035081e101d002e0340440c022100c602040c0709034078aa002030301441c1c070001d5141d82045030070040340b4600f03d0320b44950749150f600d9260168850441550f2031195540d00c03504030450315885040700206040d0769000070b201c1c0c6420a204440140c000d0044121a002901e80d5045100c5100800c1c0e05403087d03104400d9981014011403800400040d8510030003050480e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 744385854 1250 744384604 744384607
    0x40c080f120f1b0d2d050a0807020f0706090f0503060603030906070c0f0902030105040501060c020907031a03032706040e15150d050f0a0903020a02062d04060219050d140f040803090310061208 84
    0x486940c001d00024142f9400c801c201c6481c40c0d80d5900c0282031542a03c59101450380a00010a2904000c212248244805001035103030510b130303000b0700059a0202c14140c0b1701016080002c10343c015448240c90040008110168480d4146070820040320b8042c3d00c91024400c1d141c1841c8010384580246030741c00580c50400081c0d4070707603a00b440c80781c1c0038400d21940d5160000161080e4a0510310010102d850840c004080c0014181002c1c80310301d00c15401007001005420000130581855846103d8010130b001c1c0c5500341d2841000942469038010543c1c00c0d001984802c20000a10f0b80d0340b1269922002c124018403c0072819100a5145c68107108003a0084d5000542940280400010000402c0c5070035005500e408102d103c40c0e0241c2c001c0c1c040c0800500030108411307407071207030300e1a2040040d8010000d064082c040200c1a00e07101d14030111080100014000090308842407000313800149107d102a5568900440030141003251110703000c44400d19000b014041c1400302c05110080e1907021488a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 744387104 1250 744385854 744385861
    0x604050403030b15040305060105063402180a150b0906180604060c050f1f0b030c03010f090b010506032715040c080f120f1b0d2d050a08 60
    0x48010304400700f070a0790000300311001e020401032648020000c45c1c2c012425184103980711000c01a580c412442130a6036a60248075820751102d0281c68251400000c441c00903943c0f0721680400c180c3c2e494030508125001c204000c0190300800c80c02906403e0070041c11120000c1e0910355400d049014103590607000d040c001c2440c542d050800784001442130402805203499903910503000f4015110300320110362501450b4050211904000b60180e01400400c0254490452050481000703182101d03455030b0510800806a40e980c0b021312426151544e440d034082000441c9087c0b080400c00c040e0b02903400350b003040040021044010440300d103848072403011800d825005200c814a0500c0d02c50742810f010340780106101c03c0001d0214090111901041a40c402181c0b00d0600f6448501c00064403101180400c030039a901d12441c80280b01441d60f450803004d0220103400070300c1c0792451030f0075804003290072090b500503100c54001d03840102c21000400042c2000c6003d00040c40b40c00391409410901081e680803 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 744388354 1250 744387104 744387107
    0x120904020403061109030d030911010e0d0f03030c0e0a030206070b0c0c1f112107032307031b0215130209072705031c0306150f020c010e090604050403 66
    0x1281c008642180050280c2d54600c203000341c1c194411110107100344501215002c04038000e001d86c0e0340781da4200d002c4c8201d0303020710001500c05410388605039501c2258041c43c03034001403a10030740140c010300a507800589800e800501a040e0705038200d50a00c141d81c0781c4d41c1040180c6c3c40000304c0314503035031140c00700460b9102c0c484c800301c0c540540b00c1d0320791240c062208008400c0c4803d081c00e02c18490150360a02c440300020351030b0803141c826150000182d603107050074881e440c1d0441403032940141503490002101c40400c0108078146503010450780113075030305205128605605000b0803241140492240350784000c0080069560440b10883e613000c0990040007402c08159240c00301c1c0c22540281c215062440e007a070005100444051038101d0340c112408030248480910300e603440640b00050001e05c00358589090748204814a071128000300345d01c072440810864490000c0c00d80c60035035901e80580e00218840c001e03040c103c00d211840c0c1000805680002255290903940341c2001096500241c661100e050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 744389604 1250 744388354 744388357
    0x201061d0a0b01111516030b1320130e062b02011202040905040201110309031b19080307060f0c0804021e040c0507022412150306102612090402 63
    0x900154174042c1d480c03503420f8003841c04000c5200d06030340c0c20f80b1045400a071109400f01c503540b0311016004450351074014030124895100c2c00d0701e02c003859510f5200800b89000522543d00040700401c0e01c85100d4003c10840032000c00081e0051011944003206c00581c0078840803904150401ca0030845002a521040d640200700c480d07a03840d080902035607640c1d19168075001404041d02e08a001a0100039042e503a000040103848800000401400690b45c002c00c1d00006d00401d0500d07943d0210840140746c80e0205603030105001000c0c1c0202454440005e420311404840704042c00403c1c59092080040f220399010f41c01c140d00990403102c4c1c02d02e01d003405545039024103072100c80036002494070104840c0075400ca406080814822180407030600001e0100704404044200c01c01c00509052140c58641851481e041e644400000204840c904000e0002032602009075105895030b020214140005507842040040140b0100c6038940710444130451541d8034156003179010800140402c00d8001303a43c1f51740 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 744390854 1250 744389604 744389627
    0x3506070c0f03141201051f1e1b03091706040201021507020a0b09070f05030a0f020d170409020310150c1401060e041a0723030c0c0109120201061d0a0b01 67
    0x5a050b40c03074030401c512907101c002e400c2c01900e102d049407600c1107001c8540030b101003002d5111596004029998000c14592400c070b080410000c3c0000ca02400032009c03031040700c1c0c102072800399907404013042c6400403e103221104805d418031190000820000540d0300000d29100c0c0340451012000d2a41ea0848100c1c140030401000402d0200307214180710100130002419000c4d201481210301b022651101050350f5000142d500801c00c10200d00c0740000342c43d164030708000b494007a03516001303140e200301200e4100c1d6100c0d411019025a01106014900c500c484140300502030207405100020f203210b102074410301e26424024049113002d0300b1500d03420004e400000080040043c00511f9081c6890b00b400002c480d0050500ca10800c1c40000e91b0140c4117030041c4001c0c41012912240c81050311040250650005085494425042005640c045001d100c1d00b400c07a40031f00e000d140f0440304040000d003940d98507031010880b1030044031140c906040a02c2a5a00a60f06135000140c0e00820f50050700d8090404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 744392104 1250 744390854 744390887
    0xd080705060406200c1020040b0d1d060f0a020c0a0503030f07020606132406030504050106050901231503190c031814073506070c0f03 59
    0x3109000801c8040d421052280301000c10444c440c0c50811038010701809048004c85903688043c240d403044940700c0d40890510840c1c210041c0b01802180a180b0b02079004d5400030b88a188001703442c00c0030808500c2421210342100645d2541540345440482e130782c100291803044905841c1011039410314036981100c01802031001910039800c051306151361260411100c80c01c1c140e08030b10000b01c0f9144007144091141000909610080040242c40c1000303100d2000d00c40c500f00058950300740303c14a040a15401040550ba01050714582498201d094464540c401c0e030091401d40014083c041e20808500c5550326170b589001c44031074650001600d01991440b5410418800105004d000900e04440007a0b1400e50402880a1950030500300c00719401582c50a42c046221618840020f68000c0e02e080004040411500c9040d10307250b081c900509081c4801c000e152400c00c204402e40c080100b0200e84260480190030729151021020788110030701c040080164120f03114560402d03015090000300c081c2017 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 744393354 1250 744392104 744392113
    0x110109090c1106090105061503040302070b03010f030312052205030f040914070f090303140910030b04060602150114180c0406090b09241b01020315011407020d080705 73
    0x201400350b0445940744841401040000755041c03405005031401142c024158150086040000e1000758002030800c82c114020050700081d0100c60b2009103001e8450644940320075842c40c40e018141c00210f441101409040408003c0d0b600344850701030001501c00c43c28111102000d1400c10709500c208206150f0507080803401044c950000d5000628080306614240c0310340d120300c002901c06840e5000d60100080d2030090a2000a20072000344110726a640c0b507c604062140c4c00060200410120f03640c0041c0d5260890011448c082c02844000c2c819030020342401d41751000003001c0a1014003804000342d100411604141e11440103030f0014030b08080024107281400c1508184d981d01520840b000240503400c003180c0c100b54641150380361440184004103c03151600d884500301c02018a0b059000018011440a08421000382e414a5443e00005a030380c0b401440c201544000e808500d410800e81403c8509502c5403a4104c0d0303034058040f5501c941065842c13400403118070403600003c205014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 744394604 1250 744393354 744393371
    0x50c0c091302010e0d1104021303120c050d11060a02070c0e0c030603100501080312040c0b0f040e010b07020109120807060e1b0102010e0a1b0308070b071404050d11010909 75
    0x400c1100070307035440c400d0f82c45503144030741001002441182c208020340f03081500780d440100c52074543c2c0206070040c032051038601142e9480c1c480e840c04442c1c01c8001000f08800b03c640e0700402600f071140704500f010506101e8031404040d40c40390b40d155402440e424080d9400612402403061080030320380203000c80b540744001d901c0c03c480750004540007070314028002c1c8520f11100c02e403000c0c14000c644c180c50404d0000c60801c0810256100c03400c40103801035580d0010034070701046e100501d50060280000380107005039901e00c0c1100c05000341e14142d022030031620f8140203100042c0c0e44200c00300104d078480d007152850358035541001c00007403094000040401d46040c2d1117000c8002c0116124511040c0801c040030b9131030404005a0a80d0503000b8032203029000280c1500002c0c00040d0618091100251131396a0185c4959400c502544070b1b00c41540c131401d01c402003040403907100c1a81c2c100200045980390401e854040442d0b4a4013100c00d000784000d960b810781441c7c0340d00c994080700042461b2a000d000960 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 744395854 1250 744394604 744394621
    0xb030c240d06081603060c020303040812060f0a14090f0411090903090a12061a0609120a1712010602070e0f0c0706060f0f0e0c12070c141e061006050c0c09 68
    0xc013544401c4a0b42c60030240e04421283c0084284e9101d5a00207941a05e068080c003000d001520008000030303482800315869210780c3d1a18031000020705002e142c4050808040390400c4002000200711141c071090400030800094001e1800040c640c0c4155074500c0581c0380c25580c0f42c00c602424591503084203034028001100380c02c40c054103034014058482000103100b080d0100c45000c5d41d4420f80354002c90200030300c14807828000b100081d803510340c100341d44580b4590b95480c2e01e030200e141254224030030045404120410b5070140303d40100a00d0004040240c80d08a0020744590700a00c2000700e1480703280055035400305074045407a544e5102c541082147c2e02c492035210090018082d02d0300300040440c010840790001c800385030081c0b2681d5407203824003103991603003064014014403071010826102c940e040040c861038078516440c0c0c00103004d011013811140c00c0c01c800d0004829005641d500250601940100c9800480c05079078880c07030455541c0141403046071502007a4070380c10b60401d80301000c10880c10f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 744397104 1250 744395854 744395893
    0xc0d0c0212030c0705010f020106050a0b041410080a090c0b0d06060909020a0210050606090a09060503010b0d03120e1e01020c010510031a1314010b030c240d0608 71
    0xa803007225101d141d007100036403155803405104080301c0d450b07001c1442030190390b0264545141c104414400401c52548031000700f485104039900c2a0400c01011400b840b001e1078080754806410400d6580b040b0300c0b459264000d1502c0300140250381200c3d07860005805100d0301401d00c50240500a08803507a580c41103400c4401820148207400024081e0680848d01c8a654000c5a9101c030840c0d0050059a4814140f800140340141c202070380f05c0000c11900c0c155840b11030b031044c0200501400051300e20f143c1000d05080d64058050b0510510b41e0001c4080069001000e40c10140d042d2200044d503421140441450903042050151940846907104521050150000d0803d0000c10f40240100d0301c031401c04029807a441d000080903504c02a801d98035152844404a034881d8a009542c40c42d503140d600e403190006021070a0f42c003265181c03002000c542c00e0405c18080e1860050f84c6540700c0c2e00203061207102c8d0100c4421850030001001510108204041c0c101d44043c00407001652403070038000e00d024185 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 744398354 1250 744397104 744397127
    0x120c0e0103080307110c01090513060e0403050c010c03050105061206150c0313150906080714040608061908120705011509060f081b011202070506070f09080604020d03030903050c0d 79
    0x14030380300320060310380344c0440c046001d1141a143c0c22070513030402c9c08000103805c001c03581c1d1200c1641c3e140c000640070248a403c9000d28041d1300d4078be039540719510b0801c0c00c2d501c007450000107150405004101548030b10080301c690800400c800e482684078007000030304541c0c481c0c4840e24a40004925201d0034040480100070f00d0226044881d4900c0e5658403040a03802d02410a201041202004000890150004a030320078070518009130480b150b0b03d10301107144c00070303004440020400f004114480c20428814250301030010303018820343c2d152240c03d6070385075080001405850400710b8900e04200007500301c114a03d0301805d000078a0303601d9900034001000c581c07003082c1807610100c03000512004041200c500f0100c5c1da040b1314003081c2c007040c01034510070b20020034034503003907400c03c072042c040b800510580b03001d4800e40e915050710782e11a4000505003000c60b0400b44031500520305210050380e41030750580d40b059040c2030120742e4500b10708007610319001c2c049031007400c1d01401202005050388010103208 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 744399604 1250 744398354 744398357
    0x130213230409110607050712050601060e0607050c01050f0d0f0504050606010f0e0910170c04051b180105040e040302010506090f2a0c100e010b0105090604120c0e0103080307 76
    0x10028480e10401c01554042c100142c24001038149049803070900400a140d081d008004982e10311365981c036440da0b00300d4031100550b43e98000f2001070190729403044c4080800c450031a0303150b003020465100d080c3c07982c2c545140305e41800400103152604105c803609683e04240860303400c020041503000a00081c2c08101d5088800e4025a00050199801055142c0c1c408071b25981e41250341d69000c0510a11a102401c0c00c40d0b21139541100045c0360010700d0007281c42c13400707000180600000d5241400b050b01c00180a030a5143c5105d803100769500c2c0d2a1007501c08445002e141d52302c50704500d1005070341b07902c15504031058007030b2420100401d242d015085a4010201038481c01d87c0c5685a0b845610b40203019103000b00c08031084200d6200e4044100107282031021148100c2c2e10700400721a40d00d1404a100c419002190b8036103402a1b451502846051401c0e2030a0030158a01441200020000d20031130044c3d810132102c8034099824480144030b000054001d4101c2c40f4243c0d6124209590642c00c1118440e0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 744400854 1250 744399604 744399659
    0x11071406041e0206070f080a080c031905060f04091b0b040f1421160b0310170109020a0902091c1709040e01050c040807081b130213 58
    0xa0448500045052145402003411010000481000106000d00100c10707a8040400c0c40b0090100b100c095503040e00c0d5100c0c012540d91074031515009817404c04002c2c90402c10250038400c00103802540b40c989074880140c1c250024850340e03020001811030068030fa0143c1c00a141c821a8001c200201a0100001c0744051b002c2e003060384d803448020036500c5140908080540c0c042d004100d2b041e2450038443c07401000030034032050448101240700c2d800204151191850303003c15613060305076043c0b1500c84058152815000e01d1072410340b807c19440481440b03504440c00f40d0001450220b6030030761003030440ca9401414900f00c1951030015802075040350351010b100c0c9070b02d20745c090b842d45004450503e1081d0301110000b01d8401800009000741c0004e0000b41e00182c4441c0d60f00c1c076504080c81a40e1180181c24001619181409901441c04c042c0e44c10142035a81303d000d5000e0103019607807584404003800c568000928142202d2080a40500016100382041e03503540880c0120606800119900b003030f01c40c60303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 744402104 1250 744400854 744400883
    0x3030302072f010c11041e0c030b06120601020f0706120b030f06010e0a020912101b080f070c0812040314071505150306010b09091806060d11041107 65
    0x6100c0925800030403030100001a1028654003411301d0b0780105025020a14155900f00e010a040d1000e1002c40d0f02088800805101c0d642c0d10f51145201303262346894104001040140814400d00c50a50060318446082d00081c02e507a10800c02007880041003400d03190401d6450001501148074002101c00090800c034070800b090400044402450041a00901150340303407240039250307400041c101208042d000c02c2131200344c5e154100c100d07640503030071802031000302c907100000070803100c0c0c60204c41e00c0065050500040c0350f0740445c0c09a040039080d40310105544030030030240d81010003140d005140711008580c00042480d4041c00612035030080e220400b20a186104070001c80c4171700000142185d00d4000d41c1034200d03c0ca5030041e80d00ca40240a06161102e10307070006440c0c44e000360b0002411030400100c80c54641400d84d42243c2203201c40b00121416190b00b440305859a00081c5500d004006030710100c800d1201e011648508104041c0007044525078502001241e0f90041000b0f4a6048002092 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 744403354 1250 744402104 744402143
    0x80912030c060717070f0327020a0918080a0c020a08060f0609100e100306090503071104020405014b03150e0c0c03040b0a0908240a0b040608070303030207 68
    0x82444040e03d42c01c0c1070006580d40c3d0000c0e106c001d0040b801008040da81c03000d8411244580100249100100030021049011481013088010650b040000b80c0e90800044c8500e0880b09400d404215078002e550503243c05502200700d032206080f00f000781d4012140d0000007441c440114055000380c020940030825692104280008072400350380920b4508041b880422070001444001c1d0707080302003000b552032220369940341c03007064402174501612030381c10026158082003c001007601d00e1410654040d400d1529060010340004198218000c9400d659852801701a1344a1168448500c10045041112110343c80500c0801c488640c3c90340032034a080491000c0790103030070130384007201c0d501071222005035680c000c100d4140d00902c034500283d10003800007049a032525405400d10742c3c855901c0c000030501e03181c1201d14204508884001e00c034400c88285a0385000c0944640c2d00201c06800414103902c0c0b02c01250080890754022102401022400310030140c0c140c00a2141c0f90207441c000a000041800 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 744404604 1250 744403354 744403367
    0xc0c1c020904080a110105062b0c081c0e01021b010c0203010c02060a0c230903030d06060507121b06020c070b0301031110080702030304020103110c0109030c02130b1c080912030c0607 80
    0x1c15a5200d402c40010103c0182270703002401c403003501c4440c00e18400455541d24940140c242c1c10011041d0403485004000c0d03644001e44a410035007529040140040c00c00000c1d4688401d9501c130300f801880942078181c9a40155400d108140d8013034000c002c030803c1040001d40380c000988210518034282060061740511070850380c50030f4101410b03c06c44c400e070301e0880425290300c22140d407501400107000b060303030315280c501c90313140140146d0f20b45550b561036518040e1845116011a01c0c140612421482030919500081c40ca52a80c00704006945000c4000e031149820080d03440700144550000010040024203200142101d006460b40907004902040946403d05c1c2100c10000590051000402540c070903080403228820342c048041c500440002010b0940c4c40304081070300414641c298510450034046004903c6503e250b00070480040000c4c000307101d107540d0118510041c42c40701d13161713401e0105080840300c0c0c0c44c000030b1034150744071015442d054513a000300110b11403901a410028060030301501c0d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 744405854 1250 744404604 744404611
    0x90503030f21010602070e0a0204230f0a03060b091e0f070912110a08031c0b120102071b050f090c13080609150108030c0c1c020904080a110105 63
    0x14003950400c181049110566080b0b00458424a1220410000d510354604000d40c0600141e6001e040c0c0c0c0c1c2d040507400311b03481d034020b0300780034105d171042108204030800b1004804510320080041c180000716080082c5180e01102491980202c8040c00041040f81c103602c6442c00400582cbc01e005e01e0f079120382d24210130340ca0700030300128a0840040011800b507804030042ea4050900e00b4072804494640c450441e03512550781c005c0b51203000702408407200749003c0b50910b0003002148021890060b890f19410340c0260420110040c690702c0b510740281e0355446106c2480c4110402d002191900f09904045024032900c0d0b20300380703034a019100c1c0441c007814002c100c0b80d035900b409000201c2c543c4800700c058040d544264444048001c180340301044215092100600801074030f80180058030061807032030112481a0302c481c5ea103034020885000034080101740f600403103804640300441c0b41d0b80344d00c1102c2040c14021000b94403d000f4001c2008100c244000703021210615a03489400d081c18030715a500300c41d810b5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 744407104 1250 744405854 744405859
    0x108010e0d052b0212060904120e0639010c05070305090d021f02010f140610050408100c1e3f050105030c010203040f030303150b070302010c0207060905 67
    0x395207403141c40d40142c00900c0203180c2d207036900750442814038806030252000046128042e400141c07500c000070b010100d00390003074811942c0350000d040650b0b410002c804981021424001c0f4030214030700c182e44403402e45820059083c086004005107402c400480603030100c03100c04298030242d074000e41c1340051117818404800d07038842926060150f182a5080e800c000d02c01d52b0303c0400305200c070005807a045052400113080b05d05501011a11203006400e50b0f84141820043c03610f06411140c00881c41c16007682c20001c00d6961000488803400d007280d80b44902d40082c0482e2150070844403400c401b03a48040c5480380140c1e100b100c034a8a02d0314114010075400000000101104824600b0762110036110000b48515441800e241e050b251410441120f0380c42c030000b04596030001000281028098444206002d1001c1c1d4503050400a90000e0f20aa5000240816688011402030a0104804000a40b40f50081a511010f1a10703009000e0068104402c005000307204001801d0340c0118591801e0b80c500 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 744408354 1250 744407104 744407113
    0x150f0c07081204020a05030f061005060f030c07030203120f010f0f060c031808162c1614040306020a030e070b0a081506030f01060e06030c0a0f0c0c18050108010e 71
    0x1d02c200d002100e040600140d0340306800142c00140c542d0200f21400c1c0611340880503002d2443c0002c0340c0c010540d0642d100034010a01000469040f404010840b68412030003c400381d02c0d6a89400c040b49980100382600004000610038403031000d660f4192a8100d07100726006080032070b101d0315071040c00342d018441c1300007258030ba52114000a014004c01c5000e90217071081007185503030701d88146192040c610503078904041240f4081c0702c0d24120908802848400b8180c40c00301646c07003c3c102641080c0100202c80402c840201e4800301440740c032000326200c10841300c01d41c8998403030610350002d520522152001c20314160411300d0101d0003142d007070122038466040c281450324081c130580f1441030040c90480c810b416503410ba0b60342d5440502550040c070840040b02c03110344c10250064010382800040c0f03032080380306008009441111404417240c01c9050b1614200440d040e003015111444100c5000b000b0807800d040100e410107101c2056041c4c8000840c1c107010343c3c3da99501e410300301c55040640b819517401 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 744409604 1250 744408354 744408367
    0x2070f0b19090c140d1221140105060705010912030e0d090f0603020c03120106022104140f0f0d140c150706021303240c0809062403150f0c0708 63
    0x19180d0703088010030b0250080c2452096541c0f160304100701c8411b1800455052515000700307001c00c0740180985644035070108485a00b0207030700000200140301c2c00344a0803001540c001040070a4110001051780074104042c20f4012070b1025001e848140c1c14082248940700c1c0c40c0041714464100c0904649400034140c0b541e03424500b044000c1d5104081da5030061000308181540701c001c3d41901802001d0980c068850142448c1e60945452010b5a9107540c081041c04103100d500304465800f0f46031a8110343c4942e0b00580500894100440e003456076a01c14400b030950300c148000700b1103925070030902c43d05840c0405c5c415010040d5881381346c0f00303042d1111424024400011000c2e401001c481d4003010101c089a503890350b840200349403000101000080840422040d0b400314000d484100c0454140307000a441c0052000ea0303038807801002414180103151601e4402151002600640d02c406800c2c1d5420204500c00011703c908103a408490700c14034080001c810945c0340081d202500c3d40305400e18a00313007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 744410854 1250 744409604 744409619
    0x6090f10030b092406150406300207030804110a06120e0f0d090e10050d060f1107050a050d0f020303040f03090e091b01030e0a0f0602070f0b19090c 65
    0x40004040740c03014480d01ca0f000908900004c1c040c4a401c590b0340c8081142e1400c0d1003805800491351400707540098041c0001c0c00301c0c1c2c4d0000e0038030324111602c80c0e50721106081030842c64003e110344446100310030b00c001406010b141d0b001c03048900c141c0c00f4400310500c17001c045d0140a18800b480c891240010340094001c0c901c45040d402411001081c0030488103d10325103002c2d030b400c1038550900740b00881c3c00d07014200400d601044205a01c104800d100540c1c0d246090085109070f0300c607682c000d100035920400c4d694840103d5000390b560071301c001701c403e4441035145445942c550303031420107403070b144104d001540c0058864907140503403203050782c007660075a107643d07490b602d1004c0001d10481c107110f1405000300c0d98824030030341c00d881514188010094035007024120411104007054117410981041040c102502d40000d801d089603500c44c1058071080500d040950081c01400d400414540000c16104140840904041e0207203031848000307021b04c810325600d03d084a119070001407085041500810012 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 744412104 1250 744410854 744410873
    0x2070518040501090501020a02240c070209190501090605090901020f16030c08030a05041109060a06120e0f0d08010b031603090203031306031d12160203190b06090f1003 74
    0x1d1150b4000f10712041030740d43e05402d84c0c2244640300016030051341d50000322415020050740030714081404038060308000301c2042443c410743e540640140c40070000b0070321013030020340c45802e2900d80d14410007071941c40751800d030081c010b280b00d11407041c1741c2e05002c2040464184201c0780d144800743c00b0149080004031004c151030300340781030580a0000d4800300d1004155508001c47c07092090003000a01460580390001411800b0801c550160401004111244c6c6503440d4a400751401800e0030009410502e2110002d05100c07007400a9500407140011001e03000019120380c0241d494a55880304d03a00c403075502c142400f0444a045880640c003056900b441c1c007039404000c0083c0040c0685c0d1406006c0302c4c080304030281691043d400039a8034405810717130060580c03c0040740a03034500941002001c404600e510741c060f8503441010034810145c0ca0085650030840000c024890041540c440180c5082c0070141141c21a0800d006a442c0e0000541c1d91108400d000c2c82204a401404003640c2140c50b400c180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 744413354 1250 744412104 744412111
    0x504090213061202090c16110d0c0b0304030e030d050904091e05100f090302060a0507090e04030206100603140f060f041109040f090c0e07090e090303100602070518 72
    0x21801854084254481d180201c5018150f003000c101ca24007502c0c418401c2240c001004030042d81003d000e000c1c0116003400103a2052038101803980e1005140900041040c5451500101981c00306640050f42d440b00350040d40c8221f01980300c1c900c201c88000181500c8410400c0b210002902c00c1042ea421841c1c55444801c03014006c45e42c4601c180282c070018052421180000d40e05688591320380f8103c004640200e444c81c00d52440284000030390360b43c01a40d614405007003500300c59200e1001030b0400d4840c041d00342c010310280511600508103401d000c0c0d1201c800f07071a8411100c000040c003041d450300034026440300511501c04000079035030344031181c88141e1000d0042640a16000100d400c0340c0d80714094003461160144240b590382c45044108012202d000b0246840345090000641c041900d0700101011915422804500c681c1c40c00c07021103800b00a900301014800c09102405072801e000009144908103c42811070f03515185d00d03050341da0b51840d01c1140c0d44a0007a04404003080c0f500c0074005d81 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 744414604 1250 744413354 744413359
    0x50a05040b160b060105090a09110d090803150603100306021804020c01020903013219090b06010e0405010e130c0911031e07080a0e1603050304050102151005040902 72
    0x3081d8952000c0421035000c0342d14070344508a0031000c007042c04906114950000d40908006181400f0030001c143c098100b845054401603545160300b8013100c1040c110b402d07802003076000300301c2803249180c2241942c10030b5840503112001d03130542c4080f82c10300780100d0740500d230780e0110100b041c3d1459580c440030b9400072600c0c0c02c0c0401801e00300f06840e2120300180c06600e00080c0007684450f0010b09041c21100c28405460398920700c60b0a240d60000110b00580c20400342940c0301c3d00030359400d03e00c007983d11901114034400c3da1030001d202041c409503034583c40c012442641c0d1341d0049100e1000300025a4000e010b891841c20091010a050301c0c0140e0070011618451050000c20300d668058100c2160184500240d01800002c10803102c580782c2c0c1c00000301c207918056680c0c0541440c0c00010038103040240090310341e50703540300e80948120040201c14000d441e00c0e4035140c0007907128648540c030b0782c203d440342c0e9002d442110301e241c141800c480200e41c462400000120b5a09150404100280c220480c003641c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 744415854 1250 744414604 744414607
    0x51212100f08190f0f12020132040f140304060f030203070e040c140403080d050c040f060309020d02190329040f08071a10120b27030703030b040507030b10050a05 71
    0x100145e03014a0080c00035000320142c407030520303c03020081d007502c102c078121030758124031910a0120b04842d550203550b4005219281012985c9914222001c00422180504107801800d1030030f808242c00030050003076802c260b50384030311401030b64001d0f000e90000395032540204061010008103404d00364011814585107107010b0711254105894200c60b036105400580d40d00400150503030619105000e207941000750445180d14041c502040044070003810b000b05803c0503210000c910a640c2d495034a484519001080c1c1c089820594010510070000303071201b00c52406288a0800300c00d04600341440e440e03140c646880c55540d0342c030780d10341c9001004020100c8142806000c024003084030f110f01100e40c031408c844600c0070740c18114503044a500721030340503141e40224025418001011500d4041e00680c0903103d1b5001070b94090007074803c4181142c1d400d42580700210f0404103040e49900003c0c00600241c1c0c04120380d440b511011803e6503008a1604d40040001001d4003c0500c14801080c40307440354038089 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 744417104 1250 744415854 744415883
    0x40b0402010207051003200307080114030c1003050601080105062713060609061e050a03090317090c041d03160c0f031a10140d051212100f0819 63
    0x10054170615009000090f50341004900c10861082e90035011a800e04241d42149030104004000c0c54050061420040388107081415640f82041031240240000705080134001103510000c1c000c1c00110303440340c0000d044a00000f69801c11200311013071190356280101c9051031581c950141c80c001c0c014001e412548602c40790000000e40d02ca594040c020300da4138107880f0ba1405030300a00c030803ca80d259a0720000c0e2040040c3c20340c0d80101c06c07a0805051410f01040644a60609941e230420000788520484841c1c02002011800865001003042c01110100825044050500907094074420040c085500401c810a10504840034007240c8511030100c8160f1356440701c1120700612035542c000c43d480301300000d40010088503590070f1940a4000f0038640451440c0c102001550401d06c03d107540607140c00b44e0810140001401240080c5800300e00c0c2684e070383d4070b80380114500c03082200c1040c0c6007490300d00041000000224110304607103a0b5002010700c02407480310190714046640382122117030104400d1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 744418354 1250 744417104 744417109
    0x614040c090207030e3309030a03080618100807080316060b120a0b0406050a2d060905090c0a061805152106040b04090b0109020a090807030f29040b040201020705 71
    0x980e541c03600c8900f080d10040440c3c051b10741c02500501040015030703000b4003808806403000a074582409816250040044c1c9404002c19000e803003480d0f0741320410050200b0040200d4034142c1400440d1140e5044422142e41d40203100c2e124095a20510a01d10076040090085482500002c841050040451500d18040d802944c03828207090030840c1c00380001020042440940c0c80394961091f42044c0c2405404801c80d0382000c0a6006804440da041070368580004040072035101401410842d03400700007034101091000eaa0354141301155108680621010900358420340414003252914105440010f0911040064640d000c10f00f0b0321601d0700034000c45120106544980341e0803600011401014185030041c44261010011902d008504241d42640041e03124420030341143c45603040143c448803c61b00458020045501000a0f0700c901d200c044107000c40141320b5030803a0711900c15112340c0c264440460461761a0010040380034989a00080e021072042180a58014814410f5601080d2076600 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 744419604 1250 744418354 744418369
    0x12090f0d1205010605090913061803020703020319170f090612060103051b0906090d060608030d0f05010f061101090204060f030501110c030a180305030706090614040c090207030e 78
    0x909002038602002414808020b02c51140500001d25080386401e020002180702030750054103a06028403004010740500500303a2020700005413100c00c000c143c21080c10001c3d56030409020592190088076403111030303030080d06840903115510845107881c81c00d442202c10941d4000400d0600050810403080b0041c1d078500c0020000e03a81c01c100c03210f009050280004040341e1004264988103c1c884420300080524103081c0c0b0024601110319a03581c24906011400a04d12070400510050a144001c9030001011000d042c0740001e0080c200030300843e0391a0141510000e100349980c0c1804a1424082244540c44030001d0404590010030100105c0d800306084540c0d030f5100301ca03004400d00040c0208074083c00b0747e144820b00c0310105420001160946604c92143c20714082c18001c00030f03a0240007110104140c0300564015050341d4840d40e0504020000d130601c003108640140c641100141a1205880c1060260707800c801c81c60607003070030142c00300300a5200c03490940c18081001c041c240580e94190717 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 744420854 1250 744419604 744419623
    0x415030f0b030d05031b040305070807050112050f06010c0f14010c0e030705130225050102070b01150c080309100501080102090f06040e151c05070f08030702030312090f 74
    0x194000340200c0802404000c50703011000e0580309402000c6040303185540f04c0143c94000e4201c00181c414803120b4400701c402032045910080083c000d0b200008ac1c80348010417801d08540307081c1c0300c40d940219080395110450b0f604840043c0301034400c0c00480c41a5100b2400580000e10541d0036040b17481c01c52710b4805808030320850010781a074440501001d1186d206201c080266000c2e4020140c0782d09120000c0d04041c080031110000035400f10b82075803000c80b0b0070048402001c0eaa01d51a034400c000d0b05080780030b507204076400c0e00e0754402d5000004407d40300d090000000003c1c1c4d560755548098503a1181c200360702c09010380300a42b055409603100c1c88000d2103042c1c000c1140000040c0d694401d1818080d05114020905200b000280010001d6503030304851941e01c0b05000c010601d2884000b0000303200b890200c01d52140700c4030a00889420031000140c1803083e80c03d1030364a0005580d41c0c0c3c82e40c650741c0c424500000d4242c2c00520a01c0c46880009511b2a0000041c900356000c01710807424103480c081e28103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 744422104 1250 744420854 744420857
    0x9031b060914010e030301050d050106030b04053d0f150f050a060f120f1803120e1c0302030402040612080310060e0a0e070c02090127021911030415 65
    0x201c04020801ca5004501a0800c280b000248041a021204140c40b400140724890245070030301211000c01100b0360040003d19841005c0703c0f0b03031342042d040c61aa101900309409080c01050304681210301d10f500300c0c801e40c041d210b2041d4060301d401920510081d00c00d9100b581c4d0b200d91506650312034541c6155406000d444075030b0050440c24580003c02082009540c841ca060000b03500e40c1001c0c15138030202594000444000c00b240142500703a0301d000601e6010340031200460030103840b82c101540100e40758004040c10006101080c0305042298448001090404000340c0b1a0b8942030514042d0b0041c0d940b282c00104001481c996420722460708011803401114905000020018241c101d500d0107409007206d407800004007200701c8003150f500e210600a170300301700e03582c0400500118841d6540003400740c0d020300900c0380f6503951720b040c00701c00c441d4040c02d080b042010b00080e25000709920030351310410900b603000302d00d50840c040c0580c0e405c0041c41300c0003c00d0008200201e0700b42e02110240780c800320030707 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 744423354 1250 744422104 744422111
    0x14030106030e1018081303081209241b040f060503072303131e110a050402270102030c0a050607030b01020a02031b010504170313170a030309031b06 65
    0x181d0018245220400d401c07005a00c4d1010070303070890341c08407202900795038080b40c055560344d8205d4410802c00200c0e40020454a00005c00144102032461394038000c1070110112150014007004448a00300492400040c1c14002c0380018a0343d22050759011307000d282e80c00c1e054a4151621400b0111111075081200420000014000d08a0303112a0081800c000c0d02841c01d40122041603500d0380344005030150f110500d14180000900428402424001c1ca2010415800c24010714103a0078807078414a0991040c2202c00d000a610308060080740c0841300c00648142d48442c00d0407a10360855158009103045200502c08100d2801d010002c800c401ca0050001b440f0510700224000c2c151580160b61a045410034a030410040c2c40006008030032901051a000c1030b039a900c1c00485543c0541d0703200ea0f45410411410869001c008030040036507850390345e040c1c0700664071498082c1c0030044030800810030707900c5420050040780c400e41c40018114883e103850142e0101e01807942c400b00000103429151a41e8 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 744424460 1106 744423354 744423371
    0x706050c04080a0b07080711030306153a02160b25030e10090201170c1605010b10110712050c06040e0a0c050405060405010f1403010603 60
    0x2907803400c40b01c1c54540d50501c03d140e04c2e015a101c40c0403811860228040b40c2c0305174580401003120308010340c0b46403a11020700940c0f0356082150317100c40609100d00d04e04401c100303440301e17140c0d038240351402104500d1885012444c1a1012002c01851040004040d03901123500f807500203541140c4800e90039940c131403d03010302c1c0c00c07100c160108c031040201524540a400d603010403103100315441280d0220000d04484003c84051700c07806030228084540f590120003400c111a0760184c01c0b60340c4c003418840c56803130101403841c81300b900700c45994603041480c216042c980f0403000840000c1c90312000c880310300a24651285003034000e85250164461100003844001c00c4600d0b00b02d40050a50303582c0c0c9a070b40d00740103003070b03002920041c0c0b100d0305042021400511400590f0300b07403000200360300c2c6803d16010064866102c000d1050307040c4504000c0d484d45480350350303000e54002c02a50310007049208 = true := by decide +kernel

theorem cover : BRFrame.Cov 744244604 744424460 := by
  have h0 := BRFrame.cov_init 744244604
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 744244604 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 744244604 ≤ n) (h2 : n < 744424460) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
