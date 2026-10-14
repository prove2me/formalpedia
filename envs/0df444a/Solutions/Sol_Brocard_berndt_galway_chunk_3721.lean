-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3721
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:29:10.966728+00:00
-- url     : https://prove2.me/submissions/1f9c5ce2-7a56-4308-953c-4623ca7e532f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 669064748 ≤ n < 669244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 669065998 1250 669064748 669064793
    0x706050a052107020c1509040b150a051e0c07031211010e0303040302070e1012020d050102220909110603040c030c030303140601050313060b04150b070b0c07 69
    0x150289040d2440d1103000e208400348811201151a603604902c022401000360380e01340c44c4000c0000f81000001e02c9680051700c030703000c0100308900051401c1c1d446a401c105021788400001d451100d4401202c2d04001d8085012910001d5090401182a812400c0211103446103d041030201080ca50303450f0b00c5400001c0090301c5245030810b1603809404901e54420005009000d00f080801100d0f4490304256411000751141c51400305400340c150500758400e00e4480360710750503645001c5852140c48044401640c1000501c01d84c00b0102d082800200a84c1e5412940c1c0d108040705c0d512444072188840e84180a45450031121744d000a0b10564044101030048a02035220b88890410500021440d800284500e6001c4400810150190810720002030b0441031850259665401950644030803180d0200903102060303820002455503000c400b9002000e000010411005846080743c60101d40003d00c21134400308088080140c0401030315400300c9502030060030008565256001d03041450842014034 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 669067248 1250 669065998 669066007
    0x100f08071107170c090105010815040f0501121709031209040e01020a110709090b041209090c1805030114040b0711030d0c0f08011a310e18070605 64
    0xc501c2058400d106500000c1902d6034a83d4401c104031410402091000c5039000e802c0b003120030303803611000d4241210300c180c442c500d0640d01c040345820850345d4140c000307900596800c091603041700326104d554040c04460b00c44080024aa003008091851261000701c84c84c0d404010182054070b010841048038000100b00d00d4039150040001400381c040c08c100011550310110340b00c02e1080e8050000c5000d07824410540d8107081d01d0b00040420345807030442c00390041c0c403603201040000310305614426180a0501e0601815134507460300d0030a41d11410704c01c50000d072219955403500e280460503071000701400c81c02040008071042403100c0c4541e00500c0585902034580020314194020384100b40f804008005503540c508076620584001c09603036080f100018508004d61801602600243d030603030b00080c8041e01e541060354158185580014002c1081a42c5040d0404130740544a0040e140280c9a04071441c000e0306088080d48952001803441808a014849c0c566000c1000709400c401c1d12403d103052031f82c6 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 669068498 1250 669067248 669067261
    0x4061e270203100f0902010801080703050604021309050f0309010f08060d03050a1e0503150d05100f11131d07050f130b03091c0c0305090405130203030403050f0c100f08 74
    0x203203003c100d8030b1000141007004c183c00510b03055001d2640e041c404d0301ca0f481107903241c40ea1940c1d141094000145550301820219015150843e0001c2425903d080301184e00107080e07442d81d08288101c03110404c2030f44040741a034503960f0032504001d46601c080c9400300440c580500021882e81c04068007805129002a8071081d50b44580400740c26640840d101050801d0307808070041c6aa0300c11900340e40c1c1b00070641c861089526014114a0010380c10000410b0300310030740928040140b1411840c12412541d900344105905401809405811480c84148c917480c0d240074600d00540900e01078200350811a041000813103904075081d6041e14042d010071a450301c0480502401284c41500b1802040d0070100c20800107050000300c51110580040444076030350b81000050310031407144040100440e5081c0541980360409501090703005804440b000400201600460f003554065082603505070400c400081c05517004000082d00d503c0d082c0c030160303148001c01720020201419480d5210030040b000c0c004c60380d03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 669069748 1250 669068498 669068503
    0xd02122b022a01060501110307171c050921040312020705150a0201060f0513020706020d09050610050a0303050403060b0d02060f070203061e0705031e04061e270203 72
    0x2001d14046500c0b40c64000d03556150700d02d8402000e01002e2542c00d189022549501c140d4441c000005580015400d143c150343d15400030013031022050481000502146d101030030400544011702e07580c000d0000c0c86081111a031810300a03070030094043c50b4000103410b1130a8201c00126070480b50800b061407600b400d0000b04a0620000758040da0b80080181d200180310f01d01c0d940200000102c41d002008510baa6582c02d038441c000d588111584400d44c3c2480322000c02c2544c000b00f80f83c51185100614164416200c00110b41e0104002c0e2115400f02c1c08101d20204071102c084c000d014100c0e4007000007851650b00400754811804000e204544520700d4046039118101d401001c03d6004000e140c5580a0a08550302900180800c2c0e201c5d02c19500410000e103800c4a20150525115094140e10b543c6c60000740c805070700240418801150204103c180b00350100c4605014510504001c140150f82c0e29000c201c00100c12054070310a40391003000400e031904038561a0036840000b0410789a440c55000207030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 669070998 1250 669069748 669069757
    0x3020403020a0b040602010c08070f0c06271214090f0102010e150a060e0c090d020d1a160e01021b0114030a0501050306010b070c0b07020d05010e0d02122b02 69
    0x80d04018010000700f02c40341488054401e80741503a0080088001c41c00c07088820707000c103a03a030130301151400d004e0390142031280e50f803c100680103d001284803415645000f036005c6a101d99003115055420250302008401032540704000c06510308503078a0f001200d2424040d1081c002e2091050a44050140842c1d000303403c6444000c9400341618401080261038080300081100d84c044410b242540c04244104285144ca01821440c1048d904192449040c000c401e6503181043c2d901c03005200700000000d150a07c207281c0300205010301201400c14003501a480b000840940301072149402c2001042d0340d000809a084010301800c072250f106180c1c0050301c030540c10189107580c41d407000081181050481d00440c0c12107006600b10303070721a030780c5010b002c080b4014018018940000b4440030070503d80d0358805841c10750b000602100c10340919903211340c01c541780034560300055000a003200c9056601400b4101d10705525003020b81c941b00303400700180c0300c00c004007604180f030659000650158a103d075043e83c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 669072248 1250 669070998 669071003
    0x4050d0c1203080708060a03080f130b03070201090303050703090f060f110706020909071b080f0d0e0c0918070614070b01031a1f0b0706111c050108060606091003020403 74
    0x1d2069048504000f00580c0c002c4400308049500d100c01315442c1e007851103d403401c40b9040002c41d41405450b50410f83c0d01d9120386015115040c1180c0045200e9a00c0d0000310301038542c980000548103441c1c50003800350350b4020585c200741440c1109510104450300500356100354043c20010719000d070114031200801c0801240219504045801c2041080c0d550042c900924101c8506c1003e44d20a1000c444d00c800c440d008400050800500b00001242640a40034071101526050304099448038100200c070098241140036038001c1070500980c2c14403031502d036048a4901c04c10000031100c600295912159481501d04100440c500103c8520084065880302e42d4054403032500340d65a4209824011041d45524401c00c0c02038003c1088100034481c40e6139070b440e6401c0300c00100f03454802259000d810580064800a484032900c0d164100740c40c0003400f0142c0103d0407488100041e001510407201c0503044414558080c02c24403459503141c60661b80c0702c0800f1228144001c4680504401074080c55100 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 669073498 1250 669072248 669072269
    0x70201030b0d1b03020301060f2103020a1b171b0d0615030614010929010210090b01140a030b0406111e0901031a0a050f030f0f0601170604030504050d0c 67
    0x310034281c000503d8481100d000b01c000384403542d111480001c510030a4403640c42004500e1014029144003500c1c1c0d8000d1600030f00541d402e0700311725219202040325207a9400c0300100d111034280f1040740e140d481325100e00700c00030040106e5524055101d02060380a4409485045a62406810402d4a403c06450310071000c000c001c0c02d0396a0724101c0041c01d8142d010210a080c01000401c0840302c81c40740050070303d600c1181f50080100800c02005000005400e141140120b040b0001d07980e01e00e002e28090644140006079541d031500186112003140da01038280b15500b0800c003040481c0805c10303040e4009410401c0000c051301d008160131020301c903103009580e40d0703c4421907a00d0007a80308001760440706401e880611803400309540ca0041811001441e961140e100d51040c0094200900c281006030340103012543d0b6206841040d0f882c1506c40c12815a0310b5003c0340042c0506550011910401141c0c400208001c0c1065a00600640214001c80d806542c101310308070280000d01d110000140b00a101 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 669074748 1250 669073498 669073523
    0xf0e1306081912140403020607020a0b0c0f0c010212030109051302030f07050f0f03060a0f0f06030c210c0b16020a06120e0d0e0f040f111b0111070201030b0d 69
    0x2844080806120b1040c1c41000800104405140c050f8814940424a0201c543d01d0142141d003000b001c1d1300700340030a82c1c01001200010900c4080c4000500d0402d40440007040c945030000b003084e00d0828580c0c1030604641140442c0000040d105083d43d041d541c1e250740104440e40d40d48004083c155903031380041d505100d03141020090318070128004054130416565400c040b0707a010203100e8645401c0d04100c0c1c2680c02900010480d0601d03a001c40c02080f000700d0f0204059150440b170b00199030442c2c00a50300c8401696040103000b0b462040120b144142c400001c0001da0203881d0510030ba9036a12820824202c00110400076151302005104030b25802002081010b8440e20001c1c02955601c00140c031203840c00441d043c6102002640c0c6481c90a541e80d65910307006240b090110b4052941107441d006902c86142c013040d50928040c0940e1450b01c0001d9640700d20401417001941908200654444c1e4507000841080b91a10011960b4907502820b002c44d0803035451002c19492000114060588049403d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 669075998 1250 669074748 669074773
    0xf060b0312070303050f1501030c02160807061b03020a030804050703080d0e100605130f27031205010e06090c0d0c03150b090303070201030b03120a0513060f0e130608 73
    0x30b08a524001d907020003540d52100c1d0340500c003100c281c40d021824aa42989a10190b200750040390751081c2d2807040c0d5071130312020103004011b20003581102955800520307044c084980d0203881e2031010300450800b60f544007041d8501039142c00c0c140d2000380c100704028002505001040126400555100c5080c607036585001e030644009201038010b9948a000303c4024183c2c200b001e014200603158001c14a0404c440344c40e100304002e01c6014501824039484004440346501c080c0e02c0036190155130410381c0300c01c001500d8010a0007801c540641403c0c2c0c1b4200c010b101601a250b00d0b00d030f1054095078400c9590700d40040c6c00c1420f0040004030101503060080164060760f150308003048401030800e0301c0344d0340c1e038684200080314000d558940d0b815074402d2000001541c880d410111012030041c043d1906022210322002c103507804850407030041a40044c2d22802c54a81090000042c13085140000d0191580d05006110300e6400c007606104911400c0f41002c00003095102100810002080780d11411285 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 669077248 1250 669075998 669076033
    0x270503040306051807061d0d050c1516061109030d02011b141602040b060a0c03090e0910090809040c02071d0601020d0c08090603010311040e0c0d0f060b03 68
    0x140402c98519003003001046072210350080d000300c600c01007809072400d181400003c880100032004800381440d689040034003191a402d644200c154000e0021b8a04142a07800303100e0700070f0000b80d2044011004002c01d04a8001007101c0c0b00f8002d9102d100415810b624038401e4800d4001e12813456031501441c0121042c01ea015400070f003e240c14500f82007010312000f9425141500410040c800c010005c21581c81000345940700321240901c010000035505814801180f00d907000740f954480403540d100000300c02d041e08950494002d110704005540985441e015407a21000000c00082d6410386a0f00c15008102800c0d054a10042014008001c07003002c030f0400a6482c0301c01c0c07190344c1015002001c080364000f5400d15592003000f041c0c00818041c08610304c115060712103101d06070b079031040c1884240000c4e42d80500031030007180145514589904141c04100071164000c45001c0240d000800c5c2d56102e440c0c132611114a1608150b840000751004d0506402030441d0030302540d85402281009258078840 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 669078498 1250 669077248 669077257
    0x1050403122c03070801050c22030606080f0f01090f0204050403090b0a0309060e0607081810020417100902090c0f0c06041b060c02032d010525090f09270503 69
    0x84049414680d9142030f02407c0300c10940300e145d200b510800c8910a4140748001285512215041c1e1069246e6240c0f078101c203d84040e00109a00c3e0000c20081d000e501081114880302e5100600070002c0c0c410913a1075040c16480000e000740140d41300e0000405050041e00c00344001c050341040569510415100103001380039044080f181c0b14607200c150b44458200140b103500c40c010380d845da980c2c40d444a526424044a85240401c503901c140c074900c5c8074414550020b0030044c8404011446003400201e0042c2c10540118a0708500d14503180c14240035945a0350440c0c2c0152021040740e5442821010701d81d0540b04403803010810344288000c3c030080080207030794102d078111594012811340c2d449040032a02c05620f0180030b54554031030800749a403943c0c0542c1580002e0300c0f540c51000001440c128503400c0d03510842e84210740014a00c400c00208448008803071125116180c00e40c001d600340541008501d44d207000c0c00514a68405102d141c10905240d4010510701071360b040d4854000710325180d80d90307910 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 669079748 1250 669078498 669078587
    0xc0f270f060612110f030117100606020a0b0901020712051b160911040609030615090915110c060c0d110d05010f05090c03060d1712160e0105040312 65
    0x1400e05041c03020102c0f0b0045d40d25248611a000745507174641900882c12030003c2c03145c40310a00543c0c0c112000c2c0c0740c25126130801015a5001341c031811801c0e090400d02440010482c541da41d0040011302d0000f4410340f8501e43c60003c4c0c1c2425500c1d190f01559050b00740306a03088000841c4a0000e81c580c11007804140308084600250091080408807449a60a4000c92040001007440c001040c000981c031074218024000400e904519080d9030380300c004042e90481003080d98101d01b020311014010b1214042c10000c4c2903030030b0340e80e4074003d54008855a02c4000902c0a5920600402e5500003030030940c10142e404291107080d913444200001003040203040070720032400040b119100004031403c000d41e5951160030340c0030461f802d558880c070500c548500302c0755003280d10108003113032003001e50103d0002d40517110f00048414050b18203040021404c2c010f200301d4000344002c24000462503a804003c40b404c0d241d00803034005035030701c1020040e40c9d08040c40c041c1648180c80c0d1041500d0441e5003c2c5991517041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 669080998 1250 669079748 669079751
    0x304051005130801060f090b010c0206120702060907081b150c0304080f1f0513120315090b06030412090509072a1104020903071a0301030c0f270f060612 67
    0x55032046120700f00d42c82840340a2000146c9401005424590380c0304803056001030401d80c100030501c0c3d001403a91781c171104550041c4507a400c14001c000b94100030156001358a28000c0005508090885640301800d50290020041100c2c040805846d803071242c684c00c00415a200351600b600303c101d140c03070f41c01c51f005d2040d09101d0844845000c180001c2c50361052042d140142002450710700c2c60303101030000113122518810b161402400090100c4101c0c9040181e181c6d0002012001500e171490030aa50741e02145030603040074401c0f1207a42d9424201e03a00694400741b40450f080100c50240c0e80c10b0b01940c000c5030f1055010b020804015044440004c1e0344442014034200005580d01c810316a03c61010054200c10400110220f141415401802c10550090403038190944c0c84113a09044220040d01d180d20340b00c080010010030140341c120a002c0c040d810340208146040c083c0c0e030099080c25140312038661030304003050607803a00540d004003400c2044c14024083c05842d00f4020f401701804240001106 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 669082248 1250 669080998 669081037
    0x70303170a09030f03090f1b1e031a070207080a030c2a230a1e0b0f0a03020a030902191707080a060c020c0a180b061801110304051005 59
    0x152600c10b4890095142e2030b200e005112040d001c6008045c29001200d4048050110001245840c10b41c8012035480010040010703080c240d01c0985c240454103c00c05c0d0814094040c000200010305000b00c104800c0313030480d80343e070b10064203d150561550144250340039440c651418194048115003805006044c404906519114102010320121f1150300d007506590005125074800603004100040403415100402c0000100190032442e459000c60f442601c3c0e41e04c0464881c04024002c0010700c802c5008905006000c0300040551080b660a80708041d070024012500601039840040f200c0d8010b886441002c403c0424100e4003049400340a0310900c0504021000e800c0c0043c0342c50942c0d20703c001800a55105640d40341c007410382500740d0740c103500a038008002241c0340c0c0e4989100a18829441142015403c0030b120102d481c51058180151410044c016080c408000f001c480c4d01020310b00400c0904800f001141940280c3d08082d5202160044080003254408080c2004041108020fa4007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 669083498 1250 669082248 669082261
    0x804050301050c09031b04020c101a03070b0403030507061112092109120304090c050d15050d020603040204091502090f0d020307032307030c080d110c0607031107030317 74
    0x3d0740103e04403640c0c186c2c06043c40301d0000194040c4148203c0d03000e071000d810410b0000c0300d903080003001e4908080c495944c0d040060100e4880c0401058590180d0240248604100b030000b503d00c40c60101809003c400600c8404002c91580203165070340b03030f04e4005519141000ca150080d088166400700c2c84d03110348910f0482018182500d802c41c1e40703a80d41554034041550382486214144540142250302080c80b00003601d500c0307802180c03c3d00140703542e45640c600e55403810300129a5040c4889011321200706042c8002e48881844003125901100c4542d101d50326480050040d001c0440c00400742e00e10262407483c1c40700e6035000b80c8001901158211095078a94007030044900840344080d5041d4000e0ba41040455030560350203d150b4284101c400d00942c00b250140d28000382a070088412460400b810000d22100b4070080d03610591a203820440d42507440245a80c0b1542c0010300303807003400000360040400d40101036128012280c141540d803079035502e040240c80d000c10030829520404008001454 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 669084748 1250 669083498 669083521
    0x21809070e0d0204060f080f07060509091b1905040521060a09170a090f0e060d030f030902180702010c0c030c200d0615050406081b0a0e0103080405030105 68
    0x12418041d40c0d240c51082201c410411060410401660010750390700c400b04034042e5441030321001d0070104005005002d8000d15151130034010f94000c1040001c144070341c0c00e00e6500c211001d03400286607228401e142d081c0f900740f103005100d4444130041110101c001c4080c3c40380c100e0041c0041f660201d40c6490750001c10380030103c8c00e078441c41980744c2c07a80210700010200324056104203003450013280140050310032099090820340c03001c0700c00310111b81d501408001030100f0440303a002500e540015855981401c801081c00f000843d032008041c003000404048440e8445d60007210556001030405991170080001402c1c0e003030041c1c86010041d400c2901c5990220300641048187c540e040e6281103840380c0507102c052030b0b00c503000e581081000001a00111036940d980580d102d144c001d640020710203444921000c0004c5180d40114006d50a10400b00400d40d00070030050600490a54081c610000310300008480c40700903000105102d21040002c410b00140780e02a1050740d0040d4020440b135103a4064480 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 669085998 1250 669084748 669084751
    0x501021501090203091f0515040603080307031e02180a080c061c061d0a050708071205130f080408103c050711060a02030103170f0418021809 62
    0x500c00350480010011a4842c2d0f00440d4401c50348815107415008051408207031100f00b44024242d10b444078280b00d140d6102c0085000c2070b42045500f044250300e182c1e10f481080c0002003402007410350b1000600b55000204920602c0e0240c0c4020840d9038078602000b0710040c89442984034095440c0e41c001040c110703000541604134140050215007048250020b820709200c205101262103600c5560001c0c0510007a00140d07803004148050820a141c0102c00c04102d8800416110800c81c2039428440c1c40b58220020441000120401041a507115803802c164070540883c018418050741c0306c05020301001d00003030415603010f881a14000030850b080d046c2074411519000325800520000d4030840701e617031462070b00c58082ca081200107e258426859048400850344c80b0007007180944010070112080c80285c0e4040d80c80c6604500395411a02c42e04d030608245044c1c070b0614a000212030071303100a100f040d10010f0a4005c4a0b010062030301c002880070b5000207640700300001c1c2942d814075540c507150016030b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 669087248 1250 669085998 669086023
    0x20a181104060504032a121a06010e04091a01090c110105010b040e0702010f0e0106151d12030412030509010e031b04022b02040e09031608031902030a0510050102 71
    0x981882c0c00d5441d0a42d00341000c06200304c007540c000717071024070300100201b001004101c1c1d00031040900300941061038095200500001002c4808010018181e804c00c04001c1d41440582d40041c1814807450310b1440081941301e0000018595000060810913541001c2558045542c900c034004c01c0e00616030382030340c90038040c140300c003c030070301c803d0262172501030074140e0205141c80040f682e04810025a0304845003407009a035565140c00040c4000c1c061644014103518070b9140c4446000d0790004800803c0400161203481440d40841050501c901002901c010b4500e9000c4207004074005e2501070301c01d030302552645000c40c1c214860159586070109000c40b03a6458522004503900810040100a5220721036469026052200c2d401408441140c00505204140710046c3c1d19401c203580c1d03004010b00144082c0e000e50080200b080c81c0d1001400c1c01a40e181c0c003010703058a94480c1050b011501c94922040c1c0b80d042d00c08400c0200c050321603048940150301450890880d25110b500490310b41c480385240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 669088498 1250 669087248 669087257
    0x15020c010f0219030509120a020909151609051002030a080c19120608160e1b0712021c020a30080612061e01050420090d020a18110406 59
    0x603d0741d0892004074030102d8038460b184c003a142c41d0040f40015404c400c1851020000e6100b540c7d00d508505000d00c00e00e130400d69920042c641c01290349135a04c44800018030704007074491480348003200d941c000c006406c058640201503040711164103900a42c1d03600700c205544001111880400c500e40740e2030048a240c10b01200901c49006000901600c03a42840308000c801c2603940c510005103590140180c0301301407140c40440c0c0c0c085150501180c0906009020381d40d446159000407a0383c4031004003150301c02136210704191507400b6202c1c0d0a900313121014031221102c10300d07980c031202d090358046100714896215042a4104001c24883e440c0f10940410b040403426944442c08908240a8410300e58418030050114022114081c880e07400c000c0c00fa503003402040c8a600054000042c440c111501600c030681e030420070701c031141002003000c0f8030080d80341540510000740d807102c0303480e901c4903600e490b900a0305000030240d842035043d11300282d2648101c1c3c0546429601032017007508500f210101e4085554 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 669089748 1250 669088498 669088513
    0x303050d110f0a030209300c040e15070306030c030c090c08070e0111070803071406160f1b06050c0324090606031f060c020a0b13061d0a15020c010f02 66
    0x10290000d40c040b42e80250300c0034a60215402241f040a40c443c5244540c030090003603104109881841c00c0442450700c0d1003541400303080b6162076000104903040c14107958004a0f0340d102e20900340c00503c0690809010b800016501200b8071200c40c60210460b0012101000982c020f501d00f2a1080002c0d44c024000451f040c2a411682d8440e030b600204408a50054914469540107814610345c0414401c80f013000c40700c4400300301d0f60b0007449855400f540c4500403000c1da44003203000400d80d652142c0358030305100504042c4a407100303910303044007000b59100a0410160030b04185080030f81d0400c9a426142d4010001a07001801385070040710301012014040789491348960341085003d803c003c09242182c8400d074885c52541c102c18201d90b00030440c40c0c0b80c203006140e05006200700044c403604400c082042c208519643c484403200d1100403203d039440d000002540c0014040035000e0f10500640d030000041c400850700030807080c0103000711045a0200c1c0c20301440a0019240d000b481c1b500c00300560841314 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 669090998 1250 669089748 669089767
    0x9050607150b03070b1206040e0706270815010509060a05030a0b070c1a07080a061d0411190905091f020a02030904060b0c0d140d0b0d0b010303050d110f 67
    0x4002e000081c4004040d900d0f034a4a91750840d0254200d021948004100c40e410b00402c0e003498810750f5455441d1101504050307003006c401405054072110b1407120719500354003d80140000c2040100a08002816141120800306003401015000e01038284144000c80208001d031818905403012508060094410011592240381d0107001c000c040b90288128030b150301000400c59080e00c0801e03043c1484003861401d2031070008000c8070004006a511624013042840700410560403a00c120302e0010483c1d00176a03444c50a10080f200001c03000307412030070050a8040d04064031106205a503501e5008120981d14417840c00d54418100c820b40c980d011028040c0c408044c2d10350002c1281040b20b00450349012512004202101d8981d404001800c0010480e42c088540a200d140c0d240142850541d90054a08001d09100d100303080040350110346c0c0e54601e207181c0e1201c250300c0070200c2d0071103041815580d480c10050201c0c0d1152100d00c0c1c0182c5480d041c4c902e001c0074030381920180c50024040300d0920881d84c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 669092248 1250 669090998 669091001
    0xc03180f06050f0403020627040207150c090b0d0c110a08070201050711061b0c0d110111010e010e0102041505031605031905010305010c121b1808030d0c0905060715 72
    0x10b203442c0e000c00c9001c103c0400541c0303587e0000c0075100100301c00310301c482c5840d10608900917413001e0b071070344a640104a040003040385914248034140c89144006082ca1f0804000d440c01c544035407002003580c1011442c0c0400714041e501c5140100803940f98078410000108001e030700c6000042c40144150010b000c14000341d482140a030444511880e0717060603164001c070019075540c000c402c40c0c41503580320330700c203264600b02407089603400ca0050b648031034401c41698680344130340c00e808101c5042106a003090500554250002101504a500204440360300e10641c140070754042d028030a40641d100c08990360304c0d882401103a100f501540e840b50842c055a8608503003a6001505070000da9020b1410680c034224103203d4140250700c40d070000a4400c00c4880701424819002103200c460901d40010401003500850000c0c6002c1c0961910040109604e220010965120f070030dc403e00d4031001c201d010008445600c401142945521018070140c1d0f1034041100d548514040281500746020003000c255445 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 669093498 1250 669092248 669092257
    0x10b041a06030c13120503040306061e0e0a0908070b0103020319080d0203070905091e010b04060503151804030207050a0e010605161529030102030906040b04021801060c03180f0605 79
    0x240205103403603d0350303000c680d090075005c184140c4281d0400102041003009602c1000028550f2b13241d0b06a4480181d0402e1100c3d0312144181c0c40300550300070010344030407030540c000b107401a4445d11954031100380c4e08100382001400d02040f4000c0c03203840880c680d12200c2c0350f94183d480780d01079480c2e842c0907080d6803040003035000541000c01340035044502159035642c003022a0310905072030080f20a100c4103240d0a0bd040001a0701000b0f0300c000c108403d01915600c0000c0300c0d44400c2010781c011711520f2050208a8496444c084a0300b4040d520080c8010580c0c04a850703002c841044610b44021a01d681209244610078458a80800c10400007003840c9012444560f512074080c1d03600c1c8045960b090100c1d400d880c82c0d1062010303001450703a07204940c04007906444407440400c0c1c000310300314a0b060001c90340e40c010152001e010025160f0000b81156102c51a20b020240140c0c000c00c05940e503200e000d8110b0915200441c0841e0050a580502c02c81c0e0310280030881c3e8003606200103103490030b8025039881e80f2 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 669094748 1250 669093498 669093517
    0x9060501110c01111e1b0111073302010c0906110312180105040b010e070e0d0f0201120c030204051e010206010e0c09060703050d0f05061f0504150207081501030804090b01020f0f010b041a06030c 85
    0xb01328084071401100103d000d0b002c42b040d0000300766009a04401881c0b00300a40041050040c0601ca004443c81c00006503030208512000d0f804241d15464200c5201c029144400100fa609006c01c0104000c104004241250308807800030070036231100c0e1401c0d50110300000c2d45c00c0c2c00010800061010801080d041b072011801070511190003d840c002400588d5030041151021a80008003000903041c000807040c00b400c250610122800316600000392101c40600c0b4000003000f45401117000b00100200300e030368694005000c540c1e0b4205502e40649960018510b0100851410008950031452030084c0341c41444000c0110800b0003104108001070001c0b43e56420422105200c007141e0070881d02076056981c681a001082d0303941c6005141c0b46483c0e4200c01001000c81854010000645000240c1d416240c0d1001e0104000141a004070b141207291510031660b40705000d850071003040194454610194141c50902040321480042c1d000c24804030a031941014082002030984a81c41004d001d4025 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 669095998 1250 669094748 669094799
    0x1003090209270d11100905030901180b1c110a0e0909101109040608030a0f122c010b100c0605041e030909060501110c01111e1b011107 59
    0x503291401c1610f0600c0d0780003c500414545070002d200000100843c40b80c004103440c040c00b58801c103580700341c0c41b4000c074120035050020540c88904503422608041000d0145030f11450f846044d80402c903c1645107540d02d0110652070041d00345141d96031b0b20100c54000015485040b444084003080c811003600050141e6050b0045111001006220b40295071140f01b5504016844149403810031044a495910140300c0b076100700003907407140d504041c03050303854605c508006031701c1101084c248d0068040c0640c0480f120303c030354411420382015a04c4604219051000800040d10840d081c001400500c50b036100104c2c01e0405150000781c031a8021a500c1403003041c028451107000c05110f1002081854201c001c921401c1047c03007001d1072441007600528091030100a00345955040300d444002800745241007081c0d050305400e81e0942001180c815404c01041c01e2120540041d00c940c440e2070741c0c2051094240c90b003800b50099071148090300c0030402200058503c045c03038544c01d80000c00c1400c03003410440 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 669097248 1250 669095998 669096061
    0x3170c040909050601050405090a1e050a060c02030a020708190809120307030f020f070533030705120f060a150c2004050f01030c0b1803030d0b1003090209 68
    0x9041c0035103010300384680f00510311541004100310544800600301c81c402d6200c0448680850740c0c1a015044110051642c00740f0240f16080c66400e281e80740402510041c200304d900305420307500000400848040d60300380c1e51540c0e200c500d1a43c60311a482e00e10a81c199220003594007040804005110b503500061500c101003c00c074a045003142c0025800f600491501d051050780c483d010302201d01025012000740030814140000220003031113152591040381f030280b00c25040c5010240c404183c1c04100d40700b9075145c1c0f034030319030040095010750806590311600c40c000c80d50394240018058000d03c0002e206107181410190342c5003210303800000700c5040207d202400004a5460b0428245042c414011050403034150414002078840280c144000e20400c04010004641c0c0c800010054504005003650380380880102404080d0b03052240b50352501000803940780c107085642c00101e40a00c142c6114200d81d550380c000f41c0460700344441c040c0d0444404000074016115200041c100d10200e166414000d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 669098498 1250 669097248 669097259
    0x20030a0e1201060602070f1e0b0708131806060314040f020109030804091401080609120a0e03030c011401080a03020705010302070321090201031109062a0a060209130903170c04 77
    0x2d60314554010009600141001d1102004007201f01d400303440b010103089400343c0c0c050440640c01c6850f1080858201c40810480c1c01c21141c24101c82001148400d5400c207540c94071175900a10741d80c5440b001c0041d20b03081d00007035518004c4c001d503410860480113000d440c0d41c958417007540c4400054002c90400200d500e010000450190251000d001c1d8014005203040d0350304500181200181c01142c003640c450401c000c2c10030b02c00118a01d41000454200b074540040d00c4041e01e00c100551082c41d8107001c0850700c4410303000154418024402d52613800c156907640c1e40106070700c0d01000c08014006820100d402e005550007a00100182c0c0c3c40780c03034401960307e000705240c420b80115185442546441e41e829505669142c0906051481d108c2800e80c80d1100c2040010740707a1082202d0342c50b80d0a928250780c000351b962149500d484525a070b0a031400c0c0781c1c692500c400250b0020344900e200d14402524006a881c1c06e00c10405500d40c561a10860b00125601c2000907020061207103101d4078042002249 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 669099748 1250 669098498 669098501
    0x30a0b0901020c19081e0903030c0105090c04050115140f0711011409061b0c06030f10060503010510030f0b03010f09030e040209061606091208010620030a0e1201 71
    0x85410403000050b107489800c0f12007401c006040c010706802021051046011a01c0c1904540b940074140e000c1c2c100e040d140d200140c03000e00840d520641e150002080f17242c0129410740015210700900e40680312190705140801c01200c000303002c2d040809142c440e0124a06000307000c4102c500c440e25602c641408000803000e840c0d644003d1003140c24084460309000c095030012500c550f01700440c0442070034046140003003001d41c003402d001c80c1e0034071010520041c0504402e020142441101516071a520328050f00c43c40c1402c00291040c0300908101c04000a05038030600c11740c2c0c16103c00070b20b402952820040100c026102030305590070300302e40d00c40c3e903410300340e9091160912050200e100400d520405040c0a441d84a03240c900341c0c01039004014840e82d994852044035840000c002c00c04c2e00d02e00050503c0c4005002440c1e0040071789031f5900541e4185a007041d442812070380c160380c0d4000c1c2d410169039642a1070240201e00c0c201c0764410300c484190a0b00036104c2c01c40c5030323502800700104044401002c90 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 669100998 1250 669099748 669099751
    0x309020d0807062d020f0c0d050702100c15020c010b0a0303110c011107170307081612030e070905180610050405060d08040302061e0a030615020d020a020f030a0b 71
    0x200c1c0d00381e0000b0420100301d0507002c2d0032504180040100d48420649041c01c0c0140300303803902c00400941c0003500c00340301801c010a8840e0024410300b290650145460040c140e5806107000740d00c21211500c070580668410000142c00c2d55001403c1c4022150005861029410124081607155280d401040560f2140c0301601d000f54001c0e5640000c080c05052480d050000d1602003604000030058082624080080c80303004983c5a07503081058014202c1e03d050030740c0100c2d0001400884002407504810030300c8004030b0103040c010708a40e194030f441044150201e071481c100682c070740d4012260400c20300205511041d4800c1d0900502c241113102d4400e080d040a02c12181102c1015040b40c1c28082c40c05c0c00c0c41180e50041c015200380e1584042e584485095001d5484000c0c490300001a90200c101003a40034100288001000d140d11381e2030701040070b0007401c0c490144104882c041e4095a0781180700152101c40001140c01429003041c1d0b40d001c0c40307100244c82c0001a00741c0b140c500e00000150000e011a07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 669102248 1250 669100998 669101003
    0x150906120d12050106020f0a0b0c3c0307120b010e2805030f120c011e050405060714121503030a081b0403120c020d0209010f060809011103070f0309020d 67
    0x2030b0342200311201550211041a08000c04550200450702e0340e203c3c0001f2103070f1049800c050424038a80d52440f02141601c2050281c0001c6034035194a100c042103c7d842810744074021480c10000d1103e0050104842d0008540c45000a210035041005401b07259201901100040c5230410081d02010b000c100b0244003182003540e0744080b10643c0180d06400c10b0345401031301d800c4000d010031080d14840241e0f5107030003a4240c0003000c40010f0200c0c3d030340c000f50b2104500a04500c00e0403107030520302c240c4c0d0008100884003a91107000e07034000508a94403803c0001000004000414200b00440841c810500d10041a44895407000020181c0b1a503040000d0103254401f582e4240c040c2c03038107c02d03c2169100383c05004030740000600c010b20000709100086541c0e91524030f810540c03c0e0306800098810710b017062000e90020100b13400031819501d030107102c0c0242c6140e900c0b00001c603150740b1100d1303080303d0090441641910003400883c2d8024440c0450690004861a001c00c4011281d000901c0858004004 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 669103498 1250 669102248 669102257
    0x13020f0a0b1b01050c2a06010627032004020d0e030c0d08040b011203120c020c12070b030f07210603020906040209090103020112020721020c09150906120d 68
    0x5155424060740d5807002e54103250000f801a0f0414141d1807440303010380403040c1c682ca01e1055021090880c4031904050500001045038800c0d6500c450281813207081d44805103a00c05032102403c1c2c0d400e50500820b04595000601d00480c2501805841c07404400703500d0b0550090302081181600c1510b4060f803503c080c480d801544c0e541303000c4890740d458685110903e500341b1800e00c0400c4041120031a01d80d04540700c1113a00c0d100d04841d840c1c121441c840c4c400c5645802c0e0f10349544900c0150f400038080c1040282502c80d0780ca101c2081440310780d1542d035442003480351941080041c0000368038562803504944075041500700d6591110b540e00f5207d80c2c01d40255006036681c0f40070000e40c80c1070022950000c800352021032500080b46c01040c90103005010103818800807981d04180d481c4540e040b80c130410b8101403201c1414072401e4100b91422000c8140d10018455000454007610781081a580036049407400705101c04449418003040c10710090506500190000d92400d00450a0069050003656990f0b07 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 669104748 1250 669103498 669103507
    0x110c0109082d180f040903020c01030e0f100b1906020a06050f130303052e0e060a080715120204080c120f10020706090c0f0f060f050313020f0a0b 64
    0x4550030003000ca84501041c442042051112811400040b20b0b0300035032078001d010907506020082413040d440c426a81e5000f070701e082c00f000103150b4041403040d4820000d90b0141700d2030741e2070743c1401d40e0342c40c0c2c5200800e9a60446000c0041c60500e603401014407100c003500e200d005540f48269100c4a0000360300c002c0c05604007000304010032106101c0c6980c0900b04c6200804241421518032486000b245802070500d43d40d0001f02e030000c3d00784015040c4401e201600f04402520080d030300610141d85105902c01440002c01080061400c0c5001b413041d541c3c0f0034000c02a4038074017007950781c0b880310005240301803046140940d044d44400c1d0000308081d01c00940145592181202408005082141d0386034950704a400c03460400d40002c15621f1508a14810140c0c40c0c102c035042000041c81c824000920000c50a1400210006000c100108403190060501c90340e03640c030745045e258034499040200000300704100140c520308001d20001803640c006800a5100301c10346010850349811340e008014010400308 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 669105998 1250 669104748 669104767
    0x120a080a05220b190219080105030c06070f0812010306060e060f1018170c1c02100c03030f1e0c030b060f0306061207030b101701050103110c010908 65
    0x54035000780c064051035288000300b4001e000444490b04000348104207140114500c1021501c42100c2a44a980215034581c0b0140440405001c1001d9640109084c24000203c52401243c0030070440b2024000c0c03858081240e9404500200410301101d40a40520014020480d08501940039610418001800303e0400c89521032490008140612401c01e101c41200c29072140f0001c291180c0860600104a201c414201c40c200c490581068002d030040c04022840e2200008448940c003070183c8034100c000d04220304042090413100000794001846c086440c002e107100304580309815000307150008060b5200521141560380c00c5100c04158000d080440054418a21070b07410000702c01d003401c1103081c2040700401c000b8041c0d02ca0f00300001c800440000c00d5510344000311607912402c1d10f4903000500d49484041c004100013081a400341c650028814815405402c210051a103500d0305640d1070381c03034600110060b000c2a43c00d07107000001400403601000342409032201c82c0e8454000141c5405410b03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 669107248 1250 669105998 669106001
    0xd02150c010509240403021509030405030a08032d040f0609020303030a0507020c12060a0b0f090f22031211130b030f15090a0207020102010603020d1b0b0306010f030e120a080a 77
    0x100303c03480210411344d040c00002500010000101c3d00f030502503000d117035a201c407130a046010703e0f032001d50103018001c0107a04119503d0700a40c0325420890300f11141014562040c9468041490182c004542c0c0340c01143c0400c042c40c00e81100301d0710920003c200700009502080c1160000e41c0c21000c09500e54007481030b850b406000ca08104e803010742e40c6503103855001d514141e551a0107007002a4143c1e6034440500701d5103442e40031452100e009407040805007800120168000011a000100400403a4a0240102c20348020f403e02a4140d03403441d41100300c040c900c2c4001c1c120703c80703840c244070004c00c104101200d88a90400007440c030b2440c51031716403070b1034404008645001004005110740ba0b401810680d9118005035800038080034005882c0c031564130050b4014000c1e0340019600940c889014001c1102c042a04449a00e0020b80000c030555683c105690302d01054550718081010300d8108500288a07074014603000b03461004481480c003078100c0740c0c1c4460703004107880d0303000851a070200000007609 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 669108498 1250 669107248 669107293
    0xb0d0f0506090c0a30031706040c090b1602130b01120615050f040e0a05010914070203180a0312020d080702160e07112a010c020d02150c010509 63
    0x7948050100ca450000000fa84c0d00d009015400000c500c0101c01410340328180e5102c041002c00900d14907401460b03080207000d081d072040c3c8503e114004940000e10506142c021201c06004a0f25400d03003241c2404580252508003030501010b94980c400c040c00075a5801c00d050a00070700e9400001504104080014140350316454806019410900104480103901201301d50b03600092515948400007c00702400504ca01e41c481c6442d0003c80c418481d031280d240c0d1000341200c9410400b0002c020143c0440340f0107040c21990540540c00902c90f0072200764601c815200d242200404000c042a00e96030341038540c00d01c0d087c0748001640205c140089241d0840495a0889000d000410041111a40c1d41c1e0352015240a08140c20034000301040030540542041c04600100100b41d40141294645241408411104c2182078040a046d08481d550182020000e00d0790040d088007a181804c0d000c0c041c05148030062401c14503c1007100700c1c3e05100038442d484c060740c1c900c0050314896a0f200c032034502c1500ca = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 669109748 1250 669108498 669108511
    0x20d081e0309060c0901050c0f011434050706090606060311190f0e031906060609060503010b1308071202090f1509070207050d06050f13080714010b0d0f0506 69
    0x810001d01c1001c42c400285164805800e0701e11039540c030380250048078503000b002c098076950710a100000c882c5035410340050002c56020000401d807696200d000409019400d02629186081051040c1030b40c684d04001442c90010340c00c03c1e03031408004d42d803104101e5010850a0b02c0d4150740c0d07901070107410b625020f01c1c00b10741e00400415092035175415071020801d000ba2540b005101030030f0b60f0700803007174000c505007140c018006050b0340d091006a001500654248501254010314090740810b8140c0180094000e49240d580c03100d00710707800c21042c1401c03588490440807510203240c100281603202081814040c016054043e9406034441c8140104590090710200d4110046400c200745201c2c140c40403d8103640031038251541c0d03201c0c02c0c0145d0420000d600801d400002c1100381c00b0a0090079004140a07050310031480d0081d40d1041d001c8107104081d190011b028520030042100400c142d1401c949000002000009401c44184001401c551444004803903409107503920500b0f001c003c0c80000d60011 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 669110998 1250 669109748 669109807
    0xf1f020f0c181f1502010b1003020322020a080303180111041409040606080f0c0a050907050301032301060f14090609130501020702030307080403051603030203070b0c07020d08 77
    0x1c00000c50702c0d80404010248001a00c50030540352080d4036810b00c0d0300042c060f100b00c5210071841c02c90002c0c0a01107000307140b13000d145503804804140340b00c0e02c2120321031003000d01c0c03100010208520307121110543c031a0590f8400c2d0480008580b0590078002540107100e0607221a14000180120909450526540c9095440d050100b0804035010300c50545040034216806009a80c40340ba2003002442503401c281032034854411030f62078400c000502e03007141140071110348084a560b14208000c0c00701c2201c10400248060004000080500d500c02464441e0101c0301500a40851105400c441c5030707900484c40490300c2e0504004180000392409450b01d400e440110103442c040c070100d2aa075030050030740700c04010182801c0050040a5043d106044d0703004058954800701d130300302010b880c2c005010a48484c0a265040e03100194603401d0141280d03496005182420015100c5004185e4020300b202c4d20b0040401c034050042e5a100c01d40c1181c80e03c914041c5032640c1c1c0601704c50f48141d82ca940b0711120350 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 669112248 1250 669110998 669111019
    0xa0f03051504031e051b0c0a030201050307200303063f030f13030203060f0108061501090e0f04050c01090b0d1a0915130c08060f1f020f0c 61
    0x504085418456110012a039031402d840c0d51800310740558103405806032039406904408a5140e0000080184c0407040d1801da1101c1c02c1e01045075100c0c1c01c0480156404a40f2440c10801540603030040c603400700701414220800e22500ba040b0700070000505848038242c00002c1081024038000300001d54100411031641010581d149010440042d190750b04d41d0350125078107181949860400860305041c1c0341000054982d035051256814040f2140000c0384a07001d010005545060001d400b141283d848200808a580340c0c400b030074510f044440e11030b07810080c0c8001c01143d03000c80850024020398080040c45c0f424682810441c0c2022024542c0c1410810803c400700140c6004500303841502d42004000102c119000c100410011541904140c104124404100d01d0006082144d50400016118010300129140f808012182c160080e41d01080e0b5910102e11103040c030007070301c0301d664101418415580109080040c515542540b0910041e4042c0c0140d52103600c0c1444519141502950b10a07010b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 669113498 1250 669112248 669112253
    0xb0d051507110a0308330a06110601090e010212011806081b1e0d0f0312050613050a060302030102030c090a140d150216030f030c0806090601030b0d06021303020a0f03 73
    0x11000c68083c00303000c010000d40400d080c0010080066182c0034054184a40701d041c0c40000c01e501424a1720442c4107010b448000107619004022181a072130504020301304580c2045404801004102089403580d98240301411102810101d0340c0d028164007005103580071070001e41181078401941002055030003076400c00c10011100d004046500e0001c8508407803451580b0385003409600c944d110340da0310502050300c8005100c2201140001c50380680e5520308280140c2c4040016101c040d6407440d08002035401c3e400c01000160300007a0001d02d00d41380440d0303180e0b0741c3c0c0020342680c00603200480a8040003480d07440e43c2c03800542034401040340c0c12980340c0800c641000070746801140035020f000d0b60420151880300c110940c1c1200c40d84981d18111000c040da00d82070043c5640014041c0401081c50140300042030344c0074183c400d12484004160045a907503a40c011805803c0310081560040d4400da001e0b0009907050005d40341001c2c4d0440c0d040da21a1a50042100c260340c5e1341e110502e9500d641074207002 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 669114748 1250 669113498 669113503
    0x1f05030c1c09150b0a0626040317070f020703030302070204091703060307120818010c12020d080703020c0a1412120901110f03370c03060b04060504180b0d05150711 72
    0x111210f1b0300740300411f0000c00c3e030038039964040003010005840010b820001016003021510380c4482e030034420105107582e00c2c0e1040d9100c6c0d124070103440240e4001402040000d210b50002c1050610261000c129600b95582e403159000810346c081c140300304c01004010150404101110003043c01e080b00d418004000e0304c1c0e9840600c40c800308141503601800d90328006074091000030001a510002040d641d03205040c0081d158032448038082c002034000e5002c03451442c4240259940303030680d04040d214a080c103548104c43d02499030141c603854012401c120348400d80b03000203441c000507100850590340c03a04480040c00c441c107061110002d00010301c81c40312000300d18010780364003400c1d581002946066080c0714501d004c0b440c2c02c5207a0101050710707628112102980081000850303030b4500f0701006823521480c0c58907000d0b60089030b00248040c4002c10041006400d42e840d41070002400041111448002c586941c41c3c1e00c41c03e40b02d40d0b200c18031402c0c0032020440032903880b0110b480c06405a0f42802810707034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 669115998 1250 669114748 669114769
    0x51c032708030604090c0b181e130609060305070503010b311b050d0506030d1205150613080c0a03110409050f0106170c1f05030c1c09150b 61
    0x8101c20307008000140d05441d250b100d07080c0b10760131042c484005607036400c00f22525800403000440c20360050001c0744071402c011003542d0424050300601c8071140312050a2103202154034103a10401500d074103000680c40303018030508001d5809040a8110603080900741030940c0e8040c41143e00427a20b00400764150004111031021088000c001e010f1030600c075100c00c001a0500036007107140d13103d1801e41c2c80d09554018008198500d075180c0b00303010a6440c50704060b2516401206000414807410f445840c10b0b40700d41c0700d55401500e804c0d458008c885640040b40098003e00511201002e1041061051501c208407640b10780c41c007161085105815139079182103109056a9050003039840b04a0340040007814480038140c03041a500800500d41e484140143c1c0440c90110040140a0804070024030300f003d101c1c010441a00703007010400030280e2142243c043d4030051403031300d640704248542100c800d1421000000182c1400c404506044982019900c81400c04000602c5903d800c1060142d600d8801703280 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 669117248 1250 669115998 669116003
    0xf1e030917061b120f160c030816030e1203041406010f1809141e030708030f060a0902070c090606110a120e03071206050711120313051c0327 62
    0x20342159820391042d0307940034013103038804200305001c2006a1034001c50401e5104400a070308040c07080c03403084030a0301d255401000140009032204005002d5044041904100702070610700020b608a1354607a040c289030401a108a58500000c1804140004800c008220082d810f0140c20607500d440d81c0c40c40c551000303200d0b050500012100b002d0711151180d202540641d0004c080c042d0b611b02c04060552039801011450700c4400e844802004004400019039000607801b0f580c103865912000010419090f008042c554014400000401c26248a0000c1c15005100384c50141c503050402d15020301780ea01c560000e604000d26003ca100042d42e00088002038650807144114851030782d802d0840f4003040c4000010f416104105002552002407a07090003064010315003007105450703440003101c8008103980d851020741d0051301c00d50b003510009002540c00517105c15405864149035600c10b41400700c91240000001ca4801e0b5204101e074040c0180c01d400e8061604150341c00d0b1141d1003050011030f0707400d000f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 669118498 1250 669117248 669117271
    0x40e0109052404240c12060b040308030a18050a0c0e070c0b0a0e0c0d110901050d0b0f090307060f0b03070e071b020a09092003060c0f070f1e03091706 66
    0x31002e2a01d1542142a6004e2951084c0800c10741c010b000b5141c503400744044910b0034a000400030f00103d051041d10250703644000518036546502020001a004254692041c62041161239001a000300034094506104442d0740d9082807610380c000c01000001000d80062049102580b000140508406e40c0d0003c503010002030403d11000705245449241405590459903510403202032050000200c1c050640c00c4845886503070b2a84244008030030134040003013040f0307400408100448000d804090307000450704110781c1060300741e403541004e8903038052091681d107039220980c9081c2c0c2000d0150130050b02c20b6505030303103150030229002800c054110b5481c0c20003c0c1c02040321011503031082401c2e801030400e003000740711050781802c00d0a00e00040c0510310580700a94078411003a4140803480602c00c045040c81c0a04026010f80c60300d0190b80300300c07022076a1a070004d00d04400154010203248019000001071500f2508500d00070b0a0301c1c10310f811000c800d99040340d40c400b0f40040090001d0f80708000005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 669119748 1250 669118498 669118523
    0x1303110103140f07030902210c03120901050708070218061011030417031308060105011803020d020112090209090706020111091011030d020c0c0f060a09060302130302040e0109052404 80
    0x1c128021b0580190007940300190403c201c0500900c0040d40300900001e6069982c2912040b080507503030002c0c0c07505c16103003000601007a0415800f90002d045010b01810f08140b400d202c0c3e50000344045915514600c54039420802e000a509141c0120780701d000072420418940c0c41101d044075030380d00952054120808840d00e000354251000e0084d035424440b030070040c40c1c0712a2980803c507120034090003400d00050240495071150102200d9800c11240c0280c01ca1000410540045070040356a5100301c95041d200c0103002c0058940c4928603100b4030130040508030705400d1410003400c0d19103c002021403138400b413062010307030390300c045603440561042d040003a1102c03602c61186086000700070700a80c04a2000c0703003211031140c01141c010b10015007100c2242c403031040b003402c00059008504003d400615280c400b07000090080d8020a002000b8600c10401541c2d80e50014081d603100e050114200e9454110034410040100b05175050031203260090706559101c24907010228200038805410a8185c45 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 669120998 1250 669119748 669119761
    0x6090c040e040803070e240f091207081209090c0c011509090209010f0b0313140709060f121505070903120818030c0a020d050f031303110103140f 64
    0x880c0c0003020340140c224038034030346802c05503110b400486421002c1078049180030421720b00707042070411048904110301c58400c080110700400b5004121030500d10b290030041500b50f6950a000e0340c4000c10a20000e110786410041a81c0c04c0c5503110b803810151882c288102e004a40c0e030304101541c4103030030080441e1145d2201300130314090944d483da000301440c0c0150340031964103800c0d00f100d921140261408a030990342c1e1106503080310a01d1095800320441803010a41d01804035185000c280e000c1d01e4180440d061090480e818102158000141169191410072100c51022510001800105007052681e42d2075217032013202c144541c168030302d542d640d400091032080c002d8071140013444c0c106400884407424840d0183c59524141c0e01c110750031600b55110381c108080003044030300103d1410040e04151445509002c24485d5000040b5028005c1410200881c0c0081005d4000042c4130744016611528604203403800d41540000c240c1098180411116203400460746c094008400c8140d0050301c0d52000c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 669122248 1250 669120998 669121021
    0xd0e0a0c0320060901080a0e0c10051b0a02151b03070606051905032d100506150c0c090406020702030f0606040c08060a1e0b0301030f030306050f01080609 68
    0x114401042030304542000320600011405500100d8088100000400115010815540110510326000030706040000703240c0c50b40703031304100b90403529181100c106039141000100d83c01810f1000a0000340d001c07507800560207000204d0b000b003411050241801c05065004600d4141240e40804048a03000414802007008461030481d80b001140507261200800c1c90000c1c06485180305042c803c03419000c034808000403041d019002c0ba48010000c1c0140481c0c0c2c040c030b40d04141507081000400d6540c2c4d804900511050041040004c0700401c00105440d0900030040036002c6044c0f141401c0c40113002c00315090100064602d40b0000c11104102265141d01c0c241d03010b48283c82e8001c0d010300400c0c03141c00a1940000706240a103000300c500740003000c1c2c06441120842421074075954030105c400400c212041c00e0102180c041d03000340301c0300420140c40e100305170255402030313000316000f9907080740810a055052041901604040b9215400080c00000003025090045d221034411b600d05404901c000d504c8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 669123498 1250 669122248 669122263
    0x5010c0f080a0203131e1403070303080703110403110907020604050d03050c041203120e0a020a090e0f150105010f08093a030203010906090204030f08090102120c0d09060302030106050d0e 82
    0x42000c2190190f00d520f04c1e41000d1495201900d549486c122012500000141c2c1500b505440035004000e55413440d10f00b2601344801414010516955552076402841480018000b8501a2851607522245002480b0080303000802007401c542281e01403000049020400300f810000030b1070045601e45845080f00e0851145034081765206034000c04000405401050400d03503058004001c1141c444142800390300c3d03510a41d0001d40c05094460300744800d0700d00341d00652100c407000b021100c00c41080c140c040d1401a0044000010500c5580108810340c0e000144035102d01d41c910700090b880c2002086244d031060149000c095001e802070b80c000039900c00240d01d465108022072084108481410040c00a500078011018032030305141000c94200003074001c0740c08581c1d00140070b94000306140c40e201d103030fa00300c0c1908504500418440e180c03983c07644030103001c1207040b002c050003840c05401005041c840d107a61002003403500601c010840190001c059035a451803480020a88442d61803126003440031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 669124748 1250 669123498 669123517
    0x61704290f06090106090f0506070c0e1003060f06061b06090b070f03060e0105030d12020c03030408030a05060d0b060409050102040509090a030f03090f111c030f0905010c0f080a0203 80
    0x280c034104540c1d984401c66007805442c0a980c44611a600e9104c225101d10b0107020702c122900180f1000c021504040700100030079805560b03040c1c04240c8400c075400806034140d5101c40401c0c9003900900500c055442000359060a000d020800240340040141039134031801103c0e1303680c1c18114030030400d202c5150800c8600301d80c09001e130071a41c40c001201510b02145102e43c000002c0c0f80c10000b15130303044544141810380d03d00900070300c41003103a80011039003482d00c104021039080d028040c8a0032140e0030800b4600803481204401d44a26002401d2401c070b4900806440c03043d07841030303005004250840d502680019060b10040388061103402d01e54068801c41d444160071811050401607203081c08210700c48541d2183e038544000e44070b1014104c06031103045030041c01d4486441a08000200c2001440300c0e054009000711541c10f0f05401c090b03c045002c2c180640201e0010702c54600311a6001140002400702400d0a107aa01410b0301e4218110701d6800d0b004012150000d241c000090080094890044 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 669125998 1250 669124748 669124823
    0x32102280519110c01181401052502040b030a0f0201180e090f0f0f0303070e1215060901120503030f0402030c09180c0d020f0f010e120f0601061704 65
    0x14440000c048000f5a116000b0900882e084103100750300c0345c18035610f500c4010400d0f891007428454000e01c0f0160401100d418403408220344070440f01071818002c0d0302c2c00340c151000164005070043c0300580311059400c0d882900202441e4000800d0a07011249040d0203203464000606030358040d84050300503411003203c0b10005802c100b08050002070310003400700e1803020b4608120032007401c8e070b0784c41440c85a0306010703401c140000b4130749500c0741c103402c81c0c40701c0000d241c280b00f078041303040706130602501e480340c0354214000c0e078104452410024681ca00500b03541c4450031071030f69652601522030002400c42e0b181012510003003005e640d000c019695100400410b0304c6854104041e88072521044011484198050546080c03068641f448003404a01c0c0c0142411114101000070014100c01c0c260303040d41840208110300809031910b2041c0051042d80c40010445a400040380b6450400140c0c07004081100612068101e42070710101c0541065200e201c00e4041c110864800c8d0104a083d05240f8509 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 669127248 1250 669125998 669126037
    0x3021f0e031b010e07031e03090e0c0703020106060908030a26090a0302240103020402030712020a050a0806060405060403150e030a0c031b03080c16020a030321022805 73
    0x10b009440e9004185980d50080107140580310219840c1c2c0c0151101809aa0300d00d242d07041081182c405400c0d295200b850304462036911091403480503141a200a000c0e46804146c50b000c050b024402d44028141a0030413100a41c40e0054503a6a4030030451a803041048d040a01e02000706c0765000b03584400b2205884424900d044040c250351003c04060a400503c5881c480201080001e80502000c00d072003030002d02a603095400340b0020350310140203403003008205040004d081c111407020f0100c60720540c0d01d0b56030f691844403004045805c090881889201300f000104072a50710b510480e000c407680401c00d41d0031644000a020300400b803030b1081a030207000000e10041c1440e48901090740e003d10030340700c074076005c08a2447c0030b41c81c0d00d1409004011580a03c0850459038101d000b038040d4140c1c00c0c462500388146940070810100080c2c0c400c8000c00d090211070040710a4054040440c0140e00c0c030f0031801d0103054051194980c2e00d91a5421060585610a02c4000d20420403107a84e04190300c1c100099 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 669128498 1250 669127248 669127267
    0x20705030c0d02032101030c03020d0201170411152d07050615120f06060918030c0a06060806040317060f180106090519150509090906010f0501090303021f0e03 70
    0x182d6110021500005d121071642c000a01c0c45109598140c03500304620241f10360039542030250303010038860141e060007029910240c40a45000c851071145110319000c13403100d0112824004000035000016642080c1031115980e2300601ca0000e40d00250405410010b03a5420283d804040c440c0c400e0103445405084104600340c09680288228164180c405400d188001e02c40781d901d45100c01c6120969403c8000860041d1a26000840e08102001a410054007543c00c1c02881c681c001a4100301d190400e00c6080c0a1060510881c0003c080400c050079142c40d02d55801083c20342d007042c10005440900021400640321220405c2e080d940c0030704601501615800b0812840209104a0380060040740011a079818040c007802040c0d0460030500d03204605200303007122184400b100110403c441404000f40554424100f50300a8400d44c010705129410480350500ca82c444c0e0f040036041c00403003d030410010380e00040103684d0216104102c21510540c45412000e0003441d00e000c0118800442c01010 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 669129748 1250 669128498 669128503
    0xc0b0c120c0418050420130f0509100504080d111615050a0c05040905092517070501140307030609360807021302091c020f0a1503020705030c0d02 64
    0x1d480c40c40c41c0c1c0f2051000d0341d24220080d6141200c0c024140c00d104009858014284204030f03004040091100b08004c200240140450707412203c0d030700c4034a0f02c1e541882030300007040c000140c80c0054060140030610707154407943c4a0740b04a140d41e05400b07640e04414202d5841351f04c1501c04003071f00c100b4195188101400c08a01800840f0340310710455161202062113440d15100f03861407264151245401d00340340480d003000a180040024115001e0a00503c500c0709a051a62100e0710601c2017101d02c0f14100070310080340c1589044000c02c542d000c10f000344526a044621030342403000781c1090aa49681d460780c01c802511859000801580c28202554041d620440c24419400c8400c101c804000c0c5d4035880508260995078405800400104090307c0075050048410000c0800c00901500d071204017004a5100385030089040c2e411069810103d08600c3d015003114480501150ba09211030305040a40e276030003803022100b209159000480c4020803c1c148181c0701c812445000341ea0341c0c00341c2401e0203034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 669130998 1250 669129748 669129757
    0x10b071b0e01030302010c0f0918090b07090f090b1c0302010b030604051b0109050a060305041e120801050f010215060a050d121e1b03050d020304030c12050702010c0b0c120c 76
    0x213000d5420640e42100007481004e41c2214403400c0ea03204510649000e80032840e41407013a05081b006a02d60070311401241c00b52030310b58040d041c10740c2d4070052249844054011201540c03c8601ca55060200c003208648e105810b01c82e414060003410913004103507103400c1c0e0051041c56011034160060100b040b09000000c40d44003d100c1244c441d424001b2584001110468110b0080a80c0719001030818081c6900c2507111690141c0305440d000700c40b40040440000c0002a58811901440e1900799220b03403550203401c090042c5015988078011009c2c010002c0e48501460404015040b21000000d14558a0f101104010480034081d0354443c14a0709065411807a4400c0103c0840c0b60003060450a950808100341404401c0d96a5440112501225841c90580641c01d40402a00348122424000301d80b00550295100b0745411443c0e500c1c138500709041210140d00c40c0140708060044001503600040b8041d24268801851905540c0c1d040c1e4803a0f0381d0182d003684901c00d070109410004030703444540050 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 669132248 1250 669130998 669131003
    0x2090a051f06020a12030e0a080408010c090506162301020c01180302100b0a090c020c0a05011821050a05060f0604051512010b1f110102040e010b071b0e0103 69
    0x200e120301001c0500041c1c0000c1481100010380c8441ca5003404610100305481c60a4050304d4085000c1c00002042480c002c02e60300280c504140005080055500c00d11500c02c0c0c000980c03d00c12116850900013417883c0c010384030300800c214014001c200400c00c643c2030001d4a01d4692424051490111081500030340140d16900c50940c80d2000e42c5200c000984404040c0302da25500803c0031508010001c0003800c0d014142640148045c40301280484080c00f6001c144052131b0300900c902c4034038008100000003941d00850501c0603400030400d403011341f07513040400c0c0c405603006c1c0324610740b00d44140031a0802810b0054507031701074801d8a2042040c00301301c03d4040c100071001d121554a4007000c020803100c06135880229400d00074407010090a06074020319650060340000140c0380036120203d403601001074114616072041180c0c1c104466001526104090585002107081c01d0418150084c076001c103001d1461101000705840c070170010506a10ba00b1001054000ca4035160344032284445604280805c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 669133498 1250 669132248 669132271
    0x180406260111030906042a1518030201050f070305090a03122c040518010608010209010f02150112080f070302031c09020d1704090e030405120703030806011b02090a05 73
    0x110800c81901009480c020700112005d4004ca0300c0e42c2d80c074a42d050038800c03c03003100340d050441c061105030290b9840b40020804081c8039408085039503030003000c1c1142d148205000c03504410081c80541d0b441801d64280711204011290384180f01e050039691405003400c0c10b98420200d81d404002c1142640b4080c04840141c0c0700e0100074941c0d941109100300c101c025110858000000c1a195482c0a400040d0802c42c1c0c09902206250004003107402d40c0e842e500a181140c2d000520290715590114070720104080310301c0940f05000c0c08055058a049040c8200d007070301c010752070140051040c5e8008a492110605000703507915a078502e03000e9101c0d04055890b180b00d55244940d60340848a9020304103540e03034001c1054a0094150343d50265a40141003080c1203600203000c04210000325101300c6003828810340041d901c0703614040401188903071504685032070360000c000410009400c0386c5459000b0000b402c00003d0a0801500680e40c2c0d012600c010b940205a1014014200101c1c6c2c00070f4020b038000c061 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 669134748 1250 669133498 669133511
    0x307030b091005101d13060305031209060c040b04140111031902072102040f0b0a03200a06020715032904050901150b032a0307020f070b1804062601 65
    0x41596003442c28500c0c0024130b00305d6010303480320f450224441c00a5441c1840c1c001070320344e16900d8803441e681200d0444070710003170701809201120404004141c0d1085031407514600e00340c1094540910303806148a8494940c0114040d20003a80c012284a452015940126525001441c403048001401c00201001601034680e0110b807101004030300c8080e0340c9542c40326115000142d0f0921005002d03c0801e980c203d640d6440514075999081200710095001c0d0b1182c903080c54040b8814440b000c0e210605500c01d00f0100e800704601034010409030122024105060704c6d268640000b40c02400d803d40d01491440000045541200003110214841c10b0040e50108402d43d03031550154200c0b02010185074060b1482c0708200108403940c4015544103084440c400002c0795242c25001846002c041d10317081003800401001810342c1d040048140300c00b403140003444001d140010012191107880103182e01018941c426207aa51643e0b0445070041503001050b00301303c00740060f0301c866110941440d103419400e000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 669135998 1250 669134748 669134779
    0x4050a030906020601050604030b0406090b2d0f0f0714041701050a0c08062107060818010623040e2e0207020a2d08030703080601110d050307030b091005 67
    0x289130f9040e01d02c09486249000d0035910381c40c440c00c5005004446c40303600e0700341d400700050a0525190085c0500c040e112006050f1160341d140704440100c01d0090f00c02038004100c1c1511448402d00d030081d00c4a01c1401007522454421030352000001c02c0b0b40116900000c0c0045c5010b400213020f01c4940040008001588a641d6460700303803605101820001000309012400c98580031565008104012034180560640320800c2c0d824503446511100206402404000d446492007031840074169918000300300031420411005103448549041c0403040c0080b242400903600e403a40a0f2800e080d027401101e0061200403101c440454600e0910000c070f8028200a011650f164000c0e5100c070b9a00074125042e01d81400303401400c0c1c105420f951415001c84c080c1000050b0030340e841c440003902c4d088002c4d503074030f01090602030080e00703001d400981080040c0c80804549940030802c0f00e1a0780340c1d45800e035980c0e111014110050000c11038003aa2118803101401245600349500800700d60303083d10241c8206000701c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 669137248 1250 669135998 669136003
    0x50d080712230901170703060f0e0405010606110d030b010525020a09021c02030403090518040b010506070f0327060203071202060c18040f02030f1008072d030b04050a03090602 77
    0x3c0c10345800300e4101e18902907441440750010b640801640f40004260341e6815030301f13030781c0c0780700d40e04c08801c83c0c3c13040c0d040c0014882d0a0158102410481c18007000504600a205554501c24600301d01015510741d900c1859a02c920200c658400994031002a03202c441c42401007145000e01d0120b10610581c0000034501c0301034000d444080e208040e002250a42c00c158100181d407000300101c04002c5004408145a030b541003041c0e80340b00c91110000f0b602d140c0742c80c111580080c1a0401881a0400d00803400043c0541103903900c5658103190105060b141c079858411040500c0000085456111201040072a0b000014003200c900034028101900d4811005a03203c1c40103403504c1c10600010040303848028a1015010f40c00304014000150200716911140120381003034546280017291007003802040003880080e100945002406448442c1c94210351040c840f1500c01440da88140d03003410b400c14880207000704001150030058415951509140c42a20384072500700c110003040c0c0791140400d426100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 669138498 1250 669137248 669137257
    0x3090c1305070c0204090c0305160608010504061809030c12050c0c1206040f0f0b07030203090d11030a0e030c090705070b100b04230a061d090f01050d08071223 70
    0x155200d9080f2042c0035000d20026151225003680c034144003ca00000103942040340e012140f8150b0310f0fa100c2d407810518000c1542c40107078400381c81130b0700f000b00a100c04d0940c1810282d01c061038400001780d189592030f0945440d50b42d01c0018018036136000d0703c180156085002804159080c13002d443c011140d400810000d0102d021040e19664010000100081e01d14a5025200d81c051303c00c800b94004d641d61101c80307002c030445d0002c001a401005002c1d003017004211380b9102d000705042424039500fa00011650301e0060103903a104200d4280c850318403a0300c061249032018003001d4840f14280c07030b1421300981309610141080f5404180a400912701100d01903420050305c0c030910903903103080e00d008102001c40703e60380b01d00b60748092001c241d01e40f40e58985142800800103601c0b00300b01141840c028400d82c900b06d05400740621110f50070490009c401c408042d054940c01c0b5803102c42c441f078600741341e02e0078002d180e0001c4c00d0081100500c00a01d41107542c40950b10081d01d5801ca0340b2001000c0c580a9014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 669139748 1250 669138498 669138511
    0x106030b120c0f010c1515050d030206281503110d2f091608150a03080c0f0601170106050f0609310e01061403120313020603090c1305 59
    0x4444035000c0c02d40341c01c2864908a0354145030000c518010341e1110999400d80c2e04115001c01e9844005038820303003480030b1a500804003201c1c25030b030080482e14040e45440c0020440055003c0e49118080f5400c50740d444407501d4071404070704126480c0f80c40e4a0580918032400181c030030160b800b460b0950303494402400c0c0411a44a510388a400002c80340800180076400304070407160000000c1c40e080d07910303986442031040341c01310152031025510f001c018040c0740c0c0c0545000340b9550381030310141c10340c0c480d440401c0487ea4410038490f0b4504640c00070900300707140081501080d000b690b00000e081070f41d03030b00348403d0100c3c20002008255a681c04010460101e1074030715410403020300004030030b490038280c0c15a6100b603003140782c501a03580b02d03d60745040e400300c2010001e5070740c2c4128511003181c1c00d1056402030900c46840925060f0f0000000e9550304c0503801034816503c0000002d0403d8441404140c003640c1d001e88a26101d04042c980b603a01d036000c0304a01c90080e006404104005200307130150703901940 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 669140998 1250 669139748 669139753
    0x1170307020a120f02090705070b0a050714092103130609030b1306140c0d0506030705010813032d03180c090218031c18051e0301090c0801050106030b12 67
    0x42c5003c6603000c0d68605580142d81e4007030030700007038030260f210b8000c410b01c01c10711a550030b9a1140c0c13519000740174003800b40501d0111407808c0c04010515810004100320803841402150300d5880d0880028081c032a1004c101164281425507007080c0c1000102400050205000048501e40c407a0003c66880400b880080d06d44c00c10040411f8418043c4010120610b016070030204000e0781d0360200091003981030382c140302400d2001800c0d40c2410075920849812140490141502c07a25140008022440180290810074103810901c82014010b08444803c40307c500030100c807528807210442815004042e209022a04182c052661030054411225403164030001d02040e00c0c1c10000040d000f90008011800c103040d10780c1e0000c1c1030396010494844601e014445a180c0d9441d074010091440c20852200000508040424016945c031070205d070321100c1070352146401c08030030013000038050518031102401c00f1a40540c0890a91410341119050300d45948041c4140c110410071301882d411219012030894 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 669142248 1250 669140998 669141019
    0x80306041107050d02060604061715331e012c030118050f0f0307032d0206040506060f0a180b1509100f02031603090f030b0117030702 59
    0x525160748030400641a801e4410b0510381e8507521103140070100040035016074080c40402204e880e29016800241500d0f0f0358a10440c28400d4081c0d42e2185407008032545107800c1d400003280d41c0052140f103010b40346045013806440b00c083d900390f14860f0302c0c0d04106001d454042c8006041100c5241c60b1030401606950f031a214400000c0b520984510680c100c0010100820380c3d241266401d00030712503484007001511744105400c0c07400e03c0ca801c03140c458800140e00505035042c217111000c0142d07010250582001e41c03800d803241400a0a00200e2032201c1032000c5151070001c101e6038006050743c800d40c490400c0301d481e0b8803000200015074501405d1213502c901400c40912a86d001c0c1ca00411081851060118050b4180c5d00010004402d40c5111601c1160200d00c004d0145000c0c040200074803181e080940d4000001c4070300035220b2181c0e07c0c2d5445111101208003003058883c4880304003c103243c481a4800c1512460044a00c040a00c0344554001541048590801e0003208642000da4020a0003125 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 669143498 1250 669142248 669142261
    0x90602060f19020418061a0409180602040305150a0b0d03050c01020c0706021b061c02130905070906031401060915231c0501030503041404020d06080a0c0e040803 71
    0x802800405400140b89800c008a80d9008180041d0014040c928016594903444003505412541a0f41c0100131034221b820310340599101e0102141c040e04c04103c000b0424030b9a070601c12518400600008003d01e200181c00000d000c404140c4034191041d0351310080c020b071500d0750148141d075481001140e1281806540ca400a80124010300d200520a0009400c1c0b45400c1e01d01802e1404d2580050050b80001e00b62481d074000005400e05203001c1150707030508050b80404241c60620700515074041003540007942c400605080083c400003013521001c180690310380500020600d1030148107200109007421801ca0045a980511034107030341c0903682d02c00203c1d10b020402e091482c0d14165450520120f01101c0101d0b20480251040d015011441181d8410f20140500d0f0029103420003846210700d0400180002f500101c1180c084541c030400124145540d031000400901c5192000f03030700030740380490025044002003405c0d0050790048041400c0c1680d50445080b0315001110700030a01107040000512 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 669144748 1250 669143498 669143521
    0xb030703060c11160b090307030c080c010f050309030d09051501060e0406090b03032a0a083402122802030c060f220312020c030106061d091e0106030204051009060206 73
    0x1003824007d003180c248641d41d4a5550340c1185031b42004d21207400c1882003c9086d43c1000e007400010482c0d1038810b107180703810321105440340100d0002d002030580703840c010020b1181c02c110000801609800c3d15000d541d6070180545640f8803882c0c0180100d042000016131442180f243d00d4440e807020300550f2519414040320050b40e00610349500a00740c02c41005808020200100b5800c14810924940e8480c000841301022948100c280801c5040003011041071013400d90f04120041d07416601c42c1ca100245004041c00c060840c0150401c2c05802d91a030884000c4a071000c0c000e4074000c0c0d064807055044081481801e2069528003400030000f0400c0c0e01010790064007418200094032014040642c40703548411190743c18403000700c0141d002e25801e032070b240703000e10405000b01a03c0c1064441c0c0e030342c00b206110a001c43c14840f1841441c101000980074400300b401070b502a6025814000c0035038544e103000c0c0c000d40140c0a11400342202c1a200a519400360f10003100b650340d550010310050340c45080703012 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 669145998 1250 669144748 669144757
    0xf03020a0911040b0d02030a1a300a0c090614090414030d020c06040b06010e0a06050d0b040606020609010f02181e0415140315060108040302010b030703060c11160b 72
    0x6442d0070041000080c004543c002500161801e5580940c0e80c1c2801403041d01aa5118110114020090040c80700c156590640030b41c0e40400c0b08190780d581e8075903200d044003401c0504520300e005002c3c0b181c601c0104640c000ea070f141540d404002c200400d5031200da04030f0420b90034007145a0880c0d01074011801040c40c90343c1400884104c00d0881c0d240203042100442079070070000d4458116807000c02480200000b40000c80d52003c400e1030310540120f080030000f14100384030b12441061103c0080c1150344021079400007080e000010b081800340c9907440400a40d101c00407120745602c5c1d444c03d4401c0c0707a04142070088820a80440c810061070305441c07010004060600d02d110248034001880700d441344e0312180515651040381d810152000d1385403030b5241d41901c616021181c4203800c002d12040c0c000040c4042e06401031400e2828018a6480c1c0ca001d07401818202c20003603043c41040300010421440c3d40002e401102c441d40c400081c0000070f071210340e0f6507014a05072090900c00311001d20a03000a0000340 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 669147248 1250 669145998 669146021
    0x210c011116081b010c030f0c020d02060a200301030b0f0718060509040f24050306310512042c040602030627180a0f02060a140d0e070f03020a09 63
    0x82c80030302002d111007402c4610300c1d41030401090302d480b8014800f80013885032042007002da0002d4014002b0b01c680c0252905c60050030300d00002d6451a000e54501140e4480e03000c0c800f40c0c50050f55503561282016000360004454400c04003101c040041c407098400c0020700158596403150031545420844207403065000282c00d0b5801c40c0e40d9510019240c8402d02800c0034407104201191800b07500803c01a0600d0580e8201d035000c0c6e4000e0040c030003100480980c0f083d00c541c40d268120008692580c00b0b10f01000001806032592140c1310440f05541c420034024030444076000d11005018107c401d520a940b00ba42c4040364014541c41c0000300445c000d500256070144000300149102e030a40c580d4040c0441c40101c101d1032424a070001c11030015802c046d400f02000c51907000304038442965032102c2d001d00c3c41b400300900460000c5540c003801801101481d88410020643d141c951020001240042c510400003281700d1054030f200042c40f240304c0e00000243da4021300543c0000f4200003106018100d0342005 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 669148498 1250 669147248 669147277
    0x2107080d0b030303040609020108010f120b04030c0209070f0f0c0302100528020301211709041418060106081501050304080d060f0608010905012105210c01111608 71
    0x4200d40d030760074030044d40300320300c107920024401031503000040917004140c20440d00042106402e000c4202042c4002c00025032020a468166959140c1104c520150000003900482d052040c0320f16903800c0b003004046092150f540c802840f0f41c0d0391040340e4155000ca000b07409a0000f18151050b603c00c5d40000340d105059000c1900f0300704042540750300500301c0400640700c0315030100040c8402441040010907005010010b2944250651a50b440307000550582c01c070121800901540700d510385400c42902604542030f016840c0c17421034450f00ba0b610014009980e98002d00c800400d4080c041e85038503003d00c011464200790100e1000042d141580045c1c81a1424102400352501c0062580a484060070042110300002071030043c01401020040e001070003c0ea0410700181b142c0030420600d4132400c40c662400300c4808529040c2a0b041442c124180d4001100ea000075146c0b00305180c008040010001c0c00800c4030614000e116001401403049c610328000d1507280460106500c0300140140d40c10703418a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 669149748 1250 669148498 669148511
    0xa0b060708031008030c01020711100212131a0705010c11030316050705120c060109090b190b030f0d0f0e030d0509061216030b0105181504030203031b2107080d 70
    0x4c246141c11203505111180e400082007405c0102c0c0d40780503c0410130554840308144660f0402a4a031080400d1005070721402141c1d181800158000e41da000b021203070340c8143c0c80c6180c0e0301c04c0700307090b0300070141034030780e582040480810140308103034112064500708090b5003107855055003c0ca0945e04500b4400400c04140480004510709012800361098041c002c1c544d41c1c0351660000d810048141d00281800d817070044064040b602103640540d100403a05c4140400700f24030380e210b000030a001044a070b090300c1140392410f4031700e03000200002c50082c00d4485d02c81a01006004403401c1c05031400113901504100c615858103070280000c0c10101100600311401c024110461700e290540844411140c00540b031152004c40d50148140c038034000d030a04c0d010b032901045000c10b001ca1145040036600072800760949004084811065801031035000742070f00d948060300704208504d160003c0940f1010300881900506005425440c05004074402d40c14509140441d112640c007500b040c03028140c0b2545801 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 669150998 1250 669149748 669149759
    0xf06010818071a0a020115030305030103061d160528032913020f06040620120f2206020616032c01050a0e071202030c0a060909050a0b0607080310 64
    0x449a0409205007540d43d03450b1181840024291002c4c5500c45481c00c44018040c40442c2e070020840341980d0b0089004681c00c0c403e401030708400c0001090b098490300a8068550317402e03110380404130403544100c0b00590203044688a4003103d00c41c039131644a4441c0e800e601000014406060038183d40101c1074094284858100000708020044030303611540b043e034000d1201140313041901d806505405984043c10720381003000192500b55800110030b103040e80160f84009190041140621a2150b01405604d4499412250303100303801120b01841d04400350105441d2004452680108030741050b4011f10064654803000c00c070102e511440c04040680314528100400300c00700c0c00b05441640d00c4a110308114292030210308480c000340981030b1150801b14403034003a03100026600240c8040d110030341c0807500c01c2e10010b45058045100365410000303804000402c0b44c4c01c25803010440d40c01c000148450b03500c034100384045400e0706100c030343d03c014207000a8020030240c40c061923202140a4843ea01c00c1d8480 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 669152248 1250 669150998 669151019
    0xe0304290c031c051006180803040b2a03030c030c09031c1d030616030204090606031e051e1e0c03180a121112071a0f0601081807 57
    0x7851000c159100040d43c20003645903520b01803c0c04240c000c02c001d90708285001000c0314141c0c0c03040380e042000301c3d032100c13881c1444c0a000c0b40082c82075004407075590f1741c0c03a582070a99130440c0c400070380304151500c8082c0c041d9180402c02d04451180201446c610341e81c03001050300c141c002500030f441c1c00005210314000f90710100700c242407a12240a458030300030800030000f0000710040d80b54800100030440d8074442a1000209580c00038802085100400000e4100700c00a00495004925940c2000c1d40090088d8240e448044100b940c6924a80a542800102c500352030080e1141c80c1200042d1890001200244440a4100355415500d15202402d9040080d0281081e210a144481c0000034800c590304c3c0890201540f108170b60150840c02c000d0740f12240202d0348040c0003414409100d00882c9040414844640000b0080c0d000b19251b403021b0400350100c0341d040709040d190703210003004680f42c1401000c80e58030540d0b05a54a00d00b542e5480f04a802c0c482503a00315501621810301c020603104d140 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 669153498 1250 669152248 669152257
    0x304080a1412010e0c07020306071211030103060504030f091a030705040e2403160b13050a06020a0218060906010f03290a09020901020a0305090d0212010e100e030429 73
    0x40300b0305000a941083c0030b00c030188402820b40d40c41480c0030840c200050324042000b65100c04941050000304141180300c0d4083c204192000a4407140000040304004081c0e208130700541c005d80e074102c074080102c001503403c0b00e8280168140c0c25620401c104070b081040c0021640440c00b49400342c141035541c0700240a030705041d1035219403000c410504103180410603810400001c01140107040445505a040002200501a6400d4080000b036808400c00414032240c008000207022440c10075541d4800a4440c400300700100d10800303601d050341c0003c0440030005409001c0c000d14500482e141c410040d5114500010480140b40e191480e180c0340c1001f85003182c035986110f074180c0b07114507416410410703040500e8120805403841400991b4840e6030000303004d04c4581d81418410b99a00f104030000c0c0d4034161a1500035408812900044180c240640024140c005035604554a40211011542c10f645040f02c0203103440d4030600c010001c02440c0b0f800300c1e10002d04286400a400080380362000d45911 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 669154748 1250 669153498 669153517
    0x30c020d0b0a110a09060810170d02060c04060e060a0c12050a1103121305100906021804060302150d060f14130b091311091009200304080a14 62
    0x519800704051148107000b400e50381d03490b0000613450b00800d0780003e0b094045030f0040701d04014189002030540c107400c0728008042d080c1c0024410910f014800100d680303c1d5000c5000d0014003448000c11101c0712120151007d803440ca803a0001c0b054402da06000d000d0b04040c146800b040b00303031042180404c00c440c0e42d80711000c5440e501c0750358413085080042d0005540718a0369840b94410021076040d24a01035807a030308002840444610701c0342d5810701e94a03003c401e86901040d2413a00c5003403003c200459006003411403100e446502c421130a101040119526444041c1d045480c0c4100740c0380050201000340700d0104c0707020340000c00c43e40324508208001c0f1290030009411480403c0b440c0c3c11b10384002d580800003003941d002e01c801740c4140041404880044c18802500c02c0e640e120034200001034004118005001c0d110344003600d0684160f04c0342c1140780c032444c114a444e026100400c0c05500060826100d5441030161443c2c682d1b50b176420700c65216240c0c0743c0070000e00d080b00d030180458210007401c902c01d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 669155998 1250 669154748 669154763
    0x3091407080c12031e0f0c0d1715040e011409070503070b0421030318030c060506010516080a020115030b040519050c090603031b03120c0a080a09030c020d 68
    0x6007469071491410034165122803080f602d4210f404011240001210030b03141034410300245a48400b11280c0c09800b807007194107100c56010540507690400000c0d81b0b180f40d0020703503c800713404050855000310094180c60304ca00e60861071005010900349a009a144284a000002012450328080101d04a404e6030101c006420006042050745402c004102c050706800740c2041c85c0626001e2a920000e00304103001d40f400801008d482d003814042ea2011908407008911014151918903005003003c2e401101210313075a1809011440e25480b850541c1c000309403a0340e03240c0540380c0c0361322b440c0e40c0758008180c480115034071291000c1020015501440003944500d118008905141c41c0050804040601d8078019240c5505410003254000400305100e04080d00c40c1402502c0c2c1c4008242148100003024150030001c1c64a05844031000004041c03110708000268039a8603003109507401c5101e040d9003640040c601502080e440c5a80f035022054080c40703410800c441e03078074035408500c190a5800098070a00d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 669157248 1250 669155998 669156013
    0x3030c060619120b0408040e0a0e070803040b0a0804020a090603080712170609100506040b04140603010b040515040801090f02091b1920010b10030203040203070603020a030914 77
    0x10300b030115842c0c207540720148540121606090089a00460042c00a0f14440c00c5801150900801d07004880241200c0ba0422405181016001020781201c09107a4030a1040f90400100c2040110584003640c940500c0d0600d0a02024400c4402c918090030503030f400304a207800040d201c0c04500c51000114890320443d0780b640e009003040310501c0d00d4411135100307208c40482c810203440c2031070f20b1459118100304c4c0d00c0385442d2102100c14114200c281c018542248000501103020341d0703140c0141c030032917459500a8402002e01d00c10f0002c0c502080c854044402d005010601c15407404070280800f4849840e011410300380d45411582c2528450708003502c180407844030301005e60404128495100e00784268480301c0c1e40c046000401c081c814030603100c0050300c41a001c00304a5214030024038072821000e0a003101c3d42c0f00b1100460080c002001c101d80305040003048800201c0c024005c0d00d1003a60002c0c041c0c085103103042d0041d806544180110b804156031240c2860001307005005515503801c1100c02485903 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 669158498 1250 669157248 669157261
    0xe12070f260a060b090f0403090b0a0c060c020c030f01140c071e0606090501061b14150a051e0709090b0d0b090d111b0f21010e0c011706010c080903030c06 68
    0x10003101401b440050000e40c401c100100b42c0144040044031060020240e0350461160219640c404444009143d54208140d0f84501d607400601030f0030382e51084050344d40100014110900700d0b016045030000c0c00345031700300142042c0501809402c0d003a0003003001540066040301c102c40e16040c0d224084038241e036070394000d0140342c040740f080074098849400d1075000c09983c42848010101c0012000b4080c0c40304112074021004d0034410846190707856545248942000c9601c1e10140500729002c0b08103801100740c07005900003c0003001d01a40e202c0d29040032190820380b001001d0610071452a070010714071300107200040c00a1004501c40d0409002070065044100401400c8624801604903203902540101d580e103d03c0c0710401c200e4003402c54030f802401c51a0b102091030b06000f40c4007600c614554403048804500190000b982d1105a14240e131130032070302c050065a040e40d02c544001d000e5001070b400139480b5409803070040403550103001d040f4106400240080d2540d4070450401d1610703042031091064 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 669159748 1250 669158498 669158509
    0x601060f0806061e2b15060c1b120305120906010f090f0e030313050c0a2303011509090501050c0903030720030a030e12070f260a060b 59
    0x200e0085240107401c0d41001000a4554010400c45050009180711010020034418040359502217040007007080381100314046034100d60401c02200d49941c02c10003500d91000101c80340c60700352038240d200c1c506200341c15280c1115a8510813500040061200c6000c128000c089074141502072082d5180c50780d50f589680c0508500c0c101400c039007130a80c400320050041c0f445201d191401d46400e500d000030030484421071031000d0481c0c41030043c1140000024881c004091104c4104502d000310116024803000c0030510051454602c501d64041d0016071981c5000041001c203860556001400428207070145400760742c0c0c40c40c880e4032030991a9030700c003058400c003e800c0c0903c641c0f0050300d002050501d00315030080f9499202d03003900140195030fa18804012a042c3e0301c450540300e0310180071030300003580070316000c1e0280d04035007541d03441200701c101078030850440040e1400554111216481c4050b1502000c0340020040d40d03190448403140400212400c5410824030ba251401000c0c0850002404c0c0207028 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 669160998 1250 669159748 669159767
    0xa0611100603300806060d1524050304080703030216170c15040503090f0a0b03041b0803180f010c0b0f01060e03240a06120c03061505090f09030c0708060106 69
    0x103c4054985905040181d0841105030384088184c4005603103816007002000203240c0381039500381c4c0040605001c00c52400c100040d440c191202035104641900424003920140402c4034024003d2100f08210b00c00244240c000c2c1c0a160242c174038181c04482c2e0b554a8030f440701145410640011804203801520f24010481c14014401d01e481c941c1440c245500c480f0780741d200c0c40311121701500c10081040b00648412107210002d000e001c25154490525280a483c05000c500900c1da000601c40400f00b041c050200c215400280000380301c1810300302c0c0b441404881d0155084050502c41c003070f0494404a10b101040030301c10002c1070205603580d07040010203400d4034883c4444900030740c01300c8842d001c10400001d8425800304440a60840d0350b40b8a003030840940351a130011826401c24000c000f00700601d1640c448240e0744103403814003042c5814442840320f6102c0d8072600358004440303c0070910316130554641c15001001d40c0242c902d41031755800ca140c900f40c10380d801601c442d8440f200400060340c1c40301082 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 669162248 1250 669160998 669161063
    0xd0806040c0e0f040c1107030606140a1d04242009130b1c0602030910020c0c04110d050106020d230307030b0a090c2003090a0611100603 60
    0x201100c02500b0080750450351402c3d410b40c01035503680c80700098180241a00c1752241002c5046501242c0c4901d0000c0152113980310300c1600d14150181802c16145c11141c180c01d4036200d04c1c00010841002000006a660240003503030f546d41a1407003250180d610030060040845041800b240101500c0d00d00b011110101c10f40710380048092154040c0ca0755603580c044842c000c0d1100115024540740300245001401000310003240c5400140803017040392076006180b1500c418002d0b2030020031006d4405081c0d10680704120041d411210b004c034414034103603201210010706020258281948481280300300c0344207800c4040940d210020f04a68164400c1c056800d120034083c050712180100b08910800780006000041810348500d10004980c0341d00b187d020050024030b50a0000808a040280030300700c01e000c0e1403144c4140c500030b000880d400003048990140b809801c01582500e4000304030b416041d607150450342c0c0d0060b0b02e0041c1030360410b4061031002d140104034140424400702404240400c5400c2e16 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 669163498 1250 669162248 669162257
    0x7060b04150311060c0607050c070b04030606090c0306030822030c080f1c02030301450c020f030307080613050c090f010f02070308092d10080f0403051b0d0806040c 72
    0x2aa81706070404a50650480110b040c07294496416a6039541441000d41252241e050701003400000d101194000030b0486400d02c000304400c80d0000000c40035140c00e400041d040c480c2c2000701d5140030140a00e020b621220700380c040c01010ba1640c0e105085801e081d030080d6032640c8161000e08611205000c032000791802d900c60a071490041c076501946078081403044240b01d00c0b4410505070700b001034094000c002c601018003019a4031101440700001400c0340d19101c41240303800c110361446800011850b480e4942503000314203503070350041c0c01c580441004000a404c0080844640b101e610140112401402c1c6051641c1e100c0c40442c0034008045a880c40450401503008008014281c000c50340300182c9401c850507a43c0c5091080118510f03032100e440300703488410b41c400256880340d45c140c0410120750b02180c0c1003502d00e0614004807050b14050713a02c0d204501c503140109e80024000d100a155030940d00400030f60040c1841da406050031000145180070514041c100115840c03e4400c0a8602c00345041 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 669164748 1250 669163498 669163507
    0x50a060c08030c12090106030302160b0f0906040f030c141507060b0105161113090b011e150309020f06030114060d020909091c020c0f010507060b0415031106 69
    0x40c8558042640900310440000c003103144080540c003101c0414005000c420600e0800e1806031b402030001c0c0c030040d030040c0140c10100b524202e4003000c0c0012600e00410075030401290107000007240d0321100c1c2050740500c0070880015102910790304200210300030107460201c2403a1140c5d031101c00743e19001c0340e407040a000040c0d080403400402502c1d6140e8101030001125524080162418454161a0740100400c110018100292641c0c0d0b00541203064074582150b061055a101c01e8884c4102d008100d510940010b100440e240c40840d801d40100c1c1c1d441a006540c0d5504900d8005d40050700740c40042e45800340c54055062542e02d0aa01180607070b0b195246614000118506440411144e84540000a90a8075509440d010350b0b400d0400101080148c5c141102d001c0d230317918125075080151154000704410028004500c0c1400604007800301404820711000440d5542c1c45008201c0f0003030303510b12a0740040e85581c0305e0410703060560780c0c0100015086041c0b007a1004a00c402d01c0740719410410 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 669165998 1250 669164748 669164759
    0x60307030c0e0109361b090e0106090e0715090b19030513030206011202041515080c070b070507020111010c08100819021c0611030610030c1422090c0306050a 69
    0x3200803100c0d0100174083c19170903101c3d1030031401d502c1d101400c00509a440e01c1011410155076440560b03907003503a50082202c01e50b00c4c00584180c80e40c403124465143c1104408100c800e41070700005108210fa8a400c0c1600ca482d0803420005070032007481000440010084281584c1e05407143c2ea03000085d442c0024078180031994020b43c0d6500500945071036400b40d181000864480742c100c803060902d81e0b5000d80d030f0291610850341c2e0040307840580100148429000c9980e1601d80c9080701e19964001c405507515176190a8299020b078441c800481c1041400100500500c1d000e100e803a034603540c1983c5541c04ca040034032103400003c043c0d4000340b4a5401104983c6014000c0500030f00465606607182220822114020700b20f006849030b01038252424603001b82c404076945001540b1861045890a00584d9120000c90860f80705441e03103408680035070845003007040b280c07000e060140750807844906d907540030a0b16644907002603840580c507280c0fa0f001d04113000341c144c0180000740c90142c40e0409800c1c0341070b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 669167248 1250 669165998 669166061
    0x50723031011040b040e0a050705030405060c070807080c0d0e030d080a0b18072102040501020303060103050402030c10020c030d17070f030f021b0d02010b18060307030c0e0109 77
    0x52031010340903035030304440d03614600c0c080942d00141000e00400f601e175a82d58200386101107044076861460b07480d1000062141d03006138241c9004641010003016691789240c0e810a45078851401540d0098041c0003c1c400101d0800c020103041c5100000303000101c1c40f80320050312112030b00d4481c034400e0304140f181e075410780d500c086160b0313010607202c0f4003144c121000f0010501c80b0030b00e050079100c8041e49004220405401c40c00007030031400c100c003141c00044542c001d0601240180d0007158010381081020407c158070a03040741d81c0090005040e034404031218800104150601d101010144c0c0280003990810b00d03003440001546003140c2800c84c025190002e145904180041c500010311500d0002d052105103c3d03400860711164400c0219950341140e0514031412002005040a92081d030300b03070500d460304c18024a03202502c0940f0300720750300d982d00c0c07400d003105100200155014440d5400c000040750f900f88014000701520034240015506200040c002c0d29407001c6448103404c001507910204100304d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 669168498 1250 669167248 669167263
    0x70b0f07021020040f061407020109050120060112020112270807080d09021e03030a030209120102220e1605032212030b0315061011010905072303 64
    0x1a60b1000580180a5640301c43e0800b42001605a00c4400b01d00462901c0c03071619500142d60094942001c4e0300e4816000030681e20070044001c0c0001c2c00079000f00641e501810130740080142c010404065080c2901c411032a1000c04d81c024611001c4455428065503000602107a04614a20307040c01b019401e01e229604d641100a005499500d441c2e11030f42c10300c21a5402d413031003607902100e000da07125542c0d4107000251201e4071050b071080414038000e1024039405a40c00c1c50305500a0060f45c01e0a03503400058000f50042174100b41c01c1525000d5103000c0510a10041824116076242c020000580c800c05c0c51030002a074200f81c0c3d028260381c0c180650304440d01c242803403007011031901950303d0b594007a0460f401c3c400c041d1100403014180800703804006a4084490b134801c0c1907a02000300651f080201503840701d41140d10200c0389c04110104a0309c1c1480e490b0400d21504504100395642c2402405500b11624a50103840e1070300704043c2440b5017901409c2c12402010004010300444080318002500c0c2c00c0c9 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 669169748 1250 669168498 669168523
    0x90902090d12140a0c0c0806040c0b0f040905040c0608090d050403150212070806040c05250201020f0717100b1003050402010905100c050c150706090312060803070b0f0702 75
    0xc010401041584200428081c8040034070410361191a0100d010740000f070f241742d04840620303031001e000c100800001b42151065400180c410300c22440c2080d144125445258195452031041002182d0034060f4025140514802c8000350307140d070301c1c200006110080150255950f034205c0c4840d540f41641c001c0a1740c2c140d0390003800a4042040124188000b8030800c0207000244020400300100030b030301b06404074400c140c00d0340c050000210450b42100c15204108104081940b00701007500c0366660156a9203100d44103004072100030407c014907a1816003030398801e280c00700c0c0c1d545440208450a00900d40441d50000b01803044019000009034040d40500c0c0c14803c040c0c1d680005815a880365a40000401020f0104012070311200b80080c1514812141030b00c0a01c1104140c0800d42025214521450b01070908279040002d141ea42c60b01034805c6060950401c11207031040c0016444c24032600c4014212040296034800381071030040707580c01c0300510301c188800b0320600b0844003540201d00c1440c03001 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 669170998 1250 669169748 669169763
    0x30a110103020909090109032d1404170303090d02030a08060409060b04050a0207021804030207030f2a0e0702010c39060b01090806091011090d12090902090d 69
    0x14000407002400b910200301d42c054040d90510a00319810340c08490300500035625500c03e500f015400000c02d0111119400800710f4041c00160f11030710556083c2d0390b41080307a004500e4165034000018400310b0072168080141c0001051101c802c0041107120081c8503240069400c2158a5002a0846d00010409801035440308248030400116501c41005144024010002420000007040003508051001c0707014031300010f180c0d0000c9900f004020b100380d41c1640100121419555047c203000e0500d04112940075030714590018440b43c90302c2e00303040c808010080d10740b0b4034949080180721500140a103001c1d03924143c441902c40d9404503e2142401c61440c002c1445031140d040028801080030340085901e40003a052020070143d6002159001c2c8240d80da11500ea0b00c40c0c81e9581c4901065850082650113500c07032a0813803802d5040840c0c80218107036250306106840300401d04510480004440c100c108030b104820042d00103d4550292100400441c10200780d40049001414040000b50844 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 669172248 1250 669170998 669171023
    0x1090305090f03100609020a2304031403120c03040b010b0c060106030e030f0d020403050607140d0c090b12161412060a170f011d0c010e030705040c1e0905030a 70
    0xf03403010000e100f001d00b0301150400c219507a034001c04c00250007441c40c00000131600ea802090100480c01c1a101a0308495501c1d0700e802c0c0b842ea1080718802034410340740c4d0b203400b0900090302d10000e00703d0854480e595500030940d681c41c040ca000465860305801003038200c6014840f01d144a0300014041c0e056540600740020040034046000b441c60194548202c04807400098050f5040e001d03401034422240b15100301c071190345440300c003a107000900e1724450320382d003505001110101075a038209008200450501c120342917194440c1001c42c0e4052050b1000b100942001c0c09800d9605a00d45407505d0104d20b0a00580a810768505138036100d03944400c0c1380d429100e0701090640d6202562000204070030002d0b0b02c1491242640281c5424500109102d80c1d480c01212001d0191420101c1e000340d201540903207915901d030001580c015440b82c0d00c4a40610500300b020509451724842d0f00070704100c43c0c5510400352110004280c1a5507411044420000c41c0c0c201085281c600041c1c500da210381c09549800503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 669173498 1250 669172248 669172279
    0x3120911010f020102130807051302090d06020304110915130c020d12020f0301180c02010902130c022d061e070503070201200c0613020a120501020702131b020109030509 74
    0xa400b1b5020f0010010f922500e001810410000f003604c102c40c015502040598030b0171000c0012070182c21a100c2c2c01052045624002960580c010342e8401d00c600103030702506004101055000004541d0301c4214407121500032640d28005029070005024080d0600071000c0d540c000a45840b2420040002d100000e00c00d048240780f2030301030711030070f050a040c000d40300d40c2d40d18140c03114158030240141c68280750201010342d00744103004110a0a0700540785031102150000000d0090402c001c0c0d10045000c4c10443c0d00301d90750000081c860100c1449a00c1382004242400300c0d0811901074036880074951040c400c46151102138003201e5000b1303a5070801c41c0e00c80d50b50020690151114011004030160100c1d094000340310f0000c050801413a9050455415a44074020755070b4156088901940c841042c3c0000c0198422142402c80714520801c009824061107901180c102c41408480501d41500c412000075105603082d40f10760503510754402031010203410740b0050514410140028081e010810403400c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 669174748 1250 669173498 669173501
    0x709050f0d050f0610090608070b09040b220b0109050f04021303051606030605030d170916030b01170307030905241201060306050a0605040e1b031303120911010f0201 73
    0x9690488280e40741d2041543d000b544030350040320001c182c01c15203d80030548042a201d004160360140d001802514202519140240c00081e6415030107070300d404c551020398842c280e0010701010030403a00d1001e0042102d60030700f40c4610302c25203410025a04401c014903039510745110318a10040e100103940e0401e803105180c00311200c3c2c202810520900140259108402c0d10440c01c941c60781d0b504001e083d80392410507480321041006400040d405174211041d1402c802805a00300b1750840490f140c00300d01d03018030610444143e01c183c4d024140d000040100072480b0000c07401c2c6c04d007454003551410719695809010103902e40101030256110005900031100042203151100c007103038401c41e8903184804840c0414601c00d0160200107810400300190504142c030310001a9200f5031070b00b604050520f0b0100040240051901d051242d02c078490070320101b4882c0007140513446c0f44a000c2d007801401c2c100500400041800301003134030725000800c40070510320050122000c60929040c0031008003144100d0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 669175998 1250 669174748 669174769
    0x403020d05010908180405180a02090c190c02100e181905090604060b01020708071a0f0406081609150e0102150112020310020f0405060c0a080a030f140709050f 70
    0x13032140c40c0005824a030b9081c0003503041d404581c200c03400c0c450b80d5076984000048401c8031151261581c002c034420310040c54460400f5900010b4840c0031801e01c10364203140382503020350b0800c80000c00c60840d000ca041d0b04140c0710b4181d00070050f04040c0b500210150200314011072800d00b0219000203900400c07a18410f05d405440d01b5100710000380b00b1410f1030410107445180a8404451161400d0b180e80100c0d400441c000d0120303806100a845294581100071075041c25603031a00c000d64008003c103020600b04040070780060041c55075000000d03e4007004144c40711a0b01d003004800d2010213482008151a600901800d9580515010800c0d51040c401030745068540070307840000d2150301c000030038948070300005190040e000f2000c69241d4002184000101c0c891030a880d13519440403c0140054100413004202040781202250395405041c0c9844480746c03c007600f00000a5180e42d40a06c1000b034a0096100c2480c41c240560540c0c10b142402170080900f52007080c0c012038a6800c0390382166900341114 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 669177248 1250 669175998 669176003
    0x70c1214030a060510030501050f010c060b1201020408070803190e03150a0506310b120a0303050708160c200a08210301120213020706021c0e0109080403020d050109 72
    0x103030384074100164000041d01d440e00906004e2981011070b468035610034010181200e0018001228003010440112a6610160429110b40d0b464041e155215200c8005100840300050001600d49042503441410001d032980700440690042c414090903640c122008440d00f555800c143e40307800240004242003811a0040078001d85100c010081c00300f00c141c1246214810407684005e4014680b0507180400d02c4e01024600078641d6481d5100c004a003d0303020941c1d00500900703401c100ea038550f0519250803030303d40e001ca00181c4c0302c00c10310104941012403241c0140b0303009030142803c000d03104005d081c890035840181894014000c28404c0034440c1c1c2c00031098450180015400507150301080356208002c1d00604800c051180c04110105010303026603050b24040c40f0f413071412104a8003048109600710032052103090b801c0208000041d580e1000b0a0f07800410040d440261007041d84440c00c80710503000c160707016418203483e4030010340e03060101c030b050b00e604560b8881010082d04244c0e0042079034a900 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 669178498 1250 669177248 669177287
    0x2030306040c120e160f0e0f13050604110102070b03010e28020c1b0414010e090316030e01090e1b0c1501081005060a05010503010303030c0314130b010e070c12 70
    0x4504c102c51012074480e4074422071050860180c0d0743e4102148280c00248200c1d02e03001c100d603021a41c01c48000300c20300c0d0080d981e0705051a58009a86650341048410b60301100d05a5001810314180d580601969000f000200d40c141c2c110341c9045206c10303003120002d1074402c805000e0224401d12070414402020010659001103407520042028141d4460b001d240035440011810030100d41c0b45080c0c001c040311610302400b8203500345d103460911841014040c10004007400300380700010b907404c00c40c00e0242040c2d000c2e0b6260f14000e407404001400048840e0405c08180c9140e2081002c03000804106110f8080807070042c61b5542280c1c0051401c001d904402820441c1c41440001521a00040c1c0e031b0510052820003040301e62208002c0000fa40c10030310955010407018070041021a00960211409038002d00340070400710601e070f1101c44044011681d4600310740d0110151020300892038005030141414109980003420601d101500089154000a00741504c000032400a14440c234590803281d10100711 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 669179748 1250 669178498 669178511
    0x16080307030608060a090201140a050412080d14240a17060f070306080a020609060706050a060611160e0c0d05010605071e021023030a0504020f010f02030306040c12 72
    0x3001000b4050a02c205003640c131641c0081a2040024400d05000c2daa058407040c1d040501c1d5030080312550028881c0409102d400e1200203115611190055001c41c07168883c2913031035441407a42d40448010319007914400440c1e00400020f001003290350400840c0c000d201c800110705050009902810507040f00c5a11010200c148181c0c0100003052401080c1404600315140d0701c05100300c08564082c030640d1603541c0010480c0c0050f08200e802019120805820107140201c1030329400c007500c01c1955244146a030711001080025888008605480ca09201421001c01b070b60f030741049c2c086103c1c0502c001f40c840c203c012400554a0074100c685500190304188160341e07441ca0003811581003031030141c40c81c1b4900480e44104410101e0641c0c0c201c1d50041070841d810305502c0c801c0303512803214070b050304940c0c039108645140c030003023030024501c28181400c0c003140a03d4140705110300490104903080c10b00c1015082c5000094011003540c0e4441c0007a17800154240c41700c034045840f80c80d0305500b162030350f29100 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 669180998 1250 669179748 669179761
    0x20f0c030f0301030b01050105070b0114060403060e0d0e0402040e06040507110f0705130507021504170c01060f2112032a0f1833090305060106080609060105160803 72
    0x7006181264000d0b030901283d6a65000159040c0c42aa580240140e4900006100c40e0b003035068810501c65020744010300301600d81c1e880c00126411550307510142e600c071140c201d07442a803283d41d030070f011741c003d44003541018548a01403004000c0648994415901c42000900d00352040c1260304400c0040000c580c400c1c4006050700740c035800d103401854050080c04406060b1207680b409518002c8245900400d02c18036031724100381c0e40050142c000c40da04940050a03242d11248800682a07544d0a0303800028407628000764041e0043c260351200f0580301c507601c20152807404200d002000c984d000740709441c01071030004c0220014291125000e1040e801100f07041d2a5610401240e42d81d84019100c010f0114003501e01641c0110a10440d6226884c18038014003040001d070183e59030300c09010030601685149410030300c060700c100522000c0012105000bc00900038100030041c0100380354102401e0504112001c5000f1590040682e418814000340403d080b030441d20110000c6a00700c001e0548071304000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 669182248 1250 669180998 669181027
    0xf01050309190f050118020f120a080c2503020a030803071209080706050937050d0305041b0305121b07031101021e06070f05120a0212010803120604020f0c03 69
    0x2100c0c2913419610f4412085040c0c0d400e070080414190300207105111900c000020000510814080f4800300d0080c025040d00199000d005003240794480b001400a1000a100007003c074640101090304481c00e84a04201588032a03a0b0381060b07a822801c5250380703948554098407900c402c9100568064a098044801d100c0c0c89000313030020501c101e03402e01c613645403840d6540c0e84051422500034400c0d2510b5045051009104200302b90342d04800c0c1105042e401c42e1281814641040c000d40f020035211401c101c104449084039010203290a13038610a110b01315103034190340c0c00d20703d0f42c3d0b014440700028150f080e03903c14014242d100c20080c3c048802250f203918100c40b446015906080c0036100d001c60140c007c0115264150070702500000425059548840803a035011400d4200b00c00d00c2000c10005503c4003002140901c50344540c1405692030740c0c0340f4070107880170070140d008400907042402100c0661000e1500e42d5040b580444000d0303110400c3c144031030414415154000160720000a4a00c170180d000c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 669183498 1250 669182248 669182273
    0x150b0d050a0c17070e010327050f12090103020d0b040e0d140f030a0902180103120f0f0503040f06020d020406090503010f02040803030a0c1e020115090b0f0105030919 73
    0x1e03420501007061003040c00e455442d5003141400e400c0003c1c10004004074419403020302e17009414540800c0050304d120004203100903c2540b100b00c1504003404006000040045403071001170744000b4010000c0460029001d400340519103410550006040b1400082541000040a10051040004011031846141c2d124042100d0001180c103820031401c0c8815420b00361403407082601c4106107550350b02ca0b02c4100a2a02c0101240e000c0c0144080604469a1081c00da020310311445120324180e0031103402130404800c80071041d0130840301031b400c0c044035a41302007603e4019500207000070641446250810190003411042070f140707880840d00040c100d51240390038040310b0040e0002c000c030310000c0c0c22803816440f8038041c0c08642d5108002182c040121030b0312243c44000d1518141c030314001e190184540c00e403401c1c0300e0040140e44501d8a041a05d115100342401030130303910340821101c01400046540101240d440d5410700c800800080c040b0541400b611002c0d80d000114107448032694540282d4400d0b4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 669184748 1250 669183498 669183511
    0xc1e0616050705090906060f0f010c02270702060711060135030c070302011106041e170403060c11060712092406030506010b090f0909150f0105100c02060a03150b0d05 73
    0x10400d5500c8d2180c02c10140c0414290f9060795251003000e01c03602070004440d90000322107400003041c8200d2602e641d52585450043c44154040c100904148000805034400405200c0301c58000100410100710148460300010480d92034507680d4940f5000310301555018154110345501001400c286c51400200304601901d1003600c0b0003444c600409015941c6217012207008040c101120280c0300c25110101e07800351942c2c030a2689443d5446090071100050704a6481180e4850700e40d8415251250030200000c0314081c1300008100c0c034a0035410041521203908101001c03503507035810750001d1014040d40212840800241d415040c80d0054903c001060544000d80b03460080e0400841c041440800300d9840400c0107010002c08a8000c08000000030058040c410901c1840c12100e01e080446072118490740b01e0180c00107803907151400740300c2c50361203500c28007040003070120b0544010baaa43c000d682209090b49400100c401c0503804032040744049400c000b0816501190845004106400c034510808 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 669185998 1250 669184748 669184759
    0x10e10060f091406061612050706140f0c09010905150405180f0606210f0a050106030e030706020901140f0c0106141f020c0a080c1e061605070509090606 67
    0x580c1d56001c80100c03040e590680f01d038110b1480100d002440e0440150540c4035209950405121480e074400c1031000c0d50358102404a140418983c0070301140e0320858500641e407000a40f40d030314045102010b21702c0d000700048190600400c0290300750340f081d001c2c1c60180001501071004410321080202c1075821071710400f445001d03404000500c683c66040b41b24024211601c0410058480700e040100315080540020040a400070140a8180d01180712074020841410b0000c00d5040140d0b0700c0702035410503080882450b007050380c0d03803034250b80c00000c540d10079070450300068440b640840102c030804180d042200d240c100105248000c800d0740e00040c10000fa034900200482540ea0b134521142208880403564010306585494090007007200d20940704103414030640b2100040800081c444080e140c0060055900000d1840c501c1e08140d40d0b4400b01c1444424400c102401c84000a03041d80300340d0b004041d104071200d10890400070104660700c041e21004044201502d043e1300c0c8a940ca0350111040791140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 669187248 1250 669185998 669186029
    0x406090b040507050c150601180909120810050411120c0c06090706120203090c031006060e09100510020c090f0610090f0605162013021812010e1006 65
    0x1140113204640e4402901d50140204218078050058501c100400f103034103025003d00180340324101d2180707085c0544400240001e151859040564100000703d07480c00511901e5028490b1048040ca045001c0750300440300814a07800401c00080c00d40642d81000b5038241c0c2100600801d0101036016110682c0d41008030b60541d0b444458049e580c18983c45a003000c00c0208024104600c0c03640c0007142d2000c180d0b801c40300701070074580109281c8440c0040c006c401c80e9075010203112241d440322030864607690413200144207080000141c08001c40310300c03c0c248101007100400821500901c400c0151180040244550345043d910048240710212003017031240000c0c6903024182401801d4450a40e07407800488600c02c1d040042c1561158494041720480c600e810840000141740d40b1050103495203102900c40b41544200c041c015140484000484c0c5035005209003008162400c5820a00c0d5108640f1400001d2800b45c0441c0180b40c03194015405029220a4008601080d00300c0e0045440d1083c2c2c6a001c0c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 669188498 1250 669187248 669187261
    0xb0403051e1602130209030604260f1b2e0c02190210210905060121030f030204170a12020c01080414070e07171e061009050406090b0405 60
    0x1d00c2115800420088410b15141c00b5061140c13510744010700d0310000501d41031901b80028034004089a044528440c0c0800403401c420800b200183c0c80320741e42d6101c500700b03854030380044034074010484d05010402e02d68055145001d010000d10500c41e0807442d41c03015541d8031b11081c81e41d0441c200c41d02100e4505018048821620002c1d41030f05142540400a0f40c4ca0070703a40c01c002d901400c44102d841000b020403042c01c000820141a2aa03520f82000009071141040c5442420000164441c402212101020580d040541800c10b031a0f1a03051808400c424001032041d03009010b282c01100c8542d066494000074100b0004501504e2401102e9203040190280e0003240d0f5802c1013002d440c0010920008180002c1019003030020b4400b00c941580e48080e140d02c0b098105241c1183c00300005620403220900921000b040c01c5c2d0800380b0200c01e07100040306800e1751102d62602420031400349001c40841e071002480780c00c1c0c030800b42900800500840350707500c07a000302070a407000b001e43c4600e01d0013001ca02c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 669189748 1250 669188498 669188557
    0xa0509010c0509210f0106060305090c030a051e01021b010f0501091503240903120c0507020a0e060f0406090209011d030c060708130e0411030706050f0a0302070b040305 74
    0x1840030000d00418490011300700c2c1245020b10b0060010042c03040b082c6880d00700001780240800b0f0085590009480e02c0c05c82d04051a08112086581c000c0d0000ba09420205001140401c4203000324201a045041900340c01070081c03041880402c0c00b4099100d01c01140e440642000d60840c1a0311000e02250b41c031441e00394100c4815a04800301d070144030404000080c0d4410345d0354483c81e1410202d80b0400780c003240c1c24050f41d4003114102c001492407510210105000d20a00e8211403191600c14145003503035010640300c00c401d008500344180758000140a565410009000c0000f01030003d2000030354406d00035004e500044c001360701061a2481c80d5086500449881d0300c2e2110080040c500021050203000d0309910011003585e00d054100310450344614841d00120041c00042c18148a529080c00c2604501c0c0504132564070a402c4981e0030045030394484180d540341e904810342b2580d64104810b080c1c00a01c075019008110500140411082c1070700320000d4801c6113282c040c11700e020b050142c003401 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 669190998 1250 669189748 669189757
    0x30f0e130902010c0605040f1b050d03081512011a0603061c0302150408090103050a0903080609060613030c060e010f1710352d07030b0a0509010c05 65
    0x35002010444100011030301604840039550040c10306800c40340c0140c035140140ca804a41c140c481c1700b000d50141c0d08101000c00c00c40d486a0101040341502030410000943c8a50404405000c10910901241a52441c40c20b070200400c0300901d584a0311100749005400303803000e1600b540e108004102c208915080510403a07200f0b150041c1070550381041040c212040d041c1a0f2001c0d411031007007201c038075160201114504d0003207008031240c9071034000030800107045c1c60000b400d2021460030071070300380000f0b0b0300411456000b0b9021a1407400550340e04c00480c14601506041c1001810011800000c3c040316228500c180d461590360191560b086000540c2c5d2140700001860004a0954140000802c00e104542c1c004440381c100290b00c981d01d2224510300c6078082c0e1030740a00402d520440c1e80484101e10340140c4280d584016142030134181380e85007040b070700c0008406d50911084021444000080c0044000380d688511480240c0c240200c80c1c400420341190034860940c41c14900f0443c0f24020301c02e40c0e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 669192248 1250 669190998 669191027
    0x3021b1e040504050c0307140f06040311040c050915030103141c14040902120a0b0901140111010f140106080a0504120e0a080d03090b0604151707050306040b04030f 72
    0x2540c5034800c82080c00000c0c41c004105941e90701038410358013040d541c00e106090040c26403407025248030596004020302c0c40840c4129900c500b0b0100020000220000344824600b074040310006000784118100740c03020320034121038030b61009900c803541100c3d06105000c3c41c10399008030411007805015184103640d035185218601400d214086040103094402e10003000b0b02040c8144240c10140d841c0c000000b82d810400c0c0212100c0b400300c1c10040140014813401580b0002101c102e0199407400c400d00e5160680c0594460400c080c0040880742a5002d4008088110750030504001002e0700307020111044030f0031302944002410000201d0b07640c00a50117200c0c000c5411000900714002c0d11074050b81c207101c000c08200d401405010700010185e40610005c0040000d545000c1008030302881d001610f82c0c0c004cc103007445070307141000300414064440000d609546004400702100800e8503815031038040150311050345449036004000c20032141802c15030099102e43c480524003909041c042e200e9a6101698 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 669193498 1250 669192248 669192289
    0x203012c2e0b06190318020604091808031005030d26060d0f11040605010302040e131a0103060b010f0c0327170f0c0a0b030a0f0b090403021b 62
    0x1200440c070300103070110030341c034400000103020180000070581e29045410b0b051501ea49034442040c1c40340e01030240410b44451203070791840090044d400a50f0601039030140030841e1380d8400d480b41d00702c0341e090301059005e50081c10881d101e16220f025076803120458000d03d030107409101000700106c0d00810314020030000110506903241c400b001c51030398420008007040d500010300c61160010070030803400c0c1c0344454050310100100001d10010700c000d4404542c881d904161040004000e00c1c8000841d00c0c0d0460408030101658040f10b04042c8c1c0711901d810303003035814400c080c4000400c0040680c42040c3c560340030f0702c03a0028941c00f0401510a1010a08043c009c81c20894160028140c0b000c5181d04400109655040701c9849241d94403811944440611b1540c1c45800c8036480c1c90740030411174115000481c0c12010741828054601c04a0101410b08841c254865044140a500c2900100e440f0704015020000c680381c03a06000b580c480c800c1c41c0300d15140606c1d822180d0541070404c00602d05846905c40c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 669194748 1250 669193498 669193543
    0x1b080406050a0603021002010605010f21021b100b1e100f050d020a08010305070b0301030302070e0402060708070303020a032f250b1f0e010303030b030a0203012c 71
    0x2a03031006850000c0030040780c02c0c0d407624040010313502c2c00039071009108030354000241d90342003400140103035810000c050140300c03071740000744074a0030000c0340503a4150b0903050140c1c44480080b8010912424140c00d0380d494042c000d0300381003009581d488005002011600c190200380c0a420954101c8207107282c0c1a000260216050001402054402042c601c41e142c2980b030540e0504108003240c204980c0a40050984801081408070800c00d01001d089420340c0f040c0703994911340d0040d41d140e01500c80c600e00c004860300014150350315281039800103508011040e80d100c84615004000354084982c40c00400c1c5031402c110707210740f504241c2d1502c5040190310006042600c1402c421076801080c482c4000f9081d00c25203c0044000d013541080c810301c6120103803414104600c40040c01340c1508089112202c0000d020402007044000c0c482c110780d0142400102000c102e40070030b00b00700750501e020307402d50709009007004209040c2c540204141e031088240d5120703104d410030306078954a4420294a51401c0c058 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 669195998 1250 669194748 669194753
    0x111903020402130f230609090708070504030501050c09120f0327040608030702090906090a1103010906050c0c100207020a1a070506041a06090907030b0a0e1204030302011b0804 77
    0x6000780305143e00880b020751030300c3e600c009180c4085020b800a02c1092805000a000d00c429802c00d012443c40488010382088400c0c40403401100c8010009020000180301140209004804407405546c01200074407561409a4441880b41d000710400c81c018049031607503110400c0c02281500420001e140a185460005070400e1000030314882c100d0845450741c84107210a0b0f855100d800c004141100166842d9201c50040004c5184020410b45142c0c00c08010003090100200300c1d180b4071a13000102e0303000d8640e0394001c00c1c0100344e07105000b81143d141105000c540f0030703000e019000300d02482c0100d41c0400d121a040c030050b0b0291802c029080135103020700b8000350310b01c6140d1182211071016860b040c0499a11401c2c0341100c26071b826280483d0040f1401e04481b13180e041242e10090a8881c01101e042440070f0a60340c1c03080380b00282c0b089a1101c0801c9880c58640c01004205100e50103e40d00b881e60040c1d0030040d94454401200958a8240c00d134030400000c60600071824800d407500c4c0e8042d0340c0c1d074 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 669197248 1250 669195998 669196001
    0x1b0c061e170709050d050105010e071b0b0408090d1b0b0f0301050f19060302030718030308071d040603080301050a1a030406090c05061819270b030a030503041119030204 74
    0x2412031000d0041c2904081110345601545c0c41d0424080c8002040d19458280c102940c410040c1100007000000e5454140740e4140c410b001c40305c035620110202040d039541c10100c3c03090142000d803a51005c0890303900c006101c001001c8400540d0300929090200e40d13a02411513075440b9600f034203c0c00e21800d000400c03480ca88203044554414000e45456140003003001b071100460740c1d5410042c0480d9000c014404115404440580400c2c0d82494910009066490240410000030a04010800c605180d02c090740341d202d4000500c0000075109008040c0c6030310304040c43c1e030070900404d030041d1b0f4030440000303800402841005610100c3c003036617032842c1c8450301ca0304007902000a054441c0d2401d00030010721034075000b00070585141c00b110b180c0300c840c08180420110b005106004401402401003e200111407041c5501d8115901d40b0495400d000000283c406030142c005526854040d03031001c44249a0040010342c410380c883c0326242242440c81d02080340d0080800070032420114280814030040c00c1c103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 669198498 1250 669197248 669197251
    0x12031306060545100f09020a050301030b0604090b0114040e010903140c071a0901020c0102010c0f0518030304030f020307060f0906030c020c03120a090e060904020607031b0c061e17 79
    0x3c0f8240c114244207840343e12890322074241e60f50383d00c2c5034508030100040510a0f804c00c0151100401c194074284140030000c02e94041130201900c0d2003000c1d40858500d90366503102d1528154401100c04803580d654a011180c211200540c0380120b081c1680ca80e130010061144000542c0d01da00c58111358000f11690140640004076000e40621603608007195201d508070380080c1a15401b005140d0f0b980081000a0401d0b141040140c19603040c4100e444095130072030040c510700c0708240741594450400800b8800b07a140448521034050000240c0031052040700c8001d00b400c240250f044854440d500c040840e071a04075583e03400009400038105001043c0b00b5009101e03ca2602d00c110b941201211000a06181103060002204440051454076071031b00b101030b080003400e080703007042194a00407011030720803e00100001d100343d500084a004140c06240d480c0c0d4070380402c084140e0700d1041d51030a5642000c4900601303002c0b540241c40511080381288000e00d01005981c3c445a1282000008080300c110 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 669199748 1250 669198498 669198589
    0x3151b07050a080c010522111009030213050a060f0305060f07050702090f01080601080c030c0411041e050f04020405031903030605030d0c060c020304080717120313060605 75
    0x1c1c40460401040b00350340640130810640c0000181030130401c1e0b0b0f10007080e41400000360b01e08080e41256000c50701003c41142030b041c0698204600310070703503201280c1c400b510303400081d44001c01111000030041c4c1136004034481c00c8506404c20000b625a4134010320501c00340b00c000c00c076500a6000071602e1400c50f48194001245041c19030400106130b001410000c0205c92210741342200300010061410b0400c0301500501000000e004510102c00102e91140c3d0031104450191b40c40f007155044036100d180071100100b4006013007842d0155050340c1c0f00366101461040501c5050141c52110325490244225011150000c0040c030350b1101030510403071940000103082c2c0a042d99083c00040d251000d03c56500c2902c1a640c44081402d01403510004891428000c1021548140030510120320009083c1040d296518440503035045182a4245043d8100d40c460003030b400c000c028401e50a031240f030140482881004148003980d151420320480b1041d5036103c6080c01345040c40862422601c5185824040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 669200998 1250 669199748 669199753
    0x901050f0c030304021f170c0433030203010e01030f0512030903070312060b0f0c07120f0203151012020d080a0e1806030303040b1503150603151b0705 66
    0xe0300100518580e08803030045611a000041000214500540740540c0c03502200740064080710100d40041c00418464420780340d4880348008154204c03420700c1900c0050803802140705221070840d8580e440701b82e01e611a0180440000c40035480c0e10f019000b81da050315840e00710f0500e50307865610342c0d0700c0d0101c030010180d8490240c2c4c0e400769a01071700c0c01d005503c1200650f00450340e80b081460001e0500400c42149003555141c88810301c613501d8010200c1e200c03810302004c003e460f0509070642c0790038411240d0100b01021900c032050010880c080d154460064004ca054038001c00c1c29032403104000d281124280c054408400051001c002400144190240041c1c8241b4800441c3d64812103658000c44a84020901890011000c1d181c8a668040441c1d0303400d241239501c0c20a4008680e9074003002e04001e0040e41400c00244049120503040401040010200c0ba513100310300f2301d05000c81000b654194042e0142c061003e200a0300180340d20301500c04060088000109442d0201054114041c100ca450 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 669202248 1250 669200998 669201007
    0xa0207061707451706040b010b130906060221030702100f0e07030c030c0b0f07060513150906110a020a0f110d0c05031b0102060402010c021c050717030702100302090105 74
    0xd4480900800080b107585107403002e150300303144640e003040c00e00362801300d26580010100b00029819075003040c1103a40d000300154503856140390300c070100c25041e0881e09110345411800140c40c2d5002503991099800b44404a0515030303034030703805c043e248021142500540e2080802270001c040e0703a440001e070303281d0002002a001e02c40d0a07103542446450f520603101007400e681d040c81806100c02001c801048000c1c030f400d2820100d201e00c10303c20702540901400141d076810016401d5500c040300d412a45500000d61a04d124100840c2402481041000d543c80b5142016a0040e2121002191594001c41c1c0083c44080300139030350f80b112484010400c0303d4556103a0b40f500f1203511060003600b8120321901d40c550103141000140341c0703401c003a52003a4551a01c809201070513a41c003c1400c0790031540a1a240b05c6229103400030038011914925506e5039814240c004109209001c41c01c00d0a0721550150404100d90381240c0340e13941e014140c03000c1e5001768049021941c0c14000d42c0100310180781814a5401c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 669203498 1250 669202248 669202337
    0x60518190302033f090d050c16030506040b070f140d5001150c140703031b0b19150321080c04060c02030f030a0207061707 54
    0x3440340e14813084421850107818a6051201007410465040812001641441d103855016503079283c078884107041c020002648100c09038103000004441c038010000c040304d00d54900d030542d1358500448055501c01d4503080821101c602c90307992080c802280782c1d03500303804c0ca40da918480d0b2a031b03202000e8a60382a540b0b0980321486d074804032008507203c020156400c0b444000c0300d80a1820030300000b80c008006180d21030341103600807942159042d00c0c0b049071300000300380c40400c003540c0400103a0b002501280e0b043c1e0342c0180300000050341000f664030a6070342d4044104103403e03202c0c0c40501c2d40001080011b01c040045d51240f1030918190960030070400c00700340000f4140d019000090b540e001179540504010005c80403043c002002c950803441c51030000550325022499005601170341c001c1c90701f0040040c088005560b0200244080d0251900c1681c0c1d803145000c10281d6500458070800d004a1104000340d400501c1c1c40040da4850502c6484610306140900108a08034050580321140d0b8000322600300380c0d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 669204748 1250 669203498 669203527
    0x90209040e150403080f07050301091a18060a06050301030f030302090d120c0b0601020307120318020901090b0406060216090c050403051b030f010b030c040b18090a06051819030203 79
    0x103201905982c0b44a0500345801c000349801d900a0000ca015403100c0113100c12551f00000301c030304541e8900000aa02c48040000c038440c0a62508000d92107201d4a42e40c4100000d0500041d0007010100c0c0c0300c07007089030f07038038029074450009110103410300b0200f1060a010900a03002041d1011000304250756001e034581e910707a9020b441c600c010000980d56083d00c000c2011888a554001809000841c1030850715512103c0241ca00e0040008150315180d056203141c808900c0c00300c40390390081c1001800d41e140c1c59000010a00409400e10680c00c1460008a090005c160102040030a400f620000c1d030800405401404508010008106d400c000000105005003ea103c010030300300c08030f1012041c90004c0518099080c06180081e034034041e005036243d540090715091015040d2004100c88009a00042c3c100100081d130314402807040b0108010143d000c034410909510404c802c100540300e8800c85007119504036036440c550707031001004a08000e100c00d001c4020340e2107441200c1c54441180810031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 669205998 1250 669204748 669204763
    0x40302041109061b06010e090a0f060f090602070506010603060f0b0f0f0a0f020105150303041703040803040303080702010f1a060904092a150e060a051312030e19090209040e 76
    0x10651041600c8044018001d0113446c4c010300780100580c1c101e0800d07074500ca440e815110710007081411410211000c00c003068100d940100880c44c001c00030f07100a402d00074080c4d07020000490317180c01082c9c00400c11f140030b84103010a030340300304003480c10060400d40c440740709a02a800b1144c1022046c00340da0790300199100145210a040d0b5501d0140345201704019007561005800c00c400d0044c00c0b44140714907100003090318100c561711082d0a00350304c02e41045d04d04610880c1c2048100d800006004002d05401a038450300662144d802040404400b021101c100c6003c2c2d000c1c680005144540745529107011030240c410b41000070400980c2c1c0c0080d07925040c20a4a0010800540452016901c01d002d02150b1090041139800300b11003010992481c020900074089602e544180c00128040384241d00c121f0075203c49528580310701ca9200c0d00c1e0464404040d201a604030001101d1004800b581e092825407180031205503020002d20a08105900d000f130b40204224642042d079480c61041003d00420154 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 669207248 1250 669205998 669206017
    0x31e0319110109030908100603020f280905180a0201020a0f020f0d060e011103061c03140d0501090e24150603040b010509100303020a03050a120e07060906110304030204110906 77
    0xb800c8151911140d00e0500e000a071f10710100d503180200810158454a00c6460290b000319040079090100b0012441401c1312020007031613180c03d5500c081000c1c8002d41c082c6010303034101d90010a03074114200768142d584142d66002401608801d01c804009000100d115040d2403004041c8a0050540d03800f080e50180d803000b042e240c0680b00d25800b6800c6400b840b03400188040d03411601c1c610710302403007c0382c0c407440c994160b60084440c8106000074503105144185004d01517402c0d0583d5821038400c41c42c042c000a00902c00c44610f01010300840400001c1c5810161401c41c01e400d1084c600d99032442002040205150130b918109401101140d64400c0114071461150003510140e504040610000034070007400c0c82d0640000a0061000c00e8002071120704050385449c01c140d0300c1c10090001c071407030b00807220039507500d90030112101d04013280480c966041e11080d680351010703541e03161000c486020706580030140c00e070400c11040c0050306068000d1040750754200c1c0150b1618803554080740d01a40030f03d916 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 669208498 1250 669207248 669207257
    0xa0f02070f020a080a0f1401020f1602011404050d1419050601090605150421022d03030f04060806061b0a0c150f030c12050702070302031e031911010903 67
    0xc079002c501e000f1050700d018101c01c4005042030491a41d42e01e42d460070100c0c028040729003008260400300802d4041f40c81c62803041c02d405480e4100260b00c44400c8001481c12408207203031804507800480e41009035411100014120b08401c00c4940356441d04840020742c00c403244c003030080d119045090740d801162600348200e00400080d858a44100102d03009500042d10400750000607a07070b1580d80000391026074602c3c20360045003229401d04260801340c2420020b4008049c5000729981c1d29040724550368a01795540c2500204604404054481c410050f10107020765041c00140103043c03041c000d1661203080078100919000101c07480d12001c40b422640b03070703034203034003540c5840100400c09030154000c020f0440c1941020b0b40c60080608800c0e103c00404007015643d03038094a003035105d01050403206110600421040c00c060100a40f90010b034001a0b000c9d00c070740b807000080c80d507802038000d1004c0c800c400918180380c18245040004135100c08450200640f241544084c80020710807016211310a813607 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 669209748 1250 669208498 669208523
    0xf04080307090317130b040f152102071e02210f012f07051c0e100e0102151003030c051e0705280612061802070614010303050405090a0f0207 62
    0x410005c0403c15004103100741d40c2032200b04818440b040b1410305440321a07468801080e240f860856490100e1400c14024007002500700c40300440d00c1c0d00520009000d0b0b4641d034031120800b10700e00c99480c0700110094108040441c8003040c0c260b0049413503114030135002600c42d03030480000c50300d003500c0704180154815081000c10001101e01e00e09042c40003080465841d007400000d0710b600343c580415203040c3c140320300840200789115204e161541c0c242c10300201403051180544c030000300901e50108660340544607030520012010760210160344102e00c0342c1440c600203400d41ea4210303480210020226131342d2184140d07841e06103960251055a81e0b44490003801e0442c42e005c2044480103194007241110f11a16070801d980802c021014810795615083c510782c0425441c101380010308440c0d00146001243c120190111100e5400400150f0f008603010b01002c4034540e10805002002e11005001c030307004100810039814800e02140d80071181c0440020701480c8120310303600b6a40210f8081714203240c04034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 669210998 1250 669209748 669209767
    0x9040534031d011407080103051002030c040503010c03050a0c0c020618120601061e031a09040c05040f1a040b1c0201091508070908010203100b0d0b04110d0605090f04080307090317 79
    0x90515031001c111b24012146500d940c42d0701d0344411002441c02240c5400000003a4092205000c80b80148406402000908402c4e00000c004240980e1600040c600b0450880802071048401584060300207003514540b004008084a50381c45d50780e429a04100c045104c402e5208050020034000c0146485034141500c002560000c01082d61450a0505113071111a642000d602c40000700c551100780e07164501a29a070400145041044c2c1c420340e803017400e11500c8104019140c1103203e190041e0310303980c6400f041c802c2c100402c1e6402c0103081e54000b402c90200c00c030402d4418600b10380d41c60040c105401460b1b00c5258405961f03003001c0d000c2e03001c591a5414054010ba0008001005048030b400850840c01c1542c0d024641c0382c994840e00a1800740451141e5040b201c6070320074844400c00401c01c00000e82d035003480521030b40000031a00d02c2d45142ca42c0000e007908110626900c6007510016007c105e076910b9580038403d41016214a04010100364003200141c1c503034040381c200c641c04642c0e4585030742c0e0340c1c0c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 669212248 1250 669210998 669211031
    0xf170105070201020f0d090516060207061407020306060d030c050601030b0f0a0b09070c0203100f152414070f0b0a0c03090c0b1c06090209040534031d01 67
    0x14001c0800c5a104020750114000c5250a5480341c0c440700e40041142e079a181011840c001d45d15401d41c4208031145800507001e9000a0341c94110b4410b911043d12125040302c144070f0900598101a4042c0c00000c0010214640413100050301442402d20103c91200c2e52181490b11000340c01c00c031040c120410511906141c00c00c03080c1c0e8400e4080000713102440f210404600b5822018003040280041303690b0320300455030107001c60b501c07120004404109501ca420b0410010f0005601e54200001c242e420102d608030710312241c5002e00740741e06007480101c041400100e0b840c0320321a0313000c1e101e40c4084c4100b0001462a41d074200b82d007400303540d8520050030a00380d910220380005003004d05162a20544500003000080340b03500312004a040c007600c9030100000c0c43c584e070000f514045a40707440c1410100c0c4c0000f041c0e014000155094a042020340d481342808000c061120b00b0038001110311815210480350240007560620380300d0325010449003505440c02c4007010700310030140700c80c1e5111402004004210b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 669213498 1250 669212248 669212251
    0x12030e041e0b0102150f040b010605030903030606090a08030c0105041b030f062304050f0d030218120102160f1103010b100309050a020d030320030603150a060f170105 73
    0x4603020000100084000c400010129480820003a100c000e00491680244068682e8055181e41c0341850700d0005680300e80c0e10b1003100d0449400260800100b1007910880549201d8903860700158a162200750800c2100e800980700c5e1640141a6040810440c0b401c1c0090a12480414004682410140350501001240075446494842c40a0f82000420916100820301030340000c40010a50300300340c500e900c0d2841c4e00c052520300304043d809100800c040062191603128064042d10f000e9103c61000710140e02c00d1410102102091604a41c3c50389001e0300200f882c1000c0900040c9044c03082030025000000d400b00540b2103410740704142c000d004190803102555003007140200482c8004000081c0d01c0f001c00c0c0102c0003003503a180a02000c0007810032004154a4000b041d4040c140c8082c0340c000c0107820b986182c0c0604601c0041e401900c109848280c9006210040103420301e940187d82d1a401c0c1070b0001c00071556603031142ca0024000e121a040d000c05425241518030046516080c41400c0d07440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 669214748 1250 669213498 669213527
    0x303161a0108030a0909050a0f02030103030c200a030206030709090e0a0213090305120a140411040c020705010e0d1104111306050a0c1502121008010c05030613020c0a06061203 77
    0xf04100c80400c107075105901034141c4401da0800602c3d03807100c01c801c40c0140007542d00120447c0c0700000200500d90440c0c1c41840c050301c5441403e08044200d030700003201000c501d40f010f8001000c0401130005181c01c402640c1c1c41140d62400000003030f62440300109403603408800251070f0304400c04034402c1d401c041d40c500f080c0e4075040344140000c10456070014128820f102d03006a00087c0d070004922001d00d19004001544040c1c21a0545828942888203000f405210751a102d0f0b4070300352182c0b10300750010070a5001c89038141c41d5030b8840c000610a010151003a40b01c04c80f00042e14404860b01a0740f03e2150b00c441c503950000058039060345c40f900e042c4541782500100144001440500d5084d40d2041c241040250b010088002d10503a40116201038010002603991502810307082208101c0c4024001d81140da500000f40003080380340d841901c251105942d1190403c012500d0440d01a82d160024159182440212503e0180706e0301c945048031001d4200b0100104030050600034560700200c0c0b0312200710b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 669215998 1250 669214748 669214753
    0x601440a11010f05072d08030f37020a03060e0115171501031a0603040b09063d030c08060f0a0c020a1106040f0305070e15090a0b0303161a0108 63
    0x74651307254065404804d1340200300000c0001b08141c1041e58041c2040c4d00c2a40c41070a403901d03402c2c0701c0010000390100301c6003821030200ca2100102201101c246414210401e1034900c01265104010070020f94080e000c90401d154a501c00001c120f1035208100d80200105143c02c000620744400040c06101c2403942d401d01c3d819400103001708850b4070107051089100074200021004201c030a500c0a188007c3c01e081d41c443d1003c030400060001400410344030f800980c0c240c5070140c1d01d000c00f07e2018803802c201c1a800c040c00f00c00d41d07500131020300050064030040c0e4a04641d60360380caa41c1c0c50780540c1b41b0740004d0000d81001d01802001000c2600701c54020921540a01403100e207400020741d1400401c00180c10102540000c40c0c954a4110440b00500100d01d90010480c0d01c0342040399680751070344640c01c0c0c130404030000211a20052100290403a00c020300c030854a4807015410406410352280c4182d050000b000030103541c50090803548071051140d0381c0a140e469401078903d8980313805034410103032034 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 669217248 1250 669215998 669216007
    0x1c02120a060e0d050910180e15041d030a0302030c0c03032401090302090a09060e0d03230609040209090c030d110f1f110403060207030509030601440a11010f05 70
    0x9541d18400342100d400c542c47c0580c5e501c40540c1b04c02d800004039038869612402c030f0380140600d418100324600c400540964003800101c1c0e00030040d00c0050100c010068240d0418451840024031a0b00156003201c810801e6500f01700030031829600f15441600c0c0d00c0d0404000030b041000207401d281540030300c0070302400d007042d41925540224444000c010700d4110466a11580c05040180c0c0360712034060060400d0880b00480040f01c800f40040c40f00701c001c501c00e80314401078100f079010300d015824803c100c0179040904948580e07080c0700d820350025051841c00c2c01000f60400c030944041041c181c5201e200e60b90086440d07602c0e4a028109410300b07074092441c0e040b1004000301164961010041c1842c82040020203001c0503a10f0380c0307030b400381c2e4000400c424000500582032581c030002a10340790030304606a404d1640e8400c80e281240f101c4e48044a041c040310409d038186404c4a40310019008801c90100490b080d01a5005060001c428030403a0060080480583c007541d100c591410301100904006140 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 669218498 1250 669217248 669217267
    0x8091f120b0a0b07020310111c0b0a0501051c1103150d0b040803060102071205061609060f051309050a0e0708010b010206220c180b0402091c02120a060e0d05 69
    0x342e06801021200c2400042e0002103403004c00c41c8494031006204204000d0194401d2078205600407041036002e040c4401e6000c0d15a1440d100d0a580a4001031120f00200d00d01001960303031f900a00d4000c580086500101181d00e01c80e4060026034a0440291a0780e9260644103e1000d03007a812025001f070400114000c000b40100602c1604903400c10701c99a20f990752040100e2134244280c00003170800c3d0300401240f081010000314103019601ca202400c0582c2d01c85881143c0402c070610a500000d05c0c0100100b180da07009030000c00d081c1d424601111140d40d204c07802c080031b58509a600b8003c06646411001c8048001d00802003e00b00020086c07007942841030000b5036614001d441c18201c444580008842070620140e2440d42c0c07507000c14200701441c1d40b0f040c03080142d024440d11400d414140749542069140500c00c581004030000c1101d501135200795480c40740c910540354120b03000300b1039031128804110100004411148100d81c04942d05480650700c0e4103168000720b42c8803d004040c89655003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 669219748 1250 669218498 669218509
    0x30e03030a05060f03030d0b1201090209130602040504050403050c01060602030315060d061a030916180e0c0a08010c2a02010f210608190b1308091f120b 67
    0x40142901d01c02080907150980010f603100c400c4071415a040c8800500902040700c00c1d0481c1c41c05102c03c9030040b03048151241540d0903145070340c0b0001d500038107441c005030303a200a03600d4460b046c0703020f00c2005040ae0340300e1010400f16401030700e068020841c045004030070018240140c2e0701401035440a5411414000d0000304100c030168109071080c0b0010034800c041c0c1259902030380090410b00790016414081c1c03a0b0b00b8001c0e90040e035502c1d0280c010314080c044c480d00071002110486080510042440c14041703000c0d0000e080b0f041d090035070750142c129070103091b95070300328214080c3c21f210000281e00e03140010081d00428609003070440c0300c0302d00c2c1c82000134208100b20080c81c40340c080c08c00d0326a6142d130303c00480e002d810f4031002901c0545200c102031144280740e070003401640d1180085a0000d070303021500e00c01c402c0001d4001800340403d41d001a0614104031800c200742407050300e103141448454000a1454018a856070041c0c10400302242085a40081080d404600e414000c00009509401141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 669220998 1250 669219748 669219751
    0xb191103040b1f27022206030204240e0a030b10080118021c0f0c0608010605030405060106260c0a080c0c100902060903010f09060b01092d030c060c02040c030e0303 72
    0x5000520500c0204c01c03070361089400c83c41030007401011552071182250880440002034410f03015800011070100300d035030192088405a881a41541480700e01060000d04000b4018009004011300000c90070070700e0f210746001d94061445004445024549940b0711900104164000c060300e030b0409404681c0c00320ba45045803102138050b41d80b07a0081a00c443c80d0500c048036480000d08070542c1046001c10704c05c3d076210040641d5002d80d2003d600d40da036400c00b1030b0301e800203507006002504100b004102c05d5000e110400700107950f076000c04801d50340e155141d0002c150212004820481b0000d039200c0020380c007200b0558090f101310211420900d607124880e5a45291641a0b056070ba0f85405082c1955241d50660f50b501c4030080003400410b8410070100c0203400c11001c1150554242014420340e58000d506400c10394418071008400c2d0342d50131151300400348864103c6440895021400b0010802400041d0041c100a0b21501c040c0c180138070600040b1a0040c98000130186425428122040044120bd = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 669222248 1250 669220998 669221009
    0x6020d09030e1e15120702030a141c091509150b01050a0c1e0c060f02070509060310051e1008070b03040809010e0102010b0402042709020604030b191103040b1f 70
    0x211130400340d00c00856411301c181c059200f000f80703480041081c0c50b917000005048990140c0e480b4605920800e01b00043c034020440c0b03410304255404040300540a003913001300e120780d001b155855074507003000c0541c0c0d0403101200703800e94906420100c81d0201d1041380c00307410350b010700a2070300c9480c010301e0280040844020800c02804420400d2240f6a250440718500e00f0b100e0b00310702a0014182da8050150200b1050300b55107025004880c8001181e141c503080e801c1c85000090040c041291242c01300800501000746040184002110342d085002a9080d00030300c01d40506200c003281da8140550545802846e07440a5021201002000009175070301041d5019841e0a082c401d00309002000140e0141c003000c010305c0d4019101007400180950030b603514400700e465650300345a041151940040c19500080000381d084201040b040001a180c15281c91340500c010780361040e41803c042426080c0c8102c90b102e50460303103010042c0424000c981c50600c1e00a0b14220801d161ba60500340030409995252054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 669223498 1250 669222248 669222259
    0xf05030a021002010932121603090b030a050f160e090c071a060f0d21090f081b0603040f0321140711031e090d06020d09030e1e 56
    0xb842c01c1da000350050701c1d07000da0000c0c5040704509204c581d075001c0c400038480f071048150303d035400b0810500086014100c0c0d0035104074031031034914180d85209000305415403c0f0b080241c0f01c0400213656503c0b201840c0200301d070700008101820300b1050392500c005c014000c68041c03102c01c0170390207440d900302c4c1e003420380d0b18005e0f60104140c3d82c40040d903c4c214040d012000d000d9042c080c58505080220314159841604125684c04180c40c00d0010300034642c02101c801812514010306901505413400c05c1c215408001d442d140341c5841e243e0f0b10380d0340c8820080c0d122030919031210581d040f44a007541d40303015001e001a05c0d400d003545410380303c10940c14030717a43e009420b12010030803081d984401080c0c000707800391440c0000e05c401352408401c00807540040300e001d000a0302c12a22450440303c00301c200c41d03550f1001c21600c4038940d5201007008142c1d2101e01a20b81c8804415840000945140003a0500c059140f1001881c000c0905015000b070000c1102203216180c006014403141910700000b19045009540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 669224748 1250 669223498 669223519
    0x3040b1207030b04050f1006020a0308011404200309120306031e01020f18090a09080d39030b030c062505070b03040606060306050d140703080a11070f05030a02 70
    0x142c005000e05a0742035001400c0408003c8000c0100d070003207014101102d80000c2403a42c4800490700d980000100070001040580104101102c40380c0c1081101c0c0700900c00180b28408080510307007001c8040390b03403602982c040300700b02c6450300500003030038440200ca00103031035423526400194032480d51a418020206030003d420700f000c4002d505543c0b562450000007607131841c0a1360080001c004d05501c131803046d860031000980c1c0c41014001c62018035800110302c1e0401c4d680d04603c00140814803c0000a001031401c074242c0a211210b45112902007040b07080400c3c2841c0c1c900505941d00015000d02950280d800c0704095141e0904030b801e080502650741285842004a00e4010440b0340000349c40d074803c0c004003141c0420750100544c00355100720380030003181e9520780050701942d4052045075403186510041c080410140c05228a65180c0e00b42514146507c9682d250388a80140d00c3c0c20000071501070f04111003c80070001680640914100c2c45942e43c03804000954801140d0002405880c42d0070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 669225998 1250 669224748 669224761
    0x103080f07030c0606080f10020a02070e04030e0d0c05040f090803070507020a030c0306020901120b0a0b09040e010c0f09210611040902030106030b091f0504051008100e0f03040b12 79
    0x44070f106501c0715040c441203559032001030f99950700c14070601640c01010110445103290f842101c0a46039a42c02901041d85001c580411100004105905029044549004560302c03110360a038040e1192a8821040d4200700a01040307400b803207058010945440d180c0c00104840c9800c0e664404a24030b01541d4414641c03012a0383d902272540b004001c007861200c044100429a009440104400c4e03980b0950382c044603282d41c058070781d0003403000c0c1c00c200010014040d0322a00303030003400c00c00c0b40500b011654041d124881400c568540e80b6150004103542807e001c07150340640080010080c4c1d80604818151a800040c070020300c000000703010995880fa0f402c84408408140c0c0d00078442481c0454580d80d550790090302414036054940d111380c2c0194001207078811040c040c1c108250f9010740281c4603e0409081c880101400342220846c1c1568810005a014003004020f2a16004500118444060010b02880c0c101c85488590082e0014001840861140c409031a10030402c103014010689401c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 669227248 1250 669225998 669226007
    0x40b01032d050102090f1509010e1206040606081e100506040605130f1409060a0b0102010b0a060c02040e0d0f052b09110603090c010c1b2c0103080f0703 67
    0x1007080c0050350403801401c1c0180302040d8042d0515000c261110360245c4480000c100c501c00c0c82103a40002204240159000c0307507c581e40700459810058100d907007203103109800504d8203500b164111070458507442c050040d010184070000f105030005e502044d010400002c2c2685501c16102c2c40c0040655540c0020f840c0d650b190004802400c0281c8920051038504c40101c0213004201c0d0000c0301c56003080c241c4943c064035484800d2207040460007810860301e4941d4801c02030b05a225145046640b18940000e5503a40d4903c040002d102c643c6076103000060b90710500065851803d120031303507500030701120318809400c0f502c0e00100d01201d1a28954079200382d0180070740541204007804200c04102c1c1d8a40724641c0f03990015081034002c0095880f01d6950804100b0640f00c100c41404554000b84e04c00c4001d54024000c00005910400e60943c0c3c4802c01403800c9061002648801c510b00e0321801d40300d03080d00c040c2c1407882d4000300a90707a0079070300e40c10342d01d402d80316109590b03500d4401040059800c040c140305 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 669228498 1250 669227248 669227303
    0x12d05091207030f0f14040b13030c090207050f0c01020a120507051605130c050a0c06021b0a030f0e180c0c0115090b0102060112020d0c03080c160e040b0103 69
    0x20709100d50700c2d4040d60400400d0340450010900215844600d0140141e0003629580048048041d801c0d24041c01c0490102c120303081414000002120b8080100c00945028001c40180c84034900040e100d61507810020f26244006400c0d00450f000004a2a0240da000c1020704409401240c1400610800d120841e107a218009001d0174a001e005500003100e0071b01c00f144e10446004490140742c12803842511000c030f4105041d031b540425070810000115a02481c105040140070b400e0050601c200c4e110703074400c01c9620305800980d942242c1600d90405400242201250850f85400e40c00c559284001c01c0d400ca03020020300d061020504001941503540c0011119201c901400034800b03140c910080e00c007140d030540956010301d400c0024590b4103510018601d812600a03d00d00c0c000d4400c15003d0114800d1800c81c2502e07107504030708000c0085105e400c010b100c2c0490b003c005000460104c1800071400080350441000c07001c1c0c0350706203c0400c00340b0701541d042d0383d040203900310700070381014446000800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 669229748 1250 669228498 669228523
    0xc09060102160f030c05040525020a0c12020a0806010803040302042a090312030c090b09040b1504080d171602011808040f090c051b160305030309012d0509 68
    0x11000b03404a0b0078064943c812041300d00c170b98101d0000d0f07919141000169241140c103060031002407032036504500c10112802c0d0b40000d06005461212105840c0c0e21f040c0c155541118010700e031025140001c509042130300200501c0c04102a20307055040c44041501c9100b0b611000e07102e40d8880e00c505003030b00c041e036441c02804502e10050007115000f140c0d003d050701d0792030b10003581c8000c0980c540c03a503001d000f4003401320340441a80c0c4a10b80c007824414180e40700c0c1c000030207a42e001681c451031340d070302500c40c0380d00075000300004c01d0b000391181d242405a03490b12056030361410401001c000c0c0c9801401d41179034820381100d404425a14903d01200040b4010140b200f0000c079540002e41c131140c140702c0c3c6900108241c1e000c0d10484041e0a85400022040d1014132481c8000903408101010314102c4d0310b400f003410340c5a080180c641c25503000d0001c001207001c582050b94542c00010501031101000d100e4407441c0c2001108254030390141101d44440e20b000c50107641c1903103859900041c1407031401d0000300070110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 669230998 1250 669229748 669229783
    0x7060c051209010504150221250c11010509060a051c0f0f0e01180308041707060c0e01030b010e0d05030c01140402100e03030d02090103020d0c020d140403050c09060102 74
    0xd4441851030207000241c4060b14044400302e01101030719041e00850399502115074403480c0d200d20747c3c1d11006a880c8001c00c003100e002c02082705801032040001007514024141e589000d8451410304056002000180005052010401280302039840d1103007a2240300d10141846902d5125200f108032041e5084212105491300e007580c1c40402802940c04040030304a00002044a030310011150f40c201d9a00c0141002e13550304084001c40040d00c00c0703200c554441d10540354841c040340840007c1460782c1160300221291500c4440102040351710100380c0149400900c0c05102c071074045030000e400030a40d00703002e60160011081c20300600a0030012202f0f500c3c10803008000102008014001102094030206d00c02c501514100c008184110481c8441031070040c05540342a0030702084800075480012070a0500d40c00340f000088001091042505200382500a410034040d050300043c02c91151803905001034030140001e1000c0303440094064582c0800780c40d42c7e040c0340c8409005030301c0d001120942c01c9082c0b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 669232248 1250 669230998 669231001
    0xe01050a06140a030b0109052a03061002030a08070f0c02150702040518030d0c0c1401090c12110411090a120b0606160b040c0f090203180d0507060c0512 67
    0x4403561259003220000d800e040081c00e20001040741c200014440640b1182c0c05100500500c4003c5c0c2c003294110207103d06114021010b40c0a40d101c48660208000c0420300110410902d400c000542c448002e010b0f00c00f4519000c030015011b00041d00241041080280f81e0161020a44c0039203c0000e001d90010070400b680c0b0340e803c0f001c040320351003c04101d006500300000300d100f4414407040103410003c0180554100040c02c516a4011302c4580b280a0421245250150101c0c04103001c20740d08507200e0001046514050405d15030a516551000b0349969146001c8004940c41d09a0000c400f0021a004604038485500d01d0b02e26004140d001580f250f6641c10015010001e0340150780071078824403140110b90359520030411140151480807e0031244511464002120003484541c0507114240c54034055480c0d404442010485030400405241d0010500c00c2c58030440920615241616005103090102248010420b00070381780c001340b00b42d4070364203c01c038094041d5040d01d11001c0e182d4100c0456 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 669233498 1250 669232248 669232261
    0x51e19020f0903010e03191110020711032104030b0c0408030c0a0b0109050106081302031f0e0c0f01050f0f0702100806010e1e0f03010f0f050f10030b0705030a0e0105 73
    0x96034000d820542c032070b40c64403105d40458040070040ea407510414650384455014403250030344480685d24140f4035607000d0003401007175a04003807001c0e00322503000d501d145620481b60010f062030040c1c081d2820b07050580171051030085c0400d100c1103800b500d510001243c02c039100c0c103d05507114016500441094040884c0180307202500041d0b850025000b001d1107203141c1d23a1841400c048a00178050b000004103003900213800c80a044140c04030051000d021145140d9500c0e40b11922005a5659144440d48440c0844151802042903003182d81c0100c03103050010300d1040020b0310341d110f4090344001c40c2c1004943e45014449100590342d030550081c00203803090290304002020044101d030362502003100c50702d0107211401c0c80c14140c5402450b0032014103407640c02a04018101c010541025030564881113003000110f014001c81105a203018001300d458140310751030105000c0c0051042c04074508007a4200049080816569005005428400c2d5252504941c0700090901d0241c007044543c20041807101 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 669234748 1250 669233498 669233527
    0x90105030606120a0c0e1e06030d0c050a052506030515011112030712060b130e060604030c0f09060509070c20030a150501140306010e060a0f091a0103051e1902 70
    0x100b13260031440b2101e02c0036004240410000c5c1072303404a815034841300713030b01001d18062100a042a4041c80403600c0c802540d80d40c640c0b509030210100c0d000c60001000e00b110031120709031b078007018101f00e040c10f205c1807800100541840320384241c0310303042000300c410080c00807109000c2c241187c85500e49041e500d203003071b0402902d02d485440c44c1d47c01e840d1074408000354071008102070702c0e00c08140f20808003420380381048514441e40c001d094070f41d201004200010000ea118032281d0000e1140b42004040c8500d44403003817040352015030165020b13883c01000c010070396900c02c072800420780c2d0000d401c610385c82110354250b40c3c21030400407442d018030880303600b0000e2081145d04040c4041203414140503030303030700c4560300c1d040311103038a203c0e581540c000c00061140700ca000203078692080014005024480d92240940207160071940040c0707074107a4480106200041c0760403c82449103080c241448a400d02c5140840320f002820340010035840c03001e0219070081900f4140d01c8005030082d0080d522400e90b60142c45 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 669235998 1250 669234748 669234751
    0xa02030d0f1d01090b060907270f121b24090e0f1f081f0b060f0a020c0114070b0612072705091203220c03060b090105030606120a0c0e 59
    0x180c0041700369001030120300c0c0c01c2c400b8034810082ca545040310002c0d0b0404a119201c9484641c4d240c1100110f000305214642c0150600100301006480a41410b00d0610085800c1300ca250006189135264041c0520340c502078286070310b50040e8003448216800d481c0c003220308000d56007011855201c2c0740c0602001c0c04480070103a004904040c0340381d009074580c849050118042d4424264250004481c1c0b80c0c211081c1c0d1141c0c1003d56560340d000c100d4030510780001d011395012614694034504007203048410554100841075008200b03080003052801d1408050b0054020340000a003c0c51400c40010a40e88440c203511018030004400c507140c40c0d4071003c2c00c44212038504454009400384403009250300b40c0500801c0d008a0100000c0c120700c80001c40c10700c001d940018100200c01c0c0d030148201016040421003418200d004105421a16080d0300d400e1090303585a20810384248030740001800382d990046884d03908000c0848600d040e030460f007000f444c208500c5c071801400c3d040000100080c48a205505207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 669237248 1250 669235998 669236003
    0xc030b030c01030c210e060702030304170a140c0a020a03050607271523030709050102162601091217040b07080415020307030b0a0801020a02030d0f1d0109 68
    0x8640c0d01e2901c4004400704c031a032969440000711802c42e04403883c3d0184a076200145115400072651880d004034041c641a0156241001a4000010402406290101c1e11101c03410000b4243c54803100210091030b04400c084030b100782490014000d101d6910412015600c2940603000010041e036034185540c80704811105500450781101a100011071801d510281c0440140c0100c031080c0e003041c1c03240310386065500c0114280040100d00b00d10005031241818580c1c0340c4ac0c2d405a0f61b80c40c109030020142c80190340b000d41558007400c117a076001c51119072034405560307150b004101101010301c1c000107074880b07201c1030718401e511304640c000c00e011542e041d08640b4266030b10381080b10b407105a02c0942c1494111400b80064900001245841c0c6c4107041c42c035007042c0944c40340941d8405040300c40049a20a07943d9001090b134484007440a800c01d40c03011030040c80d414000f1030800380380d0040030b900d80c440c01d0024030b4801d641d11a1000c0306001540026402504c003109035202e11403804040c0e00900d41400103 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 669238498 1250 669237248 669237253
    0x31d0d030b0109060804120c0f0602030a06050d03050711011e090311010809060f04300f03021c020c150c04030614130602031e090c0111010c05030c0d0f0c030b03 71
    0x11903401d54000da851408840c80365031568507680e10383c1c6511160404042c50781081000000b40d10740420010401d194519018000059982c1481c2c184403003111140e61115000d9584120a0000b081e008400e840440780c0051f01d80c80c4032808640102d45031002a11070800d2480121100817203e54404130a105480c40303200b0700a5001001001034400140c200e03000041070b849440016078a541d0303040015005072082e5a5217061106401d1420703100300cad40d800581104080d904011030f0055201e5424860385c4002d0804501d020403d080070360145070b0221044074030070b40024402000704002c10241c800110448451809410110304d05c02255005100550341181800b00000c007a82d220b207003071405040c12440c00640302e1000e640340f202a400c02082943e18a4055001c20706004121002c240f103032580c90023500001c0b054100142040260001c40c80e4140c1c9060400300c5e00a421034101d03134024150018841d00c030180c070040000030b40769400549140d68100221420701d5070701134025110a110490a = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 669239748 1250 669238498 669238511
    0x702100609020414060f0d050a230906070c0c0306090b1b04061b03050c12041511070519150e01030c081302090a02090a03050d0e0102060408040e07031d0d03 69
    0x4164180e0059000e030811000850480444c41e241c001c000344a00b2004940303090400c0b100c5140380c5e003200d000b01c808001c141d4643e1441030b200700e03c0c040080e18103807503076010f0728803400c210041036a00c480c010700010031302019005820038048084950f000540d4082e40502c01c0241a2401030004d82c806d85a410184164000c410400401d820940b0295601c5940c0e10b03205074015080c000200743c91036019428801d00b00f1800484240901005c3c2c85a40312591141d030300c62030b220003402c4140c0c41001101c1040504070090000120104c1d000c02200c9049030240c0d039070055118607070703424140c541c450340c203022100603d050029000078040d650800309880422250700d20400c2038403200811241e02500003407868200300140340c0320001d0794125881c84001030600c01c0c07400c00b10300c688155400c140c03640c0d07001800c1b2028050b802815180c0098081c07001d03111500f060740e9080d8250185005440b4001c03032100009044610a50040f0384008140c0144650040d110300031170f0311150040c09c03a00c0000e04041 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 669240998 1250 669239748 669239759
    0x16080d090c0812030f06060d0213050907031a090604021c090b1303210e030a05040f0815010603050903191106100612110c01050415140f0c13050907021006 68
    0x5000f50442400115031481d5541d82003011a40c904010800e681c8000103100d110401d4003948051701d103911506040355861800c140411815040050506c000c050406a0100c0282c10840400321069015611159a0f40755500010042d02a000000070304844003070445001d02816008114501d004010481d415140c10380c41e80a465420400500401e1410040c02500300c403495207503042003502c0ea0002515008082103505541c000704442c2e00051001c6014001031608143c41402403103c000200340c803071448081c0c000346800500c501410306036107200040c030000c024401c0f5000071200d0401107503000842c12010b0712480f601189048188140c0b40003400901d04a10711000b41c07603182d15404101640c0340b40c6400545080344140d0b0b15114180214000c50600340200e0f4000c0d44244104100c400a01407580d048444c040300d2894851900ca082c08000e400c03903c140340e041011001d100307684a001c81034005042c2c0b4142e00c2a40c01901560403ca800f5074041101802410000e4080c0185075884 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 669242248 1250 669240998 669241003
    0x213050903181905010f17010803040519030b06060f0c0a060f05070c0512070507090f06031b0e1518070305071701081c0215010b0702040b01170c16080d090c08 70
    0x4041103c0c95550100061245600512040e00b007040a46440c4108048035840d2604402c8203074025801d643c8041070a00c4a850714184401100e02c0f240e0003107006600c1c50b05c078545020400b03080d0b0760185a001903882004c1441104a80b040301b10345c0110341000c503442c98604018103c02030042050703440d20000c81c080030700c54000b000c1c81c80e80020080202101344070480c42254440b0108440e02c1c4107481001901c14694007031700300021541240003806071b146082c80c0703100c1104200c400c21425505a800e018030320103000b5480e0407004003105c403184001c2d6000403c0c201245078054101d00e40d211020001081d034160029482842160f80d05012100f2440760140032400a00038a40d20740c00400006050a200200c4078020075018411188095140b84003c0d6004c036082e00f002000020005140301542490300405810714001c0c60194941c0c650200312807a415405840041696000138002241040d104408204590811074240d51922070740c001c10010f0031f0128048070340124010f00044c000201 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 669243498 1250 669242248 669242269
    0x141e0316060527061e16030e0c13050912040b0a050a090306090c210206041e0e0411030d08012108040b1c0e03191b080304030203070c141c021305090318 67
    0x448040c80340c91b001c02c02070700071b40f20b00c11810750248140e14000607696981189500150500b080024607402c102d4a910305250724107070524180d030410042000100003072011208419100e141140c5c44000f00c12080303d40b02007681c400b40c42d02d410050181d050105619a081c02c0b1080c41d0341c0020f41c06095000e0300b00d4190030400180d40080180310402501c2154004c2c006000041c07075034031044680f25583c08001001c10b42d000e4981d940925800b903018281006800d141800b541018100d075131402c40301c602503441819641030711802d03401c0a4420010985c080e100680800c001940c0c07038013a8000b90034901c2e028040074414560910349814402000402180e4414800c0d17003154002c004854029240540c5d80c105c420000c40b5030300c0300b03800400c0c500c0c006580140d1099014540d56109404c001007010f002d0f800445280403e4494245240d079884c51044c0f52001d0342e824155035620320b0001907415840c105506000e14104403c002c801c0c000800140707044e1100382000e0320780036060000e02c004c0074003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 669244604 1106 669243498 669243511
    0x6050a061e020a0209011e1505070c0902130b18040f0c0806090708070f110a05012703050d18141e0316060527061e 51
    0x8000c003030700d141106203200a085540031900024444a4103100e00b0040044401c207961615805400c81001002c1400310030007031405850001d0026881100300f02c82c800b40040c4c0108800303c0c50b10035503924000c4800860703101030521604d14075650100a20310304d001820031982c10b10743d4450003425001d0034410707000f2514803044a400f800300d43d00a071241d07200f02c000b4810841c14a60022a450307109485240c081000b4240d010203542101002c01301c00400d001d60303c141000c0c4441500070010340340305c035a41200c0501030003900305d03940714083c0360040005200304003950022400760040f100e1440c41d18200054a112555611b42c908410452150304c0d40102135144000907042c2d10f0440b00c2c0c0524000b0790314104100611845011203114002e026036030351030101c0d03045860a03044102d1281484070f04052101402c903400d5541c03101b190030422110390b00000b285140000f0740303250b00484 = true := by decide +kernel

theorem cover : BRFrame.Cov 669064748 669244604 := by
  have h0 := BRFrame.cov_init 669064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 669064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 669064748 ≤ n) (h2 : n < 669244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
