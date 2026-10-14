-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2644
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:19:29.643904+00:00
-- url     : https://prove2.me/submissions/cdacdb64-b45e-4309-af77-8cc9393956e0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 475359712 ≤ n < 475539568 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 475360962 1250 475359712 475359737
    0x110909090d0c0210030b0301090c090f060b030a0203040f08070f030305070c23070f0e180607050a031a061801030c140f0d0207080c1f05010e0402090703021b03091305010303 76
    0x80025584c0302c030030528000ca103404c80140800e096407a903400443ea6515003d45c01c00100140c0e10880400c41c0c4101000e008180c07802203e4103560101400c1c103560280c6c000045010001d00703000342003950340e11200b041c0d1240102e04110286040c140b106401107410000050742c1540b003070714260241d66001c40c101440222181d0302a84850003050300208511892101003103484529650380000c0c00803c3c079200d1507203807145140303182807a41c1c500003801340c0c002c20078403035226004400c1e1403583c610b47c41d0014404120740055078103a00303036030b6406400c44030008090540760701c028121101c400c020780b414400590507100448001c0d0842c40110740d105e03000c2c085080810201360003082d108203843e10141c00d2410715128803805a0010b1a00b440a50100c0c154101456801c00145240000700e00100050761500d100700580308801403000b84284508c20001d20000c0c080d42c1618910b09103508158404100c5418080e5a94400c580030303889030b4503480c0000c100c03e0b424000c040c140c90349599541283c155 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 475362212 1250 475360962 475360969
    0x910030210031a030708010e010b03010204030201050304060b040f0905030a030c0203090a170f1c02060c091008042a17011a010c05100c03060306050a060f12030210110909090d0c02 79
    0x103e80a54032840303031012502056075804000b034178040d0900c0c5000141d0181c1c2e4030506400c44080c40e0f04680aa40180b00c03c002503070f0094181d03940550440e6000c1340c0e1010b80c2c3e00043c020404005030324003c81c17a01d4141c4060000000140000b006140c0302000700301200b40041c6c1c2d89005000b11103a10400605003404404d01c051050102c6003040d104032441010989a1075081241e000b404a504000410850014031760401c83c15030004011310089150611000c00301e0000c402031742ca0041809112800b080410505c185088000c6142d405c1000c8c50701400b00d40e44045140b00d100e441d1030000c041a501e00c0c0030714107120b048840c1d00f884000c01e0302d525100c401503409401a01094446010b50040c040d001c5809000b140070b0002c030341d980040d140d821460008126040580a03140c1586407020170b0041c010308650403010350700e0003120488084030034075040f0b19000c1e43c0380d4200c0d82203042600750147e081c3c040010380701040080399900c1d415603800896a5441c212a41e5600004196600e520050700307 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 475363462 1250 475362212 475362221
    0x30718091703071106010e04081602130608070f210b04020111010c05130602151b0903100f0c021621050607020607020c040908071e14010209091003021003 68
    0x10301c601d6818003200104010203840341c008490f0140440c400412248004a081c491a0301400318003e8040e0309040503100e9110600035a40304107141115103d1010641d610700202010800e8400c1082c060f40340ca441c3c0440d11035450344a5201400c440c40d00200c1d43d205140300b0000e000283c1040f20300340e0320341615404810040a0400c0e030602400c02c4441203422428051041e06c0c25040e2203480d503c586401014007080c60300e602030011034000e10611540072000d020020341041c4d030800ea0b28042a41100540d8144c4190901e00d541841040490214a00c40e504050b405030a07400c02005940c4100c8016601d8170100d82c045466a8640181446005600d4240885a03943d880301050340180d69940d5501d005010b8480f200542d100030108200c1c43d03810003183c0214003050390144102901c9030366400342030003010401004020000000c0c1a48152101c0c111840c541003540d981c584100302d02da1034000d50020039154051a100000641c5103070200f0102c20441e6800341c0020786044202c10100c0081 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 475364712 1250 475363462 475363481
    0x91305060609190e0609040b3c04050114060a12031b05010905100218041d01060b040e0a060b1813060b0a080a140105131803030218030718 61
    0xc02889402d51980311000c0190580e00055a091041410324000460b20000106494400c29604080100140c0c104401c560021003007419200c01480788107000307210031151099145445201c20754002c928090001d03c60080b80103038000c0201c3d01c030301fa05000c88003e080301c18581100d005c0c04c0410000c1598000d0010720b5000745098039840c00102c0a0f07802100e0284800c1e10710360344079041801417120074019050000c0c1c031090218a02008034454940100140c1c850301d205685e21520701c20181c0040b42801c1c0d66802039002007103010b0701c1724052002500303d405842002061880040e00b00c1086100b02c07029250800c5120781840103c15080c0000125100215006040307511254030094943c00303500701400702c000300d0540b140d0f500d00004142ca900185085d02003402c06090400c4910480134960640e41c083e10789080d104918202c180242c14041440001d612100b4486810316074140c0c054402400c000b40c000c0e00039104841055030ba02614050080c00001500030f070448a9007a42c85120704 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 475365962 1250 475364712 475364719
    0x50a0624030209060f0d0b0909100e0c090a0629030105040c0302210a0c020109021c0521070201091509060e180f04113102190f020f0309130506 63
    0x3e001444010407195009a40a42101c4002054064201040c0c2c021400681015190ba0742540303001c0350b01f55965400d015005100a80c0c41c3e1420a82c080e05100800c0e6040d00540401a01d0518142080c028002c0d449840e500424003801c064560f254144100f01c4642c0202100c0c1c10340c0d00f08010070000f0300e100302c481740505900b04001032104030181c0c1c62003040c3c64852849286850600c20b00c4e000e41c1c02c072483c401c2c11645868014030050307464054450a100c11205a280d07103103041d02e4014035242e18a00c00940310340c05d1002e05000100758234000d0a1542c400c2e69441162030762000300300c00c01102d403031340d0101040c0c8920081c04402e100b0741d26a150120000d090701c0c22613034890705900e072800c010f80d41c140500e6901c80400050101000c062100c0384404e40b0500000321203488a2144107500e20504100342e144100728074030310752690f010780765058a6424980341140298002031702c545000d0f1030600150041180002100c900402620003000c40039000030a42c1d008a02014001d00000381003d50 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 475367212 1250 475365962 475365967
    0x703110d0f0c09051c1115030906010f0603020a021902010909020f1b0d020303011203022404020415060c020d0804090c0c1a150103090609050f0304030303050a06240302 74
    0x810a000e01401e14840d400d581d000407400300389000200300c00442d42005005d4040806620341c2402260420100b698000140310700824200c0300050220030492845c4a0305903000c0305000c002d14002c60389034100c405030302404085956414041d0140d019120310000540c01c01681c407440c48080907440052031f0f00c149080d806032074031426900c0803a0002c424091162001080b1001d001700b50003085201500c2c008020418044400f000940c0ca1005010300c0700418080038049003010300800c40c4140c0f12440304410b601c2c292505165a800c558211016031207541840d0000035146004000c1000b5030700d039951219822204c82d000c1c031013054000c20040300c1d016801c1200064100441c800d8001102c0c02da62001c0500303603942000050a80c00064040e03c03182030b9024030120900b000c00c0380d03201138428240418a02090b040003001030003a01005400c5000e14262210548404001032069078800c0d00c0820098489600710001c4411501443c52904640b0400400c0c800030011284000c2009240262 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 475368462 1250 475367212 475367227
    0x3030b0a05090c0405010e12031c0608030304061a100807050c030d020c0604051204050901030f0204181202101401063207031214041403220303090f0608070311 70
    0x151981012210020210f41c003050511040d80c1c00402c80d0004102100c52001c12034114103010b03100e109622441001040c1d500403440101280d4002200a18141c01980d0f242e02d42400c041c00a40704804000503502c569200f0100c0328035052080c2c111381e100300d0343e441085540303040d015101c0c1c1c0c1c401c0250030179070300c0188180720f20400140000c00f541c142100c00780038207050074984a441c001c00304407200c149020500c8140290b8a5070b12603181125041001a68443c1c02400407500400386100282124a01034506401740500c1800c072012001842c1c0c204e8652110b24441d100480705488404c03101000d10500401a061142d91824941815130603a409003068550b139203000990918602c4500403000303e90002416001070f08400b20032880b40701030040d9008030481c0003110500502c02072803078400164810b020f5404009071941406030f0801c00c050000720546441c4101b117288000c80005183e0f01010030408181d501401c206c9030262103405003a02c51038800c0d0068140d0f550f29080c0d40006100b240c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 475369712 1250 475368462 475368469
    0xc180509090f07080705120f0606040c0e040f1401080d0c02040b04060f06080a11040605160501020d0c050c0c22020a0c0b0117060708010b0403080c1501180b030606090403030b0a05 79
    0x204000c4c00c1500042103500d1402040c405088401c070001e40080c2c204d4581207032028004a5450307481003046a0000d1030420316441581d01c0401000950340092400000da02e01c03078200c0e404550030f50340075480034040381e0380c4075082944d84842403071010004450707819000050031309411007000d050004001040f0103844650070b00443d00d0710f07405030000509010500032440214403641103c868041161858903081404c060f00034840d0581100000c01c2007a10b00040c04429810303902109181502030000e0b0401383d00090a40d0082c20711480344e1b000754242901e962a01d018016141380a80301ca00980409038401e0100070341080b01003200b88015080184001801024402d0180c046610820080980140c5403840e09800038501c009104001c4014001e10220f03006170340403623511544581ea2442d0b02880c1e00d007407210f6804400c100d958104000714005442916188425000c40c0080015441c640c040541da00015200b0582041e4902c0115000c00e100341c0085078204400b426902c515691900803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 475370962 1250 475369712 475369723
    0x203160807240e0a030c0b1b0415120614130e0d0507060c14090d050106080a030215090105070516020409050a15060807081005190207060f0c180509090f 67
    0x56075600c4003200300c0803050440c403c402d0950100b5000b088410342c295006420001811809040c00c0101d100040c0f0100c1046012046501803071031003038845a65138070880c1100000071a08001c40d007103680e1815803600e02e2103903404a0b401039100380b031b10a0410342402b510b09042040c405041d0b49400b02c0740d04200f0104802454524039560303559840300c0c1424203900b2903800900c404100507407101700d0301d8140b01d4041a030311041811903142078540201d01d07103603004040c1390384032041500071180f2100600d40c01080003030b200854902800380c1955008500740c201e64040b01c940000c90703c14802d40104585056142c95241c2c80034100240b008041c0d12014502202c1000c226004400d1001c246c0b007800ba2030007130000034200d6100a040403070510500940300c080301440140d50343e41c0c1e0700008000e00d0598090700c02441e6900c10131943c445040c00c01e007000e805c0d2580c028580ca42051040662288030ba1840c0000d84410421001450b05200c10808984c3c0c001c0c00c1509240f040c81e03850051064140107 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 475372212 1250 475370962 475370993
    0xf0a05060114090702070302100201020c06010f03120203040803181c110406050105092b081c1404030c11191d090114010311030304090509030c1c0203160807 69
    0xa00181d85800020751038404003031100c42c003600c200024007052a40000c0e02c481540c1c2d044402c00003000304400124024010401089010306c200400060046140300065058134055200ca41c44604450300c1607990f0b10491042403001c2d8010480340c03c240180e00a250365414005188407415083e4100c3c155004103044825169000d0002c54071565181c81c3c42900f0080c0b00c02c1c201a030409001b20002401102050300c280d04100300d03058407240e01c010142e030f0465aa9804000192038504010040080c6802e0103404010107103803501c2d04084821101c0d5140c49264550b440d41411304195032419809080c04103110b8200c81d4070400c0d40344104a1040890140c1844201d403400c06200c201400240f00c03014061402e9a45000d180c0d0192184100381c150541e600010300140e9035204802103860751186605c401c07402440c100c14040000c0020009040345001e0000316191700342c0000042040e0010700ca51040076034802c1017a05208600c3c10722134440140a50449070900c011070311000300352501c504 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 475373462 1250 475372212 475372223
    0x4060206060f0108010612020705101805071d0c07031709010209040506060301050a15140d06030b07090b04181b080915091b030118061e0e0706030209030f0a 69
    0x20070940e814188145507012001346052803565242883c0900444420901a540c81e900054944180042044009640d215a510030815071005200a41e807224290303004031018010113000042e0715041c141f182a40308030040036030006031281c11841c1c0f96640002400c03801c2c0030345034401001042c2000840c902c0b0b0103405001680e16a00c01042008440c002446103100710340500041c00b494503507a10490584128580d07140a440d01ca100c01e980d6258650040440140700080402c88200c8079009042140d20402041d1000c1c0c0b00e010381075406411a0145c0b28000b00c0a2004001046c10104440c42c0f038884101d001071035100c641e64068010f0b000200450200b10b001c000e01100000401c400120080c5580e0001a64103090540c26202d84072030500e41e281a0514a0424440e9000e42c0591071201d550202c103031292095180c4900a060204050b100e124080740c410761141e511801231070081d8410b08050030715941841801d80080d0031600486800d0720801080710381c00d900800c0008076850003007 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 475374712 1250 475373462 475373473
    0x201171006020115080304061b0c0617060414070810030510020a08061005040909060b1207032609040903140403050606091e060d060b0a03030302070b0705040503070e0714040602 78
    0x80000b03401d452080100310513458403031004202807800070040c3e0701a00d10a240007100864000502c0042c00141113001e0808140701d900015810780108030310041c5043e00c05030782502d84c2e54108002c2100c1c45481f0b900c112407241d100040c0c14078480d120b02079010300c0c03041510422179141d4a442e482c0100500f184801035500007400f40c401ca03006880c050b4400d07801c940352610407a8405000f410390059101e008c142c0c54864008008100e03141e0480303c507040002e814202d03000c000c0260651f580302c5d54031094074640d407554003421801d8001403035845c02502d52080300380b40c40c2c3c0c142c00340320081a100d1425030420a0401c05035000c0c0301c000380104015030007800107111600745003041100107030000e03001c0e851050b005500c02a120200b600345c0c0d5403040b811075203e8a04810350411202030320710082d0042e4454107400020040507056400381c24141d004002c00000340c1d9480c2400d0301c0d07a2040303019917a8594031054081104000c070460040c2e00c0405480c2003103640308015520f0f1a5030b0803a4100e540075030440b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 475375962 1250 475374712 475374719
    0x40212070b070620070611040b220503010b010c0b040606030206070309060207061e030506030c10110c1903120509040c08060f150d1a0d05010207021503150402030402011710 76
    0x281d009900803803842681109051303000d011001110700c0782d02801400c1d0b50301d580185042e0003410003580d00070b2541c041d146a440c1005000329540000c041c000190f41e41031524081200d007014841c0d44001001a10b460414191580300c0c0c940c800001402114403d031510004401612684068000301e4841c1d280c0304921420180081d080c60400d4020f04c08000351000030000018101c10815450040d13810b0004d40c03600c034000428149103d0070704950300604034030303035581c1d1140d80403000c08031100c5440c0a650b608a43c240070040740c403101140210000e101e1075820b001180030010b4550201625090041c64911584007050039608480205004902c0741e400304516800c0c1910360490801040396003403154040b030050f030310213401801640c0e40710320b690350b4100886210701f24508000400c01460801a0510751610b03d01079484072200302d0050b000c4803038824010403004d041c0c900031503520040d0b5600f80c941e10184802900000c10a034104440c0300794241c2209604035100340500071816108460905 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 475377212 1250 475375962 475375973
    0x60111010b0d110907030203041a040318180b0a0302030309010f05130e070e18072303010b03220b0103031d1f020f0309010c0b040201031d0a051501120b040212070b07 73
    0x2005c20040c14010010000000d4140e15401d21810780f40c0d404000d03917101e90500b01c0d0751596840c0c0002021300c07100d4002c0741e8150784441140f0400341a000134032541e028401070003040d483c5840025050360040c4103004456000301c1c0c0c3d2103402127681c0f8049040a004004203510080700c3d0f480407285168500520441d258807031840b80c1003000030768078080402d8440b462540e0181005128000300101410540e4a041110001030110513003050b18039140e50b103600410029500a949881d181506140c8042420703600004410480e50060315441c49680307584c038141d175a101e80f0340c10000e104840e02036210295a600c040c0180965174400f98910003e82014080d180c54030300c106400fa0b80e0300610a0010307030b030b91044040030810780c0056400c900351540e100603070190100e0b2041d03561000740c106402d80344100000c0c1c0c075541d06005404961000341c0000340700803c000280605031094200500c2d400210f9440d92000303401c20710142030b410b00704d0020901c2e5030401150f42c11244001c180011700106200 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 475378462 1250 475377212 475377229
    0x16060b04151d07050432010908031b0109150911010306080c0f0d0606450509070f0602010f0b15032404060e0603010f14060111010b0d11 60
    0x9100001ca0811414503201c0d0940c61041c60189042115080000d145584a88103841c002c001c1d6591100314aa00d60b148501d100c41e513030135002130b401c1c200403a078146584114011802c44460703801031440c00300344040c201c69403426070310038032070646d00d5a915000084100000c420f140c54142c0c0300264900c00340ca480c44406880d507a0700e0341094203080c0306020100010880d00f1502e481142d141d0b254803044408100081c4160f18054001458514001340c40a4003c0c070304c005110310643c010148042c5414088111003d01d13410740007601c503500d1400b410095035445142c001e03804004850342241d4409408031040290342003940142d445440001412186024004029104607040c203c103410011072403001d404000e007403080a48950408240030000c08414070441c1801030020300c0545c1d1601802d422422007521118040d40c600031401c0c0201d203003842403120420780f010b4401c1e4152140d600444a001403d4074031582035503070300022012a50b40050310351100b8070841440040c003240300100000f94 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 475379712 1250 475378462 475378481
    0x2121c050906060f120106050415080607020d0c1e0b04030e0a141005071403040e0114030109020d020906182e0305120d2304060b0307050f060f16060b04 67
    0x41c0d010000b4040144e0b1114081207400384c0c01d845403080d09a000708a54058000c56014035005450400d0400219101a10b04c40c15151702408a60705500d44450403a03032094240a400d00180c0d05928690000e03182c854100e1400340d040019250740318540e00c0f9003951080c00e440450220398003c20074841400d002e03003220000e007040f1403031740900208440843e4070035111003048020810002080070401031056141c0c03104100400880b511580ca900140d07135600401e000d05200d1020070502004945814040d0700400c4e07502620108148a00b42d0900c450407174081d0070a64441c10340e00c0800300001214030120311403840c402241c2040208200c8a02e40b1079600c451800c544c1100d80c1c8184041540042e56445111640d68000d41e1703942e91000c0d070300042c40c14a01000c00c012010800c4005901c81e0f2035054084ea0003440c081040c11a81c10030035581d00500c2c0724041d00705940c40114a45403415601070001d80c10000c0d1703198038206010004402c240c290320001c6408a81c1c0e61100c0d4200e051a20650070030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 475380962 1250 475379712 475379731
    0x204020d0e161422090c060804110f060910030b0d0b040c050d0c17010b0907050a1e140304140a2405100b0a0c0b07260402011e02121c05 60
    0x5064083c0081961000e01005801c91480c014000a03840d9400d41d101c40c0c580b0303400110800c56592500c40003011284103071010f03220301c0101e00102509242810360409178010044c031461070322112006000c1109100b56005090640d100c1c041c2e5025128403c0c1004e060780314500400d081e00c2d01d441e102d00604819040b039070040500f40c0b40c0d400060000c07810902504c502d039040c165a204079099031030140982501712504100c40c901400003054020001d00700d0311003651214103030050204243d40b0501c0031000c0729000255000004c41c2c40f6088500259041070003032409415845c8002501d80ca080d030204011581180c194050b6030744400750104181b841e868481050048c1d0404808200503603c81d8000c0c101c0700080000c0020f0103d0007229040c28560b800f007410803091502000240c0981141c0c81c4003091030041014003075000140800c03042c4620350507100d484014000245008080d008419002c0c00d5200c1e0000c1d0345002c4820034090801000d00340c001410b811400320000055500140c0805074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 475382212 1250 475380962 475380989
    0x1403040309060809070506040303120e010c090504091506060203071a01122901060e010e0303040503030706020306060408061f06020114040b0901060902030901060812071703040204020d0e16 83
    0x10341d0000e000741c210740382494001602c1c0c80f0421020304141003030340310b581d210341d00060000405070080703040c80d80c00800c0d900c00c00c2981e007100d650301d003a51004500c400c0014102d02043c045071910307520014081e030003221000c60794245400d4000880704103401050140c1d0021404030100300108500e1101c04075111580da116515180081d00c0345414610001c0a0500c0b407030b0300828036030031000800310100951140f0030895079601d4025149010100e170860014520f10720716003035401c0c0042101e04441d0044e004510302113494440e2802900b01a0005a00003403c01c000070740100108041401140d114a1180311080d6054900c0c030800c0455000700d080d6411300c6915003c0054030b8450700d50103a040030a5003800e65910f64803038010032094100019039071003c414401c541d1015800002601d0f240002c44030074407155040c026a41c02480320050094154042d407042c46142c80026540183c030141000d41450b80d590112000d032001e042c255809a27000700c15400c250401c0000710f1001300409040c0c0700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 475383462 1250 475382212 475382221
    0x60f09060f0617150d06090b0f010b120604021305270105120303150f030a030804050106140d0f0302032703070f06050d1d070312080108070f0e0613050a060302011403 73
    0x101c0f000c030003010150248183c110143c000d44410181c59035050f0701080c1046815120710f010420b208040c1d0342041d1030440b00e0000b00b2441c00c2001200c203821070400c4203821655800c0c0400c0040d40c0580d004100b90207e5000000e0644ca460106803483c802c80c100c04003804184008102e00540140c1c0041c0c400e0000c494910702d4141d001c4210ba400000c403000d00c5208107020004170710b07402c1c03c80307181c503400d40b10b504208002c4c035074800700032801288104001d1200c5542c58090840070620303d00140d91021441900000040c001c0c40030010891090064030f042240c2010a000b03e40f91f2986503148070a201000c040d004d00d820b200b450054424018180415424004005e01b6401986c44140c21180d407141f200074607030202010040c8242070802107424440d140c0c40d1000100c1c05480c004000b24034458000b180d60380c1e0105079031050b582240c25200019281004002800785c0140041e81c100d41c0e200d460350f4001005020f071510900c8a07610100c0c0706880d40c03000400503803020741c820000328824010302 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 475384712 1250 475383462 475383497
    0x8100c030b0907030c1806021005090303040203070e090703052a0405010e01120f02030a210807020d0302070816050304060f02060411090603030c100609050c0a0c0303020a03060f09060f06 82
    0x340c0044142c0350005481c2c1034005d0035a035038075008859811040c459600003038801c1d070004000422007400c2d40180102e4554003031055a1303010958000354140c00c04281444a040200c1d012544003404100b10b4084598075240e132810302c106070310342c0d010040902d03950554001d521180c00701c11410a03582001036615080442008500602440d9500c502e0b80c002a02030022454030314142580040588007840c00f80e140100726005541c10300b80e011801b42c40341e0385c0d882e40521401c9100362010307002b9018000c40c2480403002503111810448680406101c01c400100c3c001c141e40200b54440c1004640d5a828004041c0c400c005690301c0e20210341c0110300304400150350300c2444800d0801610f100302240c9a140c0020f00f14090100c40a074503106025007010044501c0d0414001c980c00500c0c100301c10303141e21034410541c0c4140c0305074101040414842e10000780c441c0d4002c2204810b0723440d000403003031349402084207003800c181c0c440010151507450038030480f94150003030001031099081c6554100740d002200d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 475385962 1250 475384712 475384729
    0x80109020a15021e01020f0d0504020406050604030804060c0618050601030203070b130504090503071a0604180302030a0804060b1203031006020106030c031101050708031e09010b0105040905061908100c030b 90
    0x403130f564040038074100814040c3c250142c449070180301404a4958038914640070003400b04a505910076824000c0015032420603000301c50985e80c0003a070b200e181906004003964066215081100c55941d1401071824034450100750250452003000039040c903515500405103041803a41004020450030002c1c0c44042c402028810300306d03030f81680e011803840708078140744e8194004d03400050078041941d00848910800c041c00b8a11403a8115010052003040300c2c00310382c2c000f00f0010f0080260744200302c18441c4500410320164002e109610119504480b80f0102c0c03400407144021708001d42c4040240891000c062b4425805841d4501c001c1002c5403031900c1d101d60100c06440080e2104a0181c41407940740d1040c030403100e815400440306540d0b814000b6510203008a045030720011840c00c00c0202d00b0414040c02004101d1505a403464101400e03d0b20000040002500c01c0b40e00689201ca40a44400b401035a07a00614107a0302a0080b1034801810200340c0d0001078803081018989902001e4940e1072005 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 475387212 1250 475385962 475385983
    0x2120f19020310020f1c020a05040905101809060f09120c060216080c010b10050f2a010c02060108060f01060809100f0b010215100902030916080109020a1502 69
    0x14021a058000b00382012040c40301c21054500008100c11890501030082600c0c01001c101200d941121040c03410890082d8648080040c504110400400702c0139000983c021101c482142320466880d407040c801c1c03442003510018010b440780408018054240714010700c00c0510703030b41030220140950fa41c3c0c290307440b24052501440130001d40d02061040603810b60b40d0307203450b0085100001c101c50414501d01e401040f0f1500d1150300b4a00c81008604206c1d580704c0101500e0f8842504100f1505411441908401e80210340c42c079a0024000c0405035901c405100c100f0104c0002600703000b4440c2c004d0500c041600b0440c11588060706000c00444000704050440cbc145203859100d03503d40c00541424041001040310a0f00d0800704a040252110351116100713520980071079814029065120080e51012510018469402102003200300210340085a210402d1030507a0928902807140d40c02c160a980c0085040b4ce56503034404c0c046040904000f4083c142c0c0c0401e585181400910082d51103803400c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 475388462 1250 475387212 475387243
    0xa0b0f0705030705160923010312020c0d060f060b0304030e0f0a0b0a020f0606030c0604090f060506271e010c08040b040303080f07110d0e0a09140402120f 68
    0x4803281480810300036628225442402d9034800c958011000240075928013031441c0aa01c1c1101e001407184040005000800025490035601d81ca1526420700e548800440c990543c044c865000300d0568440f14041c40da60b100d5500064540340c44850b2070112540d40d0400d0102e28404c20620004c03c0d000400c4540d4580300b140c8201400c80724802003290000302d075010703c0230200c01041c1c542038680c0109003003004000c6031044503c983e480340100350351103c0c0109170703942180e410403040c42002156003141d240d0341d440d0f09001c030700c896484001c11741c1ea9104c2c20a51038802010800b03102caa82c00c04202400550b001c40e00b04140003011144840840268803006040c0710b018450042005141010b81e03004080c1032000b00e440d15624240981280e4003122248442d8803c80c0004140d01d00450080843c0c1d00c4410060440245181d010b8501c036450800c05903121000f110002032044841c0500002d544281402c2c02d03860500d441801801e10194040e01c54607085480c0d402003603400060500110705404 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 475389712 1250 475388462 475388467
    0x905100905031207020a03110601050d06110f03010b040e06100806060d0603121d060c0307032a030c0210080105031f0915051815010608091e0610050a0b0f 68
    0x40c0307885480c41c824071422400d8142d1000c20030078a16004910103015501945070b52002170f070400c6144e03898034800d0040350340c01616030f0040130214216600c40d80303402140121151906281d41411440b0350030991000460941c0080d05005050b12507400307d4001c03a094446c00640c1d5443c01e8007901010f0020285030051030040740031014149150040c00003950419080b82d0b02ca482c1146c01054007050300c240020361150018010460f040c2039084440c000381e090055400c20005a03801c44218103030032500f840144a55005400e5150f200340602d030418800e03282d0b80030900d403d106010440f0713404130203103040c8845080104020707100070628000c6589800060a419640e0311540750051a0303904028002c2c0c44202602c0c14080c46560200e409002c0c00d40a509501d21003000e645e036a080b50b62180303505085c001c00100502401480d0b85500f1034450011340d10305d000640104101c000200000c449541c2c400d0090010040468031410050201079440b900002c1c2807524041c2903110b41203000020340ea00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 475390962 1250 475389712 475389731
    0xa03110a0b0a0503041104020706110d0c170a0e15010803030f16020c09090a0f05010504030306120804091d0609010c09090b01022a1c03020c060c1c261504090510 71
    0x1140c0c1141c40074ad502c00380400120040d4042d40c0d580303400422605d01b209181102c0404070b1030240720081104e94150390261220b554030f41aa134041c045151542120780301c5d4001c1c003e01c1e458000e2029000e06200001144c072482e0038202d070107034032201408111010254096041c0000d60101c0c0c0c964610f08262211802c984602400034075000c075030301001c2c00f600b220f82c180e40200704040d0081030045010740e5040c80b030147c031504074800a42540000400c488410401000f000c0d40d1500080a00c611044004180d80a006d66950420400707c5580c00c25954411440840316049440c0c0b03409014240380411250b0030000020b5941d00710304418441680c0c00300b1003010440c0ea4080984510000078060031070704680c210f01e00f000b9001c1c0060460140c02a00a16031090a185055446141c00100140540b4800d452482c005440d101810020002071000e1003442c1203080c0c1034450502c1030280c00d48001d02d400b610030042d241c0c2c0f4180103449681000e0b1180041040040c910303400703c02014000510042 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 475392212 1250 475390962 475390969
    0x8271f1413030b161b171b07270e030f070b0a050a021908090c030102180a0b0f192105012405040911090a03110a0b0a05030411 56
    0x2403541000310100000031140c5452608018520849100e040c04198036200c82e0002e43c5800b11540c0e12100050315182c2541c45440750041d000b10300c5018280345401100a4181c220b0660b000401d035180ca24680990603041d8481081700c4001070003421103c2482400140c10135084544c100c083c2501c0c00d40301e050341c05038138030248121000c8240c0010b4543c0c1d211010f280104000c50111411030441c0e28080020701d401d0070301c0c001c50f6400c8440202044144c000035500303035510303440a05039070514884c0040b4124540c6091004100b510001000428801c040f8070400030401c4c9650050090038a00b4007051050003003080580e02141d015112030a144880c0e20b104035046001802500e60510800c01015080c3d1882c1e48000c0c16501000d101400a40300c00d0a404260700c900c60031800080d401304803c014201190348032100d0040d8500c038040c68103030150002001200543c005907040e1b016804052082c3c079100034620000c240f014a00b41c10500d0f84407001c0c5c141d010080010f0120341e92000e2151255a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 475393462 1250 475392212 475392227
    0x9040c090e010f0e0a09050c12150108010f0b010c3801030804050406050402090a030209070903051b011b0f080a1e120b010203040b070f0602041208271f 67
    0x1180003011032041d83d5941c042844209140301e030b020400b8500b8042055110703507000e61034809802c400188000c00c220018080c12590451003182207000d01c07581c626100f440025041c8c001c05950f0000b15070f00f01070702920700495150700031860610031084000c0c00007409540341441c52024204a07805200349030010906200811400310801c111600004802c01001c134003c5c10540f142078508100030380c5c4407800c1c00100d1003804401640050190720030401031a140c0c08160b030040c110f00c2e000c41c0d4150f40b075903900c1c41c02c00d6000354807803240319032540300c9402d5a010007012048001200c00b1000f1601c1600c0da100700c004041c0d0050b01c034050015080c0c2c110b90042215814902c018680c1120a03641e00a0007004104240385120806080c1025038807a98030000940e070586404130700c500d10b80400f5035034045111050020880d0501c1d006c3c48000b0341d00000742500c6035054001e01d241a40c603d004000c074a80481a500e8504041c80d00a440c03a0a60700e0724a010f102c00d0500362041100000c10341c0c401d8070240e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 475394712 1250 475393462 475393469
    0x160302220f1202130f0f061811120406020d110c0109110910050f210d09050402030112030c020d120923010804030c030e0306040303090b0901050c09040c09 68
    0x38104004449a03038400d0605403048a0000740e10300203080d2034107000505034840080c0070350f003c4d140030344d400000c030310541c860042102d2034200050044200c04040c01034640341d0344046111070b0b49100c070914081d024010010200c021002c4145000b0851500007440080544044e10840c0d0201d51043c0070351450348481c20310147d00c1d41c407540b00c281c850301c0706000c1c00300c00300104c0380f1001c0740201d0440f900340b51800a001d141401d444451301c42c140400d00c0341707003641000055070260355594480b28200103491404a2007100c034014044002c2e1a42000e06601580e40c0200d006030702c1000100031000b183d581205c0102d41c5482c007840b6191181c00001c00b0015100c2014003220543c0d030102c1501034000175030780d048070f02c1044803440880120075007010580316407061a002c030700700c680080c00080c8640310301071240e8864100444c1803d90000468030784142250110080380d0b6429450303040c0404004656031241031200240007610b0316040110303080c01292500c82c043c0781c40f03e1014000c0380c01488094081e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 475395962 1250 475394712 475394737
    0x5120706060e01170c150301050f061c0b0306011413090f0204052401031401030809031c02060a0e030307090b090a0b07050d030c020d05072301021b07060e09160302 72
    0x30b55841d40700b141c61041c00b5039841a032074450407900c07000b1824004405030a042207000c07500d0443c0e10f407006003c4960880b50400750b00040c204034000d0f0003020280d4840644030340d5100010301d03818007010705184c010184c0240c03000b801c00d8030f40001944c3e509225040b00300c06100b80819001d80c603142142c0c4041505030020b40c01804e05c0c042100821301c00621207191090929a0414114100300650803106410b00001188441d43d00500c0420401001018240c501400b1110f100e0f0342030301e420041c0d1482c1d660301401038020a0034014040c2c003e0142108407081c9201440c03031824007000241c610b14031407040e40c480c0e020210740500c140d918540c800004100031000c0c0d544c0d96480385041c940b21200e01004001081c500304450f10514400181240d0b06242c0c1c1c6c4807103261140c40e40341d00207000c4004220f1810011500502d0310308017028005000e1490a1b86003100c2c4110210000c41c0c1004480c1d00503508200042c50a100c5644da409605900f240d0b4103030036a4640100360301d040300a4801d5404d002075 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 475397212 1250 475395962 475395989
    0x90501050912271e1011031e0c06150f09011d060a080d080a05090a02101215060f02061b0703030209041808030a0c02011b050306181305010510030512070606 69
    0x21003040e82e42540d04611802c940c00e0005c109520300075107501000c526070040c1603005205c20f036510f8540e850002003e503080c05490b810a80307140a0340b80342800894038880074036400c1c03440340c04a083c0200b00f0185500f08480342802c03581000009116114a084065802e0a2075000b06516032600b80002d4041e001c81c0c2d040c0c480000c610603018040800030381d58100182d18120010b10804404120404030540c0105450407900031403004503104141c55200204140d83c686502064074040308080d4018051038442e4582746580100207410300e20000c0c16642c00c23000341041d10221401c001308440c1da03035506040058a4a0720b01021030f0081010807000d0380c40c11140c01200b8248400e100c091813103414440320500004070081e00c100c2c02d80340040a03a01d00c83c2d00b01a60505264059006107a1140700034154000d41c0400c450500707045003060701c8029000054803d01000c1c40001c1c029254044542154000494079542d034035036a586800081d6031601d07078042801c50800200341c120710018004440f460b507 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 475398462 1250 475397212 475397239
    0x9151d010c2f0d0c0b030705090409030e1e010f11031b160b09030307151401060f0f0201110d0908040b0a0f0e030a0209011406040b0d09050105091227 66
    0x7960340032150351240402c1d41014852110f00e45142207100d0341c0c0d40150100c40c0702c1d00e090010f40780307030308054000c80620400388401910342e20f40e4450f054103035020f9070311482003031400020b0141c0d00100929420180d94059607400c03040e40c1045441c0200030280c074081c2d69200c5424030403415400f40a1301c2d943d49101da404281d042103c00201003804410310100311a1640c3c2d28226102b45100305040c00750150003e100b80780109084503c0f241c100440c1c0304010541210002022080c4007003600507001062040300d0350390010341d10018240418249000070003c1c00e020746102645409a00034185800d519603501c0320410143d4000e940c001c2407003800650b01c640d811f00c00a02240380200c000000102d4021004a09281c00039144420b950090402c00f000d90070b01c1050140c0480844590f503318100700400116001203a004214800c812880010034410302c1c81e00ca800d41d400500501d0f007960101e803501040b10340030000c030307411304504038440301e1500310141c1c000c540702400c80a25540800e081e001d54 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 475399712 1250 475398462 475398503
    0x9060903070f151707081902160b0606090102031207020a050706020a0b160c030e03030405030d0306030204110a0503150411030108061905090a031b020603011509151d010c 75
    0x4605942c0d104140c81c201181550044444c5007240c0b003c244a00c69120114000030b0090500e075400c42e4580c24500070921446202c00d090380d01800301d07041a50303444402d00042c0483c4001d015003081080350100d180c0440381000039a00d000d250765000e0069005000709090034002c00802c0303c01ca6000d41600d10076540c0c2e42029480c1e44110720199045005c01d000a1020080000c110030b0602c500d8840c0000d120041c0c504441c40085280d0070f60701803100300404100c82e0781c2003224420382040c2c0d69001c1992410351049c4000c0e140000000c200b6540b0512403d030001341c04c2402c0da039202c5030180341038800790102c00c001006864980166801c00d00f0000001c12030060110392140301c1c0c410ba40c80f4440d4200da80f0441c1044500880704104160449400e040000c1e102c0c07401446502c558002c9100400700b1038000070000c4e0300a030310004214228107146403c0c1d503008200c01004004000d9440b040c1d440910300901010b58001c0e44840c040c10181c0f0050f90340e07000b05801845160000d1a20800c43c100c030260 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 475400962 1250 475399712 475399739
    0x18010c0903050105090d1e020a080d06081207030801061d0607140610030201020304062106170d0206100902072301020903070b03060a030308220308040b010b031b0906090307 76
    0x290b520b0b509000002d80890000500c041d03808180756904840170b0018400a451401100c3e0030070118082c0c0c3c03030302002254155000e4840440d00c4000014424609030300c40d441d0040411503110301e00014401c075400300350084207403411501d45d402c111006030381e074590460f610400d80002c154014000b0131702109101000d0b89003e40340c00494211005600c4180d01a0601e090503c8024010783c0108000c0c08480d01c260b049050500744030010940c0d0041a41450302903a05a8002c420396042800201050200c100108400030026002604103130400705580903211959028120340c1c0c071703000180f1504019800c2800d411501921708100c001d40124643d1394041e61055826501c2803054120104445466404a0b801284002c0402d00700c81e2556500b5540701d800108054208072060141260646102e511071315914800d648105107440c061800512034001030300a5840d200088c400c00511820101f121340c209131a42c80301c2600c404d6218001042c40c0f01d05100a5014004e8000002d40201080351 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 475402212 1250 475400962 475400969
    0xe011203090504090c0519050d050f0706051213030512070c02130c2106080718050a090809012f0601080705010c080304060e07030611190203041d18010c09 68
    0x990045803a07449081109540b14502d01401c0f282030803404000a01d4101f4202c0c4d034450140c40014002a55100012072403c000541035849400c950404240c05100380200c034058045801d0550034262620b41d2a4059040140403100c00d544000d101010f06000d803080e10f0101d01061a19240c9140080300141381043d03404d012802100501c031000c01050b120b00076040c02030f40c1daa03211480c1000c880302940245814980700880d0b95501c1c2d00224001da0184001c0010708000002081440c806184100440308020041c102e194030b046030140020f40000c0848030011000d1030044545450a0b0081e81ca61051600c0320007403141012840b100a130000c00c0c1c090482c0c0518003640d2012360b6480c01502c0d4007503002c400400c4c0100404c002800140b05502484509541d00104c1300426200c0e51100220b41c58815401c01e001d44c0030402005106031003260100d915114030285081c2031034016000090750b02c58100210540710800060f0f4010941c0c81d11003800200000248010048040050000e003203502 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 475403462 1250 475402212 475402217
    0x4170d0f0c05040b16110d0b0403110105071b1b060c0204060b121f09050703050405210406050a050d02040306090b01060c0203060f07050705100b0111340e011203 71
    0x40080d02000e0090080d03c04484040c0c0c00c543c50115100f03810140d50007079400c02c40b48084803a01c80500c40c4c0742c1c000019081441020303000482e00b4a420081c021804910420169a0600c0d08004189a002d400d0440c01071100d4140c040407042c0d454840c1140103148c04014030290311131400500c5980c04003003c0011402514100300362900d5020780d030640e100703450710456450301c00c00201d8001d4000904003250950300c040034448035910703400000103442d81034450600207500e840911091000901117403261400c0071002c4095540c000d0001961070090748151700a0040200e1100d01c01030103441150702c0000e20351070455440740c591030201c1c020702c0704c09416a0303a5030141002107450780c081c4001c801d1494004006002d242c2d602007611104aa0080050703042001c2800018002042001412483c0e00300b048007003503410006000401d10b80000d000b08425a0110085000c400240300383d00440c44d4a9607040c28403156810310604550066502c010210f250520001414100e0040002e80080c42036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 475404712 1250 475403462 475403471
    0x216030206061002030306060912030d0504080d0c17040b0601030e06040b10050603100e0403030b09400f03050f0c030903010c05040302090f1b0f03061c0b070804170d0f 74
    0x3d11040b6540d000c00c0b151980c0140c02004199214544003540c44402500750084070328145000d181081030b0f500030b80302240c0902012401340800041c5000c0c003806100c091410032200f68100c2c2480c00c01c42005071003d0200c0304c0c8007011030030591181d00309078195403651084680340d003010702d4085034100d000c8403140f1105500890104484c1340210440f8066030b11041200d600508292034038010180144c011001c1c1980c41d49a0034903a02e035915075611400a00420040850700364284c001040c1c81c00b010b1651032030140340320f59034011150b0150505503070401c400021980003854140c0d0785102c0c001400c0c40034080840c0c42d07059008000001d00c107107030080c1d009010284210400350b9040c000d500000394040c01c40000a040188440c80d0340d58441603a407000c1824002110b448529070744050458040b60f9000001c104131800c1a000000c503c00c400000c1070003e4050b51540c004000000d40310300200542c2c41e0110b0300b030107034241e0b04103640052800320365035800c03a0051400042100d5124103000030b050 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 475405962 1250 475404712 475404739
    0xa031a070905100f1818140c04030f06090215030108070602070506030f07140c07080c0901030206250b100311040603260d020c03031902030705040e0604021603020606 73
    0x41024104682c00a000441c112014020544a5444022450003044030b980130481c0c0c142c628510708402043d486851051304100c0220500540e13510415110490800c04144038690b500390040340c088076044103903030b11b402800b0315000c005083c4200003c4c1d40300389034000196a47c03062000850480f040102140c001c41e9640030182c1c5ca80382241305159000d10240002444a01d244d0b103115409400d070310300122440c2c6440100b404075040292100c04c1588440020b0002c0d210800c040501d854044441220b50f62456000070f14034840c8134580b05003030000380719842d05910340407001d001241d030100c42641107145c01c448640d2062480d1000b42e690750141c00c209501405c1906c1801e0549070000700020301b1600401112016002c0d81d00d6080700c02c1002c1001c55160080b0f0b03c040c00701c036a045009103580e4241415412401d5038104044900e09104000740203071150000216030485d85148001c00081d5141c0c00003c0003806200c3c0407140307000012021808041e03012031101e101e82012190320340103409 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 475407212 1250 475405962 475405967
    0x10306150e04020603060103020a1e0815010503041101032309011b0c2d0807060203061009081f181109071d13020c030c07030203070501050304030225050a031a07 71
    0x1000e07030b0043d411001c10004110070354400e4000b4084890300e810304410300e0760031062038050309420142d0140090a800c041c4440440002000100410246000380c21070030641c40d088101c02c081d004040c10f060380e61526a110040001c52000c006074000148034480c5407601180740a00320604150102224040c00b40f0803040c0a14000340b0150f402030b00803020030008a80d040c2c1511400468010710b1071814100340d0005174464028000305c1d2060001589908144040c40086002446414144500c01e02c041c80407240000e032204440c7c01c0e60010801403910b40d01980010140300c032040b1103074805401c00c441400040c10f0044880081030700c13040c0059070b60480449020841030300e80d4020307031101c1a45000610303000c1581c101858010400618120840b01682d155a011030340711010381c0c02c200344c1001986028060038008200c00c3c02c0041c0b0354501b90b42c1c0252190349000c41c1040c9240b078100320709018034441c4460b6010b00390103450100030f652242401c0300c0c41140c469104003c0b00c81700002031401c52 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 475408462 1250 475407212 475407239
    0x6030c0d060e0705070b1005040f0209030c0105120a02090d02040c02010c1416170c070303020d121505060d090c29070215070302030909070807110d0f030b010c0b01030615 75
    0x29516030b11941001410340c6c0b03046e00031202414043d69505450b4000c203480da01c42c426000d24600c501e9005a4601c000d00605040042101e0b005040c003400303202151020400074030b410351000c2c0302e10b00165607002d803800040540024810103500286488078045140350150b00c00a2078803140d4547c440c0201c41e802900c62346105005013001c0c04500d2104d05000280400290640020040c03a04c0e070400071807081d014900392041e807081e40160300402600780c0d007641010010082025480d801e010011251001c0461880c00f48207440c002c907000907a40795040d900c0d0b4004d10855500019900000303680700b000b49201750b408004407007488404861040c9401e8410116140d0301d501920603140c100302020011b002d608981421340a5020421010201d981d402c010300c0c0c42a16141c41d0355500f03040c41c810040101250950003a400c2d40328150803581d6907044070803124242070358038010510b9800c110048612009464006014444580001c010407104bc3c100e054040e2070f24408421060392603140318a0341 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 475409712 1250 475408462 475408471
    0x7030f020109050601180f06061e091a0a1101020c0303010311030f060109020a120b13230a0218062809030611031501140f031003020306040f03030b010e0303091e06030c0d060e 77
    0x79019103103100280350f02582b92890080e090511081480e0b98144c580d000d00305c0500b8009800c200000d80d03151807a0800006054605044000c5052080c5140d015684c1c0c80180001f41404000700b810340d000d40d400300004032261841006580580d44e4a12804019400c0351040801166010b014041e9410281c482c1e003c14080041a540003c203940342081d00400030003a10464050111400680e03081803511003078040d80c0c5051006a0301c00c480e1980300030805110407514400e004c20031020028280304010344840c00b07569401010100440903003a01c003100c80d80c0c401804181406215841181c16401441c840e02101d15204404490100112030000321034010b5030120f00301f8400d241460b0084d8000d0760313004010070443c221f03c2e80c5070f400081c81c04800710340c2241c81121005044040545c035000e00b1004060a00305100c07000c1301c020001c0d840e0700900d49401c1c0244940e81520200e8600c00500500e8000043c0504c0d950713007402c0c44403103110f80c402600030030040d040500006540c01e40c198040d214 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 475410962 1250 475409712 475409717
    0xb0a0306061b031715060f090901090b09061003020c0a050c0a0506040b030c03070516050105071e0905010503090a060603030f090b16061e020310050a0e0103050307030f020109050601180f0606 84
    0x10f152512444010103001c0c0030f002e40700001c800740d1a0070b1b8640d00d0041501141002d03100e03444075a410300304003035940160400120300341840a90b2445450305440150000070489001c1100204000304030001d02030b05440c95010300c5810001c105103d00032800d0700b0791000c1542d2601d1081c0d105d0f0b00f4040e40744150b1080395103441080000030400b07880a005540c010711545052403070060040300381044a00340d0b0000343e4082c3d54070028006200d400030410b5210240d40c0da044002c4294405000d0612800d6116030341c11701c0000400a68014010310180100c035078030900c100290b54482c02c00030044c240d0340ac551004900401000704108a002050310050401d2403030f5000c100420390f0b42c800c007500072031140c44100042e90a00031440c044074009540710b88000014408007500e003004007c240d60060b40240d802902140050002c00c50105c1102ea0054040c180b000b01c001180101702c0c014510824060031a0041000109503110a401c0c402071107000c01001b0700040d1080f8600004444951066101 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 475412212 1250 475410962 475410977
    0x9040b0f0303160c09020a120b0d03050301060c080d05092104080c0d0f05071502010c0801050306010303080612030a120e010506180702031309140c1c02090402040b0a0306061b03 78
    0xc4040802d03c2e8003020344a080c40000180d070300c411a1050340c02c10326610f0045641d008102c01100c1c5903115100f80c9000407164400c40300c0c103070784014289120602036801081807008480051000e41c8003228031003820a030b810070240c500344440e5612120f9291031502c9115090180003150107082c42581c0550302c014025088001200c000c1103404092003004803900c4501182d80c0d00402c81c1403000400a02e4070001c91000c00c0c400c3c250007400c44085c81d1515050140e00801401181c40c0041e03494152949400c00c421680c45002c000f81000d41100c126800c80e110008880c0d0445a22036180c40c8508200c041c14401c0c0011100000d007602c5003101e00981100030440e0000980840b0840035802107154010b803071500d250100c500c14048d80c1a040301440944480f181c02002c40c0303c40c641030340041c00c015a5414138060002d800f0701040344d4501c0507201da4010904034041c5d603540c0d045038001e00442132520380d540c8001d40090080c0040e4800e81c80071940c0c40b0300c10401c07840e003060018404ca0b4540d50364603 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 475413462 1250 475412212 475412227
    0xf080c0705190621050f010302090106090605030a020a02120307230f092806020a0b010608070c06020d060f171204060203120a06080303040318050a0311040209040b041109040b0f0303 80
    0xc5804a440410802c0c04031409084040949140300c5c0034000c0d00d9208521483d0760550041c09003101042e40283c040100c00d68040144070b6010090701e801203d014000340c1d450048c3d070802ca18008202c4100c5038880000818072101540005034038400701c002044828545171180f1030b240715805144940d2034521810040751950307103400310011828100c14420480074a0b5007010303902c2411000e030402800759004040440920403007010542c01007800f0304e0082d5180ca03040d4001800041c18450040c861900410b4200459000360000d001034180401a6051307996544000300f0300300d0820340060b160740203100109032490b000c8022641076480c1900218070b1314242c020042100b0304000c05020ba03540d070f10500403d10410905c02540075500076604c2140389449a64003005909407070380990310940504000300005920840040140f03407040f42c0042c1c40d5140300000ca0007605566040365440761914a17109000b5010201902e00d80350705a41c200100f991a078140b010002e94071320800e51641c418810034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 475414712 1250 475413462 475413467
    0x80c0d0b04032001060302120c01090e190c030207150603110f030a05010f05090d1d1e040905010e1204051813060203090703020f1f030203070201090f080c07051906 72
    0x5410a02c249071451001c1c0300030031000c0016442d0b4a0100c01a51500000c0080d40751074034010000f9220413015003151074008002038103170711061180903000c0308141c00046260b000c80d24144655950404180062103550800400a6014240444400d05200c4a005018207940f0600003aa940303c00301c801403022510070450103034441d04d542070345845013082c1480014006e0003200018400110080303018200701c2c1e0920b080007946204d00341040000082c0b070340b924201405c01420400d007522507829000c0e95440076021145525080b0341c0003801e116444040060542c89002550000001d65009100e04c504100081c80f0314810320f60701441d0354030200240441140603d41140c002d8000c0040482c050381c40e01c05030b03001114050100d80110400b0810360400c4034210b000c2d180c0407074481004100554804091a22032051001090b0303020000400481c000d600c8140e007280c004600c0c64010166107004000c0d030b48400401042405000c0d00011641041c54159807104200995031300301c2030411008 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 475415962 1250 475414712 475414733
    0x705071502030c0d060b03180a0b010909060e012d0e0a120207051003020702090f0103020d410c03030307020a0807030e1c03031d0a06050c070c0618080c0d 68
    0x500c6807070000300004914030300c8034070488000380b0210446d15281d01e000000d60310301900c4004c500105800820b10000080d2001e01e44e03030b0540710a14000200310025090510082250f4031507001c1542c80d041a000026424408441012101600040a41105024010a03240e02030060b01e5103a201c0100c4400140340b0525035911650707503104a60010b60303150000703a4984c0782044007002080e400564202981044042d590f84001b000a0944181d40742d0340c00300d0f101e4500182e01424010020601085188403440c001522005d03e840b0780761004c2080015900141c8030703010040591041009111940c180803050300d20850054000e042581e04603110341c01550f00c01c5a0482c00c01ca9440050101c542d15a090f107243c1c0010011400910285441c029044034608403445c800880600c02c55040400001030320040d0300e03809200030076503880e24804190307035003e0003c2c010044841c4290204a19a11050781d8414904007621000400c0d95495560f4848100c1d00060ba002080120000e0101c1c0b200c500 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 475417212 1250 475415962 475415971
    0x160306050d08030a11031815070c030e0312180418030f050c032b150b0910030e030d15060503070203040b180a090b0f01170f131407030b070507150203 66
    0x700740500c032281c0318280c2d607108a87d400c0303690810018240703142d64200300802d201510032003041028144000301070440200c442c0000c00b0003003d100300c601140c505011b440700c0c0c04c1d8001072082d1501465844413440120203150940942e28001c80c500151016551017050142c06807907964035010002011175903540f0420226485d071004100f140c0030500d80290f46904004484400300310100441c60312016a84440c196203d80340310070300284011034002085803400b40e8115410341c410035040030154003600707440f0311100c07c1e404082115615414650401400c01c01c00050703411030140c448209a519010650704da20040c0d100344406c0c46402c07028402031074800342412042e1840d41001c4001003e00055410020036141c80c4d070340d59100c50034201b811000800302420442256890344000e0710007040c00070f10303680c0c542a219010801050440a074081a150458090540010303980c0680e0307980d83e0584001c031909a00440010f1290788a10145c6411540c030041d5410144500150100a50406803 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 475418462 1250 475417212 475417231
    0x9020303160312050906150f040b09040804030507150e040513080318280b0604270b0a0203040305030f071b0302011d19060f14090303160306050d0803 66
    0xa0722200d080221030344809a20a507240300d441078040541e10305989010304000d01d05e030f0118050003139504401e41c151030311076000d84840864078203400000d00545200840076400c0140407003400203200c0c0f6580200141d1340118101c99026a48a07481e03010116406001d07000600315828000c054038042d0440398111100d5640004481c41d2074550307000c680d000303840704890150503204020001c04144004c51008a44841da20780300120303c0711282000c2c41c0b00000420007000080080c0741a9216030041518142c0c2d00d040100b5406000d03803543c1c1074480e100f815507a03003082c500003400780d0056008980c400c0c0e43c15a103490542e00da0229051590398040e01074001c2c01514a4040300b202101a074000040d8043d40c00800d0310358a804c0e03c4107070b03c00401c0040459400003019503020903050310b010031805900c60000500c00458496080c000d040c02640803941d051900d049c0000920004046c6014285000c41703040b144000000030b8040340d40c2d5104881d0030607070b0701013054085040d02003e0340e4030032080d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 475419712 1250 475418462 475418467
    0xe070801090f06031211060108070602150a1808070606080604030c1112060703060e010506070b191b211506030c030216050d081e0112052a040e0307020603070309020303 74
    0x9076698000d2103114011700c80046c110080b070041960003001498010082203000e4038561b418400000c0d1201c02400221100c201c419020400350102a030001003800d4044c991a0500d940c1032504415503400240181c81c1d10341804008980708201080050080742c1c103445240c0c0ba055a5900d4a20314548880019885071403100e1b100f0072413405010081c03003010281c1c0e0008815090100040e600d55040e0007150081a0502100c0c0c002010080050741000055080c81c0040086a0021000c1c20702c0002c8045121600c41d54414015000300b04d100c42041144494001200407400400455060800c3c0d00000314501e041000401d010340d00443c0050030900d0054a0107855070394125500058100880d0280c1c4602165481503511248060300304205030b031016020780092030b082e4030001d4180030360701d5211044c1c4050010028104205080c926800c25070390322141c000910702d0005080d2a80307203802a4280501d100c200d40c400f02c216443d0760f0740205410f007140c42e10141100202440c10049030188800c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 475420962 1250 475419712 475419719
    0x21509010c052b0c03061707050f1216090501031101020c100e1801030b090120090910030203060a0e0111090109030f0204060b16050d0c0b060d0c1d04020a0e070801090f06 75
    0x60740900141c55541c5e032008180c1742d00c1c1045101141c00ca00c2c81d0381c54030b03401003403080c0459503071900c0341030441601710f072030103880304502c3c00d00750070300b0380345000c4560312001e10000140c4540c0c10340015040b64000c000401c3d440b4400740041e602c0341048905283c3c0603500380e1002d4400750043d01c45040a440141c071500b00d000350f600e08068814002c0c0c1054800d48000001c000911209004502030b40c010002c3c5188900d0000552104e20300030205a544200300c0da00c000b5400c0c00320009008015a002000c0302c1d924100895200001d2000610010350b650a060040e4034650b035880c1114802d001c183d50300003845181d500c40038010800743c181203038000d0b15185d00040d01d4400d1405081480c024103006020781c403083c903100303241c94a400941402e001310540c00d1004200d28100e1654170610648041c1d000c0e84551a0042003003001d80c1141e100d220070002084680303060003003110302c59407098550040c2c15031a440c0010811004585550015580000610000c80d02c0d4000030044213428102103030305a00c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 475422212 1250 475420962 475421047
    0x1151a0d1a030a0615091806020d0f0f022d120a150308180a03020901150e09130209060915102d080a0e030f0901051306021509010c05 59
    0x60100b1340381c150311050070041000e2000b141500400081d0820000c40380d4049011038482410100900429070210304c2041e94980c927041156208030a8600700004460041c2c00402504010300d454440000c082c580701045000406240c070040304050500d08007a40540700041c5003600a0400728125142d85d0352800324003800417600051340c4510703c01521b0342c9200d01498050405a00340a00c03c46507042c1c108050b89400e0f4075141581c13440001041c0308000c2c04410340380407400344020342d00074071080300304034807522410440c04035584202c507081d645071520020403404c20350a075517014030b0603100c000c142498600300a1841c0b4002241c106090411000c24901e214010f2100c0d4030080d032030500350107003046680220000e40c03015002c03004110880c40301040790b030780e4001c99141211541001811541503070240302070703c7c40010742804840c0d92680b1524000e48403e01c070a1806d40c01c5070164045007140380180183c108642003565018208003448241301c1845014003003000d001c11866148000200 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 475423462 1250 475422212 475422223
    0x4051b040e0d09080f06010302242b0e0a05030307180e01030c05150a0206010303030f0b09090304090e0615010f11030309010501061409030312151201151a0d1a03 71
    0x1a00c40d103d078101a8500810a0300f41010859410318a4011100500059035140d04451519803030140c00e18800e0324500d5071200511030418590703810480b0f420320341c03004182d0b0500c02c20310300e0040d00180103c405a4105641d00e0104420080041d003041c000583c1640c86085555904044003400c18841680c4030800c00d0b403d034080c3c205a4200906050074011170403e0034000c818980c001c3c41e030381d02c2d00c000600002c0d00ca61040c00001c00300340d280c0415040000c01501f03c4117601000400d02902810042c2030b040e503a502605c6540e844604168a000310310001049180c4500490b000d8139280d83c14070001120945040c16104090068600749890780c2e100800180d4800c1c0414000041c695050003400b0f481d80b92001030f5000c40700003c2020300080c0d20044141e0303144000765140d410b030a440b00e0000307030b010800306000c81c2e4010603c0038126011400540080200282c17500e00c4080e0151500d5145207100c588202043c00100308001004192000760b00a504400d91014007240c1500090000b0742401c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 475424712 1250 475423462 475423483
    0x8040e060a120507080c0a080a030e150d14011a0712031d0a050c1f0e031908030a1b080f040c030501050106021f020a0801031e020d0311010c0804051b040e 68
    0x541c000031007888468810002c280036900100ca50030120f032300d46604030b9658414208003c04001c29080405034903211600b07500719040c80180220b0b00c03050000e0b030b268002c109500f101010b140400c8000644043c44889040c40359000400007440e200044d2581c1c0403a902008401c41003580d100325041540c1d08103040d526213039001c031014103103440003405c009240481d1040c0c550300c2021403000c1050400700c032032124664040942040b4081c00080300c0007a04014020380b06404c81070841180340e0030401c1000003036208040d4a10f040004005040d10608100101202400032820a01c08141414000e200082d030061003040450956502d942da07075402e5031420703402800541c0c09103902007041e000f01c0708400000c20000004500345011201c0c010001081031101070300c01c80f10035038280844145080c070981ca2030f801400360041c00c540d502d8018410385280b030b6840e0f5554a400d940541a602c40c20150740520b420000500344a030907103881005003011904e03890741c059030f85d03202a0300c28a814040ca0160 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 475425962 1250 475424712 475424723
    0x130b07080a0e09090d0e0f0306010608010f060f0c080f09030703060203150328031106131a04020906040e03090a030506040308100f1e0810060312020a08040e060a12 72
    0x441c405400080c0000240310b0502c0d10031030700c0c8070030070968940016550214400c54500110f440442c1c0002c40c002403031802c0310503094040d103400450200c0d04103842038122544000c404072842e07510b52040b9000d680da01c1c0c0303102c0021006146d0b123000c905282c01802e95010100e40140c17600d10384100203403401c1d000341d1080b25142c0d00802041441441640401102c0c6000c0d4094562a41c9262000c00d0260303040b407803131511501c510315a50074140b054160001d2001d4040031910742e402c01003200c024071305102400b250060700d00b40080c200f072030980b5000380c000da601170301c00e42090b100c540800c8060003040c0b60501076071009115003040f07582d031413031400010350280015011502b41030400521040d0010010641c1945e013840c00c200054000303916a088031055065400304943e50103582480c407861340e015414030320620048136401c1040750f015804481c81642130400e0800f002c5002d9031220700004c8080d00902003031104102401c44648810b510003801420401c4031601c03400c400710400c41c508001d40720f = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 475427212 1250 475425962 475425967
    0x30503060a05060c0c0415180903030b09040f02030705040c0503060904170427020c060f061809150117030a0507060906060b072f1905120d1808070506130b0708 70
    0x110340c06c003482001031440145c0d58603030b11141480081c000a40e580024414aa5a6401e81d002414442e40c8000b280910003400403005051508101006210f00325003039109014440c800129486c0501c680210683d5545481d419591003608110b00354500420a03200c000c143c0040c030040d084003030001c1025002449030f003a20840ea03d0741ca46c141d160540740c04080b8a2040002029000b40003502d42d0303110851602008256407181e0104541c50000c01d240054449150140504040e02085090511030800c01440990fa42c40105040d5160088111606a0410019090641d1040009280150041c140401c0740c0629649031400c690b840e50040010a20106616003008010300c03014450340e5804a05080300f0041c402910242c001c940f00710340c071810740301007000000741124466400802008041d079205000c039201081d140c401220709940040ca42d0101c0100400c4101111010745002c20000d0030920709040c00e10031203501940c28066601c1d100c000000b0f8000c1d2042c010105e071b500c074002058 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 475428462 1250 475427212 475427233
    0x30304021c020f0a091d031303020904030504120804140108071d181f09020f040605030a14091e070e040b09030d09030914010f12020a05040e04061b11030403030503060a05060c 77
    0x1585c01c03022141d1b14520707001000100780340082d000300407003134a07011964200c0d00d40700d515050f034903032041d41d20019600c0d110140701e509104805000d0011103440c1c0c0c0d200603d40d10700e030004483c0e9120455803407010440c1d61000110041c0c1031800803645680140100405d242c001140341d4102a044542c0010781c61084544c164103007040c0001002450415025030515850051700700841c000d50103030008119020000402d07541d1580c10413014107500d403885034080d0410740e40c007640b81e020300d0031030001d540500c0e40741304814200011ba1800b1500300d4032009459440d00e54500707004a1001e1320b618000c0c40309101c000ea000e5442c0c4a1044401c1c803d44078150418a0710034200324801070340d00e105060205401c5405407158211743c5601000944440040e0b43c0e560401040d0746502543d00315110030224070040000f00b0440d82d1290100a40c0f040d400303140004041d908494903030760710380e2100782034000f40401c00009024070059900940f00a11a900d0f60313841d0008103c01d5082040c00705901d512051054 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 475429712 1250 475428462 475428491
    0x11030102310e011406030709030f120311042d030b13210804260f090f0d03021504050c13050a060b0307091a0f03091e030304021c020f0a09 61
    0x1c030080030b82181c4402258540b82400ca4484804092070703004120010004078a40d10560f440005580c0c410550b01c650340311410054261a41071358440c011074034207181d070007192000b0b005440c201c4448240d0100100844140314810307941d03400d107648100d0203150012002510f950783c180d02c98110390791202000c980a0a01b40403815900c0344405007044080d141c144d400368001d4845a0194008109a1008151201640d0120310400d03d00e0452140070030560b1080b0820802060350580403116400c07200082d4040006030a4824001000342e07216a0440f4403a1501c07041640e8440e0064040e182a00c07504408245942c41c0180281c3c0320a58401c108202c0340340c0ba2050001034110762506600b907141091024003020854055102d180707104c81c0342c1050050a1034101c2e041810018026522424030100c10365803800b0108a000084c141d4040051058000206881c41240c0003840c003551001d044c0c45620f65084010341c1660494400c50340d8020342d44464403010010280c02e40001040c40d080c030103a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 475430962 1250 475429712 475429807
    0xc060f0a0c0c050307030b0910021608070312050109090302010609020a051e0d06120201021605090a020c0106051e0a08060c0909180a050c0f090f0411030703060e070608150d11030102 80
    0x2c414460ac1404a0601f01881480444007182c0c0300d8040342e03841690341016038100c20521041002c0c1420300d40041140401500982c4200740300360000d2082e1074451a021003a406808082800527101b40315110034141c22030307592080503100c01442403601c1400c01d40c3d601a9a05500589081c0c0c0703060070b2560031541e04124240c00200c21164020301641001c00050f120b14000c3e10a074034240e008260740d084643d00798010801043c0051800c4800c2014500340c40b85e43d0404450f01d48034813620917000807082d10109000d0310808001160524040a0108204402402505441a0308501203150400b0442040901003c80c040c800034030a44c0c00c40d004101c004a2804a0356000d002034106010100413642074294019138040f6018070505008030200345844040d60000e45014200900500003000100d800700c1a0b601c140d42d080d24036a030740c0e04030b1034540c801040340c190440701500f07003903000c19442c1c40051480300c4000c00242c904071760011804000382c01820015141c0c045651540d5103030094022 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 475432212 1250 475430962 475430983
    0x21512040c140a051011010e0c09070906080c1b06190507050a050f03090c0a090203250c02011101110f04050f030a080706050c040b0705030c0c060f0a0c0c050307030b09 74
    0x7200740c6003141c02d404221100348030b1140c1c3d800b8041a4000d40001c50180c0b034044180e1304c1540c02000b0714110b25503010ba441d00c150103201e0150402002103a44580310f558910281c4507d5280c80e0255140c040c00070740140c2c003130380c0c007404014494101000e40c40000c1c070090303004001030300c145034408400f03101c00e1040f903c000d4085418820108104090180c0050507950394001415444da20f80e44c0b0000c1b61420148042881c03588995011000300d800744407580654080c5a07035013105030402d458100008043c200200f81c0002290340308041000643c490000e103e07010020360004169011000010742c0c068102c2c40c031044a01cbd6000c0740900250401a6504600a004a00901d40c2004684031000140704082d000350072541c03640001103d80700c03107102315001840c00032561690358400c4d080194698220151042082c040d080c0001c0d901e241500941d4400d40760084e8540ca04480f4035015200402e020b2011910610042d40001d100d9609014501c01140611001c40d002c6c42d2644149040820115 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 475433462 1250 475432212 475432229
    0x20d060b0414040b040608010e060405010f1e0915050c1b060708190e1b0f010807021b03010603050316120c12050a030219030c0207061e0507021512040c 67
    0x200b0081a211282d080e406000e0980c2d000840e04c1000c40031070050a400c0e000102d16609040042c109004009004c42c441c0b0b02820007000300b07121580c2d62038244d40d483c41252544016096404081c614554841501a4481c4d010001040744d50303021942914011500c040705081c0c00f080c0c0a80c2c508001c81031003290040000545090724113880087d04801000c0c00c2d08408a00480c042c1d40307440f0744c0e50b0054102d0002c21003152494400380480520350014660316034000d62040946040b0ba5004070300080c00786003e034001d40403450095043c8000000c000204950541d00c404002003c10000e10091003401d4504950170f0001d40e4a0a0641d00c070ba40018440042000403088070020175640304d0030220080c2c083c44c12035a0b034886100b04401074080c0710302e820070200302c40c5c0c001c004040d050b60004c402d6800303580a840c82c06a4400c0180c1e914420079842002520403080c0d000c14080c8124020010f1520007000109441e914540b1034000d41c00413461207580344680000d02051111203a00e0380010140035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 475434712 1250 475433462 475433467
    0xc08060a0b0f070809060d050103060b04110705150a090212030309011113031101051b0f0706210509030c060c180a032114070b010312050c062d0901020d060b 69
    0x641c0e0381d0310600f000600001d03030209205480b03503100300403a203091211650078000c1d540c482c00e04c200188071103040e41c2d2180d4a803410030300301d000d0389009031021a078005025100d00f00e0103550261080d08000c007111301c030a55403949d042c0165108422007095200401c015500d914003124000d08590700d07031034204800b20b07086c4091500c6021441c42c800c26203034414603d01d0284402c00040c1c07024005c1c1d1514180040500c00016807072a0002103184440c4007000c00c03104110756940050340d26222401c0110310500f60074800d01c0b0954155041036411000f11000c80340382c00400442c49040503000c1c1e40400210000046051669450b13411a6968800480304d640039246140d4558400c074507000e4100740000c00c0c007011044140e001d41410742c070818001592a0b07590069240200441d80d01b400b0031900b492a480d0242e20f0300d4400c4045d034000a04910051180e9295030300740c0107100c10f02c0b410504100b4407080328880b0001c10840f890307014403803070f900168a50b4204918601511403c0c0c100b0000b07074509 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 475435962 1250 475434712 475434727
    0x5010801120305071e03020a111c0219150210050702071d1807151b0203030a050c03091008012d09020a0306090507050301050a08060708010e0a020d0c08060a0b 70
    0x100c207010811035040c20450f989a41d5883c0108200038500034a1001944515400051503004214200321034892106007203240c1c401c10800c030000186449a401e00c14501040c240141024503803822034110b1022008082aa6000c4507074000ca03005030014016080480c5005000c40a401040d0304035800c0d0020f010408d05005010500d5442146201000c01c09030f800308441901c060310701d00e2010880c005444080361034070480e111414049030401c000405181045d80b10fa4080000d070582c259006000c1c0d4501101c0f41821100380d08445020f50751130004100054840d030710030f070080a01c1907054448140942c541001c0044c1e4210410031820402d005203000903c0780650248201650300001c001a02c2c3d525105c7c0450082c000d913080451480d16000a200f60b484c2c008024504031002200c5980000d9103031103195858610654102c00810748190061142c2c4209011031540160a0030b401414180c3c0055602c0984030f101d150003010130136140138041142801c40700c2c40c01400390440030b60700c0c2150 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 475437212 1250 475435962 475435979
    0xa02040f1d0a0b0118081c1b1202150f010f05030105040c0303030510080307150540080a090e0c0a0e0f010c20040c0807020c011d03010e1605010801 65
    0x30040011082c56a035444035103560f802a545581d4605500300141025074443c10f00681d02d2003101105d041e00c0c10544d0800038068442c02d4000c0b00c400140102100314211942c6920781040d280000c3c105500404421a04a6001c16140e6101e000180741c58600765261a000140301d00b03007600f00ba8080c0e414003013008049041e0740c1c0301d1401c40ea4103190014241c0d84c4c03406400490809a000302c0e2150000042c0c0d50706001c610040120714046010080085d038582c502d880308030501029848030f60740081c441401c5003001d4401107242e0446100c2c08454201c2c1c55a039489400d52054001c000450440c040030300240e00e40810380b60340f016101580a241100d03401010b00040c00b81c084062140d000c01c02030180a902c80c0082021241d400360341105411208aa580d2a280b10711941c14003991500c0d5600c80c00504c41c2c0000742c0142800e80244c00b40b903010000440d0401803007607001d0b421440000180392541c07000d00c203100101c40100c01034500071258070110030700103003030743e20403410400d03102c0c0107011012 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 475438462 1250 475437212 475437269
    0xa060810091217150a090903050903070501080601090311040f231815130503030103050f1011030a0f0b0901060e01090801020406050909041e0b0901050f15120c090a02040f 75
    0x1120f0020304240d0240d03103000903152056600703d00d946e20304102d0b105c020590442d028054558040741925007164032903004480e0034004803510b034000740b18034008101050b0302904901040030041c0c008100545401a40303000e1765036001c207001001344215406008941400c0429401094902c660411074841c050086e03503614a2001c251108146003020076020150b200c4c2d400742c140c0c0d000060b607407250396a042c07541c0c650044001904981c080d041c0e099892800303502c210800c4060028513030b403e54940f00c15120040046040c01e40555544c0c062013007081d658220540e0081c4907a560754564030b440c000004080101940c40010a0381c014081480100c6c1c00805440825009956040d4242c1d9541001038082d20700c1111041c07500d080c1c070700e1002841003510145114035804802407045440d03ca8800150740d50032610102e02c580c070381c48103e1440c60960f0140d419010380400b200c200e02c0c040b00005d41513960590341900702960006041000d11171390460040140b08481ca800c041c550041070f041170a0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 475439712 1250 475438462 475438471
    0x1060f120e1002092701050909030a022d01110a02100603080a0e0a0306020703030203060103050f040506010b220b09011707050304110607150b0102070920030a060810091217 76
    0x141d0003044130728254844424000e098061403a41d0324900046208400d8801e60a0181500442c204000540c42a00000450701c00305910742c02024010541100b0041059401130448840700800c2021440d0700824010101c50039445240581d4419007c14080e2610610310030f841c0c0c10f5420b200c1c0400c04103500c0e00603281030030074900f00110b000c1e501400040c11107040d508001c080c10310100b502410315601d0b501440c420502030302c00300b0994941c0304025900c3d01d800c5500500e5075015500601c042400200545091044562489040c095050740c1c1d041000440e081281c03004004242d40d900c9603442140100e54048904e000d01050420318030040052000503c0030309681991b0011512640b00e06040b03c4610741c0000c0720000d4485d20007104000f91000f258014014400ca000c041883c0c9100e200b100da201c071490143c48402c6200c517031580d07010381004211442541d6101c00008819206000c0c5000d0a440e5070000142c560031031810074110703014516880100840020302180001201e140c06406c07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 475440962 1250 475439712 475439743
    0x2281707030e12070e0c090102070518040606141f0201150e0f100b030f04170f121008030d0504020a0e16120b0904060f0603080d0e01050a0c0822080301060f120e 71
    0x2980307c11070060385130120a6011a030000c40345004c12401c0c04031403400394043d0303101d443d0600c01e0b01c1d40c822a03c161000d00d41042c1d58811240d03d4810440c20341070081400b038802500000c113150709014030141c210070aa6100004c401c074903000304201401001015540022103d001000c0142003426128642c0001130881c0c00b1084683c01040c1448070640c0c9556040403144241d9586500c00600400190408212070845090400100708480360f411803090545003000000c604111620400c10050000540300b4ac0e080540b0030341c082603030302030003100c10b208040765030141c0c000c102c03101001461108000c1c1d803000018500300e02c610040d90742c8450710ba0030940000003c201c201c2840c03034445c002c02955100416000d4002004046a50503400070000a00e210008100c5030751401940410f41d444139884030001142d0400158a8840314152201c65414002002000c41b10956410b50958401e070003410114000c1c090322490550310290b031102c04804582c060240c6072403208069560843c43c144080d2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 475442212 1250 475440962 475440967
    0x501050c2a1f021207030603051b0d06020301030f02090708071b0201020f010507020706030e01020c0705010825050304110d05070b0f1309020d0b0102281707030e12070e0c 75
    0x40400304104084007441c10042c0750000b909400410080d44804200b0100710001800151050b010748550411650403e018204050030996061660703450b074401300f0740c02291110031401183c907a2000d140650321580714040c1e1200c81d8010840101c0d00140014108640c4000b0003094586c000d52800c82d41000383c0f1840404c000c5440180d007080d2460584800c10740c07030142000421070b40020311200300d82e411b4508000301201e4003400b60a078070605030440c00f154007004081220303500c545c06d6550700c4015411f00103501c500030400383d000e604148c601400000c40110900042c042c0d0b03c0c821203810074049801c0a8555240d035115030300c50f04a442042515400440c8117884025170130308855043d00e42151241c0e0302d5403240c25043c02500207400c8200000d1030400d1080e91540000303013001c0d9066001d50002100d03400704004242c0d50701c40302c0045801100280310103c010f10514007400e0038030b110361580c04454160805108041d28200d030140301e0342c0c0c0504001c0040103106c0c1050358005034000003907035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 475443462 1250 475442212 475442287
    0x1107110405070e030d08040b06030d1b050f16061d010c0f05030c07060c140606060d02090a0302060409050603061012200d0b04050d0f0e04090c030b090a0501050c 71
    0x40d0360300c8600d03003c240c050144080c0d4a00c5694404000c501c5584150b094604503102d4100b8190760314001c0c180040400d001c5c000c3d0700b01e400002044e284a40d0320460489080c8001100280d0410b0400445040d0082c00284240324044e0414000086a0403c0a000c0e000c03080c0000001c180ca254020090202d905940b894010f010b0180201e425040c0b615044500d116680c1000600b1f40d18662429980807202e001d1070b01c030b4844045060f40c01104000c203461f08004202d0308800013580007503280c6901c1800410004016294003000e04014280d4400001d114030f8500705040c1080c3c80240007000300c034400c100501280c01a0040f54100c1707600503c4620f4803225941e0b2a90350103138031201083e480709161810780700304400300d180301e48202c0c03040302580c0c01c903074081c40141d54041150001d0f1011a03450040303a52141402c0d4030100c601409924501f03072140e52500c410400040c291034140a0b900044a0441403041c24010a90003209400300030b0314240c2540300c480400d48800360304841c1e0540c40008103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 475444712 1250 475443462 475443467
    0x2010504090c0e040203160215040203120d0e01060e1503060105010206070c060b0a1502100509031c0b040c0203251104050c0c031603030b0105090127080f01050604110711040507 78
    0x40d074000070064011507036420110000703607007c02c0e80700800005200e080c2400a841040c941101d0117680d026006080000010764140100c1c0c001c106030300c100c03c6d92402ca01100742800d0089400910b40020341c60002e0805d500c80c101201c400281d60f5006e0f90100004000a0368009415070740310102e803030010158205890710b100507100c22040a40d000d51034020110b00c07607004040c07041c001c403181c2c1c086941c4288001402420703108110b41c5402d01340c0051151811500b40d0100000d504180140d0020300c074051280000d0031201c0040b001c50041e0300102e9106400090410540811144814440c000a540740e59041c0186804032445020703513102e401248061921005544007040c0c0c0b00240c9031516880000300384005001242540000c2c10403c2400e0107500800031503041c6407040e500c1c404180b1100c2c0b0a12034202da00c000103074144046a600150b150300c140402041e4440ca44004241810403004101c150341c08c0d10002c4403058020001c3d400040e031219021300700d905094030007003003594440c90305 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 475445962 1250 475444712 475444727
    0x11a040b0f0a0b090a08070e0604270506060118050303160305040b120603060f43050c010507110a0308060a030b010e0402040f0203090307110f0a030507080c030a02010504090c 77
    0x5242d08620301c1c0d0004903040c0d5800c2c001e0442e242c001d86001040c20780e40d10040c0d0b5510701c1407003000600e50341c1c00003180342404d1603003024582e00c1101d02807000d44110245201441241081d05807013076049001485007079a0b010001000c40816650300104c00b40c105000242c0328450310090305031a14030980704a00301340c0100161401010000f500548510506440612111080b02c4551282c01050000380d03c00c08140703c40c50040c0a03000418103c1c4003032002001e02201c4400100c4a00c2540080400020407119148035034000f90b86c0d5500d840702401c1041501399003014016800740410b200b20100007a0380000d031440b00c40e41628064a00d070f11440c0204031182d038607401c013401c03c1c4000707000403444041c1c02131918060b40c800e6900b009000c824040b1b4000300d00080d40d03256165002004600e01140c8000958410307010000c080c00d541c0b581d0800000d14041d190b50048540e42c10035501048000814014010b5001c0181c010305210307001c503800202184078500030382c4c0c0241d6403402c1804041c1d114521 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 475447212 1250 475445962 475445989
    0xf06051b0f06102301050c120a0c050c030606011e0905060a2604230f0307060504032d03051f06030f20030103020d03020a0c030f030809011a040b 64
    0x945154002407a54261205811250540300790818403000858000119140c088042007042003000c481e120401118103610900c3c00708218402c451807060a41108002001078030043d0301d60401900c1186010703400c0094190120740300b608450304100d0184d0b001003204240d030440003101000c0e208044c00a903100d02603600b009400520200e0f11050098218440104054088414080d81408007114044000301114000c1c180c1b0b0303d480c0e030070381040c1d10010f03140c002451302c1d01500e451184400c5500c2c40e40d000007509844141d265002c2c001850742004541c03412903440d94181c80c0d8404000308010150740351100c0c5404140d0f84000103000c002c01e2120b4042019140f00240d501c40743d50362402009420030601600b6814540003d0200c110b072010480e000311408410380b542103038650f400708280c0b507100700019804d5006444ac84000604d0b50b8601c0005544580e61003006107a00d814001d11031000200507040c10307898104003c0c0354903800560320400b40c4040760046000c8240c13070040380d00758038800c2c0e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 475448462 1250 475447212 475447267
    0x50a020d1b03050303010906150906030c020a02032d070806270303100317070c03020d06230106080a0902061603090902120609100f031119061e02070f0605 68
    0x107404000c22002000550494a0b4030a05100454480321170840c4e120381458490081101d09600300480d81c001c0d0446d8266045500584504119a4010905200782d800d40361030881d2004481c1c000d183c09040c3d61582d160346080c02071011030b0402110580d101800741c80e03502188003c200090502e80d650001692403020f0302c06403034890404012005114003903000c1240c44941841d000d4422004610a5441140d085055400c01c149181c0030700c45019203401003620f034661a03481e0340c0c910007800450416143c400c0d20700681c5540c5441801015860301078031011095007062081300269540c2c0068803210f0b0b051348003509500445180540c0c82c44500e500500c049800460702642c8000c4d586041485141e0980d980f0206540d41e542049103020140070f141d0403c2000d40c0107001190884203c01499400038008150110011100e06581101540b0200014003064424150000030130083c1c0364003281400180b0000307043ca4410181e040c0700f806440100140403e00c1c1701e080c07444402c1c0043c0000c141 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 475449712 1250 475448462 475448513
    0xe0f0a0303020109020f030c0f01120b100c0b0601090e160201060810060e130819050d0f2f03070c020409020a140a0803031005011d09151c050a020d 65
    0x24507010340a4218000280e1059880c90200030745802c0201c0c41c503504d0799001304506494100c080040d940c43c50b0300c001c0300510b1035891030904402d849816001444001e1030321213080c1c5a00d80c0c82e018004607002803d2904201f00e2950404c041c0c0da840950942148100010f41d18849916004a00501d4503500814091140c04145500795900768820780076039a42080305107a60361000c0704142c1052066200408840003000752040d00447d42d445407480e0700d21860820b1500c0e000c4884003090b11500049121410b5a40c0d04030b0302518105041c0d001308203482c1074400700742c2c2d03e039519048050100826444c10b1100c0348044e482156510b07488040c0b8954010242d0742c1c80c17030712200501170b142e0301220058003038420024042a900000011b482c40340c80490030403903c441c100b400440e208201d103108401e02c51030460000c4481e40c0c0da903a039144520551080d042810001804000703204000c1819961410244080207012880109a85188540582e12420120035510b050b41a00c40010b40003120020f0b02c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 475450962 1250 475449712 475449719
    0xd060f05030c010e03030d15080a0b01210507090c020304030b1602010513050c010c031148060306121917160b0c0d022802060403020d0e0f0a 62
    0x110000942600d0381501240c5a480c0c0354801503451440c0240084c3d4160b10610480411001030707007090714080d101011441c5141c0d40da5100901d44a000b82c0700700c5000c05020014880304690075440c0c110b200801c50088c1c030300c0c0000d807030761911200075000321048940c441030038010403802002201d00456020301080348500d040b8041d05000701c500007084c0c00550825001c258013502c021244200a50460007602d05006141c0041d101720504030021030511103103060349510390405010002032811580354180c11386000c01d404004000181c0865500d420000b01c6e404002c12a081440c0c810080c00e56030366941c1d8942600040c550032008503c0c10040c41901010001d0303807600c24050301800c0c424140440803456038940081140190300c100160750100141800124003407404081d040421104424075001045000d0710903a8841130307010003020354981c00d0b007119041c005103091009034244040e040c0c508042e034000751030303145c100c815408101c3c40404441040d0340d40a80d0b00b4030703c1002450410080e66 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 475452212 1250 475450962 475450979
    0x607081b161110031d12040e06011407060e070506040f09050c0d020f0a03050a060b070210030914071a190c080c01020d0c0e0d1e030c020306070203090909120703030e01020d06 77
    0x3205c1c400e51000c0848503404c0b0700684000a04841d80040c50410606103070821400301d024000050605042204841002142801407001811210b015a2021602011620015141a01c507501c028051102000204285500000c0c51800d945614601140c40d840c0c1c00390394200c03406000204001140b0010f0501003c2d18184001c141c0070182ea1402d20040e51004030b10b00866140b0b21a000704a9010808180145000d180300c4020001500b0300003400708140d10303180c602411070071404c2d0259005040520054000000401301048031004807882c0c4080c10454480100c028043c100900018120403010000c200d002e0f103030740200e104000c41d20340045d01c840f640505074102403140800c0c04410b49c841d850400070000d03007500f9000300084810340882201c80401941d1001d09a082003181c180490050703038140076641c040c50307840d4011500c810828080002406000d0f11200b92580541943c400158882054036096509400c00040042586e500180a07201d002d02c44a0b045240820104120030b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 475453462 1250 475452212 475452221
    0x23040206030a022a01230123061e04051206091b0310021c0605010215040b071709072d210803100321050403020405090109080304050607081b16111003 66
    0x1541025205c4843c00d0341c81070400e020b6428003403480508c000c21000e0240480d0326100c072401c420080c000038a01a81003044580c6030704d01d800c000b1010403002030104041c1c500442d000e20801030b0107001d0442410451966551130018804d41c0e080380300003854100349035406003c00d600e41701c141001590790b03444600030010007040e03241c41000c84914100c40072519510000d10a50203800084040e44942c8940d260700305c0034000104004200420020b01d04100d45000c25164060200c075030003408154202281c444114460307503803150680c4800e0303400b079200407420755800c0e0071940750485016a0445125403c1c08207001e050020302480400030070311100c02e03444c0ea08881220300401c10408807807034641480244100070070300c03600017490038001400549419801250006048000000d00500a03a164005a0421101996181c1000c42040100e03500010b00c02d81c8407500050342541c2c25200ca01d03021040c0900891158400c21030319030001045204142042c001500801c1d80d04243c55a01005020f0b0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 475454712 1250 475453462 475453481
    0x209040b04120c0203150a020c070909060b120303010b09010203090a1d010602030f04091e090f1502040b0409020304061d0313140a03120e1323040206030a022a01 71
    0x1908103400b180d44920a4a0400840d40d000f0082d18a0400c031501e512070100c0c025184d030b000c03a0360801040840f004100065001030028440c0880e04c032106003001c0c401c5420402030940150403411000c42d0000001c0212410740d0746410100e0b4035170401200403403440c007642004641207001e8860109409441502051401c403078015131002c0c03a83c0f55842203841f40901c0424950b07034101440207000560240c2c0040c062000c182c1d40c00c2a100400c12041c2d403d0b00e250200560307460302e01c0d944080c03d01030314111020b000c020700c01c0d00f503141900d8900c400d4050301c00d500c0b07650805540030020030100006a003241d080352078900781da140e5030420641015242e5000b0301102c00300c0b048000000074065143e541c84510031600909203500f9516603241c8862503254809503a00700140301801e00071560b00c0002d05041c0c83c290034400100e0741580f49400701c500600005524229100c4800c02c801a0346003004c50b54080007402c00941c5996900085988a200c080d40c00404503403612031100f020a41540710329440c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 475455962 1250 475454712 475454723
    0x1050c010b060d050f16020316030224070f0306050102060a0c050d1a0310050f01050d050f0718140405060a1d03070b0a060f060c0305070305091906080601020c0616020a030209040b04 80
    0x1707648800808151203a0440171040158100348080c036015500c00c9001c4803154003134015104540c070420030070b250b074010450206100302803020034008031341d038403286100c184941ca003001c002300d0b0308160001c0c0d50343c0c4000703089a6299440b1043c6050003440343c802d4134413281050380d042c0006991000700c0c0c504103072a240d015010b445100d00740340005805002e02030040e122058551000d90070031082c803030001c51841c400d60301446804400720301803900b08807040041200e2250310503035094240840050307902071104154019503c90a1101040d070106141c1d41000f04400300158071b910100104065030345402d10141140001b0030140e00b4040c85005407031090846a10400c40c1c40e480d0803405a0700c2c0b4090158000260581100b940081d0080300144800b5001c1e043c054101042c0c0ca00080c645455045030410543c40e0080410045400865050b0040801d0000c0c000100804001c140c0340e000f101544100c0c6402c0950a8003035454074480078010b1500a048681c3e14174150800c06000070003500d00310351 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 475457212 1250 475455962 475455991
    0xc020303210a06050d17070804080106081504050d0804021c0302061503011b050d02040905180f031c1806060f030c0e070c020105030a0605060d0603110f0f01050c010b060d05 76
    0x2c03a240d82c03040c01c065aa00400050354400781c0d445440b1050380035201d40705400303410070440c00883c280038042d0000701740d42800030a0301400d205402c0c1c1031a40101221009050110030300c4001080400d0004041185152500c6107907924000140c0b0400304a4030300051400381840c001c24164041f40c403a02c60041c080c101e00c40c0e00c1100040c03500b258401480c6081e000d4200c500c0c41c017072503c0f03000181510301c43c011000d400e00b0348868000084034000d5034081da40b119048c840109500083c003050420310076080145041c502100541c044018000c241448601e5583c0900015030508410b12110301c0d030031890403c0700e282c8440e400c1a00c0f99042c0820390b010103200500042c60708a1103040c900c034080741c0da00c09846000b15401510381c0d03040940100780c120385032900410300d610303041e029040454406002150709850360421402d00c0d80f1040042c0d000d4000142034100c5500c800e09024070203a028604940d65105d07500c00749004207440000c0c141c0c0b0100018200e0520320464000c1d074040d01c64200d03141d0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 475458462 1250 475457212 475457221
    0x1a16030b060c06072d0305061810120f0501020d0e0709020f070605040204090b0403020d03140f06090903160609120305070e040c0207330809060a0c0c02030321 70
    0x40a402031001d02d10440e400380c400110b24601c0707421a02002c410741c5540c040c111400400d031010f0010904116000650349a007005450b1a00010035480041c20f480c1050590034031680300d400d449014010707050500c0208001c4410011021050b800309070300030300219220280d04207049d0141614115010b903c0c07140c80303000b00c0d000b140740c4202e80240d0840d0541d140380961130b90312880070301402801039900590304c03020300c00410340000c21300344518401e5001e4030311000403a0000c1c0480740032091816034207020404100e0407021146507160411000ca490143c61760340c20001c1c07880c42c070031aa50509101d00d00314003001006003c0d002191440c0c41280203138621101c0000413412a88112095000038480ca202691241031540c4850500c662078815607a10035100c2203004982e110000c051421590300c44600035600280e1900d00165800501e0300d00031505181004031b80c0ca07036028140199840e03640010701c1c070841c02254440304070ec0c0d015042d03a0b160514060100340c15000342d004e4001040303441c800038 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 475459712 1250 475458462 475458469
    0xa090f06020a11010e0703380a060302030f0c0909070501090311040b030a110307090b030303040f0219030b09120301030201020322051005070b010e19020d060909150612030c0f1a16030b 81
    0x142300c0010324800310519400001d00050419001402030003025a80b0000400961410b21151910603500c200901d1420341400c14050003200081c5540220780100c2e4080c00130340e91083e10882140d41055401c3d00c401e9214001900800710700c41c407240d05126021505e410004216070320420400100c00f80c90300d641d51450220b094071018003d4541c10303001000090005808074240c0501c081c000f610707a200a000c1c0e8076451442e89802d400907519002c0c00b03030030420140410441880c4410445401908551555002030f42c2e9000f04030140d5404500c4056980c018648880070000a1100070700302003540148035002341c4694072503031040d1100141d800011400309143c0b80b0711030003140100e10301c10705550101404d2000350481c0c0220843d407501d58000107441d251500490f026103020781405603c441000d41020308072031303455101102045440354030030082a040200890001c4e00546101c41c108124a4940465100220110026800041446421660700c18a890452121b4400708000300c140000c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 475460962 1250 475459712 475459763
    0x130506210f070905010f02010e07171b010f110a050d030e0105070306030b010902070809090a0204061d0604172109121204062a0501090201080a090f06020a11010e0703 73
    0xa00020501e0b20008211340e500c1890080c0c0300043c14800003925601d550803a505003a019444480f024112040d8031503082002e020b800101d100200b0100040d07024800040e181c229011015018080d515424800c1e50005200b4000707096807103419102304041071840a0001c0501c070009803169071a10001038500350092140700c060700d40008406606030311b412001c1000e980011412617030b0510900c41041c7c984c4948881500482c41c005015845c1c40c02c1c000700070800703186001c0304503140018020040b416281c007001c5909981e02c01149681d00074100d813500d403900400c3c600d984110f04c3c0700200c290a103040c040c00f03050220421140710307100031031814013140c4d14681c80c0940d0641c4039042004004803405220b105100c16070341560203498005021100d00d41d02007110f0182c5069440f8102e10023150391200d5550350040c1d007080c042003468200c0d11042035a0507000c7d40201005e600044003014140203021482c0462044002030020700d0b0440621502c1c1c900521040b0746140300d02800c40d0104411440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 475462212 1250 475460962 475460971
    0x312090b1b030f0a020c03132405040e07180b030a1b050418091704270c050a1d1c0c0803120f060a151107080f03070206130506210f 58
    0x40f84816458440020009501c000503104a500c400c10010040c140341c01c440780001d1207821100784d68001981000100d41d55003c00110800108000074001c0508000f2500c0e0490107521703020035440703c51211410124071640003502a100c002c400c02140e949142c000004968840d40c10740e401c1e496184068440303008900981403c003076003018050b400c090542c40031513500d000382c4442030341d0700d0211000b034002e42c07241d00300c0d50340c805025240f007441c484603400e4414001d803200700400c040110a5401031071405009402c00402490102120000c4001d100d1948495401801d44049007107980c6000501d124004044800b0301c902e4600140fa5180403060740c0340307403180c1c400200c1d003952404410481c002c4024003640d070010255134003084041c50400c0c0c0120022141c1c41d0100700d10f070080181403030691300b5800812030341e200c440126080003012064401140c2d05490982d00c079a514125640b00ca1001d4110a401040100d004460302c022602ea14040d90800c80001113580c60301c031031218100d1030884 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 475463462 1250 475462212 475462231
    0x80d0c090801051501050d0b0a03200d120302030915090d030609060b030c07172106220c1b050c0112020702091303020a0218150402071109040312090b1b03 68
    0x500242e52940140d00800f6541007c0c480041c48003100c90005941703100076001039690695040c0070000da0366070307241d18a159200c100c8280c0400d01e4195540c1d50034002c02d603480820560003101103038078105c0801c14801c841c2c24090301c0145914002c1440c6a86c1c6810001d0400000d00b0004001680803840c441d078001c0e510707214461740c61a9121225500c040d400707001d00310f45140002000010720600c1c00007030008900f000822004401c445101d0fa040000045c0c01c2c81d11403004004000030703c1c4402c1d0340d542d102c9484a880030802b450700d0380065a80411900002c100003100e594400100040402e0300d80d03950a0076250841800007044109040740200740c1e00a4000e0504030214840750021220194020710038070485040b00400d07800302e0003041d03003a110700051550400030320020174102203891442e0030b0180d40860428040f5200c491018041c0d000003401307044030001003411b2511511819007504d82115007804428110724000505902c00c54100c00700c08a185414070182c000d0900f164011066035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 475464712 1250 475463462 475463491
    0x109080c011116170d02070b06100e030a02040e010908130f080a0c030f020a03020d1103010b060c060f06031903091e0602060402042c0a12030e071401020307080d0c09080105 76
    0x2955a1103504001104580b01d05806000c20034080716240000c19030288038230002041360506c039045c000400700b0815004140080100c041079261000105d01035030355012600070511f41c90111200c0c6c01803c40200180040900245884c140b40c042005002120b03100b50b03140b16201d40e11804c0039140da00284004101541c001401c0010402c01e403602c600383e0b4002807007101041d50304e50000754042c00d000781c04c40d54104103140c00c160038a02032041e18000c03403050b1101c2d4504001d890b2861748405d0018001e40100106102055090320204880e0051143c191622541d100e540e0401034141250f0307200d501e15a5101c24941c9a804244400e44000c46170107800800c0b05e62641d60030407014100030301282c00c1080580ca201070309240107244000541c1c000d5005000fa5800d1800d080341e0008240083d00241410599903024050000846500703d03511010b405009502440c0100d05612030070102410f1018003145100c15452141c0c0404061440c98540c4a106079072a60b00d9800d0394000c448a150308a01c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 475465962 1250 475464712 475464757
    0xc0c0602120d1a061602040509010b2101242d0603050703111c0b040b0603070c1401051017070602060c0703050f03070818010e0607050d0e0109080c0111 67
    0x42e801410702200b142c00f1401d1008060301c082002c80e0820360141d80c0b04c0c421301c401002941418490301c2e410140410082c0300c840d4803000410b4914a00703440326801c6504c5507107001040d0100b0342c08000c610490500c0c00101c90300602040701e15509070701543c4507143c00c01716041600c9940900001460307844030821035007603207000d030150010580148040c0070b15031500f244068100c100390081904120001c003c0b5500c0d82c840f0040c1c4103c62241044a01a030716000302a5466036860050301c0d407100c620300d0300c001142e00601d440c0200d0340c1e03d00114421036007000144101c141c21a143c03200ac1c0c0310040c00050107007801c40c041950f50241e9210300805a044100813602c410481d800070700301d149c0207080c0346160403900c4005c5106584100d03003c800041c44403040c02042c01540074001860307c0c0c1000244a403206903e0130ba500c0d01000750007001800000500080030b9502e540120507580c28070070013000865468182131220f40c0c085030a81d46594070789845003141c180c140b815a01c41e0103d810360000c45580e03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 475467212 1250 475465962 475465987
    0x403030807030c02160602030a090906030510150b030108010f14040b010311010903020d0c05090c1e07030c080c0f010e2802010507140d030b060301062705040c0c0c060212 75
    0x1c0344080d940450140c40340b007110251900034924006c140c00d81c001c0d40d6441201302c00421583d4203400c810021420940102f0221720000380c101e8403403202c0341001901070840c2c0c5007003040d94020b502648004a003c0700009030718006501c0540700f078000d9841404084101180d409410804407402480380103220018001b28103000100c078801303c018140800010f440e80c00041843c0c40c12881103076000c94188050210341490880e01c0d420401190a403410020451190060341d0708107541d60041031408646081414800c10101c86004c0c1c008010940c0d50001d10f2480381c0b01c80c040c22404590b5030174220610170720500010041000182400c0c84446454412001031840074003541c2070341088014010741010682d00c000c248035a0800348018131400714040b101a080e5200c3c41c050502c10401880100900c98100c103410b0b9407800c501580c3c84c40714105480300110440640c000300c1d00306203090f000010680d01b104500141e2401803074980c001a9440300100d03a00d060500b80c601c24501d062000c92400b06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 475468462 1250 475467212 475467221
    0x4090f0b0a060519080c0901030c060305250e0301060f14010e0409050f07061b030905040902040905030406020d080c0301120f0c03291f05010c08040e010e0105030d05040303080703 79
    0xc01003008202c150342c410001d050240c92a15000038107001e035100700948441000201215402680c55041961454842c1c032402035061103040107054840740050010000e1308242c6159182c0040c0102080340d5014000704442001c0000c103001c0e42c680301011a012541840a40486a00c02030342030f461032800004440c1070100708150390b0001d880300d902c140041d1083c0028504c44000400034112540b5010005203040b150322801d0341406080941b01c0c000c640e05c4180f82d07041e181c1c1940c0c003184950f410300c0424000d081c50b80015000b40004640071580d540c1c040b940004006040c1d8840d1803d4951004061203480284203000c01c1c1c83d445800280040c5510b1203407200140a40a140655a540d81300c1043c0108900e041c02582c0c2a050315078501400300c0c030a050b400085200e120f803007826003180a41000c0c0c040340200e5050040180d008820044c16904a4001d003074601d01c100345659542c0c1c1b80e110300400a00480c3c0c40381c010107074a900b005100c0c1d02a01c0449802d40d0768003029450740304c0d0540040 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 475469712 1250 475468462 475468471
    0xf0c0a051201090602030f0f15061207020a0b1906050a050901120c030501020d14070f020606010e0d1a0403030e0a0b150607050328090501021c02010b09010f060e04090f0b 75
    0x103540340e180b0707400421060b10245200300c1079140747e2511490a00b601000a16000780b50006210981c1e032502c051751195016100c16105010464031107490b4040240d15112201000910310039000c01000503280003100d04420b24000c2241c01c0c0301c0b4a07100c90410480501da401941e4010310420010000610100c0190304082c0c02410b050f4440360b100e03101c0d81d00ba40e0001441c50398a907101c12000c400b0107490307507199500501c1c0c1d1034900201d900c107000c02520f5000c0506207604001004801414603610740006007003080d1300084900400c010f48803035000b0044111000c0d00170a1911034100004400468180e40c210ba01907200180e940c0c403500b04070300b9404c0005105130051018004240010400c00040c0310807002e0a88456502e243e40380c0c8030600c4040d41181d42d0402c070409000304440d0740c00044c0d4196200300403040c07440000e0440e0301240140540720300c00e5444030002000080600310300000c04140d0304c4690300c80c03807500d1001d0144000e07910000d00042c002c1d04102d00c8480407843c0050200e800 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 475470962 1250 475469712 475469749
    0x301150305060a1a0d0305070c060e090f0a0e0f010519060612110706060902090a14010e0d020609040606050c010c05090f0f040f060605130f0b091c0f0f050f0c0a05 72
    0x804c2da4110104008a050100c101c010550014200b800c1c0140094144010500d9150070040001c5030f40115170400070151046114040c3c00e00400c480400f81d412284002d0752101c00c68060140d1207881502034034040d141440e050782c7d80e824101070140c0500030740c000d6568075103492100214051881c00141107980121015030010302030f140000309039010781002050020381c0940c49049250030400b0212407548214000e640902d512030450340c10a2070480c0e1070300201d406e5540a5242c3c0041441885110450b03035000e494800b000c504035800c100074100c42d14200c2c0007040303040c00c0b2a03401c0e0b4842c0324030441703d039100d4403100b030080442c80c1a88050180c0d40000e0030204240c1000c41d4400103580d52500b181021540101d91421500a98540180149202c1480055403890001300701130510450341e9044c050014224540010992030b0101d09101e94440e040005112031030411000000f400007088803203004410070a8051400020318500500c1e004000b4210145441c0801100f900c0b0b13140e10402 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 475472212 1250 475470962 475471001
    0x503040e01090606121a06090a090f060608130c0b070303021e04051005071709030f0f01021309050f0105040f06050402130f05063105041a0301150305060a 68
    0x180300411040c298000c0403101008507125041c20800352601185007600303507800349450b515110072400c01c00e14404248082d0750310790f03407081c5000c0403c21700600d40e040820407908022440307014010707aa02c554110317016562088000d0f2160b07081480d008088500180c04010120802d0102600001c020141d40d40700381401880d2100150355801e10300304500c0d082018070400310b0100020305201e102f90640c89806e1400728030b0007611799079450a10700c0c0881c5140324560085840c11464038104607194104034400100c2b0703410b4001c060545c0c040d50040c0807200225000e640d00140300d0301d2034001d9a0081c0f00040d2540c1860782000c0c1884000c10390b50440b03803050ba8a0700301c001290b84580c0300408404e01e82d485940404c500b0842050140695903002500800081040c0b40650071458940c00c809031680b000ca92240340c180400d02d044107411341049600601e0308500107a51a8041200d408590702903000307100700c1100401d01c800380421480003400c0340e042180000c2010300b44d540045103080c0b80210000 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 475473462 1250 475472212 475472219
    0x4231b0304050c102d14070b010b0313052a0d0308060d020f041104090c090f0611010603060204120c050301050c0a11010e0d080417031509041716110609031504050304 73
    0x248050080c4a0050075503010105440e40f446d844100c0e0150500e201c1051807900b2050390301e0301082a01403042c0031440d070001c40441c1c012003400302c00d83c00302ca0b046800c030f41508200390b003801e01e0075072481d404683c2e52400c01c1c000f60841c10802c0d030310080c1c51b8158070f5000060b0340c0e0700d041c40f180a0142204a1303100c0d0b901d2031041e00c20b0741d81e40314000c000c0e1300c0403d41030b440d03500341052502101c22820403282807000d2402d003003000800540a01c429646a0f14042406031040907200d03000d00811f40009201600100b404078000c03d01c081c81540c00da02501101e451103035144103141c200c0b034090703139003c41c0d080c2c08003c0c032002c442c0907028000007031000380000202080b035036002d28282817210900f1400104003605010034004c44441c4400100b980d40e200030324601b41a0b00701b4140301112003a403809244c1980019051043c07103000b00c00d01804000b80c0c1560351200c04a407101074164840c013100c81e126019200c2e0004d0400400399621900d000d8002c1c840011b00541d108000003000b00100c0751848201f00c0031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 475474712 1250 475473462 475473497
    0x1603020105090f091603051e010303050f3a0c0e2209080310080c0f100e030d050c120301030804030b09071203030213080d09060e04231b0304050c10 65
    0x5d100e00c0f040480520038440b12800103064440c080d100021842425050301c80149000810504481e418108699507043c0701e02c1c05122409041c13422002e6050250628080da880154007451080380d004a40c400d102c000f0301d00f08100c840140c682400204401c10702d01da2410021440c81c50078001030403024074a40e603100c00c03400341e842d5440100e503440e4010041c0702c02000040764500103444808060842041484046055070401c031091320702c5100e1054000c0703611401540030781501c50020301134a440901c0d150300504590b1108605403524828114942e405280e0303402501d05903503100115501d01851526003104616001d23110300d46a000748840010074802c04c0c10355940d600d1003074030b0142c1c81d8844011440035080b500c2d880300380180c001140000889074000390325002d4607400e09102c0305020020703000c039004001e42d04685d1000740c4a0160282d0884c94070a4003845409000c103c05035940413440c00b07950a0006840041032903102c51454480d92408860140e0305c0d006516100e01a081c407040c51 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 475475962 1250 475474712 475474729
    0x21330308030c0a230f070303090b070e0307080d0c060905120d050105090708070c14070b040608010e09070503191a010b0304031202090d02012003070302030d0c021603020105090f 78
    0x20454903a0300003c12014958000c106850080c0245203180d05800d82143c525010b80b01c1d003030b1038a00042000510408241c0250b11504440b9040450784e446460207910107028002ea0340c8440780700341b080140009042d000018031143c0c0b01d00940e99001c00a0780c55403800c014000c91581210280112484070306a84e103001d010340010402c038400402d403545000d007441210707600900003008008a840420003402c1d0880895400c080d407207562051059001d22032a404c020558001c00e036624400240003459a61140485041c0d50070f145411901342c5074840100d54545140c45200c1c0c250f007010480b04a03000402050380c8156004800031406e03404000c82e41110180241c00410743c0180c04002c4c4018540e0003002c103014840c1200003140740690100006004401112009041150508003028020700c89820030343c0403103852301203949071007540c5806516600300d8102608018a841c1e420100355200080a039036800c00c004052020b03605503001140e66a01c4410240d800441e104401c0c4403030303280e1440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 475477212 1250 475475962 475475971
    0x30e0406030b090604060b0a030209062404080307060f0516120b040c050c16050f100903020301050f010611060103031e260a06050f0307090e0f0d2133030803 69
    0x140c5843d14080c6003080c2261020b47d485402400800b601f0b100603100d88605541081d001c488080b292007074000500300d10300b0500e103190b09607040030400050000f00000a01851446417006103d49070007580440c04642007221030030b8250300910a1400000d01411420b080281100400301e00f901180b004141500c2c00f0118078000600b0000b02c080a0701000d10100c000080001c80c154455480c0800003042c0781e0044442c1da1080740390701c400a40d02c900800203040290b9000c0c0080c0680c6c6020b00711030b180d030b2000744107450126a1005c11b0b048001d9000c101d89050700d81c10340355072145100d511303226007011181a80400c28800d4100072a804800100e2442a140031010750416040c5050301d056810f0390b0307041c0e2081340100071801c000794640c1d90100d2800191009554002088896010a145080c44a15203030841e80507010f15038100ca6440a54110800e00002040d400d81000400c210300721507202604c00c0c4540c0c05113908001840d80000320360041055150729802090301c98503035070401d40c010399 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 475478462 1250 475477212 475477231
    0x902120a05070f0603140106030b12010f0504020f030303042a05090a0606230f0327030c071401021e0c0301150f060e010903080a0507080d0b03010522030e0406030b 72
    0x4404103c0c410b40204203c01030921880c0500410310b0350b2400948000060140f1030605440f0f040040407922204460010302002c103000380300d40364407207901c480280019201a405009010921403150600204503405182e003d031500e91030703019000b590441d6141050403200c08a054040c00070b030594488a4450107580865000507089141c14005030030a000103491100540c460f50b1800e003e0010758050392288402145181c1d41c0e036881629825800320001e0782d092601c208042d0140b000000000905022140ca00c12500100c0d20360090368007660911140d40c0c0168081a071003102410701107040d050701d102c00c00c01c071103925410400290a40b00c0091248440d80c200d0402040230b5048902004010302007800c1194240f403620b00020a608802d000c040d000010000d580650300b4882c0e411205095000f6842c075440c2d150046494014240c5100301c64887e41c24000420052400112801006034100349446110f4009540c10350380082451003880d4025540d12001021910800e0503a07c1a0300d1230 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 475479712 1250 475478462 475478473
    0x30f080a030c03051003080708040801110a11072105012c1203091c0c0501110c060f0c090409060b03010f090c12030f05181002030318060411040902120a05 68
    0x5100804480c11811010308150a02003801a082e02c51692841501d0f0415800ca03500c000303d0500c009c0c140b01d164031141c46980b03842804001c0caa10200a800040b9070f5a42d05c4291090860940742d80782402d001d04038082036484a4100207144000c0c0c0d070706100c0c1c42817002242002d8280c220300e0f20040f09041107000854201148451100e0a01540b40050500f4a046046051210700c09942d41a0807500840d00d0f07606c001407000c0c56005009000038560701074020f00500001c0d14803e050340d00460003900311442907002082c00348032010381841c8030381134148446040203044401c01000c0d2802000030390b00744c1d503504c1c00d903c02d40d20f0a0055501c103502001000c15205064a051030381d40c0145d501c01341e41112a0014440003c1c0d01c0402403080c1d482c146011915a00da0614181d40000c0030050158824141000b0ba15265004006140303e00c10b40b50035910408203200c801902c80c0e10072640209a24458403041d409484c0c15405604194005004101819005640e5a01d410182001a241170303106 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 475480962 1250 475479712 475479727
    0x9010603060f080601030b06010c1a04082715130e0a09031e022505031c09140306061003021312151407110127051204060503040f0c030f08 61
    0x2103102d4001042540001c10140d850760b11040401e80780642018104800000c85200b40800e0094a10640261155222039820680781c8682c40d030380041d210304035150f02d60800ca42050100100720f284840e000e480b90b0f441d5040c0c400400c0c1560720181050440201d4201c010405460f840b1309184540f107000320015405900c0d00780900b06030301c20004903d40140c081c251400c0c480e40440c1c0011814440189070b44a07083d19561000417100542080d50141715418106000e500300c950890b0028021791290b14605444a424200300c000040704650143d01407402305503c1c4c1041010b01940001c9460010304200002d0f0300d142c61301d145640104203001d0380c3d540c10f005021200030003030b00c04040220200301c40f5581002c00818618000e01d9001440440c0e44003100345102900241881065080640550881c103261040103410500301620203200750307031311107490350802030486058451a44403641103135035680d141c104a111844040f074132003d624400100003416210081c040034445c5041c00d40b2400c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 475482212 1250 475480962 475480979
    0x9010f06081b060f07060b0303191d0102030301060c0b090a0203070602030a030b0a050a05010305091e210403080909090307050604031d180a0c02030c07060c2f041a0901060306 77
    0x1120404548220400c003c0c080d4a808440300319171380c40f54400004107003100b091000908501032000a15044030b481c103c0440e9150f400301d02c240c0555221340d130002c0c6d160016070049aa0340024005e0340085079161900d0340101e140c00c2a050303802621030080b140500c0d2958042820031403030750700c00d001507400810039004030f03074050250484aa106684030074030380d0b1405c40042c40c518000d01c540c6050540c1c6901081884409102d480c00740b82c45070010310b4216642042117a5075642c90301c2100d049070783da44113048095080100b00c2d03003160f412a82050426514000f0411b915070050120149440104400400075070140000d034030035406510b07a0728041151200340441410015400781c4600300203142510b805c4000c2c81712980091800200003041c1160050603842c43c803801610810074070800310300007100340d44411104007241c481d0030b02c01c01c5003680c002200341405030220600300d04074180c44440c03100e0500d60b0141240c1d00c2100d013048000c1c510000031a1a03a032084e004000080e468907c01e01c401360 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 475483462 1250 475482212 475482253
    0x16050f16080a110904080d090b16030b030d03050c12041b090b01020d1d06280f0c300801061e09090b0a050901090b01030501060903150509010f0608 65
    0x2601001030841d0760000d54a00d90f20800585032940314080000100b02030092400540382e440a82131000c000f03c04140c1403801d001d140841e1140035081100301f114220034400d008560000f0406002054803001940b0190b0207050010003140c10b082042c003410359103141e04000607010300d000700640707200d54203400008404040d80382c0060700300508000c0340540b6030341e000511120409007858006203400302c44505401401308801032960052003c84c0d9510810f6107211280c42a2422151507a015000f018007625618072580d110f00200d0300301901d078070118000c0c5c030040c45081d40d510441e11902c403204881030988800306200c1800034038500e0040c002d06030015040190340344081e94021256020400091404000c0c4c028a030060381c6801481d049030322402070341c801400b001050408207685882034040208a6214050b000908150000612130301507040c0400750390f00080980d40d407111112154019182c06044c420003036680d0003e04401200c548a4207026001d2170001e00f01c00d450281c4001c02c483e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 475484712 1250 475483462 475483469
    0x16060b0607030c06050603030f0705010b03190c0b09132307051e070c050909030a27060f090e07020d09141c05190c21110616050f16 58
    0x1000c0c200590404240c01c01c08601074541e0200c004150b5a0301c0030042801d501441f01d5800503d2404034880c0d0800406402c0104801407d038200c548608108000903401d01400e007000e0491042c0b40024000b401c0081c004218100024001c1c010540030000c90740b0895080c00301d00000400d2460720540e05610340303000650441001e2030640e00f4074580c0140c1d40103004203100c41c29071151001500c0e4080040203e02d2a00401005044241c580313000d04140340c90b035000c032402000040300074400d40e000c02c170141d001101c110051000170003c60b00344041510201700d0b803c00042845106071000802c52104012188a803500390301804000780024000340880460f41c10046180d0313880c03804442942c079656140304c05802e059100e100f00204030708080d8203110003800ca40000780820440001030004224210303048620740c001440c2114400b00a0942d00d2880090007410112500b440d06910301d0300c00041d00b1030740c4002d00300034960715040e41ca80b45014090360071111386800030440100c0304418040220b004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 475485962 1250 475484712 475484719
    0x30105101701050d0203120d02090112060b0a1d0301060602010209120303012904080d020c120105060a0b0c0111030a150807082e0905071e0b031b0f16060b 68
    0x7944046144000d1000303050203524000c00c0541e4804081d903070100030081c4420a441c41050f9502080e2802c08007079030141b03000034082040041c5001488070b00344104800c80303c0e82c0c0201070030310308407940456010009148401840c01210406d10840da02071143d81c00a2072540c00050795500c1c03140c00d20001e1440e9511150306508244010050a4038101006d0502d200018604000c003181850b00d03051806141c0040940e0721841080460450f00003542c1d42c0c40480446103102c2c0441154440d60a03110300300c0307416812605100e000c114034440d0f40c0183c00b69441e940000b18007040c500c2c64a20f0140c0086482c0e881071503d4a170303860280c07201e0108103005042d0800142100c00c0c14119007030381e120f2424240c400c2340c0c098540c85807510003c0d01003191000034008400d010521960800c26a0b94061b80501403010f4403080e0719000b00d18100d62a00d0840f034103484140e0942c0c0d201003d5052406030341c441d0428400c3d00b081800d20305000b0390700400c01000002a00c507074501190910504032915900f14500 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 475487212 1250 475485962 475485977
    0x106080a14010b0a020a0803010f060206060909190206192307050303070e01030b0a0305030a021506010f11010e0304170709140a0914061e0c031e04031701030803010510 74
    0x1c0098100001c1c1914090004180c2d41d082c1d03000220700d09011803001038201c04000c00040303013141c0d0300e900000c12126244c4c00c44078161620700400007250816a0130704495408002c4d002800001600d081d5030301d50000b00341605046802070707044d00c0b031035503406180300044802812403251480104030140350680b40c1c8038182050361031742d681e5949200140104d0188a01060442d809a00c207822000c00c0c440081d040ca42d58559034a450380d030b01d400811010015000c1e00c1d00005007039103035440a5218407016521303000308002c004010380c0d141c0b40c0364410344030554985054078040d60003003008000400b03508101402c1d801c168010f06080240742d0b00030001450410079141141c00c0a888140c0c0c000b401500c00151440292030310818201300780b0b800080c01c1c060002000014400030490b001c50b211100110703000c941e18aa5030589611040300c0310b9514400d8414241c0c055050b200c00154898172a080c6205d400540e80c011404080099004030344e0319000000504c121304041c55074100c0c0100a091006 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 475488462 1250 475487212 475487231
    0x1b0105040b0f04090609020c0d111f020c0105010e16030501150809010e060403050c0106050f031002130807030503090a050d0312020d021b070602060c04150807050f120106080a 77
    0x810900c00d52064a81d0400c020644001c0500541c084600030305013001c00b009019955040540650484d045080040c058511424100b074000c582c0100d641c5081c101909184010040c801050300200c00d1450859509000c40c031407400c424800d080c0a4240b42c07101e0510351802d40d5a54148415124404080506000041141c00b001c10262210346e5200d0402100e5075880740013243c01810a0741003c4400d00c00c0c0018001031540000003804002c2301240280081d980350828800c0040d1101911a0076070300205d075180000d41541d0181140c5e5000c183c03c0c02c0c00907a100411460401c1a420582d12030308005811465031401080c01c20050000382d6410301c2840c01a18060000c0303044142003556a43c0010b030000c050001c90b0304894100c0f841000b410210140c407440550303074440364062107025214940100306880445026241207813011000d06d0000440c1000480d0242c801800f08000e002050150020b000003000241c19610300e144003d00d103540c582240100320000241c652031995191000c0c45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 475489712 1250 475488462 475488467
    0xf110a060203192105060108060307030203070b030406091a01060924201912170c0c07120f1b0b04060806060d0e060405060108030a050a0813050319021b01 68
    0x850300c032203c0d418802900c0c01c0c2c80703c2c240c1d00303522a00d44521401c003004001807074500041d48100c1c0590301c280d9400404d07a5401c1c050640d1100e0070300000c1e52503408420304100c15100b1000440e400743c800e002c040b8407440b40b41c0d58911000040c03041d0603822001c14005106643d80541d40b0402004025a9614200e51816003201000988074024081017800c1c011641e050a0300100e0606070700e051800c82d038031b8a45001c0324110b4600c05180c00c55003801142021031a2907c112803002c22412091030b91002903d0305251820302d540036000c2c0c0205801009000a484065891908041805002000000013181c600404951141410380e221010081070600c0300a0a200647e426182c0c1da040103030490b2541d20002c1c10b50b0123156422040c440c00d1210181d48101c0104000e0b0090b0f210314212000d50b620b4041c41512401041c2c0303e0f400242080c00113248191007840600c0d0000b9607444896140031054031032509582c040399403035555440100c2c2c40006c8503030408c102402d40060b210b5028140c1c8008000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 475490962 1250 475489712 475489717
    0x90f01050903033c010b041a52050d090308040923091e03070818010e12010c020c0f06310306051506030603072c040f110a060203 57
    0x80c00110444805600078140b540c04401561000c2d2610092132581e481c036001200d507010780a154180c1180001c0d0110450903130050300d505404082c03900440081c0c03c085801e4801c1380c4103d5014101e50280710f620400c001c00c00c80c0940c80c0352021100280005414020310340f004d01c04107001049003c502c1000803400301c5050320250b4400c4c482c003042121400c25a5412070417032040040d80140b4041c00d12500b40b400040c81005850040c2180d80520448001c9036124002e000c0007401072182003048401c40c01280c486440f0720441410450008054640415480001521102034aa54420101d018283c0400000d05800d40c01c542c1545052840c60100c0e04074010008142c034800b840f880b07403001c12007010544224413a200380344c50904544e2400c01e02c0c05818240d5000d102580c0710b00e9400c01c54100101103078480c28024006200f05031816501605002c0300300000b01da50303010710100600b004141d0005600950180010003102e01c6d09040c481c2c0c000c1c80680c02d81d8032403080c1e40010418a50084117 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 475492212 1250 475490962 475491001
    0x306110c0c0f0409050f0601030c060807090302010c0f0f06050f100308070212070b1315030b061207120908030618060a03110f090a05070e0f0a1a0c0303090f0105090303 74
    0x98210080d0b0348200403c015200500d001042405040c403c609201d00c00a10035040700c1c041c0041e40303222135642405951404c415511040010041442400036500450208000d0f0748034103082104050292505c0c241c1402c0c51317004540e030a803907409104000718440d802ea60003690019015140500e940d46209080c42066002801140c000c0480104010b0503c6000d00600c144225165644450342c482c2d488078905010341001e14103c40140030710140b091040b90701d0701501402541c98038017400b2002054060080211040021030bd0a5428100c034074002c00c0c100f24800e10010b034513800c2c10f0b8204069840281d030344030341c281d8001c0d007000107540c2c401e00280c04803900074003040071040b40700d00450310024901415981001d07800043c8030fa8030013541e010901c900c80560314110340c0a07040c410000c0c0200c50720041a80500100000d201b107400c000130040c47c00d40007901140c13074403689550b001d0941e08211500a0b940d0000385103e2800c44c0b0a009255129806802642c40c1d882c1008811030740054425 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 475493462 1250 475492212 475492219
    0x1020705010c0516030b040c1e060c050c04020c030904050f061c050307061a0f0a150509040e0a031106070804080a1103070203070906140108010b030a05250503010306110c0c 76
    0x40c0710100f030100c188141c41800c804d02d4001520692241850140e0030001d44044030034190384100000d100740e03088598a9554200001c81511310f28111045034004002d4400784c406004801c0d90605581d02c501c005c00104010b500030b1078403020356a0401003200c2c0020300500c60002c1c94410002c09a444080c1d09015002c44014007820380d806060080c554064a20700030170315460304d400700022400e00010034801c04411910f10031030f40408020320999100c00d1180b668a030760901c1c00581a05d00600207021461805000064441c9030703d8041817501e44030b90025000701c1c4240d01d1320085582c09100007503008100d4141a501d50901d50354000c250b01c504168401001114100e45048374014012980956001070031101d03599140e400c0880144058451003d603041d00c050f42030155400340103901e0485801c50768060035644c23628500c4c00030f132600400c0004110340103082c40004541800100100044c1569503544075030441c9070127000c484405d211500503600034850310121210000380f0300308031102034 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 475494712 1250 475493462 475493477
    0x4060914010b0703050c03070803180d080402040c140f070c050303191d090f0f070e01200c060c0303190b060a03150b0f1e160f1a0a0f0e0c0102070501 66
    0x703040448240c0500c0308201c6d0280000030b0000c06005080000d58010400c120428a01c0303040440c440d55214030352120480801c84c501c0000d0007510740755008511007141810002201048454095000c0d8030680a00031140750200760302041c02010307002600a01001c0c0c1c021450000900c070500c070f8840d0380302403090070032105030304840d00441b803010a00c0071b0102c0a802003605042c66808040f0144003104c1c0c2044a14440c400104c401d0301c80e000b01111130106031140d002c203d5204d40505200144120240050301c40c20740e07460724548505e4010080040d210001d0f54503400c0a20740c2d60004d410f10301c4001142820308121041c1c0c0c0d6076a20407030308200c542e070a0016560701001511003d6a88562003841180c5011400480e1a40440300810b07020856004a404442c088150254540140c3d03820b5000e10146054550028441d00704880107140154404050340b0711404407881c0a100446072441e0954581403044100707a8a8081c00342c803000c01d64090300c00c888600c0c00003035860140e8829981000b152 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 475495962 1250 475494712 475494727
    0x1e010b013f05130539030715080103140d050f13030c0605090a0e040512031806041110020601061e1112030402150f0904020906161104060914010b 64
    0x294400d8a0441111031000d01c60b626080c003100300c110011000c142c2c4c1d180541d1440454003540c009202c0068600720303e00300011440c40883c0780801079400c4215805210320344000c45ca5103000d2004c002c0341d02d003d070380d000c2c0700798114a081d00c1100140c038040e001e00d501c00010140425007140564640b00000440300b03495021110319401c00e00b00a9201070520a0241e9001c64443c0d4044001e201c070010030b447d040c0001c0c1c0d90304040c0265400c1203401400507004282c0c1c441d0002d45c90001180c1100c1c0200c403505103e928001d805003080c3d002c0e0b0307049959004c0d402c108195030800031800c031086032090001e4500c43d0b1408a01403c0e5201c1d9040340c0e50a40750305402070b41480e02461440307610000c8001114a070342d0760200c000c0055401550f06a101d030000c003500c1059040d014049554000d2150811f9040c2800802482b0207500001c0c8070641c004c10902c20300c0b0071501c036980c581c00000d02424a0003013411440050208540c0c8035007120200c18108140250920340020015044490000096545001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 475497212 1250 475495962 475496057
    0xf0b03090316020f0a170f0604150b24040611030c0a0b0601111f0b06070f02060a1b0507181a0f0a1523040303020d03050603030c1e010b01 61
    0xc100444c40d0b0000d0031a40c046034105149001482040040f8111071031540b640e00915601d60045034006c2101c0029216444a0348498128900c800c0d0003828411110500080164481d01c1d01a6600245203000c10100301455001c0c3d44501800068009940382c0060481c3d0140c0303d40c440c809c054100315400d40400c030503034401e8a408260100303020640e00160100248001c0b919400c8122108070b81c1000c000c00c4091070030301c0c11aa82d03940d002d0441e0301801300984c240111030300f01480060901c031034444180340040f41110000305640c0314a000d003002608110b54030720912541c0c40c42d030031158640380d600c0c06030803101000112402c000321407401f09a2404800102c1c0d0458a402019281000040d014283c60300010160301c02c1d0841e23448030360340c8510a20030301510302075840007800581c80108080c2909009038841500084e0181c1074a24241a0341c12040c50320100290507000650344128501628500384150010540e09281030310981401d881d0b0101a55003040586c00031b42c40341d001c0011f40c0d12 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 475498462 1250 475497212 475497229
    0x905061c2307051905010906030f15030f02031005130201030203040227101a04090b030c03030a0215060d0c03030f230a0f02060f070c05070503060a02040f0b0309031602 74
    0x441c8003001c81000e44022269200c1c4100c1c41100e0259101001d489403005040c003820f01516410f07581e4009251600e2421009007410454091809076500d58581c0709400e0580141c000e50b0180c10a54001501c6105252410f0351100d4544881d514103420321104401d101107090203950246000343c2c99450f51b00010b8006036000c1c01c401e0890248a9001e681070401d6500c0910138031480c451019016503038496034581c0e040301341c6c0d00b0761040d20401041c020035a00381d029102d160000340072114620810340202e4a1503204000000160744142c61041c04601c02460403a07100b24151032407a090384660fa10304000180c0790200409100920301c035410a103100f1001c800101138154003c0250080043d48440943e020b9480d131400903250103401c002d41070000480c01c0c004c020305402d45100f5030710080c044403450580c540807601402507480c0042d0303d59040280d10301842c0d10000050355030307240a05c0c0001d03d0060364002651060300380200f01c25800c012007070324005820007070f04294030703149031001901c0303036 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 475499712 1250 475498462 475498493
    0x304141801030f020306070e0a0905190f0609060501021c03020a1101020f090108150a030803180708060901140103050d0311120708070210140c130e0c0705070905061c 73
    0x801034000008180800005403607a0540241d058460b2030b211500116050921b80201c0c540002c500c042c200401c1505a00c03295020002c0640d50f8508100e181d41881a04c035002c1c41d48800903114881480800400d22503440141000d00041c059a69503211980480e0009000501410382c0030440d04142406075246c4041070100c10001c560311100107000303921907002840c2d500c0c001071100300080d10b040103a140707030031000c0002811030090300e1450382c81c0803540d88002e000c0c0400f44208402c036001d101c01000301101620b4110080d00c29842c007000c1e020b003110210102d0203050420100108042500415528290394441c0740c0401c48000c2ca0458001ca44551aa14508040f40d0380c200704e00107900c0704056024102a60a50703a101200d0745004040e40c40e00701c0400070003e0400041041c04060800801c01017102d0301d0b1303806003541d07112000c8090314000c46080e04100d40020f00c0300700b0007005010720409170075101000c001da0b00b004e8000ca121180ca02c1682404155192410010302c0440310010104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 475500962 1250 475499712 475499749
    0x6180309060a120b04020309060f060102190f11060f0f0c070324050a06051809010f090506070f09120602160507090605040605030c06160f17072102030414 68
    0x2c50440c09001499016201c0440342858686407103c011440d007130080301d000d1154407000340619280d4140c0c1c2d64003042c000e085103040d0310512004e1103002c004410200d89076402240d02241900417401c0c00384841e00c114440ca032141c401080150b89103121081075400c1c4e4031280504c1606c40e032100c07004c5480c042054001400c81500c145000c4440c81011380700c51403110316040c2c24446074442004190950751540212a48101c407914003e04016410200a5000c507100d8008101c50101d04040b00c1100d680c84010713103040c1c01800400102c144c210100400c905800e1404440786407400c004480306c0704511b2002810f50342c0000b85451115816090300c00c409401905a0340640c2d580c10000e4014840bd06ca501c0c0100d0404100260328030300400c1608074018081d100c14034000c03402d65850001c5086100465044499044860218010b15071003440442c08004050b911800c600301a54007203410346030030088001403124401c03242d501006450481e64090500c05250a10100041c0340740c1044480001707 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 475502212 1250 475500962 475500967
    0x1205030415111b270c0a05070206030403020304240801060813060c090501020106051c020d15020706050601110f10020a02031b01020a0305070516120903150903110a050618030906 78
    0x21100b404a030100d40f180c1c000c56a00f0444e07202540c01414203189080c0d050022812500010102203625005281032082d030b140140c030703280050740040c0164105450690044c0c0c4081801e000040c08102040511701c04294182d02803001a0390080c8003c00502603481080030300000700d000c0da107045948031003840e840001842034034000c0c0d400511507202c1d4400c0900540c200034002519040242c4500c2980001062031440d005142d02848005500680111800c00c00c1213854004a8000e00c0a0a012889064040780c103080a00006140001201c0d640700180c0040c0c0015003000c03000600c000041103000e202586451020b0350030303820350280d8240050700d5003841e4082d2071b1180041d07000304400900c64604002e1074a82010440e2a4092144c80300240034080c102c100101c5c507407039080d079010b649501d0032440c842c2d140d5803140c0c100c1d0512802d07200b40ca9210006501010b41100d1400c003000c1c04030f401801d021440e900c8403941c403680035140040c004820806424070044c203004490003074002500080c2d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 475503462 1250 475502212 475502233
    0x10f0b070f02120d11060112050705121609020304021302040806280c0804020310022b021611090609090a020103050a090b0106090807140d030503130624120503041511 73
    0x317041c801c515464030540e000c1c40001040361a00310178030b2515503800c00000d00d011402c083c01c2c0100b0001c200c0810a4a210b610903400c0d14403288144440500210354016803030381401d00c180f00e00d01002c0d003103100c04140113000510901d900040c54a82c4080390341ca0482c450520300e1050350040520f900d0b411041810321004c4560702e078002c07030740a00440c400d038100d61109121230200e030220b000b0f810780d020046100071810003a5040d0342100220140c208180140b800c0300f1121900d082031108070044681100900d040c0c4258a0481c202035801392084e9a41d0105144c19443e1b04d0700d40c2c070b0101d402414541e560010445e0b81c102c039800b5090a6502012000f1075584416019010080a02c90341985128240e4007290862040d107001701004000381110301d0300d02d4a940c003500c03143c200038104041550946d0310f800202c0ca41d0300440d80100c00c0700200d00013005c45407000f0900c401e182d800400610410035100b50000740000101c07800c807011a40142100c942000301107074410071003902d00352030340705014410 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 475504712 1250 475503462 475503467
    0x4120c150e060903091008100f060c060e01060e0130030c0507080a0b01150201150b04061215050d170309010501060306050904020306150301020c0a080909010f0b070f02120d 76
    0x99041041202202e2281d41c948240c0c5541c0e00c5821003081d0441003110803900c415014501c01c6401460303c01c244900c00761541c08a00c1c1e03403242948100d0001f842c1b82e6507130051000c18803460003801c60740c034000d1207600e0400c03e500c14004010310501c1144030000300700b49241082e200e514050b416000901c0c0d4030703001032030038000e0419016483c10394090288030710000b036800001990310b10030307a40415000c03004d078602250a00c110300b80302c10344001d554070f91034807035407104821210740090a011704800f61901c0c103000004041d50480c0499042c120725020102d610800941841d03001c03a0b10132a0b003400740c05203a01d41391805210340400e00c00c07601004410b2201c02d400640090341620303201d40d0100440760f030300d1007000788840040d01c0281d0150050070110300c0c0700d81080950702c0d071424003800140c90040700001c2140fa09809680540302c0720000300b200049403074100d92190040ca40791140306042d9091038042e00c0305208002000340340f1100400481d00310740310310500741c658040020990f090400b01d807030301 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 475505962 1250 475504712 475504721
    0x60102030909100e18060c07060902040c0f080702010204050109140f060d06150c0201052a0703030c05010c05091e0409140c01091502030703030b060f0c0f010e0a03050304120c15 78
    0x10200700d504c0d46070000d12141300c80310858001600c0c000c001e000d2512070703030b0607240c995010500071703030300180c8502d00f00380962036600400903003038601d58070407690b040074200013802e018019000320116401040208040d030b03071000310341d42684c80c101d0a0007a1a6903007400640c41030070a03507203607070172800100f14035455070196801401140c07801d20054042128202c0c003107074403015800740280464810b00145100e4030400b48021142c03000030543d0200444d074a05500d14211156008900141c070449149080007820b0098116054982c00c0c2541483c450b10002120200b03405564070001c4201480c0200540c1d880e0004922260011440d4030041440f14046850304e003c0c40ba054003248102d00000b91905004120500444003907010314140721866400b1005010700a0380b0b190f01c5a0705006070031101042c00020040d240781c020003014000e10a01d0314500303545c1c00801100e056040455903501203074212081f6603025902408000003442d0010080d2181e010068bc00b0304a2030300121300142100c400d501 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 475507212 1250 475505962 475505969
    0x3040c05030a0b0f040c030206040b07020117040c05100210050c070501380a0905070305040c0609060507030e04020705010e06070e0a03081905250c060804030e060306010203090910 79
    0x40216440d84450506a40d82862a0010700c610b106400007811000c021400b81c0d00103125a0303d00d41100d58940014174242c003c0d8002c0c00035140c000510302d0440d0b0300034003a0000802c51310040d410b2864580c880040d000c80358405c480c01020600c40c8400b591b4030911006030b01c01d00c0030b01c0030061070030501091041f40e001440112047d61030251844030a4a802c0c00c519001840500ca00311311001c40d01c81c40c045407042c030380303069005000f507080800e16034200c1c09490f1040b041960009040d14241c1058441040c095009030140b14042c94103000d007a51003412101e00c540c26060000c0d1004908020030000e104060000c1d010b03500c0d249039070043c0781010451703d010b0017041d691a0344003088481042842c1c200351000805004c020002c0d0003c15130201c44907031091030107042240c2440720240c0900d1105002c881c0c0000442e490380b21200421114548203006019140307015207c502d480d81e000351000581c0c020703d0f440342102100141d4161701c2001110f4100b02d012f400310360350382030254002c0e10300b009900 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 475508462 1250 475507212 475507223
    0x10914101d0705282702030f0403120902031005150607150203060a170a061a130c14130609060309030c020d261b12040308030a0605150a0f02190b25050304 68
    0x4c0c100b505030500c5d4000e60340581e511508090480e15655401e0362134580c3c4d006100f004548941281c005a5420300c901c040342d1003441d001094900e415001c1603181d140c00c608091040ea02840303d000442c100c14565141e0344004440143d0300e844600c0041e401184a500090940c6100d802c1c2131a090008a15070008511070344c000e0060760796004028072940080c040f0036401404944d004100741c50190400000c0e842103003082d40e00140c4800d100e0185611484014540003246a0b0821405502049a000402c1d0301c2c0ba080101c480c65a81c0103245000b200006845041c4000783d0400740404a0303200c05030030070f118072024450440f440442d0220f03041024002502c1c59841c0c0740766441940803a41180f503059620341c10b40307841d045940303c0006400140c1444551940d8440104090715900e003d00c002060307a00c1c079903803980c20420000745035140c409620001c40d00250000e6040c4071280c0c181010700d0750311142c210310725510040c0f1440c04100901e0710f0101104840c1400110542150007103001d5401b52 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 475509712 1250 475508462 475508519
    0x90f060f06060908032b050405031b03041202090406141509090f07030b0a020706020f04091514010c030302280809060c091002010914101d070528 64
    0x102c1c0191100d02803482580d039150010070164640109201e07200c0e6040004500b544180c0100c1441d400032284201e400301d685520004038030520450a096880c4500071181c02185050300342013030048004407110000340144a107174045410411642c212502c500a0b12002c07032050f150072401107010340c0400c02454000c0c15403401013001440d010441d45a00156500107002c0c1c0391460303498001c25900240742c00201c65003801020005207050004000c800c60000c1c0e21919207090080402c100c54210400d02c5c0030000ea0f000c100981c0e216a81c0049107c607090a00342c1c0b0241c3e16040640213032040c500400240e1800014504694000402d2503048076404d650704005940c4910010303036500310070760786003840500521513241c50340342450700741c07100801c4c0c0e2001107081004d40d40c481025180111400e580303500322101e800c0c024213207482804081203c200d0300c09044c1c031500c4605604e64100740600d034091004001000c507c03079140035210140b540840d00a0b846036a450700ea448084440c10172a01c40742020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 475510962 1250 475509712 475509719
    0x1104050c0409060e2415070305070b01091e02090a0504060308040603051803090d02061c060509060a0509060f041409060402030d0f0e10090b0f040503070603090f080d090f060f06 78
    0x744c00350380d0f2140c2400c1c8450507490301e0801110300702580c0c100c80e00d40d01c40d0421452042d42c08000000d008202d00c2034403070684615a51900b24480c950507004449003900d403500102e21550725404650008900000c0184d07603031090070100b681041207400407074000c1d040460020420000f01d004004842655408000341e89860b000c00c0f044a440912400c1680d02c2444003004500e442d00d55003000e0de10061603180782401d40300107584003070304040c500759455640e42c00030013143c10000c285640c000c50896181c0c5d42c1d07a09110000d090014003800007801500300300d08100d4252281d03480088480141201e4403014a40301c0c41c0d141e594801210100e010380142080d1919045c081e450040e1400c209445080303058240138280082290703000320050810130b02003400a1031410b210010301d66401c1003103006594908000c14075140c0702581d0b0000341003500d031a540341e0104030803d56140c03100d40d10040c0300348e0f15500c0112000140c20464070180000e51064640001c00600d40d2060440508a900030b1003410758 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 475512212 1250 475510962 475510979
    0x1a041e15030c090e031207021608060c04140a050d0c03050d170711010f051f0e071407081c05061f080a0c0c0b0106050901140a02030d091104050c040906 67
    0x1614031004002c4001450240282c0b03407180c002c40442c2c01290b08407828003214808140e403801c010388000c0c0250308040c0d44222a80d6000640c0c00141620b030006080340e080059050300140b00e0340c4503112045082080070381d0036655a500740802410000e184000321030182c1000c400f05000c2d44403c4840384261010f1100150082c4c00c0c1d0041c44201c0301c110750480c1e5802c03c1c25130300641c81300c022023a41c4d50f81c2e01ea56892400c003846154000c507860004242901c2404800074070303101c820341000c258100e010301000b05403a030207854406800610505d641d1100807500c2c00b0000b030700909a4078810128554560780c0c82d070b8144d6100d14401e900844120004003c28007008084140c3d0240710800665900001800054590000100c40da02443c1c294a600c255458242d20324000780c0010000420020343c400b4503690001c03100c40160400d50341c851030720b6050623001c0d40c1c9200c1e000f56204080c1d210240402804030408482580e808040d20500462a040d1402d69007039010b4011210103d01d418000700c3c0402c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 475513462 1250 475512212 475512251
    0xa12150b220803040603180b0a02190c0807020d020612070807080106110d081306050f1b030f010509060607140f0d02031317010b06040e041a09101a041e 67
    0x801600c061468142460812805080e0840c4018004501c1f140c0a00c0021030764140c0e01d12919a0a0006031a140c0b120032850360000140722000400c22a0304201e00481e00d0001150810f90f03044442d541c041c0c1d00e42c8080303402c0380180c101650b10181c5442c01c1000560308022898403500341e81d901c401d2a6038951005a821207001000024a5400000c0c03516515000e0103580303412140d01c54001d83d10f0b00d8103550b00c109803802100d0700c002003040b00301400018000800000c00742510500a5415032420180030360034854144a032611446141001c1829078948408907000c4680025403203801d4484600b81e030f82c2e29103904070030500520070301c0c09002481784048203844802c0703036242407041e219141c0102030720782c44a201004031065590755518030711965010b0080c0020400b64a010680d85010300b0702d0072050301002144504190007c0801c81000004a01070f800140b144c540001c2c11080d0041078200180c00a04a81e003007803034800504400080d0001000202480c00c0050021200102c071094024 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 475514712 1250 475513462 475513469
    0xf050a0f0819020408070e10180c050702060409050f0603070b0a0c080421030306051804021c2009091507050c010b0a0b0910140a12150b22 61
    0x28401030480962900c286112a00300c40c04405071005200c82d8420502240e006a01c49000ca41c0404420081c40f006464840e920507840c150103d0018900000d40c0710300100d04004501480d52552180d0a4500850a88034140d130003030040382e242d94540b0100c40040109403099000c0c4e2070a0f80001d80c3d0f91a001074958141d680101c45241031605d00329060301c0c0480344140c02c4460740404e000214812004400b400c00d036085065124089000e9810090100c501c42e80082d070250f03039020701c2c2440e11194601d030130350815030627039052100b400712180c0c090500c52800d900130148542c80020039239240502c01840d40d142c8007100e9030407081d00c070008102e994130500001c481030446d68800043c07035035016501420345601810000700d1900e80307040010354031100b207421440340f00c0c2000c207140919007030014190b23098a003503042c20404039000c015820540c3c0603c2d2841c8080000e00100c644000c456504404400c5505500c0d46400d43d031901c034a00f025800c901e90300d107519070100200d60500c2c3d8400c00c40c1002c6 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 475515962 1250 475514712 475514717
    0x41d0a0b030129010903050a08091f020a020d021915170114091305100204090c08090a08030903040e180d080118051e0703060501030b04140a090519060506010f050a 72
    0x1102c41a00c00c0d02070f0b9154085244c140032915000001080d03061041049103403149100c40c0d034407004902000303050041c0e92503c10f005441903814401241d0005040701031103030112030741003821526100191605640d0b0040503440008a040050500b4440441d404d036414151100f08108401d6030300903003107403070901c0f8000c00000150032000c0c090500020307031034001da41c20034502031000007519481d103818810b1700465a0183c1c0000d08008404491290380d240203403920b080b400905181c90074582d0740e00c0005018080d41c10005c0070903808001001281c000746401d07000f044991500260349c101c1d000d40c040358160607028000b050031159100ea070303006050b40e40e45075858110701c1060b150741c1c0050600a01220312b140b5840d454404000c05c7c051010700c601030035980490001c1c00c200004040d2441c68817424095801c0c070b00d040640400c544d040c1540a220718000040c1c640c2c17a4140545031424104843c0854170358024002d0600c5401d4024510490342038a4140901000d990111330078031925809900 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 475517212 1250 475515962 475516001
    0x607050a080d140709030308060a0b0d1125060b04111204054b0304050f0406030606030f0b0702030a0509060a0c0203030c07030611040501020706050f041d0a0b0301 72
    0x52a400050b220304480c00d000001c094a80c001d000207246800e031500d401103034081034100205584a29526132258043c5d4802c40c0f00c030314085008010340a03100f6208505d80d19000c02c142c0d00415203081e1490041a08034a5003800c054059107040e5200c011340c1965030605002c0d450010f42414010130350715581409420b8a4080103010321500020064400c0f9000d00404200a01c01200c01c4c100c400c0c0b03481010581e60a4401e400b0702d00994494000060a15820900c452030070360401000fa00e04aa000b9151041c48885110000c1c004000940009045a141c03100110070700039590307582d0022038071900565030585c40d0341c081686e03a070062082c10b000240d0708000d0840c4070300b070002c00307070032104e00070305003090a60701d03c5d40001d042d074101440d030700704a41c0904e0040007031001e0384c083c45100c0c0d0b0514040518050602000079190300c01030203000c092000010301c047c59401403004403401000200a16050031105804a01082406a880d1b001480c1091100d551525040c130404030300a240d41002d09 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 475518462 1250 475517212 475517233
    0x6090311101d010921050d090b091b0f01270605030601180e040f02120109050f0709050c0406030e1f0902010809191212050a0f1416030f090206070302060f0105060705 73
    0x1000e17001184000f1081240510151408501c58003401094512407001000c413071500e40038403840c0003020300668207500f003540f002c605d240d00c44520607c00e0300d03003c0c03178051441c1d4030030448810341d200220401400703120540c40008110341c0c00300107140201c900340c0c0d4a444240c808034007a542c0ca50329000e0041d1913109200800c1c000799001c0c1060680c184080c0c07d46600750002e0b40c43c0c9084a46420040d22142c018402000b508003041c8100d401401c01010100700c1c6d800c0505070b00a840c0071303038040c0c003051555880e6403e030005420040102c804c4e640c031446000c07112010041801034008020101d02040380c00d07000c901c1c40c84021803441da010319050104500c0e60016220301060b06241c41c010402d20242810884103032615000319072281e0301f603200124141070028100412210740c201d0300c8513080071110900070341007100c2440014025aa20300400d03554107218001005110a8030000e501c42e0b40060850105600030070781500c03030810700ba00402a6a07903041841401d216030100144542c01110040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 475519712 1250 475518462 475518503
    0x6080c09060d1b0914060a02030313020303070227180a0210090f120c14060304030815060d0c091a0f0705030409021b10021606090311101d0109 63
    0x1808603031522075000c1001e1440f285044010f200c503c0300c0b4000074038111014424400034038942030070143c059402c580b0f488200d4600075202d00010300000301801d210034405040d0b40d400c005950720590000c00000310b0884000005030010002c0340040c610402d0400041c0162006142855111117824040c1c0184a01c590822640302890082d04051080b10304010406071000c0308040302800748a030316035041c4c000900701041c030100305a10004a8403172000110007240c03249019242c01c0341d41404d0003a0242c0340c0761540c1d41c90380d10340f90780e003074000502240c0c1e8028841d80340c0150300540d40a4880600c03c40c3c440107100102c000c040c5030600078500401c940928482e8090086c00450b000700c0030340b82465100d030805011399101c42e0039190645240c54031002070034001d000c0d10b07039408018181180b6110301002c0001031800307810805455140d07184800c0f03003803500910740d80221900395000d41f09070301400c803511402000c14081d80b9040e06840445100444414482c52011540110049c2140208022003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 475520962 1250 475519712 475519717
    0x28080f06040603060c050417011a01120906090807020f030106030c0b220305070806070c1505040206190306060306060c0f08090a0b040909152901170a1506080c0906 72
    0x34141c009596035070000c0810100e2051065054059403000e540350b2409030300461041250f0540015a4503044012408000c02d1500003000309007800c084021190070350303180b4000d00c0d0380d43d005840c45044c040c0d0341040140c050014440544200c89000308000a2800d0500701c0c1d01d81e0000401d0300d8070804062111030701d400d02800b410401d01c0140181c2c4001c000809418504690080f51590321900c810300c40c0e03103014000c295018103030340b41104c00500316859a00640d0341207c00301040310b41d15408141551500401c4070407061448075441400305402c1c00003802011180300e0400024908040400c585224905290312107801c00d0b205450b8888584030507811b0390081888540c0003009000010f02400090701400040c041d8840000351554141090803071804020700c1c8080e114a0b145102500b5140007281c03c030740e254010b0800044a46c0c050040c2c82a4040b511480740c80c281c000104100480341c0e070010389200d4828142900f100c3d41d106d609131910001039a4a14400e10180200340721811304201 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 475522212 1250 475520962 475520971
    0x40e030903071e08190b010b1606091e0309180b030a0b09150916060504030312091b080303010f0503030a05371d1e06070f0606080328080f 61
    0x20400d081552031340210b2525201206414110041d90068010b121b803000601d401040d050b21901c0c944420089002c0c003848003490000c10b240d41d01c413200c1007400b505186854184101d16007000c01c0004908000d44803e00380e1017905203181d4004911281400d031801103030701000b0b015004007080185503aa1106e40c401c02404c80c0243d21942501045103004940740c40e014061400140980300c910b440500084522500001c0a0040405c0700300006a400000f140c1200e01070b010020b2029090b1074202c245e40381450003502007a02c6c03004003050b462004001581258500b10700030f2540c0e50f64006060b213a0180c0c44c1c000002c00c1e000d0101105c5100e0150002962025050781d10b0317a0150000010300c4207149001c8000c00240c1c01d03040c3d0700d00310424980035800581040301d0b406414403403c0c00038410040416501c42c040c00f40400c1078401c020b01c03405400c1c443c039480b00c8180021030302c58001c1030392904500d4402048801c40440c039264802034002c0710b4480305030741d43c1c1c8128694424983d1f9068580251 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 475523462 1250 475522212 475522259
    0x200906090315150f150a02070902031608100506031b0d050a060608092a040b030102040603020a080703020c1011121815011818060e030405040e03090307 67
    0x1022506590074003180c000c91220008400352420a2900c44800748a00507005004513a014074100441e52100f0f4000b1139440203101c0941d40b005096030803414824140d019000e0a400031052100d400d50725041000304400d10741c0d808a2030f07a0341d02091507200c4070611078640c1008081001c1589892800c1d0030380744d180c0040c138000c0d1038107248041d8107003180c40c00c503690313600582d0300c403010b219540c3d0203041c094005011030b00070944c107003026403598201da40e40070440e80c04030000103074080ca5071100e1300000c2403820000e00071920f0b148d41e91806406075100718403d0001840000000c0c2c05580640300381d65010174400c0050180e030348211022030080c46451800c6010300014801540169290884030f4429100c0100070000d4284640d2001c0c17503c0b42d04900d19140d407a0300d100500c1003100342d102041518068900c046101550072070074400c021150b01c000351100381881c482d41c0125400100401c11520240c4007000150b038010035094907800f806180c10303415003010703508014030307000352281100150629 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 475524712 1250 475523462 475523467
    0x6030d0215040f0201020a240b040b010f030e1603061d07030302070308030c04030803090a0c061d091506070308010503100b030c0d060b10090503100504120c060f020c1b04200906 78
    0x707440c0c800702d03001c0c8c3c90807083c2455480005a040b1040c50300920052500980c2e0a01080820a00107000d41c07040140c0501096515111817100d52070800a006103000ca40f100304402584078200800a44034204100b0244000071440c440c0d188030006429040741d0300356014102c0300e42156180841c950018106c100f40201c2800040b01140c40341e8011400360310b11034014079204000349030084180e0b08540c400b0041c0003290341e9040258480c046042c1300c0c940c04440c5480ca0b0340c0c0d580321040305051112082c0c3d400c032002082d140304040d080b420a50681d03404408640c80c180d00c0950f40780990301020682601900060300040940c00c0013190702924506c0340c5000f144100116012071450b111725060b0b03200040c9605410000b6090510040800c20035425003449180b078035460f20b5030007001104040c1e04000341d601000c8140301d03180d400300a891491020956880700c50100c0c003650740c20082840020f00814a40b02c00ca2480e151007145100f07181071003940c40a01003982c901c08a50004008540c04c02c104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 475525962 1250 475524712 475524733
    0x60604060c05010b090915060301200c0708031603020c06030c0a0e0f130f0b04110703050d110a0c030f020610050f010e04020301060302040e0109050c0d020307120603050606030d0215040f020102 85
    0x40a1a170b902c80c0a04400610710101080000303402c5c800003520f43e900a91401c00141e84644200c1c070780310705000d0038401d03041e0b40d40d5898083c60302d013107001e85c0700103d280008242c54030f204617405403140301d040c007a41c00c6480f05000c5504010b1148025610008121010042d090341d86024804d4844101401000c10540400e00408180020842904035180e1391b07403005c06580c0700415220f030f841d40c5d00e010355007080494541040f546503803284080160038040003040c0a201000190801e10821a003140141c0d116912044043d00381008103500318003240d40d08081e0410144001030061144000c0482c00c002c5901d040705003e203160101d0304203810411114080c101980b2903000442c0205520382e8016900d40c50101c00d01e01224041e00598200d03401c0205004045400805482080c90180c20060703072520317100c02c20781f121005200b0341e5a0307840c1089800024800013084031481504260156040030380e0007401240c40e0729076110302d100f5119207603000c200480d803880b410041552040c012103118064 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 475527212 1250 475525962 475525969
    0x306130618060c110303010506071e0c03050c01030f0b0307050103110c0102030114010201180f0b0a020403050105040c150215011404091703070905041e111c0509070608060604060c05010b 82
    0x12015002d6903150384076401c40d000d207580400c412540b400300001550455041400040b500c0c0300d04000606815580e03074100c091041c0c8015080d03600d030f41c401006d104680d9285011030316000d240303040d68042468010220041d800340c2c0a00c0800490003409440f449080000640040103801c4110304440b13018048102c955009100a601034200319010402c0c0b4024900020300352303816031524240707650880b4001c800061160905083d4a640b044034400341c3d90310102844000d0049a00103807a41d801d100901c400e000e2600c08110070b68071202004502030452010680e0303964003601c0701d511001c3c900f000401c029240d40f107500030942030090001c1000140d41c0caa45100c0f010840110403403903000014401e001340c00c02c480c5001408141c3c0c0610891480c0c00740703e43c100400a440e04400c548030014043c41201e80b1003215600c502c8801d403c0402904100444000d00c1d04840704c0714944180750010031807a000d200c16170702c079607801040c3d28982810010101c5040644d040121020f42d02c1320394803401c81c0d4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 475528462 1250 475527212 475527251
    0x30e0a0b06030105071e5016022412101508070516060c0c0c050a0e0106051b150f181002070201210b0907080603061306 53
    0xa00400408115050101c101401c59030301500480c140505c0038540701d0304d481c0d11100050000300702d042c1004241c0d90803403c0c40050310000510910b0301c0190038586500c02001151800c013049192004481c86080c4e140c80e54035202c0c486d040f041507100005004014a006a59001c03210a410340c410f1400d0b862140d50f80c0f030b0780c0110007103404015540d810002e84201c9403c03101300512008000c081038a04c52400904803d001810481c01c200d0b0018000d10103403904154501e04070342c8007804025130100340380010f20351200c841c0c04031400c99165072b000509242541e00c036000ea41101110001036464000b05641e15031007841000c005018018510500300c0d0b0034040d89030024035080c140201450a68441e4107039a2008142c401d9200000450a00c2c228001a11071b81e031080c10100181d42c6c02141c00148d8495108041a2041c10700072000301301030202c1a08010030926040d1002011a1548907042c1c1da0201d08850b0141c141d8016800102e0356501044030204042c010040002c038509030103c4541c900 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 475529712 1250 475528462 475528483
    0x10030b150618030c19150c0b01090902010c1704050424090213030c0609090c0315180608060c0d0c080403170406020d020304030c0506090a1110051303060b03060c040b07020907030e 79
    0x11044410840c82998404c0402d02d4165440c1c43e120701f085982e00c81c1444e19040c0212040c0903550440720f030440e4024031400c00d03520340004c0c414502c0314900510355016403040c0603250040382031490101d003150641c0c03500c00062041290024100c1c0c11304c1403100c029040401c500440c202c0480c40003003c1244c0101c01c2014150940d1000355140c2031214550a407420601140d0415181c03103905003000505504860a0b100c00c54000255075040c0d41808000d001541c00c005114004c1805018400c0c848038010042c9200c03203c0284070b00b8442ca00207444a4804580140c08100c0541007000011043c8030090350040c0700f01001030601c00c0255455040341c200319011004290b05120201c140300c0c1c20090f03d0b43c0a9240c6000f4a201c602503500e11002e4a25900140e01a003d03000746005420300900680d21068465a50055510f6490030014060304035003400c64024001c16002c11a0304c1a0034040782c1c203880101044a2801085600f8407503000700040100f000c00d42c0e144540701808074244408083c5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 475530962 1250 475529712 475529749
    0x50a0804080a0c0c090e1203012319090e06070c0302100f1d01020a090e0114040e030c0604120807020127022b020f0406060e120703080310030b150618030c 68
    0x341501b03502a070740342900d0006114180034051004010009554802e440040000c5410f10702a100410208011480114540b6800030744d41f000407074001d603250700442d00500c4480840d185c44d1152030040d1140b451005002d4010b8000f0441000050140c0e084a000c21004d2400015040c115141184503410505040e10540c0d40024030b9804440c3c0c45200178000d022a101803040a5241403001c3e40035028800c4401d01079074035208001c05800c7c5c2402610b021000c3c04068806a01d0306140480c2c4040e17a0300030000110780c9240108090501c14400c52940c0d88400c03480940d0030b03071601d02c4504074070380d0318030101c0c0d22008405090500c0001c00b801d0078140d0341680e40c4d94406504c1d51040055004085103524025441c1510810482e6400f1100307061034201600c0c8622112441540b6a007084078a800c09010070705c00000380003d041d01001d10104590003501d981106484040030800d584101900203507200c0030501580c070000c55180c012010740383c0b0007000c6807a000c00b900049501c502e18480d03900003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 475532212 1250 475530962 475530971
    0xa050904030507021f032315040f1503140102040806010620100b01031a150921031801020115030b0709090905030414010c0b0408070212150610050a0804080a0c0c09 72
    0x52444d0180030718481f1103000c00103082c0c0c4200f030002c4021701c0c00c13004100600c3c88508840030002d9490301d503c018068007000340305210151221008241c8034219100480b8250018580a06018010f10079a0140c3d802080500203076482c0450890720861502529030300450584d141e0200c180003001000b080310f04515010425001040c009012505d14400340d030312024a8a41150180d910a9962042100000000340e20f65a40e0408543c0300200c140c4940703034401d8103003003403c041c0d00000007408508505209034000010301d200124281c1d03040703141c02000345030070a4041c80007802c00100c95070301c0341c07507850169000b81e0b5480c96901071700c0008170140c6080c1c1001400380308801c0c00d032a05281000c4282080b82d82881d055440c01d031036041c000c0c8058018000410200c04654980c420304440410100c12030300701c051440c050100f2110182c80d0148214200080500340c240210190f0f4500140c0c0c0d201c11740260344a841e0304401e0b5102048031020480b1003e06840045e83c0b139030200000d0000100b0006 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 475533462 1250 475532212 475532269
    0x40b1c1b030506011205010e030310090501050609100309030e190e011403030a0c0c03020a0314060f0c160f02030303010e010f080a020a06030218040515041a0a05090403050702 77
    0x10146044008100d40815121814008988009407003411540c031401140c62103c401d05089004001c029501c6131180000024864000341e017520400a880340782d0401c000c2640c1c2c072008c22580748907034440b4540018402e00074140d5140240c1c13046010b28003e06250509a040e540010301c00095844161031480007010113000e041445100c040c00f502c50040d03045060f0100c4400644d40b4084c40850360200000d150240c8104420034050304006c50340580903240d80d9840c0d1400080483e007a00d881860fa01c1908002101c01204e1040d003406040c80c01140761500140201c0700c40c11041c80d20054507007011030021900141c400300011402090145070651255050100100724001690300c894210360019040d00f000d0f0b81c841c0f43d440101c4415040050740c800300389a4170008078280c0c90101d58010319205c10407c1d54070109e20a00030700e001c00c40e410000481c115a01409185248030065080031000106100504244294a4006020303060482c1001c02682c0050700e0a16a0300205510691034100d11 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 475534712 1250 475533462 475533473
    0x30c30111507090e0703020d111c060501050a0c05070e0f0907080f070b030711070305010e010e0304030b0c13090c0f090e0402090406050a0207021507021503010f06030902040b1c 78
    0x11a940321080e50703606504000d000140007444078000c0084180c202404541c085009a04561400c1c0c94441e0500c03194070f00c5030390490f298000712403140c1c04000c40e5582c4003c100d564443c06064440503100d075400c2c580000d000300c2e1200781090702103a2920038610702044080111408902c23400303030846074120928155940c1da04251165104040701d0744056412441e080c03000c41e0b00b81c123885128900d1526559250310454000c10407021000d5035020b00840401031100640051813060300c000c0090224030001c1800d203540e031149100c007030000024000881c140d52100001003101ca400a1400c22945440e001003404588014940340003003420440b102c1d5500b5008000c600052003c601d54401503c1d00b0380105084a07401400140100d035510f000902a000310303419542907540140100c02040410103403126681e00012040e0f10443d40e00c0203126028454070101d0341030311a56405203042600e499010750140c4008a8100ea010b62034000c005420340740c15084180001c10f0600c6840003420a0512 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 475535962 1250 475534712 475534723
    0x51303090815040201030c0c0f1a01140a0b0f0f040b0c07050405040812060a080706020312060f030703140304090f020702040b100f11030706050928030c3011 69
    0x14103140c200050409000302c40c0c070042a401030b02800d0202d080c4144c0d80c402c5820b40b0741803100070320403000504810148001444069422107102101950698075000d1040c02603003982c0c400b82c0c0c401c110403c11301c0b02580b0b4002802008501e00c00c2c150812101d802d4686054006801980c0c1284e03000c55400c224440400882c401440203480802603800c094036403400c103104400d03000d07107003e00800108109489244058006000031302c2614407841d25172400035102e82c003000c0c032540c04612040100d505d0f03203002c074051420010010014081c180c616a104108014007840c401080e00082c0400a0302b501c0c076019581c078181d548100143c2e19442071040008039407403200d029014060780c0350110784d41a00000d14030448103560522902e82424510903a00e0351040e440300400b024180703001d01c007540400148480482c2d00541408500c104226020125030940740c0c40030b40004c801c0e030050800b2030300b007445001c82201d40325072680c541c04220002e00c6038403041d000e0800002e40c00104071110321509010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 475537212 1250 475535962 475535969
    0xa171809040b01121a18011d0604150f0906020d0f090804050f060d020c0c090f070903140a0507030506151203070809120114150904030906030c030b030105130309 71
    0x1614600c41c20982c5031030264441c140103030760400c02d0702c1500c007062280e20301e50100c03107801d5a1500c103014a07010110381400d030994000c0700b0a81d070074010750f48030f050300f980911041401110018001555070383c690343c9226500721843c1040b10768512022840401c2e1303008511195000f0003015a48408680c1c10600321200c40030303101c106514007000100082c0e402d81c1240c084500c110b0714007882c2c207040b900240d0688125920100c44038400100d820f82483e020980850001045540f4001592200c0c0030038020001114100005004a4070900002c3c660401e0700c00d41d02c00242c1120800080c9550756481d12480303400c25105603000200700207000c07250500079000b020095a60b0700c0740c00c510035140759403402006c400070003001020803211080c0e2207945a5201d403050301002071200c40c007030700348449080e4010b541420f2400300407445440603043c900c44860060381d041d17541807100c034a400401c800404591003280d0403d9211855030f02c19036070134003803c0d00421350200410071f41a41d034030380034003e40e80517030 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 475538462 1250 475537212 475537219
    0x6020105060109140102070504021201081c05160f0f06150f030804030b0406090b04060e0c0f1e1f030f0e010b010915030f050c030a0b040218120a1718 66
    0x7007101c0390764001c05110403079031000039078110307006a000143c1c1840107a030401a04684040782000c84c80c0084c0007014100c0340201c090701e448016060494005100da00c000c00702203142001083e03242108110001062406486a2540380c602a500d000140c0111b9009946441d1078034a508001c00c1e01000d4007004001c1ca1040c1c400301407555482c4003503070080d48405842d205511001800b4010141c100b010701c26400710302008180303404d192a60080c007881c41940014400c02c80604210b091082e0400020180100045000001036103042c0c1c1c102401d94543d81c0016140030460850310108140d0000c40321291004500c0490b4030122004407283e461017802a80e0401d450380b045a600306c500e81e019543c02504111051503802d0050f4007a10984982c03480481c03510003041218003204000c0c40c003444140074140300000c0c50310200800c1c4e0184158400218003131072815804e038039102d90320140a80c02801611180c50f002d84401d0094001c04c2105101010006542ca01401140d20003594020044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 475539568 1106 475538462 475538471
    0x70e0108160501020c011e03090203030a05040e1e0106050a05070f0b0a200a05090f0d0b0429190209130b040f0905030901080c04030516050a060201 65
    0x880035140c210780c40007001c5032a61021a1213240c20905039228201103031041d01e02e150081020809030141561031120000584080c000381c400084243c0701e040e1030301e00d003e007820001100102800107451580401c1c0c004d0101c0344411700d0541e03143e07142085c0c4400d8040d206407218828242c029109071048a43d00701001004a1650b102d1a2850030521038008483c400000030340d480d02d00c0c440000024001c4500d66403051010b40000f82009008811b0040b080d0086400781c0312408064580340c0d2254108400e0000d5050100b4034101001c500d019440041c60941c04d4915000d003c00e001388001074020711013280d16405079007482c44000d000d68281c0500c0900140244051900d00c0e0056041141a01c83e0816601c02c2481c50764001d0051443c1c03841c400d0044402c030f82d00a00f20406040113000100c0481e204000c20080844c00707404000f0258106410012562059071200f811a0f042 = true := by decide +kernel

theorem cover : BRFrame.Cov 475359712 475539568 := by
  have h0 := BRFrame.cov_init 475359712
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 475359712 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 475359712 ≤ n) (h2 : n < 475539568) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
