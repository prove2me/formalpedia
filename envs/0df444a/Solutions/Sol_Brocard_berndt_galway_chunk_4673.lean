-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4673
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:22:05.194652+00:00
-- url     : https://prove2.me/submissions/1ef38566-55f1-4f96-bdb3-b783b8897a66

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 840287769 ≤ n < 840467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 840289019 1250 840287769 840287771
    0x80f07090b1210060e030709091a0f040c090608070b071b0b0d060b07030e0915040c05070507080c010503060613030c03080403061805060a020a230307090f03080703030507030f 77
    0x1000042d1850346910a000700703001c00320070004940301c0e0001d5828161034850590184d0007445d00b0082c801042c1c1040a034580110400303030400e8031010403144094011078018410507408c030f003404100319180e0b4001000304051070081012500b0260110748a14640c400d001d40800041404024050107030310032a40c12501c00003400d40107644110311845034201c1010069000c1c030300100040c00d4900b803812a079140e54103658621000344c03118200101150003071b024136884400c003c40800380b03403124030440c5150b00036a281d064035911382c0e1400601d0810590000398181e002384000142590700310041d29042002210003585668401c0351400803414142c2c00581140d103a01c20000c2400700150051040d41d0003100c044c003034010001c49c00f031007a420045004225610840c00120b00f80c0c2e07994050041080c082c03034103803180c0310b06000e005070360b90301c044c0e005002c0b54000003401903241c3c01046400c01402c03030440004045285848820580c0070300300c0d000d41031549590002351085e02ca41e020720b20750208828 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 840290269 1250 840289019 840289027
    0x5090c040b03150414100209010905041a0904050f0118051203061203030c030a06090203100308090f03010e010507090608011d040312090c0509150603040f020409020d08031005060a080f07090b 84
    0x405e52100b080e12044180d007030040c4241c1d001c8504903402150b0000c03c060310b4010b40704d488e140c01e01004002c4950707140c81851300200e880010b41c4d0303882600340c080c0b80a840140034000c40b48460a085038000c0034040c840102d801d120000145011604ca5918a2000e1229403603603600c80225210b41e0081a100809000000801002c2200c120245000710010301040046035150b44070345040344410ba0f010541c00d000c481003000014600c034001c00d000e01c00034044980c1c05070004003180c00d40d03a02c0c0441140b240d44400401184aa1048241000300401d140a0980f0b52503d86140042a69954940500f03c0c10800150078103000382501d440d1032011080400144c0e12900701100030105034041d00307101d01d0324040400e00080604900400248000384624a5500c560b92010f01c4001400703000c0380c0280c0ca5107078520160359510303150f9001c14024111079a907494101c0702008203845580004d8071584090110002c0260320103071171a80300740d501812420f140c6440030305444a890b984d01900701040001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 840291519 1250 840290269 840290273
    0x90f0a0515060901180b040e0111040509150109060309030903120804050709050115030e01142e0308030a020304170a090f0503060c2d0409090506090105090c040b031504 74
    0x85210350a800300e00c01c651a80c403010b0070000e65003c03e100b600300c3c00c1260101906074903580c6d40300c40c03000c1d0b5009200159504280070780500b52980c0704031400204e203000c40c0804c5181000d2207015485446c4900340f415007614100007078504241d034006d01c0101555a41140201400b4008403005580c0110f03c003011152a480020702008084030100c0343c5005460001413150403a00070a03050b1802149800e40315904160214010901903124012039901d48c60403900f821202040e4501800d00f503603c0501c1c015408940f415021800c0c040d10840f04d03020703441080412401030547e5084003002002503944c1d100c03400c25000c181d000380c001255494000500c40f418030f401c4164038044031014030164417059a140b04141e111001154650300c000006c00c002d1024495507174640480b107031102a0041300034141c8a01801a811070382085400d01c0d5917000100074014100200c0c0d81c030045c280e00a003c1440c000c01c2c46e6441d1400d45084c01c0c00781da200c030548030341540d0030310004003800900e641c81d0070f07140703424 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 840292769 1250 840291519 840291523
    0x3081c15030201020f0a031d0103060e15030d0e100302030a090b01080606040f1e09080f0d0f0e0a030e090a060e091506030a0818060708070b070f05091503090f0a05 72
    0x151000b00e0251181e618504580c20700820a03000300c541688a585152180701c0c4000d560084e0156081d041503075988000c11040b01b01480b043c000da0490244005148030f0809152801812407458000c0c0601d05a0405c82e0f5a6603407041c01c1000d00038a4056226221200c040c1e01820442800030070348048200080f580800005805200380743c01c40307081c8040030940c0340355400c079104444060408010200d6071620760709142c000150040c80303420140e14200c0682c0c0b0826158000c4186451201d40340c800c040e118800f1400b484c400000c03400003510403c40c0c1550b0280c220715102068a000702100c070f000aa64100a9100e10001c06510840c40600c1c9030016401d07448184050500c412a07180c0400302d5450f0400042c40c402d81c81c1c0c080001441c000e0181d80340380d00c040303400c070000758401300400a10002a0078000a05042482000d900310313641031080d000361811070480351040402c20284001e00301961500940f02200c590341592507038a4840c0040309040001e4211040341c1481980130880c100400 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 840294019 1250 840292769 840292811
    0x605210a051017030304060b0609031903030f050c07060f0e1204030b0106080103020907030203061c03180816031115040810060905040b04021207150f110d05030103081c 74
    0x200142c800301c45888a02420100560468040140e030050000400140e4254400500e001c002004542491a00030010703181c21030f911050300c90200d0b074089140400d40c250007008120100210b082c440c038a844940b0301071381e0280340c0c8041e0540742c0380c200b443c2e4240d425500210f0320900078030543d484039100c9068440b45138460f10084480516000002480a1003032606a0603658014007220040d140c0b048114040d4001419180c0e00800c4843c03800c404400d482c841c000964441e41716148039040c00c068100d0f0a4041342c2c803130049500412240108451810680015130782c1c4510090340c581544000303c0c000c0e10302034590945218001401158036600080d000d010031030780c0e103404d002e90f54881d0307000d0003500d00a03a4001c0012044501040042c90030400048041401d4012611610307680d41c0c80b0280c2c03100640004010418030171503881311581c0300d01c0c08044095100c0003401221141c410042840c401484082c0003200045100e02e081d803006a16031080880441040c82070b0801e09503403241e83c0712 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 840295269 1250 840294019 840294031
    0x1020703090504090c1206060e1611152802181309021f020c1003020d0c0207030f0b07090b120f01140307030b07030905070f030b0702070b040605210a05 67
    0x40030140008440c0f610f40194005203500c004a402803600e0a03c0ca090400c064a0b011104661901008103845d0405818284a0b003800c0303441000215a03501c02500c03401041c200d40200d50012602d450442c21b030b5120854100000075166607120341030950f4100081d8124404010040c00003030f841e403104004541400750034a003260341e04648280300120400b1500840c40003034100607404100c50390300145400c8008402e001b80150740a21202100140d5030112440b15a4082036001c1440c0382442d0040c854a4030b4a13001740010081d050468407010700c0c0c4811100010402007105000031b2100d4070914048004101e40c8015645414810079510f84200c011646d114464941ca1300024807800d0980c60502900070240280c01c10506507102c3d103002e280d005180c00d05068aa00b5048000b50381005460020810b507000d980d49039007145441404041d0107801d503001c6600171001408100c1c842c81c00c45040710070302e00f419540ca00e05d2000c01c04108c82c1d01420000300c501c0c18030070003c0b0741040f5001144111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 840296519 1250 840295269 840295277
    0xf0513080a0b0f0906040f022b06051005030604080c0f06130b060a050f01030902030106052d0d0201081614030f0610110a081605030301151103070b06100c0c0801020703 74
    0xd0f031000100703044890f00311030041003580403102041c04107480c44072101d040750024282d00911407203c0a03280741d130b40301d0380e800c2d000c0c0135010f0b02c0b80f02c03e1058600c9a076402c0390302424500d45040c03030917001030350f41c031b10140001d88a05400900510101010000e4140d5243d041d01668001d1410403a007040b03d0503e00d105907100b4078440c00040c2e0038545600036505a5000400206c03c80c0f803568011402442650b0049826640c3d45101140399511500650795000e88107000454040401c507a040102040010940c040c0c1400e091003001170781c1040c1c0c1c06a004074a0004c02c9200ea13074003102120361210080c81da01254400100f80304502514481d02c80c07045505640b49200450500402c980354a010003c0741c0c50380d0088142040041d0300c0c900140f2032009182e00824210030b158072010300350340c82a0700072852510310402c101c00058215440580d2850311401139428411185c944c01000d0318020a21031240200118514919008540720254160001441490742c1d8903911818002e603c20202039001c2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 840297769 1250 840296519 840296521
    0x1060c12030b090c0327011e02120c07050118080301030614010503120a091703041509050d02010c210e0f030109080a03110d020c1f0203090606010f0513080a0b 70
    0x114040c0c02842c00c2404040d2400340d060b52040800d840b02e4001811071030740c0402400384480905800d040f1603284a130032100001c1c0e54104601140c1d1454070140c50105454018450b04c4191001c030300480b580840b69041180c3d50f04041e140450040c0301c881c1002e040d80c28003118030703004c0c09280d1001d50305a91084400f0003580c01c800c00b500e0000c203c240309603a419444a054000f2241c0c1001c0580300c1c81c06035040c0510b18507211841c1d44851002003400404660010500b00000c4c4107559503000201d121703080c54a00541440c0c00b081c011800480e0190601140ba441c100400004060b14500002140c0400b4000e43c44080001d15030080c400c1803234464180e0803018011351506218071480954011015881c0c1801000300380c0281440b030302e030286050020f011002400c0d0980c0002c0201c40310000c00b0b00b080049024140140002c1c04000c0102e0070f1040c0200020480009402900010709003032000501b2340c0701f2411290781c0300d128030110f00c0c419925030000b00030307000091108d03075988120711454035 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 840299019 1250 840297769 840297803
    0x1110a0b0f19200a0903020310050a1401063002180906300c09010b041a0f0a0e040b0a12050c06120103120c06020f03270d0e0a03020901060c 62
    0xa82e5012061030180c8040c940ca030740943e600c280010201481075080000110340d80381c0010782401c0d0320402e90140706465500b084002c00003441102e15082c0a440451115418850010101c400300b100d48284580c0e1989182200034201168801c41c3c0e400b000155601d513000b00128108040b400d03c01e6010f128840003041e6240341c03c028001d41c1c01070814903d50310404410900d1340c1c489603810a0b440901807005840c8458403400c804038041c0c84291101c513510b5180030f030800c00320705a000402103940300074804401c816210b00221038aa058502d40301030780340c0011000400615009410690144407032000041d40440e8507840c4e04000e0082c4280c40c2e4843c1c0d6103052080c81d1042d098503400c00c081d14070051000aa00c40b2100b6000394040c5004d11807014180daa690032a40003041c0414003010100400034040e6031580c031594190400e0650420440c11048071a81c1d60b101c961143c414070403601801c0416480e0ba000400041d60024004121569108009802403400e88400d1303c040711400e2907814 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 840300269 1250 840299019 840299021
    0x812150a0602010f051b1e040314060f1303050406111006080c0f0a120201080702030c0d08061f05090402071a3d0e090109020405041113061401110a0b0f19 68
    0x20b4850704804501f071034841c01440481000c144140c404406402c1031102001190001094104521041000381814280100c841601c1c030401400042010710139100d0b01c0019510409980c00c80d00c5038200b000c03290300159803542c1081000c0100ca10982c1c9401c000050f00031001174518590720040c0d8000c0c2c43d01031502d00340461055240103c00f100d1008000c0c950041d481003d16030b03402000341c8141ea080500549100d810516041401c7e00000d0000061250318649500751902030003068800810801c41d0030f82c064401c0c000d2a000922895010407500b00707000011203110760141030442d4465492410500c490b002d0303421f44580190789110001200031080e50488100049260401c40103030342480c0010400540780700034580300095413134409400068680d401114000c0d4801c01c41c00c40444d02d80c01c2031144031840c13100a51b02803070070807008015680d5039030584025084203290010144d031744900701c20704c0e14403140300c000c0844031110b00b08403c62001591403805411404c807200030340403080541034 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 840301519 1250 840300269 840300301
    0x40c11121e0c0c0d0201021203010b0715020a12050601090321020106080a052d0a030c021002070f170f070b03100f030b2410110c030a0812150a0602010f05 68
    0x8440d41e80004490f403510715200f0b80703090070684148121011241c000950380502d0708203a004d51110321010a0344802c00441e64007120b8a210350781e00071401c01145110041000d40361004911801c6d075600e000c43c0040e4480d18641000e0364001442500c03003100c10003280d0000ea180e030b246c0001540ba000004c11a03000200700340c0d42d0f05802100500354000710324000f000c0c1184184a0503100c03000c10500701c06400d01800084940c1d0301070380342c108007032100e401400384070100e02c0e14407411900401d905015500800640300d042d21243c03040c007142c43da402004145840d0b0030b004624403a11503110b0019a0014640080d403080c000b42442c103000f01e544d50400409009240002410f180b29140014010741c460321054080f08100e0100b00b0a600410303012802d04a15141d03000002061070703114048140040001c1000c81e001a0020495a030407a12051a24010721040c486259206008200c41c84840c0d0404038144000a01450b400c50340c603c800b80c028001e81c82c2c01804203003048001240308110f06440 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 840302769 1250 840301519 840301537
    0xb06280f050315010216030b07122f070f290114040e07091b030b0f1014090324090c0a1404140718090b0d02040c11121e 53
    0x100d0030b503200d807940f030000c2a400c01e040d18114031411443c01d1484000c00c1d88400214018126500c1c4d50620032001842a0b040c640031224442c24803800441413101a482c841240324150070031207050460704203000f154812440301030881d000c204e03000018851381020010003c1e045945003011590321901d4100c460900344100e00c0481c48031281c1540609003034000002d0094188292045030340ca451403034040b40c68288144101003403154010701c9851f010310400c00001e0702140c039a07a03c40b070b10f140040e00060b403038074442c01003120a80f0004c02d04407800c001d03900010001001d58291402c070070f80300300c3c101c5803e1050743d2117140c01401241d0707150004584d6120349100600317004100c50800d1b11603098001d40c101031a40041e5140c10b02484168200140c82c010042640d414164200010020005640a40200440c503140c07094a0ba03046c0d44801c800d00b10186d050b54085800e1b000c01c001030300d2240c207014029085008440c00c542c65400300310f00604402042140c03107406a82c040341624058040d134081c07 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 840304019 1250 840302769 840302777
    0x105030f040f05100b040b0103060f050607020d0f0b040b180a0201180b0c07061119151107060b0109060e060702090a24030b07080c0306040b03010b06280f 68
    0x12665000228100315400390080b000032001c0c40700b40e91198a410522003601c02c405640302a500300700c2c9080e020f000b6581d002442c06010b907500b0884e81107003010741485841d01c2000c0014150b021900c0e44000211050780003410807044107564100780070f8003201110200c0303c60080d032001410303c3c1c41603050601c01c4488140144003030b90860740155803035a0b05c44404000c101c049400081c00300d00160091100e80c50440c09826001d240280107041400607c0003800344e900800408110300720450f03c0d4061032a04008a90001000c41d900140202040120260003060014440c001e0016a4200c0c03040f820003a600c043c85165204400c0340e02c1602e0102e0355074801d508201e90300140c07400e03061071a00f0100c502c100160170303044d0a0b50f42c0341e034a6014840c0c0d1b640245600b010810b200030007002c5a40915641881c0200386041d40c407880e51844000c00c154803455071039510041544096020042483e405031030b135a552007540340c03200390a1000114410321013251000700d41300c9622407074003285180c0654a03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 840305269 1250 840304019 840304021
    0x40504050303130303020c0f0c0a0b030f0a020702060412030c0b1b04140f271e040210140d0605040b030d140703032007051902010207120201020111040807080714010503 74
    0x4a4010804040f03055003019024070503c100f88006018070307501d10304000001c158841405050100c0c005090340306000c0c2030b1090041007805034152080319448400c40f2001a95034800d480083c05a000710341041ca980e21171280e0a10070150820110500b0034081c2c0d1500c1071a59401b4026048911503001140460384280000c100c0c511120030200070b0400001e00d00c8003000400e6010406134401c07860010201a40d81d1000348038401c5064009400480c05d01402102244070b400c60200716002410090143c0c04c0c404401c045988184403c440440d540710901d03a8560000290b4000b0b03118a00405c1c0c480c41c41c00d01031130010700d40048c4090044030103440b40e54204100d003000c0031654000d131209400345502d420700101000c1440080109031000022407507110252410300038541058111a03844c920940b107030000c0942c2c0c00280c4001121320078400c80d02c3c001858170040b80582000d0320f5440c0c080c0070108002c155980007241c020140e452000869100603510585483d01e01100c1c2d40250110710100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 840306519 1250 840305269 840305281
    0x80124061d03030c0303062107051002010e010515010e06030f040204020915030a0c09050f0306010504051008061801110a050d0f1103090a3509280e06040504050303 72
    0x44a03001505000d4a980c1d0031801021034295402015280800e8000004103e5103290118055024201c0b07108402503a0300e9040c091651900107015040c41910740c00350240f6164400d421220041e40d50000901490901c080b28408410301980114081800c16501e0003040c1030600540380b1404070300e645201d886d142d5801b071000a500441025412440c0641d541c1010140e9400944c00740310107407070018080080c0d50000700002103079000b25101d018805102809640c0005606041d500115000201500d031000301c0110101d050340002082e000c0c220400c174400c217041204200c00130222000303000010000340340b4107179885925041c60105105000c82e07054626154440c00c0c00900000001030f000c0c4100e04d00e0190f60f042125080b00581c00881f12108119407040840c0440262500c3d6445020020325041c40e00021200881007200e0b02081408040d60b45414260340c109411340c0c4900b00740e0400824800070103480c081c0311801c61185000c2101ea040034401c0520498000b0003840c1551904 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 840307769 1250 840306519 840306527
    0x50703080a0b0d05030a020718060315051009151e0b0d09030509090c0306041b0f0c0507151e1e0f02010906020c0d02100e030318070e0a0608012406 65
    0xb40b103800e801950000f080c8000541c104014400484160003e0000c140341034008403c1408001c4c0903107501b410006c003000014880c3c061004020304840b0041403603500c0e14004d10050481f0f0384a2202d660078811942c0d008644a12100292410f50710511145038210005c3d041308040c0b40724100c5900402c1103010a002519400003040e5031080c944586008181000107843c92405c0ea84141008000000c2c07007014a083e01c61806100da001020049902d20070a0242075002c80d11007040c240305080e100e03001049010f003d00d0340503087c40004d40c150010025130041c0002c02008892891511080c0b600480354082c444000f081c0c010060400c10400c141c5408480c4480251f00b5041950341320070aa0b40041c009001515580c2015001081100c00da140f00914201c0303036590030040e861a00001c2c01542c0f80100c1200c2d4000103500101c41500038000e00507292000561080a0340341e03004007480410343c59500640c0031210040001e000302500d03080c09860200c107044082803006001a0200061401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 840309019 1250 840307769 840307781
    0xc0206060607080403050d1110060501080714070f08030702100506091612050108030910050306130929010306050c0306030d080702030c150109050c07150b0619030e0d050703080a 78
    0x40f03a9400760400c0d90780d035101850035a9032500e00000c45c400209803000c25400700301000e42c50501c54000d00c2200d2800300007034450300d0050448009c2060782800d503202c0300c41c0c10f0203c07041658441c0c6442e25280c1c2c0c909150b2402e41050310020018081c0aa040100004600034140942802800c0100c81d84948209071103003001c0900300410f212040d81c1c45000a01c0520074a402050610003540d501c1d00e00c2030402900f4a0840e48070003d200051040c080941c4035404940d03800c0481680000b079402039410007800c6038903450519140be26400c80300700c5400c100b212409040701c1c4501030a00060302e450303452040c5030004032207a903090340c4103c079030207c898401e90b502c5d5000320260044c6c928003c099403029041c80d00c0303400902400c08010004010141c6079114044e8002d00004d02c40d810204641d0354001c503550000c200b060041d4403500c000c1817540c0c449088841d500d945080341d0600c103100c0714025000d400c5042c80c00f80c0e14015410a100ca4a016008640903558556203603289503840c02d00081c01020 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 840310269 1250 840309019 840309023
    0x11030715030b010915023d0c090e010609080610061b1403040303030912020102030702070e15090a050403030c03020f0d0504140a080d18020904020405040f32010c0206060607 76
    0x400d48000a0750b905d121100c0039042e1180d50162800350180481009101c00100b044481640c1c8554104038040c0742030b803140241081c405000c1005814031108480780142074000c4110a00d0000000810640100b80c03401180c990070191121a80c0d886202041401584507207400f140011482c41095100d80b03218907030083c403a10344c041502280e109628a143c0094000b03c0100717079115085c17424002c20b1021107050030307001d10080d0700c0c620f04190002e40f1210030f44501c0045a41c048040f5400d085c143e008650244c00240c034404503440e2121140c40941801d0300c058010901d08009a240d4600ca03000711780410410340038551174001070f48100001401d00400643e9080601a400041241d0501913030075024050542952514140080001111a4800c2612450b0031480c1d8410050301c6001c52141c0c05070301100c0004030b550761170609050aa1505800904003000c2c0040f0714020b82202c003040b00d03030b0400031a18000800c42d81c2c1050342240d550400c000007503030001c8006032561410a0060003054 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 840311519 1250 840310269 840310277
    0x100606200f0f030a09050d0f14010e030a12140708132901061b120e0f1228020609041806060602150702011b050a03090512030411030715030b01 63
    0x10425251442c20550a10780c03120640e003000413007024459000c000c10001d480c046410102000e25541ea944a40c03807040001440d0103040744c3ca520024000b035100805641c040c4098a5640340c1800000749202c805443c8501c60910300b00c41d07007400d50041441180300d008182c4552505071180200d40c0991303441c00b0b00860b4800c0e1492550f02c2d00c05040e0183c2110202c071045c080d4015410400040c00548511501001011450403200049030f0510941c40d201c90150031f2401d52031620384041035a44503070000ca90b070040103800307032460300315800584140075180e98095081e41c00c0380441d140100311480c5030080c0d0301010034803284c401032400d0b80c001039403107002c4c8560032010f4030142c8c0c40000b0749400d9481000585c001561950a46684004c0560302540501c003c05c0007441019064501408041e281400c00901103001c1808a0080c1c0c04013204071341041c11241c0182038035661100302e0b401114100d48160704c6420f12001400c00080000603200360044404c904032070481c08600404100021038104 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 840312769 1250 840311519 840311533
    0x1409060c090a2d08211b031c0501061b1502091801090f0207231914160e01120c050d0539010c0212011b0210060620 51
    0x2075100484101d842d008443c0140d510512160304584621101d9014200603000807002c2000e4680fa8445400003c2040d44041d48904e08460ba07101c010545002403c684d1100080c00303550a0401d0700d00c50706035080032809100e2a0380303c80049601d9034012605812450100300b02a000509111460801a112050042c1090018000503003103045074144100070001d514010310000c41e56018243d0070200c5044190301d0128035035500381080e030500d1104448440141c0c210700e840202840620104032042c0d1100e5410340d05c81c14824009081c80e11520004c0c4244005c5280c0c5496003843d241c100e640913414440706a10700515549034030440401142d580340983c4c404917071592003500023032820f80224010503070081007904104500001044010b5050001304440307040354021903a1140c984400e2a00c851400302a20100e146606001005105542403688006952850542600c17424810b03a084410310590211500f04450842c0540c40010340305910120482084004415820015208071008 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 840314019 1250 840312769 840312779
    0x30c0d020909031315081302090a0b010309120e03161d0a0b04020f03091006030c2c010e0403020d0302040e150f0310060f0824070c06140a1409060c090a 67
    0x5aa170410032182d0804541500150341c00440c241c0c0c0520400d00d2901040c5a81d0005001745c1801403400c25a207445140b01e61050b442074201d5501c5640c8501c0510710f02b4500340b8041d00550a40000f41e0081c403840301c071607844400c44806a8120b8107103c54810142c60400b003c807005140c0180b210500f90303140c0e045000e454940c0d01c020305903a081550310316200c1c10400149403c008100101d00c41c800d04101050002c5800000310508031560440780034020081c0c00c61501031004c6040122050320000d81c000150300380e41c4204503102d0b0380300303034203890400d072481f0002da00300e002c0c0d40034900c150080c4500080c552000b07030303210040349203006080a01c10824003002a140c14411070012441305c1d241d810401881940c40d065002820031788000c1e00740002c0000c58146080c44160303001d020700146c4400f162446000d442040c1495401c908103000904001019602881d020f440c03800c8054503110f0b000221a0224901038010300014001d0f007800d4483c000a121250040c400555001c0300210001035 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 840315269 1250 840314019 840314047
    0x10b0904020d060e210316020a03021f0b0a080d030605030f0c04050c09060307030b09090d0c121b0b01180e0a02010807200f0d03050103020604090509011d060411030c0d02090903 78
    0x10100003018120382d81c03031030955204407c00c075115103031806540c050300403000080c1e004507494004903820300e144412030020291000c042c0200075402d5401031002040071a42d41000708284500086a45040c04a943c1e07600c103061365602e44080000ea82e400805000003546455080f03075800c81e90545a407418900c1c40700000d100c0343d0095072000003080d82c41d0880d901c0c2e810b00098490740950140090282d1804030000502070b518618401440008084c9206006a0060300c034200c01d0929640c03d00a05102c40c942810030181c00e0003a21810403050740006101005405001c15098401c1e015040001407540107486600000d1f1494040c4000000c40209001030300c000b082d0500070700c90041c80105001040c460609071000c0c044401c05084c00d0051015840f4070007100c04030341540000190a98030980318600424245103011038030845810001d5401d07a0020f082e5020328042c0c24403d50900d4010205a0b9030502e0380b40701500036a211902801618010449035807203000031050301d01e011141c0800c14 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 840316519 1250 840315269 840315313
    0xa06051c1d0307030e060f0f09370b0412060b1323010909050c0d0c1203050d230106050c0a02030a030915030606050d0905010e070611010b0904020d060e 67
    0x603241c0c2e800400e0750402c0c9030340b104000d0544042680c480d0f19081441d01100f1861188207a007203d8804009000e10345500c0340b06292a07040050700380803450642c202409188a080c182c03681d001da96100101051403840c070001c0340e007156084404401204400d03526040135103401c7c1238070f650001c0381100c0b441001900e030050020020307601d4540b189020460460742024401a040320701c04600d4032071540c0000314002030f5100f1018040300c0e4040442070318074110001c0d0550b5001000c400c1031180d030300e0040541000160080050200041c48400d1904001d43c2582071080c10012282000b4401088410b00400c002c00180c03614a080d5451a891900468501002a4421000120b840d00200040519612002110305032440c0600c222440c005000b40b0f6070040d4201f0004c21666010184208a401d6000c1c2c00f11a400e8030540b095150f541c0380250000641e20312640c0f080d42400400241c5150030000d161080d940205008807a50300354881c00000c0111401d0002c043c42071400c0c04c452098844904 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 840317769 1250 840316519 840316571
    0x30b09070834080c0a1e171207050c0901060c020114031008030f04051f0c0206091f020105011503020a02060f04050703150207150e030d0c09090908180a06051c 70
    0x703007500f0040d0010701c0310300c005d183e100301141c003081e044100c0981260008501242d5000c04908403901442c0013844c200044001400880303900011b03c0e100308000403c91601c0c100d03081340c0d07088190f0f81e80d400c01e5623240b89040c002800a141e01c03503d40c0c8660800c101858011401d130804403961a11480c0048c03031035002e00c072507003400a0041401c10403403410050402c080100000907480c1036107000700c0503186031a0000b00038440c14010402018503103440c1c0210700c2e403894088101c1c1030f268100c0d9003c2e00030a028094142540c01b0040c2004240b0301a00880d401000c4681c0100343c69601c032009040200070152040300c0780e000e544d40010200302d450a0010b40e0340005032005070784444e94a401e504440784010014940c60414422801002c40030003920202004000040769505180d5812105011560482441d45240107075440510030003a003d0245804c0601c02001100400010840001d0a912420000500400034515000000b2030341414110b400040030586000c01f00c014a210b030320600c07079 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 840319019 1250 840317769 840317773
    0x1003050a05011a070f150c2f0d0e030102090405010602150108061e33030f0c060702060c0c0d060906051305030906090102190309030b0907083408 64
    0x2405030010051040d03078018122a45403c60850041d801e90303520340a039400242606440d041104180007034006004070083c003540c420042172410400180070103000704030707404100c41071700704484924a2080c9482c292030242c03c01840d02c0900b008003210581910307407075513415540038040240c4503101d03800382c0b90103880a41c000d00b20403440c890214004000503440049190b01800500482c030006020b21541c440305000201d0003a514611182004140003c403610f1144c81c461003048031460049618000c1e4904034151001c81416803007555560b000f02c138000d80c0c850307000c000c80310040c80d0803801410300e400510151800b8102c4100003891022030706030b06460050710341c1a104204801d5104896000c4840030682090076050f1700e50300d07540c1c0503d00c403443c02804001015074140e8020441018075804806007049007500340d25000301945801d2008590b00f14000d00820843d11000c580c6105548007600103144400318103020012206404081800d20708800d48142d140301c141843c800050700320100 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 840320269 1250 840319019 840319021
    0x150d050a1b0507030504050913200f03030910080415050a0c0f02010504032a080d1a0d08120c0408190209011d013015060b0309101109100305 62
    0xc280c60080c070710340d10028100002040b11000190708641610b040d60f03010344900344156950054031001d407030600806071a191605100d054a060f01e050303a441404002e41c0d008401c890000185550303800b42d08044ca50190804109a110714811184030303a100f0b000303800544c03401480c400c00c1c004581c000c2d105001d00584450f03550444580040020082c1006440200480e24094a004040107082800d04103515650301c02e07801c07022000320107142120703046aa40c0c2c1c0e48003122100c03900184422007410001c50850201c00e58039241803800c2141c4c0c50b0b001240c0500d030110440e94003024440081011500709001c3c80041142c5908001d00b040800400d0602d10110445004000c4540030591198110b00c0c6056211520900c0002c05503044500c450344081405151540305186038103422007101c0c041220319220403d00005580c840015410a54104142a107403840a01c9910080322440d4042d030124a80d03600c00c02c0035500504544012254003400d000b000000610310318006180744000a032204 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 840321519 1250 840320269 840320291
    0x221390c10080930121f05030604080c0313140306090d020c011103070204021c0609020a05180a0b0d0606092411070b03040807110d050705150d050a 65
    0x7020210500805041c034044a01e00220403541c0d0300030b280c0d030310258407001c1c2d203001c000480c60310040312010841182c404e0716401045180710b411081112008a5010407202c44822281c00e40601020303114003402502c038658030398032003007105d92028452030030601c01040b000c01141c900504140c060110601070b5010030012104041c42c1803809400a100c42e00303c15070400c911074001880f400340d00800e0a2400d42d8458518036076066000b1b010340607400c18000903060b01045150180c841120107812801c112003903e92001070100d00400402c0d4010910400c41080d4256204c1d06c44048100020300c0328000c1074444110301602e400c00180440303d0394546006015282d04290048080c2010001c0d1040481b10325252049080e261418a03043c845122060901e182003842000081d140705240f4580d070381418500a2240d5000710400c0d03800c11a042e10201c0640303007018040c0d00b016006402407d04504000c204040080010040c0d580c81d82e00b0020043c0a103005d0054901c111402040050b01ca6144d03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 840322769 1250 840321519 840321529
    0x4020a0e0108060406150e06130e04120507080f030603100f0b040f051902130e10050411030402090a02032a040e09160b0f07021905010221390c 63
    0x2400ca03c2c42981071540900140310300c0382c0c0c200b141d0b0802c1e14103100222002c7e004140c09100314a420301d404080000085003d01c0c0c201191400ba520032040c01d0082340680204840b24000c84c04018070201d8104443d5012200303050265800c040c0050590359640305c7d0303003402002c03a0f400307440c01203240e9110340f43c40043d45014400d08a0b2004280c8081c003551034a2800700300386c41c1103681c0c9940c6584c0d01141d8850303900d107030022800c003a162051111244d82808005080704614610805204504240800c11740300000302c1924000c41d4040c01c4041c558841c2600e240c040d410003000c2e0605041c502e11455400c610307621120340380e4011400100d5940d410075a80150003800102a9582a800403282d0148942c0000c090003c030b4121000540d1140408030b00e030111442004c1d006540320403100301a000403141e03010010110340003602211a20544584402d80084800b411005985400d0140f001581840c54005480540f03800f00f0031001c25004103650100090b00b494640242d1090340c40320620300304 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 840324019 1250 840322769 840322771
    0xf05060301110f0a0509090411130b3001020721090302132003091b030c011b02130e0703120206150d03140c100501090207020a0608070e04020a0e0108 66
    0x203400034803441c030300b280a06125226166645850900000342c441d11684a88103480c1c0c008402001004982800d007850340e003400c0c00d1000c29100342c200b00848000d000c014828a9100c0c0800741c108000e5000c001e40c1880c0740c0c80c40a04e030030160f01507407220900e010400c4c4000c248041c424110142001e0540c46900074030152903030090b003400080081440941e890b400c0740d080d462031f20800440c0c82c0c0070300b5980c08211890a040c2850502000c0b091004c6410041460200c0300d070040b40c0405441d03440c0c41059a5001107525141c0411040303151482da40740d0203075040d061240050f081035000c0c2007071000001100c900461b003407215040741106204200d0100b507049071141d001d10003883d02c1c0c100010ba4011700b01d0b2030050140319922a0300c2c2c010030940580c2d101d18074014051005501c6020380b5003616191040440100d541e00c3c50b000011498480b01c0c400e81e0710300354000d00b8001080341480301c10303151268054000010320011111064803030307036280014004100541c0e2013000c011403100c0003402c844d030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 840325269 1250 840324019 840324031
    0x412050c0d030806060708040f090b010e090402152203080c070602030720011101050a02210f07052a1c1d01031d06090d02162420010f05 60
    0x807000c240008030341c0c801c1d103036034001d03800710f42450b5501303520b25281d0340c11300c0b4070b80c42038415501c84000000c6412003075001d04103c0c1004c6e00e411045000078004c1050300c02d002c40d8000d60165040c850a08031801c0e07d806481e2100466001c45403a41480051520b48085a0700c119000180098212500c2c10f05125800017444180000c40c03c00e1525600c09803c05140313807643d00c8000004c6280020ba038401c8580c1c200790020040200f02d40e080640b10840654010445164401020410280c20006010096118080035691024280c40c2c00f20100c982c0c1c3d02541e0300c40e6400003201191014ac80e14845609003100c4028010480b40b2020303186020a00d268404800502401030203004c034951402c44061603616003482c000070f4094a0030341c1080242099105150240b09113000c1103d00c0a00080481410415808548030042c011304019921f56080c052000c0740600c0408155801b48410031580d400141420f1520400074011011043c10914140f00341c0b5a83d103400d0314004100540c850703582c01c06 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 840326519 1250 840325269 840325279
    0x3010c11030703050904110d1d0c01023004080703150b010c022202040314061303050a0e01140c030a0e060405181308032d010f030201050706060b0412050c 68
    0x240c80301101600ca00030082c0280600100284401c0a950742e80d122045101c4a40b44050301c50002002ca00010141c2c0b0301050014881101b402d02c0013400000e1052800038140e009003070010000d543c0c82818100000e451400c9040103a0034600c046004025001400c0c079803008010407480d600340200040540b580c81c44005141001c450100d0740d000d4008207005805849c03640c80401d01c400f180410150307038100030102c40e01c00310307000c010821546580701041441c0f004445564071035131080a400061042d000300401c1040100800381802100400700005050500b6405001e035440c2400840d07001c511a04001d402c0041c0c42c40c265a004076698083c03450039600b80d0701382410480070603142c1c9103000c80e940f014000d9000040326125180401c45031607600910305500c07828801c40c0c0003004000501e2a01d62402c0b124103800c80d52a0740760b005412102541440100c0c41d00d980c0040d0b80c2c03644411010358006403030b1280803c01c00b6045008000800000c5003046c80341d0040e0601e2400c09408202940c420 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 840327769 1250 840326519 840326537
    0xc03060501140304050c0a06030905070f0f0e13050d0c210801260a0f03080c030c0f0a020309030a112107060302160501050708040b15131e091103010c 66
    0x90b40d00c20300c0824003442481000d0b41c0d940311800c0003450700402c603180ba50300a1441001007089070b81500001500c0d403007002190519074542e03007260710b68410340c0034648400c130034244104140f4480750302e03642c2c110501003144045074009450f02410000d0903808800400d10000750031041000c52111802c2c0070b9840c0000703869008400304014040c08041c0704105100c180c0304148203000c04942c5ea12000c40080d01c04484881001e4540801410311040043d00403c07206000650000109821a0711030001c001003146803062010460f140703508010f55845c06c40c40280044041c40c0c50410221141d64040d4030200c890b010404100440440f20b010072000f40b944019500584200004011042d101d0f142400340c2c841898100c0300d045003481d02c0e409015917082c00c0900c003020390440c00382030195015040c0c3e46116a111090003151180d442d9016402c815074603500c80560426a100d400044030008085041003420162401600d0280030142c036811820608019585000d1088259907030003410444c8071 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 840329019 1250 840327769 840327779
    0x132d03091a090f04021e19030507020a0302100504440a0914031603061e230709150806031c020a0813030c09020304050706090f050f030c0916030c0306 66
    0x42c0f840024030460081d030700890321001250f0841050500380e45940c001a40721400a480d607004a004880d0358400310f03290070081100e061000c00c0e443d81c0300e50190000d100444441c0b0320382004000080041e0b400c1088012040c40c4c1c01207140c00d94509a001880a1070791541144107002c852541c6110003028610410000469540200d502d03402c0700d10340b0b4401e01c100032031840403a080c81e41c412080700c030f510007012020003040450752003035407540a5403484c0324000d8501c1906008840009203401c45001e0070001c155441c2c1c0151071120f6001201c0d181c8101095510180d0603c054410a040d0700030810300020000c0c3c80c2010840031001c15a00c42d039100d480e81c0c0420b00a5111014544041c165540005412480c51000d5420000665100c1420a011980d81d40028000e41060f541101c03a4020000c000405901c118102c105541c00d844102008520b8041040411001c0c2018103400d4080c0c400c141100ba99035205440c400c5034410040c8a090780d40841c001c00710f50508842c1800d1501c1e119080c01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 840330269 1250 840329019 840329029
    0x1302070b06040b0120150702060a05070207180f0905070b0403110603060612041b0e060f090907050415030b04060603021507050304060302280e0a0e132d03091a09 71
    0x100180701178801c10003034a07120842400d05080720724800301c108602d005e01986c103900140d01c80c800ca090110402c01d0f43c58040c0100e0f12003065110748ec03040900c202c20700c80c407901e155001d558444001d200005e40045103a0306c250816038a41e0110341c80f6000807408205010f140f40484140c1213084400f03915602d00394000990b0341c0203615400240c9101d420010741000309048103000341100c0700709440b8105688030070022040200726400d6010f00609003203c88a81400742e00140210000d1002d05945400c00040c00010485101051090104107000001046d070407040140030385e001d020007140140c203500602c505030004034a03045030080d00b0031107180030038004401d80c4d06681007840c0241e503d060003107a50749403018060b49801e404e80c003401ca06900750b822110305a600d02c01601d071509160303038400203241c04841c1241e0001c85581d4002c030b11030004195803000c030350b402d001141d01001c0342e00504005c496050760240c11400308000f030700180902c52500b441a4288000a9881440c0c001203401080c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 840331519 1250 840330269 840330287
    0x1404260702060a030b1504080c13020909041e0812100f0308071217070f0e0a0e010b0c010e0d0509031504030512190e0a0c060221070503091302070b06040b01 69
    0xd0201350752015501803558400e84000d000440c0418059103e075101c0880980321181000b0451040c0200022120241c2290090300c0c0020700092051013075a495445004040350380f0b1002c0a03030214001e695030300094030785000d404202912110052149005004114550501c0d009404503000740c0e0301c10030020b0083c1d000c452103103a0040f1001e9600064100585504244080c050300341041d0340100f100243d4009000f03000201560750303260850507000d0520010000900990851002e90001840260056030003419108501c800006813040500c65640c204800c074614500040c0001600d9040c500d010805140150b001070044502802c1940d0040c18900c14085a940d40798515800600c6511148000500c84161030340140180390041403000c0e154404201d04a031580603180c0c1c00309456100040480c0e8480c0108031002c242c6005940804160300320316012655844200003180094444030304070442c1001840c800740c2ca6112501d05600c10710001403103640281c0c074140c40321015070f9004000e4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 840332769 1250 840331519 840331537
    0x20606032107020604060806010201062711090a170601080d05040e1302190603150506030402090910060e07030c1106151219151404030503060103140426070206 70
    0x4810200241004074100307000701c51010798000310106002803c95009007150340305141c240e0082050ba9268180006541c8950480c048036103e2001c010822410716484030254201e01041c050502404400150490700035801c12481544800113044801e0002c001e9240034010400103005120390521005009020b2485400f80e102000c00101d00490b080d02d2002540c1f6402612103852209103000640b1a40c405116400c00030349860021401d81a070483e280342034500080895245071078a07002c20200c071001403c1501d442c0101580480b0052040c4a130034000c0c0010b130b800981710700d8030f44009400c80d504030b44802d090200d43c810202d0460408209a0fa106c442628024001c00040b4041400c201840b014100c01d0b11440021191503440109010401845007c0c40150842c1ca84249815a02c11000080403c07800801150000c2d00582c00341da07000f48180740008011201d24640e203490401918181c5164030034000c1c4d00740c035030b8201d2030b1840340e071403c203800d140783c400c1369404145a4881c240d85 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 840334019 1250 840332769 840332803
    0x30c03031303051207020106080c01050405030c090c04080d03060303030f150b13080316110612041719080601031b05120a110403030509010806101b03030609020a050403020a050102060603 82
    0x9070404140c09282518404101945810380b1031078800320282c02046d1a0192400c0c2e0300c20005640825807141040341d05844010700540500021003080c8a201d10010f400440341410a000c0030422070810010020112229640400c4251441c28050300b142c40702c6d0100729400d814000030100c001c1c1c84a400300f00b1540f0601c0c00359655040b003050400d01c06651382050703c26002c0080d50b1010150142e00103007410340030349060b41c0b00c00b00c15401c200151007070306400d40c800c005140018020a490b00c071500000700c6180c13515890100c518015001003110340000c9404546000309100c240e59040c4210b012001d0329a51640d40507000e88009000ea0040c100c1d010f0304042c0b1540010420000d5404c00c4a00650f40c3c4c4d07000da21103490b403601401c01d41003050f00c075000540100001d0a54940006800071503026a03d544030b10300d00e0080c280f262045818416020303d91161070000d0407503141d2005000410f1140e0324161160304510420504500c40d40c000c0e41150300840038022142d5001c280c0404076614020 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 840335269 1250 840334019 840334051
    0x1809051902011404030b040b0709030c2102060705030d05090c301e0f010618150e0c0d0e061e1003020a0303200a051b010504030c03120f02030c0303 65
    0x80101c0c1d202c0f0119080a00446000ca030000030469148981070240b4032881d070f00c54159403002d004984031140792001030005044011304208104000e03107a40300d8040c144000f4000c902c02e03500030442580c0310282c2200c41c0e9000064000b0218428403130340b90440300e8080035101c00c2c943c81e4009074a02082460243e040d405c3c16401c0003500d0303041000d00c60a8841d5405580d0040e00141500800d001109450743c03240c003c0c00380c0f035181c184040c41242c0070340d200b25000c2181d0320b10351064140184010650403241c1040d0200214080d900074038014401c1d02000c5509603039040d90682c65056440c209681501c942c07000c0c0900c11941c02d002c0f51202c082c0064030300c5a02d140e0354842901040d12890f48007a4000c86c0b010b00100615038480840035150702d29100302c6007903a000f5402c09507030744c0d50325030b01804580014070016405441d800e480100362005140003814a81c603500e4000001540d6070040b9040d0b07043c49006507800d50404000c0c00c2e1441180082c40c20003a8040703410340c0300e1000a1003c5002206a0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 840336519 1250 840335269 840335273
    0xe0f150f040b06130303030e19020312030606070b0c030a11030103080a3504031b0312110c0f010f050606070314090607081815070201140c01060b0c0718090519 70
    0x2c4d1881e02c4400070390074040d20b50724140034004003a10200141c1e0382c02218403c4035001c1055031555100c59001c4c00404402120541c4041c82d80c0018005a5000c00104044004249010441d5020b4100310401950301c2c1041e01c0502c08071111300c0000341d104074003030004101080440040d60091182070410441c128840c0407001080400c2840b0705400307045412080c60f8803ea040c0d01c0c14450b40c42070300c80071001c024034540511031400d129401000178a211701d0700c2d07c1e1660036401402c81c041081c004a41410380cad915a0604114180380c000240d690740e1aa10324100040e401a55000b003400d5030031900d1b000072a100140700740c91000c90842c0742403000400703107000e885d40c00c01c407941582c01007501d0b616240307a040300c000071440c0b030610180b084041074140401c02c25402c045400055050f150700316114040d134285a11900150140d440e1950703504000a032003c0c40500414040a982000c1d120701410560500d150800080304070344010701c0c002d4600002a40001c952201000000417080300320418 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 840337769 1250 840336519 840336529
    0x314040308070e030a03080604020a02210703091a1602030c120f210307030b13110310090e0a0f060e030403230309130b0a05060d060306272a0e0f150f040b 68
    0x10180540700c0d1681012000dc103100ca4005e449840d209a5913100195a91074072251f10b150100c0c210f1700d480c40101300448400038000c0c0e0302d0148510180656240c89a140000343d103a110030403c1980f160850902221001d1b41480110490300540c2114408214001d60380181800000c0c0540149a52101c0301c4a0b039980c0d080e80d60310204e820340760034808041c803440380d031150380c0054480b02c40448010b40003048010ba5401034405080e4080700030820b5a00e15111440450383c021800c0d180f030f035503c1e865a60076440030320061002c2d500880b0312400e01d811071815141e108040e030b13030b0564580d00181b010b00307840d41d40c4003901e14100c50300c40d00c0443d06032402000660081d00c154851903200350000f03400c403103015568001e40c0859001c2d0350104964009006801203d01c411020042e0101c0725804c040d000900007031131925480b40d040d5419002c0c00764858901820409500700d203061f400d0000810030400180c810f02c0e54044104210040e00d03200c008007048464101244862203607403030f031600301510348607 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 840339019 1250 840337769 840337783
    0xc08180f06010b040302030d020705030c1309170702031501060c0305033607210b1803070602030609010b070f081608041202150316030c0314040308070e030a03080604020a02 76
    0x19003025181d142d41c0d07820a4070a16440b45c441240a40036240f8480c2c0460b0000c2081c4c411210f01a0141a0a65000c0d04000090882603014403e90f661100f0704404200100817a401081d0445042035031500c04d0700425103003070001495200041d242c440103002d40c650102040101503810304040b0b81700c0c1c44101e540f0124000540841810100d80380d0300031401c1c0e40d254180080019018151400740e5192040042c51031845074000c0c030f90100580780c2d103000030130740000d8652080d452203407461804001c203001415a031011030250340305600030040c85218500000110300610b407114583c1d01e4002203590340200d010310350710003a11200c00803030186600005850b140151075808254a0354a5450b200340c0ca20100f410711099001d000d40d65841040d000f04003046038000c0480103820520440c803c803044010707020610309402003588a82a4030000541000507902a07440394488803011300c0e115100a15a20a10340810301ca0f522003e54003011a0300302d00f125800c894140c4000d40d40303000b0014140d02e0700d0b207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 840340269 1250 840339019 840339043
    0x10306121a041a0403171f17070e0a05010e1003030e0405150a170f0c0d1202030708040b071202061003020d0f170a0e0103090201170a1b120b040c0818 66
    0x210303401c0100b010341c04410003180540300b40148039103859101140c4003034075901091f1020750040398000d010040c04843c0090382002c42c10125440c0c04d03290842c140b903950040c1d502003101d580f50307401441900b00c50700c40c0303d60102e5803000301580c1502d107440081410a54103803444c06a5503070808184080c0d0588511127040300b014091103e00360ba5102407181c1c3d0181d80c0304400d02070055250b0035090205c0817882807078144004000000c145017a031164800c20450341a46070952004001038400541c005019100800220001a0302d64410341001c9989452980c1c1240c1103400c104200b113902ca08070400d040640c6c1d01503520b205482d5240ca400040000001c802800045451184c0100b2901010041c00c441c141503980a000003c4c06005400f640c2403030b40001d01182d10005c5810114032103403017056026100301004900e9445c004011205a090100485c0015032101c4404541e541140600c86c11800705a03810410b002003c40002c02d800f0000d0a003100c4507103190607103100316000f0014816612 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 840341519 1250 840340269 840340313
    0xf06060109121103011a18071e020709060f06032d0c02030c0f0d090b040621180b0916050306070e031203011d06030d080a0c0203160c05010306121a04 66
    0x1a02028020940360508203451090044c900a403203111401f4803a213018540b1900d9000360b0300950308020040f040142140d100310710940100140c10f0199000e002d0041032a2440b1940c2607050003001003e50320780c0c00c2860500800072092410b00c4a2705511005da520720204c2c0061f4808004204900f548102c2c0e06940c0c05200d50090680800c0000c5100019460300f5150300c840c2a81d07415046a603030082d41310715004101c180258a1440c0221000c5070f5650000c0300b00000c1c44007441140000306003840c14252224840039040250b4444100400d800c82000001a0b034015480d01002030b07170368500101032104001e01c000e114241900c0820680c0c0c020646048419140e607142e6038900116482c1c0d4104007101d41c15030011071258107000c951420a420640c0e5000151f0361140c9400c0090841d0064520440c441004107010800e600c028200c4094441c107005103a044c6008001410b82c1e640750400240003011a1210b070010f280c8d9000350a0300d10882c28901c0e100d584e40d003088010103000800130b010340 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 840342769 1250 840341519 840341531
    0x40b030c04151707030b04380a0308040b2212021c080909060a0506120901050c0a021b01030906020705061605030601020c0607080706021b0f0606010912110301 70
    0x6440c600c00341080c0ca2144495024030903480701e080760350700c03511454000c4041204010808a42c8290010794403c400540b010078402180603c00d0604513040351003511231030340c82c0c24000012001070030001c4203120480740000e4850854030750380da00e48201c2c41208240c81c40041d4010140c3c102600028042c480b0403000898140d44189020381d000343d80f40f04a1181b41c40f290f81413004820104010f150b07030f070003016160414440e6001d000d94550081d1449a1107040381c900010150384a100400c400c41070702e14900300504001031170a09451000d01240745000c010b02c620b04801e0360000c1d40010100c0402008008041ea000045c0c0007082e0a46000d04814000980e000500a0004515010700c01003d640c01c80038100ca80e040310a0300090301c000b030051b001083c00b40514a0410060116140201560703858042940e0f2071900301d80c4014142425200481c460070380e007420502c150301c41da200c480003034180784c0f6000c030000703003665a02c0c041c0c00c0c421004803c20009010352040c0d40030650101a00810203 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 840344019 1250 840342769 840342781
    0x6081b0c0f0706050f0409050a09051b01020610060f2a060903020610030510110f0a0c0b090303100909030201151e0b070b0a091a01060507060c030e0c0114040b03 71
    0x862072403101003840361054180008000b8410701c00c031094600f041110506203424862076402600010705248403681d1a841900c01140051002c0484038028030910425202060006400d1800c000c150f0f60120507110020855540c01030b1000190792001d10701182011651401e00444042c3c29007a2001d201c500c010240c10041c083c2c0c07007000600d00035002c0300c10558858850704040d440c1804001c0c1380383c001c0100d031000000f0300c0d00f0499030142038009060400281c2041b010554200541e400002003d250a071000c0c404441155604203a86c1c8020750301d540b91000260714a40814881c1c0134141340d0f214800c2c3c00303044c0b0030343c01505c00d40d00140040c110203a0f5540b04003001090003010f19030301c00d0300031000a10007120000300c54005600886107400c540e02e0045d48402014040c0003036804e156005070741814481c2c1038404602800070f0307494040c0c4030710290502c941145c0e400b1b4884001d06181c103000014650000940780c207143c400346000725000040002c0f60f80300380129809510020404010310103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 840345269 1250 840344019 840344023
    0x90a1403030d05070903050f0328120f06052805032406010e192303100c0e0a0b0c160332011503260a0309020607140c04050106020c01050406081b0c 65
    0x107103a100c5c0d0038040c58070301440ac604221220001d00320b8408a01324001c4d44050010941151b03a03110144c5800107079440c0d4400200b1142c10f030400d81d000e03002024501050b050382d1107644410240c50700750000c0c0300009021500310081040001c00000341c600c81d60015206070722496043c104484054240111351a0225044101c4807a900855603180841400c00c49451b00032440442100f0008004142c40181074542c540107004841c1d151040010300318450041d074481c1c0814034001c0540642d0903aa44540110007070401c5500c4410410800485800b0408502a2440d0941481c0004810607545061001043d215100300c0121117255081a080c42139000c128a50b95007128011801403c214541281c6401d100c080743c2d8038000544c400f44108007a180c4a0b5021300c03c81c500c0a060940741000c81d40300d11103500038024040314603030303c104120f8100d41041d0151600400d42030000f0410b2111500000c1c00600960091108120030140002c5044182d070340d030485460400701d03a9503a2080003000c07860f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 840346519 1250 840345269 840345277
    0x604090f0b09060306090a0b09010204120503040305010f1a13090507091a030105042105090402030c2701080112021c1209080c0a0302011d0301050c090a1403030d05070903050f03 78
    0x203200d0742d221400105182408184103105149080142402c80c2c5c643e40c03032400b544405026210150342c01d02020071880f52011280260701e008070019500d0317900c4e502d465030a48402c141c06000312400d0280412840940c401c00c003036070720011503550b0007400f440d030015002000040360240030f40c8603446001032048507540c400504062a200800070440c840424182078500c295802030000426040c0342d4507421102c40c0e031744181e110b50b00c0d009103092800b80c0010282e801c10f40c2e008140240000d040480c2080440c000c0d0f01c401c84410b02074500b5441c8038006000c8500510070540c840020342c071344104640d18005015549a4041450541c51516082405400c420240803e0100e1452840800c5c90500090303031103102c1d42c00801c10700d119070130340d40115103811024031203041003441c0e07600d89102e80d50b003070199600c00c42030000115191004101040000c900f65408541a01c02044a04900380c60200849a14082800000c986620b41000c21106548154400b903d507000c4c4120b05294044044020 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 840347769 1250 840346519 840346541
    0x3030f1a0112053c01081c02010e0a0305090f0901030804050910030c03020d06020d18020406050604060c020d050a020d110301050a060b0a1107090204380313020604090f 74
    0x602d0821100d04040c40841d80159116080b064480c1000291410410303048800148082c00d0703800c1c140d00a0390f20030000d2000ba00300b500d098001e000c54103000c051002041190b0011480240722010311440310316150402c046000d0b04108000468080c035880f040c4401c041544081c05088166a403400c0000c40d540042c01840e210315000c401144000e46c50520100540c9c0e0084c007004643ca1071582006540c05100c001151000d8003800314409543c00c9109440403500d05100f20180350095204220071140d0075007009200c0e0f1010703c01408a0fa0740030b4103480003180d066820720421122401c0c01ca14061054400942c0801002c0710720003008440020140e074404240c000f80b015485031705203e01034902c20302486030110820300c88618800d00c03036210048200400b0064496040d1114000002d0707901a4112850348006000305610b0f1102840c10702400310301c043e0405c2d06007411040f191401d40302c09000c0014000d28650040c0566640ca800c4400a052815040110304424030141000d4410180380d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 840349019 1250 840347769 840347777
    0x41401240e2101063204150e1602030f0d020f0702060304080409050a050f0604091b1e51031d070303021e0c062d0405030706050703030f1a01 62
    0x5e688240d640b0420510b0500304060840b00f94451881080400904502540941c440d243d00030f10034000c11014000d4011850444814034103150141c114040807946801190710130862940e207100d0700015036102c90000b0740c015a80300104070080107940202c8001030351094000091004006010005004891020341c0c01d000c2aa1103000c04421900b08840c0050b0481ca03000016036545019440010203034400c00c40c2c1569284412403401d01c000309a0803d85d8100182c18650b40f80c0c1801c01201402043d00080d03034501d0030703004072040c52165080c42c0351400c04003105105a26020583c00c1e00c08a8904142c0e120f0001d0f000120020058003c00c001c45503c0c48902140c000381039008205a41560340580090444032801c08580c0300c03078182c400401240303000d007441c28403007a5202401004680c4107514560b110b190361605c0f8682c299400900043c1c44441040100721a48010500c81d040741c05509080c0d466a03640d00f802e42c0540464080302c0d036054039040c0c51aa02e2400c940b031411201000303070b0b5 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 840350269 1250 840349019 840349031
    0x807140306180c2b06061409130206070507090f0f1a0f06090a08010f0b01090602070609030f03090b070309030605060105090a09020307090b07080306041401240e2101 73
    0x88012940c2c0162038260707500030020650366400c0480c48102251078504680104850102040344400044e45044500588400b42000340514074081030242100442d54149a42001d0341031a0142264100082c06203801040c0d10042c02424003e0b0701c020f040001d002e10220842c0013070b410041c80f400e8403440e041481c00c03160040c0c01800418a6140050207071101ca0075400d6401000b916410600703540d540b0040b184404181482c084c05848048910b021021601c1d040040000d0040f040d82c0e00a00304552040c4c808100950f40f0955020072a600038400315615142410300312004490303500000d0700090002048002c15500094500840e40114010041c90b282c48004407898805c1c42e0306582d002004680c14440b41c0903c0d0f0082d90041c0040c2020048a07542e40034a45603070300080016900c0e41d201104124007420700d80501a402c9103002e404401c10340c182070991040148480342d21403050206001c4017405801280310003140c2d4001440341e480c191400c000103000c452020154051542001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 840351519 1250 840350269 840350281
    0x9060310031b0b031306060807030312110f3405060601090e10030822060c110109030f03110705031e010614030a0308090309191d040320070807140306 66
    0x14402c03100b40c481460b081072130340e100c0b44a0041050518a820754245c0d60705d80380010402d03010810280107504c03030f0310b0f01c40500b032a0480e000c0864041310111031010f001004006800308018007184d40c101500061400b905e17250302c0c07405510004042011030080d00b1041280c0900c40d00186aa2040e4001d80c0d9800c01c8645900304980c1646040c1c40c003040e2008003100610008040e8405040c0c030800e12401804000a9015048210042c070350111020450310380c03240c0113005608103400000507082c2058480d0502d180c0c1c0b040d6181c003100c00080d040002248040210000522418005042c01004c80d035246144a004002c041c86c0d024043c820340d0b180103c00140c150b108c03003035020005801405840c042405480c10f441100c0e0092440480d404100b0100346140d03510860710f000480c240d407041c140907003881000a2424004d440c5400550007000c01c22001a40c05621690703041c0d081c0120440c03480784c1c40c600c01d14007a16034000c4507442c0505280491400c040c0c003455a40030a003142103a00c3c0361104 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 840352769 1250 840351519 840351563
    0x31d030a11031b10111501090c12050114040f020c011d0d030e06011214010510030210050304110609030c130212070903030203040b090d140d090f120b0402060906031003 74
    0x800383c1c0942106808020100607401103113038007056288842500d500c0ca64011755020300710070903040207481070380d521440b52415912a014016081800c5420821541070080781400d524a005526200703945070f01540300300001c81c1d01a5040c0b825540300070f000d440301542035400240300c58220500d0340c1c859005056880c0b4424003641c07280d09001409081141d00742100c1042c1101c001d5000d0303400b00c0c0b10529060701c42e00e00344545441082442814402c50b0304510401111946c0f1803101000c00500b4014840800c00030030b42078070f484108688041d44c541444010900f03041002e00002e500c018000a90070040503650020705508241081080382c694440400b075500085601010f07005900900c801d00110400078004d004e4680000d1011103000d0141d0749882c1c0041003040c101440d90000903014070200c0d0000d5088010b0701001080600c102d06114440c1d922070f1002c400070706104034410219042d0344a400840d64500c030040d181c603560703140041890304040c506220032610b90100d2070f07a81242c00d041d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 840354019 1250 840352769 840352813
    0x30b040603021c140a030f030c0908061f0807170115151b0b07030c030b01050f093a05060a050c030f040212010f0e060c040501080103031d030a1103 65
    0x402003403031404809040708040c00d40d181840888101130b204818007261401041a80603c41c8030369a100d4103080e510030000c00762620045020140561300106002020000c264103501518400214030134074910304100c00d204d00580d000758024010880081500b062020004000f40b00807402030101c4c000e41e620b01443c800a503c60451074110a1184034072107403281814224518011100041d1440582c550688070741007a0340e0800403a40d2003588520560f09401840d10403182424020f061151a540140741c40c03141071806845007106c0c08004020072080020749208070444031040c52000e10b50144914150780c500001c0d140741c070071400051410952030068904ca054a4400c05045072181108041e5030a4041c1080340d10400c280044500140c003403160010740f010410003c605d082c0010f580d642880c80240540c070415800300f00910040e6044802a8112907041c5004d100300207505044800d44941c042e6000d0341800381e1409502480a28002124015000c030f042d40d4001c07441854503511281 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 840355269 1250 840354019 840354023
    0x521040506010611100507030506091b030a0903030e0708071706010f030803060f031c17040f12050706060b0a080c3a02040f0f05030f21121006030b040603 68
    0x404140140f00441c03103100c040c0c0302d4040d01803c4605043d143c01004094070401c64400c00000e0740c4200300086490070b402c00d540c00c0006410b0090b644c0741518160a100d00c0000c1464074056116190401018881e5102c41201140b09041d42c441c1507d4010041e1982d586104a1f00301c44500c0500703550201000ca4444d048039040c01c48400c017285150707036403507142c4c00c0140660381c007420b42100b04c8400d0702c00307010307012107503d908481e071f060008190341c050038020107550070181024400c010440045ca07481049100c0c00d400107085103e200054204448512400800901603420070000054009c0c0300000340003140300300d0300e54600c20303a203103c0e0b0039080e03014559078458044850240d0345080d94080309801d10701101045180052150041c0440607030707100d0741c0540d455002070b0744208400325650f101000600003c4000c2c0c80300b05d0b801050260344081c01c40381056542e034424010309910000780e08071401c01c5404d01080c0018070b00003005041201ca10b100781400300c2d062070140c1200f480c0a10420341566 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 840356519 1250 840355269 840355273
    0x9030904051504050f0108030a030c0512180706050a2a080d021e07020607020f061e071401110d0519060b190f0f1d04020f04060e0418110d06020a05210405 68
    0xc4020027003100034002400b02c4400f808010400b8201507800c401e2207500c00c1198802d030408000c0c0844d641444c02615070301c508208101417140f10440c40c0d1025411468142d8604081c0d03001c041e00c2d640c900c0c07910010700004d02d8030350000b4444a54030b000fa00608146084613a10741c0e00d03c1040c440c110014801c030700c4001e500c240104180c100528010111000000c1c018280d54140043c07000c0c0c106034561b005c95408070350034020506908000c85e01202d00706050720f410017841601e2007041044681e01070345c00b0321418180c4131760008030b017802c4c262448a00b6400e44002031003255a104110b42c00d07540a008c1c200d40a00380090b160910b64081da030302400c501500d80d140448030178502c1b0201c038403074001a410154000802c282d14025520f1780040c02441c40502c5034182c0e03603840c0c8070018084941c03141446000c0c0303003407924184072500042104031541790401d118008140c103100000c0c0d480c01d603204004000301d00c041440c82e130301c07170703103d4054041030f200003e140044e010180d000079600c0340c00704c6e402007030707a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 840357769 1250 840356519 840356527
    0xd081e0105090402010c06201305030d081909021503060315070203043003020309030618060a091506080c030709090b010b090a0b070b0f011e030b09030904051504050f010803 76
    0x1944901036040d00d8502442c00041d080d1140d00c1c003e02c241e0091500920b001d40007089100402159503159001010114000d0000ce00790030005440d00c079008140789100b9407401c0c45040100a95000a403002d0381c000c0c1103260031140b40d00160f02d2a00244c0799180244a611502440c42503400d840381d00403115a001581058a000c1d40c0f40c407440c00500c10456104403261404060003038012000946034400c0d005540c5981265050500c1c03c8402400750022031180c2c0c03d0b009500b20007107003c1385c02c40141100407a081c2002e003428011050000505031400d86410f40020f05181c0c00300b9180d0701d80314102c0071b5480c0701d9a521041d1041d502034040c05408184503100400c00250711b8030060007001006004840351668807001007446070442c05095401c418850200304140d2641300070030707000d402c00041102d80315400006030030a0800c280002005001030800bc00c20000040041c1d8081c040d000308280503c0c40c2c4a130745404210140340500e4060380c2400c011038003802242880a043c0c5841d44011424 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 840359019 1250 840357769 840357773
    0x180b06180402061303050601090f1812030b0f13060303020708150a0c021903030c1206080a030e120d02100b060313120c08040e15040e070603020705030c0d081e01050904 74
    0x842e41302039551a0b03031030780300d800000c0010424441c9900a00266100103070500e010748100c400d45540ca0000c403518025000024001040c03840c008802c1102131400140403000c2e400869145000c10f404541c0c00044081407140c0840e85030030100c203a034829400d45042550715010b05a6030902d40d2166a00c20a0007000039902154552100d541d0140b00e204880700c3c3c0082100540814040103000c2d00000d803690070712890142c1220381c4401c8211204000c1005903d0070654984682c0c88410007000c02c10344406041d00c943d10910700707540040c6403034151a0000045030000c0e60b0382003030f00710024845042044085491070101c4c281c03882070300a032a038241c04030f80ca03a58103c00d000701c4210303e00902c4403400103140800d0a51002e030002d80131a44900d01c0e981042e0204002103400101990700c10790a0207000070702c0840c085050b0084491504000d40c8900641c074090741940180540841c1178400e200030b803009035034002c0042e03000751401f801c20700030421203841c0070700c00082c24003a46400c00100c10201340 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 840360269 1250 840359019 840359029
    0x50f18010905220207020f04090302060f1509180a200a140603130311010c030e060624070f0206030c03010609170d140c1c09060e13180501180b06180402 67
    0x14421b20040000c0c1c00c01c0d0b80c1c0703400207089440b500ca041c1c005034014800c02a809640c5801260800c280034208460400c1000c00140c01120003009003411414007ca4104141010001100c00940c48003107100c6d501060654180c0041492210510850341c0b0080000ca500312070208422400019000c540b9540c1e4565642c240c1c00c5441f4007c4040003400a04400301c0380003803013400c1d40502c0654000c2102030190500501d4008c026000d188181d90341040000c0b00058403860070041282218a20344841c0c1500340250b1481074080043c1d08254004108110b03011420020b605883c81c0e6184c107071349180c0f90545400c07411030f008542802d03a4000390754051100c0c00ba4121858902c3c003000601c0c5400803800d409410094550301c01c09440001c030708003459498101c0c0303456000d400c4600d002c030701440e5084000f5240d40303510506e04041e965600880709a28040044100304079030044001c0c806100c6820f420042d0408982003074420400000120300300303203070040c00c2c1807a040402d20504803680f100d4003048 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 840361519 1250 840360269 840360277
    0xe0d080105180720060402090601180e18010204140a0b0f0d18021207091d0601050622150e090108061b210402090108010b090106050a050f180109052202 67
    0x240130304c1518074010f0130780741c110036411448030030b41c202803c01c600706481403100c2c0c0703040581090b06000a08403e820002d03e02807155040ba045840e09a9150316181c81c440d4202040c0c44226406500006011039855155107010002000c140c5034280e41a91307483c0c1c2412240100c5d8601c085450082100c03a482d4a103d41010280030815443d600c0208880d0b80003c401c1c1901d201c26000303507085540200680c104601c29404007d01c4072a4510b410386e1000700a60300e6460501542d0712405000c01c42903013105421716040400035000180788105a1651072200301101c031503800c80c0001c0c1d080e012603011820b00d10040c504030391036440101a591180d217003203100d00b0301c00c40d030300f400a030b405000810400c81d0b0342e601c40e110800b008581030030500b000d0050100c2c085058000c6d079082c1c0e04040807200381341c882d491000d0442d0010f00c0e217581c4039042004119080d00c00c0040381e00880d84041004182021005041c42013507600340c0310703400350136660011b2141c10b940c1c80402d46400355400c460100340c045903030028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 840362769 1250 840361519 840361531
    0x12030406050a0209130b01080a0b060a0302161b03140d0f0807120213030209090102030c09100c0605010f0e070f022a100c0b0106110c062203060e0d08010518 69
    0x54280110000070508021174184038070700c9143c07510801042941c00c056a01d4018800c0d82050004118000c042162881042000010543c2c009201d6030310507210800c0c1185942e0001480c0105c480940d000c0e0361446290005890454007080d070007010300b10000714a03280e6280d6031244200000301d5031090320001c0e8014a40c200f4404401c2404002c40c90071f00c0100716803400c4404481a090444c0180054440002c0151000b45e2042045c8483e9035451000d480e00c081044544442e084030208007100c030130b01c0c018002891340c1c3c00d01c400030030080d24a880360300c26100c03009203e003945c0d51600401c8410308202c00f14103001d41c01c80c40c0c910740991801ca03100d41c5607054603c4060480821a008981e140c0e40305044c003c001340f4561102e0303080120550001d401001d01d03251221105c04924041a1161101000c46d0720405000407a0002c03840c00c0c4451801d401c1d00500d200034095641d0808002410003095000031074003c000700c1048080c000c80105060724009810084500d082d40e291081c045c80181035 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 840364019 1250 840362769 840362771
    0xa02010e0906240a0f0c020f0402090607121d040203060117090708060108010e070b0304031d04090f0f030f0f080105210610240503161103210912030406050a 69
    0x201d0b00d0743c202e40c000b0621410300d142207850b0358402544008115140a00c011010000040300300030150703480140e20040c1c403204070740061b550b448040014510340b21b4410000c0010500034410520781c1e400c407100c00c00602105103218960640d060400c400c82c4412503405010445c0c40c220710035003030841d0030b4403540444103104891080d038646c5001407a11900740d0080403269160005043c0881c4d081c824800101a40d01c07040e41142000e40d000350088030300410341040900000080550781e516504010311468000c4110f1403079400078141700d1304034120100241d001c81c0c8040001300145110300420a0500f11310340d50508180d00b80410401001100340600c44008262030500c001e100c0107104180c06400360246070612149401140c800c030400c0191107410603882d49801030031041d000021281d022010340c14070464450707400d0007910744001301d690264441c40302203a9038030265804860841c0100c2c0074802100301e5526021450b40d944170000107601003101c28004100012a01d82180d5001213100b10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 840365269 1250 840364019 840364039
    0x30402031b06160b100501020a0804090c050912010b01110d020a060b0f0a0b03010305070801140a02070507031506030209060306070203191e0827030405130b04090602030106020f0a02010e0906 84
    0x1020f43e00032868284103070742900805080c060b03280a00005140100310130b002400c400c0102d031f2a1042c19010b240f0410844035243c0451026052041c422651511b100408003181200001c011500030700152807024041442102142520040020940c00e1121503a00402d00700c0305030ba40d2000a815604401d40d005010911501c0c070599401c8100d001800a000b0f690380c896165003400c0349008070079408440345902d0603860ba0001c42d800ca95003940b041c0c03204809640d680301842d12070325140c03450b84090120210400301302c002203003541258044038001c64446405448134800c00d81c8903002030781c3e0200036900805c8540b003e828010311000000303049040c002c1580081d0402007000b1000c4449203000503941c003080000e0030140d60000051398070a0515000301086058040f07903248664000d081c85820340c2139000d00c1c1941250000c4074120300c0a031092080030391501d0004041e403c20b00800000d03006074829401c80c613800140e402d581c035405a5800c000780050501b4400b1040c0c02a040340e130040d054803 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 840366519 1250 840365269 840365287
    0x6040c03090b060d032d17160806122a0418021c0501020a120c0807020a14011805070305010e030f03010519050409050c030c0f030304170a050d1112030402031b06 71
    0xe055041e101580c00011b441e05669440003082c00000482815031003d0000601800044004802c2044005414003a0700c584031140090005c00b03072100c002001d8440d131f0350144050071000300c200c020710400c05c16900002d81d0340da00300000c2e144820046100c1512010ba4480540741011441c4400403501c44032102140356921000d09a03441305103000c010a50f8000400c1c00001103203c1c80058004a00d03100c41a8105188000e484a01c0001d014110601404101c0381400003940000881c00000c541e01c040e2250703d2404503101c0b015840f055540c0d501c0d0102098a007140402101c901844103c1642c0c5942e0900c420003002402809200e00229030502004ca841d8940c5e200340c04031580035800400d1180348c403504240ca8540f03982000c501552843e841c20000c0d85002060f2419a41c0c0c0a4600e8031402c01540e01524050070464050000d124040701039410b01d070003940c4480c4900384242038074000844c01642407018401554001c2d090782c00840c140c10903e205e1102c005951000401c2d081c503000c3d001e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 840367769 1250 840366519 840366557
    0xc07020402192a11040c03151715070f141603030e06070f050d0e0f06010b04150201020f040e0a0908040b12010e090606100c05070b0306040c03090b060d03 68
    0x80c114201107030411039056100d80c410540041d1490511a104202c00c0040d62699414130a2261441c05952500c0d0b0b8160424000d0b0440206003c910890220301c40c0d0350b41ca041e0300c0380c0541d200e02510707001e1f6030308020710480841030b02d912a80d81034880100c6102080012030307000b1500e1a41c18003052042c030408040d4181e81001981d603030700940d00452042d10200100c0d05280000d0100c400b4410840c1c07143c50150303005800e440c901d6060000014124440b4003d09060032a0b0915000d100d008541c004580c036200c1304054005d8540010100d0400f84038440268200e04c24030701565288403040c842040821800a20140d218014480109020b28a0780d100d032000d4101380c00c58255000d010804181c00e02020758000d0040050022488160910301580b607220031000c4c0c0102d0181071342c800c81003400390007170300b0417000194044100c48465543d48403c0f2400c1c0c009451080c481ca0a20003441011480f83c050454290b8002c03080c01030b103031a00420030040116a000072001e102c03c40601c04024514 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 840369019 1250 840367769 840367807
    0x818030712110c01030902011202091903081218210c01050405010605121612080f031005010816120203060a0302060c03071a010e0402040203040201210c180b030c07020402 75
    0x141d511900042060001120b0400400c3d080300b604140c54042c800c800b50780d03c400d0350107580f01900c0c4016a585000c501083c0300218800034401e06103105880002006070a0000381004490748103842c1d0540c03180e04803a00c02e8060f100d04140380d5030021000c1f850b80d0800300005007074100c03540e4071585403e54886d8140c0c2554030442e41034440f40d41d00c90081182c0d00f88126108101e80914016050341807020f9803c40c107000703243c016610106a07211012081000c1c0208032400c1e00c05080819440e40751043015403008000f18040e0a00103480840072a1001c249140c5102c030b50010350311a00900900074003140b00035000108040e9008079150400000350716400002d0400805481c050340d078bd41c405007004001440c2d45501c0c0c81c00b03030040800400002c201091b000360811345c12100984d50f03840d10b000403a00140400360522003800701d06078200364444543d1204590702d2540e00c44581c0604982003110701c00000f0f100f104848601000000c92500b03190004007119480180010b080009a80c6041400c0507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 840370269 1250 840369019 840369053
    0x70605070903020a17030409021b060f0a0b0111030a0809070b040e04110108010b0f0702040b0a1205100509100b1503040831050103050406110c2a0108180307 69
    0x115080e400c0c0103504001c00454040c100c181102c03007540c01c11701c21480e0380c1d2283e407141c400116400b040c060714442030307000103013a0241100100c0e00daa09040b42540303040f6038140c1c3d1110203681341c05038060f0294083e28281c481d039070404004d07500f86074129400b540ca410005080c1c2a082c0500707a80890b841701203401410103800709032000e4007a0b02e444d16004138035042985501c1c0c18400700700010040003003544100c03000c0e01ca08007031050701e4900782e10209014180c4489480d500c1416001c010803501e14118003200142c2c000c0d01212a046d05500c0c444085640c251202496500502c00400000c48640c019608045000d4050200380d202c0c9400b01c1c046030015541200e141b00c00140480c5600386100001101c0003050a200d0306c000b02e0314000403070154982c4104ea05140e02c9100007024492143c1c80784076901070394070600b43d41c0c0c030b442c0603602c0e02c0e40b8010752041c12552024a824400e808800502c103680078068480380042c3d1112a42801c181c09058032404403440100001d00c0000d0030142c2c0b041d000e0b5 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 840371519 1250 840370269 840370277
    0x1023035d07051f0c02100501030c0317040905180115140f011e050316020607020a060c051903021312050705040506030307060f060f09050f070509150c0303060f0306070e060a030207060507 82
    0x4800d800c0c009046c00c00401950644c142014018000320300e03200641c50460745e010380c00d0580840c40b4041b0018502a40c2d00030300580380340c030003088250400ea0030012985078039107000300000020901c3c02400c00d011400354240160f0000707903201c61820400c824840342c1805040001c03111054000d403480c086540582d43c400030b4000310a00003c2920007201c864060f8060000d07100030314140400a54a000b9440050300d06911040d03105070030360040702110b020300e88055110146202203c800b5029521442c17540321406c20001000500d0303248600c4038080e40c1e902c040606051450501000080c083c040d00d146ea25000c1004000b001410600c00c8446080104c00e000c900b161034110f07402c00051143e0320800109040008004c013115448001c03070350007829401c103203031075450f0350001c5500d00f80072502aa0328040c000461601c02035000018501c41c180450f40302e80c828012106041e00c4500a940040204001d0401c4c00402d103401409080b00c0340705c9180060400e881da81b03030801641c00903507021004ca = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 840372769 1250 840371519 840371531
    0x12010306020c0c06040b0a0516021c05061302150903011806060806060609010f18080114090f030a0f0302070204020d0609050f1023035d07051f 63
    0x8800700f070000d00d207004030848034982010f01d0401492001d10950b0410382c200031001940d440c802d90380815514100d070b009480030030980c030b064000fa51000c41000d02518644250000103036484041400250710a078081d00c1c8014490451000311940e17004540700681c1035403070300e00c5102c503102400c4143c040c0d24064074000c5062490088041d00b080d402030040c5003d000101704000e907503600701c483c03511003082d0391821100d03000f00c0c0643c02441d04902d400002d56542440b00001c1e5813900560424001e0040b00140e07208080c2c0d15032069600e108049498011400c80d90841312014005d41c01f6008941c00648003628088800110070100c440300c0d0407400f0300b1a5100d00344407803c041c9090b030750b41c085880042400a0390901c40400208511807106c1c8903011120202ca10854505224590001600c1107020340c1084c9290702840003541e0b010b20302c81103400c1d04c015640340d81c04c66080d03a809218040f651010f0990f082d02c5240c0e50360380104c405840903c41c001c0c83c0c40d08045500998003071205009000540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 840374019 1250 840372769 840372787
    0x1b031c0507030204030c140f030d03020c07050d050d05160f0804060e0108250c05060a051902130501111e06011a0403020a210f0c1a0c0606060a02031201030602 70
    0x4950015080000b014414002813000803e074a0003001600e44240031442d45188100009a91151202c05944c05028202c0080c0400b50160040c2171143c40c0c0105036504a0748a005222540c1d0060b50043c000d907108040d00545607010350000d1041000c10200301c000c0c2d23513450b01c900d0b0303100803d00307003c441e8040000ba04215981c1e020920b040a60801d10704050f040c00e001d030480402a140c0300442007048000a108003255000d40072107150141d0020644045252040f280002008100d808420b0350250860a40b004c000500c00c4459048200c460b41440d40d08010044942c0c0310240f00d404400c2c8185c000040e4420686800060141c4d9541d004220560600040320003030085100300c072075010410310080c00165600103001d0305803640ca511001c25852440d04a5100200102001e80070584d55104d01041c04903822001003580d4642442c1d92505801a203101c501d4031684081207103681029004c54550314140009002907580d910480b4100412a050340d140d000d000e1b40b0885010380d0000c0e0f9900 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 840375269 1250 840374019 840374021
    0x615041211010309030e0f0105070c0b0301060f080702101814060702010e0a08030a11071205041d04110d0203160608011a04121b0e0108010f0510050102030702061b031c 74
    0x4003011082c41c06100c0c1000541d0046d29102c0240c1c1c140c0d1061a07500301f0034081d41d200d001074a6000d43c0001050b00341c03030350710442601c0c154030a000f40c0340041d4200341c6600600d4010009180501c06607801400c107031550000100c010442d0304042d00072807421115a00208150071156000782050f20301901440c14204406401c44103004280ba4503500524400700102e842e240a03650300450809021518850f0701e81c283c90b580c4075070000203001e02c800050700508075038080080c2c4203684110a1052900211881c11608880202e070020084814690074160303900302030120321a680e00c060115a40201c49a5030006058000d801a0000601040041010003401c011840700c003190040c1d82841c0a00f001400c0d46041074408010301650f00e044ac2070034007002c00b075804500800c0351030110209561a14100d5020781140f040c230341207407420000410041802c040d200e40483d10705800940c6031032444c0c2c0c01e00020350802041540f11000560201e400c132039040c40206049894080341c2d0700501c5003140460 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 840376519 1250 840375269 840375293
    0x3090f06010f03110303040803300c1c0b032e05090c010c0f0203010603230c101d100233011205031c27170306150412 52
    0x982503801000100700208000302041d058a070001000f4510101400c042481c5215a80c801c021030301c000101c040e0781c0403840c144880341003034010500e0220300012181142c0104203558003628810200107403080000b15400500c045510408013150350f4030b401d4006400c105203014486220074011741270b40c050a250071408032488011800030081400d201d05104e58621151090718140031aa03010803041c002c80c4504141000e90080003440352640742c0c5042102803818048240c00801003020441d00540c01066180351000c0c00f424000743c5000509080b112001e242e13074952144200e410814000b0344a202070902c4e20505a0000c1445180420092340d02205da4020421106000c4900d094407c0c081c0110740d045070b103c0a0002e4440c51941066800c5100388034031340498034002c86407420449000d0b0400112039508504860b001011202414110031089600610007000390001007074540343c18000c2c40c2c101c4e001425130740200040d1601c6400c40c1e4440d40010702109203a8040300204113544c0f00740 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 840377769 1250 840376519 840376543
    0xf0d03110f0d2004090e06041a1e090c1528030905150411060c0c220212090c0103020a050904021308030414040524040c11030f0705010501050f010917031605030309 72
    0xc1030755107023545035505814088042c8001d201510b03004580900d0300110407130340002030264030220030b003851480c2c0d81e501d0a110381e850340241742c04041e50f4004c0556406a4015014411401e005034441d800d2a8121018a540d0b0005050795079260f00d010560801c06d60230002d100b03000c6500303107081c00e00b4002016000180c05a1049000304180b0a41c1800811002031901c0f0680d5420100000940611800e464080003465010302c0420354903004010744c40120b019401080a54840ca40c50301c0046069100b10407543c0089241046000c01c0e5040503030050941c40c840c02c0c810f8a1140d1504001802c66100740e008202c50140e14088000c1071170f00744195a085040708400721340d0000b401c09060086103c1d4468148126a10044041c212740071304c4034568041c080c0d100340d942c1d8120340e81d111125a085102d0580d2a986070000104403418031507128816088140c4a46d4a06450303d118141300c80aa1507659000b0701043c400e500215407060040d114251140c0003850f02da01c2d1808060307140210100384 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 840379019 1250 840377769 840377773
    0x20f030a0c0215070c0b0711100807080603060903040519080d0f030e060402011d030c1203041a0f031801200714120a11070302060703020f0d03110f0d2004090e 70
    0x400c000505d40742c905002c840711064000d40f50030b820300b003418400d900300b0243c81e045540440c4110390a580300108a10031805525400d12726203403081855620241111500a9a0320401c018011460314245214040d1140b0292400361501c0700e0311141000e141301c4120300031034107180000300c840c1d8150046100c030701025002460a4505500001c103e41100128115a004003940c21405920140600210558081c000078050301802088954940c007074890031040d440315510500320a001c031401c440300300e0071201c003035802d49e110008950610005100c080c44039641c2c4400c3da80410032403121300300d01040c1000c07480d81c8541c22401c0800344030307280194500d29500081c0e41d81d10380b441c0300003e551a41140c2d141c141400c15001210910703003010380c0c20181d441040070400b0030400d030b800548102c0d0110703d10180c451200720783c8015402d80700400c81580300b2107c00d10004c17001c408188003030503500d10074003004140384100d41160103d247c40200200303400e810028017441115014086c00082c2c01040c40 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 840380269 1250 840379019 840379027
    0x9040626010b011707030e01090506180309100e0a0f2304021e16051c0e030d050409050c04151710032f100c050d0806030616020f030a0c0215 62
    0x78007203401d05807094904110f11380811080c0b0f100e0791052103503180082c001c00582c1254281550f0b5501d08480e1602421901000340c600d81c103010065070b180342005402d1401c0c43d00610380030360304118103080954000107451000074604071118420300090040c50308074014480d504c0180008107040300e114501881c010401c80e44440c0300c0010f2001c102c4851076105031a0070100401c5900d2144941c805006817107400c109030110040d0002c6203220342c3d91600c03150a220414414181c541c0c10500c40d40b804108140810001468a40c00840e4018001c2004602c1d00d91540d4100b143c10703c17072030300020000c0d50180100000c1044401c80359000401040d40d40300d05480c5a480309554002554a030b40c060300c00c081e981c540c0b901d075184040071620005003400412100000c008148020024050315144607562000c20b0325400340f030f1818040c0c2000b40251100340d4400c9907120441c00e0104003541140b141c1629110310003414005000c1081456a49110b40c80d40390040100c0284407003182c44a0001c204 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 840381519 1250 840380269 840380291
    0x6030c06031501120b030111131403060106050307020703060908070302060114061804090804031b0501050a0e0105071406011509150507030f020a170a230405010e060904062601 77
    0x80694180c0c442481d141300d8020b6440981c0001c0d100d0b1150040e019802d1803044070941e209a400740c058400c0790100c1c9151540e0320f40b0311000c4025906041c941640010380144669841800115840f01c200c0c01102c40240d49ca0380c0340812a80305d40c0d0306484101000c5001010182d06129040c0103240c00243e000107000110300150183c0305161880c400101c0500310b0f41c1d003684680e0811a981c541020300700d80c032150369060102c1e02c080c071506030b84110310311000041030b10b6000310117848100c4404c3d03480d00454a000001968070b85d100c0d5100b0b80b4500780008000449500030000d0324080c00310004549640c0840100c090304050094204146003806000000718181d40441510a800c2d054030f010300012600c2203040c2d0030f08002301806408584200325030045c40e49403d004203003803003c1d036a41070401c3d80900007048942600448498603401d0421080100d58461409070010301001011180341113800e8000400311003c03940712801d0010b8544101d480045003c84000164080c8002400000012 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 840382769 1250 840381519 840381541
    0x7110c0d020d050102040906080f241317092d0108041b0609150309020d020f0406091406040c020a03020d0f0903050d020a050c0d021f020118060506030c0603 69
    0x1801090103441616040415540c50404861000d80c0000c001c5545030f403a4001a0064a1140580c481c588200103400000c0400025102c1300c1081c08420700410514280301490080303006000135031a101141031036000729800c0919189a041d01c50321103603503407194101744144844c40ba024008018000a100c2100b0781c10418400e04d48802461700b07140c2940c56103009030101c03403412021184000700c408040781a03500040401c0a481e40c5c1c10b00c0038880d03198540110240c640d1038030001c1d040700c810f40400d401802d004c180000036840084c80450b0090f00c84020204a402d40031082245038084030600c00a070400340b041c404000214405030100b918540c40181da07401d4143c481c0d00402c145c0d1642c50b40514812900d020165620809131900c512440300b000359501d00c0b00b07506440501617811002c0b111301e403011148480940c043d2000043d0103916641d0507051005042543c00d65407100719070682040134001c2d126519200b0240020641848428949880e8150001074050401042809401c0700320b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 840384019 1250 840382769 840382783
    0x6051503030318071a030a11090f010c030e0d03030b0f18040807050c060c0a05060a0c021009050304170f01050601081014030f1605010809010614090a060b070b07080711 74
    0x1002030080d10f040802c0411900d0052140e03c480c0301620100a030305d1064548400441c0103100020301031000381d8032038001e44c1040c400c03201400c0c4d1000040c500d4005650242d940902e0042c0281025020000d0030030202e610700090120840019650343c490060500e0005940e42c03070b25806030740303c10701003e80c0300c0940b101c000d02910107403044034003080540801108002e01d40360b11501410369038407005413180b5580e40750400703c001c07591760060000189000c1c001d0b01c241032240103503a00904080425149a20052240310001c0e02d01d80800c0101041c8000d0445103203054901200040c56485c1d141e500352400c542020b46901e041100034020f2001032400d4620030000d03140710790843d0920198000000703207452085510700d400c9015034a040207908080c81881c104440c420388a001c02c0e41e03103400310982207032910700980d03080b5543c00e4481a00c03800c0901c0001d90000c072000d070004c3d000d9102c03550500550843c4108407100c05001c1c2c02c00c12056442095641c12810500305081504a014501ca0315000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 840385269 1250 840384019 840384031
    0x402010503040f06021b01050601030e07090f0209100f09060801050901140f03010c051305030604020d06020906040b040810060504050f01050103020a02030d05090a0320060a05040c030816060515030303 88
    0x40c08004202805005100000d9803a88002c045641e01e000c40c5921201e110b044200d110654640000512954003c1c0101c03840d0301000c00182034018148010100246580500800714030750900180030030780c0f11059180c00d00d9605407100000f110251400900031421a044401000b500740c004000701e8941031045815950300d614086071031300800004c603c25111008800c1e9040d03086c1801400844c8c2c1100090442a2845000075101c40e101c07001d240e62110150b800030b42211800c0d02c07031008a00e642c1d000c0c015500f0000c010702e00d03243d503070000745c001c50700160231031881034114003130b011350304406445084c00401045d40c00380031a290140180a402905209680c14190001000f135122842441150054842c1c0792007004582400c1c601e0594a40780d40c201240400e50381080064003008003641a0041c2e030040d0018450f0343d54100b81180903000103481100c142e01c4003100403001070100c00c05000203400884110090148905169096030f101804403000b02d540c4d0f01e45c901503514080101c0354004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 840386519 1250 840385269 840385277
    0x6060b092b1101141201080106061b111903030201020301090501090908070201030c0e130501031a10140d0204050c120c0f0f090d02091008010c09260a1e1b05030303040201 75
    0x940c0c030b01e0050f60140000824028000d40014541c15041c14a040c100d06039101c44008028003a19050280c8040c0001c0b4401c0714070511188900002542084000380c4680b0090105a1840d6400c0311250010b00700c0c0e0012000350b50040b0050000140a10440d801844850018041c680242e00c6011452050450290401d03486001945009006003030202e0f1584015041010005103000000001c0500b8001210b52089500112090060540816010701008861115654900040f104402c20907410140d04000b200c00c450025036140e200c1c00784980c01000d001c1da92460080c000340c003000340040401c0340d160414000b0080032030424090362441092002c00350313903902039036000078194005041c00a5014840030100030001786d4041c1444112200301e0001c0c030060355402000d03961010540954914211401020352407588030000060700800c001e8140e40644140e600d40e0810784482181403005c4c01d1a2502000410040b054046080180d10111021141c20400000c1d2648005040a8104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 840387769 1250 840386519 840386543
    0x160204020309300d0f060e090c040f060e190b090c180a0f061202190201060e0a0e030d05070309050106030302071502210307020f0f06180615150706060b092b 69
    0x1c0400c5c2c1c00700340a05981c00984505107407010908d40d480d503100c0f41d840e014078100707950740c242541d248c09a402070b280300003101071440da107041c1d4450302c01100c0b18072054404e442c1c0c8410301c1251110483c00340a06404920141e680011000991042c40d50b022014012050b181040204024190b81101a00d86030300d0a807601c6600d500088010380104020070040d4250014140d0505405500c14000c40348154051160343e0344024a90301220000d01c4400c0168004000150000405510070741d4407020a040c0010a000360361200c0382190b20980044025921030b41d01031000400d40c0c04c14005140300c82c0300800107140d08140c005050014107007005048100403020400c8ac0c0e0080c0300714440b1b480b11320112452000f880b109c256603907400769000108503030b000000c980e0803140406c1e80b500c54040175103002e500d482c16105014100c10186200b0344800801d01003000000c4c40c6008601c01031482c0340566486012400400c800145a290001d040c445c10103060506506090010402c294014444d1520 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 840389019 1250 840387769 840387791
    0xb04021e0d0816051006060f0219060203040309180f111c090201170a1e060806060d1118150306040b010315020d0c0c03030608010b15160204020309300d 67
    0x401d0003003e4001c1543c05030700c12001200101d0f600c060101c0704590740f801c508040c026000d030384403c084c040c80c0c0c07030b4000302035810004208540c0065400a01c00e1502c031507a55a203103100310039808202c004103c5941c48411b500220740c640d004006429420800c980d2820301806d40d88060201c450a00b04503031500c4030101015607000303a0381c2d0b8807011990341c80030a0900d01010424028030b00541030200d048100000c0715201101841803100f0b56410000a0810f80ca5030750401c114a900c0310001c0310748420441010031070740c8401a04003009c2c01000304819150038403038100c50000d5880c0c10464040d1380144100700c0881c0064600a04480d0000d0380c0d19a0001000d01e100e020788124000e420b911410443d09228003540010203950140c00380c0d504014542c0c03100c00140c20703030342c0308150107511151101180010300a500000d010812803101c4010400005134007140aa030000c680403101500142c1c502c04040c1c00b403100c40f014800802c140049103510b0707006860103501503034184442055540307642c0d2034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 840390269 1250 840389019 840389047
    0x60801020f09130615270f03080c160602010606080c070c061d040203100e061e040e0c030703050a2d0b150904150f02030c0702010c020a0905040b04021e0d08 69
    0x40d010f08400c0407442c031200d031405021151030040b021b11159095000c10404109035090005484000c542034200c146140c8483d50682c11100c40c00609001c0d02080ca0650401c0081c410000d0a41e81c0000c00c1c43c905c0c1c0b8502502940e030007002000084000c0041d00d000442c01b01c840000da42003070501d80c600609980020400f41074008106c0d40081c0b001041c4101d14600301110011580e14403800121961550244243d01246200c4a01d083c0700703421103184c981c94290030040c000c0c140041250480f4900d100043d1400007540d00c280c401382c00030f01c0e02d8000c1c01960303092001012180d02d00315401200f42d4449000c11850601c01400c2c04100c40b020a19a01068044500090340181300c1184c5003814140030f0704591080303801160701440c096210001c500c0c01d000341c81c811100b030a075550a14041c0e40040d01c410044085c00c0f030b84120303410000b2481c02c606108848c05240a00c1209600707150074810b21204180b40600304a07403074500c0800f1034030360b030300c0d102000c2d00c2035880504291a0080700a14a0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 840391519 1250 840390269 840390281
    0xe0601031b081b0603100905010f0312030b0306072001020d0c0306120c2303010f060905060f180a0e100209040b040203061c0804090608100506010f23040b0a12060801020f0913 77
    0x1f402c80c50520700000390000340118100140c83c012103071f46041d211081e505038100c030490901541c06410060025035007500070309924004512254401c3d40e4100c00306c031020308a902062841010341d41d50807001d8040c980c035101b120040d00c0c401d0300c0d6510f407000b00d0320303918210180c41c03207004200e0181610b5106101d0800c0400c120110015000f480314040c01191070000c1c11190184c0002149004c0005042d460015420900b803072003d0940040017095036140022500010803202225071989240114a02c042003490454588034200584601000003008140e8501100700c511490050007403142e0fa0340d5a0f441610401c1c0310885540e007400c560725040417a80140c1d480200020315001c4001801840851814080c407100340d010001381d601c1d1001582c2c0b43d4104005400050442e425085008401086622400340280440e03030030321380e0390000d003c0640e000c0001140061f540c07103a018500e55060044502500c008c074000e5081450307181074600d06014079070003a4800c0010319010403000d002c0343d0102c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 840392769 1250 840391519 840391529
    0x1090b0a051e04020405060a0c1214070b0c071a09060f0f0105040207021201060902041802031302091521010e0c0906191a090909031c0f0e0601031b081b060310 70
    0x542301e11000c4009481108071010a0301c02504015192940c98410709001d0001c1801c1559103003043d8842e16490b01c101402400c00703040c050204002c102003010b4464030f03084a502c4460444881c40c3c205451030400001403c0d41c0086090364061080000030b914815046d0303503068800603142c001900000d60f422010003502140f0354a410008036800705913800034010f8612103680107056012480f2003504034032003100c010070a180300c0700700040149004003215030401c5090201c141440514800210030582010310404607042082e00e810102c1c2e003c0c060040f14680c60409841110000301c00301b8903801005107024441d40381c030718100c641c1d0402201e006018100c40c0a400800c1c43e02c07103003219400d41c4100c80c014461401c1e20300003040ca10b800012180039a9600d0030031040f0b04403180302080a48020515640290344988c1070700034030bd40800800b030080d4001c4820101d109108030301004440b201d50070510558200d400340e9090244100a1302c03150300016241181c0c2d0790345d10324040f07512821503009 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 840394019 1250 840392769 840392779
    0xb01020307020a14040b150d0b0105071a0115020303040201170703020d110301080124030602090f030f06100f143c01260402211501090b0a051e04020405 67
    0x400705441001e098140c3c4c1100b0180c0c1c01300a0780f10b0b9442000403061207090301001703a1000b003205021000054108a08403030040c102141040902d9031000950316200302c28a01c80c07c030b40c0004200340c240001500010710307224000381d4a54141900005c0004081c04802041588101c0220764220301c290704590ba020a4602d00b0883c00c0c40102c6034403c1c40d8400e20501c59550300303048448134102c0d00c05a16280c0020b44c0f4001c4e056051540e034502c03000c4e401005076540d1040d07009030700a510380c909005035189091100090691440c0c2a45810300c0079546800c000340b4148045024882c0d1a03149140c05c82c101c2c000c49136540501108000a8207903c45450052100983d250360642030103464031103030740c600703000740c903641d000f0500c0d51104440785d404504240301c2c500d0490301150243c1000d40310290000f0706501055410140840824541078001e5803018141514000421241d0514428000441d400b01da58016080c600f100103200d41100c110701d4142014216141a260303991541214010100a80 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 840395269 1250 840394019 840394039
    0x609061303020f090708010e0703020f07080702040f051b07290103030f020606130b0111010203070908060a0605030c09070314070f03050f010b0406110c150c1002030c04090b0102030702 81
    0x15203004411a9444228056078080c80301005520300001c141e03126840c142d580307196580c40c0944609031800c010b0800814954200309042c40d1802d0b030f070b0080140b203010700c040b1a80c1d54071a10610049982e10b01050500d2413510080c04001c507140300b0307401c54030903000b0341640d01c0c2c143c6800c020000c281140407040c0f50302c000c6980a010800e0460515040301d0080e01c079100c800d8040c1d41d099881e0482202d040c2d42c4109040c400b42c3d01d80d40300e5409038003110010714042c52801d1810741084e007240e0055401c5400301e4100802041140000c210f100e41c0b00701c1c4442c05020403032030000817075a07500d214202c05102d03800e0440000d03034862080d0310807216001d10032554000b600705280003a0034603081aa407440041e0070200083c0040b861b10050a0496030b10803600b502d007a2500780103d032100b0080741c1542c254003a425060b5025610300c0080060740d6801d526603903484480d290018602a845030b000828a03006000f00300504d90014203540484600050108401c5500340040b410740c45620350082d80100709107 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 840396519 1250 840395269 840395287
    0x3301b0109030207170c090601050c240114150a0806150301090b1309050a08030c1e0c190804050d1a04030e0103050c0405090c0a030b03030a03140c0909040f02060906 73
    0x4086045501746900e030348040c000d5061003134407141800070994102d42c904000c03a1195114a0041128a4804045d108412280700315040308461001c402c2c1c0c1d158411b0001400781380e8440701c4168100c0c41c00ca440504030240008006401d0003010300040070303c4a20400200b498540480032004240440b00f138940d40c1d070b150400c040040055820b03690196048031000640300c181846a0f030240d9410800504102065541d0102242e10003840c800340800103000b04c0540141c0007440164900780701c0c2103e91652852a089460b200001842000480480f81d0369008522010300b1602640c009035442c5d402e04440c0d0400200d505007001d03001c50a0524441000141a40001098114182640c00344210b4031380c003030401914083e031700070143c1c07003212440420b0340f41c07004000511000340c5508002c04c1c1c000190300001d007181c00412880001c01c0d181c4a0440300a9641205c00380d21101d880038183c1405031800c0441c540140c01000281070400c990743c1b00d4150343c1c49030203a5140c1750001b00055034840e1a1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 840397769 1250 840396519 840396523
    0x30c151808011a0a120b060f180117010b061602030109080d1b0f050a03050604230106022808090409060e0d030f02070308071d060706020903301b01090302 68
    0xc0358440010f0a59450043c01458009241012a040344810390100082500d84a100d0341001d01140c2d400022021110003585071200780100501004222119a6250164501070219141c050f850642d00d019070726046a503441007a03a0500480c03103403891080d40c00e480468010080c0381c00150804801140b90b1040036140d400481501c4580040702c00030f02c010802c15160201c010b4000004584107104050b0054403c0c0e10243e440180208080340c43d81d400c00003586000b81596085202c0d00020380148005501007113000008510350300503543c060070842540090340d01c4190000c0c01040c2c00070b1442c54603526a00100c000c0f90700801d042203a014442d141c1d81c2e48003400d0100c1008641042060301c003902d40b505c00e641d1426010b40703a480c060707070703414108998802c4603440240300754008040d0b16055490f240003802e515072244030016039601d80001051303d07040200b01c000c103600c14440e00b19000c450708a4031052104064207040c82d120b6031102c06801103402000d5140c07550b980f0703101d1854103060780 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 840399019 1250 840397769 840397781
    0x1403040e0a0e01050105060d180f0501021909030b070c110a0b091008042021061b0313030e13140f132f0402131a04030c15180801 57
    0x5a008006148540d103070b040c02e0340d00c244141a4810000e2092410019241e000303941ca01c9503011000e007030340c09161f4071807100809000059489a6010859502d41500724840240c6040b55040c6504c0c0c987c030316651080400e90042c80c1e4010019001c8000b010011150050503d009005168440302134850f510f0b2001c5030045581e030ba00c242020085030000e1070292502c41d004a400854844566030100c40c0050510042d00b962a00200305062005640f440b58520318000c2c5045805060380c1d0800c0c80c140c40304e400c901102c606210302c0400521407506400d00078910030b1645030400d18803203448600002e100c0c2c0012128000d070700d801c0c46c080d000307014661820a84140b00c07980c0c0741c4a05440322125030714444581c00c80146107056864540c1d110a80032010304600300c00b6800000094025203000c03405981080303450001083d000b020900002e11a000524104801a9811070070f040c5140c881b081036070410300ca0707000c00003442040c0c0c200d1240b0030344000c02000200c50b6004200c81e6100025802000307 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 840400269 1250 840399019 840399031
    0x403112110051605030109020f040305070f15110c040e1e03131517090102160807020306010608220f050a0804150c030e040f0e010609020904150518041403040e 70
    0x85800c000440f450942d55044000c1482582c0381c42c10b5070f09200340344d00250f00019640e10680000e11001000540400614001c0c0c2400704003403000a00c1d01080c0d510712007103a0744031001c2c045140420000c94000280001e00d15404942c0411481c90841503141000f107018020711403005487c1d6810884100000144a0082c80d09005a145569041c5050306181c03289213004c001000a40b002801e056004100b0783c0210540e00010f1030180c244803d641010301c001e03000c640c11803000ca604015450140010341c018034907170415200340c9c50484e40009011042007804603002400e4800c0005000c0c100c0858501542c0c01800c9500c0180c3c941015803c541261150400d00820079984502c10791040014003140350780358840200e208003881c100070107040c1828a10b564240e948000600e107100074001d18005004140d00141c0c1e480c42c0c1c4090205403240e801041340d4107501c21200b0081919041809094a21a505407104548840c42c201d940039916480c84002c034840418003140f540b42e581601c6000704 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 840401519 1250 840400269 840400271
    0xe0f0414090c190f0506180409030c060b0f060415030e06070c210210050703150e06010e0405040f030e01110607080106110d14160f12140f0403112110 66
    0xb00f0650042510540606211958881e07010401c80c10140c0c05002a501051014044000b12801050444808900550006000b01c10785c0080c44168407c65190500c16940c101015600d180422001c1c461031166013100b07013007003030140036280c0320b60302c159105a200380030348074241413400d00104090501c0c00141c2c1c41c032a8400e10901c0c400b042e0030a030440e410940d0050034540e540908400e0080c08020071240505840d1460040d46820188800707000d8444131125119900f040b000051800b02d040091a006500d80800d10021031021850034a805925241000b807070506240100c600b102c0f46140a1568454082030292480e0032403c10f070b05030b5107141c0c0d81c03008113120014160380e0384080022540104072025030007000300b0143c1e0020200d83d1410032441d0f944290607502c01d000ba22514400b6a0694590000c41c005c080d40096003003041503102011030304001c1151103c200c0e5202d40d101c010440c003485c440380d00c0c10740c44100da000c0c1c0c0112584e9111280010403412141c58407030b00a100702803d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 840402769 1250 840401519 840401539
    0xb041a07110a0b060a05061210060c05100218090405010603030311030f130314040806010807060918020a120207061a060c070311210a03020d050403030e0f0414090c 72
    0x1500c0380a580006003011001000560b025840e1580c40340005007100750041c03407104021403079444100041548076151180c1c0803ca142040002d100f6080640000f010052071749052000310b02c1c00191284180c0c400782005a0ba80d9044124100c5100d4110401c1d4004000004000610070f041d40060100c9000741c03070070f20004d5030402a11109200841e82c0c0c3c0c00c0309440e00003003251110305e0480e1003040c501c24181107038940512044c1441c950030580c00134159074058001444614414851200140014282440c0417405c0c84009000d0444405182c00029808282c80e0480da1040440c0100c000d103c0710119030381c99060030a040600340840302d03c80305c01b84c111400c000a013499411035000000d000090844039086a0342d030010b40c0246210160303c601090300000402c4c84202e98010b62011100082403015101e103806824140c1d003400440602409010402c0802c3d0007041d1116901e0044580e250400e0440b00010020500b002c0542151601c141c20032238a0f00c4002030144034003408441034604 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 840404019 1250 840402769 840402781
    0x1f06090816050a090515040f0204031721070504030c090504052505040209040b13060501022b032c012415080403110d0e0a21080a020a0b041a 62
    0x140540390b02c500ca40050800c4010840c5a55642c092504481403191103260f907007460001405540100e40c00420450340005c04100700f1061513400c02c203200110002c02d0420f0240c5070500c0107204903180d04108440d0780400164100c1c8034030111005140d00108503010030b522140c0d074600425048400f100da40c4034600840e407130752440c0120b942c400c805d4a80001019814481400003039080406210f803c95100d030050a0b55641d40c0300c0180300c002600c0300000e0f10a01d007a00080ca44041c0c00d1413026440ca080402c5640b241e000100d070421031383c041c03c0200345110000d811106045000c030b0b03c01c082c819010304600e070718030f01900302c200564200f90b242480c0c0506801c1c0f149008440388211380403c3c5182d1840c03541c05000e003070b0550340b0074060f0820640c0758001d20140c600f01000c600e20000060038040c241c150300d1070f040c0940d83c003a01400f08506080708459001104016900f000a0500300d004140e04503202c1c4204400800e4540c4101c80d002c035410903190098900c0c1081c001700076a082d501001441e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 840405269 1250 840404019 840404053
    0xe0705040317181c1a15010528090503011a012703110604030203060a05090d0f200304090204060801080106171209030c062a061005091f060908 63
    0xc0641c10003a0f00818601c1d070001c0002c0c40e2a1000d41c40c040d841c55007507840c0811145890760700c8410b070307030b4052008518148001c3e411220140a02d60305003c01401400d030504110340110a41d005202c07003104113488200300944400305507038000f9a1648c2040007444c2840e014901c2c0e40030341d41d802c0c0c8078107a84d900d00241c0c0718910820204041c04003108510b0400c0030031001400040c500401800c01032401c3c0c6c0740c2e0042801d01c10116044895030b6180d0083c451103a04c10040b100d41d1100919002d510081080c07401402071403010380d0040d0707610007010b140c2c441d16810700071a4000c20705802d045603100d648400103050034200b44910203c55180c8200000e05e8011a100542003001010142c16071510000300020b0941181840740c1e014401e4000a003090b0711200d00800003035001ca01541343d40000380684400082c1c142d101c181054001c03109000111440e0003246041d50401c071800c0f03039580d0710a071070f141c1a4003900c2076482601912070070020701d40e500015610181d41c45001aa80d545081c088009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 840406519 1250 840405269 840405277
    0x6024f050102030a05030a0612080406021009080405010827011e0c090b0d02130e04020415080705040207080d1d060705040e0601030b030a0605040b1008010b03060c0903070e0705040317 81
    0x41c0960410419483c0701c0b480381c00210382c0304030017100c00907403242c445880e45070a281580c0116070b2a03030001750078850380e90100003c0c040020b41040a001290f0f141d0307038042190240c4d102e00d5052000e000003046004c06110595440c6150000e441e503040310111150034041c2c5422490305040303206980740e140f02d144450040f500504546d031902c1e1941891b07c41601050f07402020f46a01e5582e0078031403180c032045000303107800080104001e61001800c09004110459140000b07610711030103000d000300039042012854000f02e40b000c580060300d403081030030240341d940b1560052310640c81c5000380202c181c0c40401d2141031041c460008940781d036510319030150b4461042d40a441c00b100f00c5000007595540c400e4118108c075041c0a010fa4602d0011540e8043c1583ca007607030120f60303041100003041403150541c071020004201ca00c009100900501000c60f868a00180101c0c409250026143e4499101003003624020500e101c018005842c0c005002030540e00140012130360461b2a615211100c0000300031b603 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 840407769 1250 840406519 840406529
    0x604140903090f0d2d05010608031b030702241309061d092508060a0b120d05070b06030c0a08100510181d030703031b020111040306024f 60
    0x1460101070480c3d80b20010229542c000424102007116900040e0081c0032307000c0208a513500454942c9611100000c001007009030841c520b4bc801e0000001603907400c01900249500c91100407074517102c80d6168a0607110b1076598642400a8540002e05840f0aa1010b41210b0880e82014100e1a0803041301d19102410342d07170a01c40303500c008404100c04215900303402c8504000700c4240740e8266545026803d1840446481c4640c7c4e5840074800c103241072100320104448490005024200d000440282040c011030031301500d4a2843c000042007500c003080901c0c01044010305040a9598400440f070b500c80c0c4003c3e040e2007103801c0c035001c900d0f510034042400064070f6808501c1d01c81c40c03c0260a5000500c44904040740f44940034440c1e03400d10340244018810b140c060f503004900040180395180c00c01e10f12240d40411685000d850382c20600d0240140d8007900e900883c050703900c8a2501c3c00c00543d6180b1008900c194842e82420b1400b461000781004030302000c103166001a81c081680750b4403200642c812 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 840409019 1250 840407769 840407783
    0xf09050c07060b03011b0f12020c07061107030501050c071403090d0f020d0b07020a03030509031207120b0901060e040b1e040906090c0e10080f12030604140903090f0d 73
    0x10907000210140c02820a4280190002910fa00c00a00c0c000b01c01041111002c0401c1500c209009626400344842540c5851000300394503000d404e50800780d981a40344280c4003042150380c8070258180c414070411300156045002804282002c5c49882c606500000b801c6807010302005c040818440040151418000002d081701400851520b0740400c58040d4102240e20280e0030043c00d000400c160005406030816a00400681c0d07040d00e009002c449025140b0390b1660300901c0000744040c50240c0490740007034585071080e01c103100081c0101c082c01050f0b070220307407100c68500003023803080d840340085404d0a001c5806102800081d420b00112a100b00c3c0c010001d010300800045550070141c12680c40c00d8403c10340040c94061079280e5800d004030941001c01c0100d4001c060096081110344400080d184200241500c0001c10034019600c1d8521241b00d500c954004c0002400d596495211450345210640301c00410301c1c002c001c06440340c0c8100300305441401519060045402c000694010301540106 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 840410269 1250 840409019 840409027
    0x40f080f0307110f030d03050108010c0509150a0c080c0c130e060708191b0e030d0c02220504050a12050a05030109180212030909130305120c04120c0f09050c 69
    0x491201c2d981002030a01d0300542c44d1000070b441e5460402801c0b115441c55940060306505005805085d42c4000050004004091203415516036034401035003a440321012000766241e90000003643e404200a0001c3d0284402103a6918040c00104500d0044142180c45c0c402c141c1d200c0202ca41155501c15a4a00c0da030701410010f03d00c94003664000d40c002180c00031803401d4075241e20900741542d0b036002c0d00501003c107980080d5000b5401600217800010f007200600260400d10700d000705415809a400392085050031000308030001e0f80351220300750080d10501441507107003904002d40d840ca0801c008403400d15500481401252203207096400741c024030380d103080c03031a468407840c000905030300444c80d103d844c0c10b032200e41c0040c0e440902600f51041200c029603110340e41c1208000c49c403a001040305502c0800070110f00c00007039000b0126182404681070000b4a80c481000c07140d014081d540100d01407050540c0e1a900707210314000c50f002100c0b22031710102c6260b43c440c1345e00b20945501351103488080d0001d00c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 840411519 1250 840410269 840410273
    0x2060c040b0901083309090303091b0d0605010602160e060a1a19170604050f0f090a02030f01090b131a04050309060d050601030507030e0d0e030a06090305040f080f0307 74
    0x90790a030300200c44900780c012600d9001c0b50481c611002d80071811000056a128105e1030a00c1c00740e20358000c0c52035016504600c0d241d91410b4441091112000f8031400b080030b1140d0365900d441e00b0004850b0054410005983c460901a645540200c4e116000c061a017400051586c0d004100c2403140070003420300c00c0396514042c0100c81c440400d00750f1807d1100709104045a540c10f15101d001541800d60b5840552815545040307034120300500b9aa020300d062008012200620b80b10700303034202c0b080c00b0490005650307990342c0b642080060071000350306019601034010011015040102c00d1400b409040c04591102e0007482e82c4295102001020401140c0e4940808081d60136003036070140c050302c280d9141500c000d0010707529a01011202c9401c1c1d0f540e00510600b541d2500c101940a000f0b82400c0000700e0203008100d603a0004290903d040012280707011005071000c2c4078105070030fa480706091040c00703140d10b8060002d801038007690009604040e000984c40e040003480320800d070541c002452600041d9 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 840412769 1250 840411519 840411527
    0xf030c0501080f01060f140408191502041505181201020a020106120c15020715020d03240b09040603080705010b040e031207120209030f0a030f110705040c2d02060c040b0901 76
    0x5404038801311400e100008a09c203042c4442950303100100d10605001c9a545804041d5001d003d1141450034410300c4180203041c0d030700c4413180140d40e41e4105640c50714440c450020704107a81101a0b6049029610302403407000054015204460b0aa002408610b4544186560030401480041c2c4225081c0008101c5400002c800d40c1d000034281c415200d00b55210144151120601500d62005a204850030003040760f041c07080d2f03500461000040140026610306155070282c071409402e25409000035101601d5a4503481074005561009401d901e501c45410800c1c02841051080f600890809048070075611000c0b04982c0415103071315401c0c5880c0c0350440e04a50000c000c4e070500c1b45856080001c0d140980c0e0070404200d0910125004151100f041d25000b41090940f0307024005110b0403403104082d01d000419204141c075026680001e000e0080c0e0fa045841c00000c140001c0b2004460001404a1202c001e649001114540885aa40c0c4884018140d0340c0305030f1056405101d42880058500e6100d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 840414019 1250 840412769 840412787
    0x702060d09051e060a060608070e2701080106120206220b120a06080102040b090d020a03060504050f06010b120103061508031815090303220f030c0501080f01060f 71
    0x200020001d0102480d0352034a00e4034031180010f2036a0296034140f4480d481c1c08002d200c1e4450300060080c0070091902c40003501c0e030038000d440001840003491140d540c1f9103c1e00801c45a0002d54541c2d40d1210b0038a1500e0f00c0040c0d028012440c8550030320030003192464a1100e48058030380e000c3c01c03a40c50500d200b42607003824810711001c4212003c0011000910314505000740c007020041c007198000c0c03400d250003204100c4155520ac0c910b241d0040c0800c020241c11030081d5610b01da415186004c0059407480010003012458000034005440c14051006000002403034401e481000011a01e0590301c03111007400b9809070040c1d00e95140c203694010300000d00305070001100e00c0901c0888000183c3c03180310441c00d54010001800c240b040240c01703520075242c81030b04086c4229400c00e91918090000000c26107901c1904034900c00f2581c1d11098441e00003a20402a005102c4a0700c502c01c1c4503120300d01f03100b10303110900c5054005101c1d030000c5000703a241c0300301c510b04980d01901c40c0e100d0300c8080310081e80c103042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 840415269 1250 840414019 840414037
    0x5060a0203070803150a060302091207030c060f0e0303030c0910080f04200d060b0f06120703020c0a05030c060f0106030515100c0605040f030215040b0f0c1603030b040501090908070206 81
    0x8a42c1d480c2215106e060410004e0101528003688400b001400c1c0b100240014a090103d58096082040407411450b03681e801c0d5403035860451101900d80106a0710040001080c5803d440004104141c059004010705031206044640400300f640d81e40c0100c0d400081511060303211045000410005034045241c00024400c0c0003042240705050170001e50200c0c0c82c0402651025118166428140b4054800d400d41e51401c6918904080030b0300c4030f540355002c00800000c123142d030010b10380c0504c00c81040b500e03003035660060840f80d5980031708140c1c5465001c16501441c080903003170004207005000e4003070117200b1000c20f4403c00c280041e8008000b40d000c2d406540a040c4031200600b9400714030f181c02a2172295000c0c2c60b540caa00381305443c0003840c19246c0c0d03100c0148084118244400940187e008035000320b529400420340d511034660701459840384a01062413400c2e801420810950176811000744200119010003041e80e82c0e581c100180d070340e0003030000d10090b410010307131005103051800791020107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 840416519 1250 840415269 840415291
    0x60207060f0c12081009091104020c1203253006051512070807020d0c051e0f060114060405041e050c0c0c060a0c1509052505060a0203070803 62
    0x203009454500d1441c030000220000134651204014003400380c810b00034010400d54408100440715502e86030104002d840406210356000103150401200c1000003d2100100c020352642d40c1c1403001d81d41c4e2050380080212040c0140c074044003200d880c004c0b4164003050640f0700c184034458061451000c02c5951401d0740412207580c0d840d010030300f6210518030b4960f110400d46226034074031911f1584141a00020311030781c00c020141040003a460350215203444406d070340c0d007450203820401c0d241950404000100d00c40d00d00907040d0761070314410300000308540c103200304c4000d9800a0f43c0350701e4040aa15603440c80703035421100c00c00c42000682040e0344120f8400d0460310500d1010282c00880c001551170507130300000d60400106050140c040c3c24040c40c40000012210703289000c2d40c065000d03121040e401c40103400c8040149250001d00d0203904040c060903441800e840302074041a03858510000d11086010541c6104400411182001c030119009000590015401d01d011555444559400101284048 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 840417769 1250 840416519 840416537
    0x60d090c09050c0d0608070f03080a090e0a050103030e100203180d020d0305120a0612030f1107080d1101051b07030903060603060b011d2d0901030b041a01060207060f 73
    0xc8449881440d014055000d8107542d03c07203100002a00751017640c5c005e0289608852400c200ca0003c520b6564112540320002503110401000c00352001016503211419001601e010040078185035400139050324829221040c000e01c3c860107003c80d1401da0444480982d0003000b81100c14014030300ca2005107980285080c2232961107501003240c4181910040b8041000840d500300580b484508243e03100001040810880345041884881400c42803005410310846a81c1d0800e0307144100100302c0126000001c0b92282c6a554011568a034110a155400034013030000d00743c20f0840600849019804d007228141d070455101b056902d880e40020403c4003441b0420600000003091030040500a500482000800ba41010f00240c411441071540b03035400303000e8480c1000280d0b18075042a42441171000d4840c00d240c0100d01e40045511020007880e8001003401c000410802180a911311462040000c0e9200354156825003d803900c1c280660005030300601c10900c0300c548107010030711010490303251544034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 840419019 1250 840417769 840417779
    0x11040b0607050a1e0c1e2102010905011407062d0c09050a0e070f0e04090804181803050702040f0f0b210c0402091f02060f0f06060d090c 60
    0x46540aa28100d5090300003401c3d410901103601800e5000100041c502900c040b0581e80304d4110490710f002d050b00d40361103c400c8050008038140440064110180010020400325614441c62120104201e002031805080400d8952081e060550b01c2c0410701e65603400c1180555517900581030302c0105100c190006020341000ca030744203001c081100c0d045100095a44d40d01e040041c40144030360800d90050404a800b008680d000509140c5c1c02041d500d00b18192a480003c2202c021a01d40c020641c080c1c140700c5603105000581004004035910030800600041000000d20103685990440445d840462403a50010030f008038014010303240300030b000040001c411143c030f50442e004d064816042c1039030b5441c405e100381080010000003044101c2001c40f042c51502c5100c1c0d1b01d6265095541c05035030081a0030207540c0f10a1515052700c0c52a80c44142d10030b801140003596004121a14140c00c1040004240043c0105940a015100c041c1c66107203404524403000000d00245202190803201c12480028 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 840420269 1250 840419019 840419029
    0x5090c0a1a0d090c0306060e100e10080319030617031207020c04151814060f0a0f0e07171009050402031c02061f1202120a080d02070204111611040b 65
    0x41d4541300c2c80700d0441503425070410100301c9200b42c1107801c000d14203c09020591020050803011207409010f0f024032503580000100c4002910f074064805813101083e100071080c0c1e02c1e605412002d0440d54100807543d612036000107103c1d1a0000c4002e076420801c0100243e050000c103150b4000002c2c011186080781e2080483d0803652540c1948501042c000410310201541c00381001980c00410800d00080302006403816141d10050300151003040520f45d103189680b51515180b00400c1c9071450040c107075650741c030180c000d0802210600000340803440582c1c800d075003200340e50b8020900e0a00203040681400c4800707004100280c0140c2c0d00d84130701103051040c041a00c50080300401d46a000d0715650501024001c0c48074132030f1802d0040c0361038000052212080a510000d415501100c4009000d12070545180c01e01000c818080c02c1207100185403007591555800515103e4400d4078200501d91400c0e5064081c0d0007040d07200701700520b1401e01c00010441140a0341a180d4004000003507021a082c0060 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 840421519 1250 840420269 840420281
    0x5160206030727060f0f020705091b0712080c07051f11310602150426031b03040201230c15061002060c1207120207060b030105090c0a1a0d 61
    0x42c81003000303c06000161344800c20b140d844903a4200650101308030303400a902d492281c000d0310300524803880007540309210380d51800c41141080c1e20355641c42c4094240b4a1140c5050b003020004507d809010500c0e10b80080101c03690709422802030300f45074205e001383d031403103814159580b10540e0701c41e04a02503e00b03071000144180c00c2010034900c2c030f0001702030301e00f1880300398440300303019000403a0b03802c02030240c01082c0c150710444960003100f465550341c6080c0c042e2800c145100c03d40413440341764400b01d1b449080010740c000d40e0003a0714800341c00c0c00220101c40a10084500030300040441e5403000d40280d4803c01da101031254566182d040c050f6030165145010607010840d4980c920b4002401107034280a04951a0043e442c03000c0d04a5162034a801c1005101e504400004004000000740310315201c2c481041880700740c14015903656000b4140600902441c41034280301c2c0d4600310200c0c2908030001003425001e070300540301c580e244c0d01c0c108031410700d16100c1e008641c94003c1081440305600052080da = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 840422769 1250 840421519 840421577
    0x305030c130b18040509031213050706110601080a0818040b040f090b060d050d0c06020d05010f03141b0f040e010f05010e0c03010b07020603070e030706090602010c051602060307 78
    0x3035886802c1c080320f0401c4001c0b0100d034140264501014000105408400c5440c10350340d0604040441e158900340000c11150808094040d000b810000b045855120000c01c95512a01c0e040752031590721030154540b00d440740c80000b04054810040c0d10703030a507003112400001d58401400014034054000205040d1907418203920701040e030310307607100007000020b4a1803038102c074040c0c031a080d000740c46031341d40c81d0f4a10030358141c0d00505c10020900301c01c128007034046400846402ea81032082d0750b910412400708510500080344e0360042c51204544206c3c000612500b007140b0380042a052100e04000d104401104008164005484040c2c045801009010308900351840c00c100084643c50181c00c02c02c00c03000a0300c04c45403e0010001008000f02d002e003130341c640640464586549441e146001c0c0ea02030303107094005806000d007590001d1642e030000481d504841c8140c0081c0500f0900c1042100d10348903032182030082d104000030403009414500007441c0d02c01402d040019204000d0031038031072161842410 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 840424019 1250 840422769 840422789
    0x331d0904020f0907020d0210060305060a110c01020d0c0e030d0921060518150408090f041433030a29010906080c040c0804200411032a070305030c13 65
    0x1443c10056410423118401c0002880700b040107905565a42d5203c10002d80f04000c1a9140c000d608030b0300d8081d20817514122880f0b0300840d40d448800140d100600382a001040104000446c618204d04021403106076a40240d0b44443c10380c0c0c01c2020b105038050400041030342003ca242800f00002e0042c0c424180a06411018107151070b40743c051a82c42c01c503001000500000400c42884000740c0c0740401c0c0d41c1d034174030102c0340e40d16003006280c003150041174070014001c241c000b0f403010300260101001c0a084401003400d400c1c50565044100c000c583c00000400030380660002c40c0c400d011850030409020402c071018a020007400303d280c0314038044002038100200f000d640e10030412607035404110150310745c001900c05110309983e5100103002401c00a0000d0315440c0400d0110039100b40c0c10302c0b06d8440140080c07003000b0f401f40181145405410450303154000c01525488499000c078002c1000d9021003403401313854580f00c120b0350100c600c3d400180503c000781381d060003442c0354821031350380c040c0141c04075040b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 840425269 1250 840424019 840424033
    0x123070309030b0703091a0603030d11071122050903130e01090624050d0e030301120b0f090d0c0f02090103080706050a05071d0307331d0904020f090702 67
    0x14007600c1200040c0804c0c1c141442d0a0050001030b00240c0c644041d10301001c1076401d50b550301c42c00f01f030452141103141e4040f6440c02450008810403c005800d5040c0900031075104c2c01c05880a1040d4211001d40441410241d00000350f450841c1d40c110325803081c02102903901305a6a68045180e07040c107031304400700c51180740005225401c201c1c89494001c10f94000f0300c41a84d141c140d008100000220345103010000c001403805001245a04003a08403040c0c10b0403a0307030340c0d0b0b51048010100c02c08030104a4083c03d1510212341c801111400d071a0058981002520110000301010ba85031380c4141d004503403a0134000f00807030243c1d076080e05207802940200311217640c030700c0381d4038060085032402410301010394605411f001c0410307072002600708510f000c6101e4185020340b04000902c2d00203203900c01240104511240703290000480101400d581d41c41042d96102c4003046800d962034040c40380014514170554540600e2854078103240c82d0414009003003074444520740c00c08110344003c00c0301d061015074007040d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 840426519 1250 840425269 840425273
    0x6060d030c0605091c03140f0a09120207050a050a0f06050c070305030a020a14011b110709020403060b030f06010b0d0903050f1918030201171f0603050405070e1302012307030903 78
    0x101c1004051a149003c0100710088040c02000c40c7c03000d090003c0c80c440c0c00002031901c4091342e00c08c410319038104000d0454040030b10f1000307541d01001e00407107020342d031041e60003c1c15081070140ba406950482842d42c035030380d04040e811112500600f5079110700744203084000010920600c000c0c040f0020076030260031159154140015100c0d0342490f80c0003540c0c58080070540428200c002041203407498600044070034681c0400b10300d0451550010102c9a100041c000200b0440e6881004604029820344075041c0900ea41d4a84500d001d108210f1408402c010741004201c0540c41007403c14400c1c1026401c213000505410b41580045100c20f20041c0c1e208140820035410207002c0b000e59402d0403611903000d00715800201040820b50207100d09178070742c40100740d0250f81060034a4a43e41c426006217a03a50761101c0040192400361000c2d1120b0141403c0421090011108244501d51410b003100807110349600444004200e503044101000d001c00182806048160007480400c4c003a03601c0398803480c00c0d4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 840427769 1250 840426519 840426553
    0x41a1e010f08060708040524061503010b0304080a030f061e092c0715021b090402060a080702120c01020703031a0123070c06120e0703020306060d030c060509 69
    0x603009041104441e110411900300c00080c0c03180d102c11307246440e020b641c4551a00c9490600071604c5081100780c014002e00081c8a12100188521000c4880c4095541180041c4032140320a02403014001000c02c00980440c04e500300400400701c0a280025401c4104900c00007224101e40001118008e1030261130640c05640220101520540b0010041b0241d030340c3d82c0b050b150784000f807991000406088440d1540340c0c144a070500400f001d07403c0701d00380b8482c80f80003912001c43c0d0801d00c44212200f03d02c20319a05101c45900d10440c0d02070100352034070380705203000d071840500104408114810020748280880903000500b6241d007040001680b921503515015055540e58031180617195001585c00301e15030b83c0304203610f200741624000d00410300c04003c070302200e6119401000d044425030a00000d44164405030f181d44030641039904020300c055903401710b87c4450b450b11000c0c2d4182d0160004c14080d2a112048038441c521906042007984229a102ca003602c0040b2882d030001d82288181d003c0070082 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 840429019 1250 840427769 840427771
    0x512152701150915091a03070f1802030c16200105030c03040b220f030306050619050a05041706011d0f040303020a030e030c0a210215041a1e 62
    0xc50001e0080160340b811404410340c5038411442c2d072685481c0348403044036465454a01801d80f40c00c041c0900b940000003005074000011045010b48114980000c22041001412040e01d60050b411100d4a604154403400394001800d203000356803081001c0d890500814410042c8903102d41c6048246107030030040c1d103090190010003203061040400400400e00c43c1c08080300d40c00381c1e0041c100c0000c1d4517008003070200c03080820f01c2019400d103002d00c0c1100340b102c1510307002078641c1f1030b0390305000782600c91040c82050300802840e0105000c0240806602d1405240900004403e81c42d0080c00c0655030000d40340904044000601c0310b400120042c4040107036184070841044100d198054541071042503402d2030346000704003808040e4082007a00120b403180d0005811005c02104881e00d8a014000c4540c503041101001c0300c0d1072804e403c2a00e60044000e0040d821007000b90040c0c81d0755421424107041e0306400410407106401800704080410701d0f0310047c180600d8103402160b11030498100088240e0300 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 840430269 1250 840429019 840429091
    0x906141608011d1611121201171506040e0a0f120f02100f180b07020601051c0201110c090403050309102d0b09090a0b130309051215 58
    0x140a10000c030030410f400e00306a401c04818204140c00303c04207041140e01012500360ba04160055031812125561860080c0480e0140035801c2e082e00d036615590079868550300030441c9a160049090794051403940c000036544100b000d00045448001c40070580d0800e5403603102114085106116103083c001c21032043c1e1145001420994070b00229614060755540391518441e440946803202044804d200d40c226110241c030121a040064600d440d100901c1441203400000522510b00002a40c1c03400420009121400007040c1c004078889400446210303016480c500864407070385862080c9078441d040483c8c4035500941e50f80b916814070341d005904101000508074850390820119040703000000c41009074070106e0001d0303054040c103090964009007001e000000d51141002040002c00480403400700152481051101d117613903207080314540b00d052018130150000b20002c0e018081810b000719100460307142e102c05c5946442c4030450150542c8400c40c8c54140920044c0d00010301c600d00765290602e445 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 840431519 1250 840430269 840430289
    0x409050d0201150e060105091909050106031e0908220b0f0a0f0e033a020105010501030f090b0604020c03270108010617220b010f030330090614160801 66
    0x30800170b000030036601070880b80500c1264220540b8006020305aa804001c060385001031280790383d110f03030141c0202140070800c4169001c4a41071030100c461845108055644180814240074a071400310340c0000100380720b45080c1c1907012000c142d00421101800c40c1038040d2043c80e6451058100092a00c48420303151000d204100c54140456640400e801200640011008440701480030b100b01d900104000c0f52030030308024a900030340036541908400d06823032080c0c8043c44048005402401100c1714000c01602c450f25400100e0054503060300280b04032011f81080b41d081818500c10b00c1c2d000459030040f00403e090300e002044495800048e000d00401c00d80c20148841a05c02d1f0350240c110500134840420440d810700c485841488154070402615041501440701d5a100d140b903081c40140c13400141c010903a040814000c01c0d130080382d800120341070345c10110000314440485901911450350200c2d900d1f51580502c4501203010741003e0f05c5680401208070070505000000350501c0410780006c0912 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 840432769 1250 840431519 840431521
    0x50a03030c031209021012051506120705090604080c150f03070f0504080a080c010509030712030504060204030b0a240f03080306150f1c140a02090409050d0201150e 72
    0x109400011070080c0a406042101c5003c1500b01100001d00098000a5004d111100b40c170250680c0302d03500002c600c46c482d5007042952201e0240311808102a0071060380f020f800c1000d04462070b000311078142c1044950400d1401d1042041c001442c0b500139800002136a4810340804040b40381c01000e01c008a0651900300d49445208002d4980e00e04c001030400003403100c406900c0964500c52000c0b24020280c58098070342ca0016803400514031791000300c1400f115800c2201080440c1c40201c121746800b58040303a011a8106281c4068000d44401001501c1c007647c00d000000100e40000c0b070b103c0c41224035404c009a40260340740720407000c5540011f0101001074003002404107a0a0390f408000340c0350040b201c6600d907a2410000381c2e4144070015032403180c81d0041010b40c1d103100b90502908003c0125210220305d481e00c80e4000701214240d100e8540b9041480e4041418600380e07030b008120141c0c024102140d11142d64996a190188000d03d60005072b40d24603081c01c00036984241540502001544520a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 840434019 1250 840432769 840432773
    0xd050109020301030c05060a0c020306070c060e0607270305010f020c160f09090602070206071b15080c0313020d030e011d0a150504090c050405010f02030c1c140403110a050a03 77
    0x2499005d401014020500010b0b4528181d0043c18a404403640c0103003100c1580c9448c1790300400a002054040b514207013401c003408800300c404205244a145180d42d618034102c03029a40d520010361103088603460748100c40010011500a015503c0c9602181c00c01503030f40c401502c0b20320b107413079140113040c02c1c0902400004c3c030000c03004103210012505c10340d8011450101c642421b500074030031a80001e51249000801004000c06110100240c1140a48d01c818a0b552001d50500144010080b1000115032100090003074440002460300030010309032030007080c107030350b804185a021046001c0e00400c0d00c020340841079613844000ca0780c00c9041d4818a00700842d860303011481182150117100c20100260075040400792164003a00d000746a20141846814100c4501800d1035000c0d016241c00078500e54880010b2a0002080b40c500408050045c05044215003045c00a801120010800c01840f100c404040d00d00b900e000c1c001070340c0980c1100d41003030114420802c14401943c4036034041c058140c01000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 840435269 1250 840434019 840434033
    0x6150e0d050303040c0f060e0d1103030909091c080f0424020d0b150a021c0e0d0f0506060d050a020906042903010605010c03021222031a0703060b1e0d060b0d05010902030103 76
    0x80e160f0210800410ae01001c0c0040e0560160a4126400070404420008682c10000d161000442c1841400111641803103040740c141804440b1409200b0002c0d010130000b0396004050b00440030300c100150020704c0061a07210a0ba40241c11403500c06860f035241c20228038080100c03800c1000c00d40482403030a0050301c2d0180d11202903400c9040031a600e00548840d0034007a80c4100d05a403c018020042a810b0346000c40b00350402c0b1a080d01d040c400c07000003519509068842c03c1005411030000c14524000c0d42c2041700d88203005044d01d030860b450303800d0180c5402044041c10110218a4641c0364403489241c107040c210b421942c0302714101320190102c14007294010420001c0c040422800275901d4141e112003100407201d00b0f041d0485c1c3d0701302c2c0c1000414885002401944c5a1010303c4561140d1501e100031400c0e10020b024a8414500411207182d4100400c90040b204040c0c45081a0512001d0521030341243d42d503a01c0816507203000501c4007039544982c45094054064a00300710f0843d41580c072080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 840436519 1250 840435269 840435289
    0x60203060f09190209060906040b07060b060405090612120307020703021f0813110d06020706050a06030b0a1806060305060115051213110d140f0106150e0d050303040c0f060e 76
    0x40f401550021350b031a403030340316101101c4d0070050246c4650754603603a400210b55190b208580a440c060b1030101c02c0000e916111003286c0494030000c0c013030090740c0c407013a00700121005c41001c4503010344104070b044849407103440e018610510351900500b510b1450760060203040300d00510100c0c201848085141d1510380c121090341c2e04032240c4480c0301c0c403034422494007620b01005101603a034401c40c0c10045008110282d0000d01101d44110303c14842521125980e00c00c1c3c900d2800001e21410070000000c00c0c10b2113640c000000d8181010104580d10603545806007210200d400942d440d0b00204014050740d20508513041d0101c81a241642c5840c1c0c030a040314000d0400038020b10710104202656500340031280026440b48803005040c200d10502515040344441070040000b02c26004025030000103500c18845d440c1260300c60303000c640748080010070480c0c08882c490b48059002651403906000f0500c01c02c00342d0300c224820500c0a01140c02c011210301c490885500c45020005000e00e00b05407038031010414 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 840437769 1250 840436519 840436561
    0x3030f04060903090e010308032d06130204030b01180c05030907150c0b070804030912020f1c0b0114011e02150408310501230901050d09060203060f09 66
    0x1402e840249000c80b1080d00580c00307000c503004c9500000c010b00400344021401122404840310082c034040c2c2e50285e40004428a0703030100020071b4001191070170120b0809202e10070344107005281607100e5643d102c40310000e801c801c4115664030036951b1000c2040c0700d480081152030500c141035241408509a0301c401500030048030b29041d04810740203d01912004000e903a00c024405164981688000d100c4501180e0641c0000e00300100080c00c014010312030024140c002c2c100c3c0c1160200f2006110b4a00c81d5241182011141046020082010881094040e21200c10b1602081d40c1240005200c041d1102c014008000040d13100028143c0001c2c0e001c8000040041021140e81d550903c404240164840c502e030001c413400180c4240c0321402c03104c03001c422040b90101042d41c0c07500011140c0d00f0701c880d60b0140b0001035605c03c00d01004460702510808405242103850609003020140035a14030102c103c0f138464011061142c540740081209034201c0c0f00307a500d4041031030460321000140c9034003414 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 840439019 1250 840437769 840437771
    0x307060b030a120f08070305222303040e06310b1e030f0c030a030c06060b070b04050d030c1b021212040314030301030804060807020a020d2303030f0406 67
    0xa001819101444420901e54000c1100e204400f0f2108001c2d143e4070200b20034000180000300080c80c618041d100e030900504c283c1c1c0740014121030100c1603c804850707543c815910030124005a00024400400036103400810901654441e0724090154450807809090944101c0c40c0d0306151850060403c03440800a0422500550209202c12240300a0410f0b440c0e060b04088424440d114024585410f04481c40c416004c4400948407001d409403103c00c64031409070b040d00111400c03804284a0300c45135250764090040041e074a40d4070a1000310660244000701c45c0f54a0440c20001802403d0050484c1c51080e81802e221507120044018106440080c615a010722440001170030340d02e803030419140000012085506840b43c207525140c0d160000e1100321110004c200008510500c08000c0e2412039520016250400d42440f000f503441c2c0d0001060081140320700c3d000d03000980e86a078112865180903940d0b00c40950740a0403070a00c1c00e54881d403003d4190303104005001051a60000043d8840d4110300 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 840440269 1250 840439019 840439031
    0x319120c030512160e04051b031e0a09020103060b0c15190f020c190c0e0a0b1c0b0907030b011509081507020607170f0604020d020705030c0c040b03030706 68
    0x180503030310b5029012901c0c0c146200c3c2010001c0048106040300542585a161100792078400402c0005441d001c4400010941021800711072840f5000702035500000300ba0071901c403455070854100510700b82114030241300381d2604144000c4d0b50305842070030003900c66071b05400c1c64441d01604060342c1d501d00345a0302d40c2010181e0700240000513400028041e00d0030420042c480340b1041221000a0b4100e4424081c41d402110720721746a40030710f07e400305411503000d2088a407140c50304003800140800282f03030001c10303500c85244203a655101440c900d00b0501c90040941031110320b00b00320341c0d2044000d1104603107901041052011400002c0402d044903169000d80c485002c01590844280222703034400d040c280f08030908a0401030b82940c1d0310b0b00c40da00342c3c1e003203a4031545c50000c1200d108440c26503168400780054041166010701c0c043c4954400070149c40540b80c0074028040b002280c0c4058000c9e44c81e90408243e1040d604000d00412064183c1240c091000c0701c0da541c0026101d108400d001440b80d56189 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 840441519 1250 840440269 840440273
    0xe0d050111040f03110406050d0b04050c180f07030204080c0415080304061115150405090a05030f0a02060a0209030706081009230610050301210209040c050319120c 72
    0x14000ca44641c018408039a21641d88a50300c510301c00c100d01003241c60a81c400b90286036070800344540380c1120b100428014800c000741d125002540b4000e0804d0300c060060f00310340c00460f1074401d80d54034a00d0b0303c80143c00d400c0c41c00f071507207140000000c0c00b42130402d030040200b0402504000364442c0008400c0f42c0005e81c44486282c8000310303915681c0502880e00003c40c000030740c95004940124031410b400181d40030031078842000b800f20303038003102c110300c40d20034500b04903446042c00d500040d80404958110b44000100d03860384d91540d041020a5118000c1c00600710f008a903050020540095402c1810340c20034451900194803030165000e41130070405440f001910408080500c18001c00690004000b41c1045088401e0044602108030250030040d1010075107605041c601082c4400303c0d0b50340c2d80c0c1580d0030141c08101611710035000ca00310200c280d080102507a80c082815010b5849107541c014018030b058181400c20800c001c50515401c006017081d40402c08100c03e02e01b44c14014640f00306404194 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 840442769 1250 840441519 840441521
    0x60f03060302012114010e010302130b1302161a060102070806090a020904170310240e10140d0509010e03160318080a03080a0510030203100207110d06050403090e0103030e0d0501 78
    0x50610a050485c20030000505070500c0e0343ca95050341d0003902e00c640781c081c80000e00016990316a0340c86400c00c144216101000c4100d83c00b13030420651122174507581ca0081e40f11035400c02140955501000303c01402e00c4200c4d038041100c800106001e802900ea54513001e03441d5500e480c800c040103070190340d00c41d0000d010045601248690340102c5000341742c03a810001b075080702d031400c18003c40700c02040e0042e081b5200d030f170204402d5114a00030fa0701e0340710b00070300b440074003161160011190f028044680e22611700401150064142d0103030801001903030b45403a80545082d2894040e08030181c1d0801c010054120001c19003450790f468140c01c02d40c0300c04c0c4c42490208010400303548100441e018100316801050743c13000940d40501c280010910864441c000d00c00004145440000c0d855071142048010022294001e0840300740901607150001080d2000b2801800301391001300c07001940e41c0d04010030550400c044101a2115201e641015810f50b90050009151601c80d039108103a0720141000300b14003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 840444019 1250 840442769 840442781
    0xc171b030c3601091d19110f070221030a0302090a0e0a0c02010b06130e04060207020411040e0906151e28241b0b040b01060f030603020121 61
    0x11811012030903402c201400c00000e1400ea400368001129140c0005000c91004861103100b0b45203286480a070b21881c0e0202c40f541e015151001d00c254031f030000250781c6003409026018540c50b2204445d07071002d041c810009040c144800c80c01c4000240141000c4110000080c0c0f10084a42d0030010b03529040c0324002413191441d588108180311a03001003145205071500301e6451420150000c0c0600e20f08002009140d00405160700c64013030003c20b0400441d0890301403d50803a0150310018608401c507000300f81582c1c01c111803e20f25500014081140c505c1c40c18009038880009405480107045c6960600301194004501521800b00901008194512811100e101c01d03402000c0800c0311243c405d20100c80c1c040d010420103a8020f400c070004e81e2a107d0b010444081602d20590001003144442c195038680080b0280751980f502c00d40c1240019980c0f01d11540180d018401041c107940c0340070b0b80109007250302c0d080b010406003484000c00c010f03600808113840c001c0b6207000d60340400161421050003042 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 840445269 1250 840444019 840444067
    0xd060e0f2403011802011701050108070c080c03040305150a0204030201080c0304030219050601090b010c2a0f0603020301180e060109051305060426040e1b09040c171b030c 75
    0x480c4c585900003058080800104d4507100f038039000b40c4143e807036840340362800c0240300d0300c1e02017481c0c01e0010f0304c602e20603010303006c44a108a0b030950030291080300440c0366810580049031150301068442d00422800080680c0c88205004150714160850b4002044048003500c4006c2d41c1e003010000c074003054000e11400314480d14400c0b001248001d14101075a13258003c1c40b48841142c58030314a4007180d44500724003c40d441d04940c0e221404803810552100d080550214032400c00d109400c007060346003040c40000000d1450b50b40141e00c03541403007083c406205440c140403254a00d06120000c45400110fa06c0e0704442c4228000516580d0b50802c4503010020144014654022070b4108004c001c84040e02d40800e0010120518070503070700f01c0c62684107100d54003a80245046010016829030781d0605205110311420b040f40e4102689200440c0036201d0044848000c1015140e03041105a08a545180c3c0241003160603058846c00c885071075145c1c0b10280c04a600d080001440f1401171009114052142c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 840446519 1250 840445269 840445271
    0xc0a0c08070516050f030106032d0b0a02070302011b020a02100210110712030c09140a05040501060e040f110f13151215050a0611070b0c030d060e0f240301 68
    0x800f500c00080314500e8540201d510411100300703580da95040511840b415207030300501c0480e102036a180000c0707040c80a0081004500c1c14041204009803c80da0f5070350003002c60b03020150f109c07015490040e09482008008140e041d81d240b41c40d0101c164001100005240c05a4031710129410340c0000301c0c101026010010103c03420041214650795401e802021998000e0007074041c45074146408030256880c295014002401c54041880034201d02c1254003050080107241303c141c2c0e0b50319408036007a05c1e400d0340240045501a00c1400c01820540500c1800c100c05480800a000c0740001c00d030032500413264102c101d0300c0c010951610b16041800e40b00c0c05010ba206481003c00c0f0000001854141c00c1040d0b01041401c100340001203441c054054130954900400c82d0740b0081c18104100c649441900c5418200e2281690002d00030400c1c0e0001c00004d40031202556807040c8070403549044d2845540129141e1000340c04205804500c155540d4018080c01c04400003014440024184503e503164560f5040d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 840447769 1250 840446519 840446533
    0x1350111041706010902041d1302090a0e060601020a0b071112040f060212041a2a160503070e060108040212030a020c1203030f01170f070314150c0a0c080705 69
    0x2420b4071410240e203001c08411280140c0e02e400164040c0d001e14801c2c2c0d000e400408103030203901c0b200c0d00350340756001c102d4441840603d04c0640014507148001e458420019941d114045020a0284200390388014203000801c0080000d546100380007000615400c1008100d003070183c039480c010300041c2c4000c8411001a80c0301ca8403024141180c110300d2141c1c80161241180482022082400361703001c980841c03d041502e140303040c00d02c802d2039000001e0b0030a002c0408542c0d1188100b5050803a1345095020001c001d40200b41401150405403504014401e80c021031040040810246c0c030154460000c0c40c01c0c040d203449620104007030100101004080d40804281c10754010b600107011007403020300700c90075000a810110b40645034401901c0317030740389004100c0040c000044140304406140c10002d04030b0b851a100240b03068244645030700101d6440302090041d80400c50200001202e00d94428840c40c2c00e424000c0c1c041ea501e1191080390000d1110001008003400030030029030f0a2550402e0a89040c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 840449019 1250 840447769 840447779
    0xb1003140303090708061005040519090c0f080a05060a2a0509040507030c0c03031505150d050c0301050108190f060801090302010c0318320a03080135011104 69
    0x140d0b04100e9810078a441011000600741e200020424003c2021b4066120000d003043e0900000c1c0c81c004000200b0a080390f61001c0350a4101c5c800da0003102d004800300c1007140d040c080c03031151114841d4001c2956600c0070500300e011410100381950411b40c040400100726803d002c5200112800d0180e41c480c020f941e000b000c0f86581c01c04020103202008a038100425920143d003982100c1c0214003803030005407070020f000006400ba9000d100c20100e850304050f002aa5000001c5440820b51950086218041154002800c1d80d019950304083c0303100e01d0500f1036052000080252100501c014034100c0540d004d418144100d0380409040855400184801034550100034080c3c010000b0450049d882d103140941d602d4402d2042410034074140b405074410b1003480d1501c9072000c400443ca40e4525a804501c8a084103222415000f00003412002c1c000850950401401d4000d0590007402500c144160310714140f1a03000c1049444110880f0182c005980560014014116422a54040c0d040081c0101d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 840450269 1250 840449019 840449023
    0x1b071d0a06080d08070e0102070317070b15061e22051f050d0c18121b08030a0311070c03050303011517060609120a060510090212040b100314 62
    0x4440c000000c01400082c0ea103400840c0d076500c852a14000094140b000b1400040c03060382407400764041481110601512519207807402030740d0103d980c40207036001a00d00200217845081d0707a8030503880c148005218040750301140d80c61141c8602d081c1d10f21042d010018801449100381c804000d141c82085c1d191061484a680c0c500d80e240c0280b81c810451402801d80240405110381340300d00b21036030355600b00004451080d018058030341203802445862100c003a81819074020b00c0004000720552441e0f5608142403402a680031445204a040c0e10108240048080003048402d01c299901c0d0001e082d01998419440034007c2240062a0350701c01c41c4000103110001010b58180d1303501854000c0106041d030003c6e00c03602030341c14130010550701c80790000d00075207899405003456180c0070f44881c0150708414601070405803541400c4a13119500c0c0b050201d1000e02c03004403005040e9060f021480c0c20400d005610981200030700092080540c40b000640c00e8000004031802540d004031815081e0f400101505d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 840451519 1250 840450269 840450271
    0x9180c0e0c040e0c0d06090504021003180503070c1403030406080f040807080d090203010f0e07171228050f070609060b130212072102030403020102090a090b0102061b1b071d 76
    0x10520341801b01c0450380c00210301c11680102c2d0700a11200310f4540c0494180d0240c266641d02d420000c44013010180800c00601c02171240922520020300304905280c001d86106000b481e50900071762040c0403e00c01e90b81c04c0340819801010715002c8200d59501da00d88031005208480000b00402404520513404060642015900a00c2280240702803180320301c081c3d04075004803110000345d40c4001020061b01800c94056241d030f400040540d032503046101e4031100c1d945c1c0808105c1311042e811613407812002021202d030013854480c034509a460311b8410780c000d01c034030301031480060400c07591032200804000d0984e00820103210040c01a40081003030315040c00094002030280031010364801c0000320b4071071054403019022000b007402c080d000591104100c0081d040104121f0656508118035141c0343d8603203c4200042c0042500840c00d0080c00e8002424541d0140800e0410f80000e10032120340d0144c3d100362068000d16981a005100d041c041051400a4640c80120200c032084040084452240c0090f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 840452769 1250 840451519 840451537
    0x70c0308180d06290f06070611030103031805010f050d020315090a06050406090c0816180f05040c02061b0f09090f180a030503130311070e0109180c0e0c040e0c 70
    0x411000030040d010100084a01c4d40210380c40b01c3c041644400b5407802c48040c2c0025401094001807103d281d021425944d4400c2e041075020441d603128210300428000e0640c40035107001e00c5d01801d0f4400c294009412030040704203d401550700400000c60000101101d1040401c004046503814200140f04000a10141c001c0c94000c41c200040460300c0c3d1124081d40f5a41c048a5684046554030303014610480c4112440402c20020740c0c0d2180c088840000300070002074401e00c11504016850142048100c034046580401550800d100b003041c055060b400907800201006041940d800c1d4006d490155486480c04503039001045406011440d07800282c07246c440c04881c8101c044605207040c1e80f90b40c4d0100254000c0c0011001c00000b02e1a24401e240149100d12909254410541d800800c50805200b80c00011758180c01c0c5004000c141458001e820a41d0030755440203000c094a41c40b00b103808541d0380601c1c0e90264182c0040346a2443c00003c84004102c40000080c044c20040340c9140150b02a40c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 840454019 1250 840452769 840452801
    0xd050c0d0b031c0806060403151b080f010302100203041a1809010f090f020904020313050d09080c040c020f030304030f021b131e15030209010605070c0308180d06 71
    0x4030000c1428001101e0003848a0b80019501034191014121113006000308420b4110105100c0003000419030f00d40901c0602c4282c0001c96081601d10429410a8851003c2d000300600601808100020214003e0640f0f4054030b100e4030302201d14505038a103200f6036101420030081c4140b800c03c40004100a41480c0440d03425802410365000100980030f5020700440c1030005412104002c03503501a40072420790500c030307000507090030501c100140072038004591444540054600c1f00b41001018440d50101a040d410700c10041d6051a08056880144055031030086170754452110810b4000c03c508103442c2d085d5000c41e660f0780f40c0791400420441541d02c801000d842400c84d9201f00205483c003000b202c41d006010aa040d80402101c18081c000c2c1d18000c0001c0740c280c640704150781c55036000d15085418001c3d031a00c00e41e0702d5032042c0203176100164808004c01a041c890740c000503280821490442c0c0c1c00151755510303aa05c01c030000c6a1122203030081c1e58005010151794040200c181c100b80500048645c0e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 840455269 1250 840454019 840454031
    0x71d1305011a07050316020414091e010204290702100507030f1704060c140d09020f1e010c050715120b010e150f0d06090203010314031314060d050c0d 66
    0x601484a0003001c0c1c3c001d04940091100c0711100c503c02c0101c2d03410030b000400c041201d01e5103141c11a02040107907191200da8010594209880103d2511268a001d55000840c5001d14010380c03400072403180c110f6032284001c000d1504216031104400e0310030742074008180395650024200050310f40d0344000c0c4210003041c2140c2140318850f02481c10b0204416800c4c0342205282e8490350781c04001c0281e856038105002c0900362201248130100d0142000814500b8005001a503034010006c0c03040c00da8201c21b200d4507841440c803140c02d0720308840c0141a042030801c40e204090614243c5d0801c1815004a034000c80e510010140b020791018040450b0040c028003005110b4154004403554410302d21465000300c912061625540710490092205040340b10440d418120741c0f801000c00d40700ca0741e1013400b11540200060044c003242c20101d160200852000310b152501d61258155620f80d10320460b03850100c540612407207070700ca18088401481060744104054030f060103182c0000e4028003030980c4001c1c030b400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 840456519 1250 840455269 840455309
    0xc060507050c1e0a12052209060906050a0302061e070b07091202090c1c060807091104180f0209030a0c0602061515030604020417032101030b071d130501 67
    0xd908403407010803502404d041c4d0610f0b03c6480c2c480b00d6040f14841001400c0002020003511104500c51440e203004084a56a103050050016141a600441c2200d40307428010009966248200f50840b981602d10585407042c813010882400da140384113100b0100d000440d00100710709004807501c1078807107031280c840c0d0b0f988503242d4000f02ea81e9024001d41000c02440401c48520611002e0a50012405400b141a4012141311010f0715050f51140003564407942e014007110f2960300540c40040341084549092603d00b018503004026140d4640c15443e40e41c40e01c1a5580c0c0349901104c8541c070029040b0b64580c0428034005800c2c00f4903200f91380050181c02d001c03401d143c81c442c40659503484003d140280400a00303c0629680e0301c060311250f8081e908001c0041d0398030000f00741c80305440100f00655241d0254221b070140d2010081c0800e90080401c1006000040e8000b6459030412245e20b01070346c202c04018440c0d0182d04841038010380c015074440006954440d190800307811303079400031101c2c00340101030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 840457769 1250 840456519 840456553
    0x50402150a1d03010b0d0b09071d0a0c0302070f031d120c090603190f03030c141c090b0108030a09080a05060f0709030606031a070c03120c0c060507050c 67
    0xa82181d9001a446458107000b69509078400030411600800025000842800040900400354802c490300300070702c0204062003070180442c0d07000f03281c1050440080d51f481c0502c51a42d49000b031452442c1d03507548042c051080d220703a041d0b4120702c3e070242810492034404d00303014054070804040030320804842c0501e035480b0300385200301420100d6200c0c0141880c0a1001c104100c010b00104a42d0f090312409036074001605031500d0703210307a8501030013180d1040b40f00d43c00c00034103841c0307501c1c212000d1110380110380891014010444940c035031114902c42c004d001c0d103c6520060020100013801c0307001040c001203142d500200052000340d003952901e148442c4d641d0070550701d500c0545006032194210300c3c00141921f002c580d020b580441ca038900a00c46507103981e50b040407030300c2d00c1e041541c0b02d41d07105008a0000915141c004d4200d5110300344945200707140d0307074018030b40d076080c02000c0c504544901966007014016a5440030f03d03507001c8004d01c110310f80420002c017a90400c1c04a13400754031440107984c503600c140d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 840459019 1250 840457769 840457777
    0x902011b06091719110d0c1103070909030815030a0f210302190206040c030b0c0c010218090f09100e0115241701120f1509170a171b03070305040215 65
    0x303842c050419444070321400c0d04c000d40c040d8000d40c0e4040e8880c40341d0242c9d0b0303814000903028001e40400028142c4250400904880d0700415403c42c10704203001d00306155600140d06440e0b03503440060821626198500401c010300c0e11b40041c1080620f0659000c44141c158016206e007071102007401a03004912300e81243e40722801d85025101550003442440030680201c00c039a440070b0809102842d00286410040c01c99101d00e900c4006180925599515071810164554002c00b075032142c03036041c1c108091200e0703c448114610782c4003680c2d900ca030300b00e810b04290022041c5503a280441e020850340c0c1e40d414114040906083d0328082c85021140907424003644448105c1d07094146000035503800c0c81241120b205200d04280c42111700040d4500000e01d81c0d44480c903120501c01c4d03001c20040d0062504141e41d05548900120480b8103000600c00903030302404580042e42c3c0f100360a4801d0300ca016a128080d035101611500c80080002000303003450301600038500880c403d4a69001f031740c2e001302c46003c0e40e0003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 840460269 1250 840459019 840459047
    0x302060a0b24040803180a0501080705030f0a0e0706200a03020a0f1a090d0905040b133911010603030801060f030f1a090a0902011b06091719 62
    0x303030000c1c104a405410140003a10034500400c540c07034180c480c4442445d507000120100549808450303042c595003000403a18004000a082c00741490600e40700160082c08000c00505d188103590340050f11880068100388a0607603000c003a681260f44800c801004003140a02d0b410819400c0040061520800034448401c290036901620060703200c0e503944003a50000301170984555001c600300d180800d4440b00464040c3d540b50b07000b010303010141c1201409034500340d80f05d81c0c4241d140c900d065511343c0300c400110300c00389840c407000107080c10007000c080c645506e982c1c20b51000114000366505040c2c40c0d030f8141030807082280c0307a1045036580b00041134261040d07804002d00150104004000c0300380a0700301003a0208183c01c0110b01c1803440c078004011181c0d450f41041d01400c9480c411482c0e400c24002c10f40e000030b9161420310070b014690700040c0400e454500385904041c0c052950905201c000c3c0e115001c2c2e5907205440c1c50091031810710300c200681100c5004480d520941581503903441c0101c2c480360b514a = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 840461519 1250 840460269 840460279
    0x190207170703080d060b0f0403031818020903011d2503082b0c05090a05090411100507060e01060515190e030c0411120606070b0a0b01050d090507030302060a0b 70
    0xd07007140d49210884c1c000003507000c4640e841d80c1d03020895403040405090a1100c04034400d49407451030400400c003406d00c10066055000317450041c4160180c0c03921418002c1005174001d03980d2407120020a004090100d652800c14400485003034035004041003421a140305020b9941888090417004000505c480c0300050200d5020424003000000b940844041c6004c0c21114440b46090210300c80300307980c0c6045003e0005180080e0142583c50800e804601920040d96034801928055031201c030003112000c0c056100f180c000e8050b81134184500100c4a4169002c1c00900c000d002c1e108130705001c0e0000b80103407845900000c25036001d41c0c800c1000e039030010800020383c80c0d43d42c0c03050a00752602109140310396050b0107124101ca5064450b80a481c01c0c51110b1040706985001070000c1e092403d402801f614403078501000054045015070162176001085001e0000f03020103c1001610503110721480040300c1c5003440d030218180034000c65601c2c04c0301d010382c080d1405d581c0d0302e141060480d8041c0c080c0603448 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 840462769 1250 840461519 840461533
    0x1e050c070b091207030c11090415050702120d0b03030f0d0504050106060e03030901030c05041d0f0a02040e040803100e01030f06050a0b031b0406030803160e010206060a030b06040b0619020717 84
    0x22074800c0112006c002e0080400d0903803007603140003040540000300c400b91048281ca003911440f0709500e00c02c1603442406407003e40171001d138140c0024101e1180b102c241c40015200c20071500c0303e6805208540c0400c4500d15007681c0e80110200d1080500701c00c0728191480e518241e00018064014421411143c800601940c588440031006400811404a549080000901010030050520b08140c402000300031005000c52401da000d41a0182e0000c0241c0804d0303005020810100d4540c03600700360840e5100303521544031f50381c4d150132400703112181d8810211400010000800e0082203081440854081c4c1c0701400155201003e12040d0303204d060840d5003661180840030001c11041007040801d40005001140e9030b903072a201c1e20307066001036400444080062644042180c2c00c0b40901080e00020700180080b8a80240060fa014210f8400540812825400a52942e9643e030094610071002007071691192041c110550441d4010044500548a11040451030008908801201c100c3d108000c05203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 840464019 1250 840462769 840462773
    0x908030703081f0e07020a05070812030c0a050705010f0e0c01090f05120307020d06050712151203020f0a0b2703090d08190203070210030203060901091e050c070b091207 74
    0x101d400340301c2540d582e0400c2d007280414104880d82585000301032a0f0700038000e04107d400c1480c10055180d100c2c202a510440480c40444011010399034401c03001308503961903603203250081e43c0501c683d200060483d407910754000d010304020303444082d0f0007001100700c400a442071001595003124901510752040c410f098104081e2a02c280354030000907409098a06044043e800f240410700a41c504a03a100e4070388007001852540030b1401e42d11400c803d0024000360160003c0f110742034070140102c1c900c2c120203080c00000d040c000c00581c0007031180d8508031000c1d42c407181091903021506440305014000f00c0b240b0340d41410a00284803044104a42c00f43d45020b0f5260204880600031071000c6030b40940134881ba2440c0c2d010071805110b010b2680d005940d40c2c503528030410042c440b00d5500704d402c1c14814400d01440b601d6071380529044d9001c005d0001205c0350501c034407400118800361212050380c2014100300140000401410013a0311514260600303854090004d40c44401c4d0301c06114401005000c8000 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 840465269 1250 840464019 840464041
    0x1060f08070e1002072402011b05070f0201200d0e0109030209060907140c06090c0612060d051c0c0203070803030f0f04020d0212010e0c0a060e04020d1503050d090803070308 76
    0xa0f8900c1e4500445d0b101696400110140152062010322a01c810740b0300460b03556028003a10031b00310130710642070b15000000d40c0c02400500581c10083c080514102c810411039004d50504a005170350901440103030000f04c0c000c250345444141518001424603402c09000b03502500100f810740764001c10503400341d5140030500c05015030007020342c1c2c00c21200c18400920407103008020300340040b103000507092030b251208005280500000c11540100d00030001500d2161540b8121030300004101c2e100e55040750141462850500100c4604140c0d440c003410740181e10343c201f01c4029600c0c9c800d03026541c00d142d5808540d500c0340001c403442c0464011b1040040c0000c0303005442a40d002e44018110000c104142e004038400034001c4510103102d81d0742d510f258032010020458965128411505074094604050005018a010300b2403140510f4004c40c65111500142d00502c0000480b524042841a62418490394031260504004085400e20102155194003c011203d0344e03509900e9012064450000b40340d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 840466519 1250 840465269 840465289
    0x3010b120a060b040627120605090c120106050906040207170f07080432060912010b12060132120309030a152307030b0a1203020601060f08070e 63
    0x1c94141d40c0c20b8046080e0030024064006000b441c0d4074002580d444880002d0003500c8490206810540b25200300110340804001d041801d80c491000f2895440d101074551a0100030030b502a404100c81a0b1200c40306030540c044000c0b40d5045803c1140c0b80c40d903074284400c0344a00a0050000d0081c0d031390041404805400030300e400f042d5661200d19200c040d4071003580603009900003094580c200c2c84942140d0325229501440d0030020400300500c540742100044480c412070b4145c9000340c0000d8110889000298048080b03101d000d0109480c0e4544040116160f11003401501150414903c02d0a18a200401011030501c0e10300c2e050248554602c041000248828040a1281c0300c10001c9540741e803010b0002102c1c280c400c00684040c521001020405e840510020483c06005125841307141442c0c0350350b407a0801c406040c00110801020b000c1070b100c0a9030b4100c1e00f01c011103082c410f4105540015124102c0d03500d6a42d004d000700c0c1303c400031540c1440980d04200000c81c00c0b10026920b10707107480c0d06 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 840467625 1106 840466519 840466531
    0x41703030604061d1f0e0405010c174c140f030606040b03030403020603070e0a0608040201080610180b090a120b1b211b03010b12 57
    0x10383d05000240f0b105c10448a07031040306030405490304e03910f0142a004250402d140340a0805a020340507104014000600d03400c00f030039008619030703441402031036004191b004000c01c003000601c0090202c50080c443c0f60b10341a04a4120071000800515004001c141c45403503407034840c0c5812400001741665004000c0601c2c0415683d03004641c0c5980500c0484c1d0006160740950086880c1d0b015a030002500020300106005445401802d10311402d0400c48004e40b03016214a41240c8220301907500a0124032160007045491a04502c0406007120914045144460080c84514008100c0c0d001e02003031403000541d0451414000906409088140449040c00c0c4440c1d580318944240284100c040d0000000c003801801c561100b01c81c02e1000421741000b00c40d40c4140b41c411300c000c00395141d2540c500540c4d924819040c001d006e480c100e40401348254241022230504040c030480c0103081c = true := by decide +kernel

theorem cover : BRFrame.Cov 840287769 840467625 := by
  have h0 := BRFrame.cov_init 840287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 840287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 840287769 ≤ n) (h2 : n < 840467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
