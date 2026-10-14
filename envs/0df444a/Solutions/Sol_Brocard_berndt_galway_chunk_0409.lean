-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0409
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:40:02.633013+00:00
-- url     : https://prove2.me/submissions/aaf1c8b4-dc17-4318-86fb-95c9c652a9b1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 73381297 ≤ n < 73561153 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 73382547 1250 73381297 73381327
    0xf020406080610050a170402040e01050f01030c15050a0503070201060306060810060906060e01050f090a030308060f0a0e070c02031603050f060117070302010e210706020706080c03131e0501020d050705 88
    0x1910018040c151007d56584c008503001c0d021040b60400154a46003c02010018540744107040c2c900505040c0314082e11200307401c88000c030700c694090200300c0520004d02c54074440e000565025109100108140c0d17034030750f660303000d1720601e412584d600d802806810000b040240b040f50000c014242c0d060005c02d203001c0000d032000c03180010240c1080400502171000e81000c400701d800d640c00c0174100c0c407441982c1b810014840c8400f82d400074401d540c0f2048107141460005200010f030780207480c1c074141d55190030300b0544e0f184400145c02c80c0c046c020060081c0c04400c64072507075401180240060003003070902010207414184140c004002d0001c2a080c4001d0b40e500001e107100c29290b0a0034100707205c5000d0310010708034811000c2d6a002145036100c1d0419000800305180f011200d00b0340807149030545514040d111600304407480c2c92101c0003480080c0e1105003140d60590700328056110030380049641c811003200e030600343d442940e580c0c3d00012a08036410302c91003055406012480c3c42400e000c0581803800c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 73383797 1250 73382547 73382567
    0xd060515010f05160f030c12050a17040203070501110703080c0a0501050f010e0103080a030617100605010201140f04080c030a0c03020d0804081206030304080312010f0509060d03030903030f020406080610050a 91
    0x1101103009000c0305d0802d80200080c410780e80d0004044c0c141103a100c1c1c07004002c3ea010b030440764006040c070600d424002d0201d0410328021a030040c040e00c02981040011901d42c01b401401e600c5c00e10459600001044004c4001d040c00d003580e074003824891480d41841829200c02614111100d0a0800100046000c0c007613094103495000c1526170790317290354100860180000750424170080c1003185003100c5d21640014890015080c991090000d15035400041e403ca81010b0700d0117228011030000212116100d0401650003445140c001d8244103211440c24a9a08a1000c91010524000d071840a1503010481010258543d252292291070603549120550144802d188061071058012521903035090050324068510002103d4586c0400c0d1800100c42800384103090302d50651040105507802c0041403584603003000341c001c5203402c0c00c99800301d00a0414981c15800c00d5a40c0b807001640d80c40e80d00083c001031103107994440041c1030402c200060001041c1c59001807102c100b1607507403104d070401e1208e1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 73385047 1250 73383797 73383803
    0x90103020924120c030601140310020d11030c04080106090207110f011403090a140f070506030a0204180501180c020d030e0a0501022115060702040207020d060515010f0516 75
    0x110701401942c0310b9074102c4090301001c0b64440003040c2c078801c6040c00000c1c4544901003c904640c0b60b030b607036814044103400c404443c1a0701904819602036030a5540d4006040b110402d0000140003220002c2a00c403a80080c1c560791101c0c64000790402050b802402500044c1000720310451414480d035544004104140003201d0180c8550720100e03159a00074140c50043c01c01072035543c0e0385c91400724441512440811412035020b99009281000c400b00010840c0c0030002410007000b9007424003007040a11340005140c0c80c00e02c0c5e002c0001044114110404102c1e4003810000410254141003400f201c000604d520f04000c1850702030039160303941d0b001030505000202c0d1309000651a06e14003140341464511300307010344590b0000608074a0045c0404614400000340d4820401076194419184103c0d610020601d03440b81007401005e026103003540c001c0a52520082c14003d002c1103990f640c1042d00e4040f01c0c2c1515408100e45002d00d107581184010803100c0c81403400030324181d03848246451000c4502005 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 73386297 1250 73385047 73385071
    0xe0c040e0c0310020a1115010e090f01110d060803070c03060506120f07050a0f0303080a020f041203020114070504080316060209060c0d0e0105070308061005190207050a050901030209 80
    0x103106940080c00090716081e000703419105100d00001d2900040c1d07101c03038502800181c101c84410b400c29008102007006000740c0c03d080c082079190001150300107001409101080c041d40c6416041d40000344600d108881120803d6600c4a0840521408850160348400c0c4582c004000200019402200000550741d0090000982e601d50b1000b01e00240c41d85089120944107503110b80390181400103044003100d400711051103401e0307201e01c80405401c1c9544001004100745c240420620b06d0240c004c0e0407115031501c0402d0030103a4960941c101d4002c0d40c0ac0960160359111041d01e66150440c80082d444081e50414514081c900340c9411ba0386c2c46075800740c2e8013801d0941010000c2080a40485080c200014106902d0785c9101641d01d465465082d9a840425480d80220070154051026070b41070719015120a2555941c000c20301000314100103402042000c20004642c01118040f0509043c0c49264000c1c0910790070300303080c0000601c641d00414403e244d0f1703000400041e950400c03503a6014100c0066 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 73387547 1250 73386297 73386311
    0xc030c030504080312010302090109060503060411030c0a0b0a080105010201020a0e0108040c2409050d0206070f030c050303100e01080c0306011203090f1d06010309030225030c060c0302100e0c04 85
    0x82110315002c0c1e900310b0a01408001000e240380c0840310451410707a4001c4843c1c10780c90b40c1c3c8ac4054000c40d4410f11031070380c050f00940c0c00500030031014054503010703050140640b95401200c00001b8810200e94204842c404000b00c1d8030000070394020a564050907080c0000c616148140001510300c640b0300045c0d904210703007000050100003505a107100240032080100c1a035040d5190344038001c40624040c440001d400e0a0000f1301440e080c001140b10701d80180032a440d00c0c1c41c9445440306070341052000d070b00f4045500803800c0000c00c1000103621524030b5100c500302650800041c0b461800040c1e022110383e50064041c540650b1f40031610504548081203034a14010381c030b10b0142c6005070ba542c052901907500340c0340024501c13600d240f492482403044034a82010382c0e8034001174044800b00c2e2400b81c01607220f00f00b58440303100110050380509442000d0300240513a40d948942c3d0004e1160040703400541c5a038005000c042e010000092544c007000410301c44151400c01c0700303a8510300c180c0024403954940c14 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 73388797 1250 73387547 73387553
    0x1203030b0111033414060a060f0506030c09121c05031605160f0614070503090705010e150c010e0c060301030b06100302040503010507080601140408030d0504060b03161509060c030c 79
    0x10080b4441e0f0304e0b130100d4201d000b445040ca001000807688014905015030400102549443c1c132402c0165106455000717036546c02c01050003549d0f04001c200c0b41c0e040008200c5080240e485091441d0042c20450040282071400809070514844401d240d00601000303105003c0040031900070070120400c03e01d017540e11800191902070701c6007804030014040c401098844000d000f9190001400440021a011050b4461580840f003510080f10100155000400c091000703611440300c2104401c40140110418068084182d040342e0145603980560382d034610314041c00e078000740318014520344211440e0f411985142c450394070460700105180d1250520118003550741e8029810740c0c0146c080940200010300d40b0b0702019000d0030003500c0450204d9040c40340800c0a21515080714107441d1880041e60070b00f25804c0c07008c00900005041120041d4032142c0c00d45003503d0401c0b401d0390b0f003021460782200280c58018044859055a400c0004000c0c16040c14009160020040e00049038145000101448281 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 73390047 1250 73388797 73388857
    0x5120601031401061211040501120b04060515040321020706030e1905010b010201200409090f050307030512070206100303050c0f12040306140405060f130605011203030b011103 77
    0x2d0800c004254488008500701e54003019200204030003041c1000140094008a500390095104240c0021034109400c1e1080c0981c0d04510001d060141010444e9620394002800301c0851068000e07225001082c1041405203082d04003840d040030711402324205045600094490758a07010b210140768407446006502c113000c0080d00200d40501d0518000303c426441d04901805001020500640c01d00c40c0301c5182d5190300510690214001d0001480c103440d2a9441000e803011410980388035400103d1040030800610080460511070340e41c042da02c074545e58003490a400058000021984140204a001e050003c02c007015240c16040030f40d1184a1420b0580c6450801d50030740340a40215003014860300d805002800581c2d00c1944180700803c41c0c015211455101110050450b500010120b0310081da40820b46801c0340791616000700088042c2c560900b075403400c1e8044541420946008410700d0307414802c0180c0c00009207003c50044510800301c5030740303020705980c9200100203000c049845041e20 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 73391297 1250 73390047 73390061
    0xe0307050714090f04171201090e06061e0a0902040e06090c0705060a020c160e0907050603090d0e060408030319050a02070507050103023103120207080d03090807240c0c030512060103 80
    0x8106c90036990781800c4000a41c0020a100b544e10403410044850b0000303102080380ba21030f01c030161010303018000d410096546072101036002c6400c541c09044c0072a0202640c0010006044264040b03107450501c2d4003400305d80b0f140181801c034020300c240b041100082010600d9078004103405800351312817560b4013036030f428043d102c10540219070000707100040700441c0000181c40707981c2e854192015a991401880210700c0103d98046242d045100c4002840740075503589082004058082e0f401c0c1a1160096461584107982214036000d0b1000d0714007070a1850300400b82d0107003030b680c0154203140c015540c2d9039584241d07000d01070505401151030800340503050107c05410500501d00410000350300ea100340c6031807103800252950100902011145e0307000044100454800b4030040102c445403102c02c0300101010301c0c007151031030800c00c260b10100e50f202c014200302003400400100542e000c5e0421000300c0d65003072941010b00142c0030850011039000010342d50340c840118000c00d225910007004030000d041c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 73392547 1250 73391297 73391333
    0x20a030f180e090a0b0702030c0a0b070203070b090c1c33060314011505010c03050d020403060c2601060c0b06030106080607050d0501060c0f0204020714010e0307050714090f04 77
    0x303142c0c1004240400002c0c4049164003030103c02c000c6448100701240c49214400e2621841e52000f580700b400242c011466a0b444400b502c152810050165203c030a005001d4840d54102c2c1e210800044079450f108a540240c007920302985461960a56900c262030030b4842110b0100030305160714040d1500c2014a05c0c56a28480c01c0200101903e900c0d11459080d007507403120300d031907190005010b16001e6800c03840c0d00341e0300142c40c1c034440b03c07101d541d00310b07110f6001d5462821029001d0000000041e220700941c220030100361681401c0c2c90858800010503049075208460884070940100051074014203900d800503003040c0011807540e50800843e01600c9258050005442000c080000055201e0054050030380e80700420300c0070340da03243d20488003c031002c41f01074a90001070422000500d8070303900810351140b040c05000101c84e22011440d0860744505504421608005814800c114080c0501d5018000e0919120410184440403491806005003080d0200c081c610126003403008124054145082c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 73393797 1250 73392547 73392569
    0xb06030115090e060a090809060d150f050907020d050a0c1a0103060621020f01030504060920040e060f18070308212508060d020909010203090c01020a030f18 69
    0x2d81d030007499006014031005541d80340119004a45488414020801843c0d0007070540c90230300744800200041607008a0607803100070b656850182140061840c5400103020400d440d2810a2812003071202100e0300415a00c1190019401c0c6c103e0b032604a0240c1d100c002043c5490b074510000740c0307020b05d01c40c500700724803411000039500000200141d40d0091010344026080110207030540552480c0b0103050000000d44c80322039494a024254801c0d406268014000c0c4004102c2e41d0480d210300082e41283d0202d090040300039401100c40b401c041c0115010400324a009100c0c5280c11950f42c070070640094452a01d031007809041000d240c1040000f0344c05141c100e00c01580d80c801c0e120300e08440911440b9403d18480340c0c40b0000e0401d1003002c03000908101d0400e0499045d85d14028101c0d01c00701c00410460740082c0004090000d81c42d00008a84105520000140c0d0703030414031141407904424024050442d40a040441b000a5200f14003803940e500031f051080910218031181c012050389a00140b100074 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 73395047 1250 73393797 73393799
    0xc050904090b150d0b0c0a121a030c0d03140a050c1507030f0902030606040f020f0d09050f060108150901020d0203240105181507050d02030c120909040b06030115 71
    0x180c00c0b0036a4050100321440076900c000e25400c0c01940d10036404050f003031507080c2c1c2c0054075804542000f002c4101052030005404210007106e0404c0381d41501c01d02d000e0a44038510300c5503600b41040044104103003110818012105564001c0400924101040c800c40b008500e00c010240038100781d030b14140101c81039036200903040400804aa4040b100400024140460942007000c9403055407131454001d000740925a4580c4244070241980c6000121560760800040c10201010300103031400c44a841da0101c0d0400c881e013022481c00200c04803c14046c0c10000040040703120014611081400c41c860400e2140d860b41041802402410b0340c100d0380754000800c000b04000e00f5030401c6407603511941703038081c08503d0305e004649034060105051051443d0100150740341c50302c06a04102505851141e0780781070075603039038282050034000907040564004600301000c0041071001c8102e5041d510031050403e01028000b4240c040040d10207484200c40b080451820745080d0094030010404000364403102d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 73396297 1250 73395047 73395053
    0xc07060b270f06010801061d0d0605100303030b030705090117191416050303043309050a120f0201050703020f070e1008030c07210c090f0b03060603100c05090409 71
    0xc400b1103030a8805240d200000f003156016403400b03410307201e0319030f105130034010000f40c103070300c1542099035190740701c5050351200340020158000c40d0302c920312a4101d1404c00c2e1641c42c0c05400e035803002840c1d91194211482c180041c0d00d40b1030b1420304440b030103280000c0780d0941c0b52045c3e0400c4441803402e504101d51800e103806010103000d2090314020400d0849110004074200c0c0700607011a0b0103802e0307054000f000300b0092180b90742e60034201d204c411403116441c40310071405420b40c0d80c010a101d20116481d840c0030030075450a601184010103030700d0044e42c0301040d44d0381d400e11924444480241405008540c41d8203040c804c00c50010348c0101c500c12900c0158880700300c1d641c1e07442c04440070780303901107a008041030354540401901c0961441000504c0c1440c209102c07406a00300c480303c004030500c03c403111080454204c170000002800b600c44001040012100c036035055800f025500750181e40a003042c0140303520000307846a03492540480010b600c0c0341e281800c48542c4140c840c81644076081007104024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 73397547 1250 73396297 73396369
    0x19021602010f050903060403230c0604030905030f071a040302060a03050901050a060305100e030f030a0e1501030b04201002030c06090a120f18080606030c01080c07060b 74
    0x1918000d89550188002000089520f84501c1c0c0350240c0540000001c10000b0f8044c1c0741c0140e500300b400314004504031056038869041c2e04124541d46c8154030076170500003410f0b0040e0000010740825800384c8460f50700550140d656010303030f2040c171140e50007814540c0320208841c820b56003e15030003404103a9589152100030301620301558034144030b51a140108030551282e1040c50b00301e90307100c030190100c0300c140c68240c0020f00981003140e00da80010400080340d500360030300541c490584402c0020789030300040c100f6803a292203d810784920790358071001800455052800d00342d0080d4045c02503001c03210101240011a41c46003020303038010380e650007038121440e0084003628008116408072500c5541f444d140c0f0f5038840114001400c154542d40e80e0110b440d2048a40c0710540403039003080c1e05205c080c40a107040c460080e0f841200660000c0050000d20f190902c1400c9102809280c03880c2181002d000021040c40307201e0008041d5555440401c003191503c0500e0500c80d0403840c409009440c40c1140410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 73398797 1250 73397547 73397587
    0x8220209130c0803031b090609040c080a0e03030f130312021b010f0605010507030810030507030b010e0601030e030421140d080c1213020f030604140c01020a0f0b1902 73
    0x554020080003c90101c1c1e002080d00c6c40b5208008180c0c0d00c00c03140240c0c0d003003190310a101c101d4004e031040003a040c1985450240442000d195a6000c820f0f00d01000b44074202d41003500b145949401c101b0606c11855440e0b9000c40d003000c0c1c0d11901015001c3c0a103400e13100004a00443c0c1407540c008510842c5001003c400004903030fa408009102040c800c1460720210b403080e029190100340113108031004644a041869032120b42d0500c484660b83c0c40703880da80d140c210664011513000c40c5140041c0701c5822000c0000d40c102500707090034080d400d900503a0b0ba489000341c0c090188803034140c0a5800c1c45140401408030341507000700154040e07001189030b40c0e40312000300350714001080403480030941000422048840e00f01180c3c03401d47d499103c3d900f4103008901002800c4c0c1e400003582c42d92241e140e40900c00d05025503c00d21410310300c00100e035079950810404001e880d05540007022440b0206099440c0c0103d85075000f4040d004554500c1c4550681040880c800d0106920106001c5889440045665 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 73400047 1250 73398797 73398803
    0x13060e0d0905010504080303041b030605010803031501030c080a02180402031009050c0703080114060421020907020a0206040306051305030403030e030c0405090a120e060d050f010f03030822020913 86
    0x41c440c03500d410041d1654130892217000c0281c0d20400001d40894407800003441c0c1081d030505007480d9180e07651640c0043d11001e0300400d0300c0380c0000081c4181c01e401034001d0a1240e01c207080a01903507001ba1000b03414040c000745000030302c9800040c600b0720801c080d0909000e0010050085440381031400402d10707a00b86e580240070071300c0d150002103030305040e10100f038800c810b902d6941e001e003607800c00c03d10005946031340d03038480c2c1c101d030080c4004248009a0f110001d00c182c010040b00384c505200d40100420b4007000b40190007517420484104016840740303402c40303003940d4020340c0208190300d035442d803221403011009000c0c0c61800302007008010991301003014940c0142c00c4084a606420b58410801201c000b5108011182d104c03100e04000104401e10450301c6a10605104000401c40d4001c52103aa1010400c003110765650800c00c047e1403c0c0341840d902400410620b4030f001420350380c1c050036000d4080c0460826206142040c07110326480301c1451140756000d80001d041c5d0400070900e000c3c1c1c200740e400071 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 73401297 1250 73400047 73400057
    0x12010c05040302180105090a020a090b030414060105010503190e070807080609010b091612060308041508010e090d0c0804080a080c06060111120a0c020909070e090a030e0913060e0d 79
    0x4140c00e0400100954181c604c0207280a001d48c031a00918030084d404517040034280701000e8800035851001d80003031485140540700c130383c1402d11422519404c08505801117414442c092041c0240301039806400ca0341e605090100261b00030006281603d0640190f111079100d1040034004911f4903800300d640ca0282801304000e00107401484100540070b0310840700e810084030040b150070205d078811a00c0d09a00301d81d14074009907450322901c0350035081d84036070049581c008424048401342e65000001e42e0040c280207000040c3d50400301e420030340380c0340c2c2c104030502044407100001040c01491001c45004103451340440e04038200919005049800c480c20f000190b015450011300994051484401e000150f4000381c01d841e030110700000055004421100e041103010411800140c40b0b506569004c0c103100d01c01460000c0c41c0c410401c801150043c601c120b0741d046000440d0001740c01c2802d03040510f4086403003160b1a5160402d600803c1107001c00940207e0030101c1c0101240c0002c55480c00c01000c5035a5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 73402547 1250 73401297 73401319
    0x80a140c0706050a1b03080f151e0307090b090402090402060c0102070501050105120c0108180c122119210203042a031707020303120705040e011401050a03090212010c05040302 77
    0x25001444150301801040911000843c8c2c4645002c800354000941e5000d0700000d885c80707000c2005000c0200344202d01040d908516105441c2c20800740c0020550b2000500c14400e000020800c40480904000d00030000c49021504640c0ca40d4244e0b0000c04100008640b130300c440e400e040b4081c1101703100311030044101240b100c00010000c00c0000c107480060310350b80106d1320f0708040c5080c00511006800254014156100c00d2660b42082880242d00f070540140501080b4041c014000c0080040c030901119080211204041d1041c03407109100c025400c00c0314020486803840310244180700c0005165034800400c0004002d0807040c100d01e040f46070003892184a11000c90007440c0c0905000103487c0030398a40140d80e0010a4200505099101a00b0713681000710081211050941c190354040201d07501003414880000710000184c01001081e00c209a440f0200c00041e0451080c01180c80815454000302400d64541d0410710040e0796a501c020402c17018002c80040c003d40050004034032070074004d21 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 73403797 1250 73402547 73402577
    0x20315090610080702010b060a030915051905041a18010c0206060f1c020a0f0602010f0204050a0501121103130219030320100501060305150a03080a140c0706050a 71
    0x24140d88210005010075020a00380001074030001c0e0020400c00c215925201510400e07250302014280e400386a481c04140540716140c412301003940c070000302c0200c0d4506020049a10003081660f40410400080041ca07501c441c100003210000d50128140c060780c010f41071100c020020014241f9288c8208001c2003000700742001261600f5003030741c4483e8412040403001c641031400c201e1403074608805050244ca00c3c1440d501003688103c06600071000605074520070440c068081c09054410b0414910852915082c880001d0700f0ba4514001c041c104699840c0b00303545513400d5070102500d40490b1910344e880f843d000c0141c00f80c2241c6540300728000d54803010f128408501d4181d141058950540728154080c0035403038904521400d084d40c02c402442011142c1c9488951441101d0180009a80101c0ca91a0080c0b001d40f06400b04014540100a010310070000b2407500c40684100340c48030310741025020100d41180ca41030080d24180096401a0300340060ba03a0380000c014580050340c0e40314840e800320a03030 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 73405047 1250 73403797 73403809
    0x1201110a09090509060103020f1201020403120c0b130f11010509281706040803042a050a050303070c0501110a05060a0b0f03031606050414010c0f0207080706020a0f0204021c020315 79
    0x81f10094104451525a0325035203040705620000700e00c4903000500341a60b0f510780c940342c000022001404103210a50300c0c0d0600808108d0140c0c0060a490030008001d0307190380302c905c110b0a002d000f80080d02d0720000080c07682e104404440c24080000d00c0224074686000741040107a00d130100186c9520441040080c010700c2c264617190b039410300003004c0c1069a945456080709603100500886c0c854a140403a40008040002501011080c0a040000c0795042106104002001b0b40129100c0e0340300340314407000545081c92030000d40c0e00a00e8041031003250b68030060b1034130505c402c2c018500d0203642c02300007901c851035000c00e04510702200c0d1600c000d503440702807580364464201c55014010742e090702940824030581020390040c0c4219502d59111903410703252130866011292020004407594443c0e184164100510030242c11050058041b0500c0e04801a55039210140c00400c6064910130403000d5607030740e60580356030100d03000c811181e100c3c1c030440220083d40121060780e11101380b100800c20b141004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 73406297 1250 73405047 73405049
    0xc0803090601150c0201020a08030c090a0b03073b030705030106060509030601060c0215070f0b01090902190f050114040b0f040801151d0405100e030a030f0b030c1201110a090905090601 81
    0x182c022388110344058a40d84040d85c8014501145440c00f00100145034840c40421402013256051140d240d0030001c10061241140c4465425040c0042e1034005643d5203405a13a078400c007861100c440c0074640716001c80e007401070b00c1e80281c3c0c3c194038200e0000751fa560000d0042c80000802c5082d03400031707a2101020b9901c03880c049006500001141c1000c084600e10000034454a80168052000d0050550343c540d04104240c1011b50429160f807000011401c28108045056130208410301d102400c2803c1103c0280441c881e0a041100d032030303058418107402404907006407505912160741d400710344070f1440c90759210384641b0900f9842d1010340295400b44404120a03280d4011030720b01c2a220482610000100c00b5105481034010302955035030b0149148201507003c2940300155031100039200010b000c036925190b241506500f03124101c205130794081011000301c00200d030458a2400100c045030700401c0d500b95240c0c02c02d9000a80c061000303410802d0303034045030881c40302808565a0b402e02c0c00d40b40c201c2 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 73407547 1250 73406297 73406299
    0x7050405010314070f051b07030305041e0e0c0d0e01020406080601080c0a020d110c0301150611160e10030c060c0c15020a060c03150b03040b13050c060a0c0803090601150c02 76
    0xa40445e02c1c03241e40c8100024660f8010303959100e070036081000d24a030b04000280c2d0084000c00c1d000a01084a05001000b1405031191080000c0c81c551034108013504d100300050100403c2d0f10006502c0401030b029038400e40c01c80d11010b0085440300d440d04c1001d030203890705482e0b0501141201e0001000001c00c40203d898841d41903001d0702c03e1503d049016a86005801d40b03581440c020001e66115036282441003104450240c0480340b20340b460b07e40c000c0c1228203140e0031103180d600224100b030841e800100113401141c0d200003140c42d070355590028102801c0c01da031300000c180f10400440010f0440d801028980b0090059046038546561a065000406603a14000c1c015030440300d400e03000301e0034070f070f001604000c3e09003408510001c03200c03244141c0141d0703500600f140030004000d00092005924079203034490242e41d01c1c140441080e4803000d51724007500e807206104150015114050a1080c2c10081c1d03100d521a60898403400e020350b8468903840c0901845607415007031045110454030036075941680b5a0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 73408797 1250 73407547 73407557
    0x11a07020118030b190b0a060503130206070221010c030203060f1009170f010f020405060d051003120309050f12070b180703030507060b0306060f040914060705040501031407 76
    0x140550055074072926008940503041c40815000012400101d4818070840701070861003201d2016100e10811244019074084c0287d0b0001d4081c03002d507420000303ca030403140c80d0025242081961001950a10a92200a42091504c02940c201442c011100c1e103038107100000038064960740d448220100c1c00b00700c90fa0380d4410005070500c10a800c01c140d003000440700e40d25003c0515a200c0611880c2045140c1c86464580d02c80030091441010a02c0b59089500049005526082c81d02c1c0000f041c6d401114400d00c03105559001050a280c44080100000c3d640311162240c0040000c078044e00415580b48195403c1c020405030303a21541011032140000d038141d44d00365050607203944920f154640001e000a0800320303000e0000c03108207800c2100380000d600c640e43d0280d0740c144901d002d005a03441010031030f00942c00a02800348035640d0040c2e0146c0c44006507000034070b50500d8240301d4900d032840204080c0c0c501542081c07101d50342d8002c000b002540d00030380382804038048901410700038100445425002030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 73410047 1250 73408797 73408807
    0xf14100807020c040617160312050a0302040801050424050f07051602040929060f0f06070c060320091305040302120a0507110102010902100e1311070605011a 69
    0x1806540352542204407481110322a55003400404c2c1240d401e5000518501c20000076090f191004024800541001c40907089080380b540d942c0ca02410000c031201c405210700032840c2c00701e641c401d605550003081c1319402404a030030b140c03c0c9481107850315401d00c12003800100314464102c0e01c078040c20340102410443c0a0581da103552044030b10703030071240c482050302e16445645000350352140100c07000309020f500081c009213040011412080c86181c086440501c111042100340e035200b81120f035000300c3c181d4040301108103040020341076100310030006001d0b043c02d0401140103941035100051000c0740c400d4502d01c842c20000e1a0849010744c044051303001070315801c41e400d04012504103c0c2c00501c83e0049588912040c00c0c20061500015110701c0052008245c0300c0601403c1c140d0925444004e00003040307810002d401141c1604801d0b80000e0901550510701203064550461851450402d0081040b140c0510320104605501540050302ca19041c840041100003008004215060311703018114504 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 73411297 1250 73410047 73410079
    0x60d03090e1b07050705030f060f1b120f04060b1c0f051c02010c08010e090c012a050309040b0f09190204050904050102090a080c180619080303010f14 66
    0x1007070020811a122016440340000440700c0901808800344030b04058807460b8101001c3c14078200300d440c0103003015880881480b811002030080c00303030448507100c05149900c46d0007482040c644642000a0f1101445004008805101c40030041c011440341e1410b2061080300420040d520800404040c0c00340f007200f070a4800181e120705503c807043d110700145c48800041d003980040c0300440300c0302d80740507075182e068850320aa84002c100d03000d0300310780351300e10760500f004015681d6031070340b2604590500a800c1600c403450030701b40f0900691240305001510451102e450319684a41103002410b000d1401c0041030511031414406410500d42e02600168550795441c0b84039505107007040c14841c041344e0030040445e03207403103552000e403060340100c00140e6107101a105001000300d0070790045072181c000d0507400a55a40d1201d014590340c00001e500905a101c100c0010440703200c03080d0f07101c400d0302e0505000401d12000b1024604903401c030304201d03c00d29507030401c00d20b103100b0b6412955803052071684030320a2 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 73412547 1250 73411297 73411319
    0x40b0709060305013006060f0306050a02070f030f0314100305060a020301050102062d04080417210703030608161701061d281b03020708180d080403030512060d0309 72
    0x94405617995000da03070b04a5880d04421904d441d04841115170240c3e10900c20f00c03145018003a00092010303811407500d2201d07102d120b4a80310b960401000c02010010000106210307400642812003030107000d00290a1100c034403030174411648411500780c003459000442140c920310a490417114181c01420300c40d6036202d11040c9001c00c3c0b1000b2900d03040a001030710800002d021070350b841130384903581c02540c482c1400c00c2d0400d100540180c41301194801c6040d8009102a100a10701511070710400c0340d200c044915068018045a4001c03281ca481594618240c2e21008100442142c240b61181c00d0b54410142045099070f02600400401026040c5505208140007440381d5028509039200242c0728500c1160700d10a2080704090442d19444101a42007520f9401d06111480194181107240513003982d0ba0748804d001e20900b140d500f8200a00f51600d0341c0782c802c5000304107075100f2581940c0399113921340034205401ca038a0401d548a4408002405428007000000303445800d074503640300a600d0042d03080741c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 73413797 1250 73412547 73412609
    0x15030b060315070306060e0d0201020a0213060902030a0b040c08090616030b06070615060e0a150e030a06020d05070516110604170303010503010b040605060a26040b070906030501 78
    0x2825109540c91884002d4440950320b005889607500401c949281100c020105000c60908511a445595030500180e80019400500d19070586003e0500d290402d03048000301220b501c440d001d94000410003030030b250325511044c007454007101c0070807001c14108030448604000721a5040150f211030b010800034040e0400044401111703280c04a104180f04000c515581c020340e000326040781d222032032108290b4119080c2c4001e040700b803403c240308004910015515403054440d50080b00198503c210006114281c00944044040c00310340c6d84005d80c2c13500200030360010701c030b424180c0e1402020a211a10960031100381035100c01c041c001c0d514203522480c41d00500794200a50280c400c000c0014240880d60002000702501c1001e103859601d00360901d8207480b02c50900f5481a80b1340003041c0728544d1480142c4000a990349052060340d018042038000ea666118248104868040d080004108031010340c9441b41401da615a188656501c109405880080c0203450180310030082c00783c1144c0026179150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 73415047 1250 73413797 73413799
    0x151806140d0b13060603030c03030501090c0507060902030316030504080c0a3b130c0b030402180712020d0203040302010f050f130c05130606110703080a0c020f0901060302030a0b0415030b06 83
    0x3c483d1400b1662090100c03000c42c0d00450108000d090300c070060580500c5000d0051104040030710000341c0300c01c8010100c2c1b1401a0007040d107555402c501c4159102002a60301c1c54000c00003061241c0322900340641030350441d11401a2500c40c441c4005400d00f030980500c012155400d4a51079070840104590700848484501007565800410000010296920b922030041e2801f0b824111410258106091049403a402c0102e104900704103000c0161214240441a4002134811040f1600d030800106c6020f8101014003100d14004141580305100b17a60095000707603c282c008000b00c13480602c010007507507021640348041e02d2110b070004084482c410344103401c161181050000c01c9446c0d4000904081d01c0b40307105801c843e85d07480c040c07206540007003030f03454000c640d800140701191a55460b092036104051468041040f140c10510454644400b80c801441004161343d8843d07031102c20081c000d400c11680e50030320a0420b045982c10b400c00e40300b12004000b40c81d104424017030964443c003903800c0c8064842 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 73416297 1250 73415047 73415071
    0x10e060f13060f030f05090303161704232a04020706020f030103060c02031303150f180c090209060301051215070c02010e0103140f04030201151806140d0b 68
    0x1c865a140d40d01281d000d40080d44a41c0c0300819103075001012101c0d4a020600164a4141880032160000040c1e80c0d0010040d42c0c2c600740d1849105046442c1b028107801e071f124000803036050200300040c0240d400b900c2003201d0076002c1030b003180b40c48855650010080d01c8560b548004900d080f80050303403411040c9001c0241c40036140030019a50b08040313034400100800c03084000b00c0180100b006d40c2c056560042c003d8402142040c210101c0c014104526200042400d13100401c1030240160750b4105015000030001c0030071825240c07810504d03010410070402c4903140408003000c00c1e01141c0380300f901d40108026146070308603803c14042c8500c0c40301045003580b1900c12820105e5040f900b03508414410a1035a40f5a80500000d20016208a42c4d030406c581c10701d41091a07124000c22181d20480c0e0002080c002c40072140c0307450506a0041511041152140c8000600440c0b40d4812880c0403140c040410390401c41d0036620744040d200c008002e442c0b158000c00344540b030404161198812174100c20704030b00c1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 73417547 1250 73416297 73416307
    0x5091315030c03020909010c080a05071b0b040b010e012108070209040f0b0c070807020f0109030804170f0109030512041704031401050702070807050d0c030b070503091902010e060f 79
    0x19080e00c0340350381d4012900c11a00c88801d10850030844d00840d0480c01c440001d0010110f25400500818802000303000361740d603503000044400f485010749200540190105001010286c1031541009a04035400d881150004000040e004240300b031090407250021140590310780d450714221010140759901341c900300000d01290001d03940e80d96003180154071848810b1101d440c2850010f04a41c1d0041c000b071032108060140a01040c0c495040303410860341141c090410405050041e92030010a4201801c004000304000c509103041301442c20100d20404200c030f11075402e07513056600b8ae68581d50000d001980c148841c00000c20f0012003035030401e114a40f808080e000e0002034520a4000e0fa00a9400c5e004c0e044402184503001e110702038010b4030343d00c0600cc079a0f05080000e03585803410f10845000d1410000f03c00d0070f000d20340300440040c550000102546042040c0020300c6900705071603819190003943c0d802403c031900d5006a070070941d07042c0c44031512051040108583c58000d001606564030040103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 73418797 1250 73417547 73417571
    0x4120810060207061d060301081e0613080901110d260c12250201020307030614030606010e0102010b0d110a0b070b06300d0809070b0403020906010e0a0b032401050913 73
    0x95030113800030600810450224415414012b111110720986580084090003803090103c00c8100503150860a0b07030340e845001c580103c8110b0307010000722186000300c2ca1003604041d841a0302ca52030005000001c08810048100d042006400b0758424078004810028890f0502c0c56411295010102c0903600c20104031074840c40c1c0c1d40040d0183c1c1c4400503503000080018550300742c8030b2000035040c3c0307140032400b034603039007010030383c0e03442c2c0940891306000c0096503081e000d0b0301c00d420480205101404100f004030b01e629009640e40c00720018076200300754158020410203000810740e84040d030050031000703250b150a81030004024020481d180b01504011021054007510b0108241c039880150040041a041c1107000b4603100e400340c91418150008001000070b2040d250940f002c1d130350100c0381c84150342c0710900166226520702c7c41460304204400c40024804082d04080c5101e00c83c41d12152440b0300000000b9142104507007581030100f101400095198104000c11068070708601000041c400c40c285 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 73420047 1250 73418797 73418809
    0xb22050d05060108010c090503030a121107081305010f17060d02040509030a09090c0207210605070206090d0305063f070501020c0406030209060d051504120810060207061d 75
    0x200507245544601d004100340c036402d201d6030361940910725114460b9414040041d403030307210390000c1100704040c4412181e0300c4100b50344104182c02000b0080c6940d8045440c01840f5074111492041c980e0b40c0d4040d002485502034090a04082866034601519200703040d0200009000900416008070044041c2d0700140c031148117160052181000441c2c0fa4032000f24010070384070103900207023003184c24244c0100f0065000101c070740544040200403c40d2210351004401c1c3c0364101c10000c1d040c2811b06040c40401c40c0c005c5103403401140ca21042c0c032442550b60109070b0079103c0540722650000780c280c3c50303c90809090314120300b00d80703071702a07207840f9900042d05980b0001c5030591001c245604800c0d002c01196804004420741d03080280e038240710451654001a640740002450319001d00041460030003005030600c8605c003100d03207520504200c0d003810f00b00128041810b5800070040f540080214000c001c0c40704000d022100103600501502c2d00302802298116041041c000504941480c82c00040e9910 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 73421297 1250 73420047 73420069
    0x102130e130f0305040e0603121c18080703180503060610020115090509070e0f0a0b011e050403060501090218060c0f060c03060415080d18180e0c04060b2205 69
    0x79651300354403181801000901080c0282001d0310a501402031200c0c9000c00c0425143d4100039204c140c2810b03091903c101c005060081300248110558040c8181007107600005040c1c0c56002e50f4510346901c06141a114119110703000c4c8030752680c80140040c140e841c00701c0d00160101002c0c40049501401c070440d03850700340a25000351003075544a204001d044102008400300600a06c5812845418600d140502010300940f4900c815500c3d4650070381c0c60b9025540c02245035000c25902205034500070b000428681190000304c800d5814100001000b06850080d07c2800c030260704500f40882c00d403020400954407403085100342d801280c608140d562000d10081e4482c03010100300d150781e031800c202000115468481e004650190b078500a004030310001030040745840c1030b401e140c40c034900c0786034034108004000d9104441c0a540c040300d01840d12a550081031030807221b41c0c21070740944c903d48100000d0701c0300780c05040c4501c04103203d0b02104140c10740395080b04c140880740030700740d150b00c510100e0510015 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 73422547 1250 73421297 73421303
    0x3020412140f24060604050a0602010606021209130c09091406090c040f0e0402010504090c020309030106050906010f05030a09062409050403050f1305100201060501030506030102130e130f 82
    0xd0300d00041507800040c41611120040e0340090045441020800c182c01100340d1050030304401d00400150f05912040d044901805004040d80922561184001e010b0100c42c0682401130280c1458500d080300e00005541030103000515030f05c40d607480c00c52040c00900300c03800704004014403900b0008bc860964030416203030b140d105204914a00c2c2440602000c000701030300c0c423040160100010804400032207446000e981209010408a40312400129003500403a040780300310f01d01e0455080b03c0f43d500000282105803065000f445100c0d0741d02c0030440340b002d044403001c2c0410404c425441e40d107486000156441841800d0000700000d55440c1c00084802d002540c2c0300c1c4403030898064280c41c08601d01400100113150303003413002d442c1565008103640a1841d03948080440807990f80760781d07070400302c60b040a030001400045140c200c503030000380600344900c01c03640441d16242c081003550506000b01d80c2c0c2e07190200070310600149460b101480c54071000b054041d24180c200841e400096114000e00d00240c0 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 73423797 1250 73422547 73422563
    0xb06040801090c0e01080a20040c111903090b0c0106030b0106020706180305120307050c150a0c02030c0d0f02030d0609050f0105010206042d02030a12030509031303060b0103020412 79
    0x407a4030b090340b803c55894101402640500c0c0042007020400030f1410768055010b12201340c0d40b4810901100c140756181519580181001035004103035034042c10722094031507840c0c1103d400004540281c0c922070060900640000c01615041c0301d00f6403200f00500d00c861044c40001195030f0380e92a85118840c00384c20160050f0407d0130304100d815482901103042c5500ca05003061500d16640d41c141c3c1d07404445418460169003c00001e01d0f0318003440555980504550503a070001740a0f500c241402c480450303150315003c0c030b0008442e00541c40041640e00071208580203240f00040704000350349809580c0100000c51004100c048019400c40c010100103280d00c0c8804946030130411082690b500051308058115880102044080b542070a0702180c40c1c1081d0048411030100c4080c149400b81c0c920340d010350148a980c955404000702420101c5800c041d5075820801c640700d00301040d46a101c0c5000850040c03400ca0001e00c04a12943d00c0b090014005050051500380c2e540e1b034991083c07940340c0c02500c07046 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 73425047 1250 73423797 73423811
    0x5030a02010507050f0909060f0306070306061107031a090102041502010b03010c05070b041104060f06020604200a032a140f041e0905070306110a11030405011d040b06040801 76
    0x54090141c03d40184141c101039007400c04455038001c550007448141486082c400d004100551152840010325160190a4507541c4c03410340400340c00b9201510030741d0b0000d9640b850684503030b403000c11000140c0754081700000301030014803140c00381e604018000c030b0800e55081100182104180381c1801101100d90004070740100104101400c452038030f00c1200502100300140da00007201c0e41d00950f440b0782c1c491104400c95184601080080000341c120316180648160080360042d0000b40e820720562095007401034905102d800451030683c19200142c1200c82044d060001510001c14020200d081c001480b4600c50980c50821181e8490340c0044030404003a2104c2059041ca60390355070550400f601c0c2230210048694002e090948101128100c4a656411700c004100c0c09210000007180c000d8020b01126580c1c901d1410300c0e81c88a812000451400c0356030310b450041c040160340407150142c64a261490396544d0b881c1c4e4810036550103907481591180c0c00c2180355910300c00350000d0584000002104 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 73426297 1250 73425047 73425067
    0x3021c050a18140d18050402031503010e1509241f030b0a0f0507050f0708040509010605030907090b0f010c060b0a08010e07050d050c0f13140609010e07080403200a0503 74
    0x228403c50851020417001c4800210708441c00c00340d1808460b4161001a40d90791099000000103140141465065007004840c603007425001a192096005503c8040401e4036901030785641c42c411001c550390007081c0079030b8803100c904508406640c020280814030106240645c811004d200030741c6c1084074100d800b6018420041c042c2d06c9000c07100c0c212940c082025041a01024100303000e035403101c50703200c0c41c0010001d0400c00440181c50052a0140030314280e5611280c2c0a40290800c80c4d03a1f80e481d12940c01e0024041c0c40d01d001d60b011408002d054920a41000e02c01103079086c442a1040e1809520741502c01210380714000d9400003040c5200001550032140080c86c1d050120795480300d41b1401cac0c455401c8000c43d20204000d041801e0840c1d40c00c0d0440403000118105d0b9101911100d101450400b45e501d9030301c02c01c000c440c40303482c00701c82888190381c803650000240b150030350b11800040c0d0134000241c0000e01605a040c80f0b100410440350451248005143c60309032070483c201e40d80d40000c02d9281007 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 73427547 1250 73426297 73426303
    0xc031b08121503061909050303010e0403020d020304061d060f1902010b01030b09010e0406180305090102101122091806050c0306150d02040f060f08060103021c050a1814 74
    0x449402e1129442c80c00c000390000b0354030a00507103a0195590903d001504c031181650000051582c02800c0d29103d40e91440d04d0040d61104580a8016019042040c1d900b10b20220890f002d44486840d060748803550319036210088401c9402c4650081c808000010503888050098405200200510003420310321035002425100c1614285040c9402d220812183e55a5080c030315054503030001c00344915a0740c50405030f001d060b1000c2e1081400c030501592a05265000c0001c12402c40282c00b2140d88001c1a44008110342500c601501100c00501250701d503c4040d80c861b18006000c000010042c5031180c0250007118000303640107a0800103512540c08028180c02a140d01422a802690075464a4004038a8041c1250340c440f07559240003c0c00d0082d1411079042d20302070484080c0c0324400035100c00c0090500f00d100c41408010498031070000c1c1c103030342c03290084403204103030000171000e410b0018235540c0c06010041d080e00e501c1512520108104540f02d40c002009a0285a000d528405c24820040c2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 73428797 1250 73427547 73427551
    0x3090a090b01140705010b0a0308030109050c040b07080a0e090c090f1002031b070b07060c0e0d020f0111010204120501090c150f14120106021b0f09070c031b0812 71
    0x8022818003100c005560f0f009031840544106000d0341994849040c076203913005000c1c1509155101c690f104001c010b009000020754169000740300704101a481d02c103180c00090059100b41c0601ca01e081084200141850018041c960710f82e0820001d042d012800040c035495044880c14000c0001060a407c2442c08641040c01c2c05000e8540a0741005101002034036840f80c11250400141ccc1050540c12000c020044480100074601c44a41c985140e4940b040207003644058040024070901c14210084c43d15a4413844025070040c2030744d00440c6601d0065610120450038030542c2e540c00d200010b036114105a20700303c1c0901c50000042c1050b07203450a5a064099a00001a840c0c07015400200d529044082c98110f4001c506224103007034061102c0710058403900a060401c8205d0300000980c03540c00007030180d2401740d81800708a00714081380c1400505a41e0301030b107079403200000f400700744814081d023004100706000e13140020340300450074581c07017441e0034044085540f00c1d00018664200070400714120303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 73430047 1250 73428797 73428809
    0x201021e0a12150603050415090506040b01050102010506090a0e100e0307030f02062e030503070c1401050705070e060f030a0b01050a090216022110050916030b010603020304050a02060c03090a 84
    0x80400304841d040c0071682e0a601a0b5000d150b0b07244089428448442201a0141101c948c00c0c0412016450800c2e1551000c4d18222020f001540020a8039070060007081d04c00e003809046026155544001440541005d43d010043c50180c08420382100d80240142040307a141400190b580d50054900180301e50b481c00c805c60b0454009800307010041108020080d00050a1080e00715030500030f5980742000300c11030744028405e00c0001108020004290710076411503842c0707007001c40d20030156801074481d4410600c1c01443ca40043c00c080c0b00c12844c04004a411031809002014828906404245042240d0000342c4400e446440108103901c0c1040d24000a0019481c00b9400c0c1036000401111040c041c2c0700c024400d0460000020110040c801600c0c496200001115070000e10041058001c11060700d568807640a109007060000c03a180c0d1414048079484190820340380e20b441c1c011002500040e00071242e0740644c44005001da56150041c01802d00518051a55034101108014981c4181d034001 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 73431297 1250 73430047 73430051
    0x603050108070b070c091e05010906080d081005030d0c050c0102010c1706130609060611060402030c150c010515040506010e0102030a270803091009050f0f010201021e0a12 75
    0x5000c150400b0030341808036084070ba031003a140c40041c500045424501c2d00441206031911070000d1444000359000c8454180444082040ba41ca411201061f82ea01d0701542001f82c0c071801d828805c3c18894045180c1c0070021290700031401d5111030009043c00e42003c48003000542c00d460034400c0c0641401540b034059400d00003000200b08280e000390803443c090025006941c44480081c045031a16604d2551600c010101000790584512510000b000c840c05024002004008280f51141001848602640e0000c005261240149040069a40070314020790b0002c9014070a06500e07110034007610b03002d0042051003164000c9490203010803108003e02183c1048100202042c407640c001c8200c649c1d0b0740075407600b0b004c4c04405e10031201c02d0514244100e4091411f42c40f0028070100080054100f80204540c070007500c6a1000c4221514070a5010b032035403000d121007004680d031910342200c0d039200c1c4040c000076090083c0440c4030242e074568100c200e104400006070041e06107500000d500580d407580002 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 73432547 1250 73431297 73431299
    0x70206070c0b1801060b0d0b0301050c0d050606070f030c030f0206040f030305090c150d051317090409020607110a09021309050a110304050a02011d030a1104060f030308010f06030501 80
    0x4010030781c03101c0040150841d60148045000b50002d40108100e04070032000a1000715502c0070342e4a201e030312040d0b542000c2460f04803a5900340c5810b00409001b40c00048010303041101810715000184405429907074003030340410464000604224050f6840c034001d41720700000c45614200600124540c14455046420034010000013500403004000003541501d00054655140e4180900c0c2000000c5820b520800b079581c045000524003006000503000190180095180c40c100343c41d400804001c0180905a403220305083c0320245e00217400f03180c0c0010400315201b600d6401050190f4400b000035565035461800504080c00c2076481240141a40082145403100b1203d0300c08030510310b4000d0382c008130786a4002c9a0b15545c90740141c8411480242c041c1c0d0707170b0308051501c1c1d5a03032508614100e000c10901010501c0e19a1825503185800e400600039000114403592907001210440c010f070b83d03101d81d90302008188100300e920380130041c52007900e44540301d50500c6445450141d00e0392100d8201403c280c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 73433797 1250 73432547 73432561
    0x91506031107030e030c18041401050921040527011a04050108090a020406060f1d0109031e080307020a03030b06160210050408100603021e062d03040602030708070206 73
    0x1250100c50305440c2200b041e407a00b0001074107040c0c00c0813646d507101d4848604a010319002140c118043c511503d11041e8a240c0b20582038240c450844e0b4240310341c1c0103204003181c16221204120110405a0605450140c5a00005019031001d403100c081c0c40306484600503408281801e004e005d494004e0f41d072420100540c0d0f185a0a202d140070782c5041041c400e0115003951000c204111506500810034801c80d0b4036000010003460049551038005001c00031103035200c02c00c0f0030b411580781506a643c141c0c51400d45d228255544a260000ea0356101903040e403001095941307010318000d2200d98090907049100d810010207540012414510403041000090700c400c07649500d00000b15410349540d0450404c8040584547c0202c2d881a1220f014a0b040b06a50103403603032000c03090340c1c42100c0701404d50080500c00035004d1180c1d42000d070800c2c01040100b401a2135031803501c2c0070382007420000005500d0040c4a0034070350002c0d601290726507004014401c004d130708480d55651100c12480200764610b403000e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 73435047 1250 73433797 73433831
    0x803181201051005061e0d0b100804030c0305030c0904060608091014060d1502160b0901020a0207090203060607060e160b03090c0103020d06030f050703020a0602070501021c0c02030709150603 84
    0x8804d49200d00b10000e00c003140d14401036001513030054410160f60711840c540b00e120010b04000a038041c4128505642003000c5400345055500440c0c155a4a032500c0c0981d90381580d2983c406002d10035005420b215540081c2d44901030b05c03020385401d076103481e5107080c03014515180008520003203095600f0200419104180500300c3d540c031a034100c610400b000224203210210180c0c07240e0076422540001070368101c140f00c04d500c07005a10707c15040c0350115550031240a08034000d658294005800802003003014210a401940e0040340040c0a5458041542c1d19003003201c00c0661158860b0700003070350341032182640c1c060210041c00c000500381c0c031798038290007800d8940340318421030381c1890350200e424071004416030300a0b4041c0d40d0088a03007002c5850713800c251341d0702e21030b0b440224410031010401054079440840d5003000c85006800505841c00b11880c0c3c2d8484c130842100d0642007010800c4402c016a500b00f103100010025010005030071203140303500c60f14803d2160401400c1c141803110740b02c88c0c28052 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 73436297 1250 73435047 73435049
    0x40c080d0e0609060d0204050d0501060e070c051c12020a09170307080412150e0604050c1c02061621021c0e01050306210c040f060803070b0a020408031812010510 71
    0x1222500c0e03440d004208807174024000e94100c51f03005a07241400e4000c1000c15400f42c42a6040558002c1855584000440d028540303940001d2070364122810700c524040c011008400c2c000118108441d106541c000c1c0718040340c20250a00c4006448072404002c89001c0f044810030341c3c406e034400f1310b18003000b54030344014600c254403400f441a4501201d4801340328610010000c0c0d80c03003686080c08680c3c0c0440150750f8400c0180d400f9141030168507044441e130b25050180150303c00100b821102c658016400304031003038004030103514080d0701c0c040e52100010b80f824000da40b213043c01c100c900c952400c0603034020b141518442c5400f075518881603d4a000701d8110022002d0f00f0340900c1c0132541c1e075480c44049001e03c03070030b1007090714070305402e40048a25160115010b2509802074500704515005002c400e429a6407034443c99840ea001000749030089402d0890540c4d000240120241c0f800e665141c0191544c1d010310755410800045003030300300380d901e8100e10301c0c0c00c09041c51009000d2400d0410518941d0141 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 73437547 1250 73436297 73436299
    0x10e03030910110a0c0f031506260f010c17010e01060905040f02070f0602030109150b032e080c01200d0e0102070f0f05040605010203180d0309050306040c080d0e0609 73
    0x50310b0a50f406941c00c010a6150039071010a00144581c1c61680315510a1030380801c840805003100043e000100305d10841c5c003245d0340d49405001c00359080c481030240354142d0620169030b0003440542000e0300424040c1544450007541c60714006d148100d0f407036108400607000f0040c40d03d005070040200307543c4041140d080e07940c120b0b40054001240f8903914024450810300600307440c00203000c4010b100b1954042c1d4102e400103070051000640c000213420f01e84195004a4040b80c4051010030013a035002c0540c20403036030001c509991100240d07240d03440c00341e0b820b42c0444050342c80b11b00146200e59020200ca0b68440303900e10f031015030b0590340001a46070021f1640078800c00059004000c1d0585c030822800006141d01490b2100301034940c40d901420382d00d80d000309030007141030820010351544008111401e810305140c0008011030120300708014000000d0301070b020400480d0004c00c0d07a98043c008580500d20814084c1011890f00307403910308203007101c00f10005000c0d00800007509511a0340894005d120 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 73438797 1250 73437547 73437557
    0xd030c0605070c0b0702070e010504110403060c09080a050604060b270402190605030109061205060c0c0a02150d0509010e030906071a04051e01050403050f0304050705030d0e010e03030910 82
    0x502c820741200c100340074a401600c4801d0b81000d00c131400380c002c034210042c0d491009410b01541c4c1c90750248030540d2859001c000b00200c0401c01000403e14940c008480c101051508620803a034036011680341036210a010b880d80d8106105200810140348959510b0200032f844c50480c0e94004280301c41c02d526840c04622140280c603000404542e0b45070041110000800038290312180c0b1544000d20729082405614a100d140c45804901050805502c07440c681e0700000a154130b0b0307507005941403a500104222071441c450410403000507500d200000c0b101c030140003c0c0a44564a01e01140107581e409030111410364074001074140038041c048103c801d003c1c0d00741e80090b5540d8107841c08855100b6500d25012106041d10f041c0002c210010030111068454122025200e412918140303007201d00070780c2c0050220740d0400c000d40c01d00d40b00701c000d183e0081c055000e5507141c40d5134601007414280000b070300c03030001480d400403904d2039a00181070650040c07054008604024200d40450340e200c0d400c1c814541449 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 73440047 1250 73438797 73438801
    0x2e0b0a060c11030304090c0905030604110d0c150806041409120703020c03060f040c09020a0509011407060603032003070503070f0c080a050616030c020a030302091305100e060d030c0605 81
    0x2c00510700007a40a480901100d42d1980d0700c0c220b00c00104480b8842c0320006021580000300c83c6000107815014a40083e40c40c4000c280360001c100094070a030314100d51258580c45c0010300c61540388010034400d0426190607940e440d20404100807039090740301e81c0c403400f10200c05000302001c1c001072003401d585001c4103035030791520207050582c0380c40d880c1c1640070751601c214010045281d80c0f0f407503010301030362095002c803915644610600c000c0c0e005640c0310b100020000e0141a5556208184800c1c00c09480c5d20b60300d01e41404d40c0c40301c20540e441d0303400580100301070001604048400c5e1411038054200e40003d1424940c60b0b540b003d407244501500648401c0422180c04144807588024030010701c88a01143c1c039008040c6401511104110740048400c050402070b804154003a001310684061180e0240c4078121082c0d40503802034121a613469004054240314010f21802403041e02d000d0303110340d0841c110040c5040c445480c424001844140507001a0381c0180010380c1107040740034580e43c440b00100b51741e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 73441297 1250 73440047 73440053
    0xe07050915030f030a0f0203030106080f0403051c091b05030705060c0f0f0f07051e010c0309120302010204031104200a020a02101101060b0901020a03050f0c2e0b0a060c 74
    0x4400100001039160103501c3c59150f815100000401640c281612502d48051400c44140c2e1070b80003d1003420027190892001540014403054056405171007400c10f2428018020b28a03200c2080742e08907261030540e100d0f000000d001d080004800324843c20780318030070654244404292520b002d445000c0c0a2175012820456503e0140000510002c0d1a001c4401c198240302980e0341e50b040d5500e00100341e000c0c2d10303000f0540d030410000c0a080004051744207400315480900440d44904409015810803400c800041444a039103d444ca00490223640050f886504506040751000510564035105034a0000082d150000503010080c1000803846069141c401841d400c1e41085411039000b584071580807102190541c121a1005451a0b10300080011036102d96180d04140716034050035000d0382c03100c00c4802c0000d115a0003424010300010905081c0841c40411610748100390418841144c680204d440303040040ca401041c0504240c01c0a105411105020507140302e800c2c0100f00400c01d84000074024 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 73442547 1250 73441297 73441321
    0x2303010b040c08070801080307020105030606090d0b01170f0705010915020111030a090b100602190302070f080312070804021503040f0209010305031b03030609152d12010e070509 78
    0x4803000290081c8201025110000e00803182100c8010100f517074100085141035000040e02c4549906844261454071401c040040540083c9415035020602069060006548000d420700a016000a1000300c085401d1518207002c15012510800d40c020340301045660788c0000104103d80807075444c044005c820b000124050b15001d40c40c3c031120300000091024412059000d40086c5004522904054803082c40382c400808685c495600141d002605540d0061080300820454a10a00403202d0040c4d07940c030304941150b01c4e503000030003917040403401c04c20080d10160540d90021035840c0280c907070b2420f580061486001e090352014064400300c002801c01c04002c1101c0c90315038000b061000290780d80e1130000d0703803580070006044252074464143c104a11000045c0c030f003c1c00340184503081a56940080b465108081d60102d94004503c450701900301c0c10b220614544071094800100384c0c02c40282c1404840b60352000d0f00745c40d580c582030344122103810101d407030001d440c411180700580f5265030755501c44e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 73443797 1250 73442547 73442561
    0x15091b030a082a06070905130609050c03060a050109060903060f020f0c0d0207060c030c080702030a02060a020303010f1508150102030405041d10090503030c090102150f04030e0406230301 82
    0x145071000240f8a0754884681c400c180c0704070690000c00e03004100702030580c0e00d0700002d80e020000300d160fa9805005501d8441801c0c0000c4004c4000001e605070384041c418181c88040d41c2c9000040000418821a81807201203c8007504c020f0038000c19843c80c0c108000c00584040c800500791075614401030800040540440c0d02e407040c100704040e118040200155100d40f030402c1c0b0880940300b1000001a81801100c0020445426440b079600e800046e44840b003c0340e001c10000c0364140592408000103965090141081715000e6006648079810221b12002c0c840440d00069480650740c1c5d005080642d010041a911071224000e61206000c08070041c1e1a5009680085602c6030404038031b8134100302c00409074507950716000308503410380000703035a030504850541380c02512540040002030a01440440144034004041c811241105c20220140c800311300244d4003800340c54400340038041456440207200140d1502117408114071450080c0d5030a5441408216804400400001140582c1c007940004 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 73445047 1250 73443797 73443803
    0x4030905150901020d03050907170f011e0b04110f0d0605060301120b0a0c0903080a02030d050a09060b0415050f0f030303070f08090309030303150424060215091b030a 73
    0xc070850074050440c46803600038003199401441101e44e144420b070711902400380034426100113007403172a0403d039500b01c000800d04501c601034401d000c2a05a150002d10443c001044030300c1c00500011100c1721840c00b9207400c04101803190b420038034010350000004084070784d00c1c84400c0300d41c0c2c1c0d2400003441000151102c0c0d40400d07070151010000180901e112140da42085204100d0355203290303921000c0f5021280f8090301100011407804085c000200e94a004001c501020300407603083c41049040d100695004030344051803039840d8102c031010444c10340034003500310404460a20285880040001a211403445054800d00c440c80c9022510744030004400319200014040d00d95034902401d001d0102c505c0b08500c1000181c40400103400401c010066400d4060010051071454843c603c4115110340b01e464401d600c25600c100c940d441c0f100c08003500700203d1600b000c02010324645903010b41807004101c5580041c400b00c00c2046402107020880c100025402081c40b00080a0380300030a150074480e40c401 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 73446297 1250 73445047 73445059
    0x607031a090c0d1808040303050705030f1c0f09020108160903150207050d080f0a0f0209030a0b01030b01050a0302090a05091606170705070b1314071d0109022104030905 74
    0x1100141289000400c0402d8a80006001e030441844561124132468070300500300480901042c030000784544010311400d4043c0e82102d003480c880c0110300500360310140030450340141d000940d400c0221203010b841000000488104050b2a07e50004ac1c0992401003002107106200e5aa00700f01e140201c8112000c0c5d40c0007400c613030b144401c5020160095014010a442920030302c50032018286c4541c55040c03140e840030440c3c04a40c2c540c070800c0000361400180b040d406c642c083c4252003141e1810000c2161070780c014000b551195142d401e04808c00401a0040c500440c20741030b060000d0303220041081d40110700844c00050a42c0d80f0011079051079098071451407480102e041c00900703240d00107184400800320b8249039016450340715050342d081c132980100604032883d00d0009118100d208400240150080c0403400d2420190140503081400390341005641d035120b074900b07074911468250602c0c05410b04d484114507200d4a20404250180100d005a4200b85030000040c02c051240403004020a13000e844 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 73447547 1250 73446297 73446301
    0xc1b0b0d1d100e16120f05070b030708101703070f06090807120e010804030903030305091f0e0610050a0308071e0c0501030506031501060e061e0306130207050607031a09 74
    0x31802602400c1d00e107103503502c1070031200c4d000d41d280c501407902140c0c1100c14000c07403800300e680c400b4000da10b4484103803500c0c0111003000809075410030041d48250a9591544458a06610b0b05080a00150407049600283c1c490184005000004866215401860301804c04c0440d01d00700001c0c00103108000c0a01e034012170000d081000c01a010080800c80d500e89080003074500d00110341c0c0c07103c103c80140000302481420004203000740e00c4540c02001501c2903440064655810800442c8803502030310442e61380c0c000100200a0034002603800443d09000c01d51001d00e00300003d68100301501016141c80400200e550411030140c1d4a51040d1002c201c00d0101c4081a0401211a0007a0704c84d0314082428140010303150310340031488540a0ba818800314440f41d003003510451301c0c030810307100a581043d4204244801039500f0425000c0010200101c5640e0f0f250803003e008445001000039552940140300c1080090b1010404a40c0600c41c1d02d400222090041001c07d89021086c038016080540081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 73448797 1250 73447547 73447573
    0x11070509072012070209070c030804021005120405030315010503011d0711010e03040e010603230601140403050703020f030304030c0605070312020a08040606050a0f090504020a05100c1b0b0d1d 84
    0x400b41c00441e0085810030300300c2d41d0b07d142c169800c1000d0a801000036002c14001001460400c0340811001410302c0c016041c16500d4519801300c1e0030640f0f0540d001d50000c401c0214004045114982d441c3c2c080c80d04030305552400307070518501c010312190451300314000d20014200f1841080710000b0300c2c4000740240328071001400840d880398040e0141d00c20f00d95505002090f118041d00807030100e249400c3e00101000f000700701e40880200003800c04d504101c8501c041c0c0c4206480c17800a80b010b54005c40107003041d24607600c1000202c0d81220328170760007604148402c1012504c0baa040608941d070300c0c00c04542e6101c283c90229003414500316a444010b1010608030341c0c1c0d560201810f44903d20030101000419210010040c024015104030784059000c00402e00c1500b1440d00003580143c4050800060144c90741c0018082c1001a4462000a80065996810711070b00d040c00301d40c43d844201784a80c201d800c2011824483c40382c203181c03d10392512a055003911841608800317a40e416000c0070707510b0307918440c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 73450047 1250 73448797 73448833
    0x60b0d060507030c0306081e0313030506090f011404060e0a06020d020c0705010201020c100209120601080307110406060e010813050706030f060902030606071401110409020307110705090720 83
    0xa42d142c03000901d04507504522901a1003031809442c45c0e14014841d20002d08102ea071803800c00f03c0e200e8000e0000340080d02010701aa20000d028600c5180980b00500d00070215910344041c585070803031940c0c1480c3c04103441503070261985421a8126001281c0c80449918051030062802c00c0200a0b9200107100e0304100115805001004c0321107060700c10841c2c0d508012400d1340a140c6848605030040c11039494210042e5004000e0403d0180031a42d85180100343d043c1031510991080e01690800110304042144400106501040c112800c100c2d40c0c0c20818020580c01c101002c2d14184484000410201e0f0511001c00c040a58050125103240e5250040140501300c01415566590f00304a0007081c030403050300070380c0e00c510000b030034541c10301d0036030307180e101e010090305280c0d038129580e4044803502c031440280200040c154020300980c1da0b0400c9003000742072854030f030326480543e00910420f10a550381e801040f60004503038a8582ca0a0403012900c0c406001c0025040700a4410300d8104400c000d48a = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 73451297 1250 73450047 73450051
    0x20d031b0b01081b0a091d010c05131706040809190303031d010e031617030103030c03080c03060d0809060d150302040c0f090603020f1c0b090a0204030206090904060b0d0605 76
    0x2400541d02c0741103103225112610440300c0084c5900c6410702d8018001801c150340041e00d6980c200c5245a04256000b040303a08442c0381d00310440c0000c2001031a03100b21020400306100908490021080c850b40522030030f5107a1801800051190340009068100783d520850315562031070038041402683c0d5500c0c9000360085c40003c10111a0502040700b40200301e006104141101c41c5c440003a6151050178587c20640c4a0544803c1700d0001c0740708124018100c211001c1c0d40618801c1d140d200726040da0f4180600000001814800408401c004102081d102c00b100d4621a56010f41e146481d1000300d0b000075264010b0981c0c007504180b500e600d202704596841700c00000c5074001c0e18108489070420300201d0f03c0c0440b02085030f0214003003e60170423840d0301c40d070700500b0b0014005064034281082c0d441e003000c091720b0080c04544899124040d00000d40380120b0455042981032400f103103054510760120b000d50060160780c5228151001c00502842210b8100010010005001d90b00302c400c1868540010001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 73452547 1250 73451297 73451309
    0x3050f16021e13020708180a0806190b04020c030d110903012c030309120f0f0c06091e0c061b0f030703030c03051003022202030a020d05060402070807020d031b0b01 72
    0x1030610304514207442211a42d035081b403244c51922100650140840100d000400d4020105080000f0414014041c07e8000c081007a09940740c9903150105205651040c6605807165104001040400b00000f003120900d140400c4040743d40000d06042c01882d0183d95001134165003415081540c4001e0400740030740010b1800e09800544030b01001c100e580c0c3c0401c80b00c00e00c040e8403450742043c011100c00c000d080301f40815410729140c0039110005d0015034001600540181e4080024410941c2040c8182a40085450b1220416218900d00c40e80d688000d200090b028000014030855001c0b1881080300006494404640c82050208444c5a03203500041050b400070f4a807510301141d0070310034020715001c0c10030407440b120282c1c215001c11260403141d0074080301141c05a005401103450500181d032089100c40d40c0161141103003040d1a0644d0390040c01e642c400c507c10010344c400500e0800c203840341d8a40540d04004170203880d1505641041807000c00c0b2841714040741080040081d2101481c1c1604c0c1c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 73453797 1250 73452547 73452559
    0x1c0f0c20090c070c030305030a0b040204060c02030c0409120c0f211106010b0301140301020d0c0509150405030d050c19080301140103050424060315050405060f0403050f16021e 77
    0x40c0d0002c0d01c01e510700508000928580340c440c41040483c0c810409990403076141c550005800381140c2c001000c0342d0041c0e100e00040f61920940c101546002d00200e261000b0654040c001c0e00141d6030f45000240130b034620074051003083c540795418040888214154550b01440a08a0301d20500280c101041303604c1600001803c20003103080b0101e40071551074100d4140b104250300310b07403c0500004031580320f848202c0d0559170901c0080c2202e8030a00401d180c0660b00e880382c82e582e4101c101444030040b03440742d48140c1064100300c104040c2d00c001642c110894800d10f0319a80301d00340701317a94604148850540300b000d0000c680e160800d01c41500c1c0110f0498510070380c01a4a40313408070054041d61402c460281895034250884042d08100340107403041e08600f918006040754895450482c4001440000640165683c04020401008001300c40e04143c4005480a491074036940007005485900e007038035404040030401c6a030704640c5125074103941342d004050b00703c3c4500740d05a9008190300310302803600c50a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 73455047 1250 73453797 73453801
    0x3030a051006020d0c020d02041a0108060406030506010e07020304030b010b040503150708070e15040e09010606020604241b0e042007081305060c0a11031c0f0c2009 72
    0x2460746088402114000c0d00505131142072814192a01c010b80d05040c1d030040e100d6038491005070b5407480f808a9801880022516030446140010300c15140101458003d501d80002440403440c0007078840d0441c2e0ba8070b103144405940e5807104900b140281d500003480b5440460012942c01100300242c81651010303000c841101c0c020007001f00c40c904080e80c1c49004541d038600842c02042c810390440c68107c1014000f02da03c002003612a401581c85980201d02d0004a6006d1200c52982802040010a11031006004500340303038859441740008500c682082c103402003603143d192041e40d08001c1c0c2d80da001188156914802101c0a0124140414070314030031031800051440440c0c0c81203c103842c803041ca030350311402c11403242c0d500407075039001e0220381d5000485200c00117111741d1004003d050490200780501015012843c100311311001d01d2148501c280c01110404d010007525062180310306040745403e2442090341001682c2c005d1540001174042440300d034421141030a105505002c9000c1920700e80525 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 73456297 1250 73455047 73455061
    0x130b030607081501030504030f030221270a020a0b03040f122d020304050d02041104030303020714060f0708130f140705010504050f09100e10030b07020604021f0c021203030a05 77
    0x106e10403240107000c02c4a22007071180b030b10f00c0f0703a000d0903a5090703801c0d0392884191005221103854104941c40c0c43d110044024503042885145e18982c0003022480c001c040d004010b03800140813900300c0c012412002004400176041c0f101402001c03151320380200b00d180292a080300e0080c40d00316075030000106180541980c3d681461850b8410300460a60741c0654145810142005011801442c069074801d803545030048204941070010030085210ba200103988a02c2031030314454010000b07009202070b800c000b04110710980d000c92500e5000c801ca18210129a0302e500d907010034070400840207410003c03840200c2080011002c01204070b840084100c6403515541c1004503100c0c4200d01072143c00405064465500c4d04245644075041900d000e0422000c0383c031010410000d036000c5464500c0151030b02400c00c140010420403e07004001440509081d1800f5008604001d60507100410030403400c1e021150f10034824030042c00c0d03481e4010703e4041c1582880c0152951f94100b92100b0351410f140c030002c500c40d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 73457547 1250 73456297 73456301
    0x10914071b020f030a0c0801060f0b0310050d020607050d0e0a17100207032304051008150d052a1c02011202030a06090207060203270c130b03060708150103 68
    0x1028014103010380814403a5400d100c02c01c0d003042d0b800358040c07250a05c92070010b0355007140c000290020f10000a000b03441c1100a058883d4035501c0907010031020018081000c440007618400d071241620400c80d42d441c0e501c0880d035603100700c031406010303400b907070301b259031a20750103107113590f04800894038261100d854115040c1d20900c2e6000c0d000d0b6662010146c0c1c510925590064001603000e0f0070100380009011210211900d0249019403e81d0ac000509210502d4070503032982040102d841c028003549000f00980b0640e400c00054a4400c20441e2000f50400c00204a03084c5031081c0080c6545403a051040004000d42015007914411603010092042106090798465501c540594410084006040b50040290300c081c1030700000035140c3c0b02c08038582752140020843c01d80700304001a43c1c0d240000810018054001c0030035110070440ca10541140740014401d01450400c803001c01c0340c02c204804400081401100c00794160103090100b110903508622141e00c1042221030700030055000d4001141 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 73458797 1250 73457547 73457567
    0x70605061005070f0c0515130905060904111216030507090902150a0311040611061b04140303040315050118020c07060c031110020316030603020a090c0909020301091407 74
    0x3003041c010100410421350840740c0712070040070700c00401d5403128041050903107251901020894001000c003250800d45c0415030040244410030070150401c0780c00102080006003001d07044035044250442a030381c403401030404124566084405050101c02c60600c071520500c020303506801901c100152046082c001c07098155401131200d401c600d00c5503003500043e00321200c120304041d60b6951520701441d180000344003901e21615221080c0c40680301c29440d00000a04220f0940d00d4101403904030000c0360185c6064946112505013905c0000c4086455402198809031a0400039011040d10f800b056005a040c0e0304045150398802042d40304c1310050703220300b030701e1705409600c0340320200000c9201c0d0280900d0144685080700030000020781403850141e08200c10403506078004103001006048103102d0031652864207040c44414515000280c49201602c500c0001a40703445038000c2e41c1e0b22030351100010f406004011034684d612307145068002c0034401e2141208000304000300e14502c0c01401c0c640c0e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 73460047 1250 73458797 73458829
    0x90d02120304020402070c0e0109090b070f02121b0111040f210f0c050907020d0201230a021b0a0807060606050f1606020c0106141008040b0a270807060506 68
    0x241c6141c44030b9003403000941c0034200944144078100c1340415140200e00905000b0045d40c0c0d0302040040840c01d1128050701c2c0a40b00e582800f503400041c84013030b900032509005c1180001c1c1126141d00c000010030103010a0348100c3d40d807075445c108139008a00d1070b00004e0400d88024030310a60078152100c44290000300000141c001046140100400103201c0340014542c00d4071460840341c038160b442d0082002000c050701c80f60f01580114143c00c0c0850390910414010340600c03000c01d00b400c03401d008048840c501c054546508243c00042180011561000466a049803403044401440e4541020600303034200000454555003030008c0042c01601c82c0c0165404c0d44e650b0f05042c2d03e41001c406015040010384030f0102c07402da03001e02241403060401e00c1908001c0c503107070712030048000321441007181c440e240142d284203010f481024040071948aa000581c0b040b401c480c000b84c002c100c041e041c0c0a0002c0506090001c200ca6290301c0304200c011806818201e20600c024084c82c2c0342e01c41040300f90702e10004c40c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 73461297 1250 73460047 73460083
    0x17010e010203190b0609040501060c0b0906150603180f1f05010f050405060112020c0a02012a0326011401081b09010e0a170c09091903050903030d060608090d02 70
    0x81c00f0001c0f1a644001a45107008018504c0e141494011500f034130400d0317110101040c1010106401d0000c4010000d6100420ba03000d80744504c0c140c1c2807a24443d29040903240110404400a0700c000b07040e040a00b0f000400c041106e584800b0003401554600069207542800c40716100340d03202100c55070080c42d0588141000640540b42800140401403100602e082d04100c0500c580140ca908140b008001c003030500c1c005001c0d94452070001501d403084000e400b60b010a021010000c80c6401201c2c08140503601d4605080c1c0e028200c541440c842810405026280ba8940d00001d0181d80001441c0c0700e03c002130300d41a0346940c0352030360208841e01c01c1c0211005103104000c415030561161400010f0310b800200010789058841005149d44180074401c0ca60030f0f8480a03160302c40385005002c5950150790440100140c2d41c9a54041c485210042401424060041031b1a03007103039014020380750040d10f040301c10070405544040c010140d42003034076031054602440c0101c0510510104408010606503c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 73462547 1250 73461297 73461331
    0x303050d020a03021b07150c0804090207080f120a0608030306030d030e070305010f060e180309060a0509030105042001170f04020409081204020a120203060a09020402090a17010e010203 81
    0x246010b5070010305820704040c1d00304008102c0c2c2500700880b48401000900520304581014082c982440d07007412250180041003201d400050704200c201da003940e41c0c2580140e201c0c25945400c009074040da420070441ca09000c100980c4841c4a102c54508c50031200c0000c3c062141d441c0d00f85e90726448283d890b41c0d01904110a018000c6000f40c20096842c01c0309400c985040342d03244c48643c04c445400e04c621440584680c8100242c10020a24580120350000c0007030603d0700e90524140d0300d01c039100a6901800010a913403a07240d0050054401816000d00240041e20702031505000444180b200050240f40c408581f820551051000e06d0903015580032004480e21041c0e2040f024000041c4120307485134032540c0c100c2c00500320340003034490501c2c0400d110302c5134141407042003440070140d00721216184480e1a40405030341e000440f540c000d4041d40001800203602e00220300680715040c0d4460b000f0301420000682101d100d1a14032107080008001c010006030800420300342e12090f10b0200c41c41d0b490004e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 73463797 1250 73462547 73462567
    0xc03150b0607020d030e1207030b040507151209050a14010905011a01090909080c03120a0609020f03061c080f0c060c0406080423060f09010b0108061c0c090203090a031107030305 78
    0x901c6c0100002c010040840500d103106641d191201c603800031901150400700b4003040020030071000b005000d0040030008a54a00c080051843c1106611410442e45400b110f60a01c90248044650070317400c010190300818000c40b0083c0a010001c500710b07029864400d0600400841100c6481d54800513914034540d503240440003405011920707004c3d551a00104140740142904100400d100c02d903468480049103801c40d00300d011901503a00403250b550041040055010481040320740c8140c04a17141c001461080704550034030b03440344030010911080081d03410700440a103009400ba000c60303141100c05c0c030b5403400703d07486490007944500070100348400c003c2000245078080d5030880102c4d05c04107880c1190f00c00605440c2640039140c60007001c40b0701c2e042c00f104040a000d032180c0c03280203091604003410000041030301e9201240c031641001294082000030031405940c05401068805003d640740c1c182041900e4441000c50011404251005c510303004910380482d07101d003101c1d05504d415003810f103004 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 73465047 1250 73463797 73463807
    0x3010903120c14071b080f0a0303020d02090a060905030721060e0307060f05060a080a0309050913080d0501050406081204050f060706090c0303020105090c03030d090f0c03150b0607020d03 82
    0x24005101003e0241010280d5207800380200500401914401019004198121141c15006103c0316041004a0601200006030480c03402d40e040ca401aa2240b055146100038029450303080d0f8482d00d03100f800030b400c07a0b000c04020140c450031000d4a1950f0b03521032090071114024440c1c64080350700162542c003c82c41a42c003002c0c80c6484441581d245c1030301c65403400e0445d001c030000a00c01981d25401d000450030424410005085040d008092203441910050700240d42480b403284a40410400034109100310254404110740c440c011684800c000040d90f000b0701024040c1c540901d203014800500b0030000180d0140080d103214550b854035007407509000c0a00034081c1c070103030007070720400c019000103120f803240904440c016400b94800c0e604501c2c0003403d40314058400609a130003004082c078140d40c007000b01e50190148200000300c9015601c0c08461204410350050480740d240c80c000824040d003400ca1309810300000104224002100301002018010190b003e90010400302e04480040d00070 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 73466297 1250 73465047 73465061
    0x20a120303060b070503071502030601080a0e070b0f0306091609061404030236150108060a0b030702060103111f0507020f0303040602010b04060e1329070f0e0301090312 74
    0x64030700411526161507404003160b100d1401250f06a1001484809200c000d01100e50852440c800039469810008002020240050400c40b030f441c0d40c0e4200c41008070401c0203030708014112040340c00c0d02e540341580001c5154008407010b50250981400003520740306502e080c12450120790b25140804d900303010080b140300010701c4118204010070071020015a03502509080180f9502d000d001094280c9050301300081120034480200761408000c1c04500710030380303849034811a42807070070524235603030b07107002842c0d40e442540000c81e07070180041401000c41d4007094035410b0768003071501c9014861500040c00400030401c400902e407d40c410588c2041360340b180004040c01800109600940100c1c500003a0960b4840c2d070000c0b003d80c0d502c070032a43c0181040d001d068001c00031100090402c1c68004031000603c4c01d586001444100300c1d0407a64040144018402510103a903d403003090f51400320b60141c105105407920742c001c103400b04111141498140500110564196500d00100c496049890054180 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 73467547 1250 73466297 73466303
    0x623010608090c0d06060303030f0905100c020a0803040507060906020f060f04020102010b03010e03130b0405090402041104080105010311090903090a3b100b03071b110907030e0c0409020a12 83
    0x1e841c4003098a03a0b115049069514007480c5e00141940c518a030140403140c003108060034080c103188900c4080751000c90420610544014086420a00c400080b03040c64ac82c0da8000340f00ea40302000703100a000d00015060309440300d5444d403002c0a6290380050b81d907040078108014a41c0e10600c006107280d0341c5104540e8010f031060001140d000001c800085c01d42d410680703501d080d41e00100d01c100555120500c218010504c01e000d4518083c00c00d404640d10180003007001e40520b4407980110120084030381114000d0003000c000b0411940c680ca89034035400c8512200522500c0200003103052602d01004403811880010400b00c4051701d000e429004100c40c035a0840b0302c1c0000f21503401460380301c40c0c01051a0704d880d40080c1c0403031324002400c80301e4808103030400c142c0340c1410710030000d074641c100704001c0348000d01c080c0540d4046071038070700b041040b029820f22542010810b814000c8245c1c2580094000701c5407417056a201c0745120701400100c910078031001e540016525002c209035040ca462100d54640 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 73468797 1250 73467547 73467553
    0x609100b010c0212010c031a130222150e01081e04021909050103050d050403051011070614090c03120d0906110a0207030308130312020310051903062301060809 70
    0xa030390f400240280940403440481651550122840c41c1d40c5881115520f41c0c046c20081030780b514140200340c82d03080215072410815400034880301580001300c10074046d020041c1200f04096210780c0328001d0300c1c0c140c82494000c00c3c1008501d01242d070148240318403d100b210f80071501504c8803104105101e001500998000402400040000d1000000c40c0060301f54048042410f52441c42c201d440c10a540c01d0602c00c1040900c014000603c01194400703845140140200f0720315003014842205225407600181190310305510000311403648051a80b26261a00a880d0740100c00d40505481d100d0141d004040544d04010600ba05901030b4803d850f4a801420b00285001d00100361900503404509090051380c030070482041011750204089501400048018040801583d009000c01213402e0b1841412900440007030307500aa0105c802004080003820180d28440d10504041842443e000540d141414805a200801e03e82017005070700440018280100d60b2034083c045410200c06000f040e6180 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 73470047 1250 73468797 73468817
    0xb040f030c0816140304080309060a030e06070f08060f010f0f020106080105042303090d03110c0a0f0906090b0904060b010c0506100f080f0a02010503090102070209010801020a020c030609100b01 85
    0x5101c40c2d0150141d0045540c51409200c1c20b420481d901c40015400108039901c10030040c00400d4010085c2d5903410015540107031940c412480540c0900b900c4c100c5c4611501c00d290800c640e040d07004001c03910400700d81d124400aa11a0410301039406081c07240d29002c03d115020102c54148100c40c002c0b00fa120510000810380c0d1142011800d40b902558269044c0c21515500556220a115020741d49500140110318240304031002c038038486e000c04000341c03d1081c080551824035209100580751008020082144030761101c40049181d48640100c044151030314001050b03080042c030542c889400000c040303c0040e9100d50302d0708080d14402070362030f0400408486540020b4802c0081500900444040d0403109007031501c610303184501940155215849200a1003000340c0114425030515020701c2e20325079aa40d00f410380c501a2161200082d0400601c100000341c0c0072040d03010b41884503841e801e884110b0003d008040d984d0000742d803140202d4001c1401c8180c80180c1e40c0c8142116030060408034501 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 73471297 1250 73470047 73470053
    0x70c050d0f05070b0f010501020111030403081b1b100e03090a09050c0c1218040506010c060507050412080706060b030103030516020414070305070f08070203070305090d080403210801030b040f030c 86
    0x244606039000c6040145d1040140019a028003070152040250f2507a94194070740b0b03843c01040c41001810b02e0025170449418001031102c00c9045504400315200f0304003078003c0090009907540d14071700010070140e1400d050000d000201004944042c00001d051807042400d10300e65000402d400742c001c901a00c010050b0000041c4c00344500080400d91090403611a103000e002c04035001c10844401e44618030340010001c20740e801050705010190400c80000f119510710105903214401c42e0090702049500d404038508200b0600c00601e00244200428040d090340c0c0c40c20300507140000c0c040100400d506000c01c4e10058041428540021f00041001c00c820b0160609001d4030079060f00e482002940315001c110231650440016444502c00d80780581d0645446c3d20700944901079807000908012000074402c019a45502c1c2c801c80c8075401c0f040341c6548994a140c1080f02c9258070000e0701000c41902d02e04140103001d030700e0b8075048a403c0020742c10b440d03445a44e04d2014541404045040c00343c1d800460000c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 73472547 1250 73471297 73471313
    0x30a030203090313151101020406140d1d0703301116060e090601140a03020904110d090b01080303130209060d060f050a0b0f0a060305040f050a03090509070c050d0f0507 74
    0x518405621701c0017030030390480c0140340501c03400300b4000c50ba00411040084581c0540790001e8400103101d010f4070f94071070740080c0d0050481a9552046150040310803440741c480802c11204482c411140c1100f00085400c28181c440003050000b400e0141000768845614007501c4951171600c0380100b0341c0c044410025071048059000c0d00039a00103100102e595910707080039446143c200200f420061021008d8624005041c4112150001016000f10f500c5080d03440742e400c010901c000382c0309542d40f00d03004500520002c1ca890401540d009004100004600d4000b0080b00d01030804a420007480c1200c50702030040c1800b003c0c1a80760054902c18154022458510a8030300340c42e40140d0108450600003036040540c1c01c00d0484034400e80d00030031244115500ca011480849181d0f040100d01c6d41e40d282800622072800306d80c0a01140107012107403041561001c1d41c081a50340489542c80340c1d8807050000c43e01e01e284035030001c005902194844000c43d00411580c0c001c11102d160991a017034030f6940300c082c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 73473797 1250 73472547 73472549
    0x9010c0b01081011090f0402090a08010f092901090515040903020d120c050d09030201020912060601170108340801090b06010804020a030303090f0605130210020609030a030203090313 80
    0x2002c2d4100d03d02102440c84180141c0b456100c501010b60b051006100009410b90040c582c03e901c1550300040081c11603c0740b66008009000d514000c101c02e00141070a1406000346100840d400507048041250f00d01d256031000b59101802e40310000c96030b007810100c0d070043c980a0030116100701825a110084c0c5c1e02c5005840d02648a0b9000d822841049080a03041c0c0c104810000e0040342070480103624a5800426282c0411503034401103040c02850400340d0080c81074192f1542c01042840c20280040c1c400100366020b8042a40c0e124502804c10008001401080c001d0788850f400a00f4080380c048004054038121400c44c5480340750705004a00705060a04c182c0e400f1000594443c00b281c030074000540b95103580b1000a007007110b21031030f007980003441942c02d50000909050f6100072100601043d42030b0086501da014100304410b04101036944494508040100e00c40c0f8002c540c040d14191003c201c00cad014031f126000440c2044401c0000743c1c0a9003005000141703502c014059100541d900346a510 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 73475047 1250 73473797 73473809
    0x1090c0201090c29031303030902060c01290301060302010c030507020f0a120b1501020a031206091a090703110a1b0203012d0209060403080a12110306010f090f0b09010c0b01 76
    0x8507071804d06008051890214040006181c078203104010440d60000310b03a03046c541c3c1c03510340000d40e80164400150140a054410301142d031030400700d41c5d0020034032004441240b494103158aa0400900c0405098032007a00000740015442c3c010100044d01500142440c68170003445250385403d24804503a0070780f03855100309600c0c1020a0050140110801c285d40c000700c2c400700c0d010041c2c9120001035564904143e0040405c148000302d51811400d544c8020068213980100b8000909007440b604610209031003200e02c1703980d18401140321540244110101a80d5001c0510b0410841c0c003015a04000d03011520200f206003001218016a000e110706503414103104e0407803183e2601c1501c1c60545010111409454905c1040342c80340710b94070442910222903000d0311046d9a2803030514121203d01e0030a81210340725040031303124000c0e11030900103503100740c00a80c0c0d0100e81525a00b0201d134884103500c00d0039042c1d0149201806851038070001801030880c10f04107580c0122070342c0c0d03500c980e000c024bc0c805 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 73476297 1250 73475047 73475069
    0x160602090d060b24190207080a0c0603050c121b071406040c06170f060a050d030801080c011833030501080c0603010303081305100c05070b010503030f0301090c0201090c 74
    0x3d4946140c54940c519541c6010300000c1e00703821258030400d0141c8202080036011546503000e85c01898403c0104501401c9080d017540c0c0c07000d00030310708002c5120350f074010400801d0500001400482d000381c15121051000b40c52000513442d4010480a812560b08180d1316154041250201003404001c203030074002441d40c008d244030328041c1420540d24100380c10150802c104070710f1034018a0255200e26070400e54840d1402900c2d02e4100010701d00664aa00c8550008080c8034000241a008114207040300c89000070b032800c03140340c5001150050141241c10300000c40d04201404070718401c010039103400b9000c2c240840410b40c038107408032411042d1903405000035140d1005000441003400138103101e020507190182507504558000e440b558004200c0381100da0350803041020702400b001059011000b2071010003a04c903691790001c180380e21580c001c0d51745031540e1303000050604000084500f08a030747e4040c241141d00b083e003004003500c01c4800001c1150748039201c1e00c2c00314200c441c0800c0100031040308 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 73477547 1250 73476297 73476311
    0x212040311010e070f080d02010c0203070305030603150405030a08010e06012109171b030f030112051e0309090108030906121306150303030e01050601080606070201090b0a030501031e08160602090d06 87
    0x1100c0c2ca040e82c501115001c5904003e11a8ac2c0d00f5000000d503101564982452522581c407200840c1c0342032130050410703040825004c180002d20038044001c0001441035903844005a0701d1700b820182030700003565098006078500c284503c649542c09620980307901440404142e00e40151540c0310a9a550300742041d4500740001d0708403036030503d010104c0c0021003460245041c8010b1404483c464001407089403003441028003030104200041c852034841030700e85240190080900b010319030341c07074126480c030b64095004e03100040780c5440c0005c2641c5041c00020300903403500b02040000842e0403005400098050035121b1003200044680c0100c00066183e080490051890340c00e0080036900a0805c100d030591606051203070300e990000041e540864240c0e011552031800c0c0c40101c840c04510b071700c590408000443c4c074800d02c4c0e606411150480e0301480000080b082c1c002c1c4c460300c07412034140340100442c10420203c9184500c12403c40c414900420f001410410080f020a0880170b102c50102c641c16510303c1 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 73478797 1250 73477547 73477559
    0xc030403080c1b0105041511010e010e0c0604080a060b0604090c020d080a0203040f08091306120b010602070b030604050a02070503070f0c080d0512180706020f060a0212040311010e070f 81
    0x89410030059980004440f100d1540c0060058031542c0240344805030f01d0320040340700901420706d2404110810000b0820b0550b004400c0e4000d203040c0510010034041c001c41c03000300b46400ca06542c203484010703016040c0b508aa0381d074a8020700c50b0341c0d403554000d48140000901640548941d694111258014050391800140700078440d0500421003101e452040c000d0201003480382400549650340300145903034411159001520003d006c0c210f07070141c1802c1003000309104600100480b02d03144980584c0381180d03214002039848101d2409112094901030000403810f00d059009940c010761070500051a000068450b5130856000c01d00c00d940113142d00c041c0d80c0411560042074002021420040c00307a9100c600c4000300b85206410b6801c401000b80004074a030083c4031000d071200112200c040f68606039075050040d48828105a1034011030140c040020410b4905000301e8641c0700003800024003942ea10742d01551414001d203c2101c240d940c54005003106c41e000c1040d00d0103480c2c05054800e0751b500d410 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 73480047 1250 73478797 73478803
    0x115111c09030507270c0f08060102031605070306050f0402030a030e061309150803040506040b1e0a0207080c061801050703020109060218040605040207050c090c0c0a0b061f09090e01020c030403080c 87
    0x8020f41007458800b5072406c1e15031100b0600d104100078a0141002c1d00c43d140100d143d401080103044030000380840344810000e00240c40c0d8101d03481464107001c40d503115140340c0901c0314100c50280d0103400234680302c00021b210321107190007101700410321814a5a0204103030714040c9a40c0110720155501c071050803448801801c01c50003010400000c1d4a00307410900801d2a88c000e51060000340c020204600d01054401e068201442e0080c07a40c1c10b80310303200820f000b0341d06c9130144507003e0070f4080e41c10344420034104034044076010091040f03680303c80d104540c01121031344d016800a40465590341c038240009081030006214858031003c840c01901c24160801c4122000d940c0407a12443c410402c80000a1000c00d07040c50f01c9000700d4044489a8a0104010061181000203090340c000c0c2c05842082100b0b0200341d9008404c1039070b801e107a00c455204082081e04640c0505008038680360f400700608a032540083d5030a8a9090001d401c00d45a504051b1460300583c000702c9a0290119120740491010 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 73481297 1250 73480047 73480109
    0x30d0c11011a031b0102010b0301090b06010807050903030702091509160e03060f0c03040c03080408010504140a03141c06030c0302100f0e0f01050906120115111c09030507 75
    0x10800c100c8010b005400001d907560440d000b4500c131070030494007000c0d29a00070342c4100f00541c4041c000f030040c2e0071a8034081060072021140240030580c80d41c04a40c2240c40b400c2079a8110384050015440d02d1010740801036145070061082c07090b81c0b540301098a80351207131040103001c0e4002c3d016507400b0010000b0017424159035184c640e4000d611050803c00585042c91545811540e0f80c203085540340c071207050000c420003103500007501c000000240014103200540c02548030b1402242101c00e00c680b5000210340b16410307580058001f59911030882c071402a110000d169684446541c044501d0110190000b0b844d040d51042d20308500303195007001503041080b0407003034030302c2185845030f22606000c00192001030221481801480280c4e00d209159010b502242c5010b03100405040e1280a15419128071031003d02540302c400074030070101280310340035283c0c8912550481e00682021050500d03401101e202e000034a204020f0300d140b00001094062003400c01420721200001c0804d0082c41d004000c040e40c1c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 73482547 1250 73481297 73481321
    0x1b07060902150702010804110f06070c09060b090904060f06050d0c03020301050a09030807051309110306100509010203040b0c0109060c02030a3c18090204082517030d0c1101 76
    0x100f04071101c0141ea02c1103a080d48983e0050010320902079041c0400d81c00d06c041122650415000581c110a0180e601460800c07101821422b21030142ca070078641c010350281030912034104807040040350018409400c025102061000c0008071540d58038002040c01c000c510040d6400c0c0b151903828019410280910350740412900010f000485a540d8010801c02006110600b000b03000b0828201c03208840c08804010100380d2014004000b0310903801c405540150340c60362280020081078500a402001500c9004405070040c505142c94420100300c1d44d80311245501240d50f80740c0010300015510321568890405550003582c95000070174015010210f00c4ac080c3c101840712580d0038885020740c1001481d4060b0044882d18410100b80c011380d030170311400c135450701114820000418000351560150003160071680031150b40400100f1807200110700140e400a01003003d81b41408100031892040340300c4001401200d19011116810f0001c03924500c00c4400060f9000403d010003038001d018070640890 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 73483797 1250 73482547 73482589
    0x403030806150a1110050115022104091e050403030b090f10120f140d030f020405030613021203040603060e0903180f04090807080a02120c030703081b07060902 70
    0x400c1d0a800c1c1081c09180c01d4503041207200704d1031903c0114240401030031407182500c2804156100c0404116910003880420010300c43d684010400c8a0b50f10002007040d00c80009043c0380904011400300900050002c80320b207002988040300a4880d244a42446607003e40d6001524408500401c40e89c920080e245080b10040c2e44140034521400040c032034202e410140d040041c510844c50040144a2001c20140c4800c2c0c4154030000c181c0000b00c2c400e03600000c41d5030300304031000310b030382c0108128091b5000d03c030380550180c0c002640c1c00c082c4602440711580020030100c24040d200751000e00d154415001707040020748407a404c00062030580c580b0b03500a42e0320805141030081c602800d1a441c0480f00c251407007186260480c0c0141d8586600c9000340c2a001036145a0326610343c00e01082c242c2c003c010400041c400d04481010906100d02903078412402c00010310f03c1d0803400e45080303c2c100380c00750405014641c0340112910820202000b0000305101d480080340000c814010031030529000c01d01614481 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 73485047 1250 73483797 73483819
    0x5010f02070f0b030403030b030a060b1315181103070908010c0309080a0c020415030308040c15021f06050915032a090c07050105040b1b0f071101020a0213020403030806 74
    0x21400300c2540042d01c3c560041c158590382e4500f000c034003520488507100d0b01030007603028100c00c1c00b505800c02c4103030313800c01e0364421448161f01640e00c007103815001507056000004c400900c0304103000d501e400f607640e00009022075040208980c035142c83d030082d5641350110381440d10400c1f450000780a10380000d82282001c101e4403440e80c480866611400752640308001550085404664841c1d11148004410601c041c109a44910b409080e2100c242d03000c0d5080050300361300140e0640c0c0c200c51041c2c0607a40789e001d4030680984110003104c03050111280700700c0d03546926010a075a01d44402451044506a4a111800040c207041c903040201c60744100c48070511942d41485800c5010580004040d426148600195100b51500c12280100314006100d5402d010910041c4000000c40d5405130f40c3c00031131240000d2020000c1c00c154400c0442d4511204814403c02c80030421001540b0306040b41801603410041c081da0000b00c200d082d007101d0b52280d690204061084c968071000f0150300c070034161044200340c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 73486297 1250 73485047 73485059
    0x2060615161a0711061b09040c03060e0106050909010b190c06090501050c07021e060f070f020d031e0c030e09071e021b0409050a14030417010209040c1d090601021e0705010f0207 78
    0x11301c11f809071540940e0b169200000c56034801e90181004082c8d070243c00240c3d586070440101075034094035180384280d40240000c100100341c14101c510403035103d154055034009860040d9000e00b0508026901c45d07907038035800d0010500a0007043c0c0f0600e905c4400030341d186042d1041080540c9410700ca400a0043c4038088072a6886100440fa19140400401070b107374070003803621103000c0d9004400250444448100c4004064208418900d00340c0308280a030b96982c0c07081012511200540300160001da060301848a0350304000121a4002c8018901580d8900345d070070560b181e10740482d180c1c1c030050f440702a80b00c040300700b0201154001142100c2c24088245581c07202a600c002c400030240c08400e012111b0382424070108211001080c092845191005c0300d10030306030007500b00c500628000c1e4203010001040d00d108002800c0110400c0a0035002c0613829002d004c4141c00c0100120b041d48100b40d15103c440380000c0340707483c44402610003090002c4c20140010a030251a0000d0810f55015034428452 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 73487547 1250 73486297 73486351
    0x4150b03121606020c0304030201090b0a020304060e1201050702060403110c0609042c01020a0206060103090f11010509030a080d060e06010804031803120e0102060615161a071106 78
    0x1151030014030644030a0702c41d0080c400d44000d500010300240c400502800d2068011000d0000c81e4003d8a9559400e5603c1c220352519115106c15000180c00410041c0120340c01480c40618808002e4030340000024400d081c203085850030307141704c00503038000d100700401c15604c00c00e1602c0c3d00b0703107110103480d203a140f41010070384034050026003900c0b59407903100c01ca056199000008501880c070100000d40c0c400b20410060007548480006070040c02110000741c8594000d010b240e481d15030204414000e07062507124036440502c820713096410030604008560302c1c0da5081011a840500800c43c95a8589000142c6001c131440c1ea40000000c40c086002c102d00d90f80c01c1a1040c1d88036405040070034400c643c0500c0c60a80d4030312604000d0007450b4440b54170a45580c0131036417414400080c4c00720fa00c0781d2541c0c2e042011000c00302c14000b42c801c3e000c00030a40004140c00008114a00c20254410307041d0100801c1c100e2054216445000120300300b044e48000035007007103d0368202c145840e004000f2221000c411407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 73488797 1250 73487547 73487563
    0x12060a050a0810110c0105010e1602010c0804082b021c090b0f0901060503060403030f0509010504080a110c0d210c050615010509090f09010606020708060601030c11060403050304150b03 81
    0xd030156460b0203111984d0b48003c11103007140c628000810140d0f84030712010503001c42c142c0754500e403002011302d10425580148a0002c4d40e41c41d0340ca8041c10356481e5070740d000c43e59114200c80c0701003070030f884c0c01152106507040c034500c001c61403100c0249c4c90b5510300c404010000d030398501440039141045488004a0016807086400452a00c1d500e015580d81c248e940d409400b43d03a02c034039014801d030010801859132603445207001194080b4144025121054841d00740c030340595019010100801440c2c406500440025400b00c001100b524580c0700504001142c4010010b000d6481c502c103182c841e11301c2c18103140b0300b03115030342e250418000e008090b803115a4bc55034000c2c80c1c250744100343c41c2c1a02c0b00d0fa01a4007a90f007401070003410002c0b1407801c51410003114030141c1d00d400d155820817202190850010038070b802a14500030003458140d0340c08004501030310b0310303503d02d00911125000c1d0500d603450500116101c1d07800790301c5a036520b007003514040c2c8100002c880f05840441ca0640038040f65030b00412445 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 73490047 1250 73488797 73488823
    0xb1b15010503150c160f0c0b0a030606030b0a23030105010311010806090f060603060402190201090308090d050706020306040b06040b1c0204080604122001060e0603010203011503020705010b0612060a050a08 90
    0xf000401171361400c004103541300003000d4940880e004000890750400001014540300035541070000540e2408183c00760b03207910f000302e45d00c0000c100082c0641c01040c09001401c1180a180d03010390764400d00840d0854100782c20617a00d801c042d00201010356084010260020025981c4402c50314100d0600006a85c02a15040c81f803000080072841a43e101e40550306524145011114660104e10004e40201000740044011070380000c0010702c55507010401c050b0304a05901c0c4d02d803a00005035140c2000354001441294415034810022070542c03034400140010b0441d02e0340316507480721881c2000103402c0600d902c0c241c1c034500400c000d2244010101d406c940003079002e5000a4418005101610030348403280002010080042620b6084038054001c44112000350840341742517213800e403c0c1800d0748801d02580204245212110b0745540c03080c0d001701403050041c80001207500c01580080c0349075015240750a00403045105101c042c0c035109118400406c1c0840300d1044040c90701e4800c0d52203500d990348503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 73491297 1250 73490047 73490077
    0xf0406051c060c0e01090611070f12020909071202040e07030c0b030a060806060d03030c030605041118120304030b0c0903030a030f0b0a050f01030902011103070f2a0b1b15010503150c 80
    0x52400802c040011030040d00011029505440d07c0d0303441c05582f408118802c2c4e1007a40b803080401d482410118101e0107a4080050175019144940c0038880540324901660341103219640000001c111400d0101024007410560640d0f241032020981003901c00c3c17604107604640190040c00300b2603549100300400c0c20790501703011582d8903800708143c00a20465000f19000350428405096808440006008818038509608012041c2000384900c44001004c2045181e2003003200b0720119090032184e0751f003c15414043c514022003100400e003950003e441c50701c0030075101c412010040d00140201484540705860a01865241000140d081d202ca58104c5060503a03a44424040d64800c220b01c0102e1f211203030031039948008600d800f0720340e0000d00030251540140881e29030103c018541d449a0100e1441070508140e43c103221131300d84550301008152414602036080f0020007941070290f44840c803903040d1001d00d01d40c0740100303040c14100301c8079819852062410801c803e05000d182640c9149140d8521 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 73492547 1250 73491297 73491317
    0x100807080601111009060204150c0b061203041e0e1305070303030509010f0e0c090f010e010b09060706140f100608010b0a090b040308030402010e04020c0c0f0406051c060c0e010906 79
    0xc44d04114607412804841c4c0d042c98000c1c018001503800030300c1100d002e40c401155030703200c22800f103404a40c500b00c003c01e180b6074180460000c1c81c019543e0209518214187da01e0320b030f500c47c903040300000e075822a5200d10708500001c11103007003035191107503204c400c1c0705404a41c00d2066079001d86802140c0001020325598601041c1188425030184600540c204c1b0100201c0300c0f03144c0a2941c4a2401d00014464101440081e44035880054882c2c1220741c184500e01c2e00c1c1c0d0805503891a06d8118051141d0828424001c20002c280c0c00d002d60304090784100c0e0321f02c441b8200300d00c65820755a401000414500c83d840030420090703601c00e500c0d0b411100c00020103519240b20080c11641d00b030403035000c40c1030854085004000c0c055404000c40c01035100b629602020340101c02400f080c0e0203815040c00c0c040d00140d080e22031609044a01141240c8024400550b054481000400d9071400c559454118880b2051940801c8068401c1354403408440c00c0c06d8520304c28900000b841c0018a01500007040410700d8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 73493797 1250 73492547 73492577
    0x503061609080a0f05010e030906040311060d0f14060306070507030804140307050318010c0f11010c0c09060e100e0613020c070909020118210206070b15100807080601 73
    0x1011010b01001d105039800c076030342401d0005403034100400c1900e09504e031800742110958004111207408402902460a091654685400301000644901e4002130704109000c0e141c00240f00d84141d0038180030000a400a511035010b0031000c0007000240240c0c04001030200040d008410b0b43c2c049581460600055603c030b203401180760f42c102d80a0040c81c40042407010400002001400d11007050340c20156100580000446840d014644060805041101c80802113194020f40c2225007006041810080d034403560703804440b46696000401c1640e480300240003140580102580011036200e00000c8142010941100c00c08040d1070648a8030000d503d40060760401d4064500604040f402c1d1564a9900c1c00ba110140140e0901280050350a84e1441c6041d6a4410300703400b0780d011040c0701c100b0f1268559505072108443c90341644e0005080c0b00d0500001c1006184620031501c455004030581600c1081c410340344070f40c22001c4107004000c42040855540442c070294001800d00c1e100e145d55200740 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 73495047 1250 73493797 73493807
    0x11040b0c060a06180b0a051002060106170712020c0c0a15030c0306050342040209090a050d030f0608010f0c090824040c090c080603120906040302060f0c070f09050a0605030616 77
    0xc2d0000e03800c04918402001230b16004900b0504840c003d8540210b2980c0800b442030000d00701312103410104008150405141001c3c3c0d01400750500048200c0f1640c0380b03500e001480300100d69006c4603605140c4d800d00001c2a915000724070841e6002d05090050604042c000f0307031111540c0c5d420308480c110560f1402c06c41e10034040d589460305908502040c040829041d1100600400c0b2000da0160b080e010200c0d4400c4070020341c3c080181d811001508480700c4005007207000d0400d4241014042d034540a0110340001d00707120380360300a2400d6800050305040c107000944105502d60100c002d68029003a42c5114888075080c0e002d2906041e9034590b42d43c0e41f40d1801d140d0030101508608030003850075800038a030300d400c502c3c0300307006650131011034012103040f0807421090320134900b0007900031000703000030001414000007400712012000c00c0c1900700000c4072000c40c50000e0907401400f40381c0161400300304031842e0340b1a0070303044607040c441402614107200101e95103480140a10401d0042d81d014003044601c15 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 73496297 1250 73495047 73495049
    0x302090103050106150507030210050910020a03060905130203030d020f07060603080a17061c050307060e03041a090a0308030a0b0603070f1701030317090111040b0c060a06180b0a 78
    0x18a150040e5840e410958001c0c2440e0007401c042604041c03201c40c005003c0c5040d42e0340303281e2650061292001189020b0090072000c1e280b007215208581016003400c40070700162032510003554000920503d0005120141c0d0000750003640c0b022040300201015840200440301112200b160169032450350610800c6070344610403001d8052454400b0100c1001262001840c030100c03560f5820001c0036200f485000e01c18016119550f02200606c0801d50342c18070604013511484c00350041c4c80c14800c1d5629241c041d03071412900e403c2c0c2508005410700c030700d07540080c449400134200b400d00ca003007450346801700f030200784a400042d0200c1c20100001d14514034a8100900805000c0e02e440d0700c070f0400000c05400313828241c5100d404a003100400d00d040c03000041e00c060480390141d56030709031580d1000e0503258210b405000e030640c55403206a40320041c02c10708010300040000c0c0d50002d0b50350114001280c146040649010520360034200100000c8071810140c52540200140015840991400042030000c007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 73497547 1250 73496297 73496299
    0x61209120703030b180903160602070f1b060f0e01080603190c05011403041703041e05070317092409040f02030402041407080c07020d1a010603110f0f070c0302 70
    0x10020303440c1c0805606422100c500001910b090442100d584201c0701c60400481d044202540f09004402c2806049888110300d00e01403400140340c42044d403100d0100684542060300c0300180c0e44040e500502c42945444014992885c0c00d5000131544c91008040c00482c80b00c0718100030080300410f000f607a06014403800c1d101e10510521060f0344030b2420b803010b64080d2040c07a0100e0051680036441441500460380b156030303c03004804401071030b100010f40980000d00103940f40c5981501280c413041034100082c0c2018060401820070500d5450300c0c0302c66002180b200011020240584240781d2146003210260200201c2c039168074000b8011002e800d40624031102d944075040030182c1844046070b40c0113500882c02598144180d0441020302c1c400000d0640e4020300154000001400d80b110000c0a090350910060041411070b00381d0700c4034000071034407502113000c08420308010000076130107210703590001551080d031509180c6410b0300c910941c051406641d038580000a049002c11400418030000345078 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 73498797 1250 73497547 73497583
    0x801121121030307080910060503060109020f040f0609090f0c1b05120406050702100302070b0f0c1b0313060318020607140712030e040209060910030b03060702011a09010302061209 79
    0x135003d0401800c0c05426111102e03213004005101104012901030300d0183d500c0a0000e001c1e59180c090408020b50101c0801d01c0d035000103104c04a80d54100a182034000d10072661001d080b14100b10361641120110700c3c080070224030b00f5110140150300f1403811818131001d40d180790080002030030446d04082903001100300b1403c001030041482ca42000c0030b003500c580203460300034664a040c14240c080b44034803800500f101c05081d0000c0c54500a000b15940d0121403208d030103080071440085d0031445501d02220200035000807881085c20f680701e680407801456641b50a000c03020791228070305003d00f40e40300080d01609000076070a05220135140d400402e0302c504e4085400c441e6030fa5642851001c4c0c0004100c3c0099003458000d0060b00d01030003910521900206600c0c80c00801000304079822428409440915440c1d090000c041e5031305201207031284850303030000b064000391840c0d2150808802c0396100d20030030641e001440561500c1040d614489625146035107243c5070151510324016400c03440e409000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 73500047 1250 73498797 73498801
    0x1801020d1406030607051e0c060c040311030601061d03070e040302071503020c030306010e031f0e10060311010305040f0c30050a060203060a0b12010608011211210303 73
    0x14000d03901510007002119444072107074982904150f2541010b40300900000e105004035a10f04138038141219020390303540101894030031241c000e182043e9007140c40c0c8083c0f1101260070400d101d40d03080503a09111048025011540c184a00508190b1070704204880c9002c3c1c10388800025181041030341c0280ca644460354600317161030300e0004d507508190b00810b900c02c484403018400d500d0090090320bc140021501641c1140c2c0e409004540801214488580c54440c4032189004a90f5030b040d00034010384036030008503207098420106e5241454502d40e50002600e080303010000304400410700702078007009103004079031500d482c10401001c10072008003030b0101e84503810004071200c2c80300000300070302000040300340d008240f02904a01e0800a004c080c001e90032044c04440000c100e50300459001d03034010000e240c0261180780340500c80d00304c0c560200441d2400c20050240c2e03604001c2040c01000e80f0483d1009614035592040007050786407415078058a03642c0044040f5940a200c83d048041800c8202e0f0703124 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 73501297 1250 73500047 73500067
    0x90b04020c03070804090e0312220b160e240d060509070201090308010501030b030d0c1b0603020705010b0307051c05030f0d0f06050616080c01110714010501050604030c030803180102 80
    0x26501600c00c4c9241c1b0b51030a114a4400035011064940507441190000d6003a511505814000c001041030b510b031040301c4101400002d03000c030481500640c1c840e012030000b100100400391084002202c82c1e807149845100b8858044403250440390034107503034141d0940740c4071041e0720f0501925054100301e901c580b074541004196507056000c040094029610343c4503a9176501700540c1103d15400909405400c28202080028040c1407103801e224807401620040407242903049da03040015070819000203400003122030520031700b4040c28407071030310440242c40260b01c1c0000041c0f0102c13035005440e103541ca8030901a400c3c01818419a00300d854001c14855480d064a02400c4c010720780c14581200c4646800e0740403a60b402d182082c0c4000001c4e00c1d06c07503920b900d010f880724902c4d5004800181901e64070b80d031084280075605009401071038031841c02051181e560300c507007a0039107405820190141200344030410221f8139800845e0b0490f600614120b5407a220b02d140940c41500c2c40c020038610f580001005245 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 73502547 1250 73501297 73501313
    0xa0c020f060408150c0405010c230714040e0f0715050d110301080f01060605090d052b080a1a040504080706060b0307120212070311072108180601090b04020c0307 71
    0x1400d50303407492140c800d54175006001210300030ba008903400a2004a10400000c0800442e80103400115201e1541d41281900d0746180c59034130f4200c28050540b070032407050941860f0154028038200134014150503801d00e644259504c8541c442d54644108503040d9040c4a070080003165110b1101c0ca8007071062000c5402e18602c20f078801e2003603c4152090441442d00c06c1d4041c8504c200f0303540565101480c00030844100800290484410b0b20a401000c0c0d0490840260120305002100036081c4550040949000500070181c01090001d50a0604500c400030b0459007d06010345c003002c950002d01b603146c5003001d501d680a8100000c0040d40b5051010aa0503a0f540203180b04441564900e042d03003001034480016030051340d080365107007403801001c12646802500089800c03819254114244407181d2565406024070a6055400c0104100e4212803c2c0c0e00c014925480f03950510113803458000f400700240d2f42c000500c030711142130355a40244d80690380d413a01100d2900c4444c00403241c0b1401c450810002d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 73503797 1250 73502547 73502563
    0x80f0c03040f030c050306070c0b0a020c0f0c0315010b0426010905010b03060a02070201080402060313081303030813080d1d07080106050a050111120a0c020a121a0c0a0c020f060408 79
    0x144c284040d0400161624000440d64031484065840000400040d500c4a81c07113440a081c40002940070b000100b000403042124510440d01a0020412460100c0c241404c29203940c8101d11031100c035000500800305000c0c1201d04899030580501c2111400101c842c0c1c0d000407078006480700e94200b0b40c01d1801d2110541107404905c0c03048003078548075104c80c01d00b0422403042e018004c2c0410a01c00c000b401518000001c0e40d8041042500e01001c0140b680d6042281d80c018601c4a2064501c020b052080c15802031500b0fa008131103140820b03841c41152501c6a0034051410035a081c1621040200600240c0a8404000c815101d044419031512880281e000e0511401078034051070000d100024198418000d005009070301901421403000791980300209540880803c1d000e00000c940c1140c016110040250700401d50500c1400a6186500d80f03044c6440c1d0710b51027102c240101005103c401c043d40130445054449904014050130b000e407001c0307541c86091001285c1d00c02c4010038009881c20021070510 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 73505047 1250 73503797 73503803
    0x1200307230c041a15031506030c030f0405010605130c020606031207080a0e0a1701050a0c0206061207030204330f03080a051210080c0102030403020d080f0c03040f03 73
    0x500001d000e01000310a151035a9400d2003540d0040d22101e20b40d0409901618518990003003103150181d041c00421914500c40441c0342c03062400204010160000000303440445000701c1d0094a14104010b14801501000d886104418254400f180800c1425030150000b44009010aa01c01070040c03200c10040040e40e003050f025010b030000007117562502183e4488810600d03030b132590400e586512240e84580060980c03800707001880481c1103c039540e01800100410403110344400c1c500b034103680142950300c0a0304401065040101ca44c440540200d40c1c035501c480d064031960031100e2031900d01403921207035510103504207240060000c01c0460034080c55007031002e010b000840c0701c19034201c03044450740e162252210a03070282000380009242400100700d0070140e450120f0805a115001e00c1c2c50102c04d4550810b12201050100301c90032041c84103c61003d02400998105407643d00400c01103070141c4001048044001a40e01c40001d114007503c1d0707540c0300c901c2286d8031039494107a00b40303000b01c0c980029 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 73506297 1250 73505047 73505063
    0xf030a06021306113004091506050307090b0c1005040b06040b03070b0d0b04061805060109050a0e0a0221070206060f0d050309130e0f03090a050901030308130201200307 74
    0x11807894014494081e1100b40c84008000341009240444c10f005c2914a1060445425566080c00041144041c0020f45004640000c984480d6100300702590000d82c42003040c480180b0400104a030400b140008403070124400595925141c80c4550401e81030b4480044200d02d480240402d0144c070f809841d100f00000d840401001700f07541d0806940e8185403044204c50a010070000b04002e0a40e0441f107141d0300d004e000402c0c803d448140302244040110340c48030b80035a54404106440da8410446130007080d066a40d032220a0030801301c0c0c5800d9100801442c4240c0d00082d0303004038081110244260742804d44946c10300307410481002500c9800c1940d94030311812035005000002e2414015007801640e0240c01103141800480520650320914000d45a0a41c0d0f104820502c02c50140302d00c42c030140c0307910045c0d070351212306004100551501ea0801030280c2240001170000075006428140c1282181030740483c2c520240c0300403603001c11041d0012100302c1441040c96200c1100001034000c451080b411 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 73507547 1250 73506297 73506299
    0x20a0306030204060506091e031509010203090111030606070b06130912020106091a040b0102070504061403010510150503040f02060403030503010509130b270106060c050f011404060b0f030a060213 86
    0x10010b240c00f0382c040306540101c002296000102d8a88402d45d42880007905455a41d4ac074070780c40c1740d00c8440c100c0e021102a5000030421011840130710401c1c0d8001c1141c9030460a44c101070001c02d07454003da510041100400c080071600c00e54032000075940b45101c92005114400092130301090583c6d0f0814000055820001c010407001d100d03002d004091007a4840c62103004050320200320250520b90038841c15400351850100301600c4502444000c0d16002d1400e6048180c12418142102c2008202d5515404034803418010b050041c203101c081e81ca503910b07100f5106c1d01c980c1003141e8040c540c1d44009511800c0054004105904074003d5070407250206d50f400d40d50754500403000c1003d00074910040c001c4414000150140c030f0308a4814100c2c00941c08120303003046107070900c5400c40381d00c0c1e085039010403040c108900400c60b0800c1410100c02919000380440840321061044100005d40f00401160f110b500c60320089d00e80c020500c12100006040303860540841c02c01030025800038103c01c0a07102c107042c3c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 73508797 1250 73507547 73507549
    0xb09010812030a0f0902130c020d0207030b0f0c0f07061505060c070303050309030906160210110304060e010302090d060603140a02090105060702010e0306010605040801051005030a1113020a03060302040605 90
    0x15040c1c0303055821807521480c1d030307450707010b90401800c4400e64a60455a0360004001580300c581c124422603081d070b40001001d02052902a02c0c01170240d00400441d40702080910000d0741c00706005800044400e4450902c0d10343c1e0340c44400030b0140c076140c1d0704035a0000c905c2106000c0301d5000a244140782d1140c022800c0c0d2a20300b80446485011480e003115481000d007040081c4c45107004690024284054a041000c40d00003d292580019a000d41104513600000e0551070f103004140d44600d101d0504d0000c0c0f000d80d1510b01e40324003c51003010306018100c003036221b659010303804507540208001c00c200b8604005150480c0100030502050301e50011060340b54107a04000515201003c1d0024811000e41c0e10340030800c00c4681c4801c03800c90411a46a80d0110552000c000c01d034041e0509855041c2c4480c02e0a44031403c441d00204400080c04004500f040151800f10f100640d80e80c01049142510110001084030340703100c0e82c101a0607a100152411080b03034994001c41c280d80c8210f9080c440b0390f582d00 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 73510047 1250 73508797 73508803
    0x3091b03020105121b0c0102030f0601050a020d030c02030712080a06080c0a0e10050306010305060f0601030204050a0302130603080d0b1c0308010501110c0a06080402040506010309080913060f090b090108 89
    0xc003000740820300410003030250300c41c5042c3d510f50040030b203188800c80d191102070078840380e000410141c54a1f034000c001d202205a04aa5050b804030302071070481d0920301c604400943d1518100003602c1030580d034041000840384240102c2d86940d0300408c0070384000450102c0244007100450303d86c254589002e0300441e0b8403602192880b21108024444420a818008507032101303c005420b02ea401d942c40e0100240d41d4809101d024000c40c01100603110600d0841046450508014041410184108001e21582c1c0d20b592402003500d80580740c840c0002c000e0a051401010590000742030981d0100d40f401e9112519000002d1411007034940460b59209906074480e2000501002804124000018030403944966080c84080e041601207031a48810701010590a589681201c0d0016203034078100400e5040c24001c0e0340d00720340c0078030381007000c0000703030b21000300c2c0d4081c15a00345d102e46c10142c4107901d00100b0740c00c443e0103030089000781e00b01c09507900712800c020403a150b04103002d19032840c00003d62000c04 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 73511297 1250 73510047 73510049
    0x1020f07120f3c02210301050306010918200310091101050f0708040306050103060501051801140a090626070f06030b150a0804020f040b01050712030905060703091b 72
    0x55202c00304440030038000c44019009080000500b007091a4194244104249000203000b0441e0083c06042c042861704004480c024000c001c003c150802c0104600c6d180014894111071110b40001604a0b06035038044602c00380d101d01621140d0003c014011045001180096400044003122082000d03000001c082d20000c40010b88207024908901d061035005130000c000c0c0480d000074542c60088076964100464001e90415a4031658483c01807041000358400d050141c0812910403c0552105c00d02c000942014010040c9818104d00c581c2c0054641c0318440b000703410840c4086c03100d280c60f0045a079801032045500b11203961401f0f81920607800120703528050f2460780941501c06401d2281c01d1340640001e1120f5500030702c440ba150050811418043e01c000c017035680e00c42d0b0b01414a4010030010201110405100c5d40c07902ca03080c1940da0f082411510019845081c0100a50b10410181c000b00150070014100d8001c0300304200c04d0300c0e4198030540d072a0f407050a900d500c02048107920115284d507 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 73512547 1250 73511297 73511327
    0xa09081b0d021506120c0a0b03060406050a0e1603060b04060503041529130507080712020f07060b06040305010912020601060e01050a110f0708010b0f1e1306030501020f0712 76
    0xc40c80031a02c50300b400b070441d2040000d81170481c3c20191007030740421110025035200703925000020007401110300e464007a503001403a085502104a40c2044010310980d40c0c09000401c1c900b4901c43c040c0d41d0603000e50844e4004000c1c107162070791031703641d100005089644126000c8604242c00810005d120141340700c0c0a000d500380f4000349550080c40c824000c003100031703a852298060f0201c0002c400980c40380c01010701c905900c0d03070303004e0b4507051403507020b422038545d00c00780070009005101c60311055411005035168581c05c41000b2911f10841800b1404a1003660005000c0f5400c1c12001001c1c031041c0040414004030680c2241c481d603070784400880d4441c091098050016100b0406c200d2014404c0100304003507017034071054400d401781020a282c6084c80fa5402904581d448010710f20480c681101490300d00c0009032441c159030800c220160110040c0851442d00c1015224540b4020030b040c0c0d8800c42c0503540c488021903540900b192004450f400046080b5008522940202070862240c20f10600f8014 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 73513797 1250 73512547 73512583
    0xa0f030203010b0406080d051c0f0b01081608150402090909010b1305070818100510050307090b0603070c0f060501180605010309030e09070318080703020706020a050d05030a09081b0d02 81
    0x45008000c9500e54827482d5503420080d40c43c4490340305013525100302c944006000300c0c0013a0fa50403050014010200051001890362171043d02c004c000c2d50026400d0703034003503511507200000c94009000034000b03001c0d02c004503800484210030402416015449566050303c11515003100c44400181c48041d140100e40000000e8200130124000c0c19040309080c52207460a000c1e07928030b8020460040131140f080b95480441c501d8102c0030445401c05100d104043e10b0087d00610034620301201107081444003800210070410010100001e003c45c042412811a50250b024001543e441c028120303103002c10345a240040f031a00400066944c060320a400d0075550544541107000d00034802c1140072800202550181030302c0c1c90300c1c2d030300480c500e20114800c94800e10359507490743c0c6a410002d242072640e03004a41554404001c5a01044000400640d146a80c0c500255a81e6031034010001402c80440c00170301024000c22403178424007450f4103041d10103024400316a0700700b24607034003240c1e904007280104000d48 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 73515047 1250 73513797 73513813
    0xd0c020603040305090607031d2407020a0e070e030c0a08060a09080d091b0509040c17070504020a0c062d0908090904031e0206040c0b0310050a0f030203010b040608 72
    0x2040c032602841d44103010782421400c050b40000412100e5006840440000b140c07080501d810b02da40e0081404d4103401601d8410740d8080c81c90360103220228401070301040c0380b0013190310011943c600c0c2d070140207842c1d814200c6110742085c0030054400035405075024480e004040d590001c60420506020441d2108001000c06840d04c1c03516900400c0340085c156000b140802c01c5040400031400b404070382603c00c40348000c1c43c49455564902034a06034211a10400545003800082142540c0070002e583d03188205082c20300f000c2089501e0003603581c1c481e035003050012440e10301054022620604143c007a00d0705100f4482d0503034103007004060030340c03115100450894101e020a41a60b00910f0701511070070441d850310b0403110005000050481d411000103002c580c0255840b0f040212008201c18030b40000c003641c4c14242e40d00c1141c00620b000d00c3c1840c02010000442041152600c50000c09000d411405115103500c144a80840c0d00e01040c2c0c001c2d820000b81c407140c0c4c240b1f03100d0002210010406007540ca = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 73516297 1250 73515047 73515049
    0xd0c06082211190b0301060c1b05150d06030c030b040204051b03070c030507060501120507080703051018021306230f010804020d0602030a02090901090506010206160203130e0106020f0d0c02 83
    0x3e0444250200c240c108074500400c81440b00002980a01510b403150301c41154546020040000c0345101030480c88140102004143c44501000130114445d0341c00544420902821a00a224503400940300c2c0c131078006d002043c0161039210703d000e035009030b03002e001c95901e0204080d451806042c1405580c0410000207449612403503850010b103100e480d00501e00101a00c60720180c800a03086040d034011900c078001c080050400142c0f005040d5000909049840c640702d0b15200d24844cad00c9140e0f0b460703ca03144400c0c0c0209030070845600e40c0e03004085000340c0c4400f01800004204a0040c44040c0401480c1c000c507080841d18409400100100300ca103070f082c004401100ca0707080240040360010aa03003580d0001843c0c9001651040d400c0d45001a101c0401e2001c01904d144181d02c94101c141c5080301340705050760301094032640010385807071031601e0495a80c030803403840c030840b40c1c00d103000500040c0209512070718013801c90480b41c1d9a800c03102111010b8456076104c580071246540400c40d50300c501001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 73517547 1250 73516297 73516309
    0x3110303040c060e030102070b241806010e06040308072a0e01030213020c1b0f010507030512180a0503210f010611010603120c03020d08150409020d0c06082211 70
    0x413010001c1e0000d410b04001d84d0b00c1080f1440d0542e1390f40f000d50581c0610103003038980d0300059540d00034102c1e9001e000221010f0720551000c800f03480c031410040d0700001a215600c2d59802c0341c004660082400d43d0342c003040d08081e85514074000441c0300b08014034070802c03113030075150185070140c64500d0111303540c1d03901e143c4c2040072804840c00346a0205030203000601020f10b0900c20000303902d901366412045c121380003080090002c225002d481c18080103228181c00310783d0220594040705201481e4002c00c0e158412200c44000b510380c004180c510540c030090007000408805000c41c0c2c404c850f455400380e0329100561014070021070711100c095103100d0040003803074465000d00047c0e4003000300004480b5103d44401e01030303a11411030100402d003541400d008140d41005034420120140c5030000842c1800a070300700800101c081c0d4030740700d951a002c80c0c0302955903000c0591101c07035100405103006659550082c07e0726400300c3da0003503c0f41c204d03c0940941e12020f0014010a584510840407140d055020084 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 73518797 1250 73517547 73517567
    0x301050307090e0a02091003050706032a0e03100b030708030403030f050a0e0907080702060f1b1c02040e0403090e1504110c0a05010e011d150705070c090903110303040c06 75
    0x83c00d209101c18840036840e2403494074052043c206201c0b90590441c10a5861b1601c60b50000040515000104142c460001203000c0b540d841d140c42c0c0c06140001d188101d0b407102da1403510603414000c2038410f001c03038401503202c1100040140c0540301c0d250741d10f450003512405076100103004a0400341101d1a0705104900510944080b0b0401400b02000c03c008207000f42000c44200010603401d0050104d480d404000696010a03684042403451600300118080c031120411450140319011904001102100050300c40da40400302d0219140c5564442c0b403000401d05a030107901291110700003040381c0caa060f0406108034092040c1ca0710302d11461060000030a5140c2c0c0c54010b0304400d01460700a0901400640c41d003a005400200c4c2c0d041007404030908548114111004640f01141960700e00000801c0c03580b940c10788801e03000440d94030344000307840750311a480c8010002d1002e64804160b1802a600c124485802956403a01169484503142c2d644d1000f510050100d00c84118100011841010361f45 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 73520047 1250 73518797 73518821
    0x2060409050c04080f0a03030b030c030d03021b010504050d030615081b040305030d050115090807170708030a0906180e0406050417070b060f0105040e011e12051e03030105030709 78
    0x249030035966400e0506048040c5e0303805015811114043e02495494080d540c003903441200074211134000f0200180d61060000d038010240b5030081098519504004100208440380c0743c024132a61500e49040341d12440b00ba040100864a4141d0200e02602c020011f40100c44070354540e0b0041d511030f41e10320310800c045a528090200340030000880041d0061001d4a460b6085010100d11541459902d806080f8000e2044003080200d0008010720030001070032508a032039030780e114101d01244161242c1040082d03002081745200c0006c000102d07a500001c00740440303407181c1d1956000061101101c010030450310a00c44100e8440f030104010031781c40d90155401c01d1244842c004c07460801802c403492900056400d031551152001080902e04014004924220702440c1c000e2a003401c280000f11f00702c0d0107000e454050129041c04a0012000e50a210081e004442e034046400c1c0407440c11a44e1454500540c4031000107962200e000d40000000340d9040c0c1d00e004010b00031050030a18958010000c001e800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 73521297 1250 73520047 73520071
    0x10513080f13170c03010b062502060f18030102040501050f0a030603141506190608191a0f01140313030c060e03030601020d0206040f0209090a06060b0d1104030206040905 75
    0x400b8602006181c040c01460301c01070b0040c0c44942c0c007409904000c60ba01c3ca150090341002d0501186503a02411150a10941121038615440f41000400340040390440290010380000c1c040140a0290020f000110780103900c095840c02140c05150907401a8840c0501081003440000c5000b070142c405441c05001030310380043c240f5900d443d805031030000359070242c815410240040c20501000c1c1d1070150f11190642d0400300d121100c0c003951090003990311850040005500128140c00e16040de42c408010b0500e000f40203c030446400c40070a00010710090f440742d114140e4545965009400c1d0328200c00450460a0a41d07842d805c8440118103c0002182007212100c04c8200007003941c82550125002c44000b142c070380c50640e002a00d0212000002030a5603c11410400050741d0340e01e00701280b03641600e180d9050345441390441c0ca040490f100040c07016040840c04244c0e840c41c10b003d0240d5080b07080051103e03d4011105400c0707841f450101039088a001c00c001d01001d0402d07017040340c2142e404501 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 73522547 1250 73521297 73521307
    0x14010603060f0902072f3102070503120a0f05010608090a030f0e060706050601021203090a08070204110706140705040303021005070512012309060603040303090320030301080d02010513080f 83
    0x1104143d807406218085000d4200c826461043c00c007540d2264100c1d01c09141280030504010680301318581030787d8841e224a8002410104009007070003138a08151540c1080e840506006564901410400a41080b42c626100c00016000e118404079030040e40360307030060944409070b40c9048802c1440c050010060001032040b5032a1031310b99400910030070380581400290b604141d000281007580c244000243c0c03200500a101c598500802c0c4c07100e14541c0110125036412a0b44080380181c00e0805200703841c114085429024010641c00208c1d0034803032101a021a03540e640800e035410f005030b02001c3c0059000a08114081450f9882070740c006103942005414160340340950344102000760013002030400003a910b00550340307d80444007002481100d9110081c503001d0701180e10343c0002003004e02059111300007082458064098030b004054410035011080d25044241c40c4c2d070364000e00c5462114841c07040d407485060702c10321a0901861040c0c2d4050040c0d841da844194003500300c107010441000c01081 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 73523797 1250 73522547 73522583
    0xc08030d020304050d05090105041e0909110a05031c08040f0209090706080606070308071206031b050f0301091e210f0e04050709210b070314010603060f090207 70
    0x5000341165403000503039240f6061620f84c0c00d0401107004541031000a0000c1a0a40e030480d05403025510104801c0b016401c6036526021400714561100700d40d00e142c81080003c0c030081010aa03030808050700c5550410340d50301e040c0740daa01901504280084890000c61850501c5140420740103400b0b000c4038041a1300980004501c04401c0d281d50045910021042005503000908203900c071000320b40d0b441c24a0070300d4402900c8a07600421510800401510642250640f030b0f20440155404c00c0550310302c42c0350101140c05e40e010350b000710361088440502641403890140501c1d40d0f8a6488010b04580c0340c041e0440302d9001504141c201c41214150324880b060003000c100f6400441c40c0340d5501030b5103819001000d8170140420140ca4000d501340781c01c1101c12500701e00d408003110760403030540010b40000050b10b09007000500008002002c15400d0205003a4180c001c1e4040c40135606031100d81d40d03a55607068040b123140344501c1c60843e00502080003544082d07405412001d0080c64181c0300325180340 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 73525047 1250 73523797 73523803
    0x1050f0f24030708010f03080a03020a110f030309120705070302010503041a09011401051206061215010902030103020108060a030507050907090806040f0501050106030c020a02121c030b03060c0a0e0d0c08 89
    0x780c0e4906140e000031041116031540600d00c0c90052190030071040440342582c80762115880303084c2100c0181500003460031101f601c40e8280d04e40b180c285c0000d6403a014540c602e881d40300d500948079510113102c0c1e90602c41ca103c400e507003107400c1c89501c030004001c85840c42d4019a20307504014400e441001d04a04004112002000103c0c8588410000019041e4800140040c03404045c0c100a00813450048002202c00c0c0000d1480d400440480c1d150340c002e6102c40c2e2442c0340c40417280e80384180840e024000a0b940c41c0c3ca801a506aa10036214151160ba0781d03402d11190700c0700b40c0301c06000380d03110050801042c100800c44640100c2c0707910b02580580c2e210039003945840401c2c2e0702112404180c001c16002d21800b84181409002c4529051001c3c0f64144e100039a2603036900c20280c401d1004060002e203c4100304400700c2851001141201064020322018004004844041d0300034020000003c280441403412144004440d0700e84035070515140c000e10001c80005101112140c0e160071010a590b6010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 73526297 1250 73525047 73525099
    0x10b0904080a0f0305060603150616080d240905040201050702060403143009030a060c0f030606020706200705090c0702120c0109050123030a060303020606030601050f0f 74
    0x5503032565442d40c81e24001044901c0d28a04503040601c1c0c2402d104403a503c0d601142e422083c484150101d101c000400500e5500c6840b5800071400782081d081001c01060001806000d900b0240800041034501d2036005406000190388128140b4407405002140e003541c40242c00c14018580341d820120300e9404601c0c0c80c0c0c030640003665200320180011008602c200a00d003e55142c0d1000c43c103500f0303010b6080d049024040d4070200422000401c555480d034504100c0d030a219500880e06000d00721281f2400703400c000201010100007403d061021a040f0300000300441112210303a10320001d562481c1d418a003a030340a5541071240d009210b00040d166591070b040d03600503c2d0000d17005075a514184104185c001c000404600c00713400548210f512a80c1040d520811100c00f030820100c00b1031113582491059001c041081160300c0c2c0402480300c610301ca42d0000c030a81e4881c2e0201c5a040d240c5a0130999903142c01d00c00d031603101c0d105180450302814482c02420000901030700a0619000c0002c0081e904050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 73527547 1250 73526297 73526303
    0xa1b06060e0a0c09050603070509040e0105040b040507090905070902030726060103060e090309040207050a1406070f02030309060408090612010b0304060c0801060203030a0207020d1406070809070501120b0102010b0904 95
    0x1d02001d1116400042c800e2250810b01c0e030401600e840e103044046138041c0001040d250521001050011003510f0b01d400143c0701e8640103008015a07e0030b860080740020703064605540501c02d4201c007148030f22030380c07040350800d58108004100d2180f6150400001c0c2d40024a6142001542d4211442048429403615022200b00940c10308900d4413400042c01c540180d400221400c1c501014000c0c094404012540100800e660150751200a802e005181c018490300080c0110740001590303996400c042040b40c05210199030303400004030704007400c80c0c1c7c9001c01e4400c90b0745500100080307000202943e0040c81488405008981448500000008044401d0f8401d095001d000010401005500d2003028a8640c1e9410100c00c1c0e54100306000390703a40030062016021a0740080c001065554201c0b0500c1c1c130642c0002c6071040302c44407504068561a040c0c841501288140c00882c2c3c40c2000481c051742070320b106a44600489010710014806416a10351550565695000e500342d15119180304170b01c1140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 73528797 1250 73527547 73527569
    0x3040308160c020303030f0901050c0711060d0b0619120501080606012d20070303050307111e03120a0605060a080a060f1502060604050f01050906040b09181b01050a1b0606 75
    0xa008071a249c29184020a403400c04001000340b60300180d2045100410b25a056400300d84888145140100610010501a50052020580007601d405120710440c820002c0d54525540490b001054006d40e003080c0140040e41d00080300154807540b003030340c0010b096803c080c552903281d05049603000e52040c2001503c40010b1072600e0700503281d400304500e0b514005016000300506482c4d51801861130001511103020004250855138003924104003074003010ba0070810361640703503c0c000c0e00541e0382e6001080c03003072100d40c01c0b00000c1c07800140c501c1380070219030340038010a1400004807002c443c80030b17000342113001e074541d0303840041907041c1c18111020180030000c84c0504101f140d00c0002e440c0041c01416503200300c0c24001001207850482e2007050440301c003550481c059880d0003001401030311000b04800e0b0000180005c02030040300e114014240d10300a03205035411310400c00c4a002284210526041c0030807001c0120500b4144290b05a026846001b8030705882c08100e41d4405003903580951010b040c505d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 73530047 1250 73528797 73528801
    0xf050717010f06090e15090c0d0b0f0319080c070303020c0112060506041701231e040503121b190801080c031b04021605031b0303040308160c020303030f 67
    0x10200c8450140c009152000074080c6040c2006000c102da9006080c000c1d8000e102040b0b08514101540400f154011319200d03940c80e10a49140b06500320b0b40600d01d059081184141c5242428015a00641800b8000c2d01541f02500030301d101040c941002124124020800b048603400c05011810195209138040d0031036000310340006003030f83c80d800510f040180c40d000b0200855641e440403582150710328108444602040800180104100007074082c404604005c126403030341649000610500c10303c004107a0f0545990004102202c084500800951042200d1041a005030b507034030fa848258421400c90300714048410004a402654800c4452a00007401010260b0410707200790241034210000d141e0380342c104000941d02e2750890003a0744510354461401c0b8150329603404a50303d04404101800641410f440c09940e41ea0000c81800e11107446401441e40c0b03020f01200306c0380203540690b0340030b00907110146026a4216210480e070b00784000b105900740181c80130b0024520078041c00c0e110f11014 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 73531297 1250 73530047 73530077
    0x6070609051203100e07030f020a0207090e0304030809060c010902030a06050708010501030903360314071203090b030907031202030a02070b0901020a03030b060903070e040303110f07060f0f0507 85
    0x200080140e1031404109000b0000001e13034801c0754900721074100b009100c060301c030034100350001e101a25100354440d0001503c0880396400003a4203040b2041c0b443c0c200f00f03220144200e55128080c2d800002d03d0711504000c0498680f9100c0090450b042800c40001542e8616900282c500340c540c4a0440340c3c2c640303510800c225507411122541c01030a0a00f818800d2084a96000340402d01c0d910303c00c0340180307d88458205100e05010300d00c0b079503807456520507040b9407281001908101d400b1000c010510500b4808241c1c2000b010750f00840e9545510f810074858144a40784031680c00081c100e0103d442881800000300380c000606203001516038000d1a40c0e20300040f40241400c04507000000582010440c0120300e07640000c2010507d50149400030b03020119100044062003600240c507403502c581c410100700c4003030010600c0e00480c80f90b04e08100300d10284229040a00680b418511401001e02c40c000c00304149800155050010200c00034500c0b050401400c1240c03001d46240000074285442c040123 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 73532547 1250 73531297 73531303
    0x118050906010501080f0403030f0509070f09020f0f1606060e04020906010906020d030218030d090e0f10030303020d020d15170a0506061c0605040b06010e0414041b050607060905 78
    0xca651580034211640c100400a402e00901400c0c5c042e80e001d41c5000a02130612a0313100310000143c120080c06103007048241c10350350344803d0062002c004031150f00021048280d03c2100c0d4026003a00039241040020214244c481d0424201c581c2c40800448021000903024401c03a400b40c13038007810041e01c03402c2c94014040c031400001c20720350501c4480035080c4840760300007482c1c000841e0289005603403101c0c0a9901d068880e408030000b0380511510660f4150150000f0248040d02e4422980240135915607030092403158094400241462503601c080c00468030035001444044006600545007665040c01c2004a51220b40c0380761039174110321070070f00c182411303002d8017001021050024206a059504e540d629000f003c0c0410344604038800407106080d045502000440750003d504005601d0725050002071654101c40c00ca0001e0780c0355240744824580792140c0d5420340301307015000c001682d9030390380c0e0900441240302c8941d240151000000c0c5564800c0b0041c5809480740001140000407464500d00d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 73533797 1250 73532547 73532551
    0xc0308160c0503150105060f070506180d0c0f0b072001090201080108030906040e090c060f0702090c0c0a1103010e0d0201090b130209071b0c03140606030105010f060e0f09011805 78
    0x711130b80040030100c1811852842c01c50541c2c0c3c0440d0f9095842006441d40040c1e07100c1e000c0c0040050081c94100f01504d1042460039800c0000102500d01210750304c441124104620500100254040f00d10400450b8503a080990302081c0e030b00b083e14260600501c030004a0824040700c0a2580d15400a1021035a01ca85520700500b4120010343c00d100700000080d0715801280500604243c0200000c0c142100400c1400320021025000c0780d9181c030942c0401d02182e114440030382c001c4c22100003107221000c00d2000c50705415441d0000e07208111a13a90342840fa01d100c1d00440307038503648900550305184c0c024044602000040e40000681044501e003a5240c0c00f4002c10040c0c220f400188604056142c54100c10f900882518001669540109121550308481d803401341145401c000048104950ba80c5000c040108078001c88110380e41d0203040600b1385009004111072140103090411450b4001c003000c0c3c01e9240c00802103076101d03040c40085082810264009450210700300301c0e500104500c0d206450f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 73535047 1250 73533797 73533799
    0x1020318061e03071106090c0402070503091005180906010c1b0323010f05010807120309030b160305181c090803030403030501050a0801090201020c01120207050106060207150203040302100c0c0308160c05 89
    0x400b072881d10801f80c07612644000e00841c00759400288000c1004010710840d40c42090041800c6206580f080300140180c029080b61408a281d5900100c0d0929180000c00c0c444c0c04140c4d501c3c0ca85054640d118600c411800038203100c00c1c0030000010001491455103000300700220007500f80c15a1080c00e0007400d540088103008205450300300103000070140800d0a200b40c1e0324100c01720030940074515003203401241580c4050300085030041407181c0c0c00001110013840c1c45540d581448141c884800900f40710f000100f00180c16407081041c54120204c01029482e02d5103d4201082d44a64400d00542541e00445080b00082d640c1d000501c1907190034040c3c80c020b00076a2008000d001c00c1540041d5440150600c07141c180700301002441c4409400381c0480b211150301c80000d120076917a422004e035403000d59014051140700244a0550814400825a001c8940082581d00321155049003656a000c1d4080700f40c84010414402001041815004040140851010a01f01d007080e003841c0105640304d410071 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 73536297 1250 73535047 73535053
    0x4051501020d0801140907090803040303022116060b040b040f050615030127060503150f130809040b1206010303020604030e040c02030306041a18041106040501020318061e030711 78
    0x600c0030080002e21418503880c20703500c6e5101901c40e0032041d03d85d0120755100300c4503440002004010141c4c041105090301c0b0f080e07280318001040c032255000b00e038000e45010301e5a43c14041d0341c1da40450800d4010420404024100144c210b403042e02041c02da6820042514540303844001f031085504000040700003050030344680c0d0341994184082d0300005008502803019032140c0b0b28060450440b660f001c807006000c0202100c4240000000b0b21400c4007048030011070754a21100024800f10750840307001a801d600848030384c60603041c10100401000c41c40d20041d0820010301c4030000070a41000658080d500070307001070240d440c0c5071400901404203803d40a00944c20956202585a000400e503504210300b1100422151100c2c4542042d05105030038580c0d1040700c55110012203c03024034001d00642c004c8a4581c0e4095800b07061044521980c8030342030069004028a2420760071a1660726000d000041c0900d18103201c42d14010f0b00051908284e11072410000180016142c1110b20203039000108406 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 73537547 1250 73536297 73536299
    0xb16020d0804080702041e14010501030203060f011101060b1b0d02120301030308090f010507030b040e0111040302010c11060403230115060c03091e03050d03050c0703031a04051501020d0801 83
    0x40c80c03010042d2005180d480d01066000440d99103801912444032a02803a0442510443c4d881010b0410003400c400c49041c03507000410154070a000300c2c3c2c456140a4003021035440d00f000119030341e070500c002d011383c0c070b560308c0401040043c800c2000300001110403142500f004404526030341803800e40e03d0700f8004d640c48a0b1900094610000c1600e044070740508200c0b07155a9405066030400d1000a0241000e528041c108481c4540541c00b0050281c01602c082200301d00310a882400c88100504140003503005004c10001984502083c2c000c061040103c01140000d21020a1550300140c00840303c9183c02503180502e102c20344005482d0540000003484004110440700a0141d02806040c08101c1c50104403024140510410720040c10044a0a040c9500e01d0b0b080240c45405804112168080c25903103111031031103801828091494904268601105940c01b0780080060071444442d408030200600da9644d01c0c0d124841c4100a0044204040f8403100002803d141d0754030f1002081c04000c0e00 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 73538797 1250 73537547 73537573
    0x201020c070b1614010e122a07090b060d0c0914060909071103130821030f01060f03090803091005090106080a0f020a03050f1606170a15120b1602 64
    0xa1080100c0d83c00c02e0f20710113120b8280c4503041c05030804085214081c401c0c40110285404400d00600c640c42d600c12203605013000340140c030300000d0241180c41c50303298410481400700500341d40c040303540e59400912175850010024081002d031860300c42c48001292088104014a40114a4444030b4900460710246840f41b032400143c10303140090001810459840700c10710030b4480c10812101260300c0105410302155880d80d00c255101006602030041c1c00701d03905074038400d01121064a006201803070191015030700f0500304031680100503681008142d240c00c900707400304010700700440c01100110068003020b1420040a030907240c000d800200580c0c5829000c01c007001000c603410114662143d25070321040c2643c00091070303204c0c1a410190590142003400d1028600009040403810030b14490080303401da50781e0040d5440a4154030007440003009a002a032006050751051a4003040013002da148262a240e40341402d82c028081140d000b8001d50078000c864891110f042c90601d200d0ac0103181e00b014041c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 73540047 1250 73538797 73538827
    0x6050c0a020d030b030102040f140f010f090320090108032701021009060b0405010b0307030b09060109060807140f0a0905060313140709051e060a03020622050d030201020c070b 77
    0x2c4241e0702003565506641c130240d50290119001010b21503840ca402c5038039100e203000c440301a099101d01c9455880d8006026502400802c4000311042e2503000c2c400e8070b9515011001c5100055401b03541015691840442c0e4417450000d0207009040c0003107481b50510a149856003103200d1903414200e181602d440c100707a90016210000700b503005004640c01c0110324000019200b0a00c000b58890b00340000442d08020100c0a50700c1800950f40500c042c0d1001c50510801c0f01c0c00350b918a0000701650340c14420640901a0143c00c54003500e46200c200040c5507884820750408403c01c000313982d00050340d030551070b4030502480c0603007401c40d03440d80348d03040ca00399543d10860800d000410480154085400c0750300c4c248080c500a00440c1c60900c224a4000760800000724606503400c2c0380e00015020850a00b0f094040e60145d0340d002d00414603144c60140e031248080d06a400c0380c610301031051720104072a221035000b207500a120303800250711614100d030490304086850b042030922250502c800b1181002e61 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 73541297 1250 73540047 73540063
    0x8010302150f0f0c0a03090e09030a0e12060f160203040806220506010602030301031509020306040308060301060801110c06010608091f0207021c05010f110315010c020a0f0306050c0a02 81
    0x203040210b6540c1c102c1e2080c6929070040303820308820202c01041c10b0341d522101040556101e0b100750307604a01103840f006140c1701c3c04020f071044115a441800040f42d194001c900705400810014194039680b12280c3c0c0d00e46c6082c5088802d2414086007006002445c401c010182120b205e0900203182401d051031103499036104001e12040141c0a02140e622542203603055440d14984c1010582d01a980c40d0100a0b503071b90b2003840200d82c8640740c084142c04460b06031041409e550f600901a0075552070f1a102200c00d8840a41300940c155030b24200019000760912030289010f10f400c00b41a00c5400e4900d000d070a120050b0b100c00c082c400b0040401000440102e840c48454580b000c500c20070303442c0c4828000081c0240c0c18000c0d0042400d05604290414083c000c081903481007000344000d8440c960440d0513101130303400145c02003c0a00218052014504014000343c4040c503240040c2c00d000d40019000159030380c0310048803244c02009000344090b078001d507076004d101c0d84101880d200b07100500a69038129 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 73542547 1250 73541297 73541329
    0xe03030c030d0902150a1116030503072307060201060512280303060e092d070303030f0e01140703050901090b0c0310180b01030e060c0f030c0702060f0301060e0108010302 75
    0x20f54440c1e041199500b04030300d0b048498401e41c46403145202100a007010f400501c0582c00e0307101ea2003038805a00c4107001c04c0e5098030340c07181c0614200b076019079500340d00511561850840c41441c05088103500405c22100008040607030021500501c1d00d400c1c0100480c0200c4610000d8101740902c402e0883c40010001c0101405106299006090309086005210540251000510140602045100020307002d10344210728050703030034078210b070241e0070020740e035144080101c5800c049010404a070196118480c600510f0102140d2008030140c5c617821a25003030880346081908100740141c0c0790b814032603950300c50303407241c002c0001c500161a4a50703038600007840c480121100000103100540001c1c3c0c82801400b001d107681112401e8000b40e03101a089852415000a152540018400b440011003a0040600304106031905015510300001c55000410351004141c080211174010380324540141000982000310035100d50500c1001040c1c0300078156290f0400c21480010b00143e80c0b0021480c420481c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 73543797 1250 73542547 73542551
    0xb130b0a060f0201180605150d0b01060f02010207050703121e0905060a1b050c0315150d03050f03070806040f0506090c090d08070b0f010b071101030902060702040f0b010e03030c030d 80
    0x50800c0f400b42c007000310050840903c0302c00e010104641504814064841070400c4030520423200248482c100d60080060700415240c2d0042001c80e0084446c0301c87e0f8402d81c0b0000d0302c0d045d05620b82130320f00790050b801226017071000c20007022075a80c00040045800040b116001c2d10380000c2d10300500e1180207000742d501c11a000074481c19a240a14104a889445155144800740507410b2207900c640855003240e000340540c1101c651a000c01e501c2c001d11a0450201c000c0c060041001132000d4600c407800100d0500204110810580c1208400f5500c1041a03644013881848d043c028042070b02c20b0f6070b401d01191810442030092a40d240032009900c0b02c51804002c1d00d43d403112000911a01c0c0b9000d000c0e00d2044001101020301050286080c4100500d580020302643d03203031141c101503c035054010300042502183d0250942c03003504150101030000b040a82800d4680c5c000400700c4100d40038900311250f42e421200e038196040325849040c40302c02c034065414511917200064807841741110492a0399 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 73545047 1250 73543797 73543817
    0x13090c03020702030a05010b211c050f03100303020c0114090103091104020c0a020f0a08100911130f0506010201060b0403020f1203120901060b071203020d1d010b130b0a06 75
    0xa00c00c0d819a103045400408644e0b000c0340301d08081c0e0082010340c0d2114069503c104103402100c04980b001c0d0900301d4000001c2600081d80c14a02446903031f904054003c0142c100030000340ba400b50350145001e00c242d00d410000261461401034079040c505840c035414040d40060b6640400000400d40300c5c118002e0070f010030104030503e0892198079580c0d03501ca510620101c2c0e64000442d0020341d00d0082031007910cc0030040c80f10311081201010b8948140d5100360b0002c10100309040e455004820040d120318012000440d1110001c1ca120b50706031030700c00c003ca6035040c89000c404003500403250452301c00c0c0020410642803110706031081c86980006030090000c01e00220b1940c4071a40c03038200450540c070a607901c802030807071000541c0300c00b541c070b07084151709010300070230100050b00403142c0443d8041941314403801b403030b0015006504600400c0c620300e5a43d03076940c8255040304e110000545588800050140e4200b800c0203d09545034501003011468803000800944038100b07134005940c2c450070408118 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 73546297 1250 73545047 73545071
    0x5090415150201021206030c060304031209170304020102060709300c140307060e0f120f10050a0606080c04140303040b070b06010906031404231c03050c1309 69
    0x8150941c0718040503401032030008219036066019000ca0f5040004015558486004069552402066840d48907404001150010380540d12103c50030700c41c0d000106161840b034070382401050a050042003140300010400045603414004603500103440d0421282e481c0c2007001c10815540d1010340500c2442003e02c05080d81e9050700a401081903114400c005001e48400320000351072402040c140c004d02c240340001c038089000743d00443d1541006411900c0b000400d804200300749a003481909890f015074085190300c200d05000021110107034200c0843d07103040c818480022164594000030030400d0200a000b45244a02d08680480d8514286026038004820019043d40301c0c9511400c8220400241e90041000b410340042c49001d09072100c6242035503a001c2a02500d14011440d0703404440840006c0014140410b00b4a0012219000c07450070380c250540301c0d1500740120101c0d000500c01040c0a00c0c61541401000e0344452394488040c00c00c10b0100403040c685030540260f2051030749503a420059 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 73547547 1250 73546297 73546331
    0x18090c07051903030c0801060f0503130506071706010e0a051201020c1b03010507081513020408010e07140a080a06020c1006060c0b0c03100308030c0d1407021c050904 73
    0x89035006019580c030012150071060242c03800d240c1c120003003070070140c580ea80f00b80200001812903c082c0c58003100c000c0d1038482102c03194001400340840805040210f00402c0301004501d21032040c54540c29001107481481c06a0603500900144c1000443c01d07000d030182d1202c0007480300303c030000da401e030340a01818801140a07004424400240b031182c3c04000b282404e40000c01c0c401c09400ba0020050ba8030b90f210115000078084804074480c0040d1b6403465807504240354408021405030b0740060400ba2501e110501b551080486025181d0020b02d0070302c00007005030b4010b052031408407044404140781a91080e11381e41c0780b2001500385031780820b844076489000d000c0d1000d8880301202c02c0221984415000d0a01488600c064030039141c25000079a8840d1302800700c900840454035034040343c500e1035075429007940c0010025410140d042c0035003818103084d4002d00f00b0b05540c6112141c86803a205070000d113007076401c00c0351140d00048144c209400b5a046022140c2401068a0206502c0600000211 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 73548797 1250 73547547 73547557
    0x30a0803090a120512090c09130c030c0906090b0406030203060f040c0f0e0403030c0f0e0607020f0a081f020304081801020a050d020f0f0c0303030f070c05030c100506030318090c 78
    0x70400b03210511222190b04c00001c007080000c0030302c10681529100b00306669400d100541070740200700280820414207000d054034106a2181440b2158281c0f00c1e42d81141c0c8040640c00b015200d51600c00070302c6426064041c003c80e58105036000c001051031a00042c2c0d0343d29019040950008800c0046428000b45100c3c0b2400b500f00105510040c6d543c408254541b00000c40d41980003a24084100c24814880c103001aa4a5120350b207407140c00c01d2440c1040320992096200300d91090709103161040c252240107450303008042d200d014121031203800c03108120000040031900c87c02c41c8100208000180c1482c01e51741d98001d0b0041141d190022000140e03d82740c43c0000c082d0072842040405050b85e9030000303003803903503503c9101611802d00f29000701701c0d1b0360260b1035503c0e03a0540080c000585a00390488003998003200a01d000f002094a945a042c25a0322829196005070040b030300c00401100c181c0070301c80d003244007075000354030b806400c1240b10040710300f00c41c40c0c501c10488003020407508401c00007503807 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 73550047 1250 73548797 73548803
    0x20040501020f0610030b04080408030f090a060804030206010b0c0f060a0204030201030b150d0b061c0e0c01020a031e050f070b01031214030703050a0f0c030b09070f02030d110f07150e0705030a0803090a 88
    0xa50707250b42c0b403351340d00582c000010f10b5209803802040842d103070b0b00c560320850040d58180c0007019070f0f90030f02030b482c01180c10807a405150b070b210360400d4441001e0b017044514050f1520020040c1e4a60440c000103041e00c40120034a401030400c01800400214210308842e0409000303403000402c80c14020019103180301d0051400200300050f1000380d000342c220340c01000900381210071103054030300c00d00c010398072840c01ea0780150101d5620710000c0d0000d000741d0313443c02e1114007a01d4290b00d49100300f0352503006900528425112070742a40014030400c889050b002c00d20542c2d80c24080055144040321301c03240d1000408101c10181c440010030048c182da500040c004c90360b1160103221101c083c203c01130043c4107450710a407180c0403140109a88600030040f21b40c91040b150f000d94545040245660050808000a914907410805c000304c1048000000340c03086c0361052841040105917001c01d4800e82c0c855820480041e04056420000d41c1d0703001800048007640320580c90340b0707580d6030403a0034140702035902e0103 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 73551297 1250 73550047 73550053
    0x7120f080d02030f010e130209040c0e09030d0f050c0417120c010b0301050105190611030d0501090c111c031a03060108030901180303020604020d020420040501020f0610030b04080408 80
    0x1d14140d0406030091442685000d4014869a9899451044080c1c0075501103c3c1c814000150384050f041030004550310074021400d0102c5241c0d00c6c1c4203038111410851304801260000300d5030340825102c501070304d000082c4c0b800d024001410f0601040310244a00c1c482c001a10350340300e044e289aa00280005130680341c041c8155034a401c450010240030b8056060924425441c09001150910300071550f502400001e5085104132400e000b02560207c445500041c01c62101340144600403046020701ba010304a040b2000c1200d84002801900604003a003845e9042e800a405031001c4074450b40f2a0728002c00e051030040780300340318525580c2260440c090019014065400041078060b0004002c0650030382c20381c1c480b42c540c0e4409140c102480d80a0000030016000600858091316003aa01020824002400010307507200303600d500f125090540040d45c9608070003140c10800c640c0c0521001da078014005029200620303001101c45040c841070b000c0140b010b030101d0003050600c0342080a5501801402c811 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 73552547 1250 73551297 73551307
    0x3050a0b100306080d080408030c160807060b040c020604031707200601030c0501080103240e012f070812040302010b18040c140d020d0203010f110c10020c07120f08 72
    0x1004000d0f0007140191101171103142c284c85000e62107140c05601c2640c0003103100d4156118110209040c3c0d0100b80c2c01072085c90902211008126428003e1003454462040041e5000da00d40900081d07481d200d078610155045141000007207500055050f01482511a05040d555203800e81614649140400300003e055918410f148824001461506981c080c0c5100400907507a8001120344003400d0200074000c802e0440d071010381000050300b000c0071521614000c1901c008918009003100c105040b0a82c50103009c0ca640c0c001c83d4007110107070030040c00a950480c600249500c54080078401d0081c95007c4a07030341c1e0002420301d03100f03500188141c0300c01001308000a10440c118904508180c07401d68503803102e5400020501c6000c440e01d8030325080a84813106050003602000b124032141c0c08141e03015501c4a00020440750184901c05007169081c1e5410788845030840100d11f0000101040720800c2c1c4100042e00030418001050812650ba92203136030011081440c1201903103e2210005003c0440414 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 73553797 1250 73552547 73552579
    0x6010219060203010f0902040f0e0402030a020d060507030b0301110909090304050409030203030106080903310306150311120c101101141608040305040504021308030a030e160e060103050a0b 83
    0x294100c0f0b40184078401307170644514600040b48180c4c40740144201c1100c0d0304110031019102c403a0b034854002000d44442440940110307580d481c10000407030342c1c41c0e0307110204400c885d058443d0019020054000700715403800402c03800c0c440e1203035581d1284205143d400180c0982002c00480d0007900019005101000340c5207000b81d42c0ba0420f00410011480010026840040000640712900047d40c0e40350003030b2028a20302180c043c145500700004440749000840070410701c1c014002018807208512011754954207000500c020258250342c81b0f07140902c110b0117035520000380d000020408803000340c41d144622000740c40c00002d8a03071402d4194209420044014024a0030500c9100750079000212110390620803247c1500440d40100442c106120500c01418594090308000c221316198200742920303082a14555000301c04200006521074100e41d141c56030510146680c4561411658001c43c142402d202041d1300080019040690380e1000034000d807441c0d040301352203c4028000280c0581184 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 73555047 1250 73553797 73553801
    0x40603080a0203120711150603030c01090c06020c0402030405070e061906092c010905070504030c03201005030103060f060e040f06110a0207090b0406050306070c02091509040201080601021906 84
    0x380c3e400d0181542c100020001400741c0414001b01601170b0140800b807402d400c0b141e0403410090001c540511040c0f1008042807024811304030394a0180c0420f13500701e171070420024604803420800034043c03030040c0248000245c00040c0034042d1842c21449003840c0d5035000101d10000400e4031600700140c4e10503000103400d5000f000d1901540e0354040c07800212060285101c4810b00d038011524658410840100455801580140d0304251249091032400b56282c032820000c0e40c40d604295100781a080100305003c100b40502880e42c0d000380da01c0176044000c108050401e000510028099503181e43c44840c090300598415005041e0710008010795086c98207054000d90140079084400318900050030b504d1141017000e0701c030995220742c010807555041c0b2610b03070090700288d20426002078550001154503a010301c0462b01c1052244d0b245080c2e6651401080440309001e4040404101824034402e030300c0d1104032072994003540a090490f49500c0d00c00c0100e1500d505545404443d00c8a1030080c0304011881e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 73556297 1250 73555047 73555057
    0x3051309060e0f04030807081b0403050c030708070305150a14070f030b0a1215020c01020a021b060702010509091306020c0a06060f150f02070e040c0302090a050705031302040603080a0203 82
    0x140e05180c000f6038541e41241c50050003035501801160620340058100380c0725030581c035800290350465a00c19003107000e003404607401540040301c660b00101444a0103003400c00c8200000c103208401040c00031b1854030f51a4171f8a0703601000c0b0300c40801c3d01c0c0c0040c80e84e0a19400c1030b80d02c1d034480b944e07029040c0350540006100078060207004000a0401d051406c0034606000300c0d40a44900c0410310200384999a90081968540c1e00701d051119001c1c41040c03503014080c80589503240080c0c02030207038481404010030389225024542403043c031040c400440981d03401426600583c0301500c4a01a507220842c40c1c8402c2a4a81d8004015500000307401c80c007402e01041c902c001c18440c800522a1300d46405141040c00310a00803a102280c42c40e0000c00480e00c20b6016542401450064451103074032115001c01c009030840d015581204804001c000710306240d0722040e40061f2101e0208042d0520010090030b82c40003a1524441c04038821880080d036403142c0c8000011640050400c0d544e4012160183d126048 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 73557547 1250 73556297 73556309
    0x203060f0a030c05040c02011803020105010f0806040312050606130906050a09021606050414010e0616030b0a0302011d06041206050603120307080a09052401090c02190305130906 78
    0xc140c00d4480c0c01e00751008015603034400d288250440c1030106100051240b080307010119929102d04058846040380c40349043c500a0b800440c080d8104010315142c0b0f0040c2d4042449580844104400b10b030b8010f40c011201c00502d5030105042d201c000c006003490190116902c0301e0a00040c0010344a00980d100104591090ba03440d405155103099080880c002d030032035041014503030f00c0c2000000d1050b85c07050381d020b40b2440b500b0440c4480c401c03809085880705020b00c450b940c00f100c01e009411030300d000400d8402c1e205103014041c0c000b42d800031174400141448000d050150fa000880f600a135258202840e00c000038000e071340c6440d80c498440341800c281352400c0d07070520b01d0000031403080d0038089054068400c4880d4542c0c519203078008100c0701408010800201e80b5520440c00c0700140301800805561010140b03115004d005032001d05446800603400003040c0c03407914160726881ea801207244140b03141504080e4112a503542030940f07491048031040f09111800707541c0802d600b20941d1100c016658 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 73558797 1250 73557547 73557559
    0x20d0606030507020318040b06070c06031a0906010f0e03250504060503010501151202090a140f01020c0d0303020d0204050d0f0c0b03040213090203010605090a14090c01140315030709020306 83
    0x111440113a0300d900c5126401e5482001c04808840e050815400121041101070040c07440d0040e01c0d10f030301c20743e03410340d0300900c0010f502c44114100078070507218106050002200c00b218241031440001e00511b00c1514a5010b20000f5103149003103a0301400340817042c105144810780c0e03222501c0c0303c40e01850741c00e0080b07511507850914080b9003800c0510885060b02c01c01000c01c88548030643c4180d82400004c0c2d450100c0640801c00c030a01600c40c00c074038070004c010808444486405000801c05443c400700c055038119840030a0f09801c960f10071034810046501420010b03034034090f81000401034841c0d81c103e02c0e00400c00381d0206041164091107000b460380146c10202c00c060721444162000d1006a030013035030040f4040c807040c080b18410362005074031910003400003030282d603554081442c44204039103030303000d49544034142d61a445103000c2042d88164042e01505a20f400e10300064400d0f03551000c40350b000035001c03002035090305031003100e190041da0080803903003d1665601240c0c044d510071905240901 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 73560047 1250 73558797 73558801
    0xd0e0609121c0204050303120109050a0e0c06090301060504090305030f15010503070e010e03060406020c07050909120702010903080d092307090e0a17030f010b030702060a05060112020d06060305 85
    0x140041040700e88881c8540d40c5516000540d5418686941ea900e024200c280d42000000b40641d02000102004000c030101020740b985000003100489000500056581e41003110b07151000e035011513406820798040343c109494000b0400420700511840d04074582192415260a0505801070702031031240c0d4854141d80b190744d5440607100e800c5203407051038601042040c13001c24107150050341e81000881041c513000c00303032040c00d20000b445c012064400796003003035001a2083d440c040074044100a800161121152400c0c10b52000d1360361200f01c000c03801c00c52008154041168802c0070308000a41d00801b0303082c2c035421190300b900020940c4800403150207001c1740c040204112511400c50301000c0300805801020321f4a03002c0000b40103440000d58542c0520049100001c0700305c3c1c2c140d04030182a51000fa1240f0300580141324165068003e104c02c604c2c04e00803c1649940000d020b54409554680803070183c480000580d221012185982109400403c03400888004ca910400441d0742958081c007850b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 73561153 1106 73560047 73560061
    0x140702060f160501181e06020c030301030501050a050a050114100e0307031505071403180717010c080f1317040302060703020303040510150302240d0e06 67
    0x100e902e40c03001c842400340910881ca90400d60b40c16480d03a8642c035885043c02d0611402c00342c0050b4600c40010300400c50a030701131b184046c42c0307482101d841356141c0c81c056010305011612141894601070005811101e6801101e0407102c070580b01540b0015444103000310782001400103000e00c40e6034074640105403002c100450055000300911013128040070420019101c0180070f8400f00035812840c00c030070710381c490100d80c3c110160b904a0b22080210743d04190034504507500a03007006540042d21495140c064200303030448403903a40c48100c9999041031a0810180540390107513003044041c0c03146c000601008203803200c50a0807178101d0500365680d000403207690000700102c0043c0c1020041c841002820808141c85082400040c040c440316143c040c2c06451280c4006032040d1043c8029151000d145c6901c10b101e12420320312940d6a50307800e01480044c11100c4503c0c1d42c03d102c0c0000140b0300d = true := by decide +kernel

theorem cover : BRFrame.Cov 73381297 73561153 := by
  have h0 := BRFrame.cov_init 73381297
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 73381297 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 73381297 ≤ n) (h2 : n < 73561153) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
