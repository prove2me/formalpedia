-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0382
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:31:27.216335+00:00
-- url     : https://prove2.me/submissions/89dbe9ce-2e60-4016-ad80-988615f0c67f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 68525182 ≤ n < 68705038 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 68526432 1250 68525182 68525189
    0x309090c1707020f0303040c080c010c0803070513030f030e030d140d0203151e0a0801060e0c071e150612110405060f09090303010303090609061b06060308030f0108010b01020102042409 81
    0x5e00c0040140001d2042d4020000111005502110810040c0100546140c1404000942554021300006103200e02a034007d11480ca465111101c5498490317841e4154000c00e900184c00082320704a00da081790804019149100c0d101e8140429580282454240c2d644145104280301030740201c04200c220284030300380540310500501c5131402d10b00f82080380d500e404420640c03920418244500048081044c42050103855a080e03400440391355920381094140d0110740c0423180d8000c4041280c3c2180c40c01803c0b44055445901960003403803d25140350255940381e0003203101003602003e43c00000e0020b0340951034149081e600403d05550b40c9000452460b4050180358000c80c45a0410448140200c0110f042c0d9210341c50743c0046a89038a0102c58809450090502160a840b03120702030207142c0000c2c00403940309000104402d0b450f03944001e0309800130740d00d5040d01d080040050209040c203000f1f40c2001c0400b0301c000c506061034558511541c1c0f6082c603d003404c6002011103510300c1031003014010040e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 68527682 1250 68526432 68526463
    0x402070618030305150a0e06060c0715030621060506060d0606090e09010603030f0503060310020f0904140c1e040503070e04050c01020105130b1e130309090c170702 72
    0xc01844841074004000900c2003103002078507060014901140c0c44055a903100b1001e03241c54002e80c1440f00e0b01007035200203000b895010600b0322030740300c1d100300130446d00003e4180c40e001b000c40000b04c17000150565040350000e00440c400d5003040342d00c1c51450030602507080d40028000c01d60f03480d0754000c201d481c8221000015210308104021880c00c0c2c0020002c02190100c0c080b12025680e082d105600300d0301a0700000f0005071a03418001a520f1180001e560802002401e0b500f4a1014030364044c100e034040c0207211202000810318101c10f28080c8502c0010703404200400110303203001d00c1207100512071000708540a070003540e00c00405481c54810fa4000c0c2001504450026031640001c00650380d00300d6040b80c2a00c604582c0c11015481030280701d0140d5004580c1c43c2d11180030b40d850111102001b80300e1100c50021000c40c0340e6240c00000541d01500345048548900d0180e801d00038400307101600b21501c40b90904140c2c5030000d44c0b0038000126400300e040080415103601404a00309060701c2c1d10340c0b52 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 68528932 1250 68527682 68527691
    0xf080a02100b0906102d0908100204080a080a0e09010320041a012f0106030b100305060a05070302072312030115030b010203120a0f06240305070c0209090d0e01050f090f04020706 78
    0x365402440e088288d410040450b0801c1900d06041030070380c4224003503d070064001d80d0b80e100003d84140058802401d06041440102000b000803411000c0242d109803030280e810407040f48200100c01405811810a8a041c040c003600b140ca0401a140341e03215050420004014090410306a0000800184032007848000403408484145001e080203000984401c00003402061404c418000f548003129400005070110340e4401c0726500090000414020601da000c00c01000000c0e055028106121541070055101c89118001f4038a0304400a010000740c0d141000180b0640055501c0c41e00c03140d40926010034920347d6800100e0940c00360301140c003410b52094080c480d034100079802c0003010120104081188a81c0c0b00f41c89034a10803221040309180562150a4210030702c00e40005071f00038a40e0601c400c07040780c290f01040300210103c60000c1c607074010300014000241e212135000c0d440c1c0400d182141c102620344055903254450304450314410620500342c422591640d80549040680140c001c01 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 68530182 1250 68528932 68529017
    0x109210b06040c02061506121504050105060a080403140f0a020d020f0c0f0d05030708030702010204180911090c160602090405010806040308010b0c0c06070302010b010305101805040f080a02100b090610 88
    0x5991010200c09c9104500b042e00100e011304165040e1070b0444602d644001c540e07120b40c2c80603039080c654407140c400c03406010002c0c6103450f24001e0041c544540540e0081c02018200f46000b4204044000c490b6055005000e14010503560303840028001d140032100d000c1003017003500e803007480c610604100404582c40401003002c20380e01980540121880f601c40c115400030103031500343c200c0d40d40802c020030b00281a81da0880034280040d2250344411203880c224585804074588240c803808000080302d07030a40004004200341000d004050050040e100203040600300b640e0040c103140e01c1406200240b9070003084824040d40100f11501300c109c406400e440c0d6980c81410000d000c3d00301003003054003003800c202c0070a44070380003040c0c1142121010028024004011f1900c800a043c1c094020b480c460303000c0c400c4c00007140340d20340105030340710703072134000341035112013541c8440c03c0d100e030555001d00c80c0740036000308415074072600006540040c86150144103880421a0a4660090040a140c184100c055001e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 68531432 1250 68530182 68530201
    0x1d0c0910020609070503060f07051e0418060902030903040b07030207050904230c0102061504110307030e1902010503040b0403031e0507110601031a060109210b06040c0206150612 78
    0x40c061070200f810fa900d51a00ca40606690b4030b0240c402d1031b071091102000881540c45140075014841d1081c084882030940c0925100050b0010340200c0300700c0304840d461035121302c0c081c85650000c201a8009500358904084059168003403072142460318680014403801f09882803000d0405040e0003080b0204a040600303101401c0b005811400b44814a03007150003d00c40c40c00213407081440416070003014131380e42d04400207519060309005590005e40710341c07012180094820180d4400c178565a07000070b241c518040602c2c5008889243c030141260544480030150b6409030450394019001804105c2e15165454114001c00e2580181c62600c10503800b080d0704e4400e41e421540c040c00c0d06039030303c581040c032200c0310a4a0340d078207100c001c00b0000c500d02100032030301c9402600ca41c400c0c0141404501d1a94413441c024001c60707c035000c04d1040034003a00078000c0100c4044401d41000f02507800704004204018041c0d075420b00a0101459850000c42c1d0b940a90b031000d040754041000820030480904001c0c0c0c1d10f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 68532682 1250 68531432 68531443
    0x61917010504060c050c121e0c0d030c1407020402090a09290f0a052e030e10060608041103070503010908270a030303020c0102040b0c0a1a011d0c091002 67
    0x4840311800c4c4008003400c240718400751008000e801c40a030003070b07080044904116501243c010302a44108560384000c000c0810068a00303000d5501c0506050b1480000050441d801100c000f0280710f9410320702b080404050b4141d031040390303058800581d900392110026002580d40e0b442500b20340d081080600d001a04101460702481d543d41d182880e0204d003000300711803081d01c8000540c01c80039500e42042145040101460026106034039055040c3c0048451301f507008081c00401e020076101c0903820000c402c20400350324015041c9000700244c0d410458005c0000303001030009044180a29080411950700f80500e034001c2034001c2c0200904425890301d03020a030040c801120110010800925183d9500c00c2c1840b03500000408250029045541c2a0029001075403c3c2d04c01e59800e21000c140c108040c03000705144104507004003e03811043c0b4101c00281540c0141440b40d2410340d00420103000c1500a14005004421406519655007140351126006011303010754444070704100504842d0b000300381c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 68533932 1250 68532682 68532691
    0x4050405010311150f0d110409050103050307030809010b010e130f1a09010f06050f071416080d0c020a0b16060212010f0608060108060d050a06050c190c05060619170105 74
    0x1300c40b103c40c0d40f10805074056001e0b42c0320f01c40e4080001c10400301443c0c4103502501c0d00c6100420750034101a10f41a5942c1114002d8008507000e0b80005802014103070040c03841e40d44903100200a0192807002da00091520300d000d40000d01441044006000c200e2807904011446134203441c04000e0740c460720658800650822100d80c2c014100d520000c141c00529154181c203a4419031a081d103003241d48000e40306150700c5000141d9410010010214074500e040c0045041901c01d148611420360030f26003000c1c10049100c8140c000d000081e10301c1c0006880c2e10814400f101e43d081c5c44191103445240c036203685800c1000c0d005001c20710014802800c8019100c54506070349040c0c0311000103d44403c402c0c1d0300c1d22010340302a40461103980002d01189062400c40f54018880c405803104013400c1d0740c50b0415500240c40d52020304102051507443c1c080000390743e02a644a034500050641d006d500d400c0d48401c4e010b0304081c05048130303480094000800082c0390700104200044c0541007903807000613070f000300380554 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 68535182 1250 68533932 68533939
    0xb0a0c03060b030903040308210f0a050f040309150908190501050c0711130e0f06070206091908030a02090a0f0306061406031501030b040e0f07050118060804020604050405010311 78
    0x401c0455011210000d40c0d01c42c81607070005600d041d04603203869555402c440c500364041010102445280300000140c0c0d40642443d502d00a100e040c103400200a95600030181d41c0440541400c10002ca94400e591100300c2d16101d0344a110030303140d602d0844e5016100e801c01480307403007103080040074803a5a0039180d1074980544020451600c1d0b003142e2419a00c64880d0150402501800c510803e01d012444510940d041d41c100081d004035081d0389a04003048660403203400d030094070800610340d805012940d481843c242c00b45c08a550b0b0343c0340482c1c5046880d50b026203c2c83c80400092900d54030303941151000107008100c4080f00c1d42d42c4d041c2070b00d002040c0c0411680c0340d052403000140540c2c0c2c8400d00718800e20081c1807504554590b03d0300400c10301e00c41001c80c1099143c90101980e900c0c1d504c02c0c21003050140b40502049951543d0b81454aa415800b2504210a14a0300d442c01c50300030701c90805550030743c509000242c4540c00003e0f07084c021f5402c41d941c4a40f0b4000000f0030021620b001d140307000c106a = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 68536432 1250 68535182 68535191
    0x1b12060905061f2a1a06010c2a030818010509102601030f052107060b040603020405161704030f1803080a2a050318040e030a0e01110f0712030302070b0a0c03 69
    0x5d41c04159881c82c10368840307011840e0640b02c2da0024011a68546142846030f9103010320100d602a4804020381551055420550000e0400302030080d8910440f5212000c0c00c0107403408a11070040707500400d41900240411102403900740a901c1e43d400d4240e02210746058440041d6102d04003012207907000c80c400c603010701c1100085d40445007480c0501d1240f14a66441505054040d2a1311014103502099140e000e0780d281004001a5690300c103460064488542c1410082d4540c50068168090b1040800d2428034041c01c0100180d03001c08012000030041c07904540c4030980b80110b18185181f9080206030910208e40e40300159803012600c0c100c20809040040102ca010700c09200b60b5200c1034018045030010000260700d0f88240c441c50406410207440000d00e01442c82030541190080c10b00c850019500c0c0706070440ba5039000d40c00c00300403a4000003800e032211004aa917656510039224142c0094008002001894000d44c140c0d40c031103030490035241c1e90b8a01440580c0c003c1030504081c0004c240382 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 68537682 1250 68536432 68536463
    0x10090303020c190f02010f020c040603110f03061b0708040e090c1c0f080a0908031204050c0109080d030f02270a09090503030c0d1b12060905061f2a 65
    0x10420000f00150003c0da400c49900440c4c00456007481c03414010025440346820310901e58680b44614001580107801c0c0910381314800301000075107032034001c545100750700110030702c20700c0307a540080c2011401c40c100566540b0542440c00c0c00307081c020b0380c1c0a200003e07104001c11110b01c02c081013040c0b55820844a100008100c2d1160056407a55034901609013220901d9000010324968018080740707840e81420b1640c959908401450b40d8400e407402c540130349a0005210421800f003110310300d120800d0070306802141c20400340e6030780c80710030311400c0d000c154445200c2243d142243d4101d52402d10b845054401d4058200030312080c40c1041c1ca0f1b120f00a0100380c20020308401c107480345400c6103520030701452554a030b140c492100754020062000710b0a6079100c800c4843e040070402c039100981281c07500f05001140c3e00000044480c84d07030200028034100002c100e00c0c0d03641d58004044034028a030030f0038403440c482c0d031045070b015031074000f444114000003100800710202d0310034410a0512522140c0b4050b00c0707 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 68538932 1250 68537682 68537713
    0x3020c060c16020f010e060406020a060f050c0a0507020d0803160906020f070306050402030709050118050c09010f03020d0626060907030f08030a02120f010623041710090303020c 78
    0x90a10750390400b415508070840189403030a0040f41075101490080c10050505d00021442d9110ba801100564004580782c1c0802095000b41c21a49845220030000340c9002080030350700f81310305070206003008000203c04003155106152a595250090b4406840c2c4c5005040078860710202210743c4045a603960000920910000c0c0440324012444041c1c0865460351303803104040c050150080368540600d803400314403a0707068410b583c001d1008410010b00c000f07425201100711000904190240b6604105496050341c202c0040e41030020036190050391440340c007540c640200016082400001c504541989070703440301403040218031111300213860254890f007401543c2da0500c0e1000030202c032004500c541c049950903000d168006407100000d80b8100c0d004622220b800400c40340c9202000104005029955000741d0a284450214101c038405166640454030140101e10404403468003d22150320f11010901c068201c4044480b4148440c201030715002d006034014501e243c2052103040000320902a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 68540182 1250 68538932 68538937
    0x80703080d05090c1e040902030114100e060901031509061104182a050c0a0b0103030905030102031506030903040803070b01050f0307061e09030515040507080c06031614030703020c060c 81
    0x4100920b188a650590701780d030443c9001e01460f141e405517603594403202688080c010984400c4400800c3d9070f00d80307060040301d500d2400d1034000c1c2041510344420800b0b1922121038090659800c00c004000c403420031210751001d450201c0005103140d092004541e0441d0045014100303a0b000300c0107880a440007101d4410484a5003043c009164145925000f20840025107000700d13400329192075413034031111448079481c09400c590304a40e0100040010002e143c0d0100b10b00001e800120000c1d451420318080e010020220010607501c00c11f030001c0450591001001104e005060110540762103030424102103606060902c0352500070070b25100c0c0b81e00e02e03280200f40d190039120180c8840040f03460079519500107103815001700040c031841090120104004021401086840f1014902d46142c94030701182041401e600a40345a841209038044581d5540c044d698460401c4100071182c042c0e158080fa01010b611400b60350390440001800381c0b25900d41c00501b60801d01c17104840164880e214110800d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 68541432 1250 68540182 68540203
    0xc060e100c1407020f0402030408040f08030705010b0111060a1505030706020105010504180b1f05040e100c050c0c01050f04030803090604120207050a030201050331020301050f060303070b040c080703080d0509 91
    0x8171320744406044c52130705501454100b40215485401d140d180d404410015205030080ba107245d0020545900300042401000203111082c68005000c0c0c203490a0581d5420000c0c02c02280103840d1000c070301c0070295114000380103000c000e0480e03104995810000c0d000300420301455000c0c40c18250106080041554103482d2264446039001e007995400034071240244182058a1058520b02c01c001150340d1a0700a0803c0e12004c0c40c040c0051f808001d0320803040382c100b0442c1a043c00030501546000c01c0d0042016100d078002820020307901d030408400ca5400b8812600014840803000c0240302c0d0000f000107545200354400c1e0b2118601e02806c1c0001da9840751540b00e500c0d0b0040d05c0520510065102d24083c68206118001702d41000340030302d621115000c030301c80f45112280e8003010207209601c2d007402415040410000918100c0c2403000100341c503840707110703000381c443d40103400402e08204481405000629444040c2c0324141c1d200c0c6003040c1a0340c0440005580d4500300004904090404a4411800e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 68542682 1250 68541432 68541439
    0x6080d0504060807050702030a03170a06140d06020c16050907170118021201030528150b060c010606090303120b280803130e0915070c060e100c140702 66
    0x10649485800c0f07074860802480d1004028050280b007005032030810484081900c00d4030b034103405000202c02d401000c1d100401c0060b10b01d0421303108101c8103d031802c0c4008444030544102e2001192420908080c0c8201281600079202d2902c0c0036076545e2150183ca001d442742240c1449603911540305c11a50168607140300c80356002600300402170b1100e514401405a000030b140036081040c0b0007101c4a008600f6441138034590481c41c0e462507104407241c1c2c940340d141498000c0045800040e00c48414484c02c8400c11240c295032081c0c000e0007a5115002c0c0e5580e809040001d01890342c544c0c00c000c010000a2204601060b0b250700e00002240007402090090803019110b60000344100508031710360380b40100c1001c681400d561011401c0e6000740010240d19642085d9207040c2403401c202404220001007501031305401001f0350400d140780d1801d0306500502c4919001d10402013a081000003400c6c5008105940c8c801e07001801070300b9032950006100e0410079103640781c0a600794400190790b4412180700951 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 68543932 1250 68542682 68542687
    0x3010b010f090509041e14010c0c050a0f1e032a020f09040309150207080c010207182003011401120c050703030e0705060301030f0605010803041404020a02120a09030606080d05 77
    0x440c01c01340d0041c0c1e4045d001e292000340c1000d028034070220b01e400030710b41654a114640041d0528801c00d001c0c000854010b40340c022003040e01c0f40c0300c1c1510380c045100014160440c4c49000c038284159420040c2e640050240c43c9101f1400d5881c2c060007008401e40f0b464100d00155071907400507070110300b500f41c1e801c1d00580f001780c0ca04490f00811917503100051044003408040c4001203400c071801007803500540c030385030010700045041c940014074144000b4051811035010400a0100c0e0300404028040380e8038501d00410440d48100c120a821010b603c00c1c1080c116000c000041c0c90291404000d20b40701d000e81394402d08004003484c8000b078071010070224010030300801c50340300002d200e940a00040c40d038400503100c40707640300c20000e2203030750082e0700c00c0c0c0c0c03c812030141100a2083d607104080c0100322080003580341900e0302c07450320100f054490700f6510403680410390700c0d155802032041c00032801e4100811951013044007030150140800d8041518003900d0002c0115078510000f81c1c218540e8001e40700c060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 68545182 1250 68543932 68543939
    0x120204020a17010602150a0603081b1c050301060305090d0206011403100c050c0607020601080a0831080c0307080a02040b1903301706030109080f040503010b010f09 72
    0x81e60104160804100c04018010510484404040d020705078036405000c41c00000110b102920201403c540600d0340381070000c00008803444110740c3c01d2062440d55450301c06400c10180d0800308100c4a8806140ca1005c260342542c9d4044000c40c140c45064078104210f80f00d041307000b640c880a9981d064003584c008001881020802e240001d000c0301c0040807030341918641c0352804240c0d240c00c40440c000c25004035041c4e004400034484641e110b40c00d48000c180d20f40c94041c0003aa0351959250141001307000242000e0303d400240240c1e884038000110f12002080840280d036020106407003003100a009031808080c0300d11f00400d03400c04a4030064020305a45015800b000010308000c031106038030900f150700820512000c5082030340154080c01003012403803400c0a1804030464800440312041d440c01d03410f0b04803a40c0111140c00c40341007001d203400640c2d907408080303401000310704406864004041a010a05021000244295041600244840159034006560100500c0e0001c0f010480045051 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 68546432 1250 68545182 68545189
    0x20a08060f04060302041503031e081501090305190c0602120f03091e0c031c0c0312060b04030f020a0602030703051801051606091208100306020309011b050301030308010b041202 78
    0x444448000b040000d255590341e00080444030703c0603001c04000c0c0d040408109054004003100085002050000d10030f41000d44020a0610002d0149480c0155603a9800c3c00303034410f440a1025503030200456021403504c8100da200c0002000007121592042031001c00c500744041184c0d06c041c260220b080d800d01e0030901c0300d6402900300070700c00c0c2c003140709400100000900c0e01a0300e202c2c01d4904405841c143c2c40082c2414104054143d218800108a224601c2030b5940251142040c40c0c040c03510001418050411201070070300365008168580f00410b0103c01c0c04035641120017580e07c210358403013003503070f03078820176a241d000c1c003603020300800c4080c40346c104c1c400602c0d840750700c004005140c014500304403000d00490901841c50142e800e607580e52443d6042146181c6030300042c484a0401c924ec510f0b00c1c80c00c0c0c0040d000725003c000d14103600031010030301e41c56094004001c0c811003010300c0c138103e51020700d00801c190000d100550015540d4400001d420f030b0500b00300ca0a54481007009040a0384603002d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 68547682 1250 68546432 68546449
    0x50306030a0803010308030f0a1509051f06050a02010e0c010f050705070305070b12090705090a0b0109050603041412030105010509010c05160b04060207080f0a03032304080a0f03020a0806 82
    0x1019058022640c01200090700b041c011400f940c49803000984030b00340005940040c0d42d0080c1644600351800340f09035040d9040e40c450307108175911403101155558800ea501c228001e4a07002040e6009074019000c181d0b2600714020303011564455000700f10817000002650707640c402c0d9140442c0400c0f094003e01d10071a00c260001e2070344078003d03422504042d9595940c3d62401055920050000034003041c0300245041880240c0d0b001404500106900343c1000c00149041c900034000e6456550740d509003540c05d0b401140d10f00f004140c0104010f84910300f81c107101403880100d446030207035030182200e00103081000c54180ca040e0340c0d06950355070410110b40c005581c00d081560081c2e546105462640c0c0d041d218108408010b04515000143c65500d0108007030b213095466040f5540c1504410040c449458000600390410303901442d011802050f1942c000040b20802ca0310542461160400c000902003002700906000c017070f66441c400403420126007181240035038000d0500161011003c5440e91805585 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 68548932 1250 68547682 68547691
    0xc0f0d0201051207030506040e0307120e0d0203010f0504050f0601061e0504090e07050103051b07080f0c06090d020c09190f0b0406080606190b0a050a021203091615020d0503 76
    0x1040342c5862283c41504180240844540001948802c10071045040c580078410350400c40000460800c2c1c000c0d40c80002c0c100250840e403003002038140c0e030113403c1d45d1420300312190300750042d008104813800304c01c40002411f01140e068070240326180d0041e000c00c00025034181290090364a4100c142c8503a88908081841c0303008600800c0300a00000c5101a014800c0345c50b001c00030001803210a15250016041d120020107142a03c51060b41041e41d0200d04001c5980c80f962004840340da031031a0b50199005030113144800750171480349404000914030300041c80a00240345408807111484000d00b04458080d040700d500131403004516131903100d5115500611411074185a02141aa0751480030404940540c2c0c4010a558450130034082c190030401c0b0306031000290303207082c106100d0501c542d696891048400000401c00000383c540001071080c48107041c554480e50385582d8074108544902e030b03070b0a103001d000b0780151544d110015900318079200d900c070352034400c1d005403c2200e0962410b844a410090 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 68550182 1250 68548932 68548937
    0x9060a05090303070b0f1f050105040308160506130c0f03030e01081003050d021509010b0d02010c06140a060306050a051909030c0203060703150902130b0a12060e07030e0c0f0d0201 79
    0x4039404c000386644108a100e244c0d94040c0c0030386490400c48813031901c1042a00f0a05100840c0b10070310030303070341d2180888080c0c94000f0701156039004444c409803003d588424014001c0c0c080c1e0814031100216000c4a01089030140c480c100b070316500c2d03250342000b000140c44020017081e5845080540b95000780140340d0700140e001c880d01090381d6a070f02ca580c24001000ca5180058003e05690310344d05219000154005041c000200004244140032904446048401034117000800c042201000410b80013a808054504c0d030028141c203114076008050045030104440740c80c1441c002417080040c81c4541445406c0300f41000030504c428142c040c0c006d200016041c0d003049905401713100561401c00085019078100d690000d486180401080c03550301303554010038445401045000c51680c0d924078507105a4000000c2241d4603084e01e94180e800c00405640b1140481c2000c1c4006121203d640318644079006035103041c000820071070540c1d51162016203401c4d0384060700304c00e005d103d820080e9002c0c4003a441030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 68551432 1250 68550182 68550187
    0x20f030c030306041e0f020a090f050d020607050709150924090b060c1606021e3d0b0306010603091a04060e070e100608071e12020c07030b090309060a05090303 70
    0x10f207103d17070540b850355500780f22081d000039030185050b6025202c040181400c032144462035050800240340c10031600c0b0003911801002c20001305211090006200a0404c4401045280c04030f071900c1c031614070304c0e10a070350b50700d8074142440c1c1d04410070540c4445401070107249400d165040a0f4800014114002e80c950440d00030301003054480310403c40202000d6000309207440171890000020710784030340c030090092981c00c3c14281e000d0601000541c104075041030740a00311241d80380141c1481c101c9800340605406240a404951040b405501090300f10405400b41c9006a03201c150035016920f42200003880031030010410f5101040419640b41c00070b100c2c04c00410080441082d552800809070031650910038000c051148003403c129507440105405c2c2801d050b50325000b60042d044c801642e10280141283e2050400f0940c41014a19004150b40104544480107c0d11255480800d8042255840c1c801c0011903a210400401e0b00c208400003011a4600403071040e0440d0301c0c0d0403040303490340c062006 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 68552682 1250 68551432 68551481
    0x50301020406050705060601050703050a030b01021c110616020a0b0603010b0405102405090d020d05010204080c0a1a0403020d0c0909030305040614240607120f020f030c03030604 78
    0x280001d10040c2480d030f40301600d510640c00e0032410140064000c50500008010520001c0d030000c09603814501e260500092100460005034240801035080101c035101c00840c1d0315015810030702107515000c1482c11070703030fa44c0d80d105441c1000b052145e01510150344014070900001d4405042a90b1180000d40046046413071100440e05480007924080350446141c80d0030710400103408903500351000e01c510b11241c0c1c1102010090054401c030940c16000e024417a1410041d034540b101c043c94400d070b0000c02150781b160381b580501d45810b003900e1041d104814489000828103104080850b1b8011100c904030300e0b192441d420040c045444800c00c4611001c056400150b040c940e1154050841c003a84011551340707044e20348442100d5040860700b02d95580c8900707200f040c1d982c2541c2030400c10b03209404c0b80400340d4800000350280c0240c4000501e075021042c0000b0999030701942403840e0442c00d4080725010221251039544a0180c4524080c280c1e1007440020014501600301c61000302c091001e444100d0007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 68553932 1250 68552682 68552689
    0x303020c0a05250b0d0f090f050d300c120f0f05010b03040c0302010f02030c060916061707030203040204090803070c020109090c05120403090e090609010f0c020616030605 75
    0x41c01c0600340c2d455041031000084110002c0141828210507405842505041400c40780950203441c04510136240d40e40c00f00741c0b5500c0264001c0740090b4004900d05411162071a00656441140744150001524050901c2c101020035100c500c214044e0010a02d1030720402201c0c00040c60860082401c2040f0030407000c0c4100383d18418088802220403000c92080304102d098004e03501d040e0702240780d91808100f00300214802030246820380e0303424685141e03001c0503040200d15501840c4102c0713940f409400d050045164000039030713a6110700201003110340b003560303090152045281c00c030001c1c40700041c4000140000b03200c0d42c01568014030007000090712001d03d403103110503a0011245140890110401d40c410b41da00010750000400113a5001d0008201c15000148180505440c0c6e03c540c40c907120110b401c150040014801034072812100200d07518250089558600342500c40c020654a0700c081103d01c100c082c06403102c00350a580040005d034845800d044807800c115800d074000c25a840c080411660b4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 68555182 1250 68553932 68553943
    0x218130f03030903080c090102300d0608060615070609080d1a03010609021804150e04050d030e0102040e0103080306010306080709020703120b03190609020a260c011b0303020c 77
    0x1d0090b68001018207032441c1c05000004081e10285042c00305004004150f80c0c000b5030f0a1001c0c2c20b0280410344011958424203007810000034000380560082031143c0701030303c140d201c4401c48880c9001c96503952590410320100d2101e5507001c2200030f10821610002c2005500702e00020392007000f1080c50202070031400c0c421581c020b4605c000c0d840402d50b1070382552500f4014003000d400a01070444c5086001c10000b2910f2815407106406541c6540001800640440e894401401007000c034043c00c5ca050706e0856142c071440917144010074a0035148400c106414402e030790a413040000c8069550742503031038000b401c2d00000c1907e41056120f1030301040e480b0b07060009200803e480d440144e2150721900d4060040074242e05149050340c0b42c08406440c5940001750315111542d45002400311030124140742c1e01401e06544041e41003034a002c030001d220901a4401e022007910b03818081002291024059244c00c01442c03058001103c8070000a00a809108110382462282c100103107020740440e090340c00c0c076 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 68556432 1250 68555182 68555213
    0x11a0f041806171f0c0e18100b03063a0506070207061e0318081206090c090f060c01061211090702030408030d0908070204090606090c02030403021813 66
    0x25102c04040080368002c00301095518007400141c041d01c80c0c00b0081c105400f06022450703140341e440d42e0b20b0707410b03c40c011305e83c4100b50310020340300c1c000041180d42d03214040c080a45020403032006102d0001658401d4809072401b40c6d100405083c0031181001102c0107451241ca40501c06140b0008005000501c10140301c1446e032003070001d890249401c0c0c0d0080e052001c80d83c015000e00024024a45543c45c4820f03000c400c0346190f0800180d2100c81d5201c00300461245c041c000e10303038000003c04070980821131800502c54001203c01500a50b58680801c1c2207004003000d098002c1010305000313119140802c05000c6a828000001035480d94030210402104000c00b001d07520855080040d60450803c4107903658010024001185803034a407101c0d143c0d485c071903c5480c10703040b662848a04c0800240c0c42c00c0302d0420740c0080c02442110710030308003000248940d10940020602d405850b1402d2030000c8152412290020008000010700c0a00701140c1a00200301c0c508003000d01d614000016152451003090 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 68557682 1250 68556432 68556479
    0xf0c1205010b010e120303060409170705100c0f020604030c0602160c090b09040c060f1701091a0f0f010c0203030f030903070506060405040b04080a091503150e011a0f04 74
    0x150842c40009480800140c2c42d1a009920510054001d842d0000c101d03900080d0a440001c2d9021542c18402d141e0000c41c580c0e5143c2e44400210b13a0b00703005c00002e01c0c0000d503c200c1c6c0e08100000c044a002d41d110ba00380e00080000d60007100c0080c01090058080403810750050034054902030400c1001c1c10912000d000440d810000e1807000e0180c80d440b032041020310380c0259600c06031810580c4030607462003218816801001050610303c5e0b0054400c0d0401004030640c080c80e10390a503103440703842c0701501441c03001d041e82c0015002000d031546051500c00c0900c00b0003a180c0320001c00c09500448869408403420307030b0548000c200906550380300c180118880e410030006162201d509140003405c004010384028400c82c20302c0e0900000c80c2d0503042007504964459421b607500c509500040e100450598800721950b002c02580c201043d4064001049041d1801d0f0722100094485418000188082c010410044003800785c464200e1008401041d0854905054a041a079184913405a801054001c0ba60 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 68558932 1250 68557682 68557691
    0x21201061d0103050601180b04050a0603051908090f0103090c030f0309080f0c01030b010c02090903030910110306010302090a09061409010b030f060f010e060301090212060307120f0c120501 83
    0x148240030140e400d007030421141c505215503d142c55880d44d0f9107040c050b01f1210b0780b01e420003440109069004035010300e4046e00a1155280c1400480018011440180c030310f4010040160110340c0c600d403014800d01ea001c1c8400341094055008d1100d207803070102c0703030340d040c50340d0364030f001d004903002c07100010066102d00e8200b40084002c0c54000c2401015611517542c5601c01540010485c10204842540480a10340015034002007801220004845140179401c00d4440301403001211303010009500c076110342c1c01241c5400020103101740884622071282c508510041c0003007074941d8820340081c00c142c880201660000c42d2a043c0c12801c03180c00c0e500480c20a80e0a0446a460f4185161024018042003140c0d03030542c5800089600308900040100344140c02e41c080740035441e80141d000001c40c900185c000e82c0c03a0740e107a80c03a01000b544030080304100ea000901c00114285400200001516460096140030050565444403940460301c41215160104c05003c10b000040b5046a04440d01031000403a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 68560182 1250 68558932 68558939
    0x2725030203060a020d1d0304060509060906030f0103020103110a080c0d0e0d0e0f01030501060f0804050f0102040e1005030c010909020c01020d0c0f030509010b180c0702030a030906031104030317090a02120106 91
    0x3c106c4006540d40049500503070240c10804a01009a40454402d0b0510701e9641400c04006105841000340d0554880c43c0841030041005180103040d050324401c1e00c0411187c54840b52101542c0125007883c0001031444002884080740c1602400680802c40c0c1d01003104190014064104224071468a00142d007101c103415540c0b6020007901040740b4207080811981d410700308000e100c4440110034606000e500d0001c54100b2208100920106444200840d1504c0d143d188281204c80151000700b8034071280d40380401c03d440e01050003500c030745050310341001452420a412001e50041a15040e00e55030912100c4024050f44c01018090759165036940c0b0109070025003e8212000544000c01d180c0c50100006482e8a840c001c2100c04007407141100082e83d80c038018207141d8850100000d40501a00300c10700c08054201204500340c40e142c0d14140136070009004c807030b003560081d80b001400007141c41d503100303594942044146400211210984003030701603c1d0045503101ca21501090020303992000c081 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 68561432 1250 68560182 68560207
    0x40207030c030e041505040203100b0408010f060b0c070501080c0705011407110105060105090402071b0e061804050c10021c050d0605060423061c052725030203060a02 73
    0x3c8140c00ca08460070010800a4081d0066141e20340c0641805180d0000120f9016005110010300806009010590f55521154a10b010300381c4122401c40c014280310b40407601511540603a441d481c5600700070141540380100441c0c222102070003890020300e08011040200d5420f01800b5408800310303031021030754101098014009105103484103c541d1411090090783eaa111007280e441000c21030b4003584585039410100b8103d24002d00c1c3ca030b800d80006200190f078405181c015403040004035031120300c01e2081c18013850280003c840041c2560422042c11841d460b100d0071500459605204803100c4c0c50104000710b40c204803100c000d801044c000300c1c0383c44280071140140c00c00b030001130f02d005d8206498001e45d11501da41c402c0135010200030700c034100c1410f0746030f02041e00c1c40a02c4902e4aa509c40c00d860034814000c28042e1078400d2102500c060112224088041c00c1d42a01170301d8000713124030805548020151024a00074000d821007402000015946c10002d00b805809a40001687e0f90280100c5 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 68562682 1250 68561432 68561447
    0x1c03020303040212151501090f08010603060e031309050c090409060f0f0b061209010212040f0201090f0b07021005090301020c0c24070b0a09020d111009080d0c060b040207030c03 78
    0x30820075074890804101c507042e810061071b8101c400100385c80b0703011007044010b9440b070101da042000c01c1e2030000c10008003100150002000c030b138001c250800c0890f854120003514dd00c514805031030400d001c40c504207e102c020ba40125404a403011585040540040015007034a14900095980c252078a4010440c8011442a81b621140b0b41504106402d00c40c408961103001e1100800b000c1c1070502c3c005003402a080d011698044404600d03101145080d240c260091310f00c08105a0010701620700128100c0c2d41148040d00b41c0b946214030341d05009140c0d00300140d19485511240c00c001082c04030b0b0400ea10240007420003284c040c0c024041140003107051102c0c1000161414021a607141580903161400c1003c540207560849040440750781e80030017a10203400c0d81140290009071002e41041401040c0b5401441c1c070804907614103000090000803101c41d41d0714001c100c1183c1080b9002007074980100007500c20769100f003502003145440c1c9400182240c200010a40224210b03124210405600040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 68563932 1250 68562682 68562709
    0x121113020d06081c08040f020409030207030c0905010f0308070c23091506030408030405010603020a031406090d020d030b01170a05060102121207080405031303050313050a0b07030302091c030203030402 88
    0x1041c40064104c00c0c49425000c1203601c0060220300b801140501900044100b034054000d8800d1000c103103185002036039098940700c113640200c01707850081500002030142c64100d516600188050703504545030014190710a0400304d5060390540400149418003450384e50400489082025484204006108400780b005040081440700b40340031440070b540360b9080d0385d0042e400450300d80e04e0740d5503860100e0061155400c080d600c00f818000c00030801180034180a080040719041d545103460355103055a0307070120a100708001d60401e4100401c030601c65480080300da50f05140090842c030581c403412240103070035103104020640312000c1203425601080601e000c4601e02c40c0d120720388502c01081c05107025002e400c15042084203400705003446002c000343e41001c400a4506c0b000c0c10355900d402c5603680c2c003401d881c40c06008100e034005420b14001e11000d044600c860034492400400769802c030025030051b400589e0100081000c1c0400030301c509d89860405109070021503036800c05004010b520b0710041e0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 68565182 1250 68563932 68563949
    0x50109090908120912031f090515040f0609020d090c0509041106031509090601260a060c0c080c010504021e0d060b03030c2b020303010b0301121113020d06 68
    0x30021001400020450300c3d00f200d0f0103400e207055290800050308244e50003a001c218480040107000c842800a054046150405a0401c00465540001c2c20540e0821102c0002403660300b8980300c081d05041d0131040c1000304580e00000c48075103c00c140d400700c4e000f04802c07504459903108181c041262041045d809094110307403040a61400369640002411a100224000d500100c0412010000110b0b01c0032408002000c0141a1401c440030f56a607140134482d400817901c0c410348180d84501c032150421346c02d020440243c41c130445191180c1000d042095810810001c4103001100400c419001511005801c48004501801e0500400c041d03a014180ca003001e085030440b400c15180e41d00308070801da0035400b02010482e07018000000307003140582d02003505680605842c421007003079040e1911420f4800000c441c0304004800e4822680c070702017406018807101c0c007000103000c40c50307070682030001242c030500c05060390840c40004a080308070034051410051360040b441141c0e01009002e030602802105 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 68566432 1250 68565182 68565191
    0x2004050312130303110a020409080c060604061a071e030c1109010f060e030c090a0e0601090c0f080c070501020f040806090a0c061d190e0a0501030b07050c010207050609030405010909 80
    0x10b500c541e01c00a55110090a000c40f041c00e0b5000030906200306032030701740c005008001b07076801c0d810b0480c115406112504c40c0b074040d05000a6182c9450b02c60903081d503640381e8201c40d151001100c440815400810260740d111545428650031a2404507449034603403080d0385103c4440d03940e103032401031680d0f0500058401c03810746d0018400c2044c241403074411150186802c400040d81a00800c0c20400c102281d140c00c50f03046d1040044808840d000604071400c10402c46d20b0326030361010914103c0c2e00380384240e000910203c91010303295102e001000c0d000302c2d06101042c41c01c92255140b5089a00c2607007180b0780b0302000f2804104030301044c0641c1e544004118090312201201398bc80c910b5060090003004180140b01c40710450b182c40007049808030600160a8040c04400b069410100e02003d105034145901140d00007205a0341c0c40c020207040f603910000001598a4103c015210358000001c2ca290380d6509200c21004201c04202c000c1c0640903450155645500b40390005050f07c0f09030b08a03100e018140b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 68567682 1250 68566432 68566447
    0x312070804050312180604050d020d020a02060301120c1206140606090d080d060b040905040b0601170103060b061614060105041a0607060608030301030501020301060314090c0d062004050312 83
    0x40f0844000410070307007000708150b81e62410491030303440f94140f115807440380a040208114001410049c0058190200c51110382c04910480e40c800c0510b40c0290440b800b0b01c01009401070800e004003039103100700d4011401c941c40d004040b200c2c050400081d100192544075009180a00c00500b54100400340c40442c50079236680c0c041021342080c0c2000420a4500040c04420340301c2c0396000ca005030070b18400d01da641d540e4614001c801741605480940311180500017043c1b07150700640c54058080400c102100041e032840c2c0b203110007401081da8007600a082004040e4401d4a00d0040e08074071846418180c2c0c8080d003810700c26252000503002140120718051340c0b01c10482d280440b880800c0320884415958603460316269001e4481caa010800520000c8000710410406401440c107842d0a0380d010030031418142065042d9070747c184e0b100e03509904851200a035508001c01c1e080c0354940501000314400c2c40750f103010040300c80306294840141d00c001c10244410703e01031100103295907510aa1500b030901 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 68568932 1250 68567682 68567693
    0xa06020a0b070e12010e060106020601030c03120c0b0c0304050709020a0504030605100e0f15030c0a0e0703060806070c050f030301080c010c031101021305100305010602030318070504020307020312070804 89
    0x1601009811080084005240c0612540c082d0310314100252840c4042c404c070440060180010042140e1070f80078076400805c20300d10000d04181200d40040c5001c07201c030b00e181c54640c10300d5007082982c0d0400c2012855003001c100d00307682e001d0155410800e015980d10781030a040d03040030342c60342200c0000707401002030010031071388201520141c80d001800081e403521101780d068040c287c103911a5001d00402c50070083c4801008644512418004001000030701500d0b0400d925007524240c1141d03c0900d2400502862100303442060f0b012181e410000342c103a03281d407070103850000c045030741030009408c540108041000070b11006400070703013440c015421035050010050310b2f45201911141000140c460340400d0500c20303920704c043c045120000715910841183e21810311a05801140c0c080c0e500903000d030010368824860309048403a6035000d0b40c25034451140b603440301c10f40f90740406811f1140038004206907680740300450140340190001c6555140031145c2c020b8445008010200748500c02080202180 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 68570182 1250 68568932 68568943
    0x3150e011703090d14120406080c0d0213090c0e0405040b040204021c0606031d0d0e040b030a1401050a060f060203040e0a0204080f0f060a0605030c131b0c0b060a0602 73
    0xc01d00a21520552500101149140a000c0402d44d1028001e4030748424001c10501c004015950300064a001c040d031015500114851403098100040011001a41c0f07100e400c0094a0000f4645002518014001208403c4d480d456000000469501d550321003402d500140850902c041c103840600c00d038945030300d500012100c0280064000c580010b901101d0840100c1c40c1390121103011000c100c0c880e11480020300400e0000764148601c02c0740805101e180000040309c40c21f02c1c2d2140d50711541e28403943c3c20700c006400200645a018411700b80c0c1d1000007005040704d589032009003800021a460004440406e54034545c0c0100b0070145409401d000140c1d0120031181030303d201c0420101151610034920700203201e15171016905009002c0200381000c00860400b090300e9442089440766220803000004440941c1300c1c0c1603140d800303c928800c0a090903414121140420a400903140040c543e5900020012140c6500040c018040c0d90303003000081800c207500180c0940d0526130040c1840e070041e50f0340 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 68571432 1250 68570182 68570189
    0x10170c03100b0307050a080d0206250c02030330010501050c0307120e060f0702091501023a020a0311010903080a1505040f0c170705040605070c051c0303150e01 70
    0xe0b80c440802d03039036a8508101c42c50041030003510500200d80d94880c2c450b220010310604600600908000c141035268101d031010003c11038507071500304a02d1880094490981d21042260140000c0c0504d00d02d100b140e0441c1c914403440c1c1c080784120010784005810007003405821190501c44240301c1d13501d42e20800410384100c590f000140b8200c14200102c02e992101404038903503070003040020305d41066800d4001501c0014800c1c0c480180c19200c0c0c0881102c814120202540164000020444101031038032035039070050f0741e08500b0001c4904079244141e805515030190000759220300c40510805901002c0000208001d41c02089151070350707a030080400341d010701451480c544405040011805090030000108401801048540410617404024108010740364000c2a0300c0010060304440c0c16000500c00c42d0259503041c5410b05240e401e031201d8101c0e10b400c0c0d031400c2da000c0002c24603840e10354915001d04070400014042e030350140b030001c1c207441510028080360b40d031003a0100100c0c0600328466064 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 68572682 1250 68571432 68571463
    0x60a06050f0d0b0d080d05070c02220b04020d050108160305150603011b0f0306080303010b0d050414010e0a0c06030b13020c010e03070b040507050117040303090c03080310170c03 78
    0x8580030070b00702e04050950b1a4070207910201c101d00b10010002450010b010403000d06109000c50346d80d00400351140f1030a0705011b508201808040c0314142150f5000b0f254040d02582d0006090745250b020608a800168400280d19620001404101070070083c501c011071075200517200d40c50a607070303840352607101500d02240b45103055808601e80307540c2900226840c0d00c0601c64856221140710008040a06c1c4601841c046031600307001007490794012003244d0580c4c400b064401e20341054107140130001e10008005039444c0310b1070f049140b1504000c0c00f40c4100300c00c10000829818985061141100d04c03554414420305242aa101c00d940e260a9817086403503550380c00044e20b4840c04170304079001d0309c03540061441e0ba001c0001c9000c20011000c0380d503401207004004540c0441e80742c40054803652085d11403d220684524006800644039400030303600c4910507000c61039040c0ea0707603130350740c600d90025140600c15002d0520b040c0300c80c4080c1802181e481110000900c0e01030b940d030010940f90700c0b00010840c01c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 68573932 1250 68572682 68572687
    0x712120c0206040b03040303150b04050306010b03040f050a030f0e0406150c02030f070902190302041d041b08010906050a0614062d0c0c030a1109090a1b050306060a06050f 75
    0xd55450350b0070303a0004d20310a5883c0780d81c0d10b0240f400800030800e59041100c8032154500c0840c0c1c42c802c0c10213490948202400820b54de900780468003505400c024001c0300d40742040c00c04900001d100b440354099242c82034913018040301c17100801405d010300869105000318070f0f11b1000c011010303910318801864811070400103680c124900200b8104040c0400c42002440f0301e000010701a1307100e034000c085e0340c0b41d42440e101010000e000114203903c6944038000380c680d1a041c5401009090001080c0c000e407180c0c242100d030090810701804074217029440040706941d6a180e040c240041030294903401400e4800400c211814900141054080c807508140100c00204960060300034502480204140346031300000005400200740441d640405181070440c0150700e20100c403814001468000c0310f60103403440c00750203407038010300c1443d1000904110442c4140980c480214040144140009400b50101e084d254101410f26103819000382c801400780030400400c2121641c8030098440142c04401c4159 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 68575182 1250 68573932 68573957
    0x302070f02060c0c060315190803040b0a02030c010c05070b0a0c080a0b04060801090c0f0e0f04030302070201051603030605210a030309030c08030a0507110c010e041e0518071212 78
    0x91504c404001001d0b04a00c0003c1804a0041d207962002d22087d800c603020350b9250010300349803562603100e209085a641c1f05000520918442e0400342840c2d044520403241090100d1604030301752542d0714051004618001011030030320150441e500e0340f01064810501003c01510f1000b09001402002c240206589040070840d955407500107100910a4400900c094003942c180549440182d1141540005800d80c2c0042d1085044118a20402c03501a4850340c550300d585055000e980f10400032410044100072948070302e4448180608802d00a0341c1c00280c21341090140030103a80b4900c40b2211420000384210024500016901c03495541440d0100f50340c1d03c103180a90b07074801c13052401040e003900413080105c00764460344001d00c9400a951000581000c500720240c50340326100740fa500140b01414603907140e0925030040180d100085803603180c00c460301e40c2d900045880a4903412000341101306104000b00042144202400303158540341004070f515900d800a10160465020038480164000c1 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 68576432 1250 68575182 68575207
    0x210030e01050103230604031409061b01050a0b060708040902070606120308060a0e011202090712020a112e0506040204090c23040602030418090206040803190302070f0206 75
    0x1a104100c1a40240829612480d05001401c03c19005200000041056281c8010005807990060381c2607100d01d8100d211a0050b000340303511000400c1e403c4001000446c041c0d1041c0c0103020845e00c9514000201d80c2845c4000d102583e6040000d03e07c11a02400800b010403c10340440b0704a0302022001aa19611031910030041c09841c3c0c0000c01c030b50b43e401d940209164004014521980085500742d4606440d400c144185c1c48007070095034000f4805042150060400c1801140c108d4810304000120104882601f0182e90200902100040d40e0024403285c1030010800051440b949854400c403441007400003c51041601d264106003c0d2514080b80007070311140c0c11107000d0311700c0c50b0342801441c02d288400b500d8070400712200b003801c4c09030b0651000d44541c09800e46e4182e54184cbe015625091501c2445c1c020010380008500301541d0794604980140d98042c0100000d104e020003458070760480e0007403100c04090345212082414010031000c03001403808181034403129030403901c807621480c070103949 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 68577682 1250 68576432 68576441
    0x1050402130b13030c1e0b0304030c03030c02010b03190627080a2105010305060a05060907050a140a020619050c0a030e0c0d11040c0318020d050a0803010303080115030207030903021003 81
    0x103030017420002d0b80440e0065981040061024100c951048115515000f00b10244402c0b203000d030008004481c82800203129401c11010b0310624030001c82c089800700002400d040e98110b2500380b054541142e081001041d0061f01d020b1030394220750000088210b62203070022880118014010900080c0e42040075000310b04130310504c403104e0502a81c02e42c00c018440d00420080c0403e840b140300703e070300049210209010b03091241201901801c00c1e601e44040075921074000010360000c0c0040c1c415204050444400070341040c4034181c5c0103082c213081046811b800c0c8111074460b03003541400c0200b0000039070105003c48004001525001499103080801c0700d082c03204014010740e10070500703c821001d0000801d13502d04860f000310317010028810f5400f015000c070384040f006041c1800310b0003042c01c054a000e01041507210302030010388541d000159038024940e40260402c41c0455070304130041c4019081007030340c8003100743c441c18214548910364801078202e00461000a2040800c030003060703107091180c2c02c13 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 68578932 1250 68577682 68577689
    0x402090f09070906060e15090d03050903010b090f06120d0504060c0c0503010c03060905010f0e04110d020303070501020a090b0c25120302010f0507090509010608040602190c02010801050402130b13 86
    0x1010403003d516505e0081070840035071030b42d5101d0b8001c9983c0000703e0306043e0480380b51003001400c14a80380d001c2e54007a5000d401c15500d1503455580c882082c807054403280501031099001040411040c6400801c005288500c0241c68400741d0191600d015242e40003022282a1030306814982440d0700b061410711204906c9030400c0e5095400d00c94040788040c0c054101e501603480c41e00f814032681e03807540000300b03888029120f0041a003040303501080c0491a11111808211401707400c0060218264001c245958400b81e41194543c0d030006004880644c0b108080020780005150a8a01000c54011643c2c0308000d03a40010301c4600c40d140080c00103114001c84004103503040d2450134898460078013a0092080c2100c2d00346071424980003440d0f40348564008419544001d1141c00640d0901c5012114a04001d104175000c039400c220b50640d107024800c46264240141d82c0d803800b80083d52000500c07289042e4002030081e030043c01901a055020740c0c208040e9072080c110251a041401d84030341900304140e0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 68580182 1250 68578932 68578949
    0x4080906041d1014010e01050c0106030f03051801080105091602010605030d030204030506060a3b0c0316021b100e0409060e07060906020703021e030105070e030c03060402090f0907 79
    0x8024181180b450303611940700c1c900b5807010f4041959198402036503c5554a070040c00074442081030800ca6005d0809040c02d50280000068038546035568580021040380c0c0560102d0000b1039845204401d855800d903200900f841e01d801c071545850003181007030902500c0d40880c140300e0348a000d01e580c402d6008200030040101140d6a440003032001030000c1d8880c3c00103075018007800c80011080d0926030100300c211056a05112407480c518040d00950364480040203044043c0c02c0e01081c41c103100c00025901034005401d81a42c2c0c3c0c20400650044e5060340e000e40402d40d003000c0c40b5580260301c8001c0c003412684083d200034440c02d400030350458142d108103140369400ba00d09581d40c3d042c0b0040d54801d140420300b1100b100d1010b0740b900010748520344907202e02d00c01640642410700050620041182c40b542e65284e8007609121404000f03400d45100304c41c11000507804110f40812450f0800c400c284400c1f06070060f01d404d042640110700044c0c0b00801591440c0a40000700d400c50340c042007118000d04116 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 68581432 1250 68580182 68580209
    0x140d090609020a0e06040b0102010902060909041b0311040b031915020405120a051e0a06020901030f09060c02012421051e06010f23030f0a050106030204110408060408090604 76
    0x300d0800d0143d084c00d856080c09180303040d07050030765035005105145040b03230010415130405151808000c0c150b88020011035540c01d80c500d00e1540c032105c800300c0c00301440c810070f50712129040d540140700445140c0741c85240f0a91100c6885c401d10302894080b04522a0400308108081c0c0000d001e80d00030340302d41e40c4490340044914902c0d00c00d07413102007100b82c030051044013610305d00507004645202d502e218080ca020a90803415201e40080d50075801080340d440181004504103040724010421a0450311061300c041c0e8076026134890a617070a12456160a20440e00400e100c01c1c2e103803060714400700a000e103144c0007403000c00d0703589442c4110051070f4940e907001088510b42543c00100030318440010348140c0c2148501800400d1614481c80d400060b103060205038001440b15140a2a1405c07a400b6419018004e140d02c4000c1c4840500c41102c1c003501440001c030301d071842e5206000844088000c10181503000340401d118944022440a40040d040543c540d1200580c0780020700b50700c9190f010041c00c4c03174031 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 68582682 1250 68581432 68581439
    0x30605010513020f0307050706060e1305060a020a020c0f04110705100506060a080604090c08100c020601081912030b1c030f0801030b0613090507120c06140d090609020a 74
    0x15049a41603880980761030b001c800e00881c401c8180c0c0200040c8011300d880c02d00000314064130420183c404030b0b001d0a804036909965a040383d686040544440c568455903203165001c1c4401000850b410807c0000d0031440e21601e00370094032100301000f00e903c0f458854110003215a5290422507850340c002038004e17551041468425507600d80e0220744d2107160b0801001440c1450514103450099295403102400c075621041040006d000c0c2d4082220b1700e1200080200e80c00c401008228125541144001101210b031100a483e2000c1640001900e92242c940381201c2d060414001c2411a4411348100712800000302c241c01070691800900d4001140e0341703c142012120341c04c0402c909010b5101d00d040a4aa4102110381480902000e0054031035400424610f092200a400c50304004140018940c03503140d0720780f8203010203036001e02030780d5202098a0080c0402d82c45094020591820444002c1c9103124070700318640200d07109001c04950326012402030254503004000340da61b004218103c40c544 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 68583932 1250 68582682 68582693
    0x7030207080f0d022413050a06050405060a060f1211060c0d0206101d041106071a150105030103030807050307050d0c030507030e19140a02030d050c010f1e0c110703 72
    0xc80440051144c400c1d1700781d540e0400020070041e00103100f007035281e655840c0e91040b56582112000c0302c0d03d00c154056900800c641d0702c24a40200d120300003409907070a01c2643c0c8401e40e200d80d000300080c144941010041c61000c1405600b06c1075100c0441c40e074650350100061040c0c0150b808499150040854141005a0201e4194864091b038282e030030704e607611013600003501e8a10104c0d282c0c0003240328001c07501050825903038801151004100510b05429591683d031403030351546400740801c45040c00d112030b03c22135207021484c8200c00c0c604641190b141d514020400c3c50050300701d1044c8940080800c42c11032203503040364042e140d800c800b4410303103001d20b50080c018841190014002481c3c0307002e20740483c0b4082081c0b108113269408101441c40a070303d50381414001e0b200700405604c0307051403100c0185c4040c4800048900704e51102034403080d0b000030b01400d40308d085450082d40e0303180c000b040380002442542c0c002c00300c40030320300060003040501064955440c5180001d82c0c621559000108111 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 68585182 1250 68583932 68583943
    0x70e0a0207030306140d1416080105041202010507021c05070c06081f080d121401030302030d0c090501090303050901110f01090314070b010b071104020f0c0c0307140607030207080f 79
    0x900c256004c0107800d58561003030310000c400401c840e9001e103441400c03202145c000e000c01180a0000c8094800c0b019280d060100e40e00c5180e400104103035110300070802403240c07122040311000c140c1d000900071841c04000082d00c45000101c40402e000301442e45046540c49601940e1050b980111141a041d840741d50203407411000300c400d044007801e5009100181c030b00040c0006d04941400004202c038007418841501c2d00540c0701e0544202030f544e0325a1070542c400d2810780034001e50094010f036a03211420b180100c01d440a600c000c0c0b0910900d160300b042541d85c07080c407080840750036140c05030b124508035004941c00420400d404109201c2c4000b526810401984641b001ca07100303455035001d192007100035030381500803000702600c8101800300402c00e00c81c0c441c0050411a20600380c40013102070000024080703030407641080303008180200d11100404401c03c0408440f5008078003c09a0301d03d0030049080d030385030b64607a0078003401000c116181054001c1040002030181c6800380c40102c000c0c10304150b41c07032 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 68586432 1250 68585182 68585197
    0x703080412020703240209030102040e01030c090b0603061309020a15020d0c0b160908070e070806040b130e010603020405090a03020d1403040f020d020402030f040b0105010e0904060e070e0a02 84
    0x7040c10012030329801e40000b8032401141c0e404007007468145500c110b01c0300b0303104509100e58103294080001445682d42840204041d20910303219081e00c0d410760400200c600101d4101c00600351070004440c00701c0c0d40c1d02c000c0c0c0b84e2010048810007604400b04046601400d0040c0f0000e4102c0c00e05440450b645841c10b007070341c250000319800ca07503a480500500700c2d41c8001080024006a040d50089005850b9600314401ea0a0b004e00342514541d60360381e009460b002c0e26034006001c0c1d5156074148101550302c00780864101d0740495040c0801e054080024030081d80079807005004a590308000b0346010400e4018034001e5800030820009850241c6449444001c61202100140141204038175140c1c02540159416074a071503009041d56030700e0382c400001380700c010380a0f6032203c1c000c0200401a41c3c0d50000b14420341d2181c240180700d0805241012110340c0681101d4140174147e4418001621141100350f1b0080c0c000c480800c80d11003100184d41009665007007600000010010000303c40c1c1140c00420303c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 68587682 1250 68586432 68586443
    0xf0605070c03080a050601020a140705090c07052a040213080606060406020618100f1a01020c031504020f0603010602030c070504050601090b0a0905030f010e071e051e0607030804 78
    0x95620420215200d40050748010041a45540032036111003403030b800306a00400600403203502040b140c584800c105010a00603000b80c0c40304c00140071500b010000250442444116241000c0207541c403140c88513154040342a81001c44244001030030052900316600b10405042107540300520906000c40d85018080c0303c405220310001b00d40903040c0207044504407080f50b0701905142d114141c0c20070300303018402c241c401039100745040359802230306521030154200403030b0038002000c0350300000344011441ca198100f81550001c43e0850b03e00e480201e0a4a0000606501080aa0f5661000840c031000c04080141c2140000c400451a00d40000c020413010300c807030701111034840d592001c12098400464030180002c6041000b0048415000003034072800985040c1030003940d40300c40202e80b030590345420159081c1c0d1501c0342d420f0080000d00c894000390510b448141c9180707211000980c48a41c0a10603d800360340c241c03821480b52084404085030300f10004040c540d4a205c40d0500a01c1c03e40141c6c3d00703491 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 68588932 1250 68587682 68587691
    0xc030204090605120d080a0b190302030c01090e13051e0a0215090607080d0b04050f0601140f040506090109080a230615090a23010906080706121503020d0f06 69
    0x5081c81e110b0400a95407003458005c0c03844240c071140854002c0701c0505a030804980b42c804000c0d0554030b034040d000d2036100440310911b107240f4500406103800080c1c0500c0381489101d03807041c080c1080c00680c0543c41524010302c41322484042c070307202d031400071202001c4804402c200706440904e0004a4600903c9008885c0c0e002e180030500900d9007580700314403000e58072001c104901800104004040c01491001c0d400001b13501d14000b0214003501c104030354185840d00e80700e040141541e00001300c100c0c004c000d03401ca90f0603c0d00741c2040901612882c000c0074401c802c0402d420240da88503c40c0d0a001e40003030815a0b4950310607142a1444400c141044a11400303c604125507618000400510071024800c8803104100d8100a0101210010300481007140d140d04400d0481500b6610f2200384c11040760115515600d03000841040384c040d5000080e058100207002c128003a1703c072034042c254800d903100005011591204012a68901d41c0c002900882d41d54680c100780004144644c03140790081e0402d00 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 68590182 1250 68588932 68588939
    0x4050907050a1502030414012a0b090a0f08220603020a0215090d110c040204080c10030e101e050a090303050601031509150302031c0e06040302060a210c0302040906 72
    0x8072600d65a1001c3c0340141d10030300040090544400441b031440d40306041035101d4402c044140c1034404203400704030200007118140202001458801c40e988003a124018001c00344e1243d035051a01c051015000e00960800300e80004025440c2d0060b0058011004441000c181d81d1100a406500112039460140c0609000c1401d5884124010341c0f0914010024010304608114140c0e450810f0715542c0c1c0041c0708401030300d0069221440188080c0c03483c0b40c000d100084c565810000c0d4105c18115041c00c16040070031011110000203620861060002d401040e0846c3d40110407140c20950103140040d90300745070610410300300303d502540b00240695010b0000717a44140c01502903960075014801d511152141c1005414030540c0248007007402e1010744c102096407900085e113040c50070386560528030f4084110981040e0031140100c40301d00c0039602c1500780340c40c5d50006203107800703551503003800d0108260385400d60310403a94255240d030780266402c019074000d0f080c00070025089401148686803501c0d0010 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 68591432 1250 68590182 68590199
    0x120a0908060a0606171513020d060801060e06090403050706090b0105030d0e010f0c020a180e160302030307020f04140126010509030924030a0207021503040201080612030904050907050a 81
    0x8078240c910b0342c0c940e900036030201002080002001040300c10408100e6003050411f6949000343c0c0e10304003425a0243c2c0b92102c01e0f4401c030449010340d10590150f0326000042080d1a602811160702800440e01c2204550b11801e0540f124491101d00400c854030f001404007c020220040506840041d81114450f03040d403c000e44280840b8584140030541580d90783c2d003018811018503c10301c1c4007424840e0800d035036100e102120010030241036842c0380c40309001494150100301422511480043e648100c40c9540c010070303100e100f540c0c0040e010307800f44106e5080f0ba40700c68020010010031686020700c03079a5120714401c2d02d8452446a0300c0160824501210000c0050040e240100c40c84800b071858007070640200400c0c1801140008512004001441e81c808500409548200e40320400966501510700c100044088001c0e481c0030b445600307001340070141c0d911550b207960003042540e49100c03412130080080e245008cd0166642d011b030401040100403000410150202c07501030742c94048154503240700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 68592682 1250 68591432 68591441
    0x15180b090d080a14010510020a050105190b0108040c0303030506040b0909010f0c030b01050f0a0e0909010f0b0607080706110c1b0a0503060105030a0809130212041b150e03120a0908060a 81
    0x40440d50f480c0413006000713620b0b0000c0d0201310000d40d0700445800340502d9a0701070030f558086401200d90704281460800768a940c3c040c2902000007440e000c03074540303070903500c0307150b0b51003103000246c10990340c0c80010f00c0544440d44010003100c0d0042100105103456a00e090182a2000d0160107443c144140078900c10b020f40543c1032003800585410703040c080840d9190280f0703000740d507201d41080380b071001400380c17501d8060741940217200604c00401e01c2c1e85034002d0b10302600c1000d661980507078420450503000c03079503d4003900e104560020000c192040c44201c2c0341418000d00e105101c41c0d009844045c1000c035440030110f284a8410b8071344000c034aa60b0410107448031400d200301505034101b480395400003000e040041c07004e010000c0200888001303074008407040b60400f80c3c5130212011150180024084c01710507040b0400009d9a40640d83c505005084514049844d5440305000c0e402c50f02d180c440d501840712420b490500b420700d035102c81d10042c00802e05582803041810700d0042c0740208044d078009015 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 68593932 1250 68592682 68592701
    0xb071115090906041b051306021501030206070c090501120b06040c020a021c1b06030f0b01140c03040e16080109180308070c0209010b0901030608010915180b090d080a 73
    0x41c10201c01c5401d100003680014912076006903030f00d10a0750030035840d0a14010500050b0303203860300e81c8810f4107000ca040f00c0c0b64100d8001e41d03010704211108045059284c40c15603074103540c002e44604d5103140602003148103400845102d8100030003c01c4007503003240c0c6000c01900501d01418291500744c1400102c1c0da290b4088401038211091407405402c02c40c6104d41004502c01c480f0722001c800c0d8603043c034094880441e0600d030032103402d420040c00364540501c070300d00101039a040054000e0310001130400d0a02045007040c1d04e00c04102d901d540b1700c0600c10b4900810360b4801c20f01c2c2030b2801500180c2c011200640c100c0119020300008a4041c420b4440c005c0a48002407824024500c1c035102504c1c08200204070780c0030001d1024901005840b1040d00c00c1c028642c107180f16890b0090030001406407145a0080f40d10383e80342a6444010800322840b00ca0107036000c01d40040c3c000041c021036050140d600340d01511043c030390014440c800200140c080300c461100e6807107048649500d445803080e02c24807070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 68595182 1250 68593932 68593969
    0x50c0c040902030f03040905040312051003060e10020d06030507080303010303050f180d0b0703051605030103060b06130609051c0f060507050d060806010305100c090905090a020a0b0711 81
    0x90550024241075000a400500007021500e444160540c29840c40d8455040005000e8a170f0050008049d04141c804800117608401841a0300d8920600310391001584009400191503c90030304040b0414441c032143d014240800390f51b60103030440e600016101601c001c131010b200d80900000c0120010082c3c9042c0c1c3d070725a4510b407514401302301019243c6c102c1820b010158039101c034910104c0c6c0e0307245814002d1a1144003035803414501101c010f02285c80c010032607007603045c0403c4001c0b05c0300c0d8030400b2603064a901000c0050480c0d468000f0400c927000d6500c2010b41120b00030030101c2e0141d000b08100045a40480e107151201c419078101d103101c030701c0901c4000d0400d481d810b407500009046401c900e5010486203011400e203481c0301c2e08542030719041d520090141d00500d0042c014000305000000030170004170f00610884c030b1540d20040914006100d4444480c2c1d0759404074494003c00e1000c180c1a80d0000c003010354140e11104540340301c0e8407204088500d1040e107400c000250504100f40324500200c80c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 68596432 1250 68595182 68595193
    0x816050a240509030705060301090f0b06040605090d05010b1203030405060702120f0a0201090c12031202030f01031b0e040c05030c0409150b01030207080301060504030b07030504050714270610050c 86
    0x81100b980c0c103070021502c199140c0035140e004a03050b00d8690186000300481140450031b80181e6241c3e008854010b400c050080c101040140081c0e42c120302200d241240903103d003e013070f040d80e09040340104106c0303003a180d2120100d4880c19070444000041d41c0a20b0266064651035142d02d4000d0f41e980d030081241401220b01170003440749400b04a0040c0221200c03500000c03072410410384c0e441d05100704c2904074517015100c828210061507807115a4100820134940b045203182091000426103540500c0300401c0500c0340009040c402000c0306411000380101d94400640e401d02e440e220403c401031b40141c074000d215603215038884d850a40203b164064101407d0141c03141c00150782c4004d42840403849050540800900001900c118025802082681c5d110341d00c90b421441c1c410201b640103841c038402c140c184001d00c80450303000314144040b18509036690b0305140c00c40d408a640514040d41021106004000f038001c20502c44040d18801c0c14100d900c44800038034804d090702c66005d10380c40c050340c130ba102 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 68597682 1250 68596432 68596499
    0x906020d020c0918120409140606031605120a0204090e2b03110403061428020901030906020307020705010e01031a04020a0905150909060a0b1606060816050a 69
    0x2243d00d03d800c04030460009241e03c05020466140000d42019402c0c403e400140810000c0c07401c1c420170242d52000080e080ca09c0c00c200e0002131031030002030900294a00c1024054003814000d400301d40e500c044100107401d0502d080440703c4001d400c28407445a40f1820110350161400020035010f10820000e45800100c110040c4000c50190f044400001419900d110906442c41001c0c0500001c510070030b0041801c00c040305c040020948090460720000200d60310300c040342c08192031110f0a9020700d4000580328030900300124041e02040e60b010b04020302c00001d0000c05540454088255102a29448044440e041c0110100c031070440360005022001c0540c01c1c228901a0020000c0d4031051400e07040403511400002c08900c4d14009400b41001d000400b9859820104904c03544034908440b00c22845207001d50701c000d50b100d08060913200081405c2d028040101962016003e040044200c4240c002d081e0f86800f2102400e0161610902c416600081c42d184c051448558101044102c3d0b03100202c6c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 68598932 1250 68597682 68597689
    0x705060405031e1e06010f0b04060c06021804050405010e07230108060607050f0f01060b040303050307081009051905090309210307060513020127050f04140a050402010906020d020c 79
    0x1620704001c40301d80200a2007002003a100d04c146400b0038210009004607526040b0b0803011903c165201e4242c1c2d16003840100042504164a1102c1603003011015070382d402c2d000c0443c0b5014000c0d801c0385034418907000500c410b128055100300380031035082c4104c401e91b64a41c800c000c0b11120703010b0b1581884881c45201031a55214940c12900300310007801c281d040c1482d41e074900c4d044c82c40b918101c1c10715034040300281d0301081c03090240301c0007482188030301440d15003143c03001059407200600340d405200341e035030114010b01400200400106100c1d941000141060303150403a00d070340742c0740301034903014201004585603000200494461070b100030081c110b061003c0303c01d2141c1d2003000c1c04d9840f40d404107105080205607940100c0e849982200343c8030a4a891a100151a440050014900594002540102d8000042c0306801a10070071030303c030440c241c11080044d0140904460025005407200d040c060100c0b100d41060340514400d0700c8029045803192412603840f01c2c0c480b19040160b0101e51080564107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 68600182 1250 68598932 68598973
    0x60c0f0a0909090b07180302030a03030e0f0f010501141f0c1403031302010807110c220204140f12060a0c0c02030a0b070206010b0903100b010c170c070506040503 71
    0x51190500c0c16401c2d5503110100c04a540c03c1a041e51050240000c01ca01c8560200c000700c0c2e00a0804520440b250454000c2562684006c0c0001c040c5a46e40740c00c80c0d11254100030505d03c94a18004644a004a500015020f0301081c8201328107010b8402119000385410150014101500c25040c044060007000480381804d00600980b4141090700038002401010f100440c802c020101011a051110b440010301031270008004004000b49201c3c4400c100d540130410303000c4072004640365000c1e4075080b42c51448460340704032001d4420b840002d00080c41d050390038030244010340442d0b802150280d6030040c0a1808502401d01c1000d802c01400500d5140d2140d1000c41c0303504d03030382c6400f03105216144e010030300d0303c1800d840548000000780200100c0d9507040143c0c601421070b01c17540074100f0904002190340c1e2440304444c54003c4e91100d661008603407280400005041d0424403618583d101d90410101d80d52004078000c016005034500498641000821501140c8005c2c000348003094000d0518050103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 68601432 1250 68600182 68600197
    0x9020d060c14030f01050109090c0e01030c0e0a0311040c03060b1e040e0727211502041203030f0908030408031b0a02030d0e01060302030c130b0d030e030c03060c0f 72
    0x2482d00e1801c072520760300c800034610035400310343c0c52805541030800240038507980b5401720381502e04002c21000344a81c852802180c0700e20a08022980300b91480c0c058502c1154001e20039007214800100106020301c5c1481065602c900f03843c20007905203100c07001c4081c0e6070140178a030441a03007041440780c0d07010340b5018214050003041d102030a1a88450540304001001e580400c0001d9151401c0c160300e4130040420340d07000d91130545a4030860714140c03a0702d013401c100b10b00805511350030516110070300c03054401d41002080d075000110b54482e1141c101e02c3c4000100708007540000e19200c0e6104420700c0354030500c440c05401085e001d0031541c03596200c01c040d43c0003d10581030030b012048080c51200c4204060001000507030040c54581101214800803184601428040d9a042100801c0980c8012800c080811021341e588003201101306c0041000e0440d1000b150b410605c0a507540e030070f0540c085482070005070102d00740e0344141324010805035520401c1e11500030081d030030844941e01e2008940144480b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 68602682 1250 68601432 68601437
    0x20d083709170102130308030105010314061c02150d0c0206090a0507120201020109060e060612010212150307120b04140303071d1306030f0b160507060b0a05060a020114070309020d060c 81
    0x103101da004e0101171041c4050748129800c0d800400140015071301401000c01d03c2ca010340c0021854504900011007171042024409443c00559a040c0e065448044ac0811000c0500910319583d100300e00180000b0103031441c00740014061180860115940481c01002864010009100c068100218000a040c409800301e056650f144048000502039024032281072401801a207518a000401c0c855081981c24100746140d104110405c200c44a10805a81014a20420481c1c103079030000840d05d031106a400481c41d0b803c400740002c0803c410f440c0001c0c4541d102c0d0400e07609141e4000e511303554901043d038026003c5410a04079442404c038840d4141501c650081210740307500c3d50304a00008031071003504140c45d241c0944503e0000d1000c1001455007107044d40380c00a04e5003900c80d9008207107000e62400245456110311000c420388c1d448003280c80107840c00800ca169030700c1c40164064000c0100c05000d2031500d809000080f8464028031903010b6140c1c019201541450307041c0d440c1d600030203544180c5400e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 68603932 1250 68602682 68602687
    0x306091008060405100b060c031c090f050604020f0a080a110a1d0405010c020a030219020d12030203070207230909030d02030711010b030607050412020d083709170102 73
    0x4007403070300300401402540580090720781c42903880c44032402d4817101c904050048104000c0c10b0482c00c030010448041407048500b01201c2940044520090020303041d010303000c01e40b003001200600c403011900d0341c09944203c0303030581091000c2061103c8098a4880e800c000e80042d4203980100e1003244821242d11340042c0030014403607d8900090301614404446400a8102010001080001d2103090580e40c418001042c0108031550020350b2000b4000e40d0050202c1c90004280840d110f458000c140300340d20400d40710520585520080094104895203401813007502800500c001c070100d500304180b543d9020402c6986400740501a400f2400740018256100420280710040054409140291031640d1011100c0d07890152960035202e49000e024800d0300300364240315645400a080750b003142c02444040c440c441d50b070700018820409010b0080d040c58000100b042010701c4c403c04031070344200106c0f9040c401804440c1104400100369034220042690103100f0300c0b4444450b0801c0c2070800b81d2000151 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 68605182 1250 68603932 68603939
    0x609060105031f14010206010b1306120204090f1e050403021002090a031a0108070b03071b02010e0a030309150311070201080912070b150405062407020901030803010306110f03060910 80
    0x2c2c0d03c0c034210380c090f03050384100242d10581d5603410720205004000f50144d86007001001801d501880460788074000034004a084041c0f070070b41050301038070f00a1800b6442000207a01d58803241025149082921101c040d0301e130a98500c0044a210350b50055425900800ca00206000b07400025480310f041c4903071007400e07108000000b9460719907c82200c0c1c5140e4104009500d440c05043c501410781c0c1003001c4410381801006100740c0d120040044040042d00024070901090005032000d0b4001c13100d0540150030800d01000303145e00400e2904c120342100000d40c403108401502107044509040c074982c482081007000c13801540c07041c00155040703178554081e5460507008001c2008a58403004084074a5a00e50003000350b0708229450150002d40305860600036407914800141c55460001e130074400080d000d04d00b252550714184203a800d440d074041c00c001e0083d41c4900304528550070920088460031f003000c0e6a0703c051149141901d0040018948031429512044100f0410510042242c80749031036051000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 68606432 1250 68605182 68605231
    0x703020306010315030f050d0206040b060603060a0915031202070f0b0c010e060a0509011404150e030d0c0203070b15060706050402040b150c0f0304080a0b061f0906030b09060906010503 81
    0x42c2d00a500c0f80c071981b0400c1d0058940300e424a08000c1c1148203541200081002080c85400c1c07050340820f003168500d80c0c1c0e69403030001a0840e001c0e600114981032500705800f00315120b02c4001d809407401810311100c41080440b041b0f945600341d01031845c642c5400c49041003003c0300d50020308020202e820001c80c1c2500c28403501071078004210b4001d5009903d8006008022400303104005000031280c0d2a01c0003031600340c6070200708810031603034900c02941d66422245016014002d44038441080c0038144068045402c000b950307908272540c2610026005c0000c00c440741002013810340803100141c101824034885841d181d0007080000d0041c0d8110b6180c0c041105d182c2d444203031780301060400388051a160b030741140441d03107400340d0312044144643c41000203006001300026240d40d206d9110b0038500c0240d50350404100d4540d4682010342c00c51000b00c090940b500e401525034002c3c0d038403513502080818039100c2049035601c03041d00d00d9a0032803445408194594420b80056510200c038581e142c002d024100910f = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 68607682 1250 68606432 68606471
    0x7050603190e0d03110906041502010914070906090b010c1502070c0e01090c0201050f0a0902030f0d050a021507051603020a0b0a02030105130207050607030905191209051807030203060103 82
    0x2c1ca0040d00f180d050b001c080d6406105162040c481d04d4007035814804a031012960314403440c020300e40800070035000704d80428400d4200c010320f1580011191421000911580d80d16103450081d003410508040c000b00d00c540c007610a10340c140b070b01603442820068041c3c4611040c0400c3e03600319140e8640800200000c42c600008510090500c4408007071250302d040c10023011034003c90155002c59040406015902106101c0c198111841610000f9108942d1000a03c1c2021a01205100e401002c04102800d0b401074058030001c842c540031b036010b450919403d1a00707d40c04507092004100284038141c03403110810785404806211b40120795602013641c50340064140d00302c81c0d60400580020041c0098244100c0c01018036419950640c2448001d030b42e000d480e8680103006000300340d07881c5505024024204100c0c55210078031580c5418a004600301440c80c1c44c1240e8240c2c0108000d5807001503a41020010310121130188090380340c0c143c0b55a403003100603500182c5554101501c404c084264a50200103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 68608932 1250 68607682 68607701
    0x304020a09180201030c0f0c030305060a0314060a0b030d0c080d020c0129030a020f060d0902120a02041d1b011e050d1512031101090606060c0c170705060319 69
    0xc840d900a0101d10005064a00360306e03420301003280440301e044031145c006489007007050b45402d0102d443c0da111001704030b80c488a0f6101070455400d44046a04100c80451020300030050f4600038040310f01100305040d55400102c0342d0384000b510343e500c81004100c500e009410780d80ca45800140c41d010f0070b020740c00d0a4801803100150344c0d001584281103848240c20b21200d1f114425405001c010007250001240212525103140c0100000110302c2d144442031b500c50150315078010868013200c10040b4099035a0714000d1400c900a80c84d000d00e620000130524141c054610100c002021200c408901e820040c84074240c845043c482039040141c0006450008607003201055035690b5100c0c1e0f5810908020364811017010620302c40b203401c041c088107450035441d82c016501030608410000420f550f250050115102c00762021346407450105442c0c0e401040420940d00544145011342d03210b115200c8811524031840a00b41c0c442e820402460910401850340514000c0406026001c02080c03101640e02c2c845 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 68610182 1250 68608932 68608961
    0x2070501090204091a09010c090b07050a0209180c040b0f0d0204060315020703080a05040c05010c0c0b040308090103050619260f01150906060903020d08070c090506011205090a02060304020a09 84
    0x404614105e9034840c03150750700409540007445941103500028003840090300581800308400503801091050421800d104513a01419506080c035200390014240005064071601d10301503d1201aa50306d000c2c040d0118030b071402400160890556007c10102e99000a01240c020307031502c0b00003010903a043da0540a64034070440c056552005840d000f4903041c3c00134030461001c0e190105000214070140c202c0c000b034071820708145110031013a007001101001d1030391141c3c03840c0134009004030801c803034000902542c601c03c1c0c800303200a0710f420041103034110b02c8510038085590459001c102071400c5074141014451142071040a1000064520381001c40c101e000084c5c580d12a002d8407102d501f1010b00d94001c0200139801c10a5905007140280142c82e40d11010f480780d007010545905101c4424112481c45601161301c2052a580e2154500903000032580d007808981d1110b0142130015280c0101ca20910204025122201c41582004401d410150043c2e0700171410910100760348409111304680708a028 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 68611432 1250 68610182 68610203
    0x5060d15060e030f0114010306110f0403030f09050301050f0f0c0f03040c05010e0d05031905040801020c010b010e1206040807030e0a09050f0703020f0a140d020f040f140303030a0207050109020409 86
    0x907070a140c0303000e41c0d80301364100c180c1c944200c0022a10345c403114035064039841680400c5c000d02c0005110024011202500040d84000500104043d04003072010041c0815403250300d0310076610000c0608881c000c07100c0d9010b8900300b0b400984520001034126620219004009050100d4806040241d800440d030842d081c41110b90f0500070303076810421408600388202d81800c4403160170f40e2965124005e1482c94420a071164079280308850203901034038050f00c854002103448181c0501128083c04019850b0360100f00c010b0038052807801c00d100200d501503000c000a03d0203448681d9513980640c0646416070811080790301d0051076960317041d00040140010b031008122030615020400c00c03610007514180c145441006003503260584501075a20310916030600e048175010840091005100d17049028a000d440000c040d1041c0041c04040c1040c0c55852070342d500f031561039a4103540c1c004a02e42140d5450b07401032000440303004041d001440f01c944240004521003109034049426150760034030031202204030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 68612682 1250 68611432 68611457
    0x40f02070602030f0903270a1208030a0b01030e030a0503130204060e04030e0102031206011b0b0a15050a0803040b030c07020a09060801150e06010e210c01090605030c0405060d1506 79
    0xa002d0b42d16084400d0170043c40c03500701109455084401c0d0540541001a5090f04100c10340ea20f0b03001380801003030510003c10b0041d056103001c80e419401295040d40b51841e01002c6d05295120380b03d4022840c0703090004500c0c040d48400143e40c03076000141180301002d6a040c07070a005031124002d03000103242c240114981d500f01890082c0510a440b25024115403082c0b1250060845039640c07039801c418203003070845194490662480044103c2500500006520030a0008078139035640001c8010b0400c41c3c41c1007240f40c0300e40030170070101c002c0e200b010400c0d0310a000a00800922000a641000c8900d40141c80d00c00d103580400c00c2040142d000040c81c1d41c0e1602c04010405003809400c0c01000c3c00c0005503a080e00703040d05609101c001a00890401c503c1980904068580c031a2407400710304541c0e05035400b48001700800740d440304050141c500050f014207000038000c4c002c0e01a68040c240d6a00c029050906000070700070070341c000034a02180701d91100201302004040d412036030060310080d034442402201 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 68613932 1250 68612682 68612701
    0xa053a05130e04020904060c0507141c0e280807030c090b040506030a0b090c040f0501140108010303020c0409030512161b1709042a0810150c02040f0207060203 70
    0x42035404641c80034542c008110040c1c0e2031040082e0300039031048000030103401c1c0da1802c0f10103006846001704000400221301481c5400040c40c0290512206190202c924200700d007141c2d072010704803030304d84c200c4229413683c003569800440090710035440000d046062030b0b0f104451031801c01c2039441507030010311001d8140701f01a91030180004c00b100540b414081800d100011a036075005411000d0680820b407070109090030300c00d01241c107552200500c144160b000b4086000b00926007882002e400b101d90038046402d550144140604803600f540140000740600001e0101502061078100c0400104101000c034001942c51074901810b4100038a8940c2040710744080d24950007094100804d03540c280340740c80014804021080604801e11307180d5200c1c1c0640012401903d1200310b070501d841702018101103140e0350528112140558bc0d65104c1643e20340380300814656549003e00c4104043c040c40c0040a1409541c4915401c0e20203440000d030018010341d440c040380c0146004840039034000060100554 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 68615182 1250 68613932 68613967
    0x30b090d0806010e0906032a030106050907230906030423010b03030a260c0c0105070f142101290a0203031b0c03190305090a053a05 58
    0x40350810741528101000083c058841003541940f10765008000200c042d141402245040d2640c585490780c00d46046950787d00070700c1c12542203800383d0310f4800001043e26015075101e008405948900b000c01070544000c00d0345608811052a00950401c400722064032000c0003503110b5800783d41e0340e00603070003940421000112074042c0012242c0c1041d401815554010048440d010407a0520101049001203001c0581131003040c02071030050540100b0a415507201e00800d09588104005c000c2e5540d01c000550382600c59101d4400051044000b00c82045211402445442030000041d52200000c0842404224090300610710016803500b10481c6031400d180020302516180c0308180c10901200c60007943c13404010a444180750f042a00e1401400b030a1045481e500400c00079650398205030724813108840041c5050b00d001a04c0c00000840700c0e075002c900000400d51000107081c42a01b440544100c0c0c105002400c440051407009d9861a400240c000c0350740030b455512941e8441d04c0c004141c41911 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 68616432 1250 68615182 68615203
    0x30a0207060b09040213020c01110c010c14040b03010b18040507030c020f0714040902180a0218040e0a080a1101050f010303080f0705030c0703050403080a09140418080904090c030b09 80
    0x540f601000d010042c2c0d00d0142d526000c0c0c04240d8010303288d40d640048035003d40656403682d08151000101d01c541040706421802c0007481c3c903161014044d81c3c140511250b0710441c8140400b4810500041c40709080d104001c00940c4201c00c8400346000c00100041c044420507980c0c9004a0350f80c003d00300b41d80360188015040d440d03030500500002031404079451080ca62003c409841123645080c0d0004540d40d0a16191941c0e190b001d05c04142c4c9458018540294007000040c416041200c4c242c0e080d601d09170007001c00d03008040004d40030200d042c1e6202d4415810074428031041c0320300d111000f4500c0c0003d20641d403098100014031892945182006010740300080c1800c101024074104000c1002d0304036040326000b213040740100d41d0b2454642011949805550402084002c00181ca054415448a580c3d429580110214080d000c0050200b1044492031020100c20540c80d4a00101080c0d90340d01070442050042c0c808540c0d238174940d80f0080404030381d0b081203a00050362028403803443c0701000346000d00c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 68617682 1250 68616432 68616439
    0x301020a080604150e0702010b010813020f01030902040b04090c090e0c0d031101110309060603010605190909050106271b0c0b0403031103010f052d060706090206030a0207060b 77
    0xc100805400414100e801003001c1e000e2902c40500043d14100690000d005152018155600c3d040c1000028040c0403070b8080a07002a244101213062280d41e0514038904584c0204940c20103005200150050300b050036059903c559603040c02c003095240c501992591b01d00c1000c0f41c44040781000c203010111009640c0c40c50940d03002c44400a115150000b4101580d5058185480701808a2038610302500c114501d05561240200a0210f038010008400e0700a190460007800082e49400602138102c100d9401c03803100c41c282031070820600115a009056040c000c1300046250360329526180d508030b01000a43c4e00c0c101c040450710b10004082c0c40340d44400d0201c0e102c0c09490100d0454001d24a021280d8050040f2115002180426000364031422400b24800401d585035a520949000318000522036140a00080390420101a800b072280b803030315141c0c05da0302e0b1040c145141c00740412500801c0d400c42c0d400c0c3c0e445c021503025075105009980f14040045000d1b03170307480a41c90b041d4142c60036004820700 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 68618932 1250 68617682 68617687
    0x60e011205120309160e0f0a0e0601060e01030b1503061203030402031018020306010806090d0503010812130305060114040e0f0618240f06010216030f020103020714070311030102 78
    0x680041a4804180c506002d6a926503e40004a45c00d00c80c0c26401d000084a82060001e40c4082500d0f403580300ea0300740400b8812560340d207520b2009503400240c0d00760182d0468070062284501901c2e07440d0070b644061500040685030030002c69400050340005980108012040240c42e1400212080710005a403014608509003540882d60312030740350304205603050f2034105880a0380c00e411040020503030014111855540d4480440b529410300b641c11800b28001e0641c454541c6000d01d00b00e904881c01080140145030000b2190319031030b0444640690315151403000000030074020049a8080c007030404486000761010400c2001b00c03006104200c4840e008180285580500811025888030508000e0854039543e88400ea0420360003000c06288801ca00309506c130181d808001d41c0340300310070321202ca000c00c0c0c070f4500040e40c1e15a854500364101c0c030801c0606100251950420700540b1f4410b04003d030902959584001c84041c2e0290850125031219600b0814440032080c08000071005400840c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 68620182 1250 68618932 68618969
    0x60b15070c05130f0c08091c1b030201020c03040602030a030606030c050901031a0d060f0c090302060f0c0312070203090103050705040f090b0d120504080615090a0e0709020409060e01 80
    0x9082100c1c9109035486280c40c0041c500903464242c010407080440810301300040304000c1d0f40030b40081c3c4150750640c000e20a1211145507040c1d0042215030b420519140c0813848500c5221580300344108081c00c50465400f0b022101c0b030a035040020340003906080d000b442e120242000000c1c1291066030068003058104005018071640203000c495001c0000c0c070707001c40d1203c041c01300f8044101c102c0c00e2094124020004d4182400401e9014a40c14142c0d00381c248166010140c040b0348070703100c5000c00382d84048200000e00c41078850f50020b0140c44045001d0b2800c246c8161070b20148101d08464000250304005204682c80d0707814826243c4c481303054206182000d041020180e420f400707901500300442d940380e240d140141e44a054050050354030150344c84031600030100050a039000351252055034403601003c503d28415103036041701d186102500141a89c2c0c1c1c0c5555a0000d410444c0d10101745001e20755000c075025070540018809054042c0c03000c5241850070b0300c0442043c0c0160b01204903604440c0010 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 68621432 1250 68620182 68620193
    0x1d1915050c0a030921050703140a091502070302090c0a020d08090705100c080f070c080d12050604140103120909052202180f0103060501090207020d03031e0207060b1507 74
    0x80e01e42c070110345070000e552621494001140c0d0308000043e0782410800081c0043d05520000415003e0f11980d590030b51050010f0000050b070180764044c0700400d0b440343d000d001007000080c2c00c00052a261045408045d40c0b600030a0b003550054421101c02400001c4140f40d00c0c2d010004c2160340021440c2004091904001c400d840c0d0109009513072280c8800d2003500a01032107404100003264105d03440c295251401e900c02d00b4154003c902c1140d44404d80e5000150745000801c0200e10414140c42e2141c02c040a00500c4000307001c01080c295026560b941c880000001c40700c16035018500c80c514910008049200203408203059900c000403042c01d100070007840300f8940c240d4914603201c04030300c0802c8901078070001d040718007001103503980003404804011400c41c004400d54100da024290400a50742c880000038143c3c4a81030000e0341103190b0322018800240f09901688030b8884400034090100c00e0000e519040e80e000c06000c3d5419910b4207070b80115403400c1008048049408010640f4048841c0d0b0354 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 68622682 1250 68621432 68621437
    0x50f0f090714040e0108030306040b1e01180306050a050702100c0e130e0f100c0504060e2b05010911061c050c04120308150103050c0d1d1915050c 64
    0x241003040a05000004150b08000a450281410081d284030340d42c0c49014440d41d0b034000301e401e184140d04080c076400e80c2d170500808900c0c01c8500c2e443c924004004140041d21031070554030340041c4801c0401c0c00007000c00d11a20440e80120000355000c501c5041608009103040000700c05030401030710b0040c85c00c0e001d58210000d544828001d80319042480c46420f69039008000c880000151409500c0501c825110085941881032032000c004000b802d0410108907114011806041c003c40d00e900681059403800600080003c040c50750401c070095400040010b0200d80d4400031140d03170b9164003601007000055001100200d805a0380c280c01c200d04255180040d41034034034046a250340e582c0120f45c007035003014100c4000d010700d0900f420640f0090300d401015500c007164038200440d0441c8120341c940d0310034050940141043c1c4009400c207100b14410400a0100c40102007070700811901c40038420a040c8102403640c010a2100e01040390305050400b000d65244506080c801d103040304000364414080306 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 68623932 1250 68622682 68622691
    0xc080606010903060b060d2423010e03100c0e03060610170a061508180f10020906090a0b030115020309010c0308130204092001090302060403060c090902030907050f0f09 74
    0x2004a10b0210746030100d0403e02c034150035030748040d007011103690203000c14548c2000507a07210609240581d598510202103000a0810b030401c100303009008901f15846101c0060300140000c0030755040e01c8001c0c2d402801c80e01d140b8003810106210b0303c2200005e1409020082e0701160945029503007868210006028881100051144010100205803008443d600000240510310455400c0c88000707107000d00f480c50111210440e03052510034013544030501241480710307002050000c00c41310001d40400d4029401404440c0e401400c1402041c0050340d800054400826035620f6107079883d4100700010907072030352022201040d9807040040d204982d07130211403080c1c20b42c3c2501e8480110740303911002c020304c4c034076600d000303035000c0e040c0200181845180034003282283c1445400307240c1c40422200659680d401da100280d80514140010400301c0d24072b810a0020710250f182041409807901e243e24201d800c10b0301e00500c1d030f40c440348050015042181200c881520704a1b400007480d510312001600d200320051 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 68625182 1250 68623932 68623943
    0x30909070503040512122d0105011d0a0b040305070806040809090a09080d050f0702070b190903051e010c050306030a260d090b1614030403090306020d02070c080606010903 75
    0x20003c3d080c40420310224180740d80c500d010698402c0f050310039901000302551907a16580d169608001c2d104070103054040d454110502100d5541e180c40d00560f010642889080c080307010401002031a5910141400e001d840003040d80e5417940c1c11800c0841c0741c1a0b1130f0300b01c065298070210900c00401c00800986000d840704803030ba64200d03558002c2c4c003009041707071940013003a9040c0030859100074503060700943c1c4140c1d491214203c2540c2d038440102c0c1d445120f84600800700c08100300d510115400c01010107502e4034142032104015940341d07196407405c00c110519140c0d480c3d60007142900d5040a0013010503030b2740d06282a50450400b28002074035000040030041074000303c00380030300d41001c09480c0300c92003036510340800e40c480e03508244000162031034071030440c5d064090100003405181d58400c598003080196940001520104d62128010390001c0c2c826003d0085500c0c002000501a0008096400307802101684039507192509817040306031a00070b43c1841c2c1011081040c0f42c0d0303100e08103134103d03500076 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 68626432 1250 68625182 68625187
    0x10c050708091c08090907030605010c0609060e0609030403060b0406050105040509040303090b09010f050f040c0303180302040501091a0f0112110405030a0302010603051506030606090915070914030309090705 91
    0x1100281c02581d41c040300c00f46048103210341d0018031442d100981802076043ea0181c6859840c0300301141107840394000d5601180c09406c001012845039840201002d00c9007600142d040c850006062401d00701b04d90340d0985a100181c05e000300302c1d090154490000b4196010b120070741c10100040c180d4055030103401d000e020b58400040030706120350000003200303421941c0d41e4150f0416028983c060076000720100c003502d0a002c00301d08205d00e140c500c10f22450708000c040540ca41956421220b65800031085203104000305008005030342c070707885614000d003082e1800103140710429a18198004000391002cec0b090040c06000d601e56600481c0c40358945806100c0003818601040f05c40d00d003401260000d9405110745840041010340551009065a0141c41280c4a40302c011051544899048456603015003080010070680e0600c8011ba0307411607481c0080d00c003800380e40711868030340749411600000000c82c1c1031410407210724840e005000c280d20a83c05180380080d40030201d010504060800e00401100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 68627682 1250 68626432 68626447
    0x6060d060f050a02040807051c02090717150f030c150c01090f050c0901120f080a0e180105090703020705071403070509090c041401030b060f1c081902010c050708 71
    0x158000c00440c10070400801c038500f800880f032402504140240c0da81c1c0d101720030b0003141c0c07490303e15a2068192214004c0da03010700320782ea0902c030b00d02e04043c0034181442030000b2403c0c0c0070f02000070844c0c4540ea00c8050245001480d508216005807078465050298012140301505500d4555150084500348180580d9a1885098090040c500f5550140403400308200c80000c00c0400300c1d040504000c2142c41b1100c0d0790301d40920800d0a12215002040d88038154601c1c03000401139005803c0c074071020f081902080298002091490704100c90b0341c0400c20303d0030018081881d20030b8016400075000e250440c20002299100b540d103e085000e0b45002030341c0882400043c0d5020440d0a0142030054280d0903d800c00461855a5001d10030311a0f2080b0f0900360407044020540aa803030489421055069a540740c1c2000d000a191080c03001c2a0400300040c2d209280025421680510798410240c035aa40c500003401c0208114560001d003045904008090100541c0601900d40e21504071000c1d95075043c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 68628932 1250 68627682 68627693
    0x806150a0605030c030f18070e010e010608010b07030f0905061206010f050f07170c011508070b0f04030326070f033c090b13050d02060907060302160203030313030f02010b010206060d 80
    0x458040520507441230100c0031401450b208942070480300004800b00282e41c840303005907401c42c024043d070f6500620074081c41d40813911803400b860740c1e107085003094490603072100081800d940c00781e0602010502c1d110240300701940d0001d0021a2030403589032190400d000141050400d20808402905208d01c80b190381c104010444100c901440c1414020840d501007000001c202ca8003d1180d0a072034080d05100080c3e02080c5d40442308042c0048050924090541e40c040e00e60100030004258003140c44011482902814108a0301441e043c2c2c82c1c003090124a10302c0101980c540c03000c83da04500c22085000100c0742e880c0d910382030f12401d0460f00341c2c1d144010440c1c540103001225001e4000940302c028000040d016440758207009010b002600c0355a00310308010fa0f82c40100303440c1e5010300e60040c0e00c100080c501c0390380640140c800d544a1030f0007000c0d083d00001d00c1e540081e03c104144040d01c540600030560050002c40300a01c01d80020310070280c58000207515100004c3c951405410010581c004000c2d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 68630182 1250 68628932 68628961
    0x13060209090901050103030f0203040e0c0d02070f05030c0c150301060e13090f0b070309050c010e04060f080c090f07082d150108100b040302040c090806150a0605030c030f 75
    0x4801070091501d0b45000900c00d400303041c0c28030041d40441e8110102150700c034808000c0368160ba10400c4250250340320044011029401301d910085003079030030b001a10024903035141d42c500303003401a0011a1108220b03280141800c4540c15042d104106914401d080200040d083e41d045a1082c10071801c0380d401c180200c4d03411001e04444403000c2d85000100000c00541120003900c00b4044da6400d1200e9944510607021540c05001c041c0c03503940280850100303503101c0c038500104131078050008204195214031a403400c460541200310990000060007a5904100410f20f5100070b40a00c203140340d00700828040c01c1c4803005860b441182c80030210300c80540c1114100f015010352072140085042ca032039250a80e0081034601440e00044120020030203202c1d81040d80c0341624145040d02c2d1406166508000050086466401c00e204114000103801c1c20184131261040a40402034004079a10034100170041c18a90801b20a210040c024021b03102d00f8030003920f030b00452048901e415910f40726550314029 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 68631432 1250 68630182 68630197
    0x504020d0f05060708010e04030518060c010603080c0609030412030518180609060307061d1504080304030c151b1401020a0c0606080a0b070f090e010303090302030d03090308130602 79
    0x1e010501091082100020f5030781d12550f850350b81d080150340c80307501b81030760300344282c070b0107000240e003484603c0c42ea040c800040c41c18504000d10040c680380e0003181d0542595071340da0055170208008660f030b0310002001d0010642c001e4101b4055840e10b800c1000b00e40e12a10483c802804011011400100e2900d0341107044d00d90f00070080002610181c0104100482e41049600c50700820030400403400d141030002e400c0007520f009071942c0b428030364400e41c245202c072640307154982c3c4907203e00e40d00d030a103a4150004001410441d0003556036a41141030607a607840e00e40c3d001d295541c50860701c03c10815405a071b500700700c80c507907500b1001e80080c0e82032183d540b0708500089560341d440010140082c0d5008464010704511450050208503a2141d10540343c0c5601c0c68040c2028501600154489104107030031441a0074605014030f200303440380040ba0081c40300f43c0080b8085130744001c090003586000c000b2010000c10510b01445180c0c41d130b80e801460f07080090800f00d0664031090b03036981005040e4040e101e50303 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 68632682 1250 68631432 68631443
    0x6010b03160e04060f140108040b01060c0807020a06020a1b06120209130e0c1e0303030103020103020906120f100b0901120b03010b0612100e011a09011e0f0206100f03060504020d 78
    0x3031940f5000c0045d07440190707101e0322442d903405625200081d4001e00300c01e8803507078000190f0001c9a2901109807407144503a0002c44d58100200f20400c01617407180c484a0150003680e0060072004110300d00540107142612046480c951b0304041000301c542d2016075200174148566003d42c81c3c40b062400305800d801000391080025042450301202c034000051052403c0100311252000c6804012481c1c0d0402c180071303240b54054001b08014400365000742c0007409101405003088ac41c2054010000664540070b03100c080c0350511a0b020700114026051554011301000b4001c5032130300c00810006420222a0348520049545070344641c00c040d81c00b036108589a24000d0081562041411109140302c0701c02c9079039025008103044040303440116158030b9416645c16004024403a172041ca0349403407a800c030141160402c80300e8201006040c10300380d240c090641140d101c48014855055002c0d00704500100054640c0707020700d03001c01000313a030040404102c1c1d8000d10002010b88a5001081201741041b201800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 68633932 1250 68632682 68632691
    0x1f1d010515100e0108061c0804120203060c0406020a14011508010221011503050a020f0a0336060203040c0f030305040e0903030408030c09131109030f06010b03160e04 73
    0x8440c03401894a800901c120342c2d42e40d40110406098a10032480800c141c000303142640019141c1c10b01410003050300c8094105000d188030507558200305503219400812041e4000d0381800b0441c02c00300f103801d41000c0110b5400c2e06050030450001d603a40800e64000d8040b00b4203a8100008002c2940b280105801c07020842c90400d071541c4905010f94020b0b4480c1b811300d04001114184000364000550503a00d02c104641082070880c0012009840090111901036a0800070310441100c804010085540f0720b44020819041080f0060500c0401d00340610b55006000c25560784000e1a08030844071903030003100181c480d1201c2c10040c00c0008544c0041c5006500d07120301109160300680688100c4501b26446200c560341c514400707449010644004014800a00210b92204820005010387d032030003801e540c2c0c1074461008030b0380c02d41d1600b044480d0360010014002001d8101070000d10040c2150300700820040d45801d010981521000b44401e107445c48040e1140c1800344107040307074140610000c00502 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 68635182 1250 68633932 68633941
    0x40b07111e0c03030a090608090313090b130c0207060c0503070204050c07020a140a0506070503120103030503010504060608060f060918090313090902010906030b150c060402030c01021f1d0105 84
    0x300203901d40c14003548a11807000010803034980001110b4548226507585102149010001c3d00d8442c0c0280580b00c03140020312580280f0a21003c2c1c0c0c0c0d00404c4107070804a051011241402981c4101440342016182081040c40344640c0002d00041190480d2810801c8451942000390550081a0b0006c0d442410131050022001101c0c000c0c103045030084412101040e40e403078403006815840ec13030103038001c05a0b46042210786000c034094481135000e401602e1615040550351501080f01b40c00440c0441c1c1e0100c014030541c1030902c01e81c40902214204040c0a0400c40c0018100c21710580b84140b0440001407061603c0e1034140801041d42c03c041c031080c0c05400c0c0782c1d269540300d03004941da8200c190b8100e80005034024907802404601a0184c40e06001d250a14804030050002c0740e55058111807554070b00e00150f610003005052458107480076110030b0030580b04140c142054a00c2c1c01e81190b002080b0b80900800710051500c182c580100c4c00100403070502c003000140311803503a2184c495440c1c82d0801 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 68636432 1250 68635182 68635213
    0x30c071509030209180f0303090c0603252106030b06060c0a050a05030a030c1d120309030f0106030c0501030b0108010b070c050402030703020a0201140108031c0e160602100203040b040b0711 83
    0x414117031103903406856500d0154002d40e641d90000300c4041c81c0e2680406410f00795400c00c1c070000c40e042140d600d1201504c10060f90310a00358600c1500840020754108217003180c42c2441d5101c809201650003040c8102c0345545c44240c99180081c2031684180c00001d211444554100b10281c2d0f6240d00c0380c180c3d404140d980c1001500d0f40c020310b40c00000700381410000414140b14444084050351720390710340c4e4801203112080c48010041d2245031041d81c8400c02441440d550100302504907041240c0c0003191144c02c625248203000c2055126038180340c1401c101c1002aa00440c156041d00d04140c21642c0350b0078a41001c60a0401c9580002e130018800001d1000869158008040001e030300e8000384a5520300d140c800042d41000d00c103030101900300707101c1d410701c410f80450711181100c1019404940c19000000e0541004160750300c1d40040c940101c4104155501400161032304540030500314118603254640016803840100020115100a40003139130142c0614500381d88070300b10f5800c4030400140c0b01103c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 68637682 1250 68636432 68636461
    0x607050a0b040308010b03010b0412020a0302040501080d14030723130e040b100303120e160906030506011a07020112021309150e130609050709090b010501030509030c071509030209 79
    0x3d80000354407000105010303540804590403600c5c49250145090300e4942080c0c099568201c04036407102c0f000100001680d92405031901a00b03c00c0003400c50220380910161503100703400c2c144041c4180501c1084a8190046804204010a45a00c06038541988003040542c49107180712031600303181c43d8010841c05108104244214428000f0f617540f515070174004c24021005210050010300b188403c21201f2050f0b03013080405c0510601140c10801c19145a00d220004c940c11040303646995100400900c42c0030020300d0b00401c0b001d41c8081c0e0440901c680f5038080d1007001c0c8081e0500032030704c0610081400c140e0469100c1a9041a02002e041d201c000040c05040c0c43d002d0342118140b5440041000ba6484203007500a80700141c50300d030b03014016603c0380041c045401041e1071601800c4000240011140078406d0590f106512403c0d80c7c5d810a00054100e0310064004030085d031040c401156004000914201641c8a1101d0701804030b41c0d859040394020040d403c029001010101485484407a10344c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 68638932 1250 68637682 68637691
    0xb0c03010302120f07090e0f030f07020f100f030903210903020615011b030c080a0f030518101d0a080301090b06190e030a0b07020c0a050301110a05090607050a0b 71
    0x1046203000303070494000d030384d2211405072004940e00203100402061549038802c04007041c02100743c0e9a5541005810350550f0400442206820000140300c421440d11100c1c5400d50002102c1c04144044082c2e00105800c00a0b944001030580d20800c0d2420f01d80101c408408601c04446114210400700c081140138101c007000807005446860040703403125045c007c00b05c808113010303510705210300c0ca6034080b80301c0c42951030b00640c103018081000390040307080f540040c81c4485035078580040c40556810300400701c40006021910f503660404451140b0080400c1d038840b070044109000c910045e421002e0100e10000665034070032380c411034140400300500900130303504840c40d5400c104011b040e04400d00110388103c100340032604560f2501802c600d030050545102c0e0441c041c2c120340caa000144c0d1400f01d00d5905507054000b50b0300411805c0e10901d0102415405084240c001b40000144011007004601a50b08401c080c07140114009000b0744642040d07400040e040b4044800c3c141c010300708029550820394 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 68640182 1250 68638932 68638939
    0x405041412040825030206070b040b0106020318040207020a0b03190f0e0309010f030605041107020f12100e030c06040c151d040f0209220b01020604020a1a070b0c03010302 75
    0x701c1e01c020341501038054408480c0010040d0a92008401c0b51300428041c40c05810418101d42e1004000340e11404080c007032852043e1264119800c6c542070505101005030301c4102150700030084141c00c3c03191b003050246440030603903001d80c84660b18400206a00059049804a600301004120b0f0341921007602c015008200c05042111031030000a21059818032564a580c96000700325100740da501c18090625290500e2600252158a07900040c0139140030000040340004045110b40a6103032000e09103046601c1150300001107400c00c450603458000b202c1c00c40020315561005003409620910440d1420107125054882e039281510700501c840101e03005170220311806828005005004204040d00110410b0000780214032507810440a0400b041c4000d81035a000e0101d1425512800304c0d80240110701d0304c054041260346d20b52842140c1e03540d9816411581305006000168a41958640036540341c6040c0350780303904031000882024800c20780300030540d4200c032080094004400d0040d5040e48e1084 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 68641432 1250 68640182 68640193
    0x109060305090114070201022d120403110d030204090c0c030903060509071205060108060903031003080306040f1506021006050f090901180308040201020c04050c090904060b0d0b040209060a0b04060e010201060504050414 96
    0x9c52003041e03101c001080700349105410041019042450181e4a5000b8400e1034110702d44210008003d0408074203010120100b900410180004542d6001c2c003c407007141c034034040007548040e4070010a01c0500b403001908280c0d840703020886449092254401900584002d07910700e1040f4a0215583c04092090341180c2c000c00000c5402c20b80003004072400780f50712030841c543c5a42180c490000f0303588080d1000b0340c4a40d990401c14071200c1b460140d20700c60003480f00940800c2e840c2c8100a8103140600f00500c3c0791a103000003d0149a458066003c07400382c080d2540340c1a59202e801550041a5100c040d03034200c115614480c082503030006505100350720030790941d144400f040d001d100940380300b500c00048094041c0040c00c0302e8100700340400c1d070013401180082042120310307000c0b5403615920380e020750750405908208819810007040d000d411030320075140390b0a040d1400028903003600503802188200901011482c0040e071003504040007420300203000308030078182858010704001c2c45403440c0809001d003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 68642682 1250 68641432 68641477
    0x170c03030408031c18060e010c030203091f02041a13060806060406030e0c090108010c030e0d0203040501211802040c03060f05060d140a0204080708060105010906030509011407020102 80
    0x4826070381121224402903003000a81c002c40d500c002c0c04103918041c0d85942c0d40102003079550111461200c2400340000041198600951a003560940a84201403600410512090880001e000d46012240440509221000e0b60700724000e441240d00808446080d01d0408440c030300080c0040c0302c3c5d030408500c00c1c01e00a5903030b80284d801e00e00c01c88165038081402e00c42000382030300a4001d1045081c5003005d0f14549525800011180f110a0700300c807100e80c0d95142042d008507014401c80180d09000002000002d10079200295a40306a001d07050411220901c0035080e501620f840003600001400c040c071418000f030341c0610080c114a50203038880c13810181140340c010f0003442600c00f80c8503e180c030980501d040c42e040c002c4039440380b24800e00c0c4031f90710900e440d0240d07041900d19000d01003950000d80d50350320300f9082d01d18011440d00030060541142d001040320b60b030000a9101100c50606021825030740f120b0300507006202c80c860340380c940341020701042000b0f035042d402800c2c101880d50b40c42220004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 68643932 1250 68642682 68642689
    0x60f0402130f0e060a1b081b0a0c0f0302030415170711190308070e0409020a09051902031302010f08281b02070504050c04120b13171e0f0706090203070f170c 69
    0x20160380caa0340d0950804c08c1e44d5840c9007014010b0103114001d0170400c4000e062541d410303060f40e583c00016001600042000c0c0100c00e083c80b5a025032600c1468082e408410400351854075240140414043c058200d0742c1e5148240140166082010315070512021269541800b0b084900e04039440b0340001c0f11080c40840c207140078400d40d8034258015100140700360070021184000d050180181e480c10f0064400280c0d02e030a140000e43c0b04400072070801c407540b02031b0304c00500080d264003000d0062101150800640342400101400400600304444401c4401d041d03882004180d82015000000448c400341c0d800c4c20b400003103003402c841c0140c07020405569501c015148900850050a01485500d203001c0003154550880c0c58128001010410600c4010398400e03140c8030300082881c40c03220000c00c403180c40740070320003800c4000c00e4400340f61b81ca802d4410b1210301c0c0c030b4400c5c00401000b0ba42e480041a0640d1010886100545403036245260896200d4205461203184880e155180b440b40c100e02d0f900604 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 68645182 1250 68643932 68643947
    0x303071a07110a0201080c091c140102070b0a0506240310063f140403080601050412020105280207050f060906040303140c0106060c05060f0402130f0e060a1b 69
    0x1000c0e200607001c3d209450f4011130742c038107001d403410420702e84c284405156039654900c60703500ba041d288203000c0c80000b146804020004004590000c691060280038081820010102c0c1d005810b03000000d2640c2e1a040095a0040002400c420142c4a00181c4402104c560010340c06280c181035101c00980d40e43c1c400702c039190341c920721556400b0300100e003105040828500e0200a0012440040c0c07401490038444401c81c0c450380c14900384124210144000d040e00940f040e60815400c1c60020704c1c0908184001c070b4a114001f100a040100004803540031140c240a203c480d07080302c2106004030f60302c511000b96240264012107100300503102003400586406800c480c41c005010741580e062503d540c03000c0e200002d4604035814031240402c0704100c4500d003271140d039001d810562644802d50180c0e042c00d603c0c00c0002051315001c20500001c9c0801b591740d03824026441054050b021840c48030600d20500545203021080031903100315818030410414640028009518a00d1485000550804120b03140c6 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 68646432 1250 68645182 68645207
    0x42301110315030d140a030b10080103030801090207081602060702030109140c22022209020d11030601080412050c06010806160f120f060503160503060105040b01210b0303071a07 78
    0x1c1c54171200c030b03881603a210050f041c04040c42c14002005000140482c1624141c10b2001d000544140e005104141d04484410f0140011075001c6040c00b05a03600e9012a20442541c0c0c07140c4082c0031400c008542d41c000c2211010b0f58080c00030300241c460f52510480c54040954a45683d003c4c0070380b20407040c1840c15401030040c070490800c0080350400f0749a00e0080d0b111444809400940c502d0103806c20a42c2e036245d1000f030031154001a590b204c0383c1a0041120030980e06924410000c100f407040a03a03204c0f210071303042034100b66060b4410301c40390700c1912030b40304000344c4000302c1c05070000015107034601141543c8588013181ca144c001d10080c1d03001b01c0e1060500080100403070000c14214100c1c0c840742d07014141241828400040864840c030000e4981606140304584060078850240400e080c18041540102020b840c02d000c0c903460303000007902ea40d034989100035009105070407507500580c10380c11040348240041c0c15203555036500d00704070300040780d0003a810780d000d42c6160100701214071030311094154 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 68647682 1250 68646432 68646437
    0xf0201120c02030301090e0712030210060501030603051507051b0c0414010501080f04030c0602040e10060201020c300403030c1208042109050402040815010905040803042301110315030d 81
    0x6586c00c2101c00d42c0108004105004103105050010407030694201d07900031060701940050152181d5250402c007030700c208e0340003141018140081080020000165482b888041d00401c0c00c882ea01c0410480d100c2c003174600c209445000d000c043c0c840204006c2503881e2a51010790b000d000741c0c0c1c0750940400c1e50150a224603800a1600000200c0e50b8851116042d0030903c203240c0040c04483d540c44007400d036000f0307801403880c0b2158078040c040402007407500000106020300007075042c0b2000c0551b00342c840161007400c0301118a080c413851018031890400b00c1b1509003806e10103032107544a0400034244c0c141548121142c185440c14806c0007405500481e00c5554410a00182510090108104888404504000d00c000c3c1000450996a20b00241019011800c0104114160304d41400c90000040e4080b00400d484c3c6410700020442c40f0301101c0d481600300b06041c0307000c4190b502c04100340060700d80000d615460260300c03540b244400d01c010f41c05420140700e000d800c4051075040544480b03450b10500301 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 68648932 1250 68647682 68647687
    0xb0a14091b190e3601030b28110304021201140103030c02040b040c0e0a091109060f0c010606030f0c0503070206060108090a020a03150606020d050a180b070f0201120c0203 75
    0x40481c1401c80342e04040000e2606584030302902d00031a0010580d08985141100408642c114012104004003d02e607130000d90600d2070b51542e141c45100d04409002c541c4060001480700d6030461060180c01c9100d55080c204104819040315034080c01d0300b094074200c2c442c911440e01c0c085501c50500810325500760300240800564a90395040e2031400d80c80c0001ca8204e49ca5040c10b8250303560394401c2280420107a22801e0450311004200502c4a126420203580c1c1c03440d01602c1002035440c00b003500c11549003a10060f9a43c03412800d1101c06000320400c10100d58241040824126132540100c021038001311000d000c0301a03a007100740c88030300007200d0304c00044c4d006000065803580b02c1e900080d0050243d07029241c105250f82c002c28915000ca40042d40c05c42032082d000002d04c003851040030001c000520251205501442d4000c002c5d1081030780c51400c0203000c00b00a800303074034021808001440e15119840c3d072050340c6c1c03808101e051810201131740417071016501c880e280780e036900424904100b04d601551 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 68650182 1250 68648932 68648947
    0x7091404021803030706060312091a070303020408120c010609020702010c020409020a0b0a02010207020f091b0f0f04080a03180609030b04060b0612011514040e0702010b0a14091b 78
    0x7074100b14080800240002c0d140c0000e80c40c148000c2c001c0c14041c1e40089102030460405170f0725641844800c404220b4240010000c032940001c841d1001c1c207916440b5903550101d802e003140a80030b02e40045a042c002c4c40c6407540c0c40d82d02e1100503c401458407009000040d95442520200c0c0210324000e408034954039120801440c00c0c0d84030038038184c401085a80410386461001c1d074913402240d02a40036030343c001440b00c19480e180d45c0d030201ca00800c40e5280081d262074401e50f00d240441508095203404041502000c50030241e040e166100180d1510644071035440c2001030765003043e07600030b502003100d481c482d07101c003c2e82e103101006807075050b15074a200e40d10350796540100ca0300050083d20002d40d910001c000c10798800e0018550308040e00c045002c25418403e9030114055001815400e012200544400c80c8810209075400c0321006200e50f011a600c010b41a4050641d01400e61790040d801d0001040c030000041414000c140306075021030032591400940001c0501c08421194401d2043c0102c0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 68651432 1250 68650182 68650189
    0x510080601050310030c0b04060e0d020f060d09050d050306091602060105010e0402040503011113170d0c051e01020a02120403020a1a0d0e03030106031832060c0c06070914 75
    0xd40e0020010020b4102040c0d0300c1e11146140301c0320780c000d00000c5400050800070598455035016040c0ac04507040e800300381d4140d0009100d1a42d541030180104000f0520311241c45c62580b00c242d207103800500b500e4290000c000d00401c258021a0058825201c00010545030088022007034501103207a0001c0400381d0800c0700546411901000039507001b80c00b00300108031030704e080c050305403600b406070395494031110140f40407411680d458110b0090140081d201512210002440c00107043c00b0f17080004040841d42002d42c20482c0d118a0b400c010580d440c0e82002401055005006066840e4243c8031154010440d04040c0d102d28480a50710030020310084c044c8004040c401c0d41040d0400c4151861308464241c0c91064401003c815001da400c0800100403240d00341c050000a44807042c1c42d041c06101a640c5c44281c9100307500c987c4501c803044402191f20304e0100e4070321840044281d040b40c002c2e2401482d80901540819600b10450240001080c0800d0085402c98181c0720400340030420514003c090 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 68652682 1250 68651432 68651437
    0xc01110a15020304020114070c060c060e011415010c05070312050909100303080c070b0406090c18050103140d090b090607021201020901020c0f06040e090109020603070216051008060105 81
    0x2600454050030000c54005081005040c2001c1a08407015032280351600001d81200380081198070026410428100010381030308a500c1650207038140001080c90900300384004120750442483c40758680300c0255110404848a40e03c6180d41003000200d02814200450329014080401000c50303000010501c0020400048004034a01c145405d03401c014000b000290354004c181c4001d0101c034410030051052541c4641c074141e101c45160700042c509030080e0380b0b0314a01d050090002d400e180d0703604042810480d9030f0803018010540000c4c141c0031118100014402040c0a1108950840c03103d024000e4201010801000ca42c02c1d40e2208000c0528012900313110703a10004d241603021008000100040c1c0c0c500b994525410aa07000041c2c558507001c0000e0700d0b02c60203c140707522640d41c2c0e2403003d0495484030304a41c05c0c0c1d9181c50300281c1645840381c056000d48000f8000a40c402000310030050050703400552206561030f030b10348a60310140d94009010b4850040010600060380c3c0c0c1c000a103195008000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 68653932 1250 68652682 68652707
    0x40b040506030a02070605010e0708010e060607060b12060127050603030702010c170a030606030c110c0f06071e021804050601050d03170a0209040b0103060503030a03200a0e0913050c01 81
    0x4013500d092284da98040854078240c202c1828003002d14240056076070f00410260140808600ca000ca81c10100e0001d400350088500061100381c803030340c00d6016619650841c0350101c0d06c01040710195615403502c00b207032000ca640c0c0054001e4544450880355149809881d025041c042c014601e001c0c7c0c950011204590501070507180143d5410b80607500070404401040f0600455400059041c10044c0007000c2d10380744503042c4100070044072451094080482d1081d80d05204403410000180240041041806a603a000d0010b403004020303c8208081070101030f90091085407a0840e401420342056200072040e100a8107680c07115006201074109000c2c0056a6400303410f0030304001c02942c40c41e840c80c4d02c049400310141d40d0040348492107414140500d000c429000d08051080e01e05003c0460790b81d000d102008010191281d4041c2c41944502c55034942240d45110010754403040000042c00320f011301c4a48900070114840003a40f400c01610300c441d00280d00101904800310618011220303e0650803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 68655182 1250 68653932 68653951
    0x3200304050f1e0603100b070b07090611060a020c0f070b0702011b0f080304020111100e010501150c11150c010204051302180919020c0c09010b131503090f08030406060902040b04050603 81
    0x2c000c00c1f07803540c12018056191090240a000d441c22030401400303403c1c81e502000c1408400d400166400c0004902d040c1e1144507840e005031602d500300c44041c80c1c440040008aa140a202c80115001ca500d10003461268001e0700c1d140e50301100a4541ea603d182d14100141542440c10380d60700009220070021504240140b40031502d0340001100a824138115440031040169107142180201c4028000c0740c0c010450902541c1f14018015030142007800a044024280d1a24a40001030ba41d5110005e000100c02840d000b5207500143c50918000d50160040d5803054000c10f058508800321070003104e000b04442800e143d1142041d0050010780d0f00c0c0980381040b03144888000402c0c88030940b01618041464400400d01c003c47c14092242c9030030107800086d0010810844bc6442604214843d01124100c182d6109a9031518504034010541da007001046401ca4400080034001d0440c0070b107018602034502000701c0f554462502c01244140d04c17459020100c14002040310340b4100c006181d0203000d25 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 68656432 1250 68655182 68655211
    0x5040302060d0e0c1507080c0109050304030311010e0105070e0103020307030605090907090605090402030703020907022a010e040c0f03150302040e1f020705061303200304050f1e0603 80
    0x3036000a4603500700351400342c82d6580d0b9041c080e0f240c10301086460901e00e016a0100840c4074220380c3c0101c40c0c840c40d0000340c200c1200040c3c40032080025400710304816084001d03030b0313201d40c1c0b070f0300d001444a00103100c000f85030360800c2070fa881d49441c18464035001e00b44035100c01c0c81f1400c0c01001540030390001840042031540e030303103000141a198a441a0711a904001c094052203003006058801c49586401440c09180c6600070400140c40004803003050f00d40441d6613603201d42d1644070491402c2c4551492991422400340c0801c0080c44080e9540d040300c900f603d403003030b5008508003070204940d01c6860690001d488940302060041c0254800e241c01c52607013100308903154503500414140e1710035082040c030660050003100c0621001910301c44010500500030352609441ea1260303995408090028800026070060a0040600940c10f01811800c240c443d5007070b15031245001ca131207801c10310909000798500d00c2e80c812981380824524403601030450b01d040303203071036088140640c40c0c0004000d1282e080b400c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 68657682 1250 68656432 68656439
    0x90705090a1e0806060f0402250503120601050304030807031806060b031e010b09060f0702090702070602120f16030e15040f050f0f041e0e0c09070809060403050a0504 73
    0x800c44201d0103001c0c0304840160511031000d800381d101190342d001140540052082c080307581d5420690720907503a0308590245e19181c518400c40440716000745000d404a441e0012070701044000f001a05005c15409001c08190340e034480151168841124002c0024856800281905000354005102c1c548003446c80c8031f00f0003465030344034112180354010200314003010042242c0d42000c0401d444400f84101c004000c1545400b03401c66080c0227007080301e4803544010400c058a00c071a40280c80003e40c00030503442042c140b044000c2d481d05240d01a41005010f110a130010304241c0c201100e5110701034030f480926040c40b0740d44d1102c400c47c03000c0c4101c00b00302c0070800710041591007a510303c03164069030040595580c40c02018511396041d40e030007140103881c05962881195194101a160050182c0740030801070881a655160810115150340c00e4920300a440b4040c1180050f00c283c0004050b03501d43d84ca600c40c8a4203640300a030441d0a8040365110030002000a44140e02405580c00f4070300f010b0341010344 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 68658932 1250 68657682 68657689
    0x120b040608250f0e010801150303051e09130f05060f0a0302040e0708060f0702100b0117040f020402040605040302031002070f021003020c030301180f0b01020706050721020d020f010501120209070509 87
    0x1a80d41c0321501004c1d444005004000013032007510341c84801e860540c03529038034541d409003907030113100c00b641c448208500d810b83da030b241c101048502c0180010f01c5944000000192a0000e2280113a1000400e2420300000e0043c18072419480a80c1c0004150030b28044c0b5550030030000d04840d86a0ba07000c3d0144030000a0595402c002c024014500c0480040d5180b44c0110006d2600c0f00e020303207180c0c0c0c16050100d0b150381660401c0f01880c6074000708a04030129981d900b080c3c03271000007030040290001c1c1300043c0010200d0f8010b01401c25a8421070948984808545098087c0e014005d8040d100061100500e001440d000d440754442180b1420050f00341380c00703070b4546410750304240d1140b4034183c010310044c40450f00340d100c0d00380f6140c0c184100704205212480004d60390307a10b47c0140018403038009a00400d212a100f00c40d501c002c01e4009001c041c84e00034038025101c1001440341c4026100d00b001d5039481c0f01c1d040c041c0505886000b4031410000c0d81c142c007004003995016040d0010320400300301d0310b0300545 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 68660182 1250 68658932 68658959
    0x150f02040509150102060f060d06050c090d06050714031006050c0f060403091a0c101a04051006090e01030b0609040f050105090a0312020906030c070501110a120b04060825 75
    0x581e1843c1450482d0068006420704000812402445a8940420809565518540c019645c00c084009203075510005551401c0c440c031410154809580d030711a400b005490340010f803040b161a82d5810050305100354141140c00700350b0301e115907030052103001c3c00028070501c042c11402d060381e411954490031481800303080400036076040d400103a503e0428403c48408100a200c1c0307500690015203040d0640340201d850b60f180071048429251582c07001241e0312115101c080030541e00410400103030408402d80c00c00d0144c544903103404260084070005440c2034015001d0b040740c2d00034000d20040c0d524001044031042005104803010400c2d54084008143d09103e12032103009100d004219003002410050940140d00540c902d820380100251140c54950b4000d803908000070703071071003a103e030124907060307002d404811100c01041801085d00e003541588030b0714055416a07418010000040200f06100c00d840040c0104850340e0b100005445010441350000910112404a4a8203040e03c81034500b41d00b2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 68661432 1250 68660182 68660191
    0x3031d0415080f011127010e040c0302030105190806010608071e0c0201020c0909120904061a0714060c070201051e0a020102071b030506070c03050f07141009150f02040509 75
    0x2e40c803e1042401d0020240714094050258150b070391300300100924040c05501e0301701c04006652007a20b00c0e06c0300e00e034041c804c0c1c0810001b00400c240303d10500c81b00010001d40003481000d00c152000300c088602d480d5041244800c2c0d602d03d401074919030303013065800c3e100010301070403110822800d4062460807074002088058040744550300c00e10350303c000b4000249404400c8441d0b41c03040c5945410300c00007410000c0c00790a80680d00e940c840d100da8407640020010701140c1e0202d80607501c070304844050400b0b004010701a0b1841100d094002840b0801800c0d51900103d0702c82020318002c1065001541c064006005022803c00407885007109a01d0050400d820030024100942e40101c4c502042092a445100201451098a900c0f95103143c07512640d8000142043c4d0512171b280b03808200303252166041354201486900030a64801e401d191115454004000020b0310380100403c0c42002011405015401c1d60414031081307001b0080d182c40d0700148613a42c030001c41d00740d007008009607903205e4183c840e106 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 68662682 1250 68661432 68661449
    0x204030803060103051806010504090311060a091a040803070305060d12023703030203070c0605010e010501260109110702040908120c1903020702040b0d0606080d0903031d0415 77
    0x100d00b491400035080c0c0b2005480410361000d052041910440009a45811110122004a0200303110704040d101c2c04040512101c040c00b0f8042001100c14194006c5000c0ea0300c038003452310104840300103c072100c40003030b50024000d080030001309080c50304c6a0860b640203080280000c180c40140d50703034401c5200d060140240542c2100c2c03240940700d4214160400c200e403440550300b5030040c490152801d1119601d40080500d0350200100e201580300361a60f0b1469580020104440d503100d071001c489483d005d100f820300007080c2d8110002c0b01d80d00303070b03042d05e01c88c000c1c0458914031642400c0d1500c0150401410440c411681484100f0241c0c0d01e80c05002c00403401090429a207a50007151000420401086101d60f284200310545c8091030382e08007490b10740418500141c94007524400140600404100319610a48072004d01f814080341c0c0c0e01000c101e03100c04044030000030200e00c082d00d034004207200c040c001c200c21440500c5035803595410001e110300010310005000b0684140070803004e1254026441 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 68663932 1250 68662682 68662687
    0x5090709090903030e010e0c0a0b031003050607020307060b010f0f0e01020f1b040609020901020303010308030405030f04030b0708070e01050904051b04081b030a02090a0c0c05030d02071a06090412021002040308 92
    0x207645d01c082c440c0101c091500b00c00b0b0240100c5104c0402e402070140e03c149425520300000141030800c0318174402c00995448802c1d40c405040410001303542c2d40040c1c00684006140c480400403644c044c1002c0083c144064a40c49819000600281d80c465080d03080c46065000343c0311041640030051210043e0100d20941904600c0140001e101c02c4903141d4102080f00c510401c2001c8142ea000010f072411a544160169500da643c3e03d00f440c00d6006040b00340300c0c50f0501041c003000704003050700d41038422905079558034407a9440c4a011149400c103100328501041c0100030351211414a5006982c0c8903090400c022042c00d000c45079405a0b502980c0442055049000d034090156191090510104d074114010f15801d42140c002440c0050080c1005211940d1000301841d003a000d800071000302d035040001d803038403202c2c444924400303940440411611848a01a2400450b030002c6045006603809854481180d481d541c8107450510310380701140542c480c075000c40c0c039000b000340000c0003e0743c4907030000358 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 68665182 1250 68663932 68663951
    0x20111030a141305030306060a0215010e0703140105091303110f030306011824020c04140105040606050304081602010c05030f1e0715150b031608180303010509070909090303 76
    0x3445940151590400f094039081010104000000792908040102c1d106a070382c1e1400704c0181e01c0c100d03001c41c2121080e01035000001d02c07031480070741c26407040002da24148403402c07480c480f5150101d424024a64442c0514000c1361036100c054101c583d413030744682400088007490340350092900c0d0703410405803503d50000042081c2564002180c042c1004500b048100883c1030016800c0b804402198444e40c0c45260030b01c02140502c00c016903044680098010000c4201c0b080d41002902402d000f40d90003076041c62800103409125034100d0b480307182c218285504148144051035450f8070349420580c104080260410040740041c40182014074500300c0301a0798241c0942020040e02e942010304828800a10030340c800b00301c12520003030b0809040100055000d03011920601c0d0200c580d04407142500d004810409035909901202a500610740c070303002c1700d030b545180442c003089000c10348101064206000412103401c201e5900e81d000742c6c10f070401d020b0720f94540c0070742c0d01250890402907002036141d06208 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 68666432 1250 68665182 68665211
    0xc030c030a032906030709031401090611040602030f03130b010b03070e1203030f0a020409090312050a090c090209010912110f0901050607080c0106120507080111031e07020111030a 79
    0x210b0459107001800c401210504038500d01d107600748030341180070f810b000002480c0b10744560781500c00745030700000120383c44450040c400e00a22f82684104c2d00d0902d040c001c40f41040c820310644044807030581c010761414940500003525034101a0481c84040f65680c0380708001600b5840f0070340a018640c48268881c1742c203140003000203031440780e84c1c0c2c0240310f507000d4817444400c04800c42e41d00030208240d42c0b01d02d841e80d60a00009104540c00240d40c5441c208420f0101075000e07840c10204042d1620502064071142401011507021185c000c00000b0aa0380401207003100e13402410b04041c050611403400c603a81c1640c03a44411603034804440141429034040c0d100d150880411000340800c2e20300200701d6051002050b442c1c0b00d0030001400711500032540101e888403d4020102a19110b0404000f28405241055403001c260084100315420f000c60000310034409010b036445400c0c20100654102d440243c0c0f02060140500818115502c4581c43d282d902c01c030b10002c500820b54403070000b40c410f200c289034 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 68667682 1250 68666432 68666441
    0x90307080a032604031107050306190501090506060912010e0109080405040c0806030636010e0609060601020a020409030302161b080105090d0e13060602010f06050d020307030809060c030c030a03 85
    0x107a00502071010192074801008000941e8840c0e8142080c014046c100130b10546004465805035a0610a8104004550707408a08083c1220141d0307000b4401070740c0303c05810003918800c4424580044050280611510300540a060290100c2c000050031000314110103003911082d000540c1e040343c0002d41002141018890090f4509807490250300c0d07810a400000c3d20703840041c0041c0031138603507200003110520100003480544800405030108140d1810300c028040d100035144500c0303a00032000012009580410940d02c01d480507400307490f8403001070707013080000c0c024560281c00301a820300c280c45025000406541000c8d0048501d4090b084054002c498208042d400ca580c4590414050084801000030048440c2d9041d0416100b00c001071800304400d2411045900421810103000040003a010f601c0706140c0154160207111054a40c1c090204060300754400941540c403554003080807540d080094020254020300c0103240901480300030f4a5074104030f40c90020340c0c0001806a11080d014801c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 68668932 1250 68667682 68667707
    0x30106180504090f0312060906080f060f01060507080a210e0106082a040207050312060a050607020102100f0204120309080d0311070f0204020702120a0b0f010f05060c03090307080a03 80
    0x203050241d070342c644c2e82d881035110043c0b50003020b018a20715904203020840d089500907000c0040101b00c00342d960117406a80340e001d4030740c40081d80558000303e8001c840040d0030702d041c0c81035074585600d44060355031a141a54014100745081050304c40310b56902403403040b804005050304031000320708110f50324025030031180c40e0741c81020940e0000510044c09140d100c00c03403500ba0085461100624503c0d00454041e1203a007600400314000010494021900b00e20400e00400b030a8510600d000c0d2160144030311885030013000307400750f4070200305004580c80e80e40010031000148200135050560300e000803c80d0140c940c0b42200801c40c0c1c0d50781445081002c2180300031003009403405201030744141408100d540b0a440e0050403211003142d8000c19500d881d011502c00ba58090f100786080c590341c56200d5180d400c440c1c41181d1660100c4089288042c00c0032016043c0c4100d1020150b0103880e140c10030482d6400b0081e010f129000c14450030305165028011080103020000141c02d0b84802d0b458018064400d444 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 68670182 1250 68668932 68668939
    0x5010806010501020d030e10060b040311030703080d020a020c0310092109060c050307330506010e1207050402040303030b0a06030c0f0e010c14010b0f0f0d1e05030301061805 76
    0xc0100050ba90000d0f60010419150400240c50740d15680d00d03d08000e645034840d2500c40c10720f40c0c00210300220000800c104e074061100d850303242e01180c04042e01d8080f81d2002404044090180110480c082e80c0104141822401100c1290b1140404a1b0801c49014007a0750a00d86d00e5114006012076600c00310b500b541c034868000382e1035800340780c050300810450140b80708100c244c6e11104100007041003102c1c41c064104d005500440a2003001d1404403400b11270586080d40302070140500ea078442d028040c014801611600400c51554043c085c3c00032000c05011051712075103800240c0d58841d0710083c00618084d540c04505840b0b00300501a140041d64440010145070068a00c442940600c036004801c580346449054402c0c4400100e6108601c240d0180a05100c40500c1e21900c40540c00029000c0e4103980c40c00c0d080300c00404000c3c00c0541d01400f1500581040f40c0900000e044400540358400300c4040002080c004e900d0303661540d002604000081140c84108124202011400f240146400c4 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 68671432 1250 68670182 68670193
    0x6030a210e0415030f0309091811061602130915060609050a030506010b0a09470706020703020322050102150c1602030f010903031d010504051b0414150301050108 71
    0x5415880c0010307404e01c0042d140700c0780d014440c401c240c4148112030062925881c2806440f500340c04548a03c060540200d45050089800e02c00504040e02640c0c06180e4442c60070760710350440e400340000f200c000302803120301c02e985446400009411150240740c40e903422500041803820000054035200d1560805445126410300030000100009106070540c0d16050301591205103031075080e00c8600640e0050100c91240c07803d40d05030368001b0307201d60400c2041c00b9421400141032100c40941050005131a607100c0c84c0800c04940401d11a80062045511900c1201d20f003e21290b005051b11502c081c2e6210740c9026000d08118030741c1c0c104046000744580940300c060b1410840510b480c248100027040144c0a64111003005545e800e0000000c04100240244440e000340e01c1d000b00140000c440a0500e02680c0404090342c180500c41c03a440380f94003d004002c6c07400c0c207a01014098190300f00c81584642c8500b82c00a00544685000d40590400c0240350312018811b000c15094840581208070a235105 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 68672682 1250 68671432 68671451
    0xc06010e0f0c0d090c08011a0907050405010c0c030b100906060503060a03120903050304080114090102040503070b030406020d110a1707140c010603050f070314030c06060906030a210e04 81
    0x1d448a90485403004101c2d0392005141e04403006064520806040740784000d400140307194040d000610900c4103181c02000d00d103281c01c104401454180d8891002850030322080c091940101e009030300b90b5000d01d014004144e035903a99100702d80c404880100c007980280c0c2c0104840d82c024040c2c0c001808081c01e002e0308610300400030840d002d14610000d08101001d07801c560800f4091401c5a0165030042c043e07940d2961505031460207402d5400319811495490030019103411418420764056860050242820b1460b00210b00043c3e04090820f45640307600700014904a0040c0c4200441d101d03505030030035120405080041d0905400b00499254861804c04006c90541d01444950100004100640d00c8c2d82e5001e141c4c0d0b006103410380000b0600d2080008441e2200c400082c0c6c0c804032445032100301d4003c078022001e01e8881c024802c1d0400c156000c00e001c65060300e0010304080c2d01500190855000c40040d031951501e000380c03180a00307001c0d40f00900403505140d000c0841444004151000d0181c44107 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 68673932 1250 68672682 68672701
    0x201090206090f2101150803041203050a11010e15010e1303120e0102040f030c08070303020c0d0311060f18030708070b151806030d140a180810020c06010e 68
    0x40d208200d10801800500f0911503030b80c0c4101030300c00344981c0b1141078030440018805008107030785001340c6078040302c0b1000020001c40000032a01500d86c403c1910280942682d010f4503160814080c2e00f090203000b848002c107180d400d205101d4846050402860415414429000d40402c103030802d1002200704010400e40d082c1c0070001542c0d0301d915150144004030a50710705030040c411815400303015400010300180c0c0c19034102070002564001c810464080c0c0c0e40d10b10466403080385200060258000035454012460001590100c0030302909082c0803074034411152508101044541940d5103c2c503000b40200300954120b00000c441e100d0b0011844c18466490b000c0650180d103800800c0170742414000360f41030001c108c040303040aa020b0250070150600d10718500483c001110414081c0c0700d40300031020350a210740e041200302c08514040d245021003180c001c0b24000416501e682d20110400d200203001c6408001110118405140050f1101d404000c1c2d5418490306a00c00341008141605004800300f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 68675182 1250 68673932 68673937
    0x403080708061e0a09020c071403060921040902120901060b0f18060c01050903031f0f33020106050a05060a020d0507110a121509052508070b0702100201090206 70
    0x20400160f02c1107a002040040e00c0e407103245d00070790001070011074556049a00080e180040c0c480101c0703280d001000e100141555400c00b00e520000a6001c03011140b201d0b2103011241100c080c0d40310241d464030f03842e0f40f40303c4180d0740003594000c0031002e0b0304104000220f0a02c150000f13400008003461a000007582411003074004d407145602070072041c03150554140c1d0b0744001c4681030102c4100a0115141110041c0d440350011a03464041007581240d4029044c1c4000785c0380c4c00c0c1c038100554040f11a061500d441c00718000041d0244d400041b040300e61007042c244004c0d110f0165400d41c0003050107070411040c00a40900c03588a140510020300c801d0f00e1984c0c0108a4003c238016610701030751034003840d0611403400e1400b100c0700790f0059017010000c10740007103800e003540540d070082c50300c0d0704c0b4400940d0400301140c10065010b00306810001d811000150801170704420b0704000c00b031810210780c8031403031a4281a0594040d001d0800000344050850901410b4200c105205000030082480d1540106020b0f1 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 68676432 1250 68675182 68675209
    0x30b010b090a090c05130915090209060904090506160c1101030902150a12063f050601080303061f211103040609050705060702011205040c0e0708040308070806 70
    0x21030003040c0a04192500c91414008100103801404910b04c074030400b600b6075021145199508020040100348401d030f5000e00541406c5092021104601d4034a01100a4100410072940400100316840b1355988078020310400034016000391042c2c0c10302294400080b207680d40100d0911010511000200752980021200c1c00c1013801c002c1074001c1d80d440002c440807020350032442c0365a80842e4038807405500c85808004019480020455261903800a141e0800003a00d9521406080702643c1d540400140a900c00b40e4000303165103007045415903c41d410004260440401ea500110402c403891400304034912014000f00304520a84103820f2004100b00c40840358500c414840b45c0c0c917800040c0f0194050300c5100d02220035140c980c1401c0c54200301178889004c0030703102480f0700c0b40302003000d00d05030041351807407603050f1601e03440c0881d040041d030b01070b1000030710541e0280104000024014a81c0160b54401c40607079482c07000307501d06858080c00022014181c002040300c007408001850f01e8071800f0b03c002c07 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 68677682 1250 68676432 68676449
    0xc030c01050409091109070f020d030908090f15070302010e0105100f031e12080709080610030b0a02040f0810060f1404051812090102010b0d0f141005070e030d0207030b01 75
    0x40b013116050904c5041036a4408581001c210f4040051241e40030722140107001213642a0761184080c000708074141c0320381c410003030701901c070422045505281503940c07100c2c00c0001901091f9006204a40103807a608031070020b4026035100c3c07217406008582803007a2070303101c0d001501700742102e8104a41d4aa00c0e00c4540402032140201c110060700d01d810000c10003500f954400d060700141e054a0000620760001034a192010603980d0740c01050510012940a1107401c108100c1ca14882c07030350321040c840741c401520201055a0801000c1200421403608a01402c1d54500400480c00d201c40320000300c404035846062014a40c003010701c01c00030303c0e00120031100001c95004c01d86032030703031154488555042403010000303100340d60390041c01c201180e000c2e28000c4c0090b0020041400c03000140540c0b40a0040c008103600d50f00803104001429a811803040d0701e181c00c0440744800e803000c40704002c940094035221302203441e801c1c00c1d04003880c0c100481c00b100d61082c130282007614507565864248a0307060045505 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 68678932 1250 68677682 68677691
    0xf080606090901090c0f060e0102070605030c0f09030f010225020d02040b01020c09101502120702190801090807020a080a05120c120706020d05100807060305150d050f0c030c01050409 80
    0x212002c0940100c0d10203038001130003103542c07956070a0642e01102d540c400c14000c00e01d1070925401c25030001c1b40c84001c81b122501d0380380c516035504105500b10703070040c050241d200d401448030400f90384041107001701c090104000140e5508044121185407008548110750030101c00740741c600161200100d03040eaa603170545010910201c6500180d0810904a540d80d41081c6007000b08440100126148400c4401c0103100d0625121400800ca840da0120090414410010444800103041c01032030300500201c0351060750138090b01c41540500355a00752005407844440070581c0025441d0100e141d400600c0288020001801503503501030311403804040c511240c26010816280d0b10b071701070240d900400340424056030390751081d1074460001d4104010b860b00c80340c07402e80002c0c1e110200d18425800d90b0301b41001000064980403086018140040c82e40c5100c0020708041c002030380710465203402070b034030410180c0b40400400c51203914040c0c00044403442640610601142d40c0d070000d04a4082d20520840401c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 68680182 1250 68678932 68678941
    0x60a020a0b0a11030403090e09010c08060f0604330804020d0b04110406030506090d0f0c0803150d03050c01050c030c07140a080309061605031e0601030605040f150f08060609 76
    0x1030040201115841c3d14840c004100820958040d8005040e01d4507150080350399240d900001e403c85281c990040007150b10b2402244036450401c10710300c1c1c2994000d00710b51405446458451603d018244c41d6450015080b1280755112480b02d01509042014a03201d6081d00c1c0c0380d000182c003034041400240004880c1804907050100c2c41401d00450400034000b0f200345075407458820b655010456405005000b0010300191182c880c40c41b540f4a601071307a0701c641c46651262540005a0b0002e0700d10360883d94500e00201c2e0507120784d65200038690090712030360344412000700120300f9030b4401403174014030440410400c0800d10009064500f081e030010f0300814560201001075141501194010f81a03140110400030811300010380302c0e00c2850030940c1801a54100315040d1a180401d0300e40b034820340080314840e10400c41442c03c0d254428014500481c8203607a40300802e00302c49206043c2c101150300c40d02a02e80420b65404800001d107000c451112a0701e1500000d50303181d04002d00100d214004510101c1c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 68681432 1250 68680182 68680201
    0x2030c0a031a03030a0e01080108060f01170c0a0b0909090d121a0910030210090e040209040201020c1f0201140c0a050f0f0d0605040c0206040b0412090305060108070e06060a020a0b 79
    0xd0001581c050200d0390781d01d106485c0640030080c61000c4034001180c10001084034100401d04900440206494241d00c0c0d0800c15400c170141000010f032040c0744104054489180e80b94842d0800402d5400b1450f03959800b10300070311041c144010300c03002c40c55101e961070410f815481611388100224030705000440e0707074891000106041d04040c0051703001e24240c3c103000d10701400c0c4804804503132085643d5040005040c1c0c007912a41581d01c200c5203010b050000250150904031201d0b40d00c03920510540d200d041d55800001c0341d803e801030189401d250105803c80c200c40c0c092140003c0c4e8141800c40e00424607000c0000c0000d032003500e80007820801d0202c3d00d00111560401610203680c0c2c02c5000715151103000d000e041c01022144a174a2280d824040030710500c42c004200103020f10342152601085580f41e403501d00d181800c18120030104101c4041c0000442d07801d11515001c0e01d40e002c013403c6070914141c1c41e12140480a411503100d94001c2040070300003500004d1244103540c0c802c21016031aa2002080c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 68682682 1250 68681432 68681471
    0x1e0c040f0b0a180b0f210411030c01030e10020703030e030706020a0f030b1c1103030c030c1c080a0b0307050d030c0308010906050f010302030603010b0d14070902030c0a03 75
    0x12211150a40401249507528140600700e400e01c15603920706034209440d8180454030461045290741401048950552400c001c0200213440c14582d0141c05022040c4e4151280d8034200e4090b10203503880d405041c0185410302804400311424a810710000419112464940520b80f90500040c0d070700040f1039081602a4101003501c80c0a02c0981c0d8941080e802c0c41006980250b00c964001200000c0c9840990302921075088655000f40c584001011080048540b26110a90079103050442c00c0103946150303800c000030902d0403c00700186844810001c406481d1968100154400f0b400c90f24100d15a560b000c3c036016400800000c0200301d900680000c40c1c10714100303412254001c03208688010916030004074003e12079100e0303a26968280c0c0c0e01d04000040f1031482c0202c41c4d1004409400226962103030f005160044001000040c42e042c4442c0003542640d0030a10498a00d940055041c0382c0050034400c450083c81484015899842d25000d0352680c1e214022080c4145a40c0352100450058034415 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 68683932 1250 68682682 68682689
    0x2010f0e060c1206031e0a17030c03040f05010f1e0615050f03100315020304050c09100902070309090608150106050309060a0c020c03070608090106080a0f0f02011103030c1206010203031e0c04 84
    0x1e401c06d0344050060035684600c0c0300e003010344500c409080d821000000300b0084134401e8040344003d9055444a596044140c448004251000c0d901d40d2807501000c20103100713112036a0740440c2e05e801c40660030001e5074151840c56210001c1d0450b0703030740c0c60301d95580c10070200c4440003210313071040e541c1c1d5540e118411000a403a80002c0c011510302850009040e10690007107000740d006a04403010009060304000e8818400c0318680d18600050000700900c80003030300074110840c4a030034103407441c9032104a030100b01e0f007441c0d008110f15445140c0703150f45144082f020601604a07850b0103895482e080c80b1055503000c02801c92003502d40c0d11124010964800c2c8641100b0348001001c2d10b010340d580380c0d8000d00804060329801301035440d0950000e40508001401d800050740151056020740e00754941c29841152020240e0520181848540300f412042c0004c1d44a8628150200d4603214014048082e01c2401040300f1f0540d0b1041090151004601c442c071101107407801c448510981d00c2614804a81c001e551 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 68685182 1250 68683932 68683963
    0x621070801020702040b04051603020a0201021209010629120a0222030506010501020f10050606091203040305070b070506041205090402040305071a130b0a030603020a030302010f0e060c120603 84
    0x10804142800c064000b090a28004c0b00e0074007880d06654100802c03140d05940c060b065203003440d0302c00700b4a070281d0040c14007010540001400c3c07254540d04100750120484480a65955420041c8000c0152010056061002c0c03078021000c050b02e02030303452043c410f58204d0224148168005049511f154040394100d0440c513401c1400300c18501f090003e42c103030a0000701d0303d82c01000004501944001503e800a6100710002c00074000c0b000d501da0000c5c2000391a1031780010040080480540700d44502c1c2e014441324600450351a46503041060074001c8a030801804e00300108000d1004c1800014141c0c0c0280e0045a072181501130401c0540b418422002325641040c000b103000030a000010508a04498060f004104030007589042810640316900c0c15203115900300303009104c106842805410803242a050014809031a900081c4003403030507070301c00c50060703441d080ca142843c4140d01903001a9032402c0010000c9080c1504401c2050051800c0d4101c9040181e000a0082da13041180307030401034984 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 68686432 1250 68685182 68685193
    0x22060203030718091a0f0f01020c04090f02060301081e010207080405100215010f0e0903070302033001151206030c0b0901050403062f03070e010c021810061106010b030621 75
    0x108003440c200d02507070f101c0c07072141c044101b500303071941007103120074810810581c0a00318046d0190f08000007041101e00035102503190070082c1005803203440046000e0070901005004000310062038003d40c900c032807240c2000381d0040c09503100050251065509662040301d010002c201c0704035080740381004241c1e0f101549568800002006890040035800307444218121601e150394160b2007a07542d20a003500200142d0040240208040407040710048402401c41d07141d0303220b000199240f911040070b8001e0300000405941340390741144c20545111180c2180c40c0e00b48026440d580300c500300c10006100c0d522041c10300049a00050780314100b250701455008904000000000e031707071501c06d0700c00c055030350500714011403041c0d00100c1c044003520300c2500b2503542c001500a014004542100c3c810204981000381c51200d001541c40c2890400d204403080345404100038508140102000c0c000300b0b51030281d8000600500c0030070703044821079038400340a80b1017402a60000220b400c041070b500080b1800c50080 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 68687682 1250 68686432 68686451
    0x522050a230a3c090509070911250b041104110711010905060c0a12050c011b0206010603090b01050d020f09040606030b18030307030b011e052206020303071809 70
    0x481c086001c06111444a1650100c030342410b0b10080e1050041002c00e101219004200803004d60300816840580c04041c0c03220715659102e14030907200c51000c2420b86540220715041c04202075040c01b07200c00892034014003105001d0303c8007440c403400541b010300460315001822030652540d400a02040b902c8403540380d83d805160821704040d00000354440e0004003180b000142c0d525081e000c0c0c2d41a0b80d810409040e140f181c554402c445065503001090501c202404429a04113086c82101d0014034a4000141209150f11000b414548140c0010341030602d0701070320340d003c5213140e01c1007815038000f6107e40c944d0001900001d042c0d40c1c60450700980c09040c0d803003044100070080c0c00c80001c43c1e100390002e201d141c54103444040e070a50803114600107603105000003100c00d07109401c1542010b0060405828416414a031143c41507458142c4402003500000c01c0c800ea10001d1040c00b00d22a0521085603d850400c0c0c8000d490740300c00f41841040101031074000c0d520b1110094400020202030f041003051b41c40 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 68688932 1250 68687682 68687699
    0x121805010617030702030d0e0f1e030c09220206070f12110d1e0905041a0906030102030925090c1d01020601050a061209050303070522050a230a 63
    0x800d010b80e2141d54022440042c1c000700000035107038420750040c05440e0840001d0707801c85e20810b101103c95441200d15041d282c458442400032503014050085c0d0480c0c040c5418140341c070b0141e030101e405c1d0080398850104a0700d1424922000003000c401c80810549000170300000e2140e0003500406801d60a560300900c00b033101240c100c80c4102d1064840414904c51122407545603244810000041044140105030901c3c5003100712540781c0060800214064681002c42d01300c4950301c00c03140802c096200320810703503d45101300d1a403040d401c400075407070b501e49184115110300502d5540c40c4080c4501d01020035a004910314030020f00100d0004100e0307a0004840101640e100c505000c8d12243c40082c0d200040d4030101d0601c0c180d450141c02103035414a010412126821800442424665151000e40001e101031009500440c0c00341e449a40340c1ea020003610f5048603485924421743d1006043c20011600c42c012000c0464204142c1c0740350401008030300d0740f4030380014051968002c144042c08140d010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 68690182 1250 68688932 68688941
    0x1020f09090c071a071b0602090a0f03020609060901110d020d090b03100b03150612100b04030f0b0a0204031407030b0903120103060c05070b19180b0712180501 70
    0x200e0403250744809481d0b01c2008219441406006042036020b4245500311018080a0b02d800111910300078610306e149848a1910f1261000c0440d00641c0004105915241040648014001400187d03418a2569002680074402e0f0400d5900515002c111554aa80a00c110103000441e1000707031130b020b03200d09400030749804841c03a0b0702e00494044440401c0e6200442c0079248505d0f1500525082036080090300c00b080c3e04000e0541d4038580032121840d28580311070f4050034444c1400b0075010958208621480b0b48035071650480425410f0070f03c01003010501d080c400100031034102503182c0c0b854072409486d901912407070300080c0c044a40c0f030345904102500004c8078412030740a018402c605495071400b103a220b100301401c582000907414010310110304658400994000b00307080c1075161001950340c00300400812101d190030000f4a05681c00c0c0d20669000c0d245d0b044039003d6604103100800c1d5031b40c540c80d01d4050200000c0126181c00749500340309580c00341d01521110188400d0a07142440c10314040c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 68691432 1250 68690182 68690197
    0x140a0501051c080304030804050f070308030108010c0c0804140a0f08100b030f07051201020712050714010902010c06150320031615120b0901030606090513080d0c05090301020f 77
    0x3000324820b80c85221054a003948071041e0f120761010702d16100c3d51001c03580520040d00907207490044241c0d454600500301f01003030055214080c550303140e615000882e0b003143c00c0c80300918203109e01040e0780400248117008480c1070301d80040c208200f040070100032078000c0c200c030f1b0005244024001808241c102000410102998001c43c050001620980616445011a18203200d9940c070208081c0018074001c140802c1c680031260005040514907104d4440c192401d04404001c01e40001d46c040500c90000c007c0e00501301004000d12044209a000900710885800c01502ca2580d40da070303030544c40f600580c0b0000215040f44221922404030340d58100c5014201c03500074460710812102c8070b640c5180089401c03c8419075041d5064120fa2850292000d41e000110000190713a109900c02035550b558500c20702940c041c0100041190406540302c003120405460282101c042514010009a40c8021160920610900031503000007480041d20380713005545002e0707423550002c0b40103040c00c0d40c00740241c10308 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 68692682 1250 68691432 68691439
    0x170a06060e0405010b01030902060a0c05030f07030908070803030f01060809030d061418010b0f0a0203040e0405070303170609040201030c090801020d1505010c03021c0e060a08091b010207030b0a140a050105 90
    0x51407171400650881d000000f0094010070140a001c400078005c00503904401e02410a4a10385200011220104d07480300318110003140701d1840510856808001c0c10300038061802c021465420480b07250031000700e05210345400c1044180005143d41c00503c00d844100e40820b20520280c2c0c2c41e08080641c90402c042d860f801642800c0c5180000035062814078100c49194200510304454030a190341c031a031000c1e20803415807008110000381500d0301c1600c17a100314041d03406071a049045107030044c02e1481095109809800a0050040c180c0d55110318980241d424200001d91642402c0c003694a04001d52005809510101f0080107500c0950411400d41e00c0103841554415244d00040d6440c8980110150060f0f10942511340007003c0706c451300e03044102e1400c0014000072010001091a44000e0010340050640f400384940f452042010441c1c0c2145622014110350030140006c0d07643c00c05200103041d007850040400c9400d0300325885a00c000c80524003881d05446e04011a0011702828402c1600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 68693932 1250 68692682 68692691
    0x706050a0b01090b03010e04020409020909010f0f05151908030d0e07050d050a0602090f060a0507050c010e01020c010c080c03070c030c0501050703141b0313030308060604030804170a06060e040501 86
    0x1075661040100c9800d8441d824051130640c1d0034100c90007440600140304a030416039824910300580d40c2c01544610604a000022501d144c840700007400b642d1882c00e45600541c10a414801020214800359075100c2e0b00f40d428040c9150302001c0115816a06d0b400741001e8000014101c07002c0d02d00b9000620341e07079114011105002e43c0c5500344111001e180c2d04c042c005400c0115500b00192040d00101000e1800070302075405081e0380400180c0d5540181c1d00c1030086040003918100308002440000c0c0d05610908018000e0704410002030349070448411106d0400003044110170800100400345d810860f01c00c0708036621038003680350030707031121038140030680381030f051810001000c1d889501240c014680c0342d503802250502810810809400c0f00c10490071203814002c80901c176580c2040502003103800802400001491820041c0c03440710003400341e60081c9400c00c0203102080c070090440303003180c103212000f401010300d813412a030600034022402842603007001030020301c01700c1044a050203140560300800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 68695182 1250 68693932 68693951
    0x504170414010831080d0f020301060e180604020f070f14060c0a0504210f0606170102030108031803150708070f030b010e0609060409050108030301060f0813020d020d080706050a 78
    0x44d03075400f03540640f00103a240100361300c181410b41c0c4544001a07100d400b40740d0512040210890560f4401c0644440742903010004001041d84009250020720041d02d03006c110f080b0116501217005001480513015a03000641610302008140031510810b0700111030602046461803c02d00019042c05003500c0b522a030408070301a03035404000c807100c9080f20b44031146401c1c80c20300b2580c05a54504000059902c0105905012900700030781c040c0090300c103803070014030a81080e4206501e0700b811388050081d0f030320500042c00480c0c0000125050700c8180a00c0b624030304440c02c00640341c0b841c101c48401500c4804400e000010b504941e82e607000f84034545a16280d140c00480440464080740011070000310900003007115801e104008040c0401d002d02513030700e0640c490300c8140a503042a400751015900000c0100000d541c004980b008401c0c5a160031400e60030801ca00c07003200358175000081e10401104d9101006c540d81c90321034500c04c65000e01042d450f0040307400c1110051804030b900018082c14403030040c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 68696432 1250 68695182 68695201
    0x1050106031b08011208071202280201090302040f0603150905240403120204051017070216031b0e0a050703060e090706050c010917030114060906070605041704140108 73
    0x10070b450a9a41c84640e1686040f4260000c49031052080d81c0b200020030001011a800410581410394686c0003804c100361958451a185850900c03e217880008000040c001030b80d0141260f0101c0342c0440d40810462840e01c980c000034001c80d8001003250031a564004090413641e0070003104107002d80103582010b42c0780386c1d5100c912000340320402901d6400781c00040010740102501007c0e090414001403c282d00d0310082900d042038544594003142d00642c18110000300d002c05190b20905520203850705c2c42e0030390b039800f81c0e1505a00000b012000141d03c1c00d12510394241ca0072000b062540640411420040d50b807a000780010b440500020707040110102e500d00040345000e005031180d1004002051508404540e1130b000b0140c190070355501c3d8918a00854510308800025088906080344d503549841c0c1407040c05c005445584d40607020034003140907130b0360b01c0384107a50081c1c1e000800414150f0701c61600061409048002020684020070042094a03c0ca040c9040d00c003001c1c1c981880701e48440450 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 68697682 1250 68696432 68696471
    0x3152c01140603060607050f0601060504030b10050f120c04020304030302040509100806060d02030a0b0109050f0f010f150309020904081b030c1e070e011806151d0a030b090105010603 80
    0x2803a0011420030101e131190902200400205001d682600d5098501c40e0920303013880380030380c0420001200030400784140680140c0254202004e4000b00303001c103203040082a00d01c241d629100e445201b44e421075105c0c400c4107124116440d82d00a0086559150514018000390018020a8018456800003d00e00070a0030154000c0d207901e40c000341130690720a01084404000f228040b078250042c000b8400000e2003092400f806031210300400f10301403030101261207041800801d101c40710b601c00c43c0100308503543c0030710020030768110300c40d21508140344240135000740c03c050380b00030340002c54441000103014003070000c0c10f94a44020003403c903140c03144084d0340e030b40d001b51003900c00750f0340040921f401840c01e0441100007880401068607100c66580e00b0490110009a00080d802c00300d80c5403103514088140f0580c4007030540000104890440038000901240012013080311400b640b0084004a9a403400000700540c2c2c003030f5203185c0c140741072003642c2c0c080c02081c0300b000f000c40d080c000030341d00c40107c8292 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 68698932 1250 68697682 68697719
    0x31202100f0c030e0c010e060306030c0301090602070203010c0206040f060911100c02090109151403010b030a0c030308070c0b0a27060608060f0c03040b0402040b06030a14010b0c07050103152c01 85
    0x11f40f8100003980d402000100c2d400603000c5a814412441c0d681d405031028040c45400da0300603e401625004240185800c0d0340f050075008085421180402c800601e84c19030801d001d80c0c0240001803030114603c3d003004521b452982d8182c0c84007280541030009540030902c0d003041032003554902441d999920580007030780c0e0b01d814030b1182140318072400d0002d4003805101d4484c0d42c00003000441c00d1445c44002c2402d00000d07810540300102c4406042c402d050700b101cec80a800503d9843e0078543d40e611511854000c0101500110035a40c40791074641c6551010700f50b0760696031002c540908060701c03c1c0350a41c0200500d10501e1418050600050404440003a046124401981c44685196503e81c1c882c2074940c8018030490b4001c1e5101e41b07591243c2c5600010b50f125069080c000113b001815440e0f40000da0168000310450310108846020b810001c80c141d03080380c00c282000704800d1921171004840340d00c1c58020010207020408045285030100c030700c114121012030b4241d40141d80b110300c3e00034101c010a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 68700182 1250 68698932 68698937
    0xf17010e01060b09010315050a230904020108071d0306010807030b0c18011407170c010b0f03030a03150308030903040509010f060801060804030507050f0c030d03090c031202100f0c030e0c01 83
    0x43e40139500030380011418a10100742007083d25103800000e0300e41e180c190028120341d21103c003118007803a0001020000b0b51000c0315001502c2c5469400240b81c1140100240d04021301340414004103c58504444007220b0010180c071020341c4c441448aa40fa00c1c07611040c0d808458120110b0711032111042152080e840b01126842102d55a80043d68004540440e52020b108e0800404000c2035030302d00c240003407068809585a0310540307010a40e096a00091145200796034002c2d0841059800000319000403409040201d8041140e01c1c015900c50b600b0350003d005410000b040000800020005100303032401141d15850f1a602e40000241c0110280110804515000014031003140075210b0180d20078802e181c042e00c1c15500d80d413006d041150100c10342800364481c3d0500801da24062110040180c0c16190401c207000072500d41c03040030710840c44080c0c100c0d500c2a2036400c605100380001103040503084001c3c04003007504120301006007140c41012001900c0d16201401401020854400680c0b059 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 68701432 1250 68700182 68700187
    0x60a120213020309070f06020a030905010201140402121005041a0f0408030103060231090f150e0603010e0318030c041e0b1306080303150901031208100f17010e01060b 73
    0x807070710710000b0740c005040d400e81e40c424054001500d400d6201c60030040d01480e4040d1090391000d2402425020031a080786041d6410301000d4800d200f000d44a0f99402501101c90385020101c0408060914503091481d46142d402d003020001031102040428401e04801c0c0c0f62403c1541d914100e01241e44800ea40003003281000704010070119003541c0180261040310034880503032940803000000c00c140c40041c2160f10500980d4104102c03003035841a80590860f41800b401001400740d19034101c41c10a006692000c2c1002e0007242590300c00f54824024075100307400b200e81e6002d0001081d0002c5800e400747c00d01c60312032403030007192074200b80c040c81d80250100c40c0051947c0130300c50180c001804049036000d412a8009904422091050050200034104503002d940c2d40e081c07100151301c030410071444042c01940680010800900d40b0341000c5ea60340c19610700800ea580742d20030b0060a104c4142d010b0750f403140c500d072004034040c0225440b007001243c8138030080044009464085090790b4640c420702640a005 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 68702682 1250 68701432 68701459
    0x1080105070f05070201090518151009030311010b060301080f06090312070f0e150c0106240f030f090b01090b030703050607050c101103180c06070f110904050303060a1202 75
    0x600060450b0038814100b084006841b00302040c80305c6420601c01810050100c00d000c0d09a2115400c0107101c0c0c022f8404c41510051540d0140a5042314400101080910b518500d80150290301100314075000408083e03495966503c0c0540e1001c031549840c1303190041d000840e1111100104a0340e0502840e0201c001c40d9880300c0381030b42c4002c1c010351142c1c00c1c40004040c9800c140d60707049621202d620b00321000d6441e200004021421581290808040415540341d07254644c00c942c076a9100c07a103082d140804686200b20402c030050480358035201c00c400c0c01c084145c01081102030000d81665044002046040c0001c0105656441d2a11014150b074101c00c2c0400d00162150b0700030010708000d242168100c982071a84003048810706040308402e04004428003c1d01c01817010441481301420300240716484903e0009a01441a01d200030114600c2e04042010001c02142c03019194800a005100c64030703150819546039481103d202c0d200f0004000085034511a6520480e900c1d500604481c907090356 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 68703932 1250 68702682 68702687
    0x1d010b01120c020f011b030e030403050325140c100e0a06110a080d05010807270b01090902031311060f090402030a090c0602030a12021213140d0e030601080105070f 72
    0x100400024218010b1840e11032000109000d01c0c01b800c0704840780183d00412001c0300031300300c0b01c032000c110007103810810040000c01d0b000402e6488042d07070030407080d142858000d4074280040d03640d14000c01c40b00b8000300411905034003184c03142c0d40f4003090310340300c2051998071070498901c03aa80020a611038524841844601e05c00e8502e000c106c84100211000680b147d11482c10030b41064012016158841c001400700d900b05010303000c01804c10120080e6807501c40c01c46a10f8000099086a01d402c1d6a06204060340e0b105012040003441003100465582c144114a002c045902030300613950304000711250300c69400c1c00d9045660081aa202c2142440f00403c20040a507001401c44013520340c0710f4010780701250501c0c02000052559400031030b5076070100308024100e050300020004119205004403402c1810300111701d50b12000c08071804460b120640b074001114041c9416241d00d074401c034090942a0390304402c0214410400700c0c05c449aa0383d0b0381299500b41c07141100c904001524660500d00f460b0f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 68705038 1106 68703932 68703941
    0x5010227090106111603060c0801080712080d0b030304060215060405061021020a0306060216030f0201180b032d0601020c060a03060503030309011d010b0112 69
    0x10603000003201d0307400502c580000d200e808041c10201c840103000c0391001c0c90030840c0c500c181e80e0312070420500908041200c60042071003c0004520fa03000015040700b15140f480724856505495031324200740f600118500602152a00e0074170489503014806000036120a03802041d03d01551402000b0003000035001d0b9015510705030500c54240c89022100080e0a082e0600002e8145004000328101c00018140d01755a0b102003140200140e0640002044902a03800c40e0004840c1f61203107401c0c2641d511004114010030454140194010203c8503242000c0c1102c102a090791160120040d80c001c581c0c408181c0380755a004070300c05400c0526182c5480c044144079616150020020350344000c100c2da494071481000c1070f04500d0300d10a401003c041d00024043c1c039264140410b01e140030b49403903854000c5204c2487c0700d00c1d0240105110b092603a10059480500d07008032102050001c2 = true := by decide +kernel

theorem cover : BRFrame.Cov 68525182 68705038 := by
  have h0 := BRFrame.cov_init 68525182
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68525182 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 68525182 ≤ n) (h2 : n < 68705038) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
