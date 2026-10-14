-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0884
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:26:58.173976+00:00
-- url     : https://prove2.me/submissions/192be9e4-d6b6-429f-a101-6abe5a53deb1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 158812949 ≤ n < 158992805 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 158814199 1250 158812949 158812993
    0x33813021804060c050304030507030f0504080105100e13050a060f020405030f01050412173706050f0405100b030402030709090f03200a06200406020f07141806030708 73
    0x10740e0051601341002c90150158041364450381c0d05a81d10382c0341018607603050b5007106140c09540d003040320500010a0034a8240304990007826012101803149103040c0120300020001492152219005101d820014600289480ca02688108042a45010380707100310000c0c000c55000700d42c14491405607504640044d07100303a014500030440301c00c20f0103034180c0070344100c0e410328948040c403070041c40002d00e01b2000e408044c0038809046280072404064510320605a44c807140c1e0703c800c2e65030303804080180c1d16141d50055000747c000c1d24244480d18040040c5420a5447d120b035454041002000404555041c403002c405000c90304800c00ca0700d801c038102410240e1102c00102d020858052101890740541400c6034804902130000f01040700641d590304015015100f01141c940407050007140b40e41c000384001d4005000c1982c0100000e00d0440c400500e003100039404030700200312540002c400c0741c4800003e180b503148504080111500e4030b0740443e28103500d40d40709a150f80181481580c2c030b0001544c0b00 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 158815449 1250 158814199 158814203
    0x903070f03170a02070b010e13120f08060a06080601080c070f0b0a0b0d080f09030f07170d0e0922020409080316080f130f1704033813021804 62
    0x2c003803a41e1072245443c12481000005840c2040f0b8400401c010702c0f40529840d44410141b4150711191072540d84c1c0803440c2c0207503508501051b8900305010386190710007145030340560100d90060784686400405441c0c6c035806005c1d107040044841c00140000f0068040b00e24299105229552901c081e0170038811029054665680e114203219a035089c0e172803c1c7e0580b0034a81c0d0041c001c2454401c10145120003a4000801103406009070b412401645100784011401020366034083c03680f9040200c8030380e04040e25460510203200c0c921310b5400311502c80b110030a92007040c142c80400303600300f010310b400c83d183d21980c0002e41c06400c4c040c48604222060000c0d600400544c500c140d0052820181510410740c1210320403074440443d80014044030710502031074280740c0240b50a0000380d8442e2203094113520f402c850030485100000b0308004110404072000c141c0702e1003a090440014610040200b00c05010950f81c24a030980c2020905800411903480400c9900604443d1a08522151907400c0c03602148e003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 158816699 1250 158815449 158815487
    0x19030b0901120c0504150905010905070e010507030212070201090b0307020c030f0f0622200f0a050f010c030905031e0c0103090b04080309100e0609060601021c080903070f03 76
    0x6406480581c1e648420358409034002c5814100b200f0b00000300f2511540710144400100c6c0050001d9132407003898041d129075a0042100e161505001d810386c50824105810020100a4400423035804030704000840074403d0181e0f038641090004940e002c015070890002420004180701809400103415480c50500398181c4031280b801002d215120054000003080603000140040d582c07050b4210355402031202d42c4c000c0842003000f5190010200c2042c0c1e00042d0140c001c582c1031601e4a0802041a0042000c5441c000a81c2c201008a514664401c9000381400b00382d00d40501014001e81d800009004090100e4100c204c2c0750720000004070b605001000e290041d80e084c2c030b146500c24040c0f18010344d0461601082600c0301e541e00013440d4001008001c060291000c45011400f0502400c054443c034140285440d08203145c00a040140c054811810765010310780030307501180b540c0300b0959080903d08160b00580d84040c406803d511401d80010304800003159000e00f050307042054000b4103075035440 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 158817949 1250 158816699 158816701
    0xe0a050a0b040501170706020607020c09180105040b01060905100f05090a03050123010b0406020703030c150c091e030b181f020316031a040b040f060b0d0c0302030c07140319030b09 79
    0x1100f239807200403c0c0e42600040e0011480200f0a080101c102078000340e0b00000c0304561280d407400070f421224140c8003260030030110401000559031101004010301400c565100b0701c1082003101a0800d00044005014041c0210300c0c40e4860391a907907900000c540260080c0482c0848001c04140c02e206a2a00d0103040007183c00840d0307000585080c0c3d4161007280e00203000003803e686083d135400035419070440300c0801035245800c88520601980700c1d841d00e1500c1764032070b5900b0218421903990042c2801552501410402c00c041001044001e411490454100003080d0b444a070190a12500b0f000c605402c407416036040020311a1a0f00951040c019102240042090707a081101512061440000546c982480c21201454550300c003e08102005000043d6550126010f800303581d0355602681c160384000c160040005120300801020b01c50030b103407c51440c07070312040c41804e901074040040c1030201e8441403045941010401c440161480500804807496440d0f40140038199041d81c46003e045164 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 158819199 1250 158817949 158817959
    0xf300102040302100c17040e0403030606110a020111030f030906070906090b031906050409050f07050103020f071704050618100507020d0b0603010f0e0a05160e0a050a0b0405011707 79
    0x200c2524140c82d4020f0580120a61201c2c00300e4568151840940c1c03031b80780c050f4140e40c142e0801c01c0100700070924035003804801d2405040203400c943c599030110080c016160203103500d0001c0480c0c000002c0398242002d81032103c00046052450145d42e1616641c46400024847c0c1000b000a9030343c403403100c44c0d603400c5c412030700ea1000702c0e10340e9180d10803008120810300100394401c101000c044007205100d500081c0c016541d000080c103580c030415054445410116010201610901101015100c05c0c01c0a43c504002c00d100c5400e0392007404405040e1400c01072040510100c00c03002c0310000c100040c50a501c6038409980b03d039090180c03001c0988100515458800d21a0084040d02c030f407990001c18210f105100d6803181c0300c00b00c200508041d070555840b01c00c0d616110440c840c0101a0304084002d25a648152510b03038030702503500748680200c3c0250402040f1700c2a051001651200c0070090108150300c0700c18048010301501c001c080d6105050100101e6100503a0000e17054072695181107407003141c2d0718 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 158820449 1250 158819199 158819201
    0x160504081b040b10020a17071a07020114060a030311030c061e061e040c1e050d1515050c01140c03070e090f06011b12111e0c0d020f3001 60
    0x891001e40160b0468103400d00460041240340031010403442d1f0143c541101541c84040010251615241300070b082410f11028070341c2482500d05809188071100b0860900400085201c0403d200041c03c01c14031551403422601e0901c141c1d014200311408a5683c2d0a0454600c58501000c44044900c0000c00c00043c1d041d103003e050741c0c10038030644a1403031842158442400042c120001c10030083c4010700301e50690420b9200c541200d1400d81e59038064030740300e01c019000c0913280c1c131440d031101d060038462041c80180b0000b00e103101181b4060403d165a10305a21000340500b151250300f005908110303040103146200c000c01180708066540e500c4c1c2c7c1c034220f030404014240a05480404944d00d140c0000b55481d401824520820622960308580118056994814840d00c03222003a001810301c50348d4603141e00041100041c2031070440c18002d80c28082280203503580150358102c0f803003a500d440c00f01c410b640701c03d10110f102a03c0508900f072281c1c1040c046070040d2280c60748000c010405022911589201 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 158821699 1250 158820449 158820469
    0x1b01030e0609010b011206050904020f0f12030307020c040905030405010c0c0e10031e0f140a0203011a010801050d03142803060e010f120b06010509030d08040b010902070b160504081b040b 82
    0x30007049d142d40755038003440700c462082408603410081030518451140c0da4032424000b0400c210004540e01c3c40c040d0002418040d4035a900c1e40614100380b44400010008415035050390320038607000d0000006814440082001d0303600c288400c01d107980601940ca0380f150000c0302a64000c003110407805184552040c941e540303005014046100000c00000002c40314001c524080c412101203410358103440d0000303800c4403219004040b080c50700e18242051540c2013800d09005103411078006902c410980c13009060050071340c010003900c800004041d401c0e00c030310108045040d0540c2c01c11a101c0080e00601400504003405540110702000f400010520140c46c4807005076058403004050b002c01956954414450241030b503418004103001d4040c42e9142001100800c640c2e03592001c0c1141028204440c0a200682010350001d00400010020402071210240c00191350f1028030f4480c85d400f842100d0b54040d03034005840034028406c0040421040e4070a240002c04215003c00500368400c04010540d60 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 158822949 1250 158821699 158821709
    0x3130c08070501140f0714030d0606030902101704080904090c030501020d0b1906082a25020d200909010b04110403030e1c08030f09010e0a02031b01030e0609010b011206 74
    0x10200206c2c0001480e80841000c00070155044070700b080341420240090303450715080600060b40d190560400e520704181d0b68102c0381c00d1414a05030f6912681c0314240a500000c001070a68100068805851386440d80407005264100d861455080e8030b034904507010f07502c07280d120103425043c5070a40320240b8091104840d580e020740c2c0c00c1c0300000e00e000d0040d110307103200610042e6050815400c019100d00c0a070014204405207400140c1d485450f001c00352106800c0c4580c100d01c3d0303842c0030b07010f10040e11204000c00040d60856648425036040c1d140e10f052030350380c00403000d8105440e50240452243c05400540d4a120211014080b41c4480d4100d0707407141c000d03880301500058661029034194200364100c030390701050f00c1d600e0f0f45500300c0648800010703520660f00445543d01c05c404100001e0402c0c440c0780031504101018154414071600043d80d034104002c601000114516850141c5031b0290740a0f41d900003036041601c5691034000d41e000c8c02030007e0703a007a901250940d804100f44103120f01c41d02090390 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 158824199 1250 158822949 158822977
    0x5101e020735060c040810020f03190209030d0210060506070b0a0b0607050d050301031a04051005061201090c050a08030301030507140103020c010f091511030103060203130c0807050114 81
    0x1101006103442110b0506111440d0100c50042d02c0d00031032051000601c036900c10711550f83c0e143e152481203803078126185540141321344148060382c1e104042200726034001203001a14003003049a10300d25402413040c01d542d40d501d845160056082e840d00458001c150707a104810421250342d444003488154030035414018101c00ca21400101c3e201c10076481810b0000c3d0140a541c00d0107030503600c6e00e2420100b00401400310b0f0000c40100b04001035088591101c00814040002a00346507551030303035540c449041b08000ca902c1c0c00000d00c1e5510380410071214210080001c2c8030900050a200304d101c03446004440c0203500c00107020800d1000041207a040700c0d8084001c041036031800d03e035030700c0241c411074501d070406030208203140a07140c090098102c000514000010b0200e80d62401800d94070088080e21426400c02201070f042200758010b580c116a000140507a03240d0300d104004d090320b0640c0400030120450390b100800c91210011700502542d8003a207405284098407100c211813401003044058000c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 158825449 1250 158824199 158824229
    0x19050303041209031202030d0f0b0315071202040b0d0c050712110a08041e05100f0503060a05030105010b0301060318120c030201062601060e04030c02090c0405101e0207 74
    0x2608151560340104040c0c41e0180c140c503180c2c0e0b00c61101c0c1401141c1040187c1c408104178405500074460b125001030000c40400502c3c0850b00841d803510902d8407808001d9540d8000144028000c01072409009089181195565220400c0903d11b401c41c0c2004d001c1e0701c0c5000d5091111502420856891541200a071020300d04200c0046a40d0071b10382036500c1e01e900070701000d07100041204024102a0014414030050303003041304800002ea0741d041c0d00003440380ca110007504043c04d4012000e010b40c80e8292a00b01d03566691034000c40d0301550fa540c041038041d86800c0000940314041e40c090340c10b0b221140d0b000c0c071209103042c440d01c170f400240b5000074100300e065202c2860403a000b030003803482041c424000850521b03596944c0c4d445100011044c243d8079180440d400d4003c03a028032810002d03048541c20000e840c107090320004c0c040301c18035400900a8543c400802c401c1c8000c5800e0750024000144202c00c804480304005000b050314120f81078500d0f84841c0011240c60002c102031041d609804610508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 158826699 1250 158825449 158825453
    0xe0705060f03040c150e18100b09010504170307021005030405030d020c0c0409030305070e01090b030a0b0303040803070c1d06030a0204020906070204050903091f080c070311030a111905030304 84
    0x29880034008a40013080d9010028a4044400703410316815030302d440700c5070098030110038840c0d1110798100e01089800050f041114125404030601c0c00da800c3e1402e0251109007040050302c903846607401500c1440c02c0b030324646029503000002000c1e910b100f80c1c0d0800c011101242c05507001c2c0002e0350001c00310340050100e1680d00030640c0c05071405800b844205e0b02c03207440c4080850102c41f03400341d059000a840700b08010200e600201d4041d0703012000e2034500301040c504024243c0134000685041c400c00d4a60300c000e4040c1d6001c000f40c40180c040442601d6454000d40f40810060b200c0388190315100341c1c0c010092128182d401c0720180300790000f601605000038542d080100950000700641d0f40003005000364000b5860300c1c41424481c4440000440d9a10000c004110031040703202050034800d1028040c04201e50f41c8441e15640102a1500300c94841480d803909440c504100d80402d8598070000c1513004c1b010354401250881c2c1403550058880390100c1d00c0c05000303d0a00144080e107150310030000721340 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 158827949 1250 158826699 158826727
    0x501030f06120b07110c06030f062202180a05030d121806060e0a09020a1406070b15010e0301020a0e12031b060702011a18071202040f06030e070506 65
    0x4200d0362684000200651200d420b00411400b00009654210340301c0d042140840d00b042d000c050120304034005044c3c5600720000180c141c44020711100c0b05240c400b020801903120850300c3c041401801c0b2040354101c10010703502001f0b421645120110180d08817a01285081508001c801d0f6030019014000c81254100b0603036040e0b64640044498541d1004403501441080d0300450003075105c5e5502080c042d20f0402e00115408024190007880c03417904096000507603d40b03900700d0440e003404286090140e40400082c2c02c0e80950a80036284240c90701c10040002844240d840140c002601c4910b100c11641050501300c0c050f00c500300b0b000c5000b0307460701d56862a05000e0b42c0c086c2079044080342d1404600c00019402d10100c0304050240f940501d0620125a40a0194a06c0c0341c03111008881c0c1c15805000041e40c00c07100518450082008a004c03851942c0700c2c000d80d080003045050190343d1255034107401c01c0288400d215020009107032459000c820b0501152030740886100600c0e041c10210f040179120707 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 158829199 1250 158827949 158827961
    0xf06220519060902120c120708091f0b1c0506010b1804110304031709030301061d0901030302031b0606090703020a1b060506040c020c0306041202070503030c0102070309050102030403030504050103 86
    0x202041d0040700c1501000c0001c0e00440d40a0003000e4400742c0c80b803903148401c0001a90250005002500c240706251981e1a00540250b2140f424541460281c440d0190241010740040c824400808003020540f07020b4101c0e000128140000c0c0c4004801490035510048400700c82c1200600302d800140040049080307200141890400055510794007200c1003002501303d0381840d20104ca4440048200300a050b00f01200c3c03544900380980c0015546408001580c0f2403105004040034054050000c03180540c00c800c440807c602c0c050070301d2545507101e00f4081d603240c01030040d0354034603690707542003007030b60340d40461014043c14014068400c1a11224030640181d000030340d10004210002104424160320140344c9140f140c050f58000965007000410b201c16120482628010f5500c00b0490721019107001850b40d500942050031a500320741074980032414070016501c002d23414400440e4150031800b065005044d00c40c46502d80c1d200c0591b985006a0301c9025910000d0040780f404e00c400c010b254040e400403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 158830449 1250 158829199 158829211
    0x2100c030c0209180303041b050d0c0312050405061303060c030603030e280e04170306180a0b04090506060a090e0a08130e070c03080f010b0906070c0801140f062205 72
    0x130124000a01d030580e441e6070011101641d00214082002542050780d02c0b8080141c4019150b9504052058584404a100070b00c001084da00c1707002c0d0071820442c400c1d0141c5012b801c004013510744c0c8441240e8032241c1c01c5024001551000d02d00b80e00700641314040d00c42d88048a03410344401040c01185000c1001021079132061401c41d18030840c00900004860110102900c44400c005031181024102041140980000c21180500800c28000b0707503034503c020343c4210550414000f407155200c1c58004060201c07030f0381c42d40d00301d400c1c2442c0504105021032058881c5d00e0a44020300c61940d907202c000c056803008143e900340e54002106031070101d00769000501c40003c0024404103010b90390304041c521010101d40010000300310b05542403c00d94824a440e41241c2410180c100550408080c2e40d05841442c2c0da1610071000005c00c1010010b0f0706d4461030080807008002c00c440c3e40c031022808410002100d641c1c589400e003000041c0d00d40340c003030304001e07c001c0710b1500003291008034401e0300e00411001d000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 158831699 1250 158830449 158830471
    0x10f05251a0a02130b0d1407020d02060a09150e010b090a020d0f0501050904020108040311191211100e07030c0303030905070902070b06040e0c09010f06090501020a050a0f081309050402100c030c0209 87
    0x72034801f216071000718000d000c0d80c0e001b44500952888000d05019010740145406400c10710071601281e042503a00140b4200f00a0008100a00000782801890503845140e00008000b007000410403007540039002a1a0500b420304c0881d80d0300080d001140e00c240100d560002c02d40c4007103000b40d4070800941c0d40c071910030700f400010303407014080d00c0d86010080c4134001501c08402c4010000c009401d541d58000c07070982d0070010482c601f11960503442d41c1c3c03021102100595186410300d03100d48200207035001590098084075029481c0e0030000d01031724036807109407810b109526001640d619148219200d40c0d0700b041c4851036a45960041001070f0449040c41c80b030703071b114513040580d280c3d481c1089a40201041086c25040d2490800050803095aa030300c8641550003000d070f07900100d40046420500198072298010b0242c110786054042801446072040141c500c41001042c81042075101d00d01481c000c07510311140030310425088400c44490100140007c0c4504d0301c00c0d005081a440c0d250304110075501c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 158832949 1250 158831699 158831711
    0x7080109021807180b0414042903032101080f1b010e0a08030c0f10090201090306150e01090c17010b0d0c0306051c0b0105010509010f05251a0a02130b0d 67
    0xe07801840800a4010132400403000404205010a0302e0385014030400c01e4406201d25061105010802c0c1040d248070720b810780241a89d000155014411210803100380c50701280c484003070031420700001c0c000340114806407080f401a21103042c0c0004294040074240e0001c001c5840c02d1400440d81c0c1242d05402e19080368882c00041000c1c807080c4003070107075500c06ca001000c0b01116030f501c1624001e10440141c10341c038904030305000942d03440b01a800942c3d0b003210001c41e489406049010603100b095100c101c03003010040020650349510b41200c0601c01d096030b1156801d800c241c40341d040d84882841044e96000c001c110242019015401c8110700844504002814a42c4d80d400b069901d6120782c044d8541c81c0c140c441207010413080d4900c2c140500720a191190130485642e0010345000101c001000c280400800d01d5561800030020120103900100007003140c3c0c0d2254580b0481c03031015110700004080c1c1c1c40340000c2c0d1090162007540c030040c2c00c070541080c686140c1070005510354080103030240f403607854031 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 158834199 1250 158832949 158832977
    0x509160509010519121a0109030204020f090306010f0f0b030609061c08040b130f120206030411031e060a0902011d03010204030f11100c0309090507020f100e07080109021807 76
    0x1e01d42803400c61680d141d41c98541c01d140804006c454501940e41d001d0403044503034110030f9030700900c1d00043d42d0341501c00580d01c080641103080030f4041c1140c0c0c0c0398181708007400440c02d20040781d1043c0455611b8292802c071307951121300ba842c680c00212041c0b604000c1820020706689048880e510000d04d0580c1c1507183c010720382c0c072144101d9005802440c03009100003940791242c00840343c131f800105840014041c0a604121684402c6000440b01a11070000480882e05008400c110240796840080840300d04400507071034140b190001080c0980326004d603000040d40c02c0e6107030081c541020307416034660040c0c2400ca107406050341a145103441e01036500348130100c001203800341c52901581c0911034000704458603d04201341c40c05030315000c80030407a4003125000000d4002e001ea80036913440c0355011606c0d0341c800030100d00d401c2001d805a201480350b10046803503a000c95016948956020302900c607000d84034108203080c0e9614030740080d00810901a06203c00d40d503501900c1d085103a91070100c6150780c2c00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 158835449 1250 158834199 158834227
    0xf020d06050c18060c0606010320030f0f01050909060a2c0f010b031f020703050702030d030c020f0706051206010c08070605011805041a0603100903080f0105091605090105 75
    0xca42c940300410b000604440004a00400559242c01c122903051030511030350202d42e1582c2015150605140d1100c80c006560340d9420800105020303071a5101d5128580040c50b40c50810f816580031203240f1005001240c58280340b80034038442d1502800400769915500743c0d410007055501040800080c8801000d2101d0f80c0d04201c02c0c084500c80c0d002000035a510200c2c1c40d00b12242b0f030380014032030380c8100302c0e000d0140a020403850030340308120301c0107849150078101942d041c820003030001d6060090f4100403003055095400448d00c01c40381e03804c0340d0310360301440c90b0550f65402500400010480c1030110030320344098a20101d074803000624000c0d075401c902d66103a0f40c1c140c128080c03c8651586410050210441700701c031004200d0081501800a0708181d02d450041c43d10700718400b205070300714400089054800300807024180c0076650040081c4241410000c004074410344031070030101c1005000007a03d103841c604850080341c140121041400d568001640c1c594052500c081c140607050040c410300b4804 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 158836699 1250 158835449 158835451
    0x106030503041d07020709091e08070b010902030712050a090c0b030108010f06030215030402031218130e0613030c0501090b070e030703030509010c0f06021801020d0504080a0f020d0605 81
    0xc9040295103a50400345003414100c800500c1e0282d80c0054001c110840d40d001610300211205228001000c0c4040e050080d013241103001c00640c0001140045420403030700000800c81c15000d012001000d03626400c4400903448145d48150019641030455144600c1d16846640c00c51485980081c040c401755807030101c0c42c2c0b07440d440303144800340c040010000d10360280221407100414038410800c003415640017900a913102206560003100100002d002c5460800401c0c4111913074200b03041d221a42c85207800003041c001d94455005004880c4006600c12650140266920307040020302140e640340d100303840088098250641c10062800f480341b012a00a00c00c494541d809900c0510341c41c0340c01d1001402208001c41d525000c1c0d4084801040426842400e0b00c100000034a003005130840c86081c07100b01e010340e096018000318400100d5001080a01d02d80803040e9a003070702521b4010303c28460a079020701962181c0095504040c14440002e02080064844548020541c0740d002c0000d40f02c00c002c03540 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 158837949 1250 158836699 158836703
    0x20f030d18150905060709050117070215010306020d060e0f060d050a0b070201090215120f130c0b030906011d010b030705190908060c04080c0402250c0f120b1501020708010603 77
    0x70f5981c1d414024014140820b690000346810414031707452a140008000080880c050b8800124200205841c0c51080c0308201c0202000c20050303001d56140d007000b000035448a0a008036051501c0780014901b4000103110740324000040840169507107907402e001c080c14404000b29414000c10004a00282c1c0402d0880d0140209a00000e80c1c07050900c127100a1110103079009184010500880e200020b5202c01e42e0303407141043c16900c1e51034813000a02c442d0080e219000070814041c00d000481c4428000380614401d11046c4100e8041d030340d0302d02080c1e1032107002585c68182d9031100c03c0148043d09181004580002c52403038468070342040d60f20074041d4cd460380b6802900160f1500001c0100030010040d407030b00401100829440d051825410b140c0c0e44404003000ca004d42d8001c500c0800c0d106041d40310b4840c440000c12000183d2610b42f1384002c50601c103000318007542985481c013043d0301c01c000c105800940d902008040450b1503071005119010140d4001c0e034114884e070311021841040c00e01a080c0214 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 158839199 1250 158837949 158837951
    0x3020f031e010609080307141609020706060f050a03060b03070905010b0307020d020d02030d0504050a080f04290a0516021003020c1507171e15040c020f030d1815 71
    0x80781e5104050340441e0181d00c5802080109901070004400200440d00c102c1d6216000080c00c0c42007101490401e400f0380420500e008190100094601041d002400c15521460080203900d8039506014600d07103007809880d40086400c0000c1c0001010385d842803912550050888404984e40d407040c0c170656200341c020281c0d82c0c030003100f40b003c801d8040120614130056400a401c3d24120041e000303607240110349412444a031594081014000d052010320320258009001a0740d681010300742803030f1944680305454000c0f11010204000c1c3d0f0f403042904200e1502e06414624010b0010b408442581001c8a69410800340d0514100180e88130f942090008480340c50250301d6089502e05d440c1007034580030110f400d045070841040000c0c0c0d03020581c3c5031507140140311145a0f4480440f01015070074020701c00c080340d12030300c020b110b8600518403000c5002a000c680034803e000c0104400c030707112201441842d205c2d43c4144081c2810120326042411003550f02042d5101500c001e4440410844106220101003 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 158840449 1250 158839199 158839231
    0x70510050a060e09010b1e01030905030c010209030706020c0102070b031906080609120f0316171509091605060a110109120801080601030b041104020d0c0e13060501080a0c03020f03 79
    0x10140c3e0040a5000f101c0d20300030410040c20300b010414400150241611086090302181001da0081e482841d003240c1180459807a40c501c606058000d520104401d886441a40300008140b0f1000407600d0600d81c060340a44202840c10080070101c0d00b0290003007080a8011060010701c41c518442d0200a01001c0000d0180e810050101c1341441100d841c0941856000c10401d800400881d040700d42240143d94554841150541c003200c100d01c4130240522427200d404240444c0a04003840000d0109088400250a4480d070f410255140c2c0d0fa0591030035500000301040080349846809480c030b200a41c2040494403075203d14940c2192841041203582030205418281c0c05640000001d000d044c514000709000d5045480e01c0f00e440b00020030051201104100000554603160103507401c011100406005451105d00e003d4514616140040d01400c820005078512908a0049008580e010784030520242c88090601020f482156017000a044d020045001003c1080000314411070a40800c1400 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 158841699 1250 158840449 158840459
    0xe090105010929190b07080d06060507150b03030408030a05250201142206020c041406210708070b07120302070b01090b0d120309020301050921070510050a06 69
    0x88038180d10b100e650140000011082120402c800716107a100d04680600c454001340328411003108058001042e00c1c140410150200305805014002001044005104043d1034002c11125402140c7c0c01030912065508008084880d540c4a00026034010301513074505230720350345410301d10b6001e0101c20002841c0090200081d0544c025407080b4a070b06250202c46401d82900001c28091501084103c4604001282000081040c007814000c40d223100584090700daa5801c003944842040034814080d500704181e64022142c141542c603c180c01c002d011500c22501e4020388500b41d10407009001c035902c00c1e060003280c400020403040005000410040742e17500103614180308001e80c0461040140360050150700001000d4416490540d101004c00041d108044000142d444600c030001602c1c9117041400c0382c000c41d40c150085007049000344c000380055200d199110b40d030342060f08a07080b1447c604074842d610840b0040c000b000180c0c01750048803046010001758000b200c500780d40d55040642d5075202040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 158842949 1250 158841699 158841701
    0x90507230a09121703090c041103040506130843030908070b0a0c0201200105010f120206040611030c150118140a0209040609150911040b0f070c0e0901050109 69
    0x1a0020180325054200f00d9542e00b01030f924201890300e21400c003c40081c411078820040142c6050004000740b08000842191034a6030f401580c0a49083c000c010000340c100c80100228014550721440c80741c1b910000525a07014a152000059480d0440c583c9039145c4419148000d0326201c2060200070410180d8500940002d00f038bc2c2c01514540c11011040080342c590340103941c0000b600c3d05255540190a1004895191030720182c070313841040410309040c5410301544840c0c10b0340c10880000c480c440d2100140311464115442c000e6000d0803c010500020f4840c4601c0c0d60402040300c2100d05240d4403803016810103240a524101d42200344004211540741c25a42211058100f841081900c051402502200380001d0108007040d03000604043c036500e1325440f0400401e80c0354005c001004116446040e458054030410755201c0c28200b00d0064420140c040b10308130780b18400d00c035180c80294820341040d508051825600342100d40000a281000c940e8143d11503014040009059814405044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 158844199 1250 158842949 158842967
    0x10513090506011b0302060103030c08041e050112020f0f0a031407030507020607030b0916181e060509010903031b0609150606030606050a1d03010e100c030b0604090507230a 76
    0x14080f46030744c82c40c4008a0b4001c9240341c15603815180803240c602841c14414011305ca80e508c04105248030f15841c0003038252406c4410155013099907030405d201961006038059024005810501e0f130420410320b4000b000d044020024000d181c2004500341c101d002c040d841c0101c048a14402090725802004407040d41880041d900c161141010400c0d8070050000c5481c100300203120303100c000140c5411000c0d25000e1501080c074400080340c2c900307055848040c5115521400c68a0b48101004175002203186402403043c0e844400301a1b560400c40713450f43d14100c400d0440e544080603444602040c03207020464a004801900707008a503040c02064070b2411103002c403001688288209850175000f032080c01e90020813602d00c0101803424101003c1c000044c0c900c0e44606549031a41986420040b400784407010590703a02c8009042000c000d280ca2000b0150191422203040c00e82c401c108110a000d411004d034400c0b5040b4584c0d10b80004030b242012540c50f011410550b480c40c407004042683c14115600c41710003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 158845449 1250 158844199 158844227
    0xe0307030210020d12110d0c03110313020a08010c05030609130204090303060617010302031905010f18020102061e07050c0319052214210706051c05070c1101051309050601 75
    0x201b01c03007410881c449a59029012030719000540390607050840030310940088899490701c0000a0340d03400c02c4071003621943c612000072170107402c40350000504000180b15045011100351a1213146035695410003030030850042400086002525158025072541d10580415a120703480c0000e9450802901801050b200910350032000100e500520045c0c5010076407660794400301807280358100301032610b58098903000105a00c0da618000c800d20411841e44219040f1034001e80903030f0f0381e03074440e020315110791032102c903043d48500e5004d03000c1520300d8407460040136001c1041064078108441907910301d00080080d00d6440000340003160340c04030400040301401c05209105c80c400d890a01d007030f4840304186004500a881403801c602040550de00c81244035500d54501070507140c100b900c2d03901c061f0030394200e061020321905660142038807024142c484c1900038005511507040c640041d41d558500c18205070300450420000303025881c0c020300c20000d90300140081c9140403606150140c00103082c07281e03103c00 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 158846699 1250 158845449 158845451
    0x70801050d02030a0605060d0204050906011517190f0c0e0f0102070302010c021203090303030f0412030b031c0519020f120421030203070f0303050403090602030306030d0e0307030210020d12 83
    0x10380401640c0008055210036440440440e40e59a8000056550023200034041c4d081403c00d01006002c6001143c1c4034180d503040c82135002201c412000c2105e282c0c200c0348d122080e0084180204881000b00c400d407503000300e2180e0010494500800e0600140c1d4240540349021540d03d21000d160b0b46448171038424240c1c001e200801d0050302d5a000245070a00001010b4054000c46002d0700c00244140111400d00501030b08403685e0f818102d0740780d00d55201c12641514503120001c03010706550711034000da138490500107008198450041001c0e1982d0b401a15102c030074003108001c01c950081440f51000400201900589050005804440d04001c84d8403000c0701d02020070001030001c3d071100d81070301e50004952145121880f5441c03130305902d50301c04e0b200042c01150250355148105030345a04410b100d10710a41c0c417040d480796102c2c400daa590100ba1881940754024041da50880d501c11440e580000100408881039541e40303801045500480d4407030400182c1040240301d12080d04140f903207a140c1a0308c54 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 158847949 1250 158846699 158846719
    0x60604020a0923030a0b07030b060702010509010809070f0803070c3f06181209031523011e0e010312030207080735250212070e07080105 60
    0x4401008074800303000d82c1c0306941c5140803981c10540745000c80300c3d000c4000b400b103828240050a06c0081c15104551000c0001e080c442800d03024200501a1552264180c55030b500b0810100300540302442d0050140f081c920a4280000300c040c03905420100034917840c1c0c00356035030309058200720b008905960003605010150755200440d503034020841c49403410356407000307040c982e00020221540c40842c040c003a14440c2403011a40c8400650010345400d18440c1105840c002d200002c180c54600c130603c00542040f0010440842c441c400380c02c41021700c2800d0190038807906c001046503902000c01c0e080a8203207034a1003a021000a449071156010300a800c050011303e615585e200070391808641e41c0503007090380100c1c0850030042d030300c01580e5003994007041c0d4030800003540400605140840c2090043c464506541242041c8041c04942c1042d8044d4150005643d10f6000a2440d0503103d2089801048032900015031030418440703038010309844041c40d016820700600c01802d290301a04518801e90f0515 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 158849199 1250 158847949 158847967
    0xe030403050703110d0c080c0117070807050f04030507091b140301060f0e0301020a030b09060402040303090510110307060203060301060b28030b0301062d031502070203120d0504030206060402 84
    0x1032000c1102d40c000f010132050f20030600421040350001000610400b065040440c03516000f02c1e464030b4075402070340e881343c04400788086412240010780e48079000c40c202101240c0030600c01c0c4000d01e140c2d0b0444043c1458107a80381c0d250303450691a40c0c0007400c0203645d11351115056000311502140d480c21482c2004d100d9055000510341403006200750f00900000c1c4158003103041c0284282c0c010039200400071521180803410280240a024003c035201e0041e020000f46545011710a0310262034060350f0b130304080c80c1441c0c1400b00a007003a5840c0d6060102c40948008400010001040c015214110150b01d0b824440e060600303464998012a0703401c48207021100402a51844d60310811104c4034500c61002c60355041174009010403803840b6059400c1400125140c003100c00e80043e5005034000300d606140c1d050141c0c920b501904d00000b041844404d403440c5e291035003074020301400e900040680c7e9000002c401c028406174400849c543d4083c0d11041040241038041c41542d0740284181c409500d454084 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 158850449 1250 158849199 158849203
    0x623040c06051612050702090a0c09050f06040e18011103010302011e090e07020a210f14090405040b0402040b0f0307050423090601150c020303120a2004090e03040305 73
    0x540155020440c2c00300b021580d4012540d110391074540c00854030900b009924000800e107521081e8282d0086810b100800c10210903482903006402c0e072a07841c4443c01b8207002c01c1092030b0103449000cc0e8011010300011801e000000981e40c00361a240c014407500407804d02c0d59600352070300a0a000c0d0a814103100420150341c012003000d003000400c04d24400d2501c0310010540b00012030750400c400d10715512040050954000030b422000c03034064100d94021901160300141244103060410700000d000005456641d40070304000300e541e408e101507103420300424601182c04c0715000c42c0c0075500440c54800348000d606180c41410499030090700d5a41c50f814980300031030395804040c030800340143d50395110420032400b421a00e03480c1044c50701c0c402205007081ea04e441c1d0780300b10a001d401e406461080d0340079103d03800340000710300313166010300038609000c0c10901c10004544010b01041620341c85010f118900d4202d014922441a49a00003039103a5080281071811140d1a803c5030b0102d0784100401d0010800c0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 158851699 1250 158850449 158850473
    0x90506060406050706091406270c04110d0509010603020108060906010903141f06030308060a0305060c1e0a170709050306010315090803090703050c0114120a060b0403062304 76
    0x2141c1000e80d92604c5519103840209003100001d04500141c10800042010100705580220301e146a5036021501d003041d00951440c9074098107440780e0001400d100141415004600300546003c040303800d1a440103241d600782c5000319181e14591355503200510456070400da01c65040300307007510f0080e01450201d0000c1e040340310500010b014590400e403080311048041003000101d461203440000511401007841d40940b0090000b180482d01400004103241410ba8101c0201c0f90040000e000c0d94484140580455100340200f5114900740f6580c4107814000e80000d04490311140d4a1141c05520a800d904020001814140400800090400142d60700199060641e6044002c40d07104108000c03074a001000c00540c000c0181c003010003007000e0301601003900c1c1c044030300070b0040c0c5580301d000c8001111007031001030741990381c01070501000244001c4036690710342c441a080f90025100c2d846080803c4550496482140c8254898440141c4207900b01481a01c004500c0d01401d481d003466a42c910841003 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 158852949 1250 158851699 158851709
    0x8010c080601081b0c100204092a030b0d0209090f0609010b0307031424040c051c0b060a0b030a060906090e0d051e1201060e1e0d030203120a0b0102070905060604 71
    0x951a9413811407410011280b05000c05011a0618540020b101c0040c1d0001c0c41480445480c280c1d042055101d0500640c0200da6400c40188101310080429802080c0c40d030200e540000c0c0010f01c00c00161110078081e4010402a070040c00140003404c45a49015030062950010ba41001108015074400150b22403e07203502044600302204040081c52818030070b02e100407841002090102e41e0148078101c054000c90040140e00c1400c1d460b54140314451540050303030000384002c900303110b0100d01010030031504904000d280881655480030000c5c260781041c0c0e90402d2032a40c40c0c0040100342c2c00d40c801c4078014019442d05003ca074220030085c42d11140340580c514240b08001826a500c0808850070f02c0342c1303001c00d28104d5152004c4a0390f940d2222001d000303000c0400c181e100044d41c00d14110b110100d040300b187c5400d0401300509014440058082501201944400d06c14405280b000364001803180901540020701f01022000081c40c01e0404d90000b40300500d8241440583c4d141c05d0125000d0390 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 158854199 1250 158852949 158852971
    0xa060513020f09030304090605010807050f030610020109060903120606020a05060a051801060306060f050105030f24030f0a170403050c060a0c050319081006050405040b030319050408010c08060108 86
    0x10303000c04588411403240c9102d0913494000090045401c06081d48814180e40b001e030381c0d81e40a659495015a4544110700c140c0c210074009200050722842c00382c028109681380c52001103a03012040d030310031054401c1001c088010885001d03079010b414003144107079001403002c0d20041101044684403240c6540024107108070158540c000949450850300740c10808010307280007000025a00d080000c000c1059000b590b004180e8003d00060b158401c01c181c90103031b4003000b441d01450300d5000c4542130300380da0a1100319040c124400392000d29501805418611201500a49030508142c60004c501c5100711072808441e04092100b80045500000d569481c054144d410a5132455400b00507a00300c07000e4103009010344800903120100c021124110000640d450311001042d49500d6550040ca20503800b8010024a0500c001c000600e07042d00702082d40c2c01c003e0180c900e000b58544816443d4048a602d030342c0421400a000c003d440c0c024800d2140080351842d0507540d80c00c040000a0220f00301170300144440c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 158855449 1250 158854199 158854207
    0x20922020913120207080105010f061e020115080312071103250c0b19030204050303160f0c080601031509170c0114130c08060f0414070503010f050a050a06051302 71
    0xa240404400b001075800a40181c403c1e030120310000d41e41d412500401308907508140001070400c0310003211406940842c0c444105142c2902112030104141500300021592103101c040321352025200601c02074070311880a142d5a103403c03080003000d2031000d40301c002040306000c401e0005c10401700540d0107404504122880b03507881c412240416003c990000380c59051605400a1090464401065050490059200c03166203003c4150103d024a01c103d6405030010050151200400216012824483c4c0008082101c654507058544c10744c5400111b0a5400701005000f030105910300002c2d5006844401c0c803003400b0941d81c0701c5940308041d80d0068090000305541040b030301e00f034001d031004c252410200055850020942c8100d00301e00c98041e181c2250f031040120f0f4225011524510070440000000c0d80c940300c0e581d078080c12410341070440956000c6e402d40810385940c28014908075458141001c1740600340105444103ca4020305402d400915001c0d00304500c1c1c03603401010340c0071041c03003a0068503 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 158856699 1250 158855449 158855461
    0x10c170706050f010905060f010909270302060f0f040203030412080d051005100201021e07050a0b01080a03030e0a0c140102070905012603130b0703050c030a0801030209220209 77
    0x200e009164005081c982401d08002d040e8041016060481d11480d00034010b94031200284900218204045030009801c44030620403216035801040c410010b07000c903403003000c3c0c2d8020500161318008a04a00580042c0300348051021200213443e000072030b0866010803400c2c42e40c000b071303031300d11441c401e404e516416030780b01130280100c440542d4500c00340030030140610702c1c01c0081c0c115191818001d0340c0c800c001000c12000c12030b2051080c0d0300140c0c400e500c500d0342885c0880140340706410080c0121141e201d524410350020301d90004280c02420301000900648456181c00340540d07035149450120340d4010703001c030400302e11404010300481d660120515025842880101e0910400341c1208206609003000024400707580d00e26110b0f00c41900074100e185484013140a6201e10901c100c3c0c00a035205030303005015200e82c0c08002e000c907612906000b494000ca4090f400c2c150f820203800d500120780f0101c010401d5090143c003640c0d00c140500581d00350480d842c07400320030a52850002034022014a00007940e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 158857949 1250 158856699 158856743
    0x1510060309060f1805120a020c0d1103030c0c03010c03020a050304150b03030a1e090e0c0a050d05010605030402040c02070b1c060909050d030b100813030e0618090c030105010c 77
    0x203101520058180030000080c075602000b01c038211812030b60362280c500000c54001b04a0244d0300c60311519405001406c6d0000108a40c4900d0308005179646898240c0b00c1581c0c1d9006c000509080300134801a007040c00c0e40314101401c50703c0d0b2044440a040c010001c04560aa10000700d030740c0140e0140300b01c030304511050b08040041c5100c1062070341621001500440317058210118400340103504034140202000c030300044070b00b01900e102d24107101400c840072406140c80e80000e00310700580c52401c1d5080c01940100601a504281e0014021901c000280001e40c01c0030301401201c90018002005540c0c60071522660328495414043c443c040c1070740b141060a00d20350014002001c0425080c044161a400d000b5144c07401c4c280a00c1c0440e103000700251640c00c10280c4001d1003072480d01c0d041c2d041d56035240b00756801014031104408000001007101031965503100500108a00e05200c1200280408107110075024050404100c1180901c01009288e9020b01d01d01e201030303400b40c00284600b000c0c0002e01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 158859199 1250 158857949 158857961
    0xc090507050304030c1235010f050a030201140f03040f15050f0a0e070503011505120d0509010804020303090907020c0111030c0c010c0804030602030106031a060703020c0111070f080d02151006030906 87
    0x41f2042c00d400c03503603018100ba0301e242114450b41c054404041c0c0d0342c1d02c004444003402441810b40107492101c04002544c040c111880800082030b00307051030100036403d40f40d8942d000b26401c5603c000300303020a0041c4107030780052094803000c0c5070040000b0b081c0880800c10010006281c1021580c60b002414101542400024010100580240607260380a041c00224115a000303240c028104c045e0100000000054054a541021784565140c0360103800116603079903005005a8241c0b00401140c103454403117200c0741d4450b05103a0b0186c8209000c2800051091048200f040142c0d48203218280211801040c102007044007400c00021520f814039001c4900d002369070000e08030704d00c00b000024401e505600109012403044003082d0200799010104212401450806401130307020303880e112041e5000340805100034212904850b405580d03000760121080d02504110840d40040c1664400c994040250102c041440e1a15821926113052040710f0031010380305440c10591031740100802d00036194001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 158860449 1250 158859199 158859227
    0x1811040c05041206050f070c0b0103020f0f180702060c0c06160201061d0106090b071e08090d0f050d0828062301020c060f181203070c090507050304030c12 68
    0x31840c0c0c20540c10800010171040b82c1006000034481c1c002a5102d100381d2103210503561144410080c2c0e400c603001e105250811410150700110108400142c9550300304500510b03080700f024201ca28589444e000707040c100301601ca9200e00005010040c1521400b10322035a10002c01c00124041461441c4103d014020303981c040e501812007a21004030700005601410f06031035a54889042c03c0c1c0c1d403128170030134034410044040c0c009410ba00c00c0100341c45084052051840c0201c000c80d0500940600149811a1440040350a026481800c408100c41030020107003242603418a009545002c0040852000403600030450080c0d11458041031048290301c0340e0041c0c00001030300b0b40c0440130165100d85035080100400e0143c030480602566a16112048603240a001802c7d1418465a41904400d201c1c2120340d81d80d1100303c3d20024a41554200007a06034a13008002d1102241d26008000c81260300107072030501001401c00810012a8008403d151000d50145a0300700780305101d241190700750507031040 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 158861699 1250 158860449 158860469
    0x90f011110090b012d05010c02010207080607030f3e04030b01030b0106030e070b180111030a0302120a0c08060d03110a030503160302070c150c0b0103151811040c0504 73
    0x108030038007003045030f0389050b1140c0c0d1413148032000301c4144520809480100d00c00411002902c1405135520403182560018810300403160fa041e01d446000d0b0900c002147c2240020380c4d01d450702c00550030b40707005d01e41400311404501c05040202544100690300c4c1e0f00645100c042d480e00c44c03d407218035502c0071500259004070a000640d42c50b4540b54802c400c0031320528002a040546ca04c10320540843e19904541c00e000b8000e01d03028a0228a005107501ea06180c0d050020000144929078030500041c00c034404269070040e928111000703075401d0400e0103042800300d0340c40c007501044504e821814003500110f00329402c82440115180403030f10400964403101d120301442c14448209504074010398094070314500f0250600c403503000228124041c103c070103056001588020081e0302c1c131a27031006e40d000503645400441140c680c0c44010701540207030700444806103184d00485002c80280f1510048644418140c0c0e01d208031134031070303906005605119a04c0749654102001080340201d04560050459140c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 158862949 1250 158861699 158861711
    0x1a0306191e05040e010b0d031404091a01091203020d030b0d1e0b01150e090a020f0c0304050901090c0e040b060d0c0e210601090209030106031421090f011110 69
    0x41d4500d084145403050354026030420350108040c030810f004201d2036450103481900f00c109940c034115810791055a908002c600200404100c619480c000d540510042032503120442c0511000108800d125030b001010751025004900f0019501140d0131060000c0361074003003a804241c4000908007c0321110081c021404821400c1c6441055038046038258011002c0e6101680c0e20490140c06403101100a00007941180041c003452130b181a226400010007800141031813011800440582e0001542040036840410108003610300f1541090241522880034800280c009501030210051101014400c0c1e440c0c00104600d5101c4030241d5408554040040c402c0c00742d8084080c0140107082481e5001d0080440c000c0b40d1480291151590b8109040042042c1e070300e4600020025040308034181c0d03255403161000804180150f00030024910400c0c090a0756050407050003110303100c00e40c000c00c0e00c200107000e0707580581c0c0c6941054406000c2801c3c00d0300d400c00030b00c5480c0e0405078076024140000740760003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 158864199 1250 158862949 158862989
    0x5060106080c09120d1205220804030c080709052401052d120105060405060a0f0e090c040608130c090209060f030c04030c080102090904112d04061a030619 68
    0x74868541710069141c80c1c0110f010b42c815102594130403280d025000204030070368502000004800e45107603000c0c0207a1400c1076103c0d5038074024036045a103c400b9a5000305414020211a03202e95a0084000c4030400f8112441a01e00c0418822540045040c0140031560160070110071794109101100014004a0a0040020344140d40c000318076281080f82c00d0000490242002011502600d400030f000500707081680000b140c0e5500303801c07401c03010050300b00e0000300705e5200c2ea044d481c000c160744421181c81d1030034103200400080e00104204800b640c07402c004000b0510703407003000f01600c0403c9000759030380b25180c0110355a0b10810030307410f030751a00c00000c1240d03040440c000f80c801e4030303c5421503240c66035035030b640b141c00e07409590704495108241001180008035044411220050044c10451a90b01a042d400343c04098090140c01da1101701c101c0307102c540c13400d84152000b40c110580c0c0d0b010050054150a03039617000042042d402980e4044014002d148010400e500400c024410075841e90690 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 158865449 1250 158864199 158864203
    0x3051c0c0f0306050f0d1103070e0702030703110606090f0a0b060403050124030b0c090f04050708061c05070b180d050a020a0905061309110d060504051905060106080c0912 75
    0x800e244000183c9040700200e907501d0110300000c40c20f400282100b42c0d80c0c0090729074110445c840035000b41d041c81380840000e40900c032495072a1003034205070059900c2e014641006404000c0101207152250448000c00000703a507580b001c140c00c0780d14410f4141e0b407682e85007803e60051886100140c2e201d070380030500104014054002030380c607840a8005c8444070b0051900c0e40980c80c51400300030003078100100090000c40703800000c0d144003078000b00298041d0007100041002c40d80d0907244d03580003402100800c0032605100034050410300f00c0e03079142c00d42585a910f40d1500c42d16140921010708000094018040c45000101003201030018244205001940340503a55400b1004040f40150f0011000007610301c030501c242c1d0f108120250601034102c1d682c0c2020001031060109c203c034039010120703404020307444200511030600d10541000030a0304203820910f240040d44030403a0321035940c017485180041d43c041f800c2d034115046805e0034056926800400a000d0003100c2c1529040380f18100d803041030101c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 158866699 1250 158865449 158865467
    0x8040303151202031e06040303020d0605040c0e0916020a030c0203120406020a0b060604030c0e0a1104080106090506030a02100807020a05030703030f05090d05160f050f03030105100806090403051c0c 87
    0x20031003c86034010100442a16041800d02a170841904000002008030780079030014440c0f000455400545641c40310002422101210400c900140014906401c542051052150414110160f045080c10215070081d0346900404c8001c041048500200085450402c21252080d401d12542d90729140c03646002560f6030300f0700300700f51015540309010999030309004080f1010f40303802100c85501c0078200048800a2100a0030440750760b90388451003495191040f018001610b42c410012070054603107900c07d426904003803d810b10a4000e90120001640d03680010150f2080c03606007580150740d1520144e0400310210005000c9010011b40c10b4101070b4194082c1111b0545054104004c1d150400011303902c6010f10003800200740d042021141c17200700110a030038514401c0404008000341075485a081c4089280b010206620100060016180100c80146146000c1c03a2820b0545021800a0800c4002401c090180038000803000e4415001c024090341550b000401488003c0410078000d05400d9 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 158867949 1250 158866699 158866703
    0x1106061306081e2407050a17011418011206050603190c030308070e010c08090d020310022a0c0d020f0d0f0b012304230408130504110703080403031512 66
    0x1500e0340340304c2503e068003489010250224800b03078903a41d510b03c0a480a502c07014240c014040480c03000c204514041ca0468041c14103046010f1010f40740c0000d000c400d44030091120b00903a0701c0d500500c01c1640350a142003105800035000f1605841d5513010034146101e000303120170251020004076060290440008c400c40c1c0c8266901403007a0b44a00040301d4032003000c01420b0009600c0741024000c601d003003004e4400e881c0014040741d900c907000da002911700a81c21458541564011a0780340e528681c2810700313a42007203065402100e44882d54022a164003201030881d00c0b5074640b030200000e40d01c0f10714283d070440c403002c0d215a00618150509503060b0800c910308881c410340c40360010422a003409910040d0910010180241c40c42020400c0041c040c01d0034074042c02508444010001e51101c4c001c180a10301640c40306548540020081c100c0021a411003070041d0300700f1400410b40d0030b0200c201c4680750b406140c0300b007a5451b03d00e01100500308141645500341ca00a001180d001c0c4081e4504125034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 158869199 1250 158867949 158867953
    0x1805160e060906031005060f0a0305010501180c090b0d18060203040b1501021b030322180c0c02010c14010509070602010518070605130f060c0302010c1106061306081e 73
    0x1075194400c002c0961030841e001505900515030034800c405040d0080d0350080801820029080d0001020400c5400e96a00036a0f485c1e45490040020310744a4515030b04176141c0c50b00a02450ba00c1e072401618200c074601c00c03210200c0e00081c402510400a900010f4100c104440090352091507003010400b035002601d042e0b614082c1440070031002094880c82d07000320031041e00500040c2119000b010803040150756003a4060000300101d0300c0e942c804901201c280c81c03801504e20910350034200810500c0c0001d0301083ca0041c504001c440d8620781040d00c40040e00d60910349a0300d40b861924041481c110760551000d019802c0a040c8411800007103040c41c10b45140d94002c0045030f490b15503c100d07004080041888a400c18070341800b1851060006004000c00003034440340c050f84c1c8100440b10114140d2103400041d0b1008481020194203000c0e5183c4403000d0710b00141107000e04480700c1d895080281081d8403608040c083d02d010b940098000c070004005000960b1f10280c0c02d0501d0306014060841022028 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 158870449 1250 158869199 158869201
    0x403030c03020d08071b1a07091d0402180c0c0106090c021009020604090507021606020105040309060f0905010503070c05070b030402040605060307080c1305030a031101061d04061805160e 82
    0x41132040b61500c2c0700b0b4205680700c00c100c810340f546840a1120b1300340141c0f06410311040d90b4182580c030519190264955954002000d03141488000010810760881c2c280b0b40400c00901c405a5103864043e400e8007112803026045480d50840c0c103166100d41c14498846501300000012402c19a51204181d41440d03000c0d5400560300c80601c01c102d60781c0c1c1000a6100d2801d02043c4010311443d4021030f4800042c6c0111007580e800302c9400080145541d0003000181c0d1128100010141e00c00c441000810150820740903c20101c0c2014009142a01540381000380110000741d840784a55030000100b600305040d13402c0d141d01c0c0c00000e11340c0e6100322070580c02181819000101d07410801c007168801c00d100c0d80c03a0b11030f5440e240c00c0340c240750780880100d070700007074121074042003030340d020303c414407100d4400c0d00c1d00c501c81080940c209003520b8180c6c2c0014030103c028200803c0400d010100b4070b9006610550008000b81405800d204001c0e41c203401034000d1154125051499407003009020030b507002d001e02030b041 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 158871699 1250 158870449 158870473
    0x70306060c0803060d08030103110109090506010f0c05100606021b06090102280b010b07110402091c050319020601061101150302040e0f030f0a11010603170d110403030c0302 76
    0x945200384154000500d8032030045002c074000d0b030091a001040180f00443c420020b8460f140c00b40c000380c00c156814a130b1000e80300c0c1d2a6030040300b88070003010f40f001c0c24400c2c0c0c603050001804102919683c00c2c2444802c00904003001828071001003100f9240c0c0c420042141c88140096a8441c1050050300c0d0b07030313240f01c9030341400c0c41c243d402d40c0c03a0800164010410786d0308240441c40482080c5c44182034880c3d01030540c0c40002d0703111917610301030101102440c4c0c41d644142842c82d0010070024010380141d1041041168580340d400d0514601c8410034040c102d240c00600d880e92641c410400806034071200d40e1581ca04559000c15000e04031480c0e903994403c0c03080512110b030708031055950318038016000c005041005082a4101000c000c1445081d030321804440700d02142140e01c140106103404000084450319203801c1441840d058038160000c005050030350303965004485580c1c00c0140c1030100030410417080000c030b801c2003807050700e12686251116524078001d042404072401c00c9001d03014141032800d03 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 158872949 1250 158871699 158871701
    0xc0e01090e0412050f04050307030f0201080703050c16022b021207080303150105160501051914010302040b120106080705101d011809020301030804050a0b0703270312020a0b0703 78
    0x10003203802c5021005083d4180100761100d500001200d0b0f1904c2e03050100107407941d0306000c107400650055920001441c40d9200043c450440100702c0814145000e050101ea5201030064402d001040e131140d140348100c5000007080c4107544a548041000f540d550003459007122440c03072807041d1007074401850309456100d02988614060003a441654010700003d03c207852802d61070000e108040c10403502e420501c0c1144221081860b5055405031745801c240040b000317500910310801c0d451940d0030040110740900313114120340d0610001e1321413078139014074901d103a071141c10110560f85100000c111007035854081d5511110300340326480c4205601e0705c0c2045024000d001d10816444003480050070100054019034440342012414040c01c1030642c40483c0c03c22243c80154003030f41c06201015290b610b0402000890f00c06c039004210003110900414002036003021840107100c58070080c2c04190021554011100344555001074031480c1103130740840c11103030041503002515002d001c0307008142d0b4441105074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 158874199 1250 158872949 158872951
    0x3010b010815041508030d1d010e062406070b091212040f0c0f060801140402040501210f020a05030405010c11210f041e05030c06030103150f0c0e01090e 67
    0x2ca200ea02841080c0d01e285031607031098004c892110351004e259500d82c502203245400c1105903012003507803035502d0350510000780d00030403842d44105c00038480e83c8c840c4400305032501c101a010440305210b0245c5403072500700020116501d044041c1800361070b4002c2d8103005840c240162016011400780807000190484e1000031240c100b001d402518980341c89560319441903000c014401d4841502030600400c03096151036200c0d0007007242e59241300701c81d41414810340c0c4084035580d089220f1441000108002c1e41c200e0310003610401c1800801c4035003541140302c20f000d040300c100c1c514261440052008262274108000d1401240190004c0005200800381034803401c554028907041580300400e8400466031889101a040d821b90300900d0401c00d2035203c907405a080b13600015440303085005800111040012604003c101c1100180981d04a81d4003040c5e41d03200601029003000c030070442d8034602080300c0d00520046074504801b003000c1041410002d00ea5400ca282e00e078001040c402001449d001e01c0c18680d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 158875449 1250 158874199 158874211
    0x7090603060f05220e011e0509061605090a0303050301210305040504090303090b0f04120207050f010c02030a02031203180a02060912120d0501090f020307021c0306030b0c0903010b0108 81
    0x201146403c20307003041812407400300c0300c4011803904610501280c81ca0f00460140d007880800104404c910302e030014030480c1040600060980c5406c00b00500705800040c019082448206a06047c0003007400450716031280d080c400b81c00042c00f50000042643c440029070480c0d4085448040000682040e0302d503a4101c444081d002910610042c041498590f1001c017400307109003400030307207040320380d64440300c02b20f044524440c0b0580f03c108000070302142d104d0305851500b061000c0e0041c0c80c2404001100c07500400b14a9040107500180c400464400304090700032141c0080450790001c8078002035810f039510031143c0700d0704000c010144200e00c0a0004400c841594020a117a08046a100c20710000c00e10701043d50403d84030700010f5030a090030b03000090a074010101c40c00b02d8198140038129013a120b12149442d4018410810400070590100340000f0040750320400c2d58501e0b907a8030341180644499000a032070302c40c4a0f0b00b03000d40c9815100060482a8087e4000d025000d0000f00541d01402d00f05d41c0c2c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 158876699 1250 158875449 158875469
    0x80307091202010c080310080a050706030b0306090d0f050409050a1d0c03030313060603080c010b1e01020307020103050c0f040815060109050604120204090b0403052d0a03110910080709060306 84
    0x4c1d507800580202e01440c1c4c0310107642c9020908666801c2c55a2a05840c04026141504a8901401691703070500a00111100c01c2d00208054142500d441d40d442c04481040c001b00300c414580d0395031170347c40b0740304a07001840e02c0a000e102c0390800104003801072401440c51a1051018640003411841c086a203e0301d40c10000d0103541075a0f909240140c00000c120000c444460b035502d0003000180c84031026003a40e80904000107904904d4000380001c401f10750094600c014051000000c11fa07034004201d80000da420300c1c01041517141c4044022040c0240740726134007070101c08117002c0703034100c8001255640b00100101c000c0054558500541c0c6020036070082a81014080100f030003a100c40312045a0b21510103003001462894540301c440040d041514101c0c001480024020a90400c07942c00b451160300d00d0081c0c00c155543c0d20040c074468030541d040d038014151504a0040d04148113403c1c1c6828840c054541010b901c0c01010061000741e04507440c03008207070400300106203175100e880342c0300c255440038003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 158877949 1250 158876699 158876717
    0x91a0a150c05210301060e06040e0103060b0f040e0d090e090601030f0309050d11100e01080a09061104030f151e0b131a0a0605070c031212020708030709120201 70
    0x82180c903000e2a40042d103507407103407200d070710122506981d081c0c5280c0c0d0210450760701ca50510a0082c1a01009001140310790414082840390034100100e1030304482c0e00402c000360090300c8a002c51300404030849001d80c054a0107403180340342040410301040c02c425990310b000c0710b5900c40306a00c9241e601030346d650400f944844010304c00141149034007a0658001e05108452136500c500207610a000c034007046522240c11210424141003250103aa41040c1074101865004850700000b083d1000c010110020182c8446003d01032010b5613000101c140321000030b944c3e0303e40d00e9082048502c1072542003200c4c540402590521a0402480313620307810300040c0f500103600403824440c20058140300d5101d952080c5800306000300c4211502c01c1d00048541c00144d415080ca0f0182005070521403a80403400f441402c01c52000026002c00254064a511050422400c003120344101c2d8a240c5813074032ba29250380700255040c248800800503510031a5190390f142d42094858182c844c0d0407019010080c041031030340d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 158879199 1250 158877949 158877989
    0x21110705010c1a070f11011b080a0603050f06040302160e040b190e010b040b010f12050702010b15040503120f0307120b0301111e040f1401031104091a0a 67
    0x3607841c420310740a0b5140052040708480b607801e40b24030544090020554400d800307620250001480040042d140c030080144d2005074008a032699238260b200310070031849200165101410340e20034009540c2010844909002d202001a551181658194094403c40620032201c030369a0400105417400500c0d440c805072620359030224003000241000414048041222450064510403016150003a40001c03031684c698106110842e120a0b00940c10042c8041d00c0c0b0316081d400008220628030320500000f0190f6507031404900500380c1401d403d602400302405407080c01217030350251003030307071012010741c0d40500e440d003001d00742c41c0300e100c240d80d013101402c0c000902101e00544664000001c510000308071000240700203421220068201c03030030010045030203501044806d1490803880009244246801d0404d11103a500f03000380d01c0f48036010700c00240901d1440c2d129400240920300200a8035485a407030b01e100d02c025040c02032024442000c03c00707450b400761400c003070b141044410070091505900d6401c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 158880449 1250 158879199 158879207
    0x1003020711040c08060a09021e0f071703010906060801060e0904030207032306060d081b0a022706030d0509012706020303010f08070b030705071e2111070501 69
    0x501026038a0340000705401d40c6980b5980245841040b541c1d5481c019881c1020030005029102c0c2c0111402c14410b1000141141020f81d0514070f00a102da41503807103104000d00c54485200f6680f00030580b82c107091083d03420450340e8001d58103903501c406051220030780382d11007107503045024401d500009440d984055030758204681060340090003441543e00d000c5c0c407034072015004c0d01100141368101040451408045c1000d11881d80c000c10121083c0c1241d4100780c90b0070701d00c0e00941c5642c0d031590b407030f5522031200c03010300b02320700e0540ca0390241080c2c0c0e882c05109a103820000850064020700e0380c040c0001501d03460080713040100078405131142c90900708414011031f0100390004000d094809000540741d03407a04d0300c0c036030040107004a500540ea25810a1000042480503034010002940000024880c0700d248105a030b1f888801450415218886801c002142d5004004c00e13002c01c0f151412a0001c0c000e4038a0003031a400c803c2d00d80c2c8042070074074400488010500401d5032580760400c2d4000d00066100d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 158881699 1250 158880449 158880457
    0xc03080f0706060e070e040605061207020f010c0207060306051914130e03040503150705120a061212091d0408030714030a060315060312030b0312070f060b030a02100302 74
    0x144a100d1424580140d0700d601c100c81c0c840d00701d01611540e000412002c079170b02a0b00e000d0701c41c000352801e00050f07291101090583c01690440e1112038410000103c506208005181c1c803010410000d10120300000d80103501c8001078081ca10000341044000304403402c104000d51203855400b00010415441c040e0064589004095596484400054a040e00c2c0800d070180e0160a09504003540e56103181a040618140142c00c4141c5114800410031100d150048182d84852801018010583d690b40c0f84041c020700c0365070850401d034a105400c40082c400d401d400f0310098851910351580c0b0702d40f200e000b8943c40300750203084461070010a000500082003180907613000f01450511501040c03110348003a2654104075140c03d800b66030780804000307202088080034500c41000c8410444c10b0708503151040303d8036186400500703140c0c5a041080054a080100321382800106100d603440300c0d59450b04800b0981000e1066544a04148400d0403e180100c3c1da00443e56000780110021096164140c020b900 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 158882949 1250 158881699 158881717
    0x30f0204120303020d0c090305060c131502160806011208090411190807081302100c02090114030f0f0c010f030b040501060806041503030e060c07080106080105041406040c0308 77
    0x50244000078804104070020411a8425200941c84401941c00001203d0846141d5001c0041854007080411070104140d504000c1500401360b031882c590980032019041603001c07000b80e0a4025101c080360f607000c20b500c403611054041c44143c169941101c00d56916003030090f51454003480c1003400001e00504014607005601500220320750b0b001022420840c1c00c200900c25403035204814062a065000ca044c0e035100406003010b1025040548400640180090009000d0b110500c5202c052a02595241c50880d030b00804040066844006032502d0010104245e80039200760040d083c1c49440105088580c0314415000f4480c0c1040000119034004049031404181a601e0754039030041e44960042d5400fa00441e00e0b842182c0c1050303400e000032a101c81c1e41d501000041c0980034400a54010040d020007a01100d0882c6c944a440c2850b07401c1111991120320150320340100040c40880c123400051090740180c00c90318603010300c0c0380410385404003114020602c43ca4044280700041414025011000c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 158884199 1250 158882949 158882951
    0x19050c0d030e0a0b0403021801030b0105060a02030c0105090102090102070f0b0a0e06130605070b0a140402041d070f0311090903040b070f02041a0405010b0403020a090b01110610052e030f 82
    0x1102202254251000d074001a4444c0e800040920950828800c0b02e0321024140070429180d41c9592644a004401070145c0c9100d80b60016503d02c08070300c00c00640300d035005032100801107428400704941c002c2d07002c00001405401a150005a800800c1a10008072003101c2d03001d0385040000001115400003500340c0c0c0360301520510801c6031101c65900000003529050b101c05603280e00c075003040092003c0061009441e0303810290141090061003404941290703046c0c03000310b680000d03107284581107640c080d8410294032901b44000781500c030112020701201d02132a0500321241c3c0007024081c01010803a0140c0319680f0801c000c1112114610051882d1401003640b8500b41e0348a034006810b8a40400815150064120b4071008078645807082c180140803001c5810b1a083c50740e800f0070034a00c1148910b4114994503166481c00b0790080383c6c040740c07400c216820740d61140b03000281c03908034482c64019540607024075151001d0401c90f80c840080c9100b204034200b900c12901e964220098514520410522 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 158885449 1250 158884199 158884217
    0x1e02070c180603110f1c08040b13030b01060807080f06011202070b0703110915090a0e180d0810030f050f03040f080c06091507050111070602070519050c0d03 69
    0xd582003111622018640e003008144680745040054604080d56804c1c1e10864490400d0031455403100b0300384000e44144081d40c4804402c1c5d0420200c0c50041d58001861410f0006022148150706000d0000ba284141036105950740c0390f50b02101c441c0000c0380c00c071000c5041c500125846810088002d5400601403400c1e0178085040d041e8602a038014020032217000d61200d00b48001e164050007031815000883c0e402e1400c0142e02c50001d101440c1401c0c0c2e120f600b002c00103000d01e060700c600c44040d000d403c05500c0351b00107052101100030b40c0300c0ca01314200b29602800e450b641020780300d0001d42c0d00841440310700040c40d504549030480301c20040c40d003c0314980700b40d20030324041c8041413000d0801000d030032154a800500d4070f406c15051501701c0c1c9880c0d1040c60704004034900b07656000409408204900d03180ba49525161501d940180050208070b108c002001c680351080101a80007481c00078803e074191004030410100703803041400760b43c80c001c8c61600a60b00b800003a00740201040240c0d0700a00c2e0100030 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 158886699 1250 158885449 158885459
    0x140408030c0c0313060e0906030615030a14210c0a030f030906060608061005030915070c0c0e0613020a0c021c0209270304060e040f0f051503070602011e02070c 70
    0x80c5034410f02d00319110700f00904042103180d8000b028510704030070541f40030354a450301c100003035261034005244424080030b01c00485203644042102c0000c09601142c003031800015244103d80c1d0b007081e8260700c50172000088818140d510070a0503244070480e11001041010070310364059840e1848030001c0020103030740b0903001c400320352140101d000900319502d42d5032140c180315080c0086070126452410921401b0000e02800110015000000c0f1a91a1510805496a1008640749030f2410005402800d20700c0c2c010907510301258a950150108540c0312011041c107032001c40507809011b910070081000061020058144900e0000d81c001081c00c808262076955800102c0036030044d02d0803405268228036030361a40070f0f40c1450076458001503008509051402400030a800e0346148410b02482e2108419500044260081c020311038031590240445d1510000c60081440c0c518440b520030700c1703010800108140113214015120007030020045030014201d04c070b040a9403162000301c1d5524041c90740020 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 158887949 1250 158886699 158886703
    0x8070213020d02070b0105010305010b0f0909280209092d06011b050102030117061605070503040306182604061d0904030804122a110a180f140408030c0c 67
    0x22031103100e01780210140d41030500060866405030080c1c4c0360004200541081c000d0100196502008101c500c410541c0e9095002c1c00c1d0400e4400080c041411100e04410401c00790b0b03000350041000035100000e440d650074000c05200d00c1075048460742081200d050003824143c40321084d40c4400c06041900300404040302807100d41141600556260b5808001806001440c080360103140c0d00120023041581480151a006031a07416040d00c203001001a681080260038030a42303000319040a020042422840301ca001c0c00c00610500f240e80f5801503212200352303600040c2c001240301c0420f084d682003c1c00c0503410b444046440501c1c2501608201a40841d0354400e007003d8030480c0320740d441110b80d0400c2d14280e0b02001032440020709000c4090030b40c1010102c11040441c19110006009150310801e050204078000c8511240342c1190000c5000304400200d280d001911b8010300008002110a2400d040200c402e040381142540c414500460003280d85040555040f07003000d2240c900d04102e017800d00e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 158889199 1250 158887949 158887957
    0x717130b0d0603140c04050c030609160c02043909050d030207080102040609061403061c0206190e0a091407050a09090207061b03050702120307030605130906061208070213020d02 78
    0x684e6801100007240c3e60070580a60303a00802c00e0300f0600c0c214280030001402550700213213000ca4003401e255500c00014481d41c009a2099006801045801381c001b0b6210001c428100e00704506c2d40b01c0c00305a80c6410b4100d40300d00d440e00c5c415550018024104000c000422400300010340451040b842c0108074400c080c0b0040c00209165200d0f45281c03413a02a02404c0000410400042c600c400c0c001c03c01180c4416130b600c3c110586081c0d008543c0364440c400115940641140c4842c0e003030800914580b1250055607952140c9422200d140c04103656030743c144c090f01c0300e01d50210a023107602004240490b0186000d0a646902803d00141407600e92200c20201c1c1c00040c829507815440e07400000c00401513502c10001e00e091443e06101a00e050035000e95650f80c89900c292640e5000800a00e886e842507002c40040c103c0286000b03c00445201c1540c06090582c0d800d0f50046e207414000034204401d4101042a030754441181ca0402c40b00c0d0b001c01030198000f1464004040d0200b100c5101030b61248020 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 158890449 1250 158889199 158889233
    0x80c01020306010f02030403080901140c0a060b0906030115030b0c0403120c1b0b03070c14030403050313061704080a02070905070f0e010f050405061804020a050717130b0d0603 77
    0x60326880c0642c0010400280c1c2d0103400113540041101703001048541e82164540c68003820302d0b0021044003c88442c03a07101d5072000c0030890041008803c1000710a400c5a08542c2080b100c00c1d226032a02006c0600300c03045014005000301e04030004000080d0180007243d84090508812802d250340da0b00c64548502e108502070000507c5080c0c1141000303841401c6c100c0448020412016403401e040c020419488041d01005c1031010403180501002050300c0560000e4040d142626122562850115030300c3d0030169400c0c0c400451104082203907441401d0441c035041030191808150740302e0b511103403a00c3d41314a02441c03c5000b50040402c00c03601034001c0900030a40307580c5d003482c91403801e4401030489414242513410481044020300c0c21540c0a002d407019207001301c4603955140411101e0303d46e000d503c1440250411700100b1114881508240035060180c02141202c010701103940042071144104405107801e6450850244100c4241d1809015500d10f80040000d1a640326280d6114501c1c2821311 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 158891699 1250 158890449 158890451
    0x20d0f0540120810060f050a030207060e0111040f12030e0d05150c04050108160e041e051017030301031e06150906170109050c060703021e030304031b020d021c080c01 73
    0x20304c0a02c09034802804014400c520301240d00c0d00711503070020000d106000c5030008058002c6801428010141d000c42c440e1081d00000300300350f80c0f461182e02e4840d0054800c21815105065002406148250710b2101c0107502da03403148918bc00740020400322202c03040b001d4a040c0f01e007850f03013031b40c440950032107d002d000e031070624030707155440d01e4001045400002c1a001da40f007c0c8801342c0e40102d412041e640045501250042108840507001c5508803104c1c0d118501c0c050300300424800c884089171010401d9443d200d81c07803060380c0f80754100143c1d640710030700c4001d01d600040307240c2103d03004024140b440654400c060101d80401c040c414003001c00e1040e08000700c2d040d0740703400800c544021450540748e21800321000b4400080c00780c0342c107034a480340703000050b01802c400500b00040610a01c0041c841540c040c40046402e400246015500e401c00c45044001c0361400d00700c2d01e0b0b0141070700e8140d080c40341d00500440c650300751903091021101d40c0404071303138505820210510000300d0010203000d0310307031183c80 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 158892949 1250 158891699 158891701
    0x10e1203040f080c1b06070b18010f020f0c0f06040b07050304080403050f0d032313050102090a061106010902071509021201020a08060315010305030d0c05040504020d0f05401208 78
    0xe45c0c400b040b1101040340300307000c10413840000079a02c0c03200b40d80c861900800c080700c8200e4254030381c1c013416180b603020401174400141c002c0540748040152000c40c0f031311002c5900910a840340d0582e0b0b004151000b803e000c03000b500003402c40744070f680210361041c802c42c0f006080c6a6203503252440e004800d030424015401002501001c294140700700c0c00b0304001030440a00030440201600030340c2d40c0140c022940b61201007168010700c0b800750111004040041e10107000c0c4c13079403618001c0920f4105078000c1314901a01c00001920300150081e500b045400c00310b0401d200c07802c11050001400b104c3ea0490b004603885005c1c40b004c103800e1000d407240c8400340e1070350042c6292080405040c0407500c20f0a01d171100b00c5000500100b45d0000684080418035440052448506c4030103030380600466000c1030b401400055001e407010301c03c0d0400340c8210004a414019a01c0381c044000344000004880710480e8881c8001070394112000e0a050210400f4400c0180a83d601c1d8031015903040d11191050003283c3c03508 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 158894199 1250 158892949 158892973
    0xc0b03040b0a02090d020411040f06020d020f030405010801051c0b01300f081b060c04031a090c0609130905030405011d0102070e061903050d11010e1203040f080c 71
    0x40301c0d0380c00b1400401c00c600c2c1c100c92070300180c48000c0810300a0b000d1a0707103151103400d04214100f1500070301b00c500180c0303426907a00d1400030350395216010080d00500980e140074030090000019541038a10507113071301420382c0c00d01d03080c0514441507400340810102482c620300007088e906100e0901034141281c0b400c2c0414030702c12a101003000c00c210510301d800303030b030240500c045414619101d91066114461aa0316a8104134086124280d03000310003031400360109101c03520700c00c1c40003841103d1089410070030415400ea174070040e8040880750303481c12350400240c1c500765291240081c0b8030b558004000d915846001031041084842070f95003141da0340d0000130188140c2d0303000761302c400100c0c1181046011072070800c00000c0d11600248124542014502c1c080703a81030303940c045c000e40441006440e8149040c0e0364100309a8a40c440d1188401203a00352401e500c1010041c050080d034100d20308020300511014200030b00b02c035407008205990b240740c03040101c0c00045921004116420f0060010016050b40f0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 158895449 1250 158894199 158894213
    0x20d0e0d020c09010815370b010201050601020a171e040306060f060507260c010501030b01061b0b06010201020720040b0406030b0a0c050927070207030803130c030c0b0304 75
    0x11450b5807140c0e08000040041c0c400000311800701c0380080402c900303162a1508084407964a0081491140355130a204d81c04000780541e085002000124081c068980d05034010780c01c0f51810b81f002c81c010f0f0002c01445002c54518800c0a9070716015180280c5841c129004a031000c1c042c8002c2c00e40300040000b410018040340d40285c00142c0440442c1c03003160380ca40310000d00244901c0a00915a0758031442c1051001c21084180010b04035914456584842d10f004250081c00c00b404112200070003200007190302032285045901006147c143c00b9250307001510f071a000940000c054a0456400308088400101d010101d40c1503844bc0300800b0305021141c2e0104070585032542c4a05001d42c0c40c050b000c1022070840070341289c10081c00003001540d13008240007154144603018980d500040308120300100c542c00c50f511003204254003c0740c00c10585410030200c1c1ca44005100140550f40300780080380052601c05081e114032032151030b60044c807a0307403a41e03000781212640d800300c2698040032007000706101030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 158896699 1250 158895449 158895463
    0x606050c010c0207060504140d020d0303091b080c0111120a050d0609020a14030735160e010f11070f06030b0102012702040e0a050303061503010509010501080604020d0e0d02 76
    0x42c40c00a81001d07400c007100244140074900c80da42503a0b11084501c00c183d02c6420140d4403054001d042c440c0181101c0c01c4c050060810451b003110207640038403826044164280105058580910141c00c005c80c03004011110403100d20b000340ca883c041d1103810101031610300300500c103001d0300e6240c880c3ca550448401800301d0b0b5a0381c2c05640c000d0700400602800a40c090110a406011080e4a41d103a0b1190903040ba40b01c03003844008001c480c03400c01c14001a05442d01031080144643c42c044072a40d560700281c450f07411030302050750301254810f05050413660041c400c4548950746032038401c2c5400b0700c800e1454504051540550b0040315a58028407605074940100a1302100a0000744000031956241c030480c400e41d0b0440014101e0b00c00000030466a0b2a0000080d401e000021513500c500c090901c4c82c0c5070b03842a42d207244107070301c1c2d0800e0308070028920003921704a4030000c00541044e80390038015036030b24000410583d44161700f0005c00089449500c54101da0890a070014040340c4034010340a850301007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 158897949 1250 158896699 158896721
    0x3120c1f0e0a02060a0e040603061d070b0d18060203040305030114060a12150306020706060501170c04030b061c14240a0b03120c030d050a02040302180702100606050c01 74
    0x1c1058040603240304009011103140f681994000c3e84c0e071018900490b034022001c0a51075000f13050a80c00002d114254010710b040d440300702403640912900c0000326076900c0c0148500e50219005101c0809510100c4c1d0000030284188940580900c4503a6039450484e4400c4604401040700440148000080e00d01040a15070003901da0602d060460000a4042d040702d11361103582ca601d40041d000c0c0f450014a00d28000e642c824030664850a0710b15240c4c000d0401d5010310360008004c41c100c90b02410400c4070003401801642c8940d807601c0d040d81c5589440810042c0004d4102c0c04e0302032445e5a003900d0310303001c020150084105417034450003034031903c1c2070004140e8282030f244818207107031110100c030285190f00b08042507400119200e01101107824818039503d406006e0740c1c085040207680c6404401804681c100282c10030140c1d680b440c0c0e2004038000c50002a400201c80e1500c0f0035454600c90b60540c1001c09401140c07000801071941606880507a0040000140042141c007040002401101262300c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 158899199 1250 158897949 158897951
    0x705180d4805030a0f060e190b101d0c040e0a05060901050102011b08061503071107080109153606050c070f17070b150f040903050405040b03120c1f 65
    0x40d1602c00080d40c0d03501ea2810242c81d00c50400900000c210300c0c4d5100200d401c1c0c9181c00d45040b00702004500503807014500c4245c0b14280f07440000b030b0310954100c08038002e9420b4800d14080c002c0c5a030007048180e410080000c20420010000810b18a407a1500284100302d002d0f03001c40e00b440d0030030901c1226035042e0f01040c15a81072041c04070450480043c07500d0f4001a92034405416614480050ba699184080c0342e61380d04000000c0c060400d034032446002406488808807000d944d0b6498100b822030300403000140000e4021404d04020080d150410500b80500c850070502d20720184500610118006450189807408081c0f0340081002d103010302a071191000b056281000c0e50364862120046582c203000b0305a44815040002c540d0341c503410345d031a00c0d400007210b010a2811001070005000b07100d00c05842580c881501618500e068029049515031640e6500d0507e841d140920010300b00035088107030b06010f0040c0c0312400d442240040c2c0f0f0804680001002e00d003031401040d0401050404500c6003075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 158900449 1250 158899199 158899343
    0x90901090f1a09061201060512010209030d0e241903051012051009050a0515060f06180415090906051b04060504050f0607050d080106080705180d 64
    0x1030381c4000056604c1002910714104150700c00d041c2c00c1c0103003006c4d08402c0d40101a845000340401c0150b000c0d200c0e03050150102c0d00705004191084e60f1480c161601c0a40c00800403a11300715440701c800c8100030910b40c0c43c3c1701c1c1c0d00b0304000039a0380343e44d0141800c000001a45d100108a07002140c401105e00505e6901c4c4c2640d59040f90f900c0c3c15884118003c0d11500c80c80c0c44d94100004c00c5000c1054888143e0030200f40c07590986140040d14240400782d507958401c10589450303440e40e250460480f007205041c003018078045504403041c0320180c103000c00b484000940f0000d000550818030b0144140080c03044c0000a0b1a00d443d07410300350391000106800c81a80c00621041c48926004001c1b5010b0302c00481d4003428591003100041c840380300d0403500800328060380b104810056004403505040e200c0548440c0f00360b40d5000d0045030705010302441103012082e0f203130030003955040190390390007840d000c0c480101c1916000100c14606c010040300d030006900c02d01e80c0c202e501d100d008805a0400703250030006508 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 158901699 1250 158900449 158900501
    0xf010f051302030403050906040e09071d07030b1215010504050709050306040f0c03060e0a1112070b0c01090c230301200c01090611090418022103090901090f 69
    0x5022040d8011070380056000001c42d09041c040c2041c0c84500c500240002da5494642904601094065851202d81e01c40c0c03900208007040301d101031043e00702a40003820b80b55503070340c0011805018050007064100c880d002101c41880c1c0280540c1901d080341400041140d450321043c80111075000f0000001c011140005201c0d598021404070381150700660300721a45d00c118180107015251651000305240c0c81e100200f1702c2d80b800460a0b18009005100f9000d0302100701080c00803654000403450540d410400c400c0c4222904503010340250181d00000082d074403260f0f40c5140310214607030804614400344151640321917103404103450115000750024020070200700c50412225054120f000e602a002282000f0202000d521050349076070003103405e0221800c4046410310766448219440d0065003009920400102440701c0e205020358041c0c150f0341e6075402800901d080130700c10491500540020030110140e03540b0321403458043d01c80d001000554034001c40019041341c04040d14203036519511215264 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 158902949 1250 158901699 158901709
    0xc0a0309150c031103040b07031d18010510140a020a0506011502120d0207020a030b1902031b1c050106050d050a0b031c030e06130b060a080a12030b0d0b0f010f05 71
    0x84099144c02d0100c2d10340d034000209411401150405140c0c0c1d113010a20703100745640300c03403401107106402480107211107a107030a0100303141030909400d02511916004018508090012450449061900e201c0c0e0780190007800e01c0e03d81c00040c507100140c0c4244016401e0040510065004103805400310320900300508002e511a110326000026802000c542c00c155280035070100c0d42500e81c001c00c840300c200d403070b45804c07000d81360151028031002442c1146d040d44020130303100302c074054629194946017090b90400c08440c0d40d0300c207500010107000d001c00c2080001406004842c0a04440e80b40c09031030b060100f45001c01c0b030340002c25040b900ea007410b03c51103440d14003048920ba16140c006c0c1d44c0040880241043c0e02034003609200010600c81c103001c00c181c070f0302424444564280300d102101d0250b21104100041c4201d0360040b000f06400a0100c000050040799074069541701d6420085501d00b038030000076880202c3c281003550786543c40802c100c0208804181c282c09400c8051710091780d1810800824 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 158904199 1250 158902949 158902967
    0xc110a0201140d020703080106090b0403050c0609040b0a090c0f09061e110d020303090c01020606090a1a060a0e031c12050c040e010803070308010801051311040b0301020c0a030915 79
    0x641484000d503007481c0000c02d9602120205520b0030000e540c0c4111624009011650074485c83c40050310f90000402c0c41482001100d00b1213400500600540c580d03c010481203a10080c1031640c8540c0c0c0f0140c54001ea04c038214544020200c507000003c05404112000e021508115601000c00c4004242031240a40203410040010340d6a02d04482c0c0012480381950240d4000300094100c0c465a205181c559900000840c40345002000707444401c4907035401a42c1c0e418080e9170103a4400c400b240002c0c01001c56602500c480c615440350681f0502640011403d0350340482c4010300010104a0f9441d114103040001010044800b940201061000000102406150301480f451241c0b11004550791011000035100034142d454001e20b51540e591020a0f0b9960000030114081202c40000080740304040c418680f0584001892400c00b01f8107a0300c00307000e244030f580003562095940100308100c0e1000d00c060200c110600005080003c0300e4140a4910010fa5000300f0744050483d0185903050703407014201c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 158905449 1250 158904199 158904203
    0x3030403180f0b07050c031c0e090c0405060d1104060509010e150409110415080106020610060e0409020d0c0320030c1003020a020f0a0b07110a030e010e01030212040b0402040c110a 79
    0x2a40300ca40c10324049007081425046c56038544980f8415007070300050f142e8101e18100751a124040c101981c002401074003502140d071584c0d01e07403061000700003900b0468010b080704c03d0402e000190400403101804000d41254000c80c0c00107901080b40040783d41c00c041840706080c0700b181c00c124a050510313610403d5100300d00400c880300e912005201ca80e00d81640903240034029203440c0c400d65040481000781426024882c020040c031030b84012400070000d006006090f139540b540c40c9158001c564081c000904454501241c100000321261008141d0340929032028501c2210a40500300c001803900c03c20242c0455207d100341c0002c1402c2010741d0f12030020310000c2d40c26040c05602c8070001c4105038200544035810290b5030098440703081c1000031440440d84990060348501003020081005583d84220706000100492410501586958047c100d0350031011014035025180c6000241c4108140f03005440403502c04015009010851500f80903d1050300c07458070304075aa020640024a544903214480 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 158906699 1250 158905449 158905469
    0x120b040201050a1112070515090615011e0c0303060b04121103070b04030809090a1b110316060615080c03040f0201050d0513030f0203030c0f0d0f090503030403180f 72
    0x41d01c0c6503900903c500c0702100120410340d915828146a8400301b43d0280c80c040b03a036401840403031140c2a138244080e60040c036022004010301d50360b1020420309200018055414400381c0c407680204030f00740d0740c5051a212420780c2c591a04a11a180180560b83d03290008203200400b40801d0080c10382181902c040b02d40c11080c010408000c0c2c0300800d04001c00d64210540c0740d00000740100500c0038200c0201001e000c2a14250802d13910301c0d180c481112043c803001d2042c1d94001c440b81c06070302e101310043c8002120301001e5a10740b9050744199040140ea07024100c43c02a101c40e4208803c0d9801c00b0214031170803160038a0f0185251420300141c0a1200800041c0300108040d01d203400d5901c100e054680c1c440f2060b00030805420003800c02c102150346118120000b5580c440300f220b4052021090380d00407807000c010f881c203040c4005a000260f800010380f10402550322180c1414408690240010041c0034001030340c0e0703a080c181402000000032541d44202c095200c4410007108480d0010841102d03142c80b5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 158907949 1250 158906699 158906707
    0x2010e0d03020f0d14040c1d0a020304031205090c0117010b03071101060b03180d0c0503180d020619140301030c050409061d0c0f0102121b1f02090a120b04020105 71
    0x1083c01d150082c1c0765a2450036140030910075100170400c421a0069004440c03408200380d80b0350300401040e2404400e0160762045101041324402640c01668206109051140e42c281020b401c0d101101e0044619000c81d80c010540e021503960003041402c01c1d00c0905c20060025814441150303014400034044c0b408005428041044910702940610041d21607400b00a80d6420441c0a0f511552512003945950340502c0c0664406035001e4030080a05590100285042000e22100103005040944c551500b03c2c900e000e00341c005a8602000380b0003419404203164cd006074001004044800c0c035554525030600400050001c54400e0760b0b12011650119004110300c045498440003502c00850450303c00035109041001c549008109900c202c02c0c01d540d550044100c00004a80d0340d203104514481b100001c0107080700d0184001c503903242e181c42510413540040c80d03a03040b05d1540301380c0e41580940303036901107605038491412000410041001c00c01e0034850300b655072a015800c030800f41001f414810009 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 158909199 1250 158907949 158907967
    0x80403020f010608070504060506070b2a0d051807060c0209190c0c060c0f0912140f030403051504151a040204060305010509010909080403030e06070f1109010602010e0d0302 76
    0x403081ca240d21040c0000d0206a9032040c919985290070f0103914031960070000c0124860800c9401c0c0e42c030054000b0304110094456640a00700c1e00002d1106030110302010f402c10f6500c2c031020b4002c01c58070040b00800511813070001060402100c8003400301400c0c0d00a030304100005135200c4403141c0340e603404440c2c20450f07855482c0303040240d903c082b400400c0f4a041c2070410700b1090700000c1c591411401007109100c1100c01010441c1c0030340c1c000001101050100720288000143c803a6441d072900d1161a000c040411a84406c07842c6c80b0091005910942c000a002d20401c2024000c1d00c20480b503100384594141020707a655503c0082101d14103000c160740c1c0121510314030110520700394507000503100310b40c3c40341c50f89030080250809000f190700411011000050b94082c911800c1c550a4000090b03e041905540d000c4904052000b00580d000300300340807400114001440c00340000388101036500d1101c03103503000d1102c22141603000e0419a4504110100402c00111316800030000c140750059640c641c079 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 158910449 1250 158909199 158909203
    0xc06020c011401081f05160c020d021c05010e03070f060b01090b16030e030303010b09090c1c06080609120d0e070803040608010f09020a140a110a0b16080405070608040302 75
    0x44081c4642e000c58103000011900d030040f07010740c00424081e816a0140510041c144152141a00c081c01c10a00d40c03180d110303105204980152603144014070b4900c940078582c001813070103020b071450380c0d0404041100350020484c0900c1820304806006010710f0411101d9141c00103030b2080c840e4007500041d04c1d80320440d40307a84148000c002034654010800d0b1503001e5000d0f0380ea480f10302c42e0800c070045004981d02d0b850390315000040d41c0c100d5410010592400074030710180b100c0e0002c09407003140441c50500c016003096051032406800b14402000000e0010f15003502ca61404401904001c0786e6040860f030403c0344040602207503215141203c02046018040c40814504400c40c2e210798411b0101180110326254031030368181c1200e03000040c19142c2c1e07846000410880c840e000c0e40d8800304004100d400040c09100c40984040c1d0407500700110b0158a61907018240b081140e021219884035404000c044403102c000400c9903d640c3c039140c4030514041da90340742c1d00c104034003480c41885001400070b410180f003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 158911699 1250 158910449 158910461
    0x405090f01050703020306010e0103050105060712020304120602190305040b010e1b03090114010e01080607080a090f060c030c0306030809040f09021207030210030509031614030a020304030c0f060c06020c01 90
    0x2840c00801031480c0001c00140250000c1e260a400680c0610188503998481e0142d181039800041c0418504150341c0d540c44c1c4003c54925240c41540028040003520032500800c815009010321009170b541c00f03108044040c1060207c00c18400d0514010a01003c2034111904a0550702d0745c1c54810540c2d2507259544546400d404609211100c00000f00401d850040d00b04412001d40004100a1359890300c045611101b000d0041c0c0ca401e602c2540040e5086200303146482e049070440a00058104140d1540d890504c017481c0182c44040d16803008855540c0d051040702410f404524041100320300310b941c0e500300c03407040030f810314802c5840e154081c48042d003985c4071620040e0700902c2030050030b000c0d04c0c0347d40e00c818481c0310a900c01c0700f0240c1c81d6450725019014091140c203c00d0050b618018400d810f0001c0c000c240e82058940b6503902c00040b00711607040005040e1603132990015910341d40fa40c40c0c00101c1840d070341c200702407200705101b080104e00e40140d585c1603401d42c09840503852b52000d0040e9401071070 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 158912949 1250 158911699 158911723
    0x80f15010203091e1002070810020307090f090e060c0913020319021c05090c101107090204060908011b02030403031d041802010305100609050d060f050a0b030708011505040509 77
    0x46101c00204200301301c15030b4520440301c10758401c10044402c0e901a0f84071400d40c81011100e82120b0b80d80e4403c080c0e00e90056030300403902d080203007a02f070311602c2d4003c03a0300180d000300004070f68415048100c076000b000603560000350b440c000b906e0036000c04041502d40c0104170609070075507008008211685107184c0305c2c0000301d160ba10119107444a0303c140c101c004041030520000246000c000c01c80c441000f107040710714200050b01c080306d04038101c28112842c030600781440d0072900038904042919880d0340010402400f041c1d41d0349000758142501c16003100d2001b5405480390014803128800c05801106035001c0f00e0700350500000c40e01180c40d495036084512014161300514252007010141d11007a0b1204a10b8000e907410841e81e0340310700a901241420f40185008076a0001080055251110344501d05a01c9400e010646c00a6035503c442582d909454001000c0d40315900541d00d820200721840c000c114980003400040100e100c41501c200c00790103100d02413a25140060f09404042001105081e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 158914199 1250 158912949 158912959
    0x30e03060903070c06022103220506010611030306090114060d0e030717120a0b010c080309010501082b08040f0f050a11040b130902010207080615010807080f1501020309 74
    0xc0781403580c031030710399011100031502018030705004101244009140300d01e1410307010031884103a01e0070007400290342009200c642034001c08004031145540006850141e03502c16030044c11310b0f5040c00c001031703ca0f1030040c8035011070703038402e00030842c0d540d8401622504640e50500d5010b4442a4580800c10500c100100e842c0300f5803c1003800c41130b09000000801190380914289034900321f0241c5101d040e441048400400440d103c004030701195520307031001080360700506003001d403543c4640d9905100d410844003200980d6640d001007282d40030034011087c0015007030300c000160021221034181c40c400100300d54010406900300007020805c0380c0c810b14801a8102185220503c0035190080c1d4945c0e110b0400c41c0c2d410340c600169155800c00b40500005400300500f0500c0500594100500500c00200143d0447c0724403180002c1c522004d0058900502180c1280003c1091034400900300203400f90282d4100103c040c108a0030446007006640c0085e4101082610f01920100403813441c054000000c1e030207 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 158915449 1250 158914199 158914201
    0xc0f06090b04050703150e03090111250e010e04021804080d0204080309130b01020c0405040f14030307142514100f15030305030613020f03010b25110d030e0306 70
    0xc80000a10203003106d01c40c0b0380d113801e4602010b018905407405410a03c03102c2d40103210b20110b0b5801101041c03040d086e141c04a804007055450901c008405e01e520300c125510095500703021420250030210301400031613141040a050a5000c920031480360b580c0b00704071390b800a0116042005103001c49480401001d0700303644070b81c1c03552130700c0da00c9900ca40340541c41511841c2e41000d40d00041e004903c840c0c00c05070003500c0320040d01d0f401c3c80003034540203004a0300f00311410b10031400103050120301c501611401006503181c0c0380c4004046c164260310101c208003404103100c960407145105101044694040405134101740242c0752000301c0365180740b0100c8003405001615a0600f1569010740c00c0c1003d080b800380903001a681440c0694062030001070001841000001c2e92401e04000c41071180240ca80010702d4000740149801d09038100707810401d2032681c00940d41100031503021621410702c4442c002009031803419903ca010300500c5d52649401178599020201c1858082d101144100300080c00741d8221b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 158916699 1250 158915449 158915453
    0x601211113090507020f060703020c0f011a01090905061509040b0a08010507090608040507210803070c020a0e0708070e0102010f0608030c0f0f030901031e18050c01030c0c0f06090b04 80
    0x20718200303010b150352891070200040c80072440000ca9103400d504513000340c40940c894140480c003039400a00034010a22500e5100e071071104003441410445080d0440145040d4001c3e0001402081c0c581c0c000c201181c10102402a156141d401c07440c005006603005d00d60b030b51043c20118001d049031440304c650040c0f0345800041d2030304042d0407032803003100c0594500c6100da4071480700751010f2109070b90240c0951701c9501e060200c2c843c0070040244070340000c0d001211602a681e00e801c403a5004885810001b8036012592084ac1446060100074081400440085150000e001450550000c000c00100510440c1da240e090b4002c2d40720400300d00709160140565510f0700e80c400d13641d9010f00c0c0100a9442001c40c1403245120105038444042d950344081c6282a04104c011070180000102c0c19010141e600f0319590340e20000c4c440c1031075884907000000c040c0301c405d0420740e0400200c1d031852414141064a060a01548484014803a0b5031101c103902658400b402d218000300810032008000b90f04410038402 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 158917949 1250 158916699 158916727
    0x90d140106091b12090507080d170709030807020409020103020d060b0403140727110a020d0914010903020108040606030609080706060f030c050402030702340504020306012111 77
    0x640740050400e2003520700c1e075403c818041d4500b441c0c1d840019081504140e9481c040d0300700600c0b0b00d00810032585015220358295040212203003150000c00c3c00018014001c0d0b41140c2450341c41200b5040804042745507464440852182000c000c0c421a6649010021a80250305456986103460810003400f0f458800b0b11100303601602050f641c0c11141c2d401400502c0f0002407000984105a0200c040342c41c0442e07415041107600101116004d07100c00100c0c0c0141d2130f40740506403c0d80c1d00d900a20300c032030b03410001520340445a0000e014034007a0402c3e000051360080d00c881c04480d420718161140d81ea42e418914001e040c1da8000401850500310710320148890000540200741c003904040029a0340c61f105401d00b0500307488001c0551246076002c210510300340e40a0342e070148103401952506c482010300102c2800203042e0911840c99458551a1001e428204c900040c0c2001d0740d00f1861801d0541c0007811031307100300c5400720029120716070302c07540c0c0a0950002d2000b00c610a1a0755200c10315005596 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 158919199 1250 158917949 158917961
    0xe0106030201120605060412110907080f0703060b0405010f020f06070806090907030f030305090c1206190e0c06160b0109050a0f0c17130515090105070206010602030f090d1401 77
    0x42d0000348220081d2400c01c2840c8550000c407800104158506490f20841c0c43c0c801419070b0040e150017228420a0f01c1544070300315100d104a80079510101c1600d031911014120041c0501083e04261601c003050102800f07035030445041e545d090070446081140720070100c1c82d02d074092030340c00201d00400041c001481d400182490042c44211824036070769076418940c0360b44000342d01c0094852031442c0b2030310005c03d01a9000a82004940c002d4540d0203041c0404038800c52540d04442030564003040030447c900b0007503030950f00e8018112505000e907401c5104555550501080c00c6072180000144104030b090b072803040304000343e0b4481440c407038640c1d43e10b0350900200011074641c04424184804541c03055118850482c203100135865440c5c3e00b030304c500304204900e0b10090800c081005094400004a1002c002961185031254503008207490094450f1713095580203014001998400380c0140003042d0003109039046003280700125601c45030070a00081c00c040900e0710141c00e05041c4c1d8500d140200c410740202c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 158920449 1250 158919199 158919203
    0xe0a030c14090c0a0807030b0402090d030905030606100806101809020a02010f0603240209030304140406140108161b060c110601050a03080d02040302040e070314030a120e0f010e010603 81
    0x9400c0755500d404000591040b0a10f201c0005c02c2d0750001055240203030300448290070043c000504081d464004100e62011540065001c5140080b0800c01841c003007040580c403d0707041c1d50412807006851406800c552002d000c4d6446051400e50321038007070f841440158903d01c4039040c2d1007039066681503900000c3d80561409401542004000e00541ca12405644100c0f43e0103034805403d00d08203060010a02e1221402040c86602007080d01610f80d0100302400251001c3c0c02d81a01d0010741030204021190198041010004204410703d01a070300141d0241d4071200040001a2281044804844004000025402c0d5490f2407a05a05003c0d040e17000c5641814a07850300518034270040c0003140d61303c50034860f90751f00020001061000030140e2020340011015100d026040035160390008064030046905402650300c81581003080c041c0300201c40e141386c2217a40c051450815040401000c4090003486140c2254980742c091400711820032107025036010031002088200400249980078146d40e00c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 158921699 1250 158920449 158920459
    0x21c0f14070b040504090f05010e03041d01080303070c050708010908070b15061c0f1802090705040501020c060901022103010602070b03012102010909090821040507060e0a030c14 78
    0x212021030000180c5006440d072841115081500d00030800000c0e03c80c0c40300440783d0762410031201c80080c9003401003150940590000d161114280b4250010659480d5686603a00031840c004104081000c022240c21400b02e01d04580321902504040703181284a038488641586021184420301c21042c000d0110035125044a58198407940c0f4401b8113a442580e90592090013000b1082014401a042c00c421401450b0045070b02400841d039070084441c0b6480b40e0720030030140d140c0c2d882103242012109030b002a45003802c90400e42810b00007075583c2c0ca820b01041c042d490004511000383c0c02006a071100080b5808001d0504108501c10011908207109100141c4580340001c1480000301c42070b641646c0d83d45003052440907003c9014160003007020401d9050000c00c0030041072006440c00303006151402581703041d0b55101076054250061015190425000c00f618050000280c008106081110803a1801264101e98880000c1c400d0040e0340c4024030441006000081d044040300c2040200d003008ca40d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 158922949 1250 158921699 158921723
    0x3040303080603010c020715021609090318080d0309152a030606020c190b0304050106150801030305031f1215050c07050a1401020405060408060604290904021c0f 71
    0x1040c0340c02e82e45e540d41000003617004000c00748440320424894031034090141c8100c61002454003000420100150004512645c4070799540d0709154105401500c040a031100d9000c2c503070300c1c1c1407007592103040215115041507281c00043c4144000b0b000d1036582011603010400c5440c0309400b50010203060003900400c0c2d02074038001c032000c04d1b00910030801282c0301034015000302804d0038208a58280d00c03035480d01d04504c40c0800410240c0710f240c09148524890000002e41d6401c00d10000d24056400260b902002080c000610020343d12400b5a40c000a443d07813007034170600381c612056522082a40054103409082c1c104042032007006a4010901d9000b445e042010f51502c2080c08494882e11001603c00d50005d1044000150f807142491240a02c0e400014109500d940000c0d080358070590094401d5800503040c403215140c0340c401c1310351503003d02042c03054017216200450b45032440e50110350312543c8940002010740d1901d103003450704092005080380b0640e02602d0a034a4045100200f55400340c80b02c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 158924199 1250 158922949 158922961
    0x30a0b0f0d020402030402060c0f2401050d11010c02090a0b040b0f030c12010e07060f0e0904110103020f040e0124050331050d030b011103040315110c0f0304030308 72
    0x1054240a2540240000c40d81c49410380030700020354070182040341c00030403c000381c41b440744061085026042d0703100098250000045183d10300c41000050442854030710900410a981e1240c88104074280d00000c1442c0c1500c1e0000144e030240644100a03401085000410507240b0b00d5a00116903042b0485081000200351400d10141c00c5a1049080c2c2640c032002c0d18403120300e464000b811450a8100000c15045101204c030713070602d80079a10850206400c1e11258400640045c82c0740001700e4280d84890052400351201c0f18104180f02c10103040c5540090b0b404601c918590484014091004011103a940d69003000c5000b01004c548940841c40324260f0002e4662280e41220b0080e14000b1a4403101245d84203a00c00201d0305400e50384105405a4090000450034006054200c42c1a00c00090001c654000506a41003520031500b040d00304100a000007140502c600ba21040700744000280d0000390321010070903100d241c64140e0719219240d01161803540000042040d24443e9460300c140f0346480f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 158925449 1250 158924199 158924209
    0x20a0315080a0b090715030903090501110601030210050d1505040c090b04090f0b03150709050f01021507090803040e160302040b070f02130204080a14122205090705030a0b 75
    0xc1d001d140696004194690007090040301050b0700182a6800c0c1c030303c807942e40d02070140d082080790f4081c004280c8030f03228941803642000e64600200700038208205160450141d21340c5a01050100900c01e01d09201c45407070301885081614165001e1803020032290b81c8000518004085500c02e142c4150b00700200302c1d2215114041c290202d560040e4098200383c1440440d03000741400e6407c20128aa03520300042d45641d0810000c401c1031181244030030603041000c0c0040c00b02d01990050350144940e124a8101664001655401c0d0308012060340b889860342c0c07034121030106442d808061148000b04012a081240c0c1980c0360080288241000c1c04008003503098081c0d00980c481c5a4030007009200803000f1800e030741c2c01200d2141c4010841c0c0c000000800c0c0d030000701e8005801c204c1c4641d00c405109810080c08065030a0f40c0541c00d4000c0007040b221401040d8248580c0801032518141303010b07000c00a44603016800301520000b8201c000c5450311400080903900b040b41d03886201420710300b043c0310324101 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 158926699 1250 158925449 158925491
    0x1050405100e0103060b030c1003020d0c03051605031e01080708010e1603031803021203070605090102072d06020a17161202070f0209040305041a12011202040207060f020a03 76
    0x40b00028030b60f103951100c03002070480103031681c1c040c010340c0c40700e90580d40c80002d0f10200c201c20751401600c0c0d81c0e0516a113070803180409501d009041c03401050105204074a115441c801159103001c0340d50307940f402c480003054801d100461341c660301e071080085891107010800384150f4422400030000360b1001c0b48942ea9a08076a42d0320841031607110420b102092007080001780802c0d0503000031115070754a078045420308962008240f040e0b080810440d04101c02800794907045503051009509013143c03501d07604291384841d414400501501410740c2ca2118040f0840808590025421920f600f16003201400c020240d41e241c0700074802c2c21001076540e10381400b42c0f07242c403281540d0b003806591050003004003d500020003581d00142c2c0c44100001030380e441c11203501c290312990741d05464510b000720407920b03585144441c00c0e40010510442c4408890016400d0446e0940c011081c0e8010380760010400070b200c1c100010700300e2400e1128800344c0011365001001213461664041100001580710300c401d45070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 158927949 1250 158926699 158926709
    0x507031101180b0403020c090a021803120904020304020d140c150a0c200a0f0305071d040602070f080712090603110d0c03110a030501090b0603090606040c020c180105040510 76
    0x10740700075180120b144100c24a40c054401d004640040500d1340004a1034042209d802034119000200703c600d410011542e5903000c50140c1c000c011088038440460035134020400b00307500941c1e0120009007950b0356003504208031504003810f00d1488207161200e80c1c0b02d81912401500844801c1c84a8420007500d60862b10200410f5803240800207081d0b442e200d224103030055190b908280b1680741d900c20340d140424100100b01d481452034407186986407140c200000346e800000c403001e24a210448192070700c409154000d0707000b03a00503031b1810310b841c041003c014642c10141080801140d90000c12594640b2040c88900071780703440d0042d9646000c11000d903206880b60351003080090020804a88194200101881080c1000305280307480002251480e04050b40070f100082d10b4000412030a0898803c21032a081c0c04d840051961821889251390b540b030190985000d9581c514481813054401d200c40c4140310001806514080c1d44203041c14070600081c0580c9105034075110206204050300d800c0c28040311 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 158929199 1250 158927949 158927981
    0x6011205031b0111040b030a0501060806010212070f0602070812011401020c0f0f030a0c06030b0d1a10050306091b030606010f1404090510180b0102030d02070c090c0507031101 77
    0x80a010400280424801480080d0340700c404000c0118031401c00317070015140600600b0344928002c0000005d485040c0c1c01101405109030500041d0390340401c0c1c002c2a0b0442c003159640d40d10541c91301030303a00c02c01302901511861022406c3c0c420468540010310b10b10424040c0744e21245d0f01c07004880811040c0602c201c0c050b034481f801c41d0000b400c4c440c24072000008010124480d80308044003081c11328144110844240c04504001c0c05500d804d4442e0700c8981005844104042000c0c3c2e80d0100040d440c010809001402d0b14000f800d041c2c041e20120020b8107001d01902c1075414180d000583d00c2e03502d1002800c95010310342101e46030381000500c041c42008140e49088501809040c142d07070842800e500c101c0444810400840d1201103809154050040440054141031500d950702d2901808078a10424075400d0100c168466039001054034101100103c00690742c4a0350301e44210050102d5004d449403038102405843d409030008050100240680c45002c488803020008508032901d90850107100 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 158930449 1250 158929199 158929207
    0xc0e0f040905030d110c2103010e0a090507140a050415030201050c100905070e07022409070509040b010603060f0605030a02091216030c14030304052e030e0601120503 73
    0x252815030089001a030190054030b2a04001358842c13016a00040340c000309800d030000301000c2e4504100f100040803002d0500726241d02c81c0345040d0000790711041c46880b04205810340811040d43c40d0307900203044994020111941a503441c144040000c2c8480354075489034101401c0015542014000c03401c0040d42110713030745a1942103a00649864010030100c0038240b16800c1c504100203100c1c41510441d9015400800c005d900c1c281e030b110402107000b800b4030111340000010b81c403030750200c0000c0b80048452910702929030781c0f0000341a140c109140e01076540480c8107070511080c00000a00b282c1a1121540c007840f10766124800740f00084d015200e4607001030010000192940102d6003d4000c00703000030702030080d800d1041d20651800200340c1014000000802c01081004011420f500c000c110382c4d100c0c544080210400243c5a01407885114007809050005088203e0791841c6005402c80010380074064003c000d0b0020002d0118460301c109500c00c040000c2040e001c1040102c0380c041d44400114031f4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 158931699 1250 158930449 158930479
    0x30f01090c090f15030209090a0519090201050901031d1b09010b04081f06030c0b0a031d0a03110307050d12060504020f04050111120301061110180210090902030c0d0c0e 74
    0x1884500c844d10000c02d070f82071029407191b680d1f100c010b6010b41500c0358041028100b031140c0e2280d80c1100c00025040a242800100c0182d170000d0a071482d512090a0010711140c0c0d508190f4410100c11101c0c05590040f081c0303408542402c1c020805003039030123803004e0f0748607070300c902119038184594001c1242661060800c02c1c6c030580c040380c4081080808001c040b400780c2e56580d416011566075044410f030040042500400c860b4588a050850340070500145c01d24480e00d1481c544030b42240314090300300502a40e080f0f80407034040044420303403036002003114001a032098000b402035a00d651500001c81c104440040e01c2d140c18025258402e42000c151840c251030a0015106591048542101405901c0c95200c0c0898680d01560080189440c0c29801c8484254503d05000c42c111100d6505490103a84040300c4280f80381e9050106d03410b58240d00c00e81c898400641380b4910030b501502c0094000003c03c101102900b018040401c5948400c0c0300d849030461099841c1a10f4010498001d85441c082401c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 158932949 1250 158931699 158931719
    0x12140f0c0606090f0c0d0207020a0b0d0c0819020703030e060708060a0e010e01210b0106030f060816050409080d0608100c11120f040504060b04030c0e01031502090a0803030f01090c090f 81
    0x342000c01b507040107140050316400300d9040c00080c5c1c80450032760f5000c58020b449041d18050b0700003503102807400c002c003071070710070340755003010101c8072004101c164089940c13400c01d8041d9001040c1c0300f030b044049940a10704507000402d00281124424002e030446c040015a921501c14594160707a00440034040136030a00280c0010024031840400003842a00212008980700c40d0815018240a40e0302003991a885050001030312440c4c1d0080c070107035101c0d2543c502c0b207030440c401e400c1c1030724002c603404100282ca905100c0d0450142084040100d80381c10800150844000f41d410014400c611080c0420204400d003542c00801c020055451a04140107a80503604184020b2090b4204402c05901b420744920104048464580214070b810800141c00d009100744103240200515403a084204c641d81107640c0c2d10680003800c4050000c840c2c0104501c0116910103800002500d094011240c0300c4c81e080c07401e203404c0e09003803140b07070301813072501c4e8215007002d00c03486a01080c1c902103070750310414030700d0058545 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 158934199 1250 158932949 158932957
    0x5090705071115031905060f030c040b010c0b0106020d1209020d020f0103020d020d0603140f0a030e1c060506010e09060612091002070515130f12140f0c0606090f0c 72
    0x754402c01c40100e076044410f115010b0740c05070203601d00c041c43c0301c0c20f200200030840740064911881011544440d41c42035030000341c5010b41540544000c00c0c050451001622040300e0110000d01e0400d109001080c5580c0c0052044001b42d059030780d500041843d8410542210007078400a0341000200340903c0145c01c115210905000040c9070052414554141c50f1003240c00082490758241e40b981e008009010080b20304010032000030000d44034911144261a581c0c50343c01c10001e00f445204070f1081c0d801d5071501044009024001c4915401d51506d01d020700c000e01040380c29030f01190581c4038040590404000e150311448000d0310b01481c22642940400c40c401004168101030320a802c001c17100807000340081d00980d031003140100020003001d4001e03ca0087c0c010302c04c9129407640000700b404100390100d040c408582000c121105c0011401c000c81e90b040303011003a8030044200080ca450307080d000324000c2c00d0191400080c0c440540385c100811404100560324140c1141c211400304070200800745c000c1c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 158935449 1250 158934199 158934233
    0xf020f030705031305010f0606080c040803090d080904060605040603051b030a0e010207060c02071505090f040e0a0c030c050a09051e100f0f0603050f16031a0d15060509070507 77
    0x130035400c10b0b9552a0039100c080c070300c04807200e84500d400c120700d5070000c000c030350040c00c10600c590605092000d519520b0142d0f59400d80f280c51148221818841c004040f6940c06030054024092580c4851010306654000d01c105c0c0000387c94040040c0c42c7c124043d05000e4031007e806000b91075500c400083c00007501c4503045111247d5401c001039000140c4600c10381c1280c0306a41c025000192800c03e000b03c0a420130140c41003800070411040c417142d41c50080c80382038850110760004010000c0803115151421254008004059404010043c46450240c44e422660308a582600f802d444042d000c044e200301b40e0351260052859903c1600d40d030300030780c0026800f0303100c03160000245541e441d0300304a030800c0354462030070304501d0107091145139458003545070301011a849159143c2400795840200440d41e80555003016507e140d0152401c403007108980c101d44008100141c03148030342c1002514075a007840030b021068a000700015460a124520520500c0c4a0b00c4042c00e00c00d4640300c004480750800b120f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 158936699 1250 158935449 158935471
    0x103060c09080102040e04020108060901060c080304030918060f050a050a05210a08030709061b12030b1002031b0d1b0201030b0d05030d06080f070b0c011803120f020f03070503 77
    0x810b01e00070901c003400c0144031002d04c450f12424240009020980049d00b0a801080d00200502419802007001005164841e00c159501e40e00c50808441ca0342594004e040710042e030440070360101005800000c26111074840b16880203960303408115a0100911031f06402c8801801c0412491400ba150000d41c5818a503100b5050282c100741a4201480300200300c0312840040300b400351043c0c0c04031648003c0d0a46050074000c0b2002da011506882694a60060060700a0801d45030182e11070b4211001071400034001c10880d003405080030351039401800107c004c03d1049500300381503131030001e80141d01c2c0e0b0540c0c41d400c070000c0c50040340b4052031440c500d081c2e0506403a480c80401d0740d166540001d010a0058024540700c454501444003950429403241ea60783c2d00014168039401c20120b0000c0c12543c001e900340b95900501c182c002d014003003d400c40c010071403410100e9403e00da0011850440f40c200104200303e543c0c0340340d034007208034019018400c2d1003e80030f00004415038001d400954000f95006c1d4 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 158937949 1250 158936699 158936717
    0x30a020d08060a0905040b07080f0c0f0702030c030607050703270308180604060809010b090c0a0c0f0206070302060f0f04050a0206160f1101030c05070f170d02040b1801020f060103060c 81
    0x10104142c0b10709860481f00c0f01002c00030407440951101405400106070403500c0014240110710420602400408100f05040016040b085503420041040042c101500b42e40a600c0c02c0c400103411a00401e03001d5001c6150310f4178803481c041c0342c48603c180364000f052080a520b415034071201440d810013010050320200c0a602d0201e0341d0750b1040135000801899440042600d8044a05801d5580520b480360080300101e080c00740a034035510a40703200550901c3c20107035880c520300b403413240305c2c0ca01c0001a410840004c1d03100241680410560b110b401440010b04060311041191840c80e582110003a0080e04002c2e40c240040c54517000070080d01d10015080407201026031181d0240380c900c2c1008440c41f000710a0300d40010358042c06550304801d801d09005040460503100c15500b188403070401000b1a02d40d854020344d09121605440050800c00c40c2103403a203403241d24410440e0301c07162411104c05c0804540130070661002a05460100a440284c040c50340381d42d42e6440a0070109151405214080c0c0c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 158939199 1250 158937949 158937959
    0x1204080d0c0203060c1308070f091802100e03030f030c071b15120605031f0506041a131b020f070f030f12020c10090e010b041208090d02090403110f030a020d08060a 72
    0x40308d0240401c42481031009143c40c050f0300c100d8488151030b100c41130b9907083d0000940c0e00c0c1044034601030064109284080c86030300010381144225a080210b50101001740a10300d0318540280015500c1207e0210042090521003490042c0300c0c810300214103001d03050080b0941c4540d9070510b000002503804619284c80c1d00020303013003888121190071540e80440305a80003414500415401910543d0308101c2d803901541d010040d1515600168080d044104150082c2da20f1a8410300c01c81140180d85848116503c100030744404402c2d801c04c1191203030072404181d405078440d00b1402c07a50700c41e400c40c071500047e07656000c0103074002c5082000c1d802503003015240e50320b495030304010b020307129550040c11605000005e8442c0034180c0003660407200a1109010303c10080002000003a0440103980c0c4a0500900155800302c0717601d4001d40084541091004158000b4601e088100c1e10074242d6081300032401140d5074901400c40344900507031190105040190240c103416410402c00361115a182d81c540b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 158940449 1250 158939199 158939203
    0x3030a02210103110102010f0623030f0601030c15080f0406150e0709210c05060d180b010501020d020c0105161103010e1507090b04050402031302031204080d0c0203060c1308 76
    0x99005480c84c2c0070070b0407880b00301e40c1d0a00c941c40c00f8000d0700008100c0107052034600983c04140004940c000c5d20341c1000c8001603901044448001020320701118250340c0c40703103041c4400c54107a101d80d4048091810580c00168010710780c0a10441108038036102660301c507100e00026280c0c5900f6400d0b51204900c0c045419020255114811001d030380380c0f4101c0c18902000c0700380c803c9100321000c0c100400c210b0814005186040d404d41111030840c0e107141c03140e103154003940c01054441c08a001d100d1200044004001c00e00c1c10260480d04242c09541c122500300030185d0301c81c040302481c1030004200b08104c807003004d407103681c8101e25801142000c1028120101090849000c0d825510081d441000c10819014000504c984e04c0310407032804070304a41c640ba0701c002143c091400740a2280fa0088001000301260407048070307005400804840080c40310749003007196540079014040c0b9030302416030802c1007680030715440040181c1c080c00400322907440300800c1d2440d800c0f40014500740042e0391000500a40700b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 158941699 1250 158940449 158940451
    0xa032007060f11150103030302030c0f370e0405070912060504293d060206060a0f17012406120603050d0324060903110301020c03030a0221 61
    0x107503180c00540d0108048050500c1e21803120000142e44400b80c400207003d0b02c514864116945420096100c1d2a0581010450f005948540c040710402080140d42404040c4148090b000c5485030201c2c07a2110b02800400244645000400700d625003e000300241010750000341d2040329494044c0308162100c040c0c4105108201c01590020349500600041c031482d8502c0030072844c2426800c1640700c103003070075029569030018800c0c040ca80b01407802548440780084407034100801c0150b007890900c48400c03840b4548142d401140300620550000401a040207020807060300c0c22900c14078000391400c01c542d28001407080301e820941d500c581c50030340b20b10544a00402d105001c6c807140c98010b400c04800600310702e408050046502c1c1403130020400b1900101d803001103851039103004184107031898589181800000c03003240d0300307841c40200000c40035803110707820059a203d003c0c4d4001804281e000c05080c0d01910391286003541040002c45d114041c1a401440540718184001d9225110101001892a0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 158942949 1250 158941699 158941709
    0xa050c19082e06060315080c0306071d220506030601080309060f0702061c0b030105040305070204200a0513150807120e01050a0603150501030c05010f0c08160201020f0c030a032007 79
    0x41c69041b210b100c0d040c02040c3c040039203003180051030a0052540003a0b9034440241c507003014018100600030b40c580b824140c6c0c2c841610064900b140003010105891603c4500f5440380d2341480c0f07880b000c0f44180c54041341d05412561a07034020b5084c0b800350810450503038400d820030443d1000c10450400140c48800181c103500c82d0600c07400a100817081207001c2940c4040706c03441e10a914110030400081e030003000380c2d00070940544002070904840451a502c124803503d0143c480309004c14180389450b440030003001c00c40400881300e00d0382c03655405d41181400000100c1c3c03012860400000c0c0c9201d00c01e08038020405038a42e004114803410040c42400c40d042981d0141038030351926800e00034007488140107030f0207031075068080049624503103400003628001d011380c1d07040180c0226a1243c4a00c40c0c400400b405402c0500316503596064a440c0708100c0400c01c1c00c9001d070080d100784400901000c6000121028080d01400c1c1000c50303640c08035004403121740110811310041a501d140c1c8003041000754040e003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 158944199 1250 158942949 158942951
    0x200105010b09120102070c120f0b041202330c0d0905010603020f1905060c01020702120604020f0a1d04150507020106050a0807050604030209100302030a050c19082e060603 75
    0x76002010700190014261030f00c032181e8010001d120004500c001c03a40c08560340b0144549103201d40e03250003010302d800350402038150b201260a1205002880c0d41d4050b9884503a0200d400300c0f81c20800000c92050007400c0703255075000544014045800e40100294066244188985012a540b0320101140c000e0720341651035030765940c424421420b002111040901c0201e034880700c0c03c0500020f142440c0014081c040c0a41808241c220180009406480540f42d009020400c110f41041005e981d0f154200e07000d0748100c5103001800d14608100c0345410030358000009040c0210b03550480981c0d010700140007124812140400ca004620091080307501604069001040503440c000400c1005c5489401165141c0c000020800c01c550720441210100c0b0340c1a241c86926645d401c040b0030240c0300c0e591000c0d4240c01261840c2c0c04211000c02c2e0b044443d441103d101c5a001d0814004400c500304078010366883c0e5010f0030001c01c0312545140032403c84c020b0f00c000c20100802c150880400d55505a000d00003007 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 158945449 1250 158944199 158944207
    0x70303020406090b091c05120c010f050606090a090e03210a0e1603020f0406150f080c040303090323070909060e030a0503010e040f060c0e030c09040c0501200105010b 73
    0x25540c01002d00380289103d1a019050118078400a44c945424a407038510400080c6d0121080003000e0045200305010309a95075110791403000c19901901b1840e0081c88a6854800000d030b4a00d0590251203500801808252240b0309007150b041c01402101a81c402902c070511405a2181e4111610201d4101c000840c2109090030480402543e1114510380541c0d00507803040d629052032810014104c2e03404842500d03000300501c1c0401c0091402e43c1105140c42c0442110030100d54000724140c0800300b0039903d900195a40784007000c1140164040100082c0000c44104089942008110071490104607500d066140c02d00b40345192450303031360001c0081a112130100d82071120f98810801100d003034034082d619109803084024082e1005000c0e80a0034801440401e09000c1103444110340c4a500c00010030460110150241c2404801e038000340c1700c4c8c0b040810b101c0480c20300d10010780c001d036404101d420b40e850a02c401952610103090070402540d83c1a45910310300402401140d0092100034280ca0b62 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 158946699 1250 158945449 158945459
    0xb0a020d14010b030a0209010306030203010f0606090909020f090901021605060714040e180a050106030818220c0509040519050903040b0313060221180f120901030608030703030204 79
    0x191010300e0881d850121103500100303c0300031541d0489034000840800181d03103200020040c1c008004d103400194040d887d007030410441c0c89095006034182c4030607481d01c8008554a80002c01660a81b03d4000e401c0400d8003007103240341c10506e5a40360802801400036041062101c0c1c007407503101091800ba50a68000800d10441a401441c0c40041c1d60754680c141d464079081400700c042c0b650740540001140e44c404a43c2001a800505c0fa10141c035601400030b03c1a07a40d02c0c200200d494014403030326482c00640d015002c00b0381c0f40000d40c4141c41c034541020710651507003540d007440c01000010810014080200600300d003940d01c138460540f01e0819002d8082c045c451034290345046030401010140075074001c0006024881c100016250700086c20228000c41c0d0b40f007842c040020b0300902950f11413204085108010b4400c00441e843c1c8036400c0070b1200384850100c4518903549407098805040b1580200120b134144003402001001418018100803d0300c2da59001c00b40d1456000c440c042d00000d6021030207000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 158947949 1250 158946699 158946701
    0x20135061f020613032015100501120f0609060605070501050a090b0f0c070804080105180d0507080702040e060103031106060108070806040f11040b0409060f120209040f0b0a020d 78
    0x4409403940032404240e858071001a58504000d40802e03125500713043d1500801d8406c2c003800b0038001030f0715440c06016683d0958035540e800c410015401044115000484455050315044102c4005075500300c0d40d0100e15804600921041e08840c0d2101e40f80c800114102085014000051080340c2e511035441d806410b007540fc4500c01752403c8ea90034100406900420b494501c0660003800c640300ca00110f845072255550745109400008050400c0480c2c0000c0c41c0b00117502140c0b180340070283c40120703c104e040320380782c5070f11101941c3c00104105000520200f03207854003402100740f0152001981c0b85100340540d03d445001d0780110006a04400e010351240d209001d600d4100000f0f00b0840d64500740402c0161004400030300c114000ca03a07c3d980305492031060b41095041600d1450169a01c580385c00c124a0503611500800360641e00309140003819400591f610412a45004152140035086a0030030600036006481602c00d40745007400c42c0f0202d4081aa8140075107290040140c0c0c0d00d480e044014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 158949199 1250 158947949 158947969
    0x201060b0c032b180b0702120f0703021e0106050a09050f070c211107060503010812090114120a0e0609060402061b060a0f0b0303031302013506 63
    0x500a80c0d0305101149008000005440d14106401c030600011010385030510b89010b0441e03032200010341810502038110340d608440030019806203e00440c01e0350394407000d99030b540f0b800040c11000c0e0410401f030030440d2550006400c03010310900c1994082103030208001c590b01403000d0700c5100c80c1d5540d4010040d62815060305001091015024016031a228100c1d03010303081d0040a040920041c0e1000204200c01d2861201c1d8040c000c60002101445020009044081c00f608040207846451000300d40c01c0d0184090340c1c100c4201600512680010103144c80c0b560300646005814007120500c400071103038102000d46010b1010a880d0816440c0a000b900c00390f0350011b040d10200e400420902440c0a40801c0d01075225405076a030b82c3c1d0315212900f81c03003c99007840448030203902400090101d4903085d03802c151500d40710450240003082203801055200d10048c2e40b01e03d2102507513000d410065000c3c85046202c02d45800e1401c0c5281c011100200c220350121451480c0245000c04000c042c3c50112400303 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 158950449 1250 158949199 158949209
    0x20a08090706050f0703090314100b0d05070b09010513090f110406121d0f0f0d080f0a0c020304050405130b0f10030807050a08120106021506060316030f1a01020106 72
    0x51603070914052000e4900d00c0354006040740d500c4005841720605008216220040d80c0c45000b400d0070103840c0a00c01c0d1101201c01400c903010341020240a00d038070385640001c00d032030341002c0680340b078502d0250608a1580188031803818000c0901c000c148540d04c0c00c900c0030007440e00480c042459990003c544c4201e60040403140f02e00d800502c010b1140a50210f400d01010440100014082100f04e4180c05036a980c018498014402e0200f600b107015004210060100500d00484c1d41c413040e121070585541c6021114411203038694000511105c03004e400502a845060050300c0ca030a0712000841c00340c8900301c807450345031802c1400e0601000440c15045601c00301f042e580e4200d5040803031442e4014141440003804504e0f000c035148060000c24088940e031568080e21507540c800c001c0b80c4800c10101e003442800c001d4010305c00b18032203242d442e40310280700341c8004002031302d55a0b5003042403003c1c960000131842090703600c41d5a40701440301c9104490f094074280c031032100601482c800090035a0a66001 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 158951699 1250 158950449 158950453
    0xc19030b0c0a0f0305040312062d030803070503130f03080603160f060c060f0507110f07060c030807170106030510050109140105030903130b04031e150c0207051201020a0809 76
    0x820360303500e900c40c0c2880c1c10004640b90101d05c50711a424220307052041c440c0550f245a2070030380001b4400f56009440c0102201d9042090660103141c4414845103205110282002004000040440784182c009540c48802c820700b14060700d5180d11020b80d201c443c0c1e00110003260604003444000d260030800b0923001050300c0c0a28110700c2c10314441e402d01c2420f45c4034000c2407080e110102c80030401070790400441000b40b40402c000514000c1d03001400e20800b400030521134003135128031001e038440214082040d10f4807622603484408295a0403a9440002003000041210036141400c0d0220280301541c001d09071550041014104410516407018132039101c5814413003000e400300001c07460080c0890101009081258581d034464000034254410482c17480c1490190b1940890b00041400c083c00c1928010072510ba06c0d80301c10070310702913860220800074201032500200c00300d80404a03004211601e0062069030002c9942e40e01280e04c4c010941d10300c001994000c200c014a895008000030f034011a50300c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 158952949 1250 158951699 158951707
    0xa02030402031b0d052a0105040e0609061804140106060e1309110d050109060b0906060702040903020f03180306060102030901090e15151215030c010804050c19030b0c 73
    0x10010f0f81c0e03190400340814241c40007035920961070b910b40052800e0340340c010040e03604581c203940c0c0d030b44907640985c00301d100a007400c5280301000c0c1d446081070f6070542d03065450f803500c0317a02e4090400030b29240c01800e45502000748000c5208069180201c00d0190b48212218402502c0d800b64281c2950340903046000ac006100495244640c1e0340489108203d00c11200050003007624140924031b141d1541b800f40d08107010036181020030505520440f402400f6160801c01ca510f40410080c0041040d240d9660120090125101515080c1e10209825100b4011507170240c011861160460b00b01c0a025070b0503195541d15034805080a00c25560b0040342440510f00d8015070a0000c0d001c04440e004188401868000042400e460004d12071040c401c0185110081906100310003680d501800041404501c0307c804034640b44042d020340610290020050030142c0c0b02d0000444400c2401042601c0d948501d018012150321404050005d40511407104644181541880c040c8800050442c040500e0100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 158954199 1250 158952949 158952953
    0x702060108061f15020615191202060702040c110105070305060a03140c031b09060d03020a08031305100504140f10020c011401030b09120a02031605100e0705040b0a05090406020702060415170a020304 87
    0x30000805071204827520051000f201d00108505014280c00250030500d40007044012a400c08030329030080094400a01c0ba81d5600c680403001d54400ba18101c0e044442d448040c40040c42c0c55040344040700100e8112803000c02044002485d0558910086d070b840071119981000f50300f000c4400710b03801076041c1c840100214140c3c0d0025a2480c42e00303400f405120380407020803942d07014848014a100d8110b0100c400c04048000300c100201030940301101e0f900102d19018030140004038160100005440140096040094102c40030754456141e50380036550321080e80d80503070309a0070414040c500880042049240400b00d081c98082c0c254410030040000f401548811980002110040e01400e1641c0085a5080c586035181c2258510301c0c0c018241860441466464001a400102c410448080c8207015011080c084a00c45038050f00f0b0f00151414005400308050390000c004843c4042c22244c0f41c559a4400e180c00c1700002446a00003c40c41080350401c1003288807240e420061058013180b550a0036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 158955449 1250 158954199 158954239
    0x320d0512010e09100912092102040e0c0d06150501051617070f060f0506240f040b07030903020f2d010311040e010e0702060108061f15020615 62
    0x500c5501c203a410100700140c103d100030300c183d80ca01c000d48081804081038915040b4100d02d00c80585100152480000055403403003851011281c2420f02d00c104800405030b02444040c15500403c030f4203603c121031281516444d081c4810b425031307020700c4000464545800000031100c0c05a44030a04104090068411801c2018040c00c1e9491b401b00a00750108442c2030180384e10b000e0490f01500f40c51840900070f05100341e58100034080744180404112542e686010840d1049103c506e01c1d640c00183c0320526000b920050040103100d0704082030310308041d60340b651040d4644c09007000310700041400b10200110305011220b0481c801c800c8a402c0581d0034810284c54401b000c001c0f90310040d10900b180c564440c2d0090340414000a08108141d640769120300300e202c2c082c030003846003c1580304940000381d0300b2403012071010b06884044018104a484158014481c002c0b0a4181d1500064083c0700240c01d00212040304030f42c20b025006450301d4540560f1524034034844503911400703000c550701d110b1030003484 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 158956699 1250 158955449 158955451
    0x1502011401140301060e0703020705010c0305010b0706090c1a0703110105011203050a090509010b090123070308150904030e03100c14130306050406050f13020a0b07320d0512 76
    0xc00124100c140c1c602c50000ba0140017968096070b1241a81020301a5542d45500103010f8140074030028030441081c803004504613002403140c14801c0304140456800603165030001d0380b845014803081d800007516000c0b0311003440b412418011200800240510425070404892807180803d030001300b10662410404680384220500014208500002c0c40400903005005a0010740006001d41046c0e40c0c41c2c1c41c5580300340e844141024003250041030a011a4503240410301043c103c0141c0c0141060040d03603003600c00e6500a000c461004541d004030600e10380b0340091051180303020b03550350a8035505c04e1007858104981d200c090650141400d08070481c4940184030801f1407100b04922560700c4808032403200f03090950340c2005000c2402d0200740414403c094001d240038232004c0d8408600d41d110390300500c0391001e0722980250820562541004401e145002030070009020300b540c0203070751141d0000184880c041d202c0c12000781c0d07503510304000c41010400c81a035101182d81021854030b1083e0040c0034034050 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 158957949 1250 158956699 158956709
    0x7120f060e030c060106272108070609061b02060f150102011107050a110603090601030209040f0501020a02010501150f140a0201020705030408060402010806091e150a030c1502011401 80
    0x14a41450003075040e0100222005148808107a40040d61100f1008050b050400c07644c0900c2d10705001007a14089410b110b04084481400f20344130f841c02c04403402c0120132402c401c11b5411440900c07143c40801c07558018600c00314070902c800150368103111801c420785a60008010119408041000300c800d0f420726409030000303d0701a040101d03a041c940101d014060034903410a0b01500400e101080110000f0031320050340c42a005291115801028400c0c1c03408216818040c0b40d101d01e00400160500e502a981c020380503c44100840860340c550070f0a907808860701c039006030742d07601c0104548100c0c1c204010440d41c0615268480d0000c5103002072206501d006c3c3c66514803000074407846254000d50455159070f500c2001d5a80b01c595420311641c896070211416400f24040c0000a00b41c3d02d005030320701c0c0c8513090703070035048100c1d4041224000007a11b00a08c480042c2c8004d00d0714807642d80e142d1403104000c0d44108042ca01c0f150410300304450a41501502c00706682c180140003142948070f40d14141503403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 158959199 1250 158957949 158957951
    0x90f040b03010b0d03170105100906140904061211040b060a0305130c06020f0c0301060e0f070c06150305010b0406151202070606092403080315030304030602031807120f06 75
    0x1000c00d400640103001e603019543e4040003e01c040c100300750708001c04958450030201090026a41d800500c429861203100410000358100740900c150b900078000e4141070750344450007a0910f05c04101040444119070402c0543d80404034081040000242018190318030645050000d00079403404141039000b465450800d0585810000e98869154a500b1000399004100d0090946d13031501c2c080e459106130320301000343d800f039850902c0141c20140150750448001280280c8943e5800c0400410707183d020b0010420031048030380382c1012880e2802180400d5000c40700c41001c151443c0303055421213000c8072408e401107081201c10081c110a084854620782054145680c0c0340226100d224000d1040603002040c81d89889030114407110180d1000c0e0840d40013403d0100e444403140100c400021051000a0007100200001803002c80e41c16030140b20040043c084034240f5031a9925101a41c204a62099040c00081c0744005401ca040000400410803a00c40d2108a011900c503200360940042001c1d01c22 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 158960449 1250 158959199 158959211
    0xd0906080a0c0c021903020117100b0a03021c0203070f170105100516230a0b0606180a08010b04060f0e0a05060604080a0308190209090109090204180602031902090f04 73
    0x10740039003180041c0640c001d040c00e000c40c2d250141c5d80600700c8a400181e0001340c0d0074500001918400c0c181034020701030203954144452508941000a500c41c0540340c04054003881204021803001412145e050548100540c50f4508400018030b600c00c1841c3d08001c024007582109504c01c5003140351415508280e85403c41e000001e02c06543d24031410742645035880c0150082024012015203000200888071580f103c030100d414006965007200c00b00c041c01006200380856080e06c2d006008100386061074960350204a4a100005c0000300b003540314041c5a5165004000d5501d840e200d074401420040b201400414200380038142c45180007800700240c1c030340c0e540110701643d84210a56000700300400440390041c030140360003803180701c050701d001403140d8005500c4200c124030f900a48054030006000b8203031980c03a04030108080d046e888070581c2c0150383d8042c40c40540113400c41b0005450f011303000241c0e0b41c1c10035032a030341c41e0303080f25080da400d03260b20610200d8620703600d6244400601e282143c021800c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 158961699 1250 158960449 158960471
    0x60b070c03033f150305010204031109160c050f070303020303060a0603020c030301030807020a0e160f0f020c090402040e010c02030703090503010b090402040525031d15010b030403140f0c0d0906080a 87
    0x41c038840b1300300d040800c401c400c00400c003c01500204152446140500912400401440031081e0180c44000a00c130568212082c0e09105186a512041c01002299041403507040550300302500b5400a60068100000b0800503041081071500103054074601103103000014050142c803800f0600000f407000c90006240002c1d903903181e120002501d2095080809800c202c0103e001d090408140e00000c10b000c050103c903a00e019919150f010b05242d000b078008209490100450300340020812070340540c2c2c0d0719410000500904c240d206526050700150350728441800c0c090611074807644154401e03810510b040406072105125242c11a6064401144503211441e60b44000f0140700048000c1c810740c0b41000044585c15041220b802c0d1070940300c28000d000944003a502c9110001500c5002920480104034980e0000011036100c1d01034a854101c41c80c156880c915035078403051310121081004501c4040c480014810a40a60311500700707420500c3c94084090710406006055400b02c0e5079032540005 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 158962949 1250 158961699 158961701
    0xc0319030b10050d05060f06040b0c01140a0b03120c0d120b0910180605062b1b030e0613020609060c0a06020301080c060a1d04060b070c03033f 63
    0x12400c10300510300030201d800900c00816070340010003000c640c28148004100f06e401d001d85400c103040005083c0e10b207803600340400022103a02c03200d40c80da0f184d035030380b01490601143e2550f401c1c01740d102c034607011560300030000425192418548102000e4202000030b03c040c3e0a0001e8201034060890400784210f203100c0703003003a00405e01c001441d85c211245004020601041d0640f02e0207480ca1a2181c4410300d01c0000d601086030041d0250703e42003002000b5800c509a0300c40200e645009a00304280b03104103000783c01000741e403150030081d035403042008018104942c0500030040300c480d0450040c80285402229010034010300704000c1c0c0900070000303804050f034680c4404c40e404004140211291800d10749041c1c0c00960091245007140d00039403840050074a052400c0b240d01c2c0b80aaa503000c0310510103440d403010b01550001c219409660307001c0c000707048040c0701d0181031154040e00c18584001c0c40c0d030030094200d0740c044252000c0300c0b1081c4242500303065001c0300c8242d40500c3c0c1c0f2107050030315400301181d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 158964199 1250 158962949 158962961
    0x50301271506030e0a0807020d14070b0304060c050901020a030f050421050c010306060f1b2901060206060d030503191d0c04051314010b1002010c02120c031903 70
    0x902094204040308071028a00101c1004880321030340c081229541000b80a0380b143c0c1d00610050002608004500c05458100003101450340108402aa40d40400b20501d00d030030620741c0705c0103081c50040100014417601c1e01c50600141d4090400d240385c0f54a0000003512038580c804001c040c0301c80c1c200030a100c0c901c1001601c3c0030704040c0320102c80b644040031400d4080340803280c040703859104100030602d07254440e000302800c43d001c81d00c944018465140c0142c0703449c4d84032a403000000d0303022103800c004507400712940c00702d10075181c600d889950041070081c68000016003004040d540490309000007912915401503929400d0316182c4e0310780d212001514102c040ca8030107051070f01e040121300d8207400104066901450001000c0b24040f0303c44105000c2030f54000c44400050100c10700c401d00c00701390602c80b1010201d850400005220045d580000c044014640007c40142c0d501c81090075183d80402a40c0c0c00f080e103007407200c2d040c204049243d80e030364401c4800022070303510054091525140260050 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 158965449 1250 158964199 158964269
    0x8030a021e0301080f100c0e060a0c0f0b010302011205040b0a0213030506100e100f031403070512031602010504120c0309030b0c030403120b03150c040e04060c0e030d050301 76
    0x40740e40c03560f682c107205688042c2601510403600800c0d56640e80f6109510840d41103250070b80320700741da140f00342c0100000781c3c011107a1036040c4015091a400002c6500c10360a0926210b4040d880442d410350000611060f199105c1d88800f91401003404007146801a0b402c1e481018a403015940b01104051181d5404607544010850b1090400340b100702c2000c10030060950701154034a01996441c0d00e140184007030580b14580c191628041e05101088042140300222510002240c1c5818025035800c1d180542c030000304003003150301006011303400b01004412005c5c911548028000303420503072540101480204102000e0000070300d100c404050040c0c2490009540058003180f00745024000c5040301c0d4000c640031000103040f140d0340b245035609441100751031400034004000249281d8100c40c4005405070105243c0c0105010003d69442c0560340903204511640011078040c0000f10050700120400f003507244280c1107034020820055124043e09c0c1102c48011210b4a4000f0022050b00000078459003 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 158966699 1250 158965449 158965507
    0x21c030e0f07051518010807090305061003061d100b03011d0a0b0f01060e01200714120303071d0406090903030e0c1203040b0906040f03150c0c08030a02 67
    0x200039054440402d1041c21550165950840d00010881c41c25045c42018180303c03020ba20400307a01c0455210b450841e5102d507a90524a89403522521140e1400c44102c40d101c41b241b41025080c001c0000728022079071461210000e1840808801c00b0b40c544440e103d01c420303101c0075900c5145059654094122172041405880b19592200d55045119215003a40006496203108c42e008640c982d0300301010300d03040300c1c00360351005a505c10b880b0045440b081c00380c010b903200c0501c00c0340c5d007400100244900760003061400c05441c07280c081c1409201010b15000700141107900148100104190800084002c2c2441d61741c250441c0020000050004c05c015004108968904414181003680682c0524110014002282d0b0201c070010200411110102c4c41c50301c8640060000f045115041005401d02040040c001030030162242c011035411401076100f0b44210240c215848030070082407141e6450441e4900e80450801b07896110150f10b80700242c01700202c2d56000807060008210820003a0007010b000700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 158967949 1250 158966699 158966713
    0x4140a05061603030608030a08070c0609060e0705030f0c0306130f0f150506040c050a030f090b1f0906080a1e06051006122a020f01110a030501050f01021c030e 70
    0x100d8002c901c8524038045022902e402c00110f500900003041d0b50a15005580d03121188c0c3d10803002b11b0304896040c0b003ca075100d40710540440001c10600803130417550640401044114540010145040c0344840003480740c3d00f241261000781d44000c94010750184600c108413070200c2d028600b6a0f1910264071028001036800e240c20401c01ca0101d041c4048290701c070005000030b84072107040000310b13407100c01c1c400080b41c0d0410062030028002d8102481040e10318000244080c419101d00c5c255003021103441c050b844e0005040c1c049080c441e0b40100280041c000704101e81410146940d40c0d41070039050160201e811920080400343c40006102c00842d07001c1d8040c0314a0038010743c00c81c04481d1078002d10380410703242400d05400c082c05202d8802415200c1d007501c041d012110001030070602c0203411020440c010100f4107000305100340111103514140d01410340c0d031100408401400c03154181c104620425484441050681c0d001030001b6200103248810170b0b01c00a1818207400038801500070a10502541da = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 158969199 1250 158967949 158967967
    0x905061009230307091e0f0b03101808031602070f06270816050102190f11010525060612030206070305070509030a030e03010501090e060c0c12030f04030905011404140a0506 76
    0x305252416007a240501040d1452544601034a1000b9203483d05940041440b4540c1440354104211501cbd040784103050405130380d11400c80c164000ca035002600000d04109a00540d0304001c1c04005080101d50308006034140000100050000d1400c496451a40075900d4500c401184c050801085240100c4411072010604201d610015116090150080f140d01da0308000034512074800d00307035010303880c941c20040c56550f0004200f00e6013030303135810003030b09011106c90301d20782c2208841a00d80c070098211410041e40f0b0942e080d59207a401040c00168100070a400203074000801a4020500c2d0801062a030744010b03089416000d128200307a810b11852114209140e0401c500303202c5508182c0003407107107a88030300c0c014040e540702e2812032900d0b0b8011000111012040406070200308841001c0d00c3c0002003c1c003450070503400c141c401d50009140e01c2c05201c105a04040000010602800d185d164124803103051003541c080d9104e8614000501c10b2680d490b6a00c62000401405c001442551500044 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 158970449 1250 158969199 158969231
    0x309100c0c090506010c0303020d0b06130810020f0a050705010e24011202010e01050a02030d0f050601020105060f010e0d05120c01020318070311010c08070c090506100923030709 78
    0x11042a100710044000101d5803400600034103205602c180c4074070102018a50f403c500a5001c1e070300d5600d007542e03104a10442070343d41000400c0c141c01030350203903401d80c1d0401a04ad070511982c4520351000d2841041480054840d0b01d090b0b944046a42c108540c841307400381001c2c1d01401e5640c2c50001c4a0148445040b800b884012501710041480c2c0e170301011907071301d4007900740481e203009401a0201c0c9a05440ca41203611a0700200901c02d140d20583c0c0c01c0a200ca031102041c0c50060306240070464645080180a507424403900d540310104440c03c5a40c0d00c0750500107020325594950700b43c000c05002020406105003000444042402c500001395030b00150b8912a00075001600c006070b031102c0d807030710380000c404000441005903a08400b03585103000d80503005645008102c84120303201c28040c80a680442c4413400500c0051201c2c0001040c0d41c600b004c20404c42c8287d070800c3c10706100305d4007030a0200e4000f0000381d01c10b1201c1c0f2008681d021031410f0020740352004a91000010724208142440c1140d50 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 158971699 1250 158970449 158970467
    0x7050607021206090d030c1d040207031101110702010e03150610050909040c030209010e0403022d01020c0a0309060318060b01020c0907032c150403030608160e280e030910 75
    0x5584c0d010047d022200104507010040514401d20380d9540c070120001524180d4010810380d84242401c440001e00c0b04161800c1d00e031040703921144004003094070310540d6003042480502c18421805800c0c039685000b48420b400c04003502c100d0040c207400454800c60f50003801101d13a0901c005148044510b050700d002500528240412402188aa0300001da0300c0b4040315450300569158005e40030341d1a05009800b1a0480d0316500341e14003c0750140600c000d0002e100070000b800100c00079000c07480321400d01038884c0420768851002c0516146050606000401d03040d855617034441c0c00454928051b50040345001485401141c0c440041000e10007040e8041d4032409050306403c1d14036074179854091040c084955200900d014941144c400040da0540d00050194840c0c46428000383c10358961803694030f4910601d1140340f0f0b9062405c01440032440060b039195028030b54210130080c0344c100e440402041c014400c002c150141e210384050251140a0064603403840000d0b01c410f4651000200042044503 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 158972949 1250 158971699 158971723
    0x201151206150b30070c0803060102071205060a050c031012020607081201060206060102011b1803050106080d02160b0a0f030b060720010804030813060204092a020105090705060702120609 82
    0x32400c5058075800d000c2004c914420306081c1c6400c20705822603200d455640d48000d18050450240078008151040c10040f510401402103000b04000e1800c40028009c565000d071444150030001d0042000c08034640038404159070043c2e904051600307240c03020591034014050000c004000100d0501d43d0303a040c0004840c101c5d0380c0c541c201c40b1284c0340d52005a003268644240f554010b2041072984244074014035036060760010310030701100181e81d203031901400c403201504480c00c10340055090030141641008241c0740c2c0000040c200b02c00c2071600d108060743e80f140e0000101804000c217a150701c094060746c0040b00b10100070f001c003950f58240d858000e180090040140c0d51004c0c60390150300a42d4482c03009584110352680703803503c03c0d458003030445180b2802032204545981c0c080202003450300b000c5c004e42003c0e2a4040c0b400200c00707001d001c44d0740200c00708a4000c0445e0b2400c410450756880c00a40201107a0017078440c03a5440c0e5090020510300141c1d114040c7d0144030b000d0a21000c07003400580c8200c03803a = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 158974199 1250 158972949 158973007
    0x50a0203070605030f060904080d0504050705030f19030f051909090c03050402090403081902041203090b031510030b03030304031232131a0402010201151206150b 71
    0xa46078070b4140d88030b00065801e00a5040780000082c2c807410038070402c9410a00a200c04d9083c0300103a13240c9410b440c0304a44c02c850a400401d0200914101044006507000e9001c02905a52051080e0382040c221040e401071f00f0881034180001d9807a014008a4104110012070781c02600308501014040c0d90f80d51043c030000610302003c14881c24800c0c81040d010382d82c014801002a15103450481d130712040a003244240d400746107414000e6803620310080008140c10400741140045070b00340604080c803d0303407065003076000c00c00c10403066135410308103000301c031301c0440c0c4880401803403803801c4000702107115281d40c05110010900c014960414032002100d60018418440550108843d03a2070b800805000b4460f204600d540260200d42c052100c2c0d8092162540207960714038a85520100741280303400d0103803196002d814401956820b0184450216100401603001440c0210140d240030034100041d15895491146100190f1680c0d405c500429604118644407036800041d407810700c03003c55043c0390700 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 158975449 1250 158974199 158974213
    0xa0b0907051908070512062d030d0302070b220206031f050102010e070e041b06050301150914060d0603080d06061706030a030c050a0b0f0a05060d110d0602090607050a0203 75
    0x9841450f03028820221903071060708024074a101980b24240281c041d66009418051803c44500000d090705900d842602160807ca541c41c001d060521845036406030030540100320080200c1c03c4c01100d5a006891b11610f030b000f408100c40326001080c40428000d50101d8000103000038a404000682140440383d031051020503940e0005908a401d0880c094030701e600106410000b20b5069500d0552007070181c400c000e60883c240c0440d815500707407900100081034005c401800060001ca00080076102d4034140b08a03800d09103041c0d070603500b1044440e41e219240001c3c3c01c400710310042c1c11074402954400c0b0401c2d10303900c0b0700340e11001500240c0140f80000d20001985804041004450350040e94060042c10406440b80c0b0102d5840f000e8640503642403007070002c0c2c40000364040d500c141c40750201e90340303070301c2103042101144050f10344c00340c5031074407803a0382c109a0004540701941c84c40c0824012904030318408124a0310f40040e0041c54a1700c0c0d40f20a0218496041c0300c008201200c055100702c00792420 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 158976699 1250 158975449 158975497
    0x901020904141519060e0102010e07030b01030308072c1306030501050711060c03070302090a1a040f050d1203020d1d070302090106080108030702040c030b03010f0e0105100311090a0b090705 83
    0x25104d4801804000c0640007081008090700444136040c0228041c40003007040c01c02c0c13818051138800558021070b10130034520010801e041d401502c00d07400400920780402e80c140c0076140c01f203080003d1600006a40684541d2221940c0c9225a00b2101c441c5c400d400c0c442507640c2c1c01c00a008040464128001c15030496120f1a200c1b404a00d8a02c10b924030040141141c880d248218003c0d0440c0c1802030304441d0004011038010b4121b0760b0103c007191545944c50380c5504044506101081940c452170288540600301c20000b88424170429522103140307001620ba5400c80c0703459001e41341d00d88180c2400780c44024085c40e40007001c201791050b00d000b5140316056036654882254092402d10805074203401c188181c80c01031815402c643c6111843c0d02d404034800ca00400043d003114075a105645e6174680da0408022124002e000300b82d4004421504070ba11549952680b0280b5081d1049442c031840119001400981d8030380e0207105449c00240804104c7c1c0741103c00541103074041c10441080c081840c541002d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 158977949 1250 158976699 158976709
    0xa0c0809061b1c050c101802030a0c1401051c09020609040c02010603051209090c1e0406120b190b03040501180812100302060d0c09080f0d0809070e0f09010209041415 73
    0x12040c4400810011803201001e000824400c0303021203140f2441f04044015035010403055544034060038072022050b18041c8a000c070700d030010343e096040c80007d010031440c0341c0d0b20050141c42c2c48030381100401c02015510002d40f42d486003401c0e45601c28509145550016815805182900d20440c1161484c40c0030f000c05100702e00895100715806080b00300050307030100351700001d8481c1400340000b020300d6080143c5032141c0e58126030000c0c000181c0c1e884d24020010123a00a000e05520240e802040c50220b1240c01d000c031441502940c402d1500000101d001c10009501034402005003074080045664285010001a0b01620516103042c28580119005142c443c8100040703903802000c084c6030035010441480500528401c1a007031200680e400140c0020a2010001d00b81a00c2c024050703c40c201a8058500c28000e040120300c0d50184000344140d6080c11038164120244031820310315940c0d441042406803188a0700960060309102400703000d00740d1031144034090030104042203c11028101401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 158979199 1250 158977949 158977957
    0x3050d1706040504022d03010f0e060f22151404020915060301030609031e0908010e010605030d03020f0f160614060906060309010b0a0e0403030608030a0c0809061b1c05 74
    0xe50300818004210001b110300522a0f007148111a145021801040001034212820440c405501c284c81e255910000442032080300e0303001c80324040e40440c0e400e003082c4413101c40d03d004001064110030b2400a07418000c0c2540d0304c043c6080044420710507a096100c0d5410013440a8400703d000714010000301d080c034070748020400401240640700900f140e19640b5000c015005503017040d410f01115218955089001d201d10440282c400d80300c1d000d20070324041c0ca103030840d10b05d010082c0d401c0e4900b41083c0542d03a0040f030203450402e031510b000b580b500b00c90444080c85114006100c1c1c44203c0014502d0a14a1144280440759001c0c0008028480341c40742429a449411241c560f84090b641000650614092002e1904615903800000e4001c6100300820030210090700000c84403100a403c0104250f45406400040c000101c083c42c104501381030043c00c4c51800382c400400e614030105180c06140c480509503907485072060f61000d06500200c04458561303001c54107d51084401eaa00e441095028030122 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 158980449 1250 158979199 158979203
    0xb0102010605031c0c08210619050d02060d0213060806030c010f05070f081912150302030d030504061104120c05041a060c03040806090d020715050301090b01030603050d1706040504 79
    0x1380164510101140d000600e0201151901018810701410f80c60f0702c03401e80f5524100c1030880a0711b00f400001c01c800f40721041104e0041101e100d50a0240f5140c59070080940e560555420344c440700421003184c0603001d121180c454440b040b00300080c0e0b0550003c0124010344060f0f044d00c003c0901c50004441c661142c01062021403000c03c0648005400075206084a0380500845420076041c42e4201c151039a404c005240012042c0d40c0c148600080b84c4141c50318803001c0e400d0302d030b03400d4510fa003c04c3d103031521081d00e0390030315039120000340500009070010070301d00d04414840782e03850761202501c02101d8101d41c800d9440c031108200218003400d0a21881422328145170340c811001410104101c03040d80030301f888940070b000600001038040810004680118040400f034500c0101500f002403400d90203a124005154401c0074051240b6001000c4906582d8140000300303506808000680240003160701c0241148182e040b042c0c080e6602150005d010b044c0580344803025280d4000301b0060fa0303020707600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 158981699 1250 158980449 158980483
    0xe030c0615031b3015010503030412020d03030f15060f03060e06040207140115030b07170c03040303090b100f170c091909080904060b03040312050606120103060b010201060503 77
    0x2104645250a504c044442c112462040030300f03407158125280326111160045484d0341c00707940c0044a80103819001d60141c04150011030900f072500034460120907801601078062400b40c2e2820061622907004060001e107200700900c12070404100214900c1c600d48503500006016480d2004850303ca030003403c084ad061301c5085c87d029140c0d001000700a49c40000100c0d07009166007040388030300b4000e00a246c0400350244883c48014070b5400c18985064000f8125410020004e440e038000c0c607000b022460300a900700704001e03117035a9640fa05034001c00c0c8186020b440e001c0c004082240f021508440c1200b0b985075000c07452000b070781c3c907400c000c40c0002e11f10340c2d00030903003103642c401e03401d4100405000e41c49842107500c640c00220030300c01002201c803e62000c0d14400000030365600941458000c1c200208402101c6614626040d14002d1505940081405c11551200e000c504507554070300585410680c0300c800c2000f41c0d43d4a283c408014441c0510f000d02550030f003c0002082c1c50b000c620b0841414290030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 158982949 1250 158981699 158981743
    0x4030c17060420062104020a060c12030f02040308030a050603100b0616240c090e0112060504060605100306030507050a0e070f030207080a080f0a0e03070311010e030c061503 76
    0x2504507000510f40c440d690007400602040c00c001e860740364611a083d400f00011116824203005002e400c3c041a0840c0007480000c1c00840c002500c408016400882d0614002451140801e07640d80644100d5001601c00740d400b106100e8181c0c0143d0045005420480c02c88403100b00c00b40c903100950380b0702c8a20541c04503080c0410881d00d9540c401d1a42c402c0d00c1507085880c0b10366000ca0035001d2400446040081c1c0780d03140d0481d141a42c1040490001d0000b070b01411441350b03d403e2580c0007002040300001c024a0315a0007003000c20181da0031103000780100600c2c954502d802084005c00070425440295242e200d0080d001421781840018031b010b580508103051502c6d910000d0981e03148010780001f00c10103a08111480100c0c2c0c098002d46000405a0b443d415a0304000201607001306c405440c01c16440d10348286500060400001c8414041d0706040c030f1558001d40b071003060b00405c18890600d0317103400002000441d07000d021600511611003114903c40c0c0307071461020300d5a920b205017119146c08017540 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 158984199 1250 158982949 158982983
    0x30c0b090118150513052101052802090117010b070209010b121602072105010b100e01030b010207031403120a0b0612091c08070f030902030307062004030c170604 71
    0xc0c017403449403401d00d1500c00e40c0c50000c00c000d004442280c2d0300da4149003aa0410311402070091300d411014203400126801107082442c00d801c010b040784803403810741c0061a81041d1b40520000c090a21001c035a0082a42e5902d03200d084c0b90b03202d41c5040b40304a44032000440d0900210003980c8a16003200300250b5240e40c1d101110b080c002074415828154412402e002030740d001d20390420764000c42c0d0002c0e00da80c401e02e18503109003034882101d08244a00e541d25881c840542e1311503041d500c184001d01e004115500b540c2d00507400d040b0290070190a80f54881c001034071071600080100300c070880d100f090205564418651204613842001d015130701c80e4040248008081340c4003206508129032609480c80343d000c00c0e5007510341c001031400c40000f29070600e08000c05541c02c50300c8041c15407510b040c103101c0c40f416070380020349a00c01d29600a2a55649820416401440119006882d074a18a04030358881d1241810700c03680d1000e1080402e08840c0c0600c0060000020481c680100d50102c0c0c0780072400c501c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 158985449 1250 158984199 158984207
    0x30c060a020c03040f08010c1709060c21100e06190312202a060d020f090a0303030f050a0209031009021c030306050a120506070c030504030c0b09011815 67
    0x102c01100b0756480709200c0450342c100f0040c444001004040000140c0c1032003a5006010707490303034240540d0070100d100104019000d000c40d20951000310000c81076980c5a0344d0079418400e1410302d03041c0403041000010071000e16510200b500c01d03a070f0600e1081c0441c1d03942c02c0803c03000305550340c0041c0b1500c070a9001000060000c01003a00c04c2e20580c142210403080c0703c070102088010352a2045496800b04800f00f0345c0c9405143c20314400340043c1003800031032090402007100b034402c90750500901580020b1040071b220010064994601c001070102135141d640e820001d0240c404861150340070381c504000f1074548803151003112440c1801402134043c40318101007050051a0f00c400587e08118a105400c0c0004101d54017640c020340b09460000d145401d00c02030101c12a880e8000d0711101041c98501000700c2c20000340d1aa1207411072034452214034031391600321454003e40e40001e002480c41000403031190340120107809981003e98520000285150300c90040134054410720700c0e01d503001104080360b10b01c1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 158986699 1250 158985449 158985457
    0x7061d070303051639140108040203070e0f0103060b0a03031209020f04060807080715020319170a0b13150504020d14010305010c1101060311060c0f010501080607020106050102030c060a02 82
    0x45135440341941604d441e8103918205000318018801280c108101c113038103c05200686690300398550343c1500c3c1c2010041c0405101c0c05090364140410900001c0845d82d0800c20440a000342000c0c48450707041070701c0090309050b000c0c00112006c0e410501c184141d070034420707040b80441e41c041d5240741410380031149050061a0548040c1d0b0001c55990011100e9159400f0303e00c01003000e072004119551421034041c0c00c01ca030380d8000201640c02c1d11044104517600106032a00c400c0d103610201c0803400920070a4440401c100100c00102c0080c104001d10b60348554416204201c040d5410b4007004005031840c0212103401c203003990140c0300340c182844207080c2580540320166500c075002a14055000c04020081803d07403044403031340c0d1a0907690008950051450440c14003d500900281d4107640c0c42c0001441820801800f80c0e00c0802d142c1c5420404101d4584400f062400800040d61070302d80e025102c440842d0410095800d10b10001610b500c004115903c1040b020051304560b120383d500316003e940 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 158987949 1250 158986699 158986717
    0x70303051c0c09092d0203090712050601050a1706070e2103030406150315020901141306080106020d090b0306180112060f060308070201080c190507061d07030305 71
    0x350280c8001c8035009115008050001c0c3e1941a0840d00d03000000341524940754000c003a2040008444101d0300d17542e54802e0300c480c015980561284d50300c5500f10314098107075000d654024142110740c828003202060660580da42503c13a15100394903000b81e81b200c0365107042d18080a60100700041c0c04144a803005012940c40207002500c1c8119009034802100c404445504a940001091100f001a01d00c916003510343c1403200e02c14200e1841c1c803080341301003841c02c44889054000800311b5803031784034042504004014000494807080203003100d40b055541800789802140402001040060000071200848600c680c0d46060060412082e00a00c3d00302402d050340000c074543c03541612461507812140a88041c004d4030003110003504080d025203c00c03400c8004094506042400490b4080e41254280703a020701b0301d151180c582c60b01d8130400d0b00c45d00007103c0d1190f0400c44506c0c42254082c005041c201c2c06600280039003550750400351441c44100707040c84501e500402d81000024054809484415 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 158989199 1250 158987949 158987977
    0x60f07020f0d050d0c030506030a06020702030a060204080c09090303130204090503040302040c081f050109050f0a03081b060a060f030b0907080105280c0516060b030f01091406070207030305 83
    0x400c507814500e003040068420021800205800540c800b8510940054181038a01400b080c02c2c405d010903102d085114000e4542c81e0002480c1c0d080d03440070880d0610080e231000d000c542d141ea03104200d0707032240844136410b4460502c20b00441c81ca00070020a8901440054207001f00310985a400c1000070102b008044070300b40001c1c400080940d40d588a001c080520984404060346070446070790720b00c5801008612100c003030251003442035992110000d001da0320165200141e411810300060b40c268916480100b1240c0000307845075000200c0030007081120401c008543c5561a00034414003941c1e0180540d00c061882c400e0f0400109030041482a04842c0740419161160f403104032240c00c0d41c10889159030026034054100c281d2003d042c04088403920710010400c01010001801046442180c1c82440040b11104130f0506110195110304880742008013201c5000050051183c084e0000840c01d9130a0148143c03c207422020204500d032140001e50301405010342160b509490680100d00b10081c15 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 158990449 1250 158989199 158989213
    0x60a27111306051e240d0b1f020106080c180c030c0c01020a17070302131401090503030301090f0e030a090e04030309050a03110106060f05041505070210080a0605090603060f0702 78
    0x1ea110103881501c0d00780000841e034011030315113050002c0300790a5100c100202091407681541051a501522102c0940302c03800704040000d440099001c001c0d50003042d4280700c13180031240b19140c056000a040b26000401e40e0800c411000812113048501d0b14400e0040910b40000f40c40c452070000150341c8030a00744100390070b0004c413034606400c84e0032180307100d400300300040c444c3c50501d03070a00ca50540c45105484c0542c07921040b440b262114010300d02c42c0030b90b000101000d03041c0b5a800395100700050480501282d44960b580c0c114800603003800205401c1161902d825440c440b20701004a03903810010b512120451854403804040c013001c003d10550415585400c02c0300040d105115854484d4040e5840c5401441000000790071070b00154094018010000044d210700c0340c0101c01d0b6022201c3d07581110354031a8800f0703c00d4600348a032038402544040d102d00f10803c420380040244d1301811514100300702d200c1d110018401d0295090f22079552552010000420321454006c107158414110301c1901d080c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 158991699 1250 158990449 158990459
    0x903141e07020301060f1d0a0902010f140409110d051003020a0b090f0a0308030402010f05210a0e12040305010f0218120c030d170f0709050108090f060a27111306 71
    0x724000940000403402c7c0508041a40904060507a50301f0104002c5e04110a03403607940041e295000e10090316081c047c4100c02040141050b4050786c3c000c00f0682c0041c88004212655101103610030740b0b201180600d850b012034250080b02c1100b41c2a02c4c0e003e80001c850701d0501220f02400d400410f54cda0344904610b6000074192503600808000318400c0c20340039100e092501c00507120142a5040c6000c10200384650305103a00c0842c0b0220720002e0031801c00100c0e07202d0000007000b400c00c980400c08107110784c54000911906500c01001224020740081045404010903070080e07100340c0d0300446c0200c3c4040105115442c001c80da44480d03a4418040f156100c0b80d1401003030818003501952001301d0703015a194003629042c100c50701d40c0b050b080d40500f96140b61500c0c010b444401d103400f49030b042110041c00141c1d80407041000e96502400b1380c04075102480c080d6244000780240d000344218000740621400c510440c2d503050f141406074040030015840b082d0b5800c1c482c1c900601d0306405105525070800281c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 158992805 1106 158991699 158991719
    0x1d1504020a0b0d09060c0e0307060807080601030b010c021509120c06070f0804030501150306110c0604030e0103140a0902090915062e030903141e0702030106 69
    0x10f100d03020700c4103e0006145424005200302d02d0401e0392500d19070484402946584200d0413610415101d0380f084840d0032041d156107010880840101e82590301030b4019078100c03181032400100130328580d0001881c415681d01c0c901d07a2032800140304403075410a001c01541000313250707000300b6040321b1070004035640307200b0b0f0000a840b051010042508001c2504c1c03c5030300840e003000083c04120900200c06411540510048500390314040e0381403040540442a144100b541401629460b903460301e05071903460f80000301c10304040d51800200750030004c0340f403103a008604411001516005600c10b0028440c0080c110307203020707481600d5003c82400d00b60f0a0300c0d4060416640c0c041101e0044214440c1500961800e02c20990712100c14000d169043d4804803000b8043d55414900380f0002c03544400c503100d5585d914401e40009900000f504c0c01c1d540c01009801e1025000181c0b040c0d07a504001 = true := by decide +kernel

theorem cover : BRFrame.Cov 158812949 158992805 := by
  have h0 := BRFrame.cov_init 158812949
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 158812949 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 158812949 ≤ n) (h2 : n < 158992805) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
