-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0035
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:29:24.954989+00:00
-- url     : https://prove2.me/submissions/85c43d38-8322-43a0-b623-0efbc5e09dfc

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 6115115 ≤ n < 6294971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 6116365 1250 6115115 6115127
    0x17150a05180f0105040302010b01090b0406050318011b02010b0102070f030b0a0204051002010605030c060a02150c0d06060309021e09070302030903091809060604020406020d050708040b030408040f080a08030106 92
    0x216403070302a030a00d40342014884007002040d8518074054000b24961030140f500a0943d144244128188000c21b0000d001100d03a800c00e0b60160358140c6011900c03992204030a4280d44030250628040c0e500c4c1c044d1481e6107518928010395404400d4000b07101003d0340c071004907070b035a80f42d06c9072072080e0321004024400030fa060f00c802074000c0d07a640005414551110b00060100e40c1d56029130025030756980003004542400c4c440a58011801c0301e180c2c3c01c110360240b000e52103814400099101c51448800a40d01281490a40301074000341001000040c1c0c5602d00a0024902d0807400d0317114406515561410000040b01c4e01a1204050480d0900b84c440341820781c06504040d08000a600092000b1115512000d103215160544001c510000742020745800381080c101910050285004010912040b07030001051448000189000d035982c014505101142d800f40b40c0001e200c0e0070700001480148010200075206072442401313059542e0390b481144d03681c0c41040710300003000b00c0401d00c01080794a010b80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 6117615 1250 6116365 6116371
    0xc040b0901030e030408010c081914070e0301060308030901020d06090608071203020c090a0b0906030109081801050705030703031b0c050a0303020904140702010606020c01050702030a0f03260117150a05 88
    0xf8040320b04003078591002c03c0c2928034501521700028608020400084206811400c0c1d100c954081003005403d9100100110780e802418a414000007089a00ca01d44003588050b0042d0b401100407512402c041a400e400703540301030b905001c007030f0030148040340c1d90000d031151404031241180104015460314905003041014800d00340c00354003854114a0035900c5640b80680f0800381000006042c081c20741c204102c1c03038000303000e03d0b000380c0c544180d01000528040c01c440c00880d0b82080c0c0c0e40a403501c0c0c00101d0701031003240002003050001081c104201501600214001c0c814401d0400741000003110403a5450b40101000c3c1c99039000c42c01442c0400d020364000d014004025001180c600c454110b030081c0140203030b40724030041c0e560311070400005a0610080340350020910700940303044040c0d000030342c0d82e1501d40c00190410101c0d045c1542010b00074208605030101c403800e000e840c407140840c0300d40a14402d22840e0b01c0a030032540003000c801408240818524101e00f100f0810303455116030300d4004c0c1002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 6118865 1250 6117615 6117641
    0xc06040605060a061412221b0801020909061903060908030901050106050a09030618020301090b150105090603010e0c07020a06020a03090e0c1c020c01090804090605090103050a0609050102120106020a0b0c040b090103 94
    0x45013000101e1341c01f503101e00580c0201c6048540c8280d103414210070211950288240e40d105025086e142d590300c030b490340c0d00904111070160744100b8241c010b031901c0203144d200038042351a0041c003500f000864800b65100f44c403220020043c81c0c2ea120700039903041c4118011040002c20340e100c10b1000031810360000300c0c41d8516100c80180109036601080c00c551901405540701d5103040c04004d40d1b081940c201a403560001e00e0054205050000880c5072400180103010410082c400040d80119619003581c800d01d80040002e078074141d80d00000380d120f880c504002c0d03000626140d03020600490000940d03005004101c0101e2500b00c1e0300b03902070240180e4180301c4003410340803c001c6070140424050541054080c0c0740c4103540314542042c58048a101c0d034045070147d40c401004101155000c500d407079034075401813030101d0071150700d1418a009105491608513400384200c0080f035a107074001099040580714903800c0105844058510003d8091485030308404442003051602c40d520079040305200c1000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 6120115 1250 6118865 6118891
    0x7030c03081b0723030f04050d06111209060109020a17060a080105010b04050906030109020a0308030c07020d06090308091b06090102120408160e040203030304020609060c06040605060a061412 84
    0x42d6408a4103140e20400c400e0700c80d11282c208200421130405040302d9402e00c284021481c01c0718000a540050150b88a002d229440c1c41041005101c940d030400940714007040d58199844099801c0c20214030001d07a004030b104d02c500d0002161180840c4211f9030340200c03076180e41d40c0d8542d240c42410f101284c0140416001890381ca8002010202401094081d2401d0f941d003a07119803c2c04203004004500500d00b51103a030421191070050780394404402c00742e0360000d140c243c0e85d543d03030f9650010f20b03c500c820081d00115806030100c00d104039a0b00c03000d1007038840ea4800405480314416a0360b184110201100b6000d0300c40800c0c455850440010207921a060059034000043ca100d0040c803078005900038090382d00001941e100f11454100e8001c06400d01e4018138030b0070304042d00400d56a0000810081c0a0030000404203050398034001680d90016609003120a02c0c0361510300b40020303007402e0300d41e540100c0f4140c1020032214040d810340201070404120300345c10106120491840ca0b040075042c0e080b840700c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 6121365 1250 6120115 6120151
    0x607030e10091d040b040b280605040c051e0d0b0a09090201020c030f070b0304060b060a02071a0f090409020d020307060f0906051801030b010909150503010b010507030c0308 76
    0xa40007400403a61032151200e141103440c140c0980000001580d40d40c0100c94060f040200003014201056005034000000400c15941e031110400e002c07003e0b409100d01c0e01100c9401440e05552030300b01c14161902a2820300490501510544190040d904501885041f2408210007003c0540142070190043d03100410000808000b0401c0000c8a4014402c4591204210425941c04203d601c07a0300d00c2c160010403101c042461040c1e200d40c058080c88803103081c00000316041c80840d03040400d045c3e00042c0751998501c1340820103542c07402c1c04e11402d825003104003550300c1100c0c2c0300e000382e03410f86020b03c03625490041c6480801c0001e101c055001ca900c0310200c82c841d400350710300b0019603024000b02d0f00d030419a075250400107440342c40140e03c500d0402404000113400c0c204810000c5001400070708020a107806080016100000580c0001c4130b0355280444c90000c4901c0e0598010031150160300812026181e0001118948230702900036002c90361040401c0c000a1184841684c485422070600102103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 6122615 1250 6121365 6121369
    0x30d050402040f060e061008040f030806010e040f0b09010602070803070b13060c051e0306010c020904022404030204060b040302010206071404030b0c0703031401030b07050a0e060c01020a080703050103030804020607030e 96
    0x54205e81058516600703100400ca180c0c20080c072480001e19003410040f4080c503103540d0322080b40c49003a000408000504000c19140d03405600d01040000000f441400b8080f119140c1000608040c65076034404c0c40503800008070103001058117000e03074075800c000c0c41c642030365601d40e00c03212a4003030141c07080e200c2101c055034086401071003140c1c05011540e5a070f5070389030300580c1c10b805601405502620680390400c20310200780c2c0c10201490b080c643c15a1a03444598550000410507040d00000440341811444007a1107007000c40000c1041e04c1c404c843c104040b41e03d410030f4461a00540c0070080c09640314001182e440c501034a00303080c070010324980e0546820707140d41e00c0020b550005e68101e20003c5000c6421020150140a05040311620f26500d2903c2d61443c0c88440007014060f02400611800203100c4a0300c5104014031540042c2c083c180503550070710540928001d500c0216041c5c005907051020030304440c807038091a81240d2301603482500c0e644440e02004456840710700c0072000d200503104521200d03 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 6123865 1250 6122615 6122621
    0x40204030b061008100302010804050a0f0605010501021504170903031303080702041404120f020309040603050a0203010e0f031e04120303050108060c040605120702070f08010507090611030d050402040f 88
    0x914480e100900722428075606000055600404003001d020803082080040510108103004583c0c091030040c04548880c18200e0810005510181420320184d26000030301c0b0f641e03003085040358070a03030880320202d45801140ea090082510000c041d40d000207008602c01e0388803000303400003000c018140c032714040c0e2003402107901038240c3d0f0084420520100320f0005619182c8552040100309810f2400c1a14041c2d60f5828614503880540e0240701c0c8420180103070318030030400c0d190f01980280c0104030060316801c0c0680d0f20040290100d20a608200841821141c0400c080e41103964090043d0304001941c03040712041e60074100100741500e8244400907103d14240c04004049000361000200e079418960303050304040008140341e5101a041000304010759200c02244c3e801c1d156800008965241c8103422418212158004244200c3d11440440c6238001980510b00502160302e4000300340390b503010f081d112404102c400c40860b40007440b0000381c1025540010381e10510003040022141c41e110401801c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 6125115 1250 6123865 6123869
    0x708030711100e030d030f0e0d030603050d05070308041401110d05070207140a1701060803030c0d0606030507090612060803030901090b010506130315062c06010e01050d020a020c040204 81
    0x28014046480c03041d9800c00c407005000c4035101c1e00d8a04642403442c0c0200c2c1d0f40d010300d10110000c0698a003503e4103441500e03400540400c5d540d40540f850380c898000000d001d04041d01040d0351a01482107002081c5015030100e80d02c160b0f058032012040d0380c803a202c4280800607440d07807100c55501c80d07000b84450510b0000600711500d40090000b80c03030824800080c178241540c0c012120181c0200c440d00b14556a544121089400801c5030006c06c1c0003240c90725014188940c8180140c0c4801300c14401007416440c0500b00034120351004000169a8007800c400b034400c2550b40708007107003400c60148522031040050354500c045030140813508d00e544a40c1645503510490300c800c5182d42d00c500880820002c207560fa401850f0488410b03084c565035503010100180d2510008200764402c503401c41400301960044c0008100080000c05085041005000c1200086450360700c16100f000001c2c4541d80252500340749280306950320b0b800d000109007068001d6012803501010b40c4903620199183c1d0b540c40c0010302c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 6126365 1250 6125115 6125123
    0x3050d021210060f03060308031f030602030a060518010302060d0504020118060504061101020309071203090305060403030f05060904051b0a0305250f06020d12090f05070303080105010302070503070b040507080307 93
    0x2d41945030031001000e200000301c2500070141441c3c42003010500101c29241c0000b10100c6506441d209008403a20b44c400f01c0d030000340854000300401042d03010741d42c80102222030a80315110841c0f0000c50820030488240802035102c03a061000700003d00301680201c0d030140c4181004100724000140200c3c120080d03500020000d01c00040a00400703070b000036410013080384d52009600354142064440e4035883e040c003d0701d4007520310141c000207041c407a5010000468209041e43e28609180c20000e01900070b1084240e0682d0915011071300c2d41c1004114140301d40c0d0001e025007032011a02d1640e41c5d2000070500040c1d132120001101002059044c018081e444510b110001d1081c4402030001c01485c01d0365000c2c210403074880b00e0401003180c000c200d903100d420441c5005403d581e904e0513648001c1810305005080e0711102d4101c078041103800912801aa4001d4540d415980c0c1c1e00d1004405078824040002c01c40c1d001801608002040d41442580080c81001526043d64685e68031a1840d003120703006607 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 6127615 1250 6126365 6126391
    0x4050409060b030c010504050a030b0405120c0102070204060b0a0804030c0203100e010e0705031216031818050c03010b0706020f040503011112090309060301060e0a1503020c01051e0403050d0212 85
    0x100c9514003000001c4520380203007040d1f03080c0380c0303003c0009403844036501c1701801c0944070384006400c01505010000d0351040701c111080c1c440100f214094001c3d00b003180c08900980c0360900101340c103820041501c4030a94030395074100159a803070754125503034803503808102d800d40700c1c01140b04031280c001c2c00346a0003064024000a07840703403a01805407400616034003160081d0090103075100b070310360400304031105800c4190781c904004e03109241c1191882d04420b0b540300d02c220890404203403070950030054503070f060300c1e0b032402d000c141c591091810b401e100030710a40040060170045040001c0041d0043d050018000911509140e51080400c3c00e554810440d05002c103000120b07904100c40c05500c41d500f01b0100c50043d07082c0540306c400704900e8030040c00b40506010565010784002d07a5100400c101034611542040e244800b104000b0300650004a035000655003418001805031200256010010411f020402113940320b6850070380d002e1380408480381000e9020442d440309014208801c5014130f02400400b = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 6128865 1250 6127615 6127631
    0xa02010b0301230f01030f0201050f04030f0f060e06070503070e040902030105070503011502010c12050a0902150a0f03020708040504020c03130305070509090c010207090b06040f0905150607030c0803040303020405040906 96
    0x481d1000f0001c1c00340061030301000c0180007203aa403409440410340d0a080103a510301c41d4644550807401164001414019a01e90290400c90156405400184200000d11491006910b410b451b010300310396440000b038041c00002e40760b610455140000c000082c1c40064031040940201c1d0943c0c3c0102c42c54000320300000010060180e00481c0f03082d54103c188020010000c0f4958000e110140708600e5400264507240030520004495000011a541c014448103c0c1041c04c00745080d0703600f020404401040c2141401c031901402802101e001e2540038418501d0701e4100010400207400489160302d0307911091010945003000c1c050103002550203000200049490601000701c0290018241c20868000300350060840c0d0b00000c01c031040d5001d030b139404141c0a03000f01c04188540995030225201c00400d4800003410103007640494040d403102d4003109c0c2c0c01b0011106000c0c15101d080700040020b16004509004116400c000c0c4d40c01c00e20a00c0c01500c0c0640e1240040c06945401c00247d400c56075030402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 6130115 1250 6128865 6128921
    0x1080109020f010f0c0b18030304030e0a12031704110d06091205040302060306040c0201020c031209010510050306070e190305010c080106180506030c070507030309030507080715050a02010b0301 85
    0x40301c10100d0910b0404904c2510000080c4450000340e80104581e1102003c5040c44a00740c80c1c600b0501a100112900c07032505050091003043d118140900611a055000c80d06003100141103001c660151141c0100e6500617103c810704240080013910700419440310f45145968070f0014a501c580206004100c0110034240008900c00a40c041020311400304410801a00e0307200580b41d008200711000500f441e02208241c4c0a4469494008050300001440d040d11002003404240201107840080046a941503014502d040481c02403980c50351080000902c443e21800c1d0542c8107000281c0384a03004540d00103100480680303034200710384603512120310021183d4800701081c01002076203041040e03035002c03039640d15125140380601e5000f1000000002d03082c0d0812012140004c1d4004121004650340307090090074441503010440316802103105c0003522080000f401003d9400a2a80c00d000c001841020303184d59100c00f0b100d000399500c0f141c034948255004c0c802e0312144003c0d10310f00c0d50322081c800c2c5 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 6131365 1250 6130115 6130129
    0x103030908010b090103031d0a0f1d060f060a09150801030308161d0d02060c0106030506010b0702010906031a031b0102010c090b040509060111010912120e060402190b030108010902 79
    0xc1900d80c9810080f4902d0399a218100b41100d400d4101400010103a4400811980704082038039000000349800199000c1d42c0f8000d041100c0b504c036203200c1c54600e002107000115206070788107980800d14124852042c5015030052802080c40c2c20140001f40da01c042c1c00c0201056a0204004103000364010070906406c951300302d81c4211162412401d0300412800600711000d160048070b0010300c10104580c0c60348408071101e41c450b4000b001c0301c0d00e4510000480f8040e04081c0000c07205806080300010304120a90155009943d05842d849292418907200704e0040404602c1000401d00103628440a078a041c0101c42c00c8a400d404207440454a080c00642510109030250b8200803566000300106207201e0144c0301510412170b07021103142c8401e00100c96140c5c0c800c03234541c110b529080c072000030400030084842a000d56500c2e40214440c8000c486400c541080a141c42d85d5045180000d00500d0001c00e2207403032103e960301c0040e0842d00c607900b1100680090300200303007583d52007243c4400e602d0500 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 6132615 1250 6131365 6131369
    0x10504031b030801090e070e010311040e0d0c02060901090905100302041505010801030602090102071a040f0504020c030d050a020c031219060323010603060507030c12050108030a08090a0506040b01030309 89
    0x9a41c03002080c1641c1e40060101a0501c24a402c0ea5030703da98585181c9000d0202d074000700300c00c1d88022180d58403400c104241d52298031203a8442c0f8500741c1c000321004004a40f6800c032100c0c944801c40584555020301425032312035007402d41000000c450110318003203284141030240e581c00031014003084c1944180801c03200c1403015040c0886149004005c42c0e0391020032141942d600403005611024001d00503441c00d480d5802c814109840c0c00c003004000b84000c00a0030441d5030542c00c1002d50b0344e80b00c0030302089100d8040c000e403440e0001c1050300b551084e00d810543d00000b09500c014506085082c0880c2190003000c1c0900c2142008001d10110b1107403105204200002d0b000f007081440c0c1b030741c0d460f20b10b10544011400c5280f1440e41c0501017041c401c3d4400c00080d0b82020307080c45249840c1e10000c00500f00280c1038000301c0c0e9100c14401441c8820721515060b200c10b40d00440c504448017000f91031061004015090320300c10072aa40700000d03402d0114900992040980040550443c500901010b040e5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 6133865 1250 6132615 6132647
    0x503040b0901020c030d0f06151d040207120806031213030302150609130c03020414060301051308040501050702040605060c0c10020109051216060c020607030b010503010509010302092701050403 85
    0x510003800c461034003100b210703101801c029001450400c7c00e030b040805040d20740d01143c0131569040f01007003a41d800610081e480041c00d10b010210317003541b1040008074010f4120142c40100e54072005203285000b203d185070050002030440c1c02e110b00228030160a90f2000030042c0d02d07164500400c01c01c1640401c01d000c40030a914100c0c070402c0c1f4013100402d200c000014804040442c03580085002d00c41805c2c000c074040d64020344140462030721558540344d00301041d03422134002d610b40f500107100e171f040300300280e60656400304401d490b05190500458480e0000942681c0c403542c0c50000280a030b5603070005200c00700c9003402a003601c9402c40200002000d0f11203100b0b05590520806c0e400044000c99541c1c9001c0301c49030816214441aa4080e50320481c03d0b100412084c03408800000d080d8000603114820903540d5000d000d4000303248011211808203204183c0c010729101c0c014001403601c2c94070b00e83d000da001110010085038196020590b40c0503518109040d03503444040c0b10505510014803c8003030320b0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 6135115 1250 6133865 6133867
    0x306020a02010e012702010903140106030b0702030309060c030601020c0402130503161404050c0c0d0305090601120c090b1903030906090f05060a03090813030503040e09060118090201050d09030503040b090102 91
    0xb00031010f544501c504c03070041c00301805c464180002c40e802619030038081e54103e500b0105040c400800d250007408a404240e50954800700090201031002089900c01d221100c05401c40352545807052146400c0a010b035415030040c001240c030b4940301d501c0906442e200c00b8581071456843d22041c503040041c8940344001d00101546c05018800038101001c01542c1d090310005034941e244200120795025041d0a85454040c800c0340280195264018a014100d50030a448103640e80d41c907403402200c501c0000400984e81c190081089981683c4026150b40300500070180e600802c2450116011301384e003007100403035800c4d801881359aa020306c0031b60160450b00e0301c402e88a4101000500b03203005006204040640303810074101003180f80030a0398502504110050512501c03403800585a40160081d402e49451080c0084e83c03070100092414129a2090071030884808049a18070103403100328401e03070500004000e5082035007190710410714220300035610b841d203d0801d0b241214009c00064138401280c2c2c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 6136365 1250 6135115 6135131
    0x1140d0515040608070b0306040f0e0303060102010b10020d03050c0403230c01020a03080609040201030b0a1508130b070c03050705030d09060e070305070909050f060c070c080105010f030212010e01060306020a02010e01 95
    0x1800103070340007581e90200d200d47e100e42d50100040c1c0500000301d1110350781c9081104910386420000003640c0a00401d0b0002c2c03107900c440e0410311200c081004200d10050303100311281450b4502907840550448802c0c61164505a1030340c075407007600c03040c0940c0c1c0544070320719441007101900c0c00d001c90b01402c4000d2000e040b20401c40c0c1c07001880744c08094170070b40c454a98900400e013160700039800102c3c100340280c0b01214203540c3e2510700004002651a40340032031a050009660f02c41c4142ca00640300d03600054142041d00c0b400720450741941081030403001d0000030040b81e00807883c00c10213400c40341c64210010072030b18503030b240013020f90300d846800c200c403540065003d0001035070200d44c02d0140c464400340050021a10306049280c01d500039003404090040e6824041901c107030000512241d806032400c10551542e9075038240c2210b03024400c408500e04001020700045c64003d001180201c92030300041995811000058211040fa900448003207a00088641e40306030280500b07041c01c036459008200c102 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 6137615 1250 6136365 6136379
    0x110601030507030602090102030c0f010203070f0309120804050a0804030c170f060601140715020405090906070207060e0604090c0210111c0905010207050601030b0a0501150e010c0201140d05150406 86
    0x51250200130025134011514640036482001907503080c0480703400321141074180303540150003903009852080000300386030180d01502d40a801680c203442d9200c0c9009000540381d500031540500c029008441e1800b070841c0000c013040c0d0030750240002d140105043e07001240f91000c1000c40340302000c40c10490760415001341651103800308407a68011000e0030060003007216116108401c0c402e07408001c01c020031144e0040202c00304d5501400070345000b940d495485440709490103944103021035481005030310191b818404035114085516143e80c2c09024107003084c1c5c9031703810101507460741c0250b0001032703020b2014040044560300a04c0800244491981e00d0180d0141c0200c8c1c0e048089242045610340f55090310042040c02d40c112944243c001d000c0e1a03003541c4a1400324101075050790104940c60070040082036400c6e421300181419601d036100ea0080d40312000054801408000050f814411608801889140300400030260003032140030028091401d064061217601c10250181d000700c3ca4104140440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 6138865 1250 6137615 6137623
    0x5030304020907020f0304140a050a08030301061206030b01030311150601090302010507020d06020a080907090203100e09010609060902072d020d060b041104180b010509040216021002060402011106010305 89
    0xda016124031400380d807210703c160325143c11401d82c032406104c002400140c0351030007155001810000c80c0c14250450f540c80070003480d942c082c0541410350704200010806a030007000f210030b0100720001c000c941e603a900d03110394808190036402600810b114180d043c21389517051118281800284615000c10705010000a211500500009050003000540c100655452402090105620800039075440ba040382e40280182030664843c507652046602c0170800c90b4160080e28401e2407100c3c3d2950f60b052a040070034242c001c1c0034014011301d550b95000031035080c4d91809250060000d00d0f101582d69005c0c2c1c40c105900d40c0031000d403844490240745070300c0e075154075003c1c40d07100740c0b074040350007400760045810000c2c01025a82555070344245040d0040355106241c50290049a14030901c00581803070a0212800f520103801c2602d0005201300f10810b205d09d05980074010200f280c900080024031650b000c21026041604c0c4907000d40d200317200308011503030300580003a0382003000c3c8098101e030f500d541e03141652 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 6140115 1250 6138865 6138871
    0x406080a0908040b0a110105090c030709050106080a020706090215090111060103050c010302030405190b060a060807020a140f030d06050910080307020d02040b091e0108010207020d0605070302040e04121704050303 93
    0x42c01c4001441740360141c40f403406902c205042000810050038510100b039a0303032a040d45000e020740140b081c0050103060601c541070480310790703807507440055481148800c0203601c29081120110746d9018140d01503114102c03a02c0c505aa107000e0160740717517110000901910060340e00b201841c0c0c412801840016408526505e151100382000750312500d4502e400742c14080b400303010441c529108450034060200032085180251002d507100503005031104d00450b069801190640090303031000400400182c00e034803140d10b2078154601500d8040303901d0b5100d142107610825040145686410051025107402c8040c1038000400c00d480111262500d01d956442e0b02a80e00040e1007020342203120010b40d1511740150400c1e020080014480c0d1034000110403c4ac0c0000400c03c4545080308004120380005100b1140307501e8008103100b441d8002c9940c0e180c007400005120b20105902400009442040040494012481100072080e22003140c4001400b9a1f10c10f41d20041f8402c00c401030001251b008403c03a90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 6141365 1250 6140115 6140129
    0x705030c010519030207150207030e0a030f121e03050105040c020705030d0509030703140604120207060203071502120702031b06010501090504051803030a0605040b0a050307180603020d06020406080a090804 90
    0x1545840010044d0028040c45802400a54000c2c030340e0040d001c4e859008100070b5100340c661030400c0e90b0315010311003c0412800018104c05461201d00007280c12100c0c40c040c2c0007218503000d41c9000780600020a600524050700002c26164401401140782c6400740e1702d445a0b1510040c00590700e00720000c0d6030780c41c000508006002d80010390312030a032014007003840519049454000c9203400c2c20060703a0f854400302c0d01941c0140e030351000032032410f1003ca00c00e0203e07002580103505040c0d40707440e40d0000d14400f98842a00c030750308100c3c418414941c140040c1c410100c64002d961102000041102d111180012451480d0044001840725030380280a05013079820940340052140d540b02e00110002c00074104001e00380c403010040100224954101a0565509583c10b000312009038080c00616440750040c154580c0040c0f03414070101c1d25903c480701a0f1070b103066000c1105a0781e5008a040403906d104183d4046d0b4001405024850304002c406030009004d03c0b0401416000351580806402503003d410 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 6142615 1250 6141365 6141397
    0x30f1606140c0601120507080d0c0b060307030b160302070501050103080a02060705030903030a0209060c06100f08030c19032703030e01020a030906030e01020906120604050117060114130c02010b01020705030c0105 93
    0x509001c0c007080803401400b1030004403201c3c9c403148034002e030204507102000c44884100300006109818042100700071650b0081d54aa1252600581d440903001d11840c1074041590a00401001c140d0074022070303000b076004a40580c1d44840d5428003c1c04e01200601d0714003072000400a02a18901c0001241d601c150400340060321114080c0014003144542c00c4140c0c014429282807144049001c100041180e00c07205e04070042079541c502e025200d01626048054941001e107030031036002000f1000d0070280d44285004400b031001c0000b440041102c400c000125818001d0051080603003100c2a1130036920240000c040340704459400401040041c047c04041548902d90b15281035800d4045d103441402c01841180c656095005c1303d00c0e0600c08642403803045061030000a11003d802c0c18071301d40b406a0310041c2141e40e007042649030001c216a076005800103a069800c000004503481446043d100541c00414480c584e207000a1902c0f146400080c8a9001062002030581e044800c8401d150803030b401e00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 6143865 1250 6142615 6142649
    0x115080721110a020606130e0a0b04060605060403030507021003050103020607170c030703030b03070e0103080412030203040b0f09040e0d020a1e050307050303011a09130209030f1606140c0601 84
    0x1c01902c4511150551960b01045140e00300750042400c5210f80300580710100b80303081098882c41070750f1000d400007415030010203803100494035000d586175016000301008201160380e0400b00303072983e00071b40c403c0e000218040350b29011443d0010002d0b081c4041803806100d154159000a03800d0310548038003c004660405201035404602004e80d0101c401d80c0003070301e480f1103650402801501841c031409210780110040401d100c1220440b4a0580b50403008650030320b0f017440300501c0e80b00742c03015042d030640c8401c0c403000900000070700040045000b80046a5181d08500040c48140d551440144000d0b03000b40c049040245d50003d060b29196401c807407442c0c0d00c100c90054100051030300480143c01400001440400d1100002c000c41c121203210840c070040514074607840c101d5000701c142c0954401c1029a40441c203400c5038024112240000381940d40782425405658641440c0c0140180d0038520f904042000c2a040b00c05041d400c070070076907203510303000d18600640c4d220070b014003519441c80d401080f4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 6145115 1250 6143865 6143927
    0xf010f0e0612150c0d060e0106050418020403020406030f060b120615010e0d03200a03090501050903030d14060307050102010b0d060e0f030c06191401030b06040e0102040b0301150807 80
    0x40ba5007100b00384401440903042c60b0142944c20341c400d0500083c95400c00900180d00030356540d419040360032039901e950815090040314400104001da0340d090080d000d120100140e0368034401c1c02e0080d845404100d40c02c401520b050703c01d8924201270184182da4012944448680121315143c0c0450346040c204405100c2c1c40040e100f07142c0385402c5035000352451243c0c004140c0c014121041001d1005c0481012142040500382c1d0744080c000018001400000c04100c00d5000d13802800c4008002425a800c125211a003a805c86403401d11000d94800c400052100d81d090510144024001c00c0c802441101c41900c0030403045070780760000510b0a981d0308070055200c2020700c803110700b80380e20400340c0e1341e41c400c0079251f1035440c1130550f10078440504403e000c051801e142d100740c44660810b205807014903848c0d601e03801100040100001d4000e6103d440c02100c5600a100400c007501041c500b09803254100040301c103c1c4200c0308040420301c10180207000066030841905506440c4140b80a0300a085210b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 6146365 1250 6145115 6145123
    0x608030304021005130e130308100b070b0c04090c090303030501050315040b0a1107050705010e0a06080403110c030a030210060603050606070f05030702040c030c0e0103050705090603040206120702060f010f0e0612 93
    0x3004000d141140d0050025007c01d0040c1160140d0003039640d4015900c0355000409450103a10074500201410010200040c6c3e401e2100346d40324040501260a00f5628a00002501c49040019000600c1e049041c01015003500c1990301419080d4024401c1c41c00c4d860980c1017882c0b01038005081440382c0400168400b03c10b820102c1c08416641d1525166456881c1280d940c004038040c250100c1c40800300c2c3d20003410035078140c0781210142d95903e89070703480300d0310191000840050140d00a000e0340c5161541341c2c0b02001a80400c5100b1f81c020095610244001000c40f090b0360001802c142c2000c0c00d012032640c40030142d4003001d030420703558000c10100b45003491562050050007500182444d03041c102e0b5980550100080305142c0d140d03006031140b02d00044089540c122401004107006002c4546641002c501455000f0b1000d4941f41c60100300c0080d43c11046030031950000180d100c881005a00150800f4079401060740220200286041031032030408000018441401988000303004113104038204 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 6147615 1250 6146365 6146369
    0x8221103010204030807060507030908160c0f06020706140a0507080c010b0a090b03011a0102100903110105010f08100603030921060e07080d0507020f010804051e010c03060803030402100513 83
    0x4000b10358403552440e003a40305801c014800c0d42c49500e80b070000b80700d003402401090f1034540e01a45487c5031000c2c011022106a020355400d8545c010700303c001156103052000b182c405080309400826440b40303400c0c0300420207840110f020f8000e00c2e00744400300c0b10316006010380304c5c3e940d400710075541c4171075040f40104d0040c000b841c4480ea00491507800000d00700e0f5143c5c000c5825507020740c02804030300160020700491401520501d801a44840f004810807607440d40b042c85518402e1034101046850284c25500b0350300c003a00000c614848814040016440810514411214000d1f0a01405286480c0600311108601c502e1385080c800318060480d0f01c603d010310305080313070384881c0400200337103003c09250382c0d090240102401e500c944400c1c40a00b50280c1c080d83c04565000388024055824007004403540320300580100c4061082088049103120100060700c102c1c14282c0c000608003001b1300b0700400381d031816400084c00c3d800410900025840e000d0500201c078040d400c2a81d82c0780d036852040c5094852035 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 6148865 1250 6147615 6147619
    0x12031113030f0b06060913050a090605040602030106020106050a0605030a020306010c0210080103050c0103061202040207050c03191703010602100b06041a07020a0504020a120c03020d0e030307080106082211 90
    0xc0000841003003244101d03806020300503407204450f90303110818072145101e07205049900400e0340b20180309402540e0005548243c802c5004181e19445944000c1621402c0d182100c100d0b4010006000340c6074240f250500921017154030b02651403801d00041e2147c8406005950b540e50004000f94169008061580c10385501405141510700b0b40c0000801d40042800300300c0d49401954046503a0350703c01e020348000d680440302031031501c800e81c1d42040000d40c00721800b102c9900500c2c0310443c0983d070510480c086000c141c0420b840081709480c11445c031b5503080900701c00642091005120302a80083d100107a9141d02d08000360070000000000c600b8040d59000101d007160307440c0841507041260002d080d8407031081e1403445080380c41d24200b0040e80905d241010000d403c0d180441200b2806030041c201c0c0d8150350600504c1e207203602d12144152009010b002080e50300000611803c1039104008a004018506d490b5840b42003940500c4007030705c04a05a021904105128071040c000c2039140041c0030000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 6150115 1250 6148865 6148897
    0x5060403080703080603030903030a0309110603010803040603050615030402040513080c010617030702150304140303010609080d0306050306070c02030102040b0a02060403020d050f0306011b050a080309010b0409120311 95
    0xe2850000056070051408400140c020404541c8a0400005544d03403450020042c40c01d0461403030044006090700e01c000e8901060210300380307070341c0d07200d0600031400307449a007015540d42c9080c040042c0c26190013804d1107000382e4240915039400b440010680e900300e40d04a4000c41c507902c030b105401034084024403015080c2c500c0060f8080010805520103c115000d28805820580800b0802c60311780c01074101c0a500b0045001d002800600010025980329205100a03c5503020707117185280303150026000080490031180c8180708514082010444211a41c90148800381c2828086511844054481c00c14403c01d0a501e804656003901036401403d002c400301a100c1002610081d0b030b0303e0003503c094001d8040c0c0c00c0e4410b81248140111200071100c8840300b480e586425004694007185070a19204690003039035482c0000e07009101e00741d41395010b045038a8480c1040c0d00c005003100d4034258a030f4400d52030900b03e400083d2904428056841d024200060703095005100e0416034410b2241c07000310314032 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 6151365 1250 6150115 6150119
    0x8030f1912110301170609030703030c11010c020105040213050405070501050a050d050a0b09010803070503030c03071b050a031b02031b06090901060804170a080610110d08010302030606010906080a0e07050604 91
    0x402d80030318102c94604d4a8401c0511201650a0300c03088140e504c5400e40c2c1041140c1c2c1c010074020781003500b00b052207140c1420b1000c80e940070582125586042240140d4503803080c80298980b604810710868000031041003642459a1200c1c0d07034400d00c3c0314041c18400301060b2030300d2040c0030381c0550f50810703d000c02c18801c40c82c01c00559001058a0300050348528146000421054400029030f0340442d03015000750b140d031301e82015041c216000145201300308440c032400a12000304643c005e41869200304014030310b00240b80340c05003840e6101c1d5a10034540c82e180c0e03140320140c0e60015003001d030340b003101068160440da100e021800d20f1180601440c1c2001421000242075580844418404d42c040d0800c025211100004095507211b0520128001a0603c000c1901458200307a9101d07408603030306041c0701c402141400e190030102d4410300000450381c40c02c010800e5003014408142e01440c24600041c40d2410702d40c016103042c401070105101c150380d480c20502c00500c02c000040181200a150710b403529 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 6152615 1250 6151365 6151391
    0x120603060e06090d05040e06060405100302030603072c04020d020301020a0206010e0f04030c080307091a09040b040c020a0807050c0301090803070e01030b01090504200a090305060108030f1912 84
    0x502052401c18841c070302c00503012510100d203100e82283c055071158130b040c0c50445c0340c10900390003822442e4451000c000020b41b643d60540c1d90707100c00500b81c40160316841e240041504040c080d03840321003002c0c00061041700c0c08080c002c5801130b0b0040b00c1d4803004a900d95001080708440079000c000d4156200082c0919000c0d00028030314121501d9210600c0030765034602d42090030030801d450040201e03e040c020100045e02c40030140d40c1c03081407441c1030350a0581e610b52000003441040c03440e11040c0380004403207100c0d04250040d100383c00b0301038905001403005560025030700c1e05505000780440001144420030400140043d0391030b400c1c001c0c003d21602200e41084040750380140c0754080890f04002c511081035000b400f4144c0e03041c0f016101e0300d240341d14100902c0003030404101c0b210003029000c600d4403448901c1c0303405072032583d450f0340c2d88a000b1030440c6402440d0403070681207861998014003020a81d03000d030300101c412300040394011746010038a069043e6401800c1400d98540d56013840d01928040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 6153865 1250 6152615 6152621
    0xa0204060e10090204050306160e0d121101060b090118030501020a03050a05060d02090609060102010f05040f020a06050309060105060901030f02030403030b031002040602030d0b0307050303031801050601030b030c090712060306 99
    0x944a1641e038a040c20360f4490320202240f1a17803003080c0c3c25401c0900000c2c406580b078241000500b1039810440041030280300090032202d18040216010724140e981c61214035400085005881840802007040c2e030b04051b00e03000e40d401400300c101c0c1040310201000c1121841d418182c402198080d0081d5110702410030f001d0041e2404032091285207150400055441c50440d901503071071a005008038461341c40b4801031040298000340072a056649a0740c9162441910f442924480c1c0c0c050b84a20040c2107603803041110380c0f07400340d220808118060050180785500810f490307045032400c50780c580d41c070720184005034042d142d04d800c8200214404000c1006254068204002a54045041c1d51009001407043c200300c1c06203004d4440103a20a101c8001d000321140c0c00b01481c03540040842d20802d43d5200001d21b140e0086554080b0b0443d01c1c050840155000d00825030404824201400070102c42c1020966529040752038620903400389000c106030381d0052200c03594400e040310090103059100c0c2090406 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 6155115 1250 6153865 6153871
    0x11406120304051e1504080d051602040f1d03091c030206070507020109090e010515010302040b0409020306060904050106050a08070206040f0b0a0b03100b010207150e09041a040f1407030201200a0204060e 89
    0x118003c2c3d020b420081c1d032150044402080d00000580072b1050a5000d2000030502001400b102c1c5588041c0100c00e100060525804114010011941c40441c03e050220301c01c400040420800d490003140c2c1c00182c1c02144c1d0030350140c21840c1558680d002d41c001240c0307283c190350040010b9842c0039070b00c41e100c02c4c0642145214100005d00c040f009150000114120701c030320300c560811404103000500c2000c1242d001150400c20041c040750600b22044c1c001404c996080e40000007003640060219450b07070304100b550364030031454009403520b4039068440261349500a10b0080c024401d1800041d500c084a07400f0144454010b02102c81c6080b482015000400c0100d1205001d032144400006441c038240c1550342800c3e01035038503544001c40ca030701400003034503000e00704940304103c4448010700200c04c5142548541d0151018007800c40d00ea0a151921805802e14540542c00194083c00980d8000b044c4110400402910860007444129000d040991452000b90b2190600d2b9000541c070000c0c00e00140 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 6156365 1250 6155115 6155129
    0x1608070b16120e030c030607020c0409030e041104030213090507050609010519020303010609140d08091c03050318010b01170a0b030a0605010603060b04030c060507020120011406120304051e1504 85
    0x5245c29200e001c0668844084031030800680c48804038a0042c14250441124a4403a00b40b01d0003c2c2c4100001074152043c100c6110004000820b0410562500e5514014202c80700d034001c00c10361045840ba00e1304d4018038020340340145400940890940d104a084450401000c00d80361414072103464002d403613500a2181c540041c2c0c181d40e010901001c14941d03c03c40d06002003042c10b00703807010758a903d11034020400309640800882550703211451805d02c6004030b07610907501d1075924905418007514031000d80480c03211303aa150138003000f6581d8000890384940140012180103035621183c808018044c010941901401418240d404005140d0042816240a600e0910115489800c03c00d11406035220182c50420401e43c10040d05004000828108c0e0040c5040c0e0800441ca54100ca041e8400e8424100f0030380d903562400d01000c1c0300201150700705900300d840502c507200408204d075481c0280d014180c881c84260481c60189803180250030a02c400141c514911224168102c520b940c1046c49012 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 6157615 1250 6156365 6156373
    0x5120405010b010e0102030c0705120102070c08030a0f0e03060403110304091a040501060206040503041203090e090a06060501020102040b0702090c0c0f060906070e0901031b0902040f081608070b16120e03 89
    0x13913420360000c0300391404001001e00078910309182c5000c01400000c2000344c9042c41d50708000d100b0104602ca0800c4001e41813110041d0307a81c0c904103200601c0381111080c2c1d4030802116032080e0301130341c3d00442c40540064151400003501008414000c1c02d5204941c0000f8009180c03075141a01c00407003854540030154212000c02c40b0303a0b6074001c1a03031117650440740248190402c02c4148a00590303500c4036842c0714003c0c03030a1401581c070341c0403401100506a552022680c084500103040042c0341c02401c01a000a100a5040901e000c51f0b0184600031084000e1054501e400065089404070007900c148405507811100b505091310051616204241c421100d40d020314000140700d90b0065100443c079403000390131200140e00c0c0d610740303001d4a90100c0d80b107070b81d4101800d00012141c482d8009400134048005e00d0603445460070000360700d04203c00c0740ca080610007801c410095204081400800c441e20216140e42c1c071480d100c22001c00d15150385000302440d14590300b001f070007540440d9801c290306023a4222 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 6158865 1250 6157615 6157637
    0x604050c03150a02130e01081f02071707060213030c05043b030706050403030926070204180b010602010608070905040804030809150301030507050913050703020f010e0603040b07030b0d080706050705120405010b01 93
    0x51400d2f40305980c405001c8a1510317041308444582c0781300404000d03015000041c10100c80358922140034015034025030b8420050803050100b403505204049608440c9014000124135070083d01e0450782d0741e018445650303100c4c81070b0344d10140310600840c0c0c182039001c90200850701e002c0c40c0c040c004068030387c41992010f0107030030b840c1c440602103900408141c9142070303020704140036942000b018064140b03824400e1580b2062200c0018585000c45001e81050317000400d01c181030003281c034035051481d84102001e0b804e1100740008115a082118150798020761203503640c172803000201e940c81c1000d00c08c2041a01e000000002800b8003c502a82625411180c0302103d1b1a078602c10844100038510103003079600f003580c0c104014544104582043c40c01030506501c4001c081c80015401c1d00300b21800c0e50000520020081d5407a40b41c0f29404100f80b0490f0801d507042c1c000d440725411f500840d240200441e9a80011610483c00342c0c081d60040354669042c500303a45003c2c50300381e0290004420782e0740800c0c004c107a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 6160115 1250 6158865 6158923
    0x303090b03010f030f02060c0303040f0302190c09020703050f0f120a0203010612090201020c0303070305040302030705030307030804120e060f07030201061a0d0207020f03010606020604050c03150a02130e0108 91
    0x88904880b1802a8103480d10f085171200e030305100e91214100e07408402080348515500041c006180b203203010f5480b84400c07011508000e800d004445c0d55480507405481850000a425106088242d410200006850794400e1030151941d02c01c2c45445c00122402051040100b400a03000b02502c0c1245003200e141600d4100703155060b80000e020320808103079800405900f4402a6020300c06050052045a58450551000c00d04552007140140d00280d8002000e0007581000c0080c1d0005150a90041d0310304035844c0c134001c0003403101a000a214031480c0031449461813152400c02020203005100c00e960f1030594140b40340c96485404100c02550900a0003e9444000e0002020280d0314a10891900410301030181c002d60082004a900900044079100030f03440903c00c84d0060315503034009105134182814001d203401c80c0c200d81140f01354402c6110301403401042c420706800c5068200050384a50303150900d40c4103052181c102c10b072a908020000590050002407201550302c108007140702c040da00c00b0b0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 6161365 1250 6160115 6160117
    0xb0307020f120702190506041202040605090106020d050d090b010b0403050c01030606051c02070b040501090b0c070c05120c030607030203010f050a080309150403050a05010501090b030105090d0f0909150303090b 92
    0x28441d0107208040c41a000541011707428055603580c50400416901d840303000055040d08241c0082e401e000711880e102c030460500344a1200607140450b1030700d4680d80f400710005e40e68a01c0c00e15050401030b0100741c40c40c0702c0400750003401003070741c0c01075001541e5030b1a40c00d02100c5400600c4140c82c02c7c4079041600505500038400e03042030300c08079a41d0f03d1920b801101c54020755848410011a015030030000b00010500c0880c0c186c0c080c510520000c583e003050b0f82088130480c040a0804220f070881004038070005128402d2510403070700b056410250510281e482c850070903081301609d40e094000c0c00100545240c1c168001d42c180ca01c15001d00d010182c8440a004880343c8502500d203059004001f81070862800085122102c0d4102382c05501e001d45aa5074941890704007182120140c1d10303030340180310803c100c0c006c2c1080400305400070440381c40d12081141c2e5070003611484509000365020322101070b600c100c4194000d061620400d10842e01052003c1d2400750b100c0c841a800140351203400318500300604 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 6162615 1250 6161365 6161383
    0x2a0909050601050402030705040806090307110117060f06040302060c0a0b09070501090b09040207120306081504110405060105090d1b1d220f0605060a0e011a0903010603020301060b0307020f 83
    0x380100042da00700002c0c8030082d8000780c10790060044c00c0c080050764440400442d4400c0510f58040e6071166030514045503080c1071034035050305101e50310403440c80c81c501d882e103000e034044001c0316400944004500418550301c11500301035000f041c00140e40c42603170000581e540f0b65a2280b040001c9a40d43c0300103a03500c5090502403c1d000450403a81007240c0c0f299003000e4034803d8001080180341064650302c0070a40c03ea01210007021076101e0208100c031040038000504c542c00c031544030492514042d5110140d02040d20700e61072180359200080b902591050094990000e8040c2c00141e990030f8500703280060340b850350b0320040039034070081e8007040e1810155040a440810480ea244039034035060b07501c0341d8407828801401103002c02c1c280c0c200046107810010080d400d004040004050400000b440000039558101c020303418031440040107005031141a4103180c0d601160443d483d081d481c4002809440541d00c080e61560801c10701041082c6001d00442c01403420b40c0884010380040c0443d01e445075060 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 6163865 1250 6162615 6162623
    0xd111b0601050f0609030f070602070e0702070f03120201060302060d0f06080f06040b0c070602030f0603010506040b10050904020405030106080d1b020108060120010516020111030606041e032a0909 86
    0x240c24603146505103203000e4001920b0050564061f080340c50400c030301c0c0c000e00e9442900160b21902c020490b0050a00d5182e4012480348003a200315800c0192135400c998031803000038118064115500c2e5100d200394444005503030300030591651261a08042c20250044a802045847ca040c0d80090406000240400c241400401802c100d6890383c43e0302e40e00c5400280804151002002805c0000b0103501c02580309400759004440c40b410240c05050031118014101340c0502d18088400324295550364179040001c00030303c0c006946042c05e4000c540039000d07a5101940640c2800c4010404800204070250307a544240d4480c0c10302da043c4000d007440c0c641e0a504c081d0100f54880d0118660754410f61504c50001110040c4543c080c1c07031050a1421507800f2280103000c4034504e0b15144d11182c0c28080c03034001c0501b640d0030341c0c1981015400600580b14522800030188401c10000b02c04d0140f4a08120095800410381e410300c0d0110480324464614074040c10000032010a030200d0700c1c013030620401d410340303800c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 6165115 1250 6163865 6163879
    0xd23040206070309030b07050d05151302090f03030403050a0203010b090f06060a03020705061008060106090303020c0910050a080601050f120d0c11030d0203040906060801080316020103020d111b060105 88
    0x556000e10407079900012041e810450007000c04800302e4401c41003540126141e644160381c441c0303001a10b07801c448015000090f070807140072209a0303943d2103421000190316100d070300582c6c1d51100000501c06950300c0440d150503010125000090100c0800c401c100c5600036402800b60f5680c240c100090030030204c810113144030748400070580c2818400041d03d5051041c1c2801403820505480300362405600f02c508200c03040503003000f4001c0203401e102c1180103080030f00342600e8445c25550083e4403125042a824003585006000444004041c0300202c01000d001d00f034006604d844412564452409001e1140101c4034480c0c1c502ca1810135503441e208401031344019104400003030a040b6240f0384001070036540800400440582a94140f01d10000e10b1103030b40007103559601c1e00d111441900e40c19402401401103180040100030004821200810302c10f85100405848030320040e402401000101917403580380850801807000240c009000b01c10380410350700c01292014001c155107000900031940c100c50 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 6166365 1250 6165115 6165121
    0x30a1104030c0603050603031308010506010e03031303020d0203070302090c040614090d030c02040f0c09030201200606010f030608120414030109050c010e040608010f0b09070905150c0309040c03020d23 88
    0x4404d1740300a42282c001010703245403210600009407455540c1c1c11100440c0d66603c144519581c2014424084e2501a000b550030300c0c0d44500b80745100c902c0d500c40640200010543e0004564060200030007441d40180303054414100341583c40516081405480046840340301411813066618003a40e800400c01052a0000340380766500300d4030702d03402d1041280c01c280c40f50083c4081500314002c0386c01c29507266490702c00e164650300004082c01410340249a2130400440a0102140c021a426a02850a08000364010b6010070308800030100c640c0003aa00f8001c1c00090000b010048006004803a151207980c40c0f01203880b401c040c220f50341d00c0c000808a50100030240090350051150707820181000300000780e02c90b6201513885c2540d0314002c0c603500d040c2d5142e60040c51850005166600a41070389880303030600d410400440e240380c000340380d040b142d1600411034665184c400c2086440002c0042c0c0144003a0802d507502074040c0d08214142c40486042c00c0c82e400b0b0305154482841c0c19103581190148144d1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 6167615 1250 6166365 6166367
    0x90a06030c0c05010f050603100504050709020c030c0102030403090302090606030f070f02030f040e0604060e04050705010503040f0f0308010303030e01020c0c060d0e0303040b060f010e0907030b0f100203030a1104030c06 96
    0x3100c808420700900105482d1a004508280704000d4031108088010680d882c010b805c2500340b84005282007982c42c5031800740404107200288043c00c4d82d080d6207005a4500b4052401c5280d40121a0450420340c00081000109a0310403d114122442945c0c080c1e0f05480d0303070b01044a1404229088000340041200007404030b0301c103111101c207a02880c015246000c0400f07944220341e9000350001c00001d0558028020355061900c1050300500c0d864000da0035508050769500d8a0700640c1c402d0764100b000110115062140e070758400140380343c3c49a02007150008624014000030024442540070070b1401000c001d05c48010b000310340070140c031070340503141d51800da2040002c180c0160b900030040c20f660b5440e2104444040004500490055081c90881d10300803041104d40040d08028604100e00641201c141d0f07150403108680055271800c0105412a0200100d101030700201c038911f41c003c01d07855101d5015a00440218083e9210010a1180c1c00005488042602c120f200041c030103a59128204521 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 6168865 1250 6167615 6167621
    0x804090b09040f061e14011809020901030809010909020301060309050d020c010e0616060c050403060c02120d020c1203070c060506090105010206040b0405150c0901030506040c09050402090d0203151605090a0603 92
    0xc0d00703a281c4105051700c0c10725070481d01081c0711105c120f03401100600c80050504401c0e03104100c1a4028400c0341c507a64041071a015040c400141030000124890a042e13000b44a6403003d0200000115129070b900c0300000c019004580c4203413030f40e001f52028514000d00c00f1440390b01400c0107031161030070600d40406108041c0e0100c1d449100b14202c4415410004800c0c2c041c58204006595843d5202c40c11400c00c00c0c01ca0306a24600b0065501034051200d0102c000010740c0c00b00460160010784644145003a00e040250020300980010b80001c00c0045140e040810343d094075014520802260340c0f1241400300c0e010707085c05418090380c05500001c00244581c103916903c2031180d01a9101300f01d01480000c1c0303c0000b622810b001180100310550656418450164030180c121028041002c13540b4018111100500030075005030b80014074200c8a1716111140400356601500f200c0100c5c20001041c4507503403080d150b016001c0c44584601920a101d902650700301000240b0001095150080640c02 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 6170115 1250 6168865 6168881
    0x180712020607060c030b120303040c0603050601030207060606120b0409050a020909070f0b0405091e010303050c0304030803010906050a050307060203030604150e0f041b030302120c030405060301030804090b09040f06 94
    0x3119404012202c0015007900400c11001410b4030f001c20414a004d0420407104403404000500307a1051042101084107400800c0454045080c0003e0580b038000041b0b01a1280140291006040c2100014503592000316150203601d1660100200c9030031404100c01e58051903005821035001c81141c10140c501072002503040754040c0112010541d0341d84200b41180700d2640000c19043c0082810403c50400c1c3c0100344d07110400b40001245c400141d110307144180300c180009020481e010620f101d2241e010000c0701c001e16044028161a50303550403d0101600450103503d004076541d000010341401c0000c1c0f14400e4547c0d6801945c11562031f441484003c2c528041c03c0700d07100c900d5a80010707809201c000103500030f0301c00e4a1015254645820b000b240005903586100c10012030b4001040800c2d4080780c201021551200003550320a1810611451030040e50805503100c1c0c2c00100010410071440300400031284544024424032031260208a0042c40444029086d02103000305800001c200303602c0140d03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 6171365 1250 6170115 6170119
    0x1207080a09030b010e0406050a020403030c1202030418020301080c0105030f0a020f0702040509100c09120b04050c031903020105011a0409021b0105070e01030501080309010c03080705210f18071202 86
    0x9107999403078a4242d035190082e030110344e2001600d41444107000450180719440248981c055280c20b24558006062115102c0058240b64842c1c031114405882030040f80c004103d14041540a40d4104120b48000c0d4130a102c1c00d175a80c1f1660380405581d500070000d9a02c10b01081c088000141e6903400c1c00c0c1d010354440022103483c0e100400c0782600681d02e5104907401101070800800f10f5a11480d4410100c1e03540040b00402d001c890681005003e0450703000711006640310010780c05984586c60a5032401c0240c01401d94180a020706103500c0714500c06100380c90b43d000358001d2015903a00c051801080454440c2801000020001800200102e40091103940700b4000e20f4080c07518509140c0d400c4420569004d07001500c2c111501c00b0f15a40340c041c05002d0241c81d8046e52074510703510000307409011400c1000341800200340004109038080d5080d2130071504034070360810a080114040c155034007400c490000e40d02c40e6020114442c0ca8594140c61031000c220320003000014100b185201b24404280c004030307 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 6172615 1250 6171365 6171377
    0x50a0905030d0306030605060a0302061c0608060403020d170601050405010f020f120c0706090806040b1b0712030c030c0e120a06060308040602010b10020a0204090228090b01021207080a 81
    0x129501c0401102ca00d0345500d6800041c0746040d85812011b40300e01510b12845101c20300018400341ea01e900032200343c00c0203079001154084e01d1039000e43c0986129406685d9078054081008145500070458128400d03142d52107241d041502a005151500141e4000b4005903040c0000d0000d9400340707240e50049540d500444101c18004810b881c505680703030101264001c8003044400b9010380800c03441c00a00b0709401c2c00b180860030084403d40d940e070001c01c050714034840d400c0846d0500c50750440540d41c40390104141a83c40146082c55201040064100d03c0000c1c504111421041d00c02c0c4200d030031201c0c0341da50710360302c4030b800d0000c1294204019030381000d0b81c081c144141000400038400c0e1780045103e261001e40721441c0c14006401c480e100b50300b15029064030840c06c05e586a020032903050642c0c0c1142c000510600038008525100e11602160001030720303084104510034886031030101141c000030020702c01c440195004a80315410b92101842c0c040041c840c4030f0005142101a16450400345000b13 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 6173865 1250 6172615 6172619
    0x612020c010c020a02100203070b1b0c03030a09050c09060607060905070504020a0c0c0503060723040302100507060b0105160b060402130308130902070206040509071701060e03060a0501060f050a09 86
    0x120703007100c01ca5031001e070140c1c0c040c180b078400310b042030740e41c0da4141341c00390015600740200c540340c501e540340d0020146014003c0d10000790010b41090819114451105400c907500c914007005100002c058020080d2030300c3c41005c5501c41d1034908114601e10034000030740003504015032136607110040c1c41d104c02c0c200e41502030300707001095903102c0744050038400b046503403403280ca406141061503c1051079003003140260491070070072040319008202e0004014000c124080f40c948503026920305401a504002d42c081d5082c4511111298800c026148103030080d0b03010402c51000034015106407003075811882904044070f005801141a002d000c9510007400307080589030081502e02001301c0205600112000c81000c9601144941003010b050080d00d6042c800b10325051141d0005110f0b17010301d218540c4917040c6440011107044c441c92032021200700307000b1110b42d02d5031a1540500344010540ba00ca000340318000014004400720700640d0704864154070350001e10046068115460303400380940300140300c510400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 6175115 1250 6173865 6173887
    0xd090302010605031b011103030f012303070f0e07020105010806060d030c05031b06100803040b0708070c0305010b0414061008070504030b07020c130c02060601030b04092103051609061202 82
    0x117403901c85900e214a21001c96403c0b00054100403181100312015030042c02023001c8400b52281c1d090641e1305003e80e001c8076003041421380103003148849119405000c1e03100d002031440d0808149005481f40c0e813003002160b948034a4100d0803680244560601540184040341c00c50405414111039240203240c030480400841d203a007844c6d50720074140c400b80040301a1841c00203400602c800740e0002101801001c1c41031412049942d24040da0080c0c406c4120700007a90300c20009614111112154440404089141e40e0708140d402000303008003860140e800c00b00207214071141c0c100c01900c1844001c101c05040c141d0290110f908000c0285000c05102003004044007050103400385134403a48859004100c2c242c660802e01081c01d0260401c1c00c82d090078080c08180664020500170360019082c03800080f44542c0390000360151050007809815910200c0d940c81c3c3d9640300d40c0e47c0000c2c5010540b82441b035038803000c005d400305480131498800040d800d803406000d25842088214100481000098101420010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 6176365 1250 6175115 6175123
    0x903030f1801020f1b01030507030e1b190302010801030b07030204030b0f09070b03040503190909060902030901050c070c120318060807021606020706030504050708070305100501080304030201050d09030201060503 93
    0x4440c00c4018050700003892076690411210520b14813982c0a080c9041d107071307480003111515800702e1505040e11000000c0d40c19109502060616400b201156000350080d081c030480800441403040c00b506101002e00c525801161801e0100c0c0d41c180c0d1462056031841c0c650708500d400c0604444201a020880000819550820140680e04403810b0b01c0c3c441c100740d031000d46420f100e0b40c0440c001c2c040900810010401c08001c2d031f0305246001102500d82807d0200c11914414150000ca01c0f0034901000801c610a980c0c0c082c500c03030200c84008001e80d84990001e00d0040c004ca400041401250a60030700a0300c3c222404102c220b4402d0a085000403440407403040450070b107402210004207484208035203680c0c100a01031418000c0a0501c44a5041c00c03002525034900e40624801c1c1038541021038200315040040c0702c0240315640a49641503120304d010340e103030408000a00d01d124204000842e4024001c0200c0707045a5050f141d451038a1000d0700c0720f8014190100003036054ad583c49000050742c0c0c80601c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 6177615 1250 6176365 6176377
    0x10e0304060909060509040f02090a060b04080304031a13020d0f0204060905070305161b020d06020408010b0306070518040b0105070203010912030c0203030108060c0f0d020d02030126120903030f 85
    0x10b141c0300030300ca0a10070288100d5890b07511082c81030940c00140401b05180090140e01d440e0150380400702070b5241c9211102070040c1c1c1d4031450b055000050002000c40c00400900300b5240b1480e6240c00001c100002090101c406070360340064039079039445c02001441d1900f0030b003108521a1942c3d00070102e5540001d821100c49922108a40ea140e5013007015082e4103114965000b010700e524140c14114080c4d0081009401c18a04101541c0f441c0d520740556541500090009a000b8400e43d5516111054a4003901541030031500903c00c0302d011600321402102560305101981c07510000d80c0600c5e0741000082c0c1088404da83c1802410032202d00503807001e000740d41c0c1c11400b501424200101900000301143d600c0310180045400c1400103012040002c515141c00459070200345480d003d91201280c528407458510520440c4000340c245c41403146a00a54102d07100880c94541c8020f031204c080b00441b103d001591500e4010204014540050501400f501c18000c0c003102d0170080b1250034112158050 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 6178865 1250 6177615 6177617
    0x11061003030824060c01020903010e0a02040606050f032205010f050411010302040b0702090402040e030c010b030607030e0c12030d022101050301020a05040e04020102012703110c10030905010e030406 87
    0x420010310505421402280c3c0220360000503500c0c0c95200802160700c8401030208074426080002e852034110000d406403805028020000c002e15070704510aa50b554850b031700e04902417818047c00041e2240602c1c142e03500d80700176400301c919540e142c0c2000302c84410310500400003d007444003000d0206809200300601006801000260f0707086c1414410300032503441c04540d040500410040c0500300e099401c1d40c0c01c403581540c101d2026240da02c00103000d881092403000c5240f002044500c1c80b00c0054018501c0074000358282c811a4450030001c0f0161550701ca2406029403111804010500745802c0103255070301c03220280c2e401c00d1140d400c2001a0380c402c521105844200405102c01e06024900b16401054210002c5103013071001d8501403c1401079115a07503000d124640042c0c01d59000390004004020f10320841d8403908601b2100241581a00000740c0c001848954002000c090006030408068401003101c0881d00001c1c0045001e00000e05045a065494210303d9400c0002000500040d10036 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 6180115 1250 6178865 6178891
    0xb0705010222050105040506030604060e131401140f04020a0302040c0203040801110c0d0f09050307060908060a050702071710020301060203070215030403050403060914070602010e0f011406060a1106 87
    0x66204180020001848180c0b806032032210204126a0440121400c950058030755644956941780010010142130340640c1c0f1001e00b203010010811081c9140102041c031a02c0603d050030103100c1c0d480d013280c06245d61902040e0384000072401d0600e1024219a00c10320061452407441d40300d1b80400c0c141c0b81c000c00701c01302590010806009406080c01217040750702041d40e406042c2a0f4141807a9512141c14095500348402e40d103001c40b0141c407505403000a000060112032941d6030710034000b041c41006128901e030b0307400340da408540c0403240750081e07a0140c1803680c0280b003800c0c00c1c01c200000b00c031180c90b011040792180542c0482c480c000c0d400a54020103150f0043e54855256006124181c6110398120f501c0c0c40c030400810002903040010745007540d4010030000340ea403130300c0c1c80d000c0844030345202c01c100c95101385240011b07079a034150000f01c000840b4200380ca1032020083e1500d8240c03155032405400b1582c81100054850030024060440c0402c1890705111020791210014200001940c00031036001c0d03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 6181365 1250 6180115 6180127
    0x905100e01061a0307030203060a0312090905070c0c0b0c0309040501120c050603100b0307110a0b0703150506030103021003060510080103030305072a080405130501050f03060609040f0203070b07050102 88
    0x542807140e400100f0300000c02c40c0407040388000c41185440010049001e1607400320200d412606d230415840041c56024415103580c42003503801400b900d040b44101c4030b00e242040c002502c6680300381c00041115500034003030b880050400c10322075200c0d04204050016488140444080c1d942c0310300455000b8480b005000b601d80051f03040c564000b10321508250f015010400501c5005040c1c01d00c010112604201c9080e10798070350003402c455580d1211245c41d09445100c041c01d050000e441011402500b0319242040842000752079204004424424168000e40a000400260500301040282401140740000b1202d485200141c800c01c81044500000f454181c0140101a0980708080e0403824501b44441c11b0301364640310849808607100200c44403003000b903000007041400400d440240000600c030802c1164503c220a008100034400c2c06d01c203a2030072000e4401c506000c14864080c00d4090130800c05a91183c8454040a03e2420100d0300340c40342d95000180d400c043c001a15150744610000f585e110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 6182615 1250 6181365 6181391
    0x3230301081908040603180c170606010e060a03020f090301020304080315010806090c07050106080304170c0a0303020601031410050a0c11071415040503070306060503151b0d090510 79
    0xd028a5011821040d54010b038004580f900c02950f045500c5d52a01103035036284003940700000c00784060018500725481304049007402841c0050114440c102d011101903940352401103d40e19260760042e6000300c020010000344603c25001807242c2090304403a14680b0346400f0200342264001c84043e80c2d40f010100605c8803070741c441000705c0d885050919190400782090302c000341c40001c000d000820100000525042040405c4d00880014030090060b25202d5681e03200302e10b80002c1003001e0980f82e0007a241100c006242c00751806042c0c0350550f0007408076030f0031a80d81003c1c041c4900710381c10f481c4c41042d1512110ad4014012140f05055003d8045007105500002400034100c1405403122508485002d00508543c09090211044120340380341141c04003880060840c8a940c2113241c01d401000310220500072240c01007001c4400035001c0355401900690419a5500c007620ba503081d14054a2281c00c079066032402421b03e00d10044000110320710565642c42ca0f01c43d0519203100c00070740324140c6c80d00c05 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 6183865 1250 6182615 6182623
    0x90b0118060c0209070905031f180506100807030c05040506150d020909010905040b0a05060117100e0c1c020f0c060709050a0603020702060319060f0305160b040308160323030108 78
    0x400c0d202e080411b006030509000075120034a00407100201d4240b400400304200c8160800d10645000b044071856072074450500a8891108a40c000d4145400400006404000184840480f500031150000c0da43c103290401c005400040c1c0300d19131105010b00076040d1424070f50001c0107003584041c0300580e0348131200d0500214840503841710003183e20b0202040701055661016651100100c440080d041d6105001a6043c0424580c0d81148400480400c052580c04076042415904960b200001684d92840d4595507446401d4809106201d42507088400001d25009032408482901c1003d0800d0700050229181c61822075a010015507540420041d0381003018454000e4403880c50103600d840201e4001c10502d10014161050b00a48207500742c00340c201962003100034040c0c2c01358900da243d40e81c0c100b80351f5403404c0c0c0a03004501021540b002441da10312000b100c040340d030300500407402c010b0f04800190003d41b01e05015401d0110b00340c840c00b54250340031101d005000d12518856181d50510010600d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 6185115 1250 6183865 6183871
    0x2010608060c041203080a1b020c03010b120a03110106150818030301050105040302010c02041506051308060403080c0705160b040f080303010b040509070201060b070303050105040c0f09090b0118060c0209 89
    0x2104000f00400c2c0034030031103d0550300c0182d425041c44501600c2d060b04041c0145084074407068000c92000c1e0310400703954007260300040071000318000c0c003a00d0907203010000e203045c40e0600070b0490b5000010900000340603400402d4403840c0c0f0400040e06e156648080305500c80d04641d4400040d06060420504003c0024030014900c215401036045604000010740244580c3c00040d0502131112041ea0444d56560815045064091408003015a40da84060301e41d401848070030440d580c940e81c0104d000140041c1c02c912554060b44c031b4010948503619400d209601034502a1040d004110f0760a2104600c199040020414108030315035407450400480c07031301c1109400890a5420801c0100012002c58094030281c035000c4403100c84a4031480800c0e40103000399403015503034143c0407580100f410317050f9101d00e048038070580d014814041048002c80b2040511030a28000c19800802032000d0901c1c0e502000510074181004241c2650300039000d04208000d078840c0000440740b654800442c240f0070051a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 6186365 1250 6185115 6185131
    0x30f03060303230403020d080a110102030907120f0204060b091816030c02030d091a010e040203060c0d0908030c040303030b0102030c0a030c06060506130501021902030a06051b0301060201060806 85
    0x128103401c40d603008004041e00400000d40303081c011110080c14809104441c01154010905a080d008500e000da102e50400329080c400300b0844d52109000c40300c18000c0f04c0c8680e8142c806020035a04100310803c01c80b0044074180d03050300004410100584440c454440942000311400e0389803010481046025410740c5c01002c07102c103800091041c80340400c03030106001d030041e040c0804c45281148040703245000340c4000c044c40034100a00b42e03060080903d131020044c00c1c0c030b082c400103e0382ca84200c0d800d40c5c2000e440080d0140c0c055000a0402000080500f07086c807031044c2c021800c60b0b6030f0340f6840644d4005803010440391400240410405800d03110303a41c0303800401c1c0041d40c04c120a03803066a4032000307606005001c1c4071081300c61074104801540058050040201043d07200d106821451203040c5141c05030901600c280c8990000c003564628070b400c003003503004000b00b0550040c0d51710782018050103003c495102c51048020313858649214060341c003901441c1d000041103450980d0040c0303451b4014040c10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 6187615 1250 6186365 6186371
    0x9010b01020d0c0b06061201060507020102010c110d0c050304050406061205060406050d081e04060e010906020c06040315020f0307020a06050f0106091401020c0301020d0b01030f1a010c03020f0118030f03 89
    0x90600e4018100d00820368210004c03480341d0380da5a022558522a41070750304040346241e0000304107260000080c129160007a40200302c00d00c203001d000d940401c1c1c04007003c0820341c0300300c046d000715a1141901d0701c0b0b16440364003501c0c2466500c1c00420b0680380a604402c0110f42c0d5400d120403c1080c6200b6a13a02100446040c08400d00d4140801d8aa2480b03400103410389c1d03400100f2515050b01400c0034450201c03a200700964035503131210001c1c1261500c1c0f1003203000410203100002d40311f1001842d031020010041c04649080c0c5582d6a030040180c2c0840c01d241059000e1004a501c11100d20181d880740d80300707402419550b03104c0e113810411180c00800c1c150300e01042d040140700c407942c400300f0305041d506050102150f20070050010303490700c0c000b001240d906600018445000d40078540042d420024207132428400c00720241107410a030f800745d180c03078130180c404801e0b2005c0f190b02c01c4058940c518040d0041d219a8442007010900b0342d0f10310340e00c440e840b007640090740c000c05034014422070102505242c10 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 6188865 1250 6187615 6187633
    0x120303040c0302090c0405090115110111030c0a170a050f07210203040f02090c0a020f0705030d08061c050a0b06010c0209010e090321010801060506130e0703020405061209010b0102 79
    0x100d603200c05501029004003d081c00045c00d843ca64000c450103010000c2c407450741583d440004501003400f40e8202c00c0095071191b241d20103036070140600c2e1001d40a649005003075030740d49810740035030b500b0071402e00b010820000e1031014640c440103000d6009104a40b801305152401300000f1802d00b078007030802c00400c920008003003100800e8180c4000d20032020b40004d6030326119828000c40d220860800a544058203000303118446142c100241101c55840c3c00350344519041c4400141c950441c2c1c4602501608100c400c0d49075244100242c95216100030495402e640e03542e121291914000001203c0641c40741505005000c050040107902c03040034038200f03501d49601d501203540c800c1c0600c50000c035030510f5404103000750014410b84040901104004334061444005213814910030711a0f90710a501e41000420181420011650200c0c81c502c15008141e00d452110269502c00901090401d03909000204495640c000106418240c011395030b40c0c14107001c441213086030207a00385241954425012 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 6190115 1250 6188865 6188873
    0x1e06090803030702070e04020409050d020a03020105160206161b05010b150403080d0905030c030708040306050105060301030b1801060f0e04061515030207020301020702040e0a03020c010207030305120402010c05011a12030304 98
    0x1200080d148050f05906c8a5195440030070007030890721000070420b006103290615503650000711400c113580a58001c1c01551030742b41032099400d00301c2400c0001031b0007040024001a0b0710401c9192094034a1500103010380c0e12421060150300280c00843c2c1e03694695031126010710380301034001c103500580c1100b01c0c074107891036445001c241300d82a00e650010f61a80164000d0041c14811b559040d00c0e1034003a01c1e907654044c0340841c095803190004039110340ca8000085032905054003981d068030b0744440280c031700e911410402c2c40381464080314124a0764032244040341c0a0194002d0314000c03d14241500c01900381440c4c02e4055a03845c41185500c80c80009040100b5501039801d6141c002d0303242001a0380300c00703a00200340644210b00000c0d4105040030040c48880d400001c00d042114002e900b078400802062004984038105071001034000380040c81510998a0040c0449402c580b05050166081003195212400d541080c00c550010307100b088030458907810300c640c202450f529544055480d600e420360b6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 6191365 1250 6190115 6190123
    0x9100b0904140c04060b070b0a021603051b07091a040902030c01140d0603050307020a080109080a0f12050c031009290109090501080616080403090302090903041e06090803030702 78
    0x291802e05900d80d81d4040c203600b4845403092841c098424441103803034103030401455114460859295a1540000d507020000748250341000300880c86445001c0b8081d20b044503940c0192106158005001507004090701c42000420010541c030000400c810000d20008440c0c0d02c0000d1001e0b02581c10201001e0040c3e0740841c59408100090a05d07841c80c1d02c480c0820b400300c0c00391b00110161a4501a000b20600034008045e1111364801c6034507500541e111a00b039401d0b6001080000c01d4024203000000c51640a900d07011400b8038107103003c41c184d4016084400030345005440b645914503002061103182400d180c0c0c25009080041414001c2d202c0c080c0c80300e400115201e1002c2030000d02c10000c641d0aa2003800e48600400e0301c4481030000f561910142901c0310b0040c0c4410062058500610400a01542c59244240d03095180c200000b891902400312000000308140010b0104000118640d40009200c41200704104c40c00b02c040c50138000040c11088090308403190a41c0306000b0490420782c006 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 6192615 1250 6191365 6191371
    0x1505040509070e09010608160f03020f010e06030709050a05030c090c0c010905030712030c08042004021603180602060405120a020102090409030302090f09070207060e130501030b09100b09 82
    0x1950008881d90365030790090612240d40c00c244030448600050040f141300540106050307840a1081c1c40c0003400c9110516080203040c811040c018021010400140c81c164040d201a6801810301680800003400003607200e6004603000c4c40410348002081c23100e4280559030074080d00080c0c4c001c110080445000407c8090000c21620903401300040301d0410320300a4000307800040c1c2c00340c2125120100ca191800341020401c04000000b03240c165906601841031405900480d0000d0f00c076041c020038002d80b210070103004040c85800507001c01164040d4070841100400c0c05000f035807183d00a02c01c040041154a0080d4800002c40d0300c80380603c000b00701c01003802c0d500409440822984c032264900240d02a0080b0020968807a180c040d03084181500340d0001d01c02e90078104c8400031286003e504100d60840c058a8000c0141c3c400002402aa4010009100b102d440140118005000841d4660070356209030811a600220f01050210315502001201001c461521f02840070f6409a401711305078040003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 6193865 1250 6192615 6192619
    0xf110d0504050a020307030302061b03070507020105030a0b13091712010e070e09070305060f0102011a0d0f020406060c02030f0a03020604080703030f050c1308060108100b0a0f150f031505 82
    0x35004182040340030480605426400303802e070384c01140d072170074040c2d01d59030102c40c041881c140d40155008003940c1042181e00c107940c55154142021070503001112590001059105040da83d60005400c41d40c5118400c03071507892807000410800a28070b0880603a980c1c0c000e145000c02e006001140700400c22a25150542e61003a4441803269101507003114110320342440d00b900100084244001c041d032507000a403040005441c07110240f121100120700300c0c0d00c640c852044103004148042d900f89010100074070341c40d00540488050f44403d400050490300f4507813029001c0f4403400c401208609007030090003240c6020501500302c0d003030f058070003070f448140c0240010302d56000040e403a0304160195014412901901d1070400051038410300340d9100b50b200031414101c041801c6c40000c0c00700d5000031000d0507640b00101600c200e0400340754002c0680b80c40d0740300d02e0f0b02030303110040411850090054000140561482280f504000c00c0e03024001c000f8012805c2c0401d8100580e10f00e80c90ba801500804803042 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 6195115 1250 6193865 6193871
    0x40b01030f0203031209010501050108060306060a0603050a0605030102040801020406021e0a0b131506050906030304030c050d020609120a030e06090d02100315030b010302090106080601020703140106030213020705010f110d 97
    0x709100003804c5114000c824204800c56100f401207000341544524183d80080e00c4118181c0c44a204056891208580349035100041040c203010f4a4400d070041a0000001031003c40c2c210340343d500003030aa80082d045040240e50100e000c0000c9a41041400d00c0ba0003044c4460b8030788140751650b9030b182d00040c5c078003811a902c0f00c0d01081d400380041112608964005c0e503802800a203810201028169501c1018891104e01000c00c0b000c2c039011007100e04507070f400100d000340c0ea441c080a2200030240d41a09a90140702400b91312000c1c1c48840c50781035001600700241c41181c007035140107018488150410b600410062100c2001c5e070700c1c1e0302421b4400c182c046521522400f2000c0044014195219545290b00e8031070500108000b0a420240e059900c01c44c2c0070401380c0e895000482d4007a00c1240c5040c01603104401c20000300341c6001c40003106010100010801039100d4001c1003a4140d0800b807280c8207940096008207004003842004002e20369100c00340911114207211040b1030241843c0c3e542d03603076a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 6196365 1250 6195115 6195143
    0x60302090312030c0307020d0219020d02030f0307030801060f0302040506030a180606080a050c030309090103080703030908120a0b010815060d021201090b0901091806020714010f23040b0103 83
    0x36081000194540b000408150740b49044044610140c10a44a130800341c402c08060075000c40c0045040d4460598040c13040d14404656000c2003048151001d05a0b0940a030440704281d0f0101407006144031400f075103030001c59515202d00141400c1000b5141404c140c03050005100998610044a810504002d000704611000184103089044940d0000b40011301e0840c0c00030f214840407800c0080c0764003036419600d003e17621009150710392103540c83c1240d11000c0301c001400001c0e00c2c0c501901501c2d0180c030340000c0c01803046d03851020a0380061020305c484040d10040140c0c9401c14096044a00c41c20300e4181c03c0e030705224041b4102611251380c203d01c078040201d20089504a140d050712480380c110001c0b5450fa581d50800000200400c100c40c070700410041c00081035000b0380303005107070742d1520b50f8501c0d00d410841ea45800f0300a400a9008031500c900e00540c10150702c209000d50781108a400c400003850041d030004030308184500144c51101c080c0b014003040045045034604074110707038014240d02c100310 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 6197615 1250 6196365 6196369
    0x10902030c09121c05070c060818010e01060e01080d02060606090112050408070c05060309030f03060409060903020c040c0e01020309100203040803030103030903110d12120b06040803070b010f08030406030209 91
    0x20165200c52030304440b182d20783d000300369000122401d848100224581880c0015130b01125648540d00015240314064103041040e60302c01c0700080d1740900100141c07551182111003a0382542d1401e40b46514981d101d007024815401a0703c0c1c01801449140000c1102c081100740c0a0b44a62005085611070000071a40803142e074021080407046a80180041000c3d260915200e983c40d08905016a0546909800403900342819000c0301c0c02403020b00c000b9030400310403555149841c0e000616240d0400c1d290805000021064024151168806c0c0c004e4802156000309100071200051041420008100d4241103140d8001c421504200d03019174500060180390a01030340b940c800ca07841402c8501c0004000000e040d8025028000c1d40d22a00415808901307150800281065038100070b0245214120280d0280740280c92040e820040c00e403022600c443d05400040403600541d101110541000510b0750401000090440c003410000703280c031484a0608421a55074004c9004030701c00e155001824007213036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 6198865 1250 6197615 6197617
    0x305060f0409050304080d050a0207030803040201030906050a050403080603010b10110304031a07090905010303050405040b0a080106080309010806040606170408090a12020405070309020105030613020706050a090b070e0108010902030c 102
    0x501006001807011001a1820f65542d610612075a01140108102c4528181c406c0d030072078540107510b40c01000c0c0c0b0b906540b18000940c2c4007401c100d052550b508560720000e0042c0c024544662180d61000466141505002e0441c98008107100d10991408420401d1603603140703114108408a45806490a0145910b41c4e18521441c0c0014201e000c503501984903403c000106244a001031750b550344040e13995912420b09035170b000e01000b408903105010610060030a5880301402c4079006290b41d403899aa9401d903821511a03030040045d40e00001240603c5507008541a5081802541c04000c1241781140040065000360030303100b507000d031b11404601809003a406032041c0500007072800c040150764400b040a01c110119040b0f014609190005503110b001e841921607198060b110585075940344010080307100c0621048002540c1d00307010060100d07646101e030034440e02043c000040d61004074203190182e000014200c0c000c10801f00188515664060303610b40c1110060400541c903170320703507210702829 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 6200115 1250 6198865 6198889
    0xe070509040f020d050402100c08030c0f1201060207060e06040b0304060b010908010e0c010306090b0a0302010f030608070909020a0509090d030203130515010905090f0a1103120706020703092301030506 88
    0x1141d0300100340074111410a174480744c0614422100303440000800c460550320303d064040003402016013803000038080048a802040350740c60300c4641d2403801d4075842c0f0032181300e034080c2c01031310049e817040000f031120075004642080421070840d1030700e0809103043c0c000c0307255202c02400106100d485e40007943c040d034004c5200740050700f1007030001e00020840443c85030b0b46014004030580042d00f00000014800064401d100d5a018040c00403005c00d810740c0c006480301001b01114904159443c031000401a00502030440901403040004c6200c50701070041000030104c6400c0746204843c514180700c00a440080e4848981c51a814056100c4d580c5d02000d500103002940064060f0280b001d500e12150704812082d13050b05d44181d800c104907140c0c151260340e117550140c40e6607003a41c40380d802400802c3d81d23800300540000f030007003c030b868442031010b00204075001210100c41c0242c01040d100101a0015504400b9000b110480031400d103e000da8020f03260300340c000d481d05040d41c51020409503150300504030341c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 6201365 1250 6200115 6200141
    0x1302070803070c0b0601030b0d020d05030d06140312030106020318040f0608010e010e011b080a0b0429030d0504030b0703060510021608160e09010204030501060303080402040b010305010e07050904 86
    0x24407881c100304050019810080c00f01c40004c509000148070358040d1203080e00b80c0c0070160007001e0340006a400d06c001c0c40281c100507501848184400310420b1400c1c010301c405000342400c4928803050030820300d45800e20317203004007184010510060100913170000959810744400c03090420200085070200e001400c006640342c944a08100c00030034610015001a00540c20100082041051b09176495088440c0c1c4507000720340c0c51042d0043c0760802d109d00c0c03181d600003844400009c0d0150102d0005800c40700b4603000501c0410412454142c403042c402c10b0034200810640260221340440034004049201c0d40c04010720060a42d40801c20780ca22a0344034001801c0041d000c0106d5040005c006540d0701c2d22121842c001e003c06d4800800d82d00c8011840c07003101c40d40350b688120741d00d080c694401d6a00c1c00c010540102036509000010102d442406041c0003980a61141c2c04c0d5403c050052109640580100c41d0505007050010490b100c07218801c241d20510500d00a80c4800d0380d00c1c001005001c011002c00 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 6202615 1250 6201365 6201367
    0x40807030606030308130210030b0301020909010303020a03091d0406090302031e090f040207080a030207050a0f080d0606050703020703060e03090915040b0904110103150e0a0608010b01020106030b010513020708 92
    0x8001c1004503488141070300d000c1d45542a5940c4c03505242003288040d00702c0250490310350000105428000d8002c0c801c40ca500a002604127407011000c03d004c0d02d0240d00c1940181d1180c3c1d2b0110606400c0802d050180040c04003800c0885c02110801402140150009102c1541c400100041c940b092041da6040c107070500090711081c40303004004245400030706902d0f101765007102507040c00c2d02e07181c400c64162991013178429040a90404040c2c0080d041310100b80e07954050004420000346c00380080e02029441215803c0d203500c05e040285003198150703042581440020091480030a400080034412250312140100e0440d18543c00300b82507014504002c1e801c00040010b21243d0440f03005000070407034090b10304100142e0160b00704102c01600383e402400701d1b52083c1c40d01d840c2e94800c2e000344005c0340000b031006c056559110401c8142c075004031040120156660002e11601c0020b0042126808091000340150740c110344071041d5880040c840c05204100c400c0d418640540643c05a50040e80c1001c001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 6203865 1250 6202615 6202619
    0x61005070803090706030608010605030c041104030f0b0a060f03050a0f060b03070f090c05030105011707020312070206091e1b0f060a020a050106062105070c0803070908060108010203040b0606030a02040807 90
    0x4966030401360158001017820702c200842c1d200d02c14400c034003c60f0002801084004040d00a102c02807072205c5021140e044108404004511415000d4448074420f04130b40c240da20f082d6444400b01c0750b09401901140300003002c108003141002038078040301c940290b03000d10348100502e00840102501c414203601800350420000305002050b0410b411103036030f054188154016404100c0b820701c400d005281c0460b140100c52082440030b051410b5000610740102c80c82c0912545100e010004100c0c2c0500040e8004410041462818031141018400c80078500c0b00c0d100d804202c00752104a501403807900f550b9000280e020f00da8841107152200f080c090300c510340e5900911b034020345a446600003928103600340b120005840c1d10a901526a40f40424020000e00100071380040141901070138034020045001c0400020406000003140282e10302c1e1100140300f4603180c1140e041407016845100aa48103204010115040003000da90144080300d8003952641e403940540020b001e03a4112260f40c0c40340c2000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 6205115 1250 6203865 6203881
    0x1006080304060306170604030f0203070609060506130b011d0a0b03010801090b1008120708070b1006030c08040206030402010c0f05010507030b01270b030a060305030d0614011106061005070803 84
    0x42003500e04030f0f0303824000319882c0c0380300c1038203a481c16000715015070040380001c0210740b28107800c520903504c52043d2860841c103522181c0030748070a4641039501c80d50341d00520195181040e414040601c9954050003ca040b2500203480080341195807024001c80010209603503070b9805e01c000140c81d03800c40302d0307880307584444042c0d0003481403980c12034071213010354082002181c0201c03c1d1421a200301000f090554000540212f0395002481c04589603a001e10410307001408000c141441218030180d030b01d1009150400042c2991007109416090081180900015840745030403a07600540a003090303003c0d10100e01c1c2c40c00600817609806810b9510305818400c00645c5604030001956099031140c410030503100b0544c15203001104000d82c0200c3d025001c1005105220103107034848620100062940c0d500d4480c54110380c004550408100e52364803051003200700b001442c09043c4400c0c81d1044c042641035a102d55606809800e051083e182c6400300d48a0610450803500e40d194010103c036200d080000b5 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 6206365 1250 6205115 6205117
    0xa0506070806011407080f0f03070c1101030b06040911190c03031406090f060102030c030c031201140901031707020a060206040201080a020c070501081509010b0301030b0603010908180310060803 85
    0x581100011004400b2402c50362003040410a80100c00c0e042030f117000748a540d0003103039912040c03524031001d80601081c520001f001010354072034603c41e11414801c041502e0104403910b1414141818145000742c104000e03281c1005030b0341900e043c190b0000328152284003d0341e40c3d01506403a007129032500f48075015000c1d408069258075510a80f0103001c5113100545070380303510303c0440e18503420500440c0014500000d50302c6035a08200e060040d28644215100c0190840d449082030a89a40c0005013582640c00140d01c918011300d480395182c0b04140700d490000322480810710001d031400d41c201c903402c09d040e407a05040704d805542c020102d60070103a40e50070181d16201c040710141d010402000002d504000a4001c80b48184090b40161082d94280401503a040d500604028001110511005000c0d12806940348c080d051035007500f0788962551801410b45a001044180240d050580c0880001c0502c425900d94108800c0715200310b11010010a2030040c0d03241403008a0360410500040180d4040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 6207615 1250 6206365 6206371
    0x801150801060605041a0d091704080709022107020705090f01050108090a0201020706031d0106060206010807080c03030403110f0310020306100509090414250906090b01021506060403050a0506 84
    0x300240441951010b00740c50320300440c4120718206003c91004005103401c40c1c003c1000f080e5071000024546a03940b81d002c207401c00301070400d20070390380094148804081008000000c0001c641c06515100c501307a08441c0c0354071119408108400548040340c1d403107000b8070807030014042c054407a40181c6000c0d0b0041300000e04c03e10406010410b0b281c046030f000c40011032044541038040c0c0080048500c0e2007003c40040015040c3d40e550a884c0520842080700d080c054080108600e41c010102ea50520f45004d04002245c3e1101c401540b000d0641c4481e07460200c180d41c100d0b074000000d00107110100e070214000c3c1d85071885140e45406030300e50b0680c3e600c03015405140504403d40d003903030f894840203000343e0b020f1181c04480395000d144080040d0001c1c009403c800501d6000c0002d40300600b025081c15845600044240458403004071814882e244807482940020100c5c607105210a40f08400040d4842411070050b0f40a070402c0b0000032104d13101c1c0421140150381c400b04071401d10300c45091079030b211081a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 6208865 1250 6207615 6207629
    0x5010803041e121a0f060109030b060d06020c010e010509030403030206040b0703020c150708070c08040b0307030209031605030c010504141003060503030a170c030106020d08130c031104060807140613080115 90
    0x400843c840c5101104211300c1b480060312031202d032074110349400341c400000420807a40b0083c94104200003c00074005403174201008400403c8401034400d00c8c5081d520000d0501d80c0d940d10511080004c01d0740012000e8020741c1050407002c1d207032114142100030b4890810405403d110700080407074110106c800340c0740708003240e59a014040d2140401160300d004040c10141001d4028482880640c00d950015900702ca0a0b0400602d4907001c20042414094038208007809403ca0b20010086400e041c421848540b8017440c2c4680382c00d040c4003042c0882c1101c0c400e1a4003808841a511480c58040c0c2d010101600004003240c0c2c541100325001006152084000394102c4800c42c04a03545410000c2901d05841c602e0b0040e00711400c104004850600e00280700c02170f0360105038984004a042100e1000203140103124100c0c50a031000c0500c000c3c2c0381c6560221840394001c0300300b0000d8070800c1007001c0802504554490350380c0b0745010a2402413940d43c01c610504d51074151881d000c2030304032050804840e00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 6210115 1250 6208865 6208913
    0xf03090106031221020f0403060f0b09040c030501050106020d0f030c020c031605011206030807020d03030b090403050304050f060603060105060c010e0105100501090f050d06050402031c030b01110105010803041e12 93
    0x113410030000607030150445501c071016043c401400001e1940c3c010724800c00c8000390004644840d00c00040940005550035102000801c0341442440401e000e018051310f4240010441c8002190005000c2c00d480c80ca410100365444508501180c400d000244010000904841416000d0454085c0000c160b1081c103010a2000d41ca003078800c001e41c046c0e6011240c22040c0b079810f1500720380a001000104402c00c4042696079003110310240c0e01d108001d4055406a61200d40f40c0c9000d260291402003c4030280065a0102c820403000e130b40c00003903050558105840e0f10381c4402d00b441e01907014000c031030007500301542071000b004242098000030000710b5200f66100c1c1d4011b0395a810140d6003070302600176070b9003141e0108400004102560001500b051002d401ca03051111041c04044080110910f4030001a44680c810b4040e0740c2d01c4424006c132030300410020050b5515000c0e00c19900d2055100d40c0c140304084e5a0180740c01700326910350034024855001a100902403500d08003003810030040c1c40e0030309405 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 6211365 1250 6210115 6210167
    0xc030c0f090e0c03060a090207120e220f02090303040e04020f0d0809010c0804050402130e01090606050301090e030705070b0409061401080703090507050409030c11060306060f030901060312 83
    0x882400c0d01400ca0300e04a5558802d5110300e00e14074080c3d40b00500003508018114000a4200c07802c0c4002c114260243c0d54244003000191401400c00e480030304082c2c82080400511101e0b040d000a48440c050b0ba004000505001c646002d00b010380139807500180e050002150010320b10104420f10741c450b9100711032a203102043c403010486c0301075140c1006000403c05108015465008202c1a0701042c011180700741400e41d1000050183d91180000c1c126010714410304214024901014501500d0a003d05011050134003800400b540414859401071315205e4040d404148824801c4402c1341d5044001e48520948800140489034894481c41303250038500800058100891040741c010078905968450361511022811800741600110545143c05400400103c903680c0744201c404480c82521010401c00c2141045034a80214205260107907404000b08601a41c0740d40c00c440b50081411241038990b1200314806004201d01d410003481031961070442412550020104195104c1c030520501c0000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 6212615 1250 6211365 6211367
    0x1120f050118110d050405150103061b0509010203070201050d0b0d030c1401140103030f021e160e0405030901050c01020d02070b190603030203090d11060d0605120703170912010c030c0f 81
    0x945101284050f40c0303400e10141d44c014206800c1036400038002e904444121000e006080c00f07110080e402240c100da92640741c4807505071106400400d000441c00c0482c101403440001070348030701c00c14070020f04101001803007807400c003003580c004ac00c0d0171390240c00003e62113030700e24003e44030b80d041003c269214405a4181c00580c4014000d200e0360505091802481da40780d03503410b85240108440c0c400a50080017000144003141e94210014034450200038030001d10310f2440140d00c9961600102d01a0784082e04110110b400041150031910081c40c100d641d510340090058024054100644005030000815100703001d03402c000c0701c0c02104201002d00c141d000c82d1290408451142c0700040140c1c00a0100c0b40e442e16000701c00760390307207402150b0b8014240d14040c0000c12a900ad0800c902e940e13030395840c1c01c0c400c6c2d040c0140d01029541c10040141001ca0854844020200b10101c1110302444002000b04c03c135154280c0030310b0714042c810024082641a8000a009012401c003074000060b11000310071011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 6213865 1250 6212615 6212621
    0x311070f0f060e0102010209090703060f050a0b0a0503040f0f03020a060612050a0303050c0c0105010b03070f0207080a0f08040b030703050103050f0304120b09010e030c060f06040506010f080601120f050118 90
    0x440a07000795101c0d603441c000c001d0b1203003002414040e0665501788500803403511410146d900c916440d55002070030720b080488248070300c1016081180200c081c0300040c00a000b00760201c480080c03003824110b40344d9603940352450501d2504c8400402c44040d0b90303c581c04250300000d2142506d80719000a01c2180d4850031104000c40e96610060aa44e012440342c0c00403074001e0340701c5a00450503807001840e0107100202c460a440782a40300c0c3e12060350010410485c1d07640044104c40d4040c082c40904100c1d031805140320b41d10310806070068030b40b460708c0e5224020020780300225801821456010303610b91030b02c28805002400e0074807080d190383c0a110203a4120321000300441c1d040da80d00310282269541e49459070720f02400010300c404910b6589150241444404001a29103848140c0007046545405140d038182d103500644018040c50a140501201740c0c0c00006e9540109524034000c2c14960f101c1c40101e440701041107450404c149856001d08843c00150400c1c0c2c182c9038200810540103002100314011 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 6215115 1250 6213865 6213869
    0x50108010f1404020d0303060801020c061602010c21020d050108030a02011a06120c0f03090f010b040c080c0304060b12010209040501050d0816060f02030709080c0d0b070311160311070f 81
    0x1d034401070400a0010310b000d17440391503171a010717140005030030f0b840305030103400c9a01030520050241d0041d0f04102c4040d0b50b51901d028030f1560f0b84001e10075040403070700250140410350380b0b44981a0440f104445004040d5040d1124178035554002e10603940e44018598481c4e05c01d00c2884019401c00d03540d130b00c0071307207000301c81c0404888081c000601d401d0900f4400d409074200078001140e40a000c100318258111001c2c051402900c014000d0081590201601b5007142c2003081d0700390289090042d80840c85801030510b952011001c012150740e1b551b1890994028180303051450791080d140c5105000c01c59055024103203041c07096504006d81d0b40c0721000c000c4c40780701102c070051a660040120801c00b0001c07000100c0424441c2c1c00200b94215021800410383c0c200300c901d04005901c03003a0070082404100b1185002d50403d17140b5500d1449a0f8036040341d2000001c252400b03161b129111b07000c5089008045920b050020b44101c01c0181c504d02d4020174101810340d46801e1807086020115111440d02d0700001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 6216365 1250 6215115 6215141
    0x80907060509040f02070501020a02010605011215050f01020f01050708010503010c08060d020402160605130c091a091008030408030307090e0910050a020403020405040b0406060605070812040c0b070501050108010f 93
    0x104110460b000c010140c021048880e1044c0d030240405800503609001820200f62990004200329041100050820f000840700c91803c60501c0c10725102020728030350703080c01c1c3c400588020f40301690030f00047c2d19103082e4014080076980780c40c04004403541e0080d40c0314103a8034118000e01030303c41700720412503154105454140c1e1200b0340d00c05080041c5400d40c01001c007c203107508010840c4d02251205811244211010200f0340301503110039007000f00f21381180c1c014042c64401000440b04c1d09140d007000300c0d803000072743c4d01410109001c10100310740300503140018000201100d5885441c4c82c0c405d902e0b600260750303840c0800c4114002080c403a01da683e03000c1c401c25003c0000d0541c515005460009030001400ca40340f0740d6400c0001101686a0340a03491240e801105c1541041c101072074041c0846030168480400c00509200c20030002d00074104452100c0d081800c444403a41341d900384400c81c03103540d9000e4040e1440014030702d800c000c41900050b04803180704c0002c00030028000032035010340e41c1707950b0303101 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 6217615 1250 6216365 6216367
    0x6080c040303022d19060c080f0f1f0605070209010509011a0a031803030c08060105130506030907080a031706030d09030602030901060b310f060813020a150809070605 73
    0x1420041103080e4690b56000078034105103031070b8081851405e01407180c5c2e0f80c400c202c0c044003150003800f01c1c83c060803103e54110f1921740420b103400f02002c1024072010303000c06881441d45c0081242c540300e16601c07a54101e40c044081480582e00c00c8007404a50007a40c04030b01a0464100016071445e0001c1100c3c12910110000142c1000c3c6200000d2240e00c50030360241495540c0d010540010003403001c5480e40c1d4400d8500040f441c2055070050089a801001d40b41044802c00581ea90320040001000499006646003602c9484036042c05081100a170801d60007445100902c10030b1640c44401100c0010700c1521242058507a41c06042c0c440074440741031004107140300b00400000d45103a0045600540040c00028900d8407a9007514196208145221040e00a40c0300d0203002d40315180c4c114010740040d289440e100e07140110b24100900148100f40c02c2c004400002244900380d00200d0b00c14070b500400003428140c45503280d80740e01c50500c1d03445002541c00c0e400640155800600c6609581c0b140e1181 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 6218865 1250 6217615 6217633
    0xa0503070f052205040e0c01020706050c010902091519060e0907180303030e0d030b1003020307090e01080d0905030c010c060b030f0a0501020d0b0303040e07030b060f030a050106080c04030302 84
    0x256950005146041d007000300800c80d4901c588040715070030100006070066101c0340380c134003410801034455500c079418003504440c1110445070703000a07166044841ca0b041860f2503d0f41400c88500404d1449000394200d80c698040101b01700128502c100e041d07000721503500741c54030100340d04141c0c12801e0251301e01081d2041e44124030340c90899580c0c0c3c0d2007a60ba00c0d0131505003520303128914662100340d104a01103070729280210100070080c40302040062081c54100602003141e000281300f04003244a0005040c3c2c004045180184901400c4019140b10b40016455581d5020041d075190388a100100c000b4128200c081180c3c50701040341000500c050b5219a255601e40c0c031644000c01110742c0749036040c415040e0000d00010305001c1c00d000b8901a000040c1c40c1d480c4000c50006680e100ba035814400d41040000340000134195801c03541144261800098109110000c90b204d840703880051a19048003104100d03509855401050580700c00b6526070405403510f40d02e13504940251300006000d604003003d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 6220115 1250 6218865 6218867
    0x606090409050109140105010909030c0209040311030a0f0206010b0f0d0b060c0d111203100317070c120204061410081306050103030c0c0509040803070e03011407030f0b060a050307 79
    0x18151140008200145168503907403032a00b100c42c0c402c070171140116003c5501044c442c0038880c1d1401002c24010502c001040355038010400144090003c0c480c040d4200828103041c03050a0020150a4078001c03a5500d8030200b0018011031114121140140f068000110304903a4074410342e10883d131715920190500640300498800381c403228501a420010620150440e00b10030820003609a00540b561003d40710705115032402c020010710360191110080041c4020540050041d5040b00d401039178561480075074444c030105500c04c1c518058402e00c941040899800005284500100d100300c800b0003940b5501c2151000540559149a078401c03030340a40740640380d006510581d409042e0300500d9910034005d50b90501180e6083c1c202380c000540300d071390040c10451541040005410116003100703451625070340b174021a11009010800300318000e16242e4241c4c41c25000740c0c101c440100b010041c0307403034101d800400a10440e1020b04c03080e401c02501c8485411b2010851b020b000303055903207074507656030004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 6221365 1250 6220115 6220117
    0x150409060f1a1e03010b07050c04090203060402010804030c020603040602030f070207030c1203050f0d0b09010602120a030b01020f0a06050603011a061801180303050706050606090a0302090709090501090204060906050406080606 99
    0x180181210000340d2030000d03c05500f00214080c1c4100030600c3c2e1600c80b5818458500500d0410b110b00482c9005003d41c090303900052602d5016509180140090390b45280c05c8034442e03000d84009401810200030702040000c103402462081e250368040d020241e540f00c0c8c0499880070248005040706045400500440d15907910b0140000d0213820003038901a0660f081c95144e07807125000000c03040d0b444100c1d914520b0b001e0f60b11801000507200400e4104100c1318491454070500c002c1c44140359903404010840c0e4000d0009010707000d9400c1c140c85c122545400c146001d400704640c4148694a0640c0c408200c0c126503682030144000682020305243c201a1076100082c940c1850605002049d120b10428202e50841d250280d80b003907581c00c1c5c65000c5031401005031040503107010303ca0042030013030a0341074a4001005080ba6012154900d19850750501511100084d40048007100e051000224049466800800495410342d44100507190f45a00c01c9500340140d01400002030351040200d02d0341c0c6402c00c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 6222615 1250 6221365 6221377
    0x120e13111c09050c010903030503060906010c05060405010b0307060c0b04080a020109020307121203060302130b04020c010903090f05010906020304170102091c0b0a020405130e0102040302150409060f1a 88
    0x458424038082103008088001101c040c54041c02a40310038000d820801c0c00d0202e01c50f4440282402a0310700d0446d503020b03145001c001c00c0e5901402ca070b4000a22980c1c0b1803010441c07050340103400d85071035013802d0902134080c0501c00c222178000c1c411180005066403294001001054100740058000c0c0c603203544003500da138803900302241199298040400560340c180101402400c08181c0b05585845925110f00c8d05001c1c01c2c0e00c50140351501c603042000d42c480c0b07481d00713079900f081c0c00000039603e80c4000064001d025410900c4039942ca00603a401c109a041520002901c02c1000b8800c840d960303c800455054100f4010040107800a11080104111003401c400721400500000342c1401d0403400440d8001d5013400c29442c1c0c0195501c071b81c0090000c462212030f08001c1c001c006520b8107040c13102243d09111490707104080c141d03440b03000380c1c085042907043d2005990b0003001002e0103501d590011415070881d004156000d49452400039100d011100440103c911080b03460021001200403106c10303400c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 6223865 1250 6222615 6222641
    0x50901020c060c011b020f0105070503010614070201140d0b010806091509040c15030212070201060e070c0312050403030519020301050d02061c05070504062003041406120702010207120e13 82
    0x1502c040da80c030240300741005074a417250b6401020203010807006507096440140554090107010801405516403011140c2c4035120b0310548a40c0e21800ca1004a800520040190392000c001044034418005c26400151000740242d03603845540c2c8030101007081499081d142c020300040110805112070030050700e030702e80c054003a080120b086075580e899074a41d0280d4044400c0001d40c0001c1a03805042c086640c15000310884c07000b003080b541044e00e50046c043e005480c980500001d101c0030000c25110311900c1541028000040c40241898600640503040640356082080d90034212800300940301c3c82507a040b16030050101010300055024400d40c1c2e070100c04440001c0b10340341000340c4113600901a89015070070741d039210b641c0c40703240140050010039241c00e00181c40301c3c0400c222035060000001c0d1415554000000081010440c0004440b88900080e03110b140781003804220030140c065010b0601c06003d804401803980e104042280c051082e08034695008194542d894003100440c0c0c4019146914 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 6225115 1250 6223865 6223871
    0x726060c0316090b22080303070206180106090f051e0c0403030f0c0203010507020705010813170901020a0b070504030303050c0405032104050307030b0406060911030c0702040902040504080306030d050901020c060c01 94
    0x3038088501c620780c4030205001d180142800c805d604c09407400c0c80c0c2c5005241d58805181036041c1318400a454100142666994118003103068100c3c10007980030304000c0c244540104602848003828001405044825411028003100e03454140814180210721560348100c504e032900d42503940680d10340b803200588404020401c1c0d81c840058030240301d81801a2042e4008001551805000600310140242491000c4176458800c0c000038641f512242c100c150138282054556210200407854405402c101034010302000c0b05101c2000d404c48020000d481c040e1340e060089598035002d40c442c1d0321071441440c0d05640b00420f200c00341c900b280c00b00314013043d010006514084d43d031000039240144c079410035108541c2074024042000090310a22005142201c01400070303c40c0c10303020f00704074000103096504c1604009800000c40d034480c0c0c0480c40c3e103079005008115506250030320031117a401c1241c1440c017900c6104804031341c45000340280c403154001680148420940102807121a4100d410403500543d2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 6226365 1250 6225115 6225119
    0xc01060906030b040506060102160e0c070209071e090e01060c021305070905090a0605010c03080403020f07090209010e010c02061c0207020312090a140906010c11030726060c031609 79
    0x1141d0164200441c090b6810020768145400e2507424030401034000703410740d405414440361b9400b01003400c20031118040e0040f501e40e62111019180d5114100e0000d40c0000d1440420200c0364000c440749001010707044001551000510303040d1145801070003a002841a000010424148510b0041d1090b030f10150401481d0303814903003c0401d81d0000da031202c010070401c102c01d00690812401c0d8540c09141400140a000d2801c00083c2c17a901d2258400f40400c0925000101854001c00030900505c00c3c100c101c03420700e503880c142c60009420020341140090035072144200658070400100700002e8004059518200420340c541d14405034090a141f00715809018603400340e64140450907900c0c841e10002940c070600e075010802e01382841d80080042281e040d4080c205a02c5012105602010a080c82c07403280206081c0007200580f204401c1c1c1d0b0500c10910080740d150710b50200700c9002004004199280c0b080c0c620400d0300d4000c22900c0c038106100500005048050007025004031070850300304220155 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 6227615 1250 6226365 6226379
    0x70201090f0602040501020d050316030509031201030308010311030d0f030b030c0406030b06120303010f060c0201110f0f010507020111031605040f06050304021507050a0605040203070f120c090204060906050c0106 93
    0x604200c80c1501d60b550301040800065030140404050302c541881e00e68510702e0607080c074180344144111454105a130f03980009a140d5020000c6030100c44554910b06407542e52441e006044490074001241e42c20404c201d04e00c81c0307090000e0441c0700035000391926890018407210441c01840c00b03500541d0326115210003039038a5211441420081c501074940884a840c00e10300388041c400d0003010201c101e90041004224606107140c45000f40e4190b803410810b144810700041314580700701c07828200c6600610700d401070607000004096609180038402030043e65101c0ca070580c01c94003600403890301d8100400002d40c8140c4081071480081c40c007030806504103074840c0f5031f103880b11800c0d03004030b0702040000040c042036107030032403540080c64206100f403894040f66030b45d0182c40700d1403100014000d85e1110701250466405128805c040d0070a50421017280f9960004506610f03205d0f03400b65116806500e02007000c00382d41c001c0750190340840d280d40c0e16240c9000400c032600d85c01821030107141d543c0e840020500e0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 6228865 1250 6227615 6227633
    0x50906040602030306040606020304030f0605060d0602040e04060b030f071202030a050304120c080604080406030b0d060c020a20090f09070902030c04050108060a060801090903030e0613050d0203030903030c0307020109 95
    0x24103425801142c40c1e1500b2400d000460341f5541050095500601c001c10029080d540d101c10a241d011030302240d039071545000326001c03c5820100820031400428041000700e0021049881640200070a00801100d0000d0640381e52940c0c8424a10350491ba02c02d00108440300300c5040e000780302404441d031a02e00d43c0c55050850704a0340280c1961403080d1280c0c0240900002d0300300140c11690301a004604283da10390030355110340e1242c0e4050540311100300310156030301c1d808a0003d540280c82409080703800e100080d1918440001180c100904611030540700c0b044058601e80343c0800340c20402c0c6511201c1c040001040000c000c1c0515214610001c1140303840d60014601881c3c0d0340701101d0321f0300e040600141c041c040041c1841c4c000e5102000401c14503611007085070458828140010b18141541412000381440c03400c1440c481c8903802c244008660203c00341c8001074001d0303054950348080c001040f03032a40310580707403500300d9270003440812890706035080110380040150000040d40401d9507144554 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 6230115 1250 6228865 6228869
    0x61203070b0412090602030f1e070506040309060908070503070302211f060b030f01031209030503030f0a05010f080a020f0a08150708090a0302030d050402060702060301031415040b06010f05090604 86
    0x6415006090003900c603030042014130290285001450604014a00e5502e00780950103e00040702034200324100b81c286001d04440c1074039000f27815102e880c60641800780c5243ca96203d0031000800d01d03180020070300e00124070340041e503a0080103003142925503000c00c9400e12400590b528035072402500c40354444020002003503001402d0784920548031501c811201251856806280580800c10401002246103179440741500d034401c847c0403000d8454581200e40101c20f400c014171521002007401000410080280d02c40d00350748500303000c0350303803651481c0031141d809100394441680100002001442e100c0411202800040c19083c00142c1c2c48032000c2c43c10b204d00b08680080407540d410300089641c0840d000d944030800400500030f00240d0b0303800030350360301c141e425500110b59100003160440d980c0404840d03446800605580d165612424040c0401d210604009035071f20441001500b940c0d4060801071059400261034100d41da1010010340e000584d28094034104030003042101c82c039aa0302c5000d080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 6231365 1250 6230115 6230123
    0x41206050601171e0702070b1201090b04020c0a080d020d020307050901030605090603070902030c0d05011806080105040f0206090a0b0c030a031d071707050411030406140f061203070b04 81
    0x40c0c41c2841d1001401600c03624511040070a0984101305404016243c100c8240300c0000300880e0503520074404030308000c800d80100202c11000948200420200c50b0300d14107079400140b04000c00007036042004124401c500c407941d62a00f00b1420b403008510184044c0401d030341401c00c0503140401050400c0e040741c3c070844040c0c010039000724042c444c1e560b06200782006080c094910100b14180300001a51780d220500c20b00f040c036600000085d003445d02c01b10580f4030030003401c2020311055031201c200c0f0f00300c212030f071701c035000e40524000c00003429041c14050744d405141c000911214407030964013401083d40c040c104d2030780c002c1c0410000052404041c0d00420010100303001030f40c0c94807402200181594010381010900d5924201000c12062003c00d024046421013032060341c84200342c2c0300c00e41c00e20055603c084c0d80185054036400144600400840c480c500c03a6008000b801d070303100c456000443c01034682180b0010980c0005045052035000007400070040c500720790a2090700e1791110715182c0200d408031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 6232615 1250 6231365 6231371
    0x30225050303040f17060906130309050901030503030106020d02030301050105030c09012601141e01050a09032f120a030e0301090f12080108060903090907050403050d0905030c030d02060a05060105041206 89
    0x201d00018a4030383c44100000c0e40107007110381003050710180d4546009e40440039400e4020071503010075016941e002c0041c2006040d2541c80e40e07417402c3c21a1260003d05c648000350103048121200c05201004403030588034140c441c076040d40c507812030500040c1c002c07100d001d046c402c41c05400c004c10a522586465030751402030383d6055944c10f103005401c907840040560380c000c0c2d40008507c41081c0ca440e01101c040300c0d0a10b80715031034191000c2d003107c03c20010f0340003800346191914600c1c403001048881c03d9040c408040703030521082c7c80500b40240a042d00029140f039412126800000078030450256909420090012070381e203043d44c89030f1501601806007118111410384400140c0c03900104118010250203014007118645582da20703031a84280c2100d40d12500000b00001c0c0c2160196090300c0103545c12004803401c1580c280c00150040c00b260050398481e02c6082e52450081c94001565203c100c102c0d0701074002d0b03490305070101c40a02030240c5180c0c140441844082004a0960103e540b9203003d40b00c08 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 6233865 1250 6232615 6232619
    0xe070303020f010b030601050405060303090a03030203091c050d030e010e030a0216090501030206120402011e0509090f0c07030302091c0804150302030f06060a110304060201090b010503010504030225050303040f 92
    0x3a14203140ba01c40304107030380d05050fa103a5503950003080e0a1304640c01500c0c007144c56660136000900b035200f104011940500b484074040309265002028003d88502503c4030800390200030160840100348000040c95940b0108a00c00740d24800e40041e50010704040c00418010810302440c0d08680280360a200103078404105080c03140300381d5481a005041c4c0c0e45040144e941540c0210311107108000f166401c1d00520000709046910030140c030390300c401140800e24070f103602584000b451a4824182c048c460b40a0740007240c40d460f08556a9401074095503407040c84d0000e2981c4c00e402030b40040381c0840e40030031000b40700d85c001500996007003882032184003c56070b6503080007500310324511090000c10403d4410700400200b24202407806400c06c00460b030f841d884988100c0e04803950030002001c4e503902e00020a000034803e80542000803494407402c04200183e07214400c1c1030813608100d0740900141d0107004240034060440c40107104111070318188000854640001c130340f441c0d01c55800041040044942 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 6235115 1250 6233865 6233867
    0x30706050f060603010605070c050a12020906030c090703090c0803070303050103050d0201050103020303091e12030301090b1f0f02030c0601230303070b04020108060d050a0c0501080f010e0f04020d05010e070303 92
    0x34565020340010341d09071041c10114003140d014041405100240400080c0750f20500c80d5000c1c140d0001d080062007190155140c0c0108189007a1205049024081d664080351003450046070f117001e09400540007680d203980e200000c0340a452a9a8165035001441501140d865014001450024045c3d10085600d51443c5401032401c01503011203411a450440140010781d030200480c3c00c0350408075880055010002c203845040c03124103410940c03160900c0d0980841000100c007541c100c4e483c2c01c01c1004034541010500c0b1240320300c2d00341c1c0d481000c116003240480c81e00802e04082e91150034030440f820714480190561501d182a0025600200140103a0110205c0c00d200c500042a081d0060b5060811a81d07400c0c002c000040c000a062101290005e1640c0d101c0c020400ca001b508502102c05007005400d0040e440500340c02000c0c00a21301e20000351070601c0501d10f0f641201d03c11600d130a26541c45121540710981c4c0500f0032648210080305940105109002d01a440c1c0c02490140604c1072452034 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 6236365 1250 6235115 6235121
    0x503070501090c080d020703021009090c02010b1513050907030b09070c0606050f1011030f0708030a0501060c020d060207080d020d0509060105030d020c01110309090403050a0315031509020d02040e030706 89
    0x44000c3c0c0a502c4090888505c56020440004503581604c01020400003400c0946103003503035402c80c1002da0b10b0b100c440941c450341500000f44078042994a24020b40200c9100c000e684140b11040d00300034000517041003142014030242ea0710000342c0c503001420b0484200000c00c2900c060700c640d0000780c440900e030000d00c1000e01c80e4100070300f81102c0d10387d0f19105d03080105079104000c4a4110500c50328058902c070246061040796010a0009000e0b6511241841c01403081d030015665902c143d0b1400c0000700d6101d0040250702c0807140c00420837144507150b541c0d076401035404548211540c1005002c00c8202c2445400540200c42d040940420b00e481c0000440b494444164803242c400d9103c00d5500c07200a4000c6640f084904007803800e1903070980c542140e98911300c00c1d01050364201454408000070301d80c3c0000500042c0c0213558050242180d001503155102c409404003403c42001a1410b60292490794004104288080e200c0b9541c1c83c0d1a400103000c9031801403030b8004036040001d0207410400d480c4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 6237615 1250 6236365 6236369
    0x13060b0d060f15050a0903050d0903060b060702030a0b0910020d06060201050a0c120b030a0b150102070906060206010501050304022107090f05090c06090114040602210c06060118030503070501090c 86
    0x459804081e520300140036200608020f11401801030002d440c2604900c10669000510740080440302c0902e040340008040c030403a88410b6804500d400c4600c0510300c0d144044500c4207400070003c1803442d40f50780b15141e8840020301540d4241c46040001d00c8007261034000380c000110114030015103580380040103401c2d101c004107405089442c0501d210715540c0c1090040c41100140c2d13000081d28004507020031b181520103c00902100502400c1040c10184000000002e60083c1d082c2c0c0e010960742c07084003050752402e0103040056003088005002c5c65210708081c55000b4002010850f1640360700a0505410300303007200c1c4004640021509102c01d030054003600000700d92641c400c2101d40f501040c440c0c2c955025031582841070800050180d143e078072a540161304071800d40d4010f9a250356455000c0c0d900c0382012aa00b03482c00070329507011048179007102540d800d0a203000c081c00c9a80c0c2c0c0e0340011907140030300c00e023882c00301006002c6c04404103808001900d030051080300005070780c69090401604a059503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 6238865 1250 6237615 6237629
    0x170d050702010b01080915040b070509040e01090507060206011a03060a170a020a060c0203060f0402120601060305040209060423060103020c010f0204030b06030a021e03030d111e03010b07020f13060b0d06 89
    0x48247e4003640080c2000f07140d110382c108600c032606072180a000c80c3c1038801e0903403450b44141450041080c1c60419404800d841c2d00c02c104a98207590b58004c1039845113800d00c5919111904425226000010300d001541e000b28010102c884041d22510744030300108040317a40c0d4945501c807021800860401c030750b040300500141e0410703034200710150340000d55650000700301945000d84540418110b466281079482400b0004007615515a140c0391b00030b00500e0103e0f401e034892840c610218015040620a002000c40403095081400c00140305002c80d46074040e00407810154204003110080c14207104420003414020b002680d12481c5003045184d90308050641486034010700f04200042c1c1d203191501c4182003802c00d406065641c11400a0b0a5001c4d42c02c028100b503003020034a0a03101c12030f200034200c4070200491107054003021070184c00140402d01918120500401050015142c0110000d8260000908059079080d0010341a01500d00d594070014000002003050310b0344412600940000e0081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 6240115 1250 6238865 6238873
    0x907060806030304050d060b04020316020606010311180109030602040f1a040803091005070210050901021006080606010c0203010906060909031713060209061b0609070905090a170d050702010b010809 87
    0x1000000c0c3c0c0720700c81d905c103851244560007007003000c1020580040224810040c01151a4074002c1d2082c00c0c08580200554018091840010540d6000380b00b0304a4906c0000d404a0602d404884142c03841510015490306202a810001000a20a00040000c1c100d1b48818900003031030400030360354040307a0f0038501c24210000d00c414000c1d04800000c0d11401c0b001116044504039503c0c0e010b54072441601e50103034001e640c55080139201600100100b85040080e070803514ee450002c0307607000488426014018030782d0032440c041000c0c0c1d0b2040d014441a1800180001003240450b501c0e642251815400103001c56200c52911b8140354012810b81d404015080e101e01c1ea6140c031034800a44d109800c10000e025643c0807032400d46130b480300d8080d01c44842125842d49421545261266603c060481c0e00c2611031081070030104a24465004082c09a1a040010000c4040c1c070342e01c41800040710b42d5030b042074a0b004d2022415844890003a039010f40010b40000450104840005000080c010107100c501d40c8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 6241365 1250 6240115 6240121
    0xa03030b040b06160611040b04060201060501080703050906060108071b05010506090903190c0c09020309010506041104030312050a1415011e020a02040905100606030e0c0a050d0305070303090b0702030309070608 92
    0x113a03903070164403001d90120380000c10307000c0034900c42c4e80b0f40110b40181016000200300418800d80542c07100301a5007098aa0b0311543c0d6032a0301c200c0940d80103d6040e00e0541042e008107030154020910300d40c0040c40c504240440c20000c0b00301c1e42d0031001d00300c010f480c01d079116014040c090402901064211081402035841c00f0b80c01c0c014580c222030502410380411084204900c140715040d110b03040641000e0b0401d5550b07042c170445490281c0700640341907101d6490407001c49621082c102c210350443c0d80c19242d101c1210621030550005240080130001646c0d19102c1c00f041c243e000080141c803440c101c1c1130b030a09108560f8001002c1c4240c903104603941149100c11401e48540000b28804815411100420880700c01d1074040c5c20003401c942c4684a00d030501c0780202d0304d0380c0c00d17822170292144c00e0350031030354400680820400c004030030f88603182c1c0000403203054802103882100146595400f80c100411450083e64412040368002c4a0610068201006000004d11305100e0000208510700e4008150700f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 6242615 1250 6241365 6241387
    0xa0b01060c0c06080415020c0309030f030c0d0c32010b010906170402030f0d1d040207020105040605160807060c03050a050405031605010e01020403050106030b0108070f0b0705010e0a03030b040b06 86
    0x140642c01400248130700400000d04201041040380c40015483c0415034699041031109a80d036003112654610a000c0c3e420000407080000007503079080340c40e07032006025103080743c0310503034403814500e4003595110a6452800c117035100000c03c40d0b00050a40a80c2150719003a60304080c02c40d02c0403401c0a0420410203020050316602141c12030040306407000c0302899441d10b03c002498240f4101003c3d49034043e1040030039129401c6190018a241c03902510780e50031405804120403803040b098028049181480113221161081000c1c0c031144958404001c0c2e00d0070a51103004050308000030454110b904c41c6203e14a85c5da140c0200ca400402c03803c3e00f484141800e583d461f840e4080c44410028131046a0b6844003440801d4000c43c500e40e00840013156a2038803814483d002c0c1111340826540a8810400042c0d242c1e170004a440489140038143c072910b03402e0124a0701e1613800712000340c4840d901c4c3c455050a03d0780038050b6031f5106120b9140000c11529807400e000c159907140500b11b12422050015560344 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 6243865 1250 6242615 6242633
    0x70b01030212030d0501030c1502060103050303010e041403070521030402090411010c02040501031101020d050a050415050c0102180f03010b03120a03140a0606030609050601020a020f0406170a0b01060c 88
    0x5250304407a1070944401166550307283d03000b08091002840e0902c0300000502034004829410365440c1c500b8801a147d182d00d00360b98890081c03000800e186c1c0204010822107000c4028942c00911a01d009200c1040d0b038141245550008941a46d154110078802138001440081200303224120b403003068111700c0c254001801d042c000810140c034002c910b0300384810356803080d481305070100d500820402a55031031b428100c5a200588200501520803220070310701c1c4074003070301c00d031444391542d40c0e20149010308250000c0891034403060101e09000d010700200c510940d080c00a007080c411600100b52154104408200d5201e01c2c40100038003e925005082e28a030700c000ca850304c6600c0749808202d03501d61200c4000c070020020000180050603103a0184800d441d03060f00180304441031903a040c856640c440c80038000b01c55041d5103043c05a48100c1c405001401c0c86c21a00502e0340d40107000040341c540d1210880d0040e05140241c0509411107401c00c01081184014603007d030405290200384845550780e11030306 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 6245115 1250 6243865 6243869
    0x6060c0f060507120204080303150924010203040f060309020a060503070e0415030b070206070215060f01080a06051314010b0703090e0a0608030a08091b0307090b03010e120c070b070b01 81
    0x96502c0b038002502860080080c401c003200c00d51004c65442d51b40d8015070b6125081a1204001280c80314000c8189190090406011300d040c0c0400e40241ca070444000c1c510040600c0041c2d0550100b8000040d403407268010000080405d84c402040c1410f542c410802055041d80040003801002e00c01d2050301ca900854030081440260b400192520204044043c2c454003940001d03c4621a9410010503550205910317014502d20303000c03150300708203080c240c00000604842c0960090700700320a03400b0943c4141c040e11b4011107004c1d0300103461070b124404039249212031f4206000968075580d60603c101c05043c0440e00420350300c900241810443e9400410200091003080b107552001008503009001680c0000003e100c80170860350742c0d03001c01c1d1000e0b0004034101c4100d01c0601800201801c03140003401041505200240a0702c0810b0811440c240200341095010348c0540daa0740003805503020800011900c0202002825101d218100e2101d1501c031641d00214904441440400c2c000746900d104141 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 6246365 1250 6245115 6245123
    0x309050c040906020903120a0912020105030a050a02120708070207060e0a03020103020903070b071505090606090a05071103040915050102030a05040e040305160b0906070201150302040509120301170106060c0f 91
    0x50910050810f80080d0084004481d41401010b0030350882c0507192000f050340c81e1003602c1c0d02c20742c2950352a248034982000b00006c0e02007502080002c10681c07940c3d03c02644a903011a0040c06e001d000020f56080340d800b03c1d54000030903040024801d0f1079404205c001e0041000e443c0004800300101c0c00b190241c1c0140c48000c2c141900401c042202d50b03018042140981400e01213035841c2c01e1a42410104000c1e010450384070300c2e250030040b440e00d00303020440074031031322000d400d5404503200e1521501c0280402072244c810031403200407500740243c09000070002480c204001140d2401c4a60300c1c2d090201c0b81c0e41c406419588100000102d46030400283c80c00c6606650f4180d00070b17507d41c1010756203482140c5800d1902034000c0014000c01c10070700d45c5140501c60b0001150700c543d6441c00107900329140c0d030301030820038034600308200010300e0070b03400c2180c2c408410420313141210301024030000503070802c2c0c00c01e01040841404005000c00c09101c0c5400400d01c0e49000006100907458070f40d803041242d50050 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 6247615 1250 6246365 6246371
    0x3120c1b020409050d0201020405150304050a0b040804050d0b060a0602010504030206010e090c100c0b010504150909080c01050c07060b0d0b070302030a2004060318020906061605030720010309050c04 87
    0xc007955140d52201c03000a412a0075201e044101d00c070300a00070340c400d0042601c10281405412510924001603a10039588a0000c280c803010381c3e201d035020300c280100b045445c00001c01000c5040c1d00c0c2c00b2118004944201c000e801c3c9030408070100300903104103420490031607240c0340401000c02d030f0000b01503044a01c201030a10031078942041d01410130403625149600714617083c02d46540c0c1644003515101e0f150050ba15102140d0b2a0f00c204820350324855120320fa01001c0c0c040504c42c1c00580d500207071710f05200d9003e09140c50211400f180c00d4540031100d0441000e4042009030030b203c8107020301c1011080c1114400d2942c1042e80e038041d0301400203072080c010103502000050b0402e00c690f001e40b40089a1001c0c0b401580c4000c810300d60f003507016004900000323091404051222040780e000741c8801d40d0042901031103568000602049401001c2031501504180301c510010420070300061100c1c0340104040c00441c0c8100c5806c1900ca85901d003040e040516004103030300455008038528a04480841d008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 6248865 1250 6247615 6247667
    0x5030615090c090d03050408010e0601050a05060c01090b01090608060f011206051f0b190c11040203040203150a0203060f0f0a0501110c061909050612010302040506040f02130303120c 80
    0x100a90040f00b10840d001540c0072541028540c110016000312940580203202d135411a072180d6898210a20400c0e070010100b00f024805403800c0d801404010300300c0b00000035003148903141c0111422081e4072404e0900e03500c4005210b42c0c4424850319502050080a210b82c0b9494148280d000c4142500c0107400703240d451000c68500541c03100c6940728505c10756a40802281c450301c031199a81d01c441c005855841c440482c418541e800f4500900c85030ba00207680102c403101010600000c1e5000a000306d074235001c0ca01044000c245a45407103402500703500b900503120300d002c000380301070b034000007907502e2007501034196009080c1d4446842c44146c1d882071804034140348200039060305d000301294980b640b04801103000c88050160580000c0030b012640d4901d440d0581d50000e2009505c124400c2c02c0610040350014005810180c02c01c541140c005000024048600b5080d401280c10140740d4860854848104005140d0310150002103650401403c021111540c24060003000c40381100c003840e0780300703841d031 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 6250115 1250 6248865 6248881
    0xe07050906090402180f0a0503030403020d0503040503060a060305010609090803040f060209030307030e180405030409020a09030f050c0102060609011215110a02060910050c0a03150f0f0f0503061509 87
    0x1981c0140401510135521030420780800302d00780b50307800744a50041d41103500070082d610340075080400300d0f50098055440c1034110f27000d1146113004500e045d9424803040100042d030b5101000501d204141002002504c1800d51505600750380090344459500340c1094010400700b00340c4411203030010382c403e070207901c090614580000a40140001554940004184417090540104248410320f1017154030204030072000a0842960100341d9020f449540180400d01c00400d09034018813a10a0030f04200c0862540c039940d50300000d0185004881940200f521f00816507010080143c00044c00c41d4507880781c0d070600308288080c1d90700850180404a42100c02c000d480481da108d80b00055003500d000740e42e19203407103019507140e205460303428042c801c1340902c004503035442c480c150240d00e00500003031500e0b1030707110b0440140440003504c0d4074900f80024000340302c1c101d00e1030003401481c01c080844032940c030b8404d0180302009a544020b00a80107182041000d0f070315805400b00704142110381000c4c5454130300d5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 6251365 1250 6250115 6250117
    0x20303011a040e070f090902041e080d020d0c03090506040303170a0e0309060d02040f08070501080903030c0301060e0f030604030810081203060d03050c0307080405040b010201020a020d050a030e01140402010f05040e07050906 98
    0x1000c7da40652001501155580601800500c604c1c85104e021002640e24440c440d6611800303440301006070031140030540481e00c286c10112800b802840c0180302651964000381040c2c2c002da00450118208007000e8074a080401f0705264801c0e68020f0802142e2031810b80305490344100042d0f148100c42c0003a030768921981550580c1c01401d07800001500300c54450a80b5a51089180607060200700340d500000da80100010450744551074025143e815a442c1c48030640d40c080e800c0444940c03103800455088400c0c0c07020004030f4070450081d03036401c07420304288d504001c200c0010342040d0401d4000e81044800401c081c01142d030000fa0075244000c03400d11505049403940100c1110b0b40040c040040c0716000d00030302902810988008403410441e44044100681c04c07403081d5050303100544c0041c42d0031007416000e00045c0910204030304010541504c00151142112f940350182101010100d003400250b50740090700034480074240c24020f203000d0400b10700300008500140005c080110008542c80325454100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 6252615 1250 6251365 6251369
    0xb09090c311a010e090103030e0405040804090516032f09012006040c0504020306180601030b06070515010b03040305030a050c040306050108030307030e010501050d020f040204030f03020303011a040e070f09 90
    0x1400c00c00800d082010884202c4145440b000d001400c40300c8036503071619000300f00c2812264180c68510a491f03001081c80302608000b04203484402042c800064142c1140c05960710032202c1c54008000302007600d1015003122407281d000d4550b103100348a084201c40ca0000403114111740300120f02c1e01c030304000c001260754109540034000c40355805160748486940004103e80658410b1141609031901c0c1e8085c0070490004960742a408400800c0a08030f5403104440589c0044040c900403803a0600700c00803c0c0641c6c42131000f00c510383c0c00603038189014604500c40501405490700c65519504003510000d0442c04081c0c800c3c40702c1a918004541c0100044017250025035100740148181d40c1e458408a03100d40080301c040001c2403c14810101c100018800c55050f15402000050181096000d1040d4a08821407568005a08001c044042405c58407a0f842080c42940210b603a98140b11010a038a002c1d4400c001d030189040c0b0080c0090381001d803035994428018980f0380da80c2c143c1424200d501c0700c03250f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 6253865 1250 6252615 6252709
    0xd06030507080d020c010212070201080601020a0212031209010902030c011103070b0f01090c0905060301090f020c100219030501030203190203031309060f0803120c0309030c100b09090c 81
    0x7500001603001c0340442d1908592003181c096a200c0b1403183d00690719000c100c02102022481081641c005600511000b030708810b0601c104da03034014142c1c4c040351042119201c1d0014550021844440c03800b0b600a055034022404402802a60040da0100c0e9995020b8290303030b410300200c00580c91501c070080081e2000c070f036084000301e4881d0604840e410b0948000380200c2d074049040809480d403140c0961a0712003140c2c00034006a1440c2e10307204400b402042c0390800d44c000f0b0b58007040b011070919010405042809030b184001a40d84080e41030a0200c004008010014107041800410144e60003051410000a440101c2c420b1820344e803000070704610507040480c0e0003110000d4085506845980b00e4030a0341c507108159142151100181070b070301d0242d000345903100109407000804407070342d01c03011b181c01228500450b4100b0401010060030250501d08110017203507124a080014901811829080070400001d004040a00808142008845800c215013000c8801286444106240c1200190162 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 6255115 1250 6253865 6253873
    0xf0604030b0405032b05180a031107090207060c02250306050a110304030201140109020c07090c02030c030301031101030f0204050609010e01020708010603030e030d020c0d060c05130306050907080106050609060d060305 95
    0x25401c5c62801d1440d403241202d00c010f01c1c250000c0e804004000c5041e003000c518200400c20701c0203640e001c682c09101150010118001c4403c00940e01541d0300240a1540c030520000c280d8401c0c00c0002460031030091081c84210451511401c007141001c0d04070000ea03900180e0118080d50f907100001d0280c040b4100400c0310800020421050650652044040c14280502140349176a2032003810103a00403103580e01840d4004407401c2060968690001071042c2440c011340c3e04249081942c41d0468101768810307200d8039030400c00200250789c0b51050792500a01c1c544114101414000410b06038005c049110781072042004541440e42c0c000c118080050054000a1080a49910700207050384882c0081600a00c60031808118440c000706840c1130038440078000c00d90b0640c031900c0c0c3e00701910b14034007a002484000c10080c00c1d2421440040000303103009840c04181408c0610182c0d203015002e0303104d4403407a4940502030056130758003804c507240318400b01c1d00d07a61a410008200c0b0024001c5a00c000e0181c45 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 6256365 1250 6255115 6255157
    0x60e09060702010b060a1b0f0803010f0603060801020f0403030305040c170304050306150d030c0303020d050709031104050609010b0d020f07030f08090d0801050904030e03120d0b0f0604030b040503 86
    0x1000050041c800c0380303558000c1c0450941c0724140310040c0680c860400101d4985081d14a4580600301d1140c0c034980180303010b802d8407166445550306544203820180741000804414021245c250084100504402008500d040000a440910b9001d10f0100a0030162101c0100d4103100141c07034544050140c40c0b50390010301070340b10401a40d0768020320800c2e029008403400251100d1029040110300780001e8440c10442e00140c0d42101c4242c0202c40480a00d6824080d03180c5030b40c0c0341c0c0301e0a84240b143d9201c0003065425810031401a40f00080c41f03610941c2400c081140030380f1110003250444614040e01511440081503550182c0140ca041059000f40802d10340c007031541c4100c7c0082c0748100340d25004450b86850078219150802180c50401050721440108451304059944503801030192a010413281d501300b00117400c00301d031800c0e07000c0030003004035a1424500c0e581c4909070081c08200c90840c1880c841401240a9010f1440068040c1d5072490010702406000e004460302031078009490342e1070700d03 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 6257615 1250 6256365 6256381
    0x7050f0303010f09020906030105010503040515010f0501080c180907030605060c0709050907030b040201050a050912060f01060207060c0f050c0d0b01080105010501110a02090603011805010906050a0507091503060e 93
    0x50001d00c1140ca81070082a00010055030324400c1b1201c0c03034000f5101900d560300301401076072a0350019108540900c00c10009160024082281d036001e05070b02d200c03c12010386442d0004203620800f401c3c2d803000d04400c02c00036000c1407960340c0ca00101402503c0e10a210341e5507060540c02080e0580c05160088800030352903c10410118035401503031000e00e400c0010b03448111900d036540c642070100804006c0480089401b660045010f0082c00d0321174a8554036158600020410514080504038a1035201c103007445000480014801d000d48210700c01000310b5850494007d00c59500084094003101a0345140001e101d814465080b00c1600038003920355030b95041ca0309003483d803024840c4d9460395103001c002094661145107502d4011071460000e00800c409602049956803001e4003030b50381990307940b00c5a880381c1c1e581d10344140d8042c01a000041c606060f818100c06954000f046048840c1c13600082144182d040002d20003590100b203100c000d00d490701c900a0b00200010b410a800744880c41c0104501d078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 6258865 1250 6257615 6257617
    0x911040609020903010f0207050d050f0d0204060c020108180a0305030c070b0903070c0504060b03070809070e0c0706060e07050a050a090503030d0204081006030305030c0702040603060f09050607050412061107050f03 94
    0x8010244d00800495200c0c03036140c4101d0207000340040c100d4016080c0a4401882500500740300304044603040d2420f480c007500082281e006500901c041102640030038259178000700840e40c01050282c2500034440b079452080d0f22540c00c0d0303000805104000c00030894032014070044d600e001c0d901485144880c203022542660300e40000c0c0e000c442c0b0070142c10303010600782054003500c0111420030380e0607825910f40c048251448440100460070a2007819800580d105000031564055506c0b54011035890b05c15062800c143c0d00c80760015030000715004c00740b0000304e901500f202c00c4170030240303441905c0f503113b40030031500e01c195503004c60f0781448003240c000e004042a0b80100f044407100d408030b0307106e070606542000580742c4c1c038840980810f4080c4005600c1425a0303009049062009200041980e103e545040407224a886a513807525501c8065000300315003000349035000341e11820540e00f0701703240122103050322140100c000c108540790000785d4403480300001503408099100c8140c61340a00800c4000b0b5036 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 6260115 1250 6258865 6258877
    0x209040c0f080d080a0216150b01030609020c060601050304050a05060103030909050f2404020f210106021c0c03110d0305040c0b0901090308090307050a0e090c120c0103091104060902 80
    0x341c01c00e030000184801c07000401d03414465080c1c8584000d50307500080a0004d40210701840a03696041c0c602c2d00010301d68151034038840c84440c0300012520030707107000142110919001390344042d10410400c00a41c00008943c3d90100092070415600c0e03a07075250850030310840050052135445a400040105500301480400781ca5028400b045903586500b1103039100d94041d181c100d54100b5000300005c040040501c0110301d0840548054071b403003109032a000f8994000c425510140c0450310404240c1e01301414a24010606840100520a034160180b0402030a400178003043c40144942801054060003c2c1040c0d109908260782c46c8051041c409800b83c04115000c0301d09601d00301000c190000680256844070106950b0450810300b580d8840308151f224054840d454481c14000044030742d50001201c000d8000400082c810303007441080d507403034500c0450f4000e1050b00c001e4106c2400c0c01001888030049070003441e0110300c40342c040c105940c814182ea84955001800c0400c0400c1402080d002804 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 6261365 1250 6260115 6260129
    0x92d081005040201020123061519020105041a010501050a12090b090a0201030507020601080a0201140c0102070807122c0d0203010221060303070206030103150b0301021308010b010c020906040c0c0209040c 89
    0x400380000313100b001140c003844060320852800c01030114906080810112740225040400e8a191210720380e4a901030440b0301640e500141c3d10742c41000100503100c0d02844805260010980d1700d5410310380042c103a4002d010030802001180464101d02c0f0046820040ba02500014210303041c1c107240e020561501454001613000c2030404010070102403001230041d0407911000d0140160000c654011260245003400c5100304013000d000c6078030114001e100030040300384030301601941d80c0c146107065801c0442455801e0140004c640c03000884540310314010b14010140404489250350074000561620354402010f0742561000c00e10030740c1c40411108805881048181500c120b5481004046c1d4a00c030b00316000b90440c03024001000010441c4140c480081c8500c400411029030840221b801c80e04124a400306a01040ca81000320000038400c011002002303182c000b18000d1540c02050768100050551401107907100000c40382103205035400c090080d40100500000c0c2132506100034846901d000d540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 6262615 1250 6261365 6261371
    0x40303151206051608010603020903070512060105090702030405030304050112090b07030f150b0a05031012080a0f020a02010e090c0403060501080102040509010e040309060804030e06070b07030507092d0810050402010201 96
    0x1e0b1690166001d030404d0b00c0341a61501c1d0795a09020048000c2d402c20071246070144a511408241c9944001e2140e0303030100c1d810028010ba41c5007404010f02500701800d00415900100010300c880e440220846041c0d400030f0805c0c04400c01c100f01a04000c04042c036015162145c241c09101c40c150341034000c440a22883d1030180320320181e199895005404900c16949080d038100080b0345040e00030406541d1203603c019140c40d000d99035040e040142f5119900c01c440840c030024181c50700c290400007412511400344028466031525500182040401c003080310302c02e410380c40018140d000d0203c02c80d0040d6900a800740a5969580707000f40c080e401c0f9000b140c0c030401c52940003040b07610b881072401380f00d142c0640e03d40c061140340c0003040c2c90940019105508020070710042001640f10b0030001c00010307108042e020210725028000900b1031300c02070700701d00800c14600ca0410a81e10036040c20030f8042190030209141d002c101d0035248807540154420400e502950b81c2c03441c800d00050313020742d00c00c1d0300070f030024 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 6263865 1250 6262615 6262621
    0xb04030c0b1f050a050603060d020307030c0b090306070305190905010209060d0618020a09030803040204060b0304080306040b01020d090306050c130e010603060e13030c02030f0102130501090e0705030105010804030315120605 98
    0x2a0194150107010340000d011f1000464078548028440b00050001c0e0070b60344195141e4642d140100c041d50414107030700b0300001e01720b0218242000915445113085c138041200c4e060031000380440307240d24405009466210010801230000030340c11101c03010070080c03e0b1561107454816141c06041c2c544035040e600c80700031001d05070411450007250002e171496510710f5802030039075076000903c3e00050401c0e41c010350340d1440400c0d0300164100071806140204449500da1500000f0807080d540144e1849045400100b9042441c0350015031103c19254042000300786691117550000a50240013030741840b150768490001191a84c0518050503202c880e80c080c014a9100c4072606020303201034500e61030f07100000100c0d0011a104000c0d0304442c0384000c4c00e4404010044840c0c030b0aa803c00a50f1081c90407940000708090342e0020600c43c001e182c9003000d0031891511060141041c007051241c507061080c3c00000808061099000e8a80754442c1d0301030101d46a1204903d014504042200700c401a03d44008 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 6265115 1250 6263865 6263869
    0x70f0207080706020d1809020714060601020d0e0f1206040b090f07081203070201090b01080706020c010815010804020a03050102030405010501090c05120a020906040302040608030a0e09090a0b04030c0b1f05 90
    0x803241901d070f007600180648038136210101d8025030b070380440c070401203610140400c089a0f035000815039240500340e015401d2500e812000e051150150005040d548003103418160039411440d4014041c00442c0e0b44100ea595071000328401c0410000d111b070144c05400200410040d001d207031180200304000c01c0383c3c00c0290400351196600c055000c2c031a1558020b00c0255580841c0344015035100300c651001141042183e5a072070040142a00040c00d15000082c052102076810042d80c090f10a00b403034842441c0c10180e0b6104400f50400d81e1090420000b000018150f40750341c1020030007954810021592850702d818424001d04007805a4502507042c0008058010304c20020303175160641c09000315002e0703210081d01c00b00030f500554001c0d0304420140b10010150741d407841000c0041841c10301652b624140c00c070f4000c210742d45480c407661065040300c5c2408a40030000808034030705540117400440680b00d508007980d400c00220f40c010300314107928041080c00e0032126040450321074082a5445802c0c1c43c0d000b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 6266365 1250 6265115 6265123
    0x6020705191104110405100f02060a020406090b25050601060f080108060a0b030c130b0301050705070507060807051c14010501080108030904021308030c060f10050d060203090f06070f020708 83
    0x10302400644542144075103d01c0d00303074841580701c015150500d14090350398020894021480341d0890114020455440645d90180b02c0180c5c0720324006011842c08c1d0412102a2128100b40241d022988010441040710680400c0002495400303040740008000d0b0351600340d586590074060720700000c400d800610300c03450003448940d05a8007401e0182007140c1d40c2010040040c10300b101010340c507205440d0110b030207480705000342c8a41c03550040040f41080405c4181070075a00040c01c00c20801108000d004c0c041500414200266046c81c81c1a84403925003400c2210a07010752030381d80ca10a00a40105000082c880e03002016182c20b00c56a0003090ba030341c10040d03454102c24886c0c514503400401900346149050350080180700b0000d1046452151500350843c81c54101c00807000d61384d80211300348005101d161110070380c410807541c00c2c11012410240071520210111000402c104d40120101f11120b9041c82048078142c03081044071000c0c0742c41c0c103006115414042c032000140c01882400f194040c0d001c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 6267615 1250 6266365 6266413
    0x4090501061806080c0f190302060d240f0605030703060f1502010c02010e0615030712030305010501080901021606020a1b0c061b020a0e18030a0e0406080313030803090307020402040306020705 84
    0x1010b0300082505c180a0190f480d074109161f111010502c0c4004c00143d5691000e031800320407407900003518550560392084404942e55079040c071200364038030410074441c40b403001d00e082e69000c0c03802548a031106003007580608040d4100d034145a0034401c003c5602e66194419070301400703499000f8082c100550f2010b908841e00c600001e4060b401040000d110600c0d02e41c641c050402d400340c11650200c1e600c3c0e201c64008803041404030300003901d4000420044d0307807012481741c0240b2010001c6240c41c0c122009a15507080a10004201b540c01068208900303008240242020395190102d0260415a20b40b404048509018400c0454400010b51115059951107410110750191449168500f4410607103602c1e0740c001c0403172044000d0442d90350405401400500581650741d107aa94a001c1c2510402058034240e400403c1d0300e9200740046840c01c05d5041102080b6138003c0105907480d00c6280d610342c03d40c070500c01c019400c54000a0000200b009540c020b00101d8003902c181d0304200c0c2028a0400850091 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 6268865 1250 6267615 6267619
    0x3070215030411150d0906020c0609030c030403030806040621031d0901030f06020702120109050705101707020c1005030105040e0304060503041101030f09050303040213050903070602070204090501061806080c 91
    0x8039024070040c200f064004405014450155040c40d91700c601c0c60301030f1028840e08640301c41d000300f140c4141074402c116041e0800c00ca10091403c04002c074521940d24000c40c80041d04100b8140d002ca0344030740743d9500000240040354811030b49c41c10300d42e4050f8204044000100e001940344440d1898100617605c0142d0312100081500d0082c2c0d1a5445140380c5031503c030425102d443d401c2101c0c03030041c1d458013030b100c1d20340c15800004510801e03907007403090a001d0940e005d14003c80c541c0c0c880311501c961040088181d9507162440150703a49039040220310f000540d0720681c0e048850394076841c4c14141c00c0380203076040361011101484585443d82c1c0d503a40b80e014503c500d101060040c40440c000900d40784c03041c2d500c042c0624000882c202c912000703030f0a42e201040c3c00ea416400020601c0194184207a545042c0081030400b440142010b44045940e481003e0000e8803039a800300381d00f0115070700c98001c10007140d008402404201d40701c0c40c0c0c13000e02d100887c1c100c07032075585009400a0401c0011500072003103040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 6270115 1250 6268865 6268883
    0x102030a0c0609050309040207050607080109020f03060405100504020406030e0705100504050d080903060f040209070806030601050112021b011512050703060509010920010e030a050a0303020715020301030302030702150304 97
    0x3450303460300b02406040c0c0045425004c240080101030701c0700c0c40a0300c8411f001d90000c00305030a043d18040c04c440c5c0107810044140f8010084940d200b0000003c590704544150340c0020a030b0f0710702c0001c05140c903068202c00d9115000260000d805a0f06411500b0052400301c19100c02699910030050050010701512010440c00d1008100529042c40000c015078095540787d85400b682034006418030b003080710400d02d42c00c640000c3c40158200f071503440f07a002d04141081000c1d8281040041da40b40300500c28141080780d01040d03581e0f2900603070140d906450010340d45528120039486241c0c0a0702c614140c1d1140d021800c0030009540c2a034007482100c0c10380001c060000141507880702c9016000017040c42c4019901c485141c8001490481d904040c983c0d42d00d10b0803000c8070a10b00050500c001850344a05c80c2e44010382d80000300c1c3e40403520650700d60741402c00598407481d07172804100400000454004892021000000f415000300c01408c9841c0b00307c560303c03400b00111600c40076074042a5405001594 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 6271365 1250 6270115 6270137
    0x121e070b01030311030c0102040906060e0d02090a0b0102100509070302012303070c060b03030a0c02040605030c0108010b07062301080105180307020114040b130e1006170604060e0106030507020c0102030a 89
    0xb02400111904c8403d0405903031512010750041400e82c0c4c815030214003c00c1c3e551600304003c50b4080592070030320100b241e0015100411350001508060040c0c038034605950780c1e154050843c0c1c000c104038210010440801d100d5803404050b07450b1606041c0c8402d0740450710f0705a803401e580142d44428045140c840007103500b151503581e001c0fa4076042d1404100c0756143d85030100c00ea139030781c04c1002e4003a1079200da41c0c05810551500c180000d5681e1580864004e5103c08040c241c580c0e000070106043d5891000c40f00d440743d09900381900a402c9000382851010f030b03110214110021a20b120703e0589007060024400703a02c6410140054100c6d822890140c0d030400d00c503540040d80714902c1e0641801d40d40314141c1c03c0540305c45191940f5401682c2c6825040c0400408000459803600301c20381c07007100100001d081920f07012003d0803810001c1c2102007c4e0441000081e070a82c3d6070b50105001e0594032105003480d40c0c68440207402424107483d160054464961980c646620000440d0824070056490412030382c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 6272615 1250 6271365 6271367
    0xa0608100b030405010e010c03060f0501081005060304120f0203070c030209040501090501111c0b01050f07060905120309010b040c05090105070305040905070c03080a050606070b1503121e070b010303 87
    0x40e084000d0010180030000d091249000038502a500440c00040c00c2c080c9852501d003151440c41e070613001d040c00c00904010080301040030804640d030a003001511a9200396085030030130340300e80180b907000001000388018088260200c4844070324a4940303d400d00704191040e680c9005070b410081c40c21102072024001800e2820701c250300544144004200007456640d040d007510707e0030101c40f0340b1130380110342006080c00c1c98551610021006404000e0000d0b000e0000300940f0a004900203c0d4034005149804c100f000c0d4031887c0d0480d000025180300000d0702c5400380c1303982e0060315518103079800e01c4259503040c07038244640c0601030b680d03407a200e18055036800151410f4202d02010b40621105000c0065521114000c1c5031180c44203075510007201ca41440c001e4902c0d90701a2440f1080c2d454801000959140c01045038219508514820601d582e00d403044d401c1c03000003029040d0140035102c0e907074503044680c1e006400c11000071100500c0f10614088215000d0240d00c10140030380303480c90010000700e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 6273865 1250 6272615 6272627
    0x9022d0f0706110c010c020d021e0607080603030706090c050a08150117031b07030b010b040e0403050702060910030506090a0905060408030406060b030c0304030e010504030302030913150308030411030109020a06 92
    0x103412a80729040c2010441803850f03003155007044d13640015800141030208c64a5061060800d00c0302028a0b4510591a90742850350350540201780d0018484a00302085a80ea8100180c40001d17500c0a418011000d0a00d03004515501300c3c0301c0c6034003030b840502011801003c0407840c00034000111055070394030382c0392400c2e01c824803c0342903036030881d030204000343c1009501c0215040c0645040341d0040a6140c5103107080704c01500164410b45c20b03400d00b403001f400706441e0020320582054051038010348545081c000a0742c580300e032480322a80101241e9004030310540542002d4441c6800f102d070000326640e1140380c48140c41087c0001005a008100010005900d0342c01031600306005680c001101612440a0740c0c0c40c1d0b205490f10041d840021040004065001c1c898009124080c64020305061071503070069502e018428a0314820341c4c0350212501e40100c07543c030400c40b8842c08192126440d81d2410301100950082d281991040d00c804100240c5080501504148a6000d040c1e00502072800c4012280 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 6275115 1250 6273865 6273881
    0x105030a0c090801020c1e06040209010612020d060602010504050705010206070203090d080705010e100c0c02090103150b1906120c1403040809090403030c1b080301090f0609022d0f0706 81
    0x80c4030040740c0101c3c1981d000d00c00341400c080000020700b03018081103031180c900c502040c1e205e91140d0010007000016143c0034211811940b45040101548005da04240064081c4e0042c54820a00d442c00014403140d054200c103009500032003d49403101e4541d001285c9a2900301c9005001da4010081940c0390709000d41021100b9000300c4005081075556640d190075144c05141e90642944050300b05a5013901a10544d501006c2604081c91480c0c0c140d800324031865030500c400ba10061105e600c0c0400b6000c02d4000d100740c2840105850101100003100d0866491680036103000110084420b003c01980351107002d80780800c0382c4443d5994400c4014800a41d031000740129402e09040c03180d50384076214200e6103806a842610301048080d280900105100c001010301c1ca104030b03c0752504401314900008507415129096404a190485204428050207455008490346440000c41703503c581e000400c51a011485030309004002003011488580074001c07001c86001c110410040c08000500c1940483c00c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 6276365 1250 6275115 6275117
    0x10606020d120e0d030203040b01080a0317060301090204060b0c07060e0a17070315021e03160e03070b03011805070206040305040b07020406050d050c040f02120f07020304030c0303050c07050a050105030a0c 90
    0x40d161424402c040e0030303c4441390980020980210030700c020070900521890151001c007006180070303d0f02e038600030444030248244003082d544410100d51036450a400c035540b080d8001e40203121180d0b94410b8040c0a901c40c4070b1000301400b0380c0b00702083d07291042418060b003480c0104008406800c00c000d07012410217081c803c1c0c159106000000000030b4100850a101401c00301c1c00680790301c0c0d510307100b904158030040700041008040007089040300c1190a2030003400050302c2d00760303010b6084502182c6840490740022640030000300001070224a107100e000c01061541d40140301c00d031601e4006a907640c0b011303680200032078014803084c01074507104405011418001080869904c0d9101c010802a027448102a20380350030212440200d81000e01681c1c3c2d141c1015a011031030103400f00152200e4400c041d00c0d010241c1801c902040240f07100301705403806580c20a82e4255215074138600a03100d54803c051030940d81c010408001400e1900d141003d04450040e1285403569035401625801400f10050082c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 6277615 1250 6276365 6276371
    0x3120309110f040e060c04031502030106120906020408100209030706020619020c010b06030109090506090d0c0809040209180f0c030f070509030708070807090f1107080c0a0b04030906080603010606020d12 89
    0x4404c80404121075030098504083c841c0d956401c1d070a00c0b042c0c03041e640c0700620200340100300411940e50710803140d001006200c6c000090701e581a1030f0410107403040e5070091801c2c4c40f036841080b0100285500038640340078100d045a9031240d60b4582070ba10740000b15803400a00180c0d9160320210042a002061082c104400024400341e0350300004079580c1080c0c00a80074907586006401c1008800c2045980000c1a00300078802c19410400c000c110072401c00c001007812802040c01045d03502c0b241c0541d0a2114020302486050514100000e5441012200c01c50105141d10100d0040b00420040700c0c0101440040720001d0f5031250020b9460350300030800d0a8061041030000558440140104800b030081030019101c03184c03500c5484010f03112110103000f0001e280007400382c20003414508448600d43d110341510f4858603004051403c0c5010340d0710203416018280104020190f00400d80416100c064503501c502d5214081414201c0d01075010364030141e4407a190000866000d400c9191503151010004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 6278865 1250 6277615 6277631
    0x5010f090e040803040201031a10050a030915140109020703050304030302090f13020d0e0106050a150c061a010f020313061103090301090818030d05040b03060a0312020703120309110f04 81
    0x20207000c0004881c01e41e8003d4010040c00210340e80350050001540c1c00c00141c0340c0d852141800071f402c1c2018046514240314000034210b02d0280039420441c01c10340c0221035050044101c1142030301824007940780030460f001080001c511301e4124401c2c4c0b001d15405a6841b400c541e25960300343c00947c08414160f51142586152070080c2e600e60201c40d04807000e604025845070800206141078036024a034104859060580c10300050315141154400c550346250700409213100d0a0056403640c10078074014205604100c1c90f43c05180300034651202d18074084e62100000c00c015401282c83e4000c1009a25000d55100010480380f40310340c84002902d034144081e28900302d50940020300315408200c04032034141010501d140c9440c1c52112132282c4a0003a0040d11382042c101d00300800301d110b076000d6045401c0000c00400c006da20313070032260f8029507071165600c64054150340c0302954038032007488115400c81ca189642400e0790302c24018241007990000c07500c14403441010421907425600ba1036581c0041d911511 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 6280115 1250 6278865 6278879
    0x1080304051504180c0e03010c020303040b0a1107110306010609030308040f0203010e0f0a0203070501180905130c060201050604050c04080703030c020f0d030f0f05030f0a020a0903080c01061d09060105010f09 91
    0xc0b00c4d11001d038030000a40d02083c1103000e46290680d0001c00c1c400c1e498241c01140c40f03030300481240e0b80103502170003180c555500e9041c03000040c0851840c4215901d0042149420001517004070344807400c0840844072a0380e40c8000866541845000c0100080c0c80e00012800041742d6800941800348018000b01d51003c051850030306e488100c14a4048070341c0a04130b403600b036003070a00406002d01802e18000c1c0e1110110507000c1014141d07031049104241c2d40e200050030b001d4081e071203052025800205c0c46003050b0f8800c0024064541555518400c42c03500020403200c4140720101c904685045c800f51602c14a10340b0255034010021600ba80c2010944040081c203507100340003001e075941311ba161717106c010b003486000600d014034083c40501480300803c10300000200a840c01c84c2d00400f140c10150f0b0794910320070b08a41d49135440e480141212004074403044d0064040d0807500c01d6840009000c440756035800d280e02100c901c20740e00714940d03420850040c0420351080e0407503211100c09052681c074096135024 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 6281365 1250 6280115 6280139
    0x10926030d060504060b030402030309010c14060a0203010303020607080103020f0103020d060b04030503040f06050705150606070209010b0912011b03050705160303090201030c02060411010f1101060803030103050d02030301080304051504 103
    0xa80303007403580d14541404203251921840c0054860b07280f02909524056010940e2486000001418070201c0e101d14000c0010b07d0540c2c4025400c1c1e40300352421428a008000c002e9002070104402500841d00000c0807031b88a40d281c10b049039001450480684040c200544c000d5200889010440c0c0c4c840b00082010005c40c07005000035481240210350b03c07890440003034001c030b41c29004607003001000c0042c80003242002405040281c95018145480c3d242c000002c0c01e9881203010007900401d0310340c0001007200664011f01280c400035100b03558406450241c180c02c0369541c01c3c2804029020140c100c50f21132081c1c0c09154082c4050400707602c1c1441c0880704401d4940d0b00300040740001d071170f0107800085580c1400390b08a0aa2540000e140c54100cd075076130000444090305d018100025007000790b51561084003a20780f410101c0000300042ca8860341541c0d22a4403d0100741c40d54860360a41060492000003100c0c12284000003a42c02d0070b01709810030207400c0703126520145080040c8408a45403030804 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 6282615 1250 6281365 6281377
    0x309030e040f0617030d060605071106030c160b070305070507051203060409020a030609030e010309020f040e0c12010608060601020304230a0b030c130902030907030201080402040f0603030f090905010501092603 92
    0x140080d46c44500b14130200c01540c015030810b0b010030006000001c0002d400e8000c51116110807109541c0300d03a40c00071984c0b020300840c85034040e0480042d000300144000312070403600031707045940d080c041a0f40710704041e6018421024020308503440040d0344400302900b107000e141c100500074004102e441c516000503840301a16002595200d40d164a000101600036a052618000c01c0c01c0a102d81d2100e5000074003600b44004000c3d0103161203480264050314140b03e01091a00000c140341d5050b00014104c1d40241840e0092115a100b80b00100300302d51f0001042c5c5085440c0f42480c0d5010000310306603d03440d290395070801c50704100303c034a021071005040c001444c483c1104000040e01d60804a006006950166000032082032040041c484002030218002c1c00b0b494080c20420519191032001c24010310102d44440041490312401108041c0d00090b908920035440d9a82c4030925290007980301191070070721501d40410000304003040b4040d485d1200f10307240011450426801d007143c0c100d550455100e4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 6283865 1250 6282615 6282659
    0x50705030f060901050a0606090306180804080706030e0102070503031b07060903051801030606020607030c0e030304030303090203060c030601081503150f01050406090203090601120212030c0604030f0309030e040f06 94
    0xb08111011009100c0c4a5000100c0c1e20b0622100345807020113000442d141c040030b4446500d034071510340d41000b43d0402c0c04840d68800780e146d0352540c0c2c44c0c0c070060b201c855900515000030304000e012061103e0500984860070b400c03801442c59a2144580c43c0700c80c810314040640e1040c400d1200c14085a0140b1808035440d0203a00c1303c6503210505458094000400c40314641410300d00070003031001643c0001c1030340d409012030a0020314650595402e65207015040c3c02c0c158548000100801019403680208500900c2641160030300d4403401a01003960004131215400212a480010b401290702c2c0360070003c031440031f41660549007001c102d6031100c41d421503400411050b100d00400071410684900c0006103d1a0002c60850507c20403c5403603030818403e03182c44000348100182599240018610f010a1010481e603540da040c1c64860344681c41110141d01080e64407125038009400b82c000d108009500d6076500c008400980108001002c00007c0c05031f2156440c0004110b80c113007503502c1c841386810 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 6285115 1250 6283865 6283873
    0x30c030a0e070e070f0f0f02060a02160f0f032303070f0c020301020307080405071203090b09010207050604030308010504050606040e0402120319090905150604150203070f06021e030c07030309050705030f 89
    0x100179009002080704858031802c000d800c4040d42e0f016075020a0258001d040807001503624501d03000300044400540c0d2000e040071001a41003400c10050384044100f0a110782c4503d02d10f00c0c00441400c915011998548080c0c1707504200180d98644a0502c0721143c41040c2401c041002c42500400c1c00ca030412906000881c0000c400d000502208016440046c14440c0516100c0821a070b0000e22401003840303402c00100010031505c030645e00a02080d0040d2202612103900c96580e420024415030082c03003120302880c03400b400310707040d4180002200c003034031110140c11095480356800e0043e000c440401c40343c582d00060020940c00e041307015101c0c821011a0b981d03100c8442c103006801c0121a80038008110392403001080008a456060644017212400090f00213541a650000e80c1503100c0c85a0081c0700b25024600b5400300701866000e80140d0042d40403102c040400c00c030b00c41c0300340c0c80140c5d40d0b000c031480d0501c4018000b910981011b0360052040041d120121354031008203103840300002c0300039480d0b08 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 6286365 1250 6285115 6285137
    0x3090f120305060402090a09090c0302150a0e06090108070503040c030210020d080a0204050102120319020d0606170c0301170307020406060206070f0201050402061c0212070f0201060506030c030a0e070e07 89
    0x10703250165603080305084500318a0000c4082c0011041d5103980715245601d03489150f010305001540413548025500074000a8400c855080400c040354801e0000e100071032809a403000790b505040c42543d90060341a190f007941900e07034000c00d40b5a0341000788101c400c540d8602c00030005071200310480501d251030341c0081c040b19213800e50141095400401019650744107000070040c0b603130300040000c0800703c42c3d542c0035501d490b680390301c01205282d8a2480601030001800400c1917450b0b501c01c070211221980d5400c0707070a070409441c03480341409641c00d5160103800c2c4010b03c0400c0d00306801020054144003141d04d0850b0302e90114003560345982c012000358100308100a140d41e0810224821071060348001c22640c54141d0000f81c030b0f80242c1c8800070345091a0310a202004606038100c0b5000c8400c55401e01403480c020710005c044074071200a810065091000c001603504246060b00c0c040c0907044403003030075075481001c40002003d1130141c0e42d85500c51070300c00081d0756441324040342c01441d1301ea03581c4034008 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 6287615 1250 6286365 6286367
    0x92104050103060501030203040b04110105070c0e0613020304110402031306050415050105030a080a030203061305040c2603090d030203090a0e090c0d05060703050a1508010212070807020304060f03090f12 89
    0x43c0c41d541c800c03030601d4010420040001e09000c01d09a1280d4040104094500e130500102c41c41c1c02200300091101202c6035012803940c08107104184649400c41d18050203c106000c040306034001901e00502c441640303801c0308124500358010359400100084c2c1d207c1d0005068591070141c1e0300c1034600713869020310881c00320004d04041c011103004d440c0070340040c0005511076458126521840d1483d008055020010401d04d40d180c1c9000c69151126001c14403440c145400e24540003040c03407041c60b0a625800600241b9140d0310140201c007800c005010b07500301b41003802402a82c101d80d000c118210b010421800c44036a440300c00d020041c060861480b03001d49082142c0600e4190a88000f1b072180c020054000300145d400590a54070281391f180101d042d40f13401d85040c001d0302e903d80c1940450b441c030b00e0340460b002805501501e40c08140051840a507112240184c0342502d0a035003000050b0000c2005201c0c1901520103101c0d160030034a00001c0030070140c3c88105a1128110b401c5039440c0070101c19040d12 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 6288865 1250 6287615 6287621
    0x207080405040c0c0803010605030402040603080d1a030c01020d0806150301080f1212060d02030a050105010617060a0501090302010f0908070609032a050f01020109050303040606060810030305070605092104050103 93
    0xc00f56030300b8150516605529a542e0302d00051140e4810803900100080464440c0c0d00840011350380014001d4417924007030b0310b0001421002c485605890320b41511800c0918000030020750241040c2c001e41500010440100c8211038001e0946070004881e80700c0c1c031102c003d0580154000e0506101074400c40c0c4542030369a003080700b890b41003994044140040d00f2406500ca210315045201122000f00345d0740144007081c1000c0c4034a801602e10b500c1e01000103100b039000548060243d01d10f50301d0000e1613070740c0310070043c8240950180c02d00107001c400c018801540542c1c003035101811541049071444d561030a00919010300c3c0d41100c80014801d210401c100326088002641030f4180c54000748080c0320114120f2882c00040c81424480c1d480b11820304e082d80d00030b500891030607412800f50b996a25007030a1600240c50301c2e20864000030794800002e401001c001c40d6040c10740382d01d5600d10303162402c0c1da200c02024000152040701d032402000041c1071100303c081e40e043d18a9240f031111640719071500c0005011 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 6290115 1250 6288865 6288881
    0x506070f120e01020f060c0f090409020405040305090f030a08030402040213080d0c0201090611100f0b1503010e01080303010305030906030709120f0c12080421080c010f06150813020112020708040504 87
    0x11742d80c403078070521102c00c07419000d5402a1011000302502c42401c1e80001e8058800c85d50b02a40184c50f02e001e100502d82d218008200d032140c00d07640900001c0b40801410395914864401820b071000a001103001171515800405c1d05601010340d00c15619103405225040420f50300b050400f00749501c071240115600704103024004c203100d041514051003032001654072031110b00c1a040d6410342c2e840c0c0c046130035105580220450f0310007800e00e000400c02c0740306046c2c45900038000c40311036803c01000000d000030000308403816240d200000e103003401901000c0c40000d40000d40034030700f80f0074840c00116181c100a50400c41d41c078059000240039009600341191000600d0b0401c1c1405800d003442034000c191004202c80c00c4410a107501504121600c0d1000c005001c440c0d801440c010b800036482c941440b0541010b11080303121340d0204010fa0369010402a100d1505610341c0220720003030001a4040e03229503110b1946401810700031610019132484108a038400074017246c00e100302060501050038648a6512 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 6291365 1250 6290115 6290143
    0x30509190b06090405030408030f03010906050402040807140a090f1406030115050607110603090304030b01050315010306020a0c08030c0703230f0c010e12040302040c090f0506070f120e0102 83
    0x104805445241c204200109594055004040418104481002218000c10040040d2a1200c000d04807000c100d60083c031940e4016800c0c01004141c030b103024400c50f4100d48285005180301c03403030008180d880d0405502002ea010440d040000303501105030040140081c40c2c110300040d0184034103540c10074030402903d194002d80c50407865100c0c00740e803410007005a840c110750340c548076046480d281e000e2142c050000c503003124002c030038811602000000b81c41924460510b5164a070380b541c0605a032a01c4602e0b4800301000450010004220503078000c0c414004180303041006104a0349404440d54416280d0500700c0300005404401d0551050070f001e1381c0281c0041801352a01003044d4040320b0700501904240d56000021650f6500c08258000c180d03402d03d0b0400c1c3e49014103c03103d4542550028030069000344e0500c00000c08480c4175502801c1514904017030030810a0500003440303072035048402e00b11441400d07034160130041030070286a00c031103a1341541d40250340b6146c040024103100358101010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 6292615 1250 6291365 6291403
    0x191404030917010b03010905060702060703021903090206090d080d140c1818010305060114010809070603050a0603060906020403030314040302031204020604121104060609030c0302090408090a06030509 88
    0x840040c0d80030741d5910898520004845038041050a030764010110000195455813038505d410082001c0861a170340301d0030031a002d071045a42d03000400c0e0207030b200350700058168001a84580c001c15009611012003240060403003400c100f0030001092202e0203448090f00c212401258112028626000310f070a40c9a100780096000d003813107035240249005081041c542036400c0d51540708a526200078198400110807080034032943c1d0303410034035201d00b021302404030709807122203580c0c405500580600c0d014850400007003003410700c0d151045004010140158141c6620ba000000c00b0440302e000c1c2e00981d50213200c00607074a61951802508032034a130003050000c2200002040302194010058032010b80d11400c1c1c0c101655250310008050344116000700200c803005450007000c0c04040c8014181c0c0003030540d000c01895854407000e0f2564179452000400b0700038210010f00050a102d5803080d0024407032110a0f0418080c0030000b01303880302503000003000036902c508000c480d4204008801040810b689e600c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 6293865 1250 6292615 6292621
    0x21318060305030403080306041107030e0a0603060b16030e040e1b01020c0109030f030c02180601030b09010510030e0109080c100b01090b030f041704090b09010e0702030a0f020a0b1914 81
    0xc20384900880c40046c024003000310008616880300d40201030304a01c445200d542d42e00407858043c0511083d052070350b0040701141404a0064041c0c4070325810749010040c21420300c00a045084855120601d04508202049031420b02c40d482d2030085103680c5a00ca0060810040c0742a95600325000100e446811584810801c10b06a41c100041c0000d80b5044800d001d4a083c0f9810305480306112080000c0d080f440882c5259052403d003003169029080c01da8042c8a0103000f5420840c00c0c01c403c0c043c41354400c0c4110b101640550081d80165000b44008002181e0361207291210b9410f908000320550058100300c060864102051041c508214424207000c50200d040141e180d489000c01020b0183e44280d28002c07600f8031180c0003613080c10180088075143d8560719810150060805421440d0007005c100001150340c101c0075200070704c914203d074001c60804030080070484200c10102c14507000e41c003c1b442c8010104007030f55170081c8602107540116010010100b504c0003100c03210320184050401d15014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 6294971 1106 6293865 6293873
    0xc0a05070e01030203010f060311060a090f0603060e01080604030507030302091903080a020d080402060304030305130b01080304150201020702030709050c1c050403170103030e06030a0204090213180603 88
    0x1f4041044041038020668000740401132070040f04042040b5a0304041002d0103222500b441c1000425036078540c609a0400941c00110000c0d40740c203000d0010704659002c042c0100440700c000c2c045840c20351001030240c044d80d0002001c15800140000c0c02e0b50325000e0a443c07020000e8801880300e5603e10703100507140c0c0a45502805802907691a1a249011303050480c4070300d030003400140c59640c4580c0d044000706802082050050b04002d640800302d030b0095a03041c0a0301d012001075035501d0034480320f00d000220031100001160300401c203a034016107010070424211051400d0100703040e104e00b0071095060046140c45032140e540082451000840d07600701900943c001e45030706540742040001903a0940090001602117890041c5d5100390b400c3c403000441d4003c02c0e10030014203158840950009981c407150286048052000c014403950310134071031800300c0b0b0b100c15104001341e900d1aaa = true := by decide +kernel

theorem cover : BRFrame.Cov 6115115 6294971 := by
  have h0 := BRFrame.cov_init 6115115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 6115115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 6115115 ≤ n) (h2 : n < 6294971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
