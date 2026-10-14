-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1140
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:24:56.475652+00:00
-- url     : https://prove2.me/submissions/b1747b70-cf72-4869-b4c5-ff3e87094a72

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 204856115 ≤ n < 205035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 204857365 1250 204856115 204856123
    0x70311030301080102040f090203070905040b220b04050c12010e060a090c03050f0a02070f0602070f0807050706020c041112091915050c0307050703052d09101d0118030203 75
    0x1c03c55039400240030044c0942c03840c2554050f00da16002185541070888025001841c01c0c4a818080e40d1525600082c1c1d5035048a403010005291189000814074128108010084987c0e102d21452070a0003041e071002c1180e09940c1140d03420040b0390140c0e42480e03d49d0540c0d000040246070b20100f213440c04903e0a00d18060a11000c450f41c602103280c2c00e00c410024403001004220800c118418000c00000c54682c8540c80e0801e900f052005907155081d00308540c21680041c0094441440000c642041003c009122000c031102a800d03215080d800d40100720540798860060440c50700b043c40000a05042000c0b841d07008140b21040316035000810368808000000030f0302c142e071120142c01d1303840c410b01040e00985a1120440520525603d051072000d0a00e000b40c00c4064104030000c1a021031304142d024001d10354a40d802d00424071f410800c19120042c1e40304003102c42c0078008050b49504c1c00740c01a11400e8400002c1582d03418100c01e003600440d00606004c0030303840103000b100d1001000d624248 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 204858615 1250 204857365 204857369
    0x324030803071416030503190504050601090e1903080601111c080c0408031608040f0f050111011a3d02070f030506040602090d200f0d080f070311030301 67
    0x3101258491408400c040c042c000c091840792030364a0f0400c088a0248a03500300900034a5050070032a40b030b0380b10b40d01058030007200c18907806606031404051009001000800314100c030b031110824415807241c02145519140f2820702850782d400140848000a40101402940488103140658040260541140c54400711040220700502c00e5a0aa845a5409800e0a03807003200c24025078a02441d01c0da005a0700d109085c1a40c0c030f14089810b07460304003d4840101d40007802e1030f6100d10700c5951175120415030080325104d02c1b400b00d4890240100100c0060140c00380080440100c1101403d80c2c3c030600c4000d40212681c005a40308140c0c02c6403100006000340b010041d003d1400c48016481c44801034030b0304150342c100540c840401d0306e0404c00034a0018025a001e984410090385400c0b07218007103003c50074000001000007882031030345a41d0401d424540c45a80100700c03682c2d504500050180700100c080024007600300c003010069850b46a0503440102030b8107220b483e01140300684180103d0650b0070030303 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 204859865 1250 204858615 204858623
    0x9020d061a040b010503100603020a050c07180b011e0f110303090c011715010309020409021c0b0c0c03030c030907030506100305060c090619090f0e01030203010f1803032403 76
    0x51122450b040503c00c48070320502c00c0c2007861450410304400d45029030759100342820141c000540e2003000744078030203459901c040042100c003010317110741e01e04036400c80580c4080f0701e0038035154000140b50f104400d076100348500c84182c55440c05580c0c074222012482105200c00384a120707105c10300d680c00200f0080d44a14620409040301211600004001e80030b180044840d0790407c2050018030741c140980580c08940909000a0782e03540d9101117005007480c04006580030f4149121030300408441c0c0002066248a0f86181d412a0307a8040d120045004039000001d00340d1040c0002540d0444200055030070036080d1048985803503503503071800e244c103070b0803950201c90f00340c914400c1042090030009150403110812585061441c2c0c0000719443c1e001e0138019101113200c559001206500440b205d8010705070050000b00105e8840c0300312111050280f108a00941c030b00a207000d00c5448902c42e800d2010009004019180070584088000e00300b007000d0801d240c007004524440030307290154880021441 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 204861115 1250 204859865 204859901
    0xc180b03090d0f02032506140603070603020c190c081204090f02091c0606091a130b09010509220b04021206060105030712060803070305360409020d06 66
    0xc546410304480040e08410f0004031800108190f40100a8942c180c1c4102403c907074910450540d04c0c21411000c1c0090681c41c40c0c484210105182050303107600c01c88042c2c0460302081ea07500401c07000c92082c2c00115107942c22900310503110310400310550003034902030350403021080e03106d035600b034200251b0030305190800200240c10040c0f880355014500203a1114401141019052000301e50b00125203564042c28082405541003000b481d0350004014050600b03003000204c4200305501321503000e0211680c403941100640900a05860050001018005c4c212400c1a40707417109004413448042c00b030008107210680001440400f03842d17101d040302e000d80c84401840c1018018050700d0f46064449144a401001c200034207a43c002084903000495450060405240000000d00510300d50f00541564003000a00c2401e242c2d1040207454516401030114a00c9a40103111006040c545c1c43c039101c0c40418030603202d032030b03141c503501c48040c4a0001d0031302c000030740b1a0341c3e0710021144150710003011254 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 204862365 1250 204861115 204861121
    0x301030314030c04030609060e0d020610050901030c14031c120e0105130b070513080607030e030310050409020117070c060b03010207020315040c0b1b011503150c180b03 74
    0x1d480601c02904808850049103142018400038425200c0d41c000640203a072602090b07003c12103541c2c8000c0303d21402c4420390700c41c40c9070340030000d460f058141c5081d5030580e46501e01246624002000d02d040b0ba0303110307042c00903032858114a4001c2100b091052903040c0074840e081c210b440b02d1345524030348012180d41c9088a025600c4501c40840e5552025000d80b03a00d08410400c00f1611028007442c000e40140c0030401039510402c08441c180710701e6140d0030031183d003500001f901140004240e801501562000d120034020700c19015524001180c0c1581c5c0c944031001e003080541019423288080900605d8086508150360801002c500b90030b84903840014608205007042c815540700f44800807000b1070095207440c895800095858804407031103101a041d0340301003010043c0e80c0c603102004008064226845501d0f182e030009211104000c08112075003000c5150703082c49130410640f41078950041040d082400102c40c00c1008005402148090100c0a0030100003541305503080300060441101e1183d59103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 204863615 1250 204862365 204862367
    0x70503130e01061409090a060512010506040b01030b0907050703030f110703033c0219020a0b01090902150a03110310051f05120a020906191707050301090b030703060c030203010303 79
    0x14405034810010800b9213841301c411500c40b48100c500380c0b04100d50000d242d440e01d0558a0080172590721440e4401000300c0c804807100810341100d17100d002c08072810452191200015419aa82820b08552101900000560160041c006400a6030081ca00026a0000c0303c8a0600707d4410102c0c1000551020814008040e4180111040a0408000f401c3c1356007804610300c0301421480d58201030700030208890310a41d5650b505a682c10700b9220b440301d081761415140030b03485086922050ba94441c80e000080386822280c081c2c4594554003509105d803e03000c4c0101c00007207070000ca03202402c06466690015204c22000040c42c081c0c039101280c16032851610b01000080207640c804d0141c44c0c2c020103441e20301e580c0c01c0030542c0c150201c40d00c1d0400d001c2c0d50b2004500000c1c800c1c84241640440041041162202100004500740c100380e210201d5200e042c0380780149240003202d400000910400051140c46203030b4020451403c005412903080c60f85035685c90741990074107840c1000180d40400100149 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 204864865 1250 204863615 204863639
    0x606081606050306010f02240718031505040f0204063809011808010c0818010207240b130906050c03040f02101704060504060605060a020601170307050313 68
    0x803880803240d000d1080d00e0800c000e06075000091500d03044c821010040f01509000b48421000080341d03c44050700c540c02040e8480110b0000e44820000541003180c41144218940b00b08090340d410812807501176a03041d41c001e000d8207004104403100c5030003c0c440c07001a01e030f500540000c1c1c959002000802c3c1b8011180140d2806000c4495452800f0310500f100007003042030032546440703805e1910340005500e00340c0c264188a4640d11100030f075842c08001c426403a520082e4103000b2001c800c290340904071249401403d03805144005030502d40044250400325819000c1300c03003182c520b041c1c003007940c21405000640c0b441803400890f007450388421000d401c10907503110302a0f0008080b014581035003400d0301c5050221641c0c200003030060088088801d01180101c0341500c0e6810b10000c01000c80c5000d10b422000741a050394121505820b1510100301454410709131901c49403181d0080080707a2a14540050400303a042c0c6004640c00100100404181b040c80241011141719404800303061610000d2610 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 204866115 1250 204864865 204864883
    0xb0411090a020909060d0503040b0f0c010b0603060f040b0a051e0901081c050c1c0509090a06180902060f0f04030b10030308071d1201060302240304290103060608 71
    0x1d41d0748100020380c05542d5150703407142c10000660b40c3c9407150800e4540300780380d03100c0c0c1d800c814485074020900300d0005000794001e1400d0a00e040c020711104100009100c080d000c15a4025400b1619011100060420354450800030000500e038403c4c142e40d64011501d4151288075229501c0140b0340743d04aa803c12a0849006111200040c1222600300ca21b5119a00c1e4943c034105c10004001102c0c120580c0c204409a0080048001c4110200486402800a41c0000d000500641601c0000342008003144100070490701e0161041d025036100c14688001482d03040c3c0100e07402082400403460800389a000f0b403101050322041d440d500c60540c10105860301c5d000785020215030000b5804d1000951020045400612904000b150460b054100f50030080c040c3c01495005a040407100840b00ea05411070f5088130b0081e035161a200d0700004224444101250744450952000c00100c0c0c00100c0c1854100344040128503640c0002044640565483c0400e901c10fa0b03060341c4581c4144010700c024020702c00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 204867365 1250 204866115 204866131
    0x30109150e010503060601080c0712051207030c0819020412060501030b010b0a140d0e0d0915030603120f0228030e011b031107080a12091505030c160b041109 69
    0x380a41c5810f001a0b500d03500200980d04012a000206990210b654145c8120340e0780005802c54015100d1401070040d00a16040c020780c0e6042030201c1d01150007413245001940042c0c0d140211540d40324411201490700c0b00841c08201c1c0c1c20800000c01c501c3c0c03201c5894030315101c0c6401160035499410034400801c07060700010013003201080301c0c0030a82d41000000e00807120f00710b215501d0700480040c0100414a511680056005481240307080c598008506410b641c02c502e28040c2c0d42040400031021558a030000130030440030519008000c9005040181e040c04403481150139081c04503007001038004440c0b102020301a652a599802c050300840c42e401e02032020720f4a140c031840c2200500060007002078000d401d20480c600113500f407890501000c00070341081e9044481c0f030801c6291031907081000d01c01c0b81000a04050780807801c0301140c401004c0035001d554455086488102c3d98000c1c81c0d0000003210a10031400614100042d0040c450760302c1540541e03845080c01c5009020700280070700040c0121 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 204868615 1250 204867365 204867389
    0x203040605040501030b06041503050412020d050d050901020c0f0c010816050714030405040c0c05010b0a0e01150c0c291312060902030f1e01090b010b03130803010915 73
    0x30008641c0030702601d04030741c1d003480c0120b00d02003203c010445500c0740b034010700720241c00505107114040c4c03d9003007a0300582c13095014032010700490004a848078420401070001510822108a6000703250b0482a0445296000189808440b10180b40340100341a01150720b0740140c3c1c0683d1039580c0102e101e0784c0c01103500c030000c0d040c00c81f003240080052003203000c0140806c0c509900c0c8159500d0400c1030b5009010b001c0d0007041400c4100c00040d0510300607850072121503003030400c1d40b151801c000ea511021500b00045800d0541d08141e0075010851100e1035100420070303140b03640000f1910600e6800028028018030101c0ca800010083c07810b640d000084050307000b010030150010f0001400e0200495140c125003541c1e510461402034058031088002a40c54071840c450142401c002064401008003460302412000f0025aa800c2c00e03544645005000900b40313100410811551400a5038408814003aa1044541c0b941d1600705a40007a046884a80da480d010800c0390740c0020300140150401140d19 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 204869865 1250 204868615 204868619
    0x18060206070c080a020106051306090b0414040b0403030e03040902040e0906090304090905100203091501080d0207030201030b061603080a0b0409080a0e01092403111306050a050d050c03011401020304 87
    0x9007880c45028002495400f00246003468030303201398030000181000a1603045202c4003400c602c00609218040c0305441172404140018030710f060721904c20513101100d02c058140c1d03100d0710340d4000440020411340a050300d07584540c0382d030035080c0010070103810102c40058540303080181581a00100030858840e03940881d050140c16407000040d1001c480840307401095004042c54403a04120442ca111342c00c0e140044140801c0c1740d0046034025041000206903829681d0320108030b86c0d9174400e141c40c07a015800110051002d03501c00d400c09100307400c014103010729010098460b40b40104410805030005944281881451021030080950b00c800484041c0f00b50f40701500c0b12200c505c6507810390014041d00c00e10b401082d9010749006d20003004ca1681c40c5440c050f1065070510b20b00729141042c0300183c40c1c40314110314811303a0300960381e0400300300241d061024280001903030140d00401100703052041c1840440540c0d101c9008203440f03207843c034500da034580d4945403556191341120254030381550418070003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 204871115 1250 204869865 204869867
    0x50a06050301090b06131508070311090c04090507140c0d020d2c0a0b0f0409050f04080712020309060d0603140f060a18020d05010b01090902030c090607021305071806020607 76
    0x42c45410000403900d10b00101b04440710300380100b17001c808001c0400c800c403000249040000c175010f42240d0246030780314618007030101006031078070007180c0e05440e0b074005001c00c0c460103000d540002e0b886281c5081900103080b80017550a001d401c2400c50070150351080442e807444aa050203000d030071795081d04040c56254151003401d21120304819080b14841c407100c5d140041d59680300d03a40c2c001001c4080a040e540d100c1d4100c5444154001c0c003032502d101d410301e40405d01810b0300400192280340c10007082420310909599100f019845943c1074801c511041c843c0310708039901c6000034110f02d00c000714001151441c3d4600940000603000d900c88803600a00c4450641c01c80c086155548043c400e81c000030000d0010240e910001c05921003c0e40064070072000c80b00300b10055010000028007602c403150840c6c1d4400903001a40b20071036040c01c82e0f000c00e12128030340381040e0003d0860188001e2042508e496000d2806040310170464003540017449900c030040541e52595540340250050784058100c0f8902040 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 204872365 1250 204871115 204871133
    0x1c110418060207020f09010b030412050901120e010b0616020102010b060a0801030224070305090f030703170d020f12192307180902130807050d080309071503050a0605030109 76
    0x1802070102600000c40800715510740702003422040e401840d1900c0303543c54245086064004490032201d102103280200085030049091781e0b0083c0050b034038140348000700302140e006440d8501c031b541784035034903400b4480941c0c7d240c002400c1000d000810744001101d42d80002800c1d10080031507a8056441000500a0b103907203c2a801c0c152a01545d00c52441841c07502403400f000e03615010820000000300e07401c820036078040c0080158045c212004622074910200f09030f1a482580300007402c2c0304500440762081a203844c05040c1e504000400103007880c00b601c1000480d640b044413042c1c0901d40c40d0701003140c80e80e442c41d4590542002c003281080714804404514a400c088011a09540b90b0f1800c00034810300d01c01d964110000114150000c221652515844080e410880100c9824003c80c83c000c03036940310000d03051040380d0f80140a01c0c00d5041070386a45100d0740c0060810880d5010f8201c010a081014034929020340401f40d84c002082e261188580f0120368141c0c1056109904141c990b4000c946840 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 204873615 1250 204872365 204872411
    0x190c11120312040606030308060f010c060b0d050a0b0703050f09070909020621040b061e3304050913030c0221070311032b031107021c1104 61
    0xa16000c60800110515a2850046903000160503011400f040704100207900008216442616003403440d45900040244d42a0703c55072840c0081d80c03c4003048085060b6070488043c0c0700d8090140c412807100c0e500e51500f0300e40444405c0d580648002d0a00c01c642ea4036110b00c80d4407217000703000900c060074191001501c84100b80704d007a940b03c0d06d440b07080b01907580d000c04448903d000a00c00c0c841a10360701082c002141401c841c241d82da5282e0390b001800500b0414110071540d01c5648080030381c0300b28441004004004000181001128500066110030b140c0d40d916600c0f011448005031220300d0039041003560b50b40280102c9803250b0b450040c0d80003c1c1c000e0007080d54140c3c12100f109200741e506503004904031500030846420311403d2800000d100341d514605840700d000342c058610300d56030070149040358041e80031484101400440d50400e000e01c01d80c04000000e007102e03038261418000d90001008825100c07256468110055280700400c04241108100868141c0d400d11964110001d0300c20690f4000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 204874865 1250 204873615 204873619
    0x3040b03060406050603010e06150a02030909040c03050102031009111c0504150213090e0309010206060d050a060f02040612060819050102070803010b071b0e04020d051f02190c11 78
    0x40045422507540303401c107101604e000b4114a0301c940e03480c0030011010f03009031402c501802d0130310018210800d0031011100d68905175002149084105418403980d00340040082d100d02e014400003100042080c0011400f680c011215219544d0502c04400304490444000c500c0925007084900c5280d030644000000034003445c0d000085640d268200403585c182c5000600800510014200e1929606c424043c1c085d03440302c410800c0846805002255240304501e0300c40d025a000f07800227009480d160840d006c0441c850001c1d111114030a80c0d8202c00d4600300307081c04140e0ba030086020b028499002c410700320f07060100501070050b03a14008500c0e407143d070703101d180d2031032501aa034814051100940495460607803250030240d072980d50310300084c1140c1224604581e07020f089410301107a90710714840c0c00162a0701d2480c010742a141e540c03c101c1130100c1180704480c03a000d8080c02c0281d5141c0a10350540301385080b003015980304a0911040c035030000000100050040e001d40d888046441d1082100c3c0c00303802 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 204876115 1250 204874865 204874867
    0x1b031504170c0c040903030608011503080301050405040318030303050402100815011b0b010e010323030d0c0309230f0f0c06180901061101050a050103030206070e0109080d02060f0f04030203040b 85
    0x50016503050020f5400c07400c1e001814103012408156242e8070020485500f40c0081094107145071600102030282d12018003d01800c0c0018091850941d0240e17030481d11038103041c280c840940c8500d040201b59a4010f801090348d6908200560501000e8a00b440d80c3c0c6191034407181ca00b03881c00c2c814041c40310b05140d0422802810740300035007156203040d1002c0380c1c1106241c20590f82d80c1458a00c80d400c02d000441e210742e0b0710f0310f280c107030b881c01204541c1c50031620394003450030f010040c80000002c00070b0781048003c142d21120074601242446914603682c1c805070100754a600f1145100d43e18200a1304100b270015400744041c0c074020800450036031800d030812550035588841070414a640d107800c0a0f491039102c07400d00c00015039260000c2c0d50340715460841d0000d02041d81c505d10642d0842d1070901c0042c016800034000150014803405000e07511001c1410407000b080d403914526450041040d00440c0968001000e110300307140d00004050740b00c4021f5010303682500d4184d07002501d902480c81544a1404 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 204877365 1250 204876115 204876127
    0x30d030e0f0f010506030714061e09090a1d0c011b1b06080103120c0c120204111b1908090132090907020a030e1309051b03150417 57
    0x401404000c0001e289902150640760100d080240208004c0c0c0e01c041c841c0c80350444c002120701000305201c005480081919041204002036180000682d4605040c04002000319540bc0d075540d400d400c5c051003000310006018074214480c0d204039182514010601c0d8060b80980409a80c05000b07180703c2070071036116840e40706c12031400410942d100000035440c228840b4001c12a2540841c00354101c03401404000034519801e4010341d0303400ca071142e0180803104c81d01014003a050841c050419414030103080041c120388038124505041d0031480140004080310b40700041440400c008000c100c000d01034034104c600740300c2c3d99a14118802c00315442c2c10320825103071811088889281c0c00201a501120901d08004020b14440d071381c0e0300000e80749125142e45000309088034070000360741071043d1340342d00c6030001e006c408410802e04444050f00001115104d40c00c00d0006401400078080a040740903020501038481c40405041c420030b40e40c0980102d02690810011031501500321004a032100d02c4150b50340c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 204878615 1250 204877365 204877391
    0x504150c172505030103080f07020f03061f14031c12110d140925030c0e0105040509190204052e090f0204030c14040b2e0509030d03 58
    0x610240605004a80800c0c02c1200480101e500305028000071039142c8140c110000302500c40340000e00010300402c106010021014161078024403a1a0005021303070036400700d590010b0715040080b1400703a004e01e401d0640d40d8940b5134060808025082981d01e080d01c2d514040e020a6a80301612200c00500c1220f040b004400b900440c2000c0000e04943d0702440140b00e0b105054406038001610300d64510710f049050f458000d012a03805026000c664040c10049200c1070107411034a1a4004403200200001d00000000385141c0030701e001000130b0f003070142540d0f260604020458030700400150180e00041400440600031481e4092a140c0c12a23001074641c43e10944a00340081881c040740d0300490100c801484a000e0241103400c4898528040c44404a0348a240c01607009034403005103140115503050148824105184812500c0600700003581e4441500051b1001000581100701c524180840ca4412201c8118000040e501c4e003401440d2a0000010942d286922000700040541e1040c0d003901031 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 204879865 1250 204878615 204878627
    0xc02030a08040b0a0207020a080c010813030f1101110c0601090e01061805040f0b070c0209061203070609080d0603030504080d180e06030f030a0e0f0d0201021e0718090210030504150c 80
    0x6d03900a002d60014039210311402c0c0e9615401c5029501040c0030000141c2e01e0000701f07252451566042d95021207500348100c0640b00d0b45503400d00c2078055500e841c01d413000181ca00005d0200c0b224100014011035141046800483d0f60041580d0343caa410104140004080440c030701ca051498074400046a64031800e284911001140700108090900c0c0240034985500003031244446000701e446140c03176190b030303010011113950f40311903071019130001c5c4880b1010940580c044410306000b000010300d040c400065805c00c4903400d40044000c02e001182c00e110104003088801c80350004c030b0800000c42c050107543c1c01c1c90160107201d60207c1d0621000021240d071028008104d82c00405d80c00c690701d40c1005100502203c61418416002d4403031015003c80601d0004660882150184c000d045144010600d0140c80c148045006400748a50203000031040201c1c1d0508260b40c1c01d10900142c00d511390f104200b00c80400d030258070b00f00350902c414800412500451410500c0380c8041c002103180c02da03403055440c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 204881115 1250 204879865 204879877
    0x27180912140c1f0b090907061202040503010e0304081203090604060f0f09142b08100806011503050f041106130e0408030105030c0303211e040c0501030c02030a08040b0a02 75
    0x10790081c814010002498905449495007101c0000d2004d04000d1080c400300c81000c03035a007071186d03100306010006640180e00082c110700b4103079400751405842c0c0f0007003800c0d90203080001c0460381c400901041411003d0000c0813150520059035841c50030a6211203554060140010305416a122102079110480d030b8040c2d403000c500403401780408142410014580100e03440066102d0090a261220b0003c15045a11600b0b01000742401c000050741001c6404807401489003140e44000140891001c800f000160b00a00c45001f24010144541c0001010b6030006081c0a181d848110240000120746103000301d49050f040e9001a1600e207440006806075102c2e80c80030604c0c10030801404240051a0300440c1a1003050b0212080c0854a8092640d02d11426030f4900a4840b001c1c04a000103058040d03481d0424244040c9030040883c409001505200c1503800f25529151103600b00070780e503010f000e640060000c5002a508080880801801c2c00c10000c000402d64500b10000922184042d4141c4030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 204882365 1250 204881115 204881137
    0x40305090a030516050a06050408250308190906090b070b091006060c02040e07270209130219020619020d0e011b12020702130b012718091214 62
    0x88150101300c0481421480e0103114080c0620300d42c08184903011f14102c5041b5101c05009004000080c04041d40740001c900e0000d50070480d614000000c42c80c03803809401c140c6003100b81c400340c807501444050302243c065813240060103d564001c02c01c511180c01900c0c2401d4000760013039215680c080100c0d080440345a00c4522003440c01001051040d4440300566441d80309a0f0108485005490400c0c0c1d200c03e80d2140d401d090111581d80d0355409400c5150a916940051016042c180c0c041c00050040e8180301c114201541d022a80c035908544902c800303104c4240f58006850507045c01d0300c03101c00e143c26020307106015a400080d006141050307644000792901d82100200250f03d0340c1c01d5000101d08074040074500050200944203c4c6204920031a011268028129501d0102d030b403680d50003a01a00390880e0601548400b000848800d04860540e5040d00000301814035081000c0140e040707100c400800340e203524000782e0340d00041400c0042c000804903810b00e481003102c01500243c5c9807140c080340403 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 204883615 1250 204882365 204882373
    0xa02010e060c0d060803040e07050a0201110307030b04180305030a0b030c0607050114010b030c0909090c0d05010e100203061810170c01120c0e0f13050c071208010e040305090a0305 79
    0x2000588a42001c2d00c034044100f84288146039445001503900e000c0c500038030000c80309450128901d5401003000f001c50012600004c204140c1c039580c1d2044c0d0740c104580d8031300441c1c1c441d00c0d1310840e0b00c0d061082c20010500c610340d03c00341c1500364400030f1041c00000c26000d409907540202c24a42c0e641001041c6065200034502035641e00c181c80c00034041c1035003030b1540c000b440305500007285548000e015244a0114034449500b0090030700100038640401401d00c030394a0280b101101002d4903405400030416000c0c00020a000110303243c07241c07a040c11a821007801314414010b1024640d0740d541413045400105a9540e603903160141c1c5608010400d50240841c0003d20458078840c003800f1940c2c5001e03003800d884e40045914200c00d18802c1c0e41510794003800050384182290b00d0782c588200c00140d4820b026050002000701c280e03100007200c5040c0d808048030100030174140c04106d08802220109030741c9242c0170030203504d80f00803040684406080203091080115203e0903544a4001102c01160804121 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 204884865 1250 204883615 204883621
    0x160e0d0206031519030b0a020a09050616110d030509190e04050609010b15030f0709050301060303090f05040e07090f1107030c02010905041b0c0203010e0105010303080106120b0a06050a02010e06 85
    0x2101030458040d00f14000c1a4803a041c0b81e00032081e40c89841100d41240a5200b02d0350740e410032000075880502e4000901240010118142d101c40002d4100d0095005118801e02034600b400e0882c045545840c612030b484440461000a52160582c1d1005c40250b034410f54103200d00706d0011046480b50440001040302d40c0c204401c2c0030780050707840e009050301002007105c40c0c0790b00240440711004146408110070700300081030701c90000108180d4400490f14002440303e88440000c3c3c2911100c0e0703c00c6d400a141c2080a01c40036412061a20040600b00c41c10401c40700000446501c4d01d1061040e29007a941d207222000a0f40801c0d005441c40c0c120701000b25940380b0b11490301402e40c501344442030340002d00080c00882c60341030910a0f64092281e9169521086508000495210340702800c100d0701035484880e01c1c0b0420030240182c45c0a54401c1d100c807080c560410700c000b0840716000f0f40e02401c0b10705111504000307480b01d4000006881461030007940e6818003039400c0c2d01422885801400600c515020 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 204886115 1250 204884865 204884881
    0x11070b03101d1b0307020708060106180f031a072303010602060718052403041a13020a1a0c06010605090310050919140106080604030e010206160e0d020603 68
    0x8140941e002104075000b01800180184007141c4200e61001c1c48410f201c1e05009049044000356520618610403103155985442c0c00505124080c0c3c04a0049a14000007904104965003120040d24855009000380c0349903840b00032544011180703111603040c08101190030705100b80082c00c00d4500700160007040038490f40f8480c02c0c55100b4032030b00005000c7c00000c0703a070b120f101d00d00a014110075500120040e030f04100400403003070030704038141090300791128407400c0a820308000380d4441c500400118070520180701000e411404006d0845440d0107603612210300603030305c01c502542a500030100000c0c111641c0140e0102501c250f94080180e44070340000040c441b82e000f401412100303402d8040c1ca840301e07030207405402514001e80d03104000703801100d82910006015041544841d009201c4c2d403030815510344d030080c02c441c00b81d00212401d403c00c004100a16410003111111200300b03100030001d03441c1030301c141c1d03000d0f013002c0410504000800a44c0602540c400f03000904154006142d03603900c2c200040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 204887365 1250 204886115 204886141
    0x1061202010e042a2001050604110a02060c0a0c060f0614150403023a020f120c010804081306020a0611070209010e0c0d05040b240604050111070b03 65
    0x224005005010b82150b5400c1c580a90160009054010752526060300c09422140010900081c10404601d5a04101c03001c80540340e43c0b8031400c2c900000d4076042400034042507605001d50000c61030000c20030000981d07400694240c0c00a0061607a41d1103650030310044401808140018150070308009600c00000c401c2c0e41300c1000c881c4000c2c403c0c5d2103240a00d0500080e141100720440281d50144020805400d06049018502601003004180081d034103a9800b000508081511300644002000b42c086040c00c039407074180c2c01002c54100040b03021650302140d4981c40d2101b510b04000c2c021020504010315031056500b9540d02040c01c090458076400025074a03100303d141030303071100d003450b8500105140315022074000c1a000b521410050f800d1881040c00707002c0103806d45040120420000380c640c94240320f4180107600c030399030190503824083c1e0b40c1c0826036100c0316031001c01d103a0400e48500d0340d503a500880e0200d41c028200518281d42e940032050a01000b68400e0700c840000004100001b4159a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 204888615 1250 204887365 204887399
    0xf030506070f020111090d050c04061d06010c0818030a05010c050a1d0102070303081312030b090901050906130203011113170303010f03030503040f050a11030705040b09040308090f0106 81
    0x2d559420b944012450403401c1c0c031401c00204001c19002c2101d000242040c1e03003d1000940104201c51a0b288100c0c08a421656503911842d151045582c04281c8030700030806194220b8401d290030001500a900c80940341e1181d070035a00504484402c00d1256601c06104035101130ba00305008022106181c0e10146c80c0f80d1080c0031034030016280c04060000400da00d1103021702c84a042e402001101d08658003910b0b40d12000e0503100c41503086c0507144000414504050a41289a6401060b084370102c18460081c001400700380c1075074102400c101000000284050784a01e241d405001880c0e1a400403900501401c100429400302c005040c2c02410307540c0f2920802c99040c3d001c041c0ba030404495000740c03a40000c3c024800071408aa100b000424480d00256820a00030883c3c040d90141d90b640d00780c64002081e1044452013064011428940703414806c160081c42c09172820f2140c0413681000611000d001803008080c000c0032804145807000400c043d01d291400c100080203410340b56940700d000c0403510 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 204889865 1250 204888615 204888617
    0x6040f24140109030c0e061201060303020115060804050a0201122405090105090106021b01171e090c0904020d1a0906060306010b090607061d19050106060503010b030c0a090f03050607 80
    0x80e000c00c0900d500c074403c4842126001a40c4034155820b10509007000c10b005800e0b554052a584500740481e0002c0c481c0d00000c5100e0b4000203619648000f407844400036603401070060010403070400011800c04120718180039424a0580313100701090384000c2c0201024081c40700354941016924100111000c85041030700c0c42200c1000081c1ea8070000c0003ea130509010b0721005800010701c1002c001c0111203166441c81c01418002441d140040010380c1200c0c088940c007603054001ca1503101e0541154100075040b4554802914240b5140340108440381d030050302c024060380c00403401c007041c0710002c64107000c01c00004e14082d200b8100407a600d5135808007591014424013419000007200b0110104454424201038051420070b215903d69400030000d0a1020540c0c040c1043c5140d58043c09215610300400300d000c000e18500c031a8107020b0b00b114070720341209050080c00c10060004108000030703280d014a0303240f4000d03030b140d490800440da8041c05601005031000e050501104008c80405c44510031211 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 204891115 1250 204889865 204889889
    0x516062405031e030a0c0519030e04050136060b0a0c03030509030403020f01050313060203131704030308010e1807030303050603010c02010510060507050c03100204080d0305010e06040f24 82
    0x4000c120600c440400f140c07180c1c1d20fa02c100440b00900c4d005040070100c041c01801550301842800e510b41d09003808106c011000180d040f00c4644181c68240720381809011144a9002000329840300012071200314030302c1c0c070301c5c592a5001440400110742c004002070801000c40544810700182c0c050025800b0b414218042030622002441582000060343c084030340080000d01e800f1182001900c89500107859540301e100d60400d40f101151550008601869141000400042c0181082c503007150701d01030b03503c0e1046001c000400100340c2c0180c1980c1520092400c1084a0300e0b15114031280c052850740c8540d290041d40c2000081c140c050344803d120b9103098000b07110400c1d00480403800c03200101c41401601c00c120206019452180001e001aa44540212000c0c5405000000d01d0100a0340010482540004003440082ca091200582da045c0c21308041c0801d5042c804041c900000040c90b241c0a166200e0010800041c83d820400603103408503114600001d040c6010300303c8000601492440b401c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 204892365 1250 204891115 204891133
    0x4051c031b020907120f0c021b01090e0a2f1b03120106031806060b0318030a05030a0c2f06090c131d0708030a03050f010501051606240503 61
    0x1c000c151101c042540107020144641c0c81c21001c2e071302c0c04000071004100c3d668a4076400a184400e205d055150500d940003805800c00700c1480380d210300d2100740c520b41049071311841000204014803e450f003001002c4408900b42c40c0c40d08080d00541960300e5a180420511014441c88140071340c001c1422a006480c14007040308540141640c2748107290f2018840344500e4010401d2034401d07800b0709041440d440303081044403041d845074802d9944036000030307110800010500080e0303040440000c282a54900c0036600340341c0001e1002d03141d408010030700c24045840d01c1b07990340f12600c035880141100300c0001d0003070712903d401c8280034940c2c04682986001403094001003901da110010f00040c800300d0040080380780c45484101c21000d00689400314500b607803050509240381e4802e10645d0094061600215203d0f006240000c0c103440d0090010200c4544000040c041c40e6807083c102ca0b100751030042604800300741498101700030071000054520842c43c000500da041c0240441920844004804603000f0207 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 204893615 1250 204892365 204892397
    0xf100c020d050405241e041401021c0e0613080f0c091b0f160813050d0b0a0c0908060705040503071509180b1c05010c090b1e04051c03 59
    0x101c20b038000e1903070040300c68061700c00500d900801100742c0100100c28500300f08400040d002e884100d4031040003007510201e000d001c2c0b42d20945211813040d800f440200002c1031501030440110700c501c4401000c000c04050300d407400d5194202103600390761a0728004003025545d940210703121802502c1000f410f0003100300c1001c031480c0c18031106e8002c0104019408500c43c0c80d1401d800306521109109003015030074012408260300ca04448107030399008844459039203503071100425441e1391903044070303100310b03160481d950200c0d40482215038002c400350000a9443c54140d0700b0380d90340c0c5c03035540204400d02c21581003002c51640500604100e6a080c3c045480c1c481c2c80d03581640f4035111581190300042d48550381004001c18031240c40e1a42d0002c850000f44410a180c017040964980076046d106088a540d116800c12600344641184c02245d8074041031081d0424204481c1d500c030341002400d460f030000508a4030005603004035402004010f01100101d80260300042d0400581807055010812400d04000c5034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 204894865 1250 204893615 204893617
    0xb090d0504170f0d030b09090a03212d0e0303060f10090b03010603060510020c090c090f030307060e011107080403020d03091d04060e011104170f100c020d05 69
    0x20280984800d820541825040c201d988940d8907001800c1c4a6032000d400441e0707042c040d41c03034510000d40e00803614800d907409200030680040d0036400c480d4450090880825440725140d0190030a00d410311150301c0c0d0400710f90020340444015484841410581d5000b1030405c201c0d01b0340c5480d1548014400d8130918050b407512070108403202030f00036001c80070300712451a125901030340110540c2880d81d0132640b00c464800b51070b00b007608007402090343c0318000c1c011464598000e001080541c4010980a16058080341c02203401803d55000c148000c100c02d242e996803000f00461aa102a040342c1d140c0d03e036814064042c0041d442070311441d519040c0c00f220404009000c83d00380d9600803895a2174240355500b40030aa00c400172040e020450302cad204c0451400c1d500c82c03902c802580d00c804844018142420204222108145907194030380c5028803d251050b4900c007602c084841d681c000700b580660b003210071402c000345081100b4150050810110085c07030250f001d00100746055086441ca00c04240c820340785 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 204896115 1250 204894865 204894883
    0x110d20070b0103020904060e030c0c0307050a0501050a0305040510090f0b01080a0201050307050d15030f120302090f0f031e0303010305070806070522170a030210020403080a08070201020705070f030b09 88
    0x600750300c080060000d400c0000040b50041d2040c040010040341d00700da114119042000f00314082e402400312100a403a080001c10068401140c11803101843c02c1d001a04910558202805041d03e1340e0000d002c6c80010b10004402000a10080c00004024078181219a4255404440cd4840745001145419000135081d103000d0741a1a403a20b59110140d096030303e0b40142c041c040150340c036403e560840ca41d601810030004c0d441280c12200008082c0741500301088460b400c08105441030200050b60303038030a01805c012010540e03080800e0990072000c03905142d0a0b04084a1030850018005000302c40000214101d0380240d0507100f80c1c0e52190038040d140c0c00195140070000c0c9040c001c81d0410305418140400c0014030500d84090b06584100c00c01043c44200d1005026800c5641a0424540c0600035503c0c01c50495a0842c90103045a80c0c808850003558844030400540b8000110381600075030440d05425000411104036a944000800040c8941d001c21124140410007080c45081e0014003846 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 204897365 1250 204896115 204896123
    0x6081f15030b09010f080303010e0c070203010c08010503060f06010207120512070f051902090403050a0309050d0201050106110703020d14071a030103021c111e0a080607090812040612110d2007 84
    0x7107141d00c6c144c0324074102b40c40a40b2103d0031460800030000103a4091180c580c4200003502c50b18400d602d000304040c2040c00c001c00456081d000c020820405070381c04181c8400747c1c1c2039074031142034002503418010300e495807004e9009810240040d18000f80842510328150b0320b88200103e0310303946904002d03c100008039020007500424420301080000703008901078400018140360000b0b8004031030301c940c0d140410344402b200251359100010710041d0b51101440007080750074002400254915800719030020a41900500030f00400f03025103c0e201001d21545009000510b19041201000d01041d00994000e10080744180070342040c4c81c45207503000c0081c403245500901c1c948004c0001710184904210780d50038081c403911040c1d001c280c507951520001c030b02801000c001061589043e541c081e000c10059007101c0519440781c0c0780e011302039000d1070441d003e5075054645203c481c074607203160700702030111300c10b11001d4000d0102c4c100300800d10640c000e0504503000450b420542030341da40c0c08002c611032128050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 204898615 1250 204897365 204897367
    0x3040302090a0207020607060c090602070803030c07030203040f090e1b01080a050702101103060406050109030804031113110d0605120703061107050d0f1806081f15030b09010f0803 79
    0x15180001d500c0350300603142000075160002d00e070f00040310790340215412070f09150b4130741000350b2156200400401508090004cc00c0e99070a1460a554074000140304a594400028010701098820300684005024200b034115116403543c45500107003d0410b00946141700301119400300d00c0704141030350b0b05683c06840350811a00c3c3c9901100142c4801004081544610781c0101c080483d1440b80085801a480500d80c903410103c00b003004dc2c1c4e050783d20180c10024040418804901401d044404a90703010788a0340c9050700d01e40205850032880003040c4a03551800104510400b01c80c4024031100402c40300c1004070b541c5400c100014a004070b804103d43d540020b20600006110b45d000c1c45200020706102800d0000c599174040c0b910614040b02c100042c60082c0c900c520981003914400000a10740e141c4039883d0030b00d000107145000040802c2125000b08040a210148640185003d0f00b80803000425501e500c003030140281490001140c06034103500c00000c4e494024102c0c0c482641d110780061 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 204899865 1250 204898615 204898619
    0xa17010515100c05120301091508011a06070614010611160f06030903030f060b0c07080c090a05041b0801051609030b0106181d270c1005041701090210050c0304 70
    0x899907101e800b0350413200d81c415840c140c080003003140095402020400d0001c9602c41d50a54007400c0011240e120350030750307810601141c41c2c44c11008800130100105030703070550329a0202e08000000c0c201c0c20001d40c2c010101c0c00e00109009600000141c5020143c00440b0032440d521000c406407000c061094000c00300c0001003d0040350300c01d41001d45014003910340890f0210070f50001d0811107481d948a6211a0b600050903c14a0018003400c802000381e8005003003000c1d400f10115100b800000c2c4041e101d00c2c3d813640007900b00002c0288413070a5181d083c80d81030714903448001680c020305007622041003c402e6a800614a58855100001500c0d8800c00c2c450641c2d217002000d841240004071018156840400007155052190704078110401d0700f0341010b04581056007901c01102e8001c0c0484c4030300d130642d0f1180302a403500021500720940c0140c3c0e200841c584a6281180c8902694000b500c500d034a0088001194605400040085000721015041c0c084100400d1b2440d01c550308900006420600003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 204901115 1250 204899865 204899867
    0x103080d020d02040906051203070809090618040506040b0c040614090402071a01031101031406010806130617060f0412050705010609052404021c0510050a1701051510 73
    0xc0d09211000030805810224500030708016a0082c0e00000d4181da91100204040d03d41038002c3c2c1d4124050101651400d6843d44406145104248240b405070300c880f400320303640380c07145c0384140c002c1ea0189045c110241003919001c0c0d164241900d0681d203102005000c00c146484110484040b10007a440311b5040c08281040481960894811203a005031b082c00301c5400700e4106488148094442d1070b51040a60541c940741e402c02035100034090425180980c00c100b0000a030140035000071007420218003d550b00c100042c000c2071202140d000c95414440002040b5501240800c061919082929041da03244031441c4a01d003011940540808101c0c0c02c00240d5500031001441001c1c083d00000c18030544a41085007541c80580310f16140d40142055550b0042c91001004600c02d0215019841e1400e40d80600c2c8203a955042510109907580011511140710b0300a0b107001031101404044c0c0701030352403441906201090b00103102950820001504060300e841c003240305407500900c898200a08094 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 204902365 1250 204901115 204901117
    0x30702040906091b0317270a0b0f09010e090705030f04140d080108190201020601051c020301060e0108060702010e1507030e010f0f0b030c10110307060603060207020f0d0308010308 79
    0x21050303500b01d03901e000c4a00803800441da04a001003c1003110300c092031540c80d180400003114226030904200030300c443c041182c103201a5105460003030647c601003900b030768000303132030031501342d000b4002c0c10b43c000703000d82510440d00c0c0540306100090f2074040c1c840c0340f00b034180020104100c500310006641080041c0b50b00c4038041e000c0741c100c0c5c0502c01102e00705120189080ca0048400594004074501c0c1004000b9080c0811000380910301807140c039030646d8251b0340080c0d0303500010300480344100c691a5105942c0030090050b0b00c1403c1d00100248699135903004424281c89086c05451041d0045000040000e40140180c020400021004040010f101c50308034014080c050030034410952549007503100101c090091040303440552200061259000c045081112412000c80c2c1c000d80002500c008a07540d40102c0c0140300a203400c0c0069802d460860a41c218441c0800c01002d00d8034100021042c00450b902420110b4400c2e52024041041403003000581b43c16160000e0020340c0e4a001840003550080c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 204903615 1250 204902365 204902381
    0x31a040b060d091a0c370503070c02060d0b01020105060d24091506051c0c050d03020102120403050418020c031b0102090d2405060a060e061c09050d08070203070204 72
    0x903a0180542c403504c040c00d59940c0d01900d130000c20881c0411188410345030500e1151410420b90718032032102d0400d990750581c05211720540300500c100480000d03c0140684441003826078024401a5500c1035040d8180007000e402c0c0340e49005629080004160b41404001e03c07124a821160703012542d0a0000d0350071951400c03c0c0f4088010b07490312407480000e002c0c2940842403540300500811040d0608061082030049400d51800e1404c00f2407400001c5041c01c038801b01682d0054450030701c000500c0c1000e80c007904c10b125080e14a030700c0340b400b00000d069100000d0001d488481100b441840c101c1042d940030b038000c20085221b140c00030440c072502d00e01000a0803000c08071240000d800c00107202d000440408040380152400d1754101100c01c0d0003110401760801844428504100e5428094007041c4510b1881c011201031002c0e118002c6055a10b03001030b100840c107080450460303e0001c226446c0580400b4000312000e100382c1750303184c0b0308501030038089200341390942c0150f0400c0d00d07a40800c4040d003004 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 204904865 1250 204903615 204903623
    0x712050402011205090d02060f06060403110303090a03150b01020a1703180618010510030c0302060c01021c020705100902150d09060f0207030207090c09060818010606031a040b060d09 80
    0x24450080e49100f140c0210f034481c1c0b50100160041003003440d00a4100b420040c0403201c40351406e001c101043c0d0b55103040d0360640380c201a031005031071202e5011900d90311864001517486145c400d07002041003117068440005c240c0114040c480020142c3c0107a940302d4200d43c00070a00203025811148201d420400f6540c042c00a058a2584565003a042410f02c101034034039805010301c4094441d20f05c2c1c000d005294200c01400b2200600c945141c403040c1c009005030200910440c40040c54039110f20b000d40580d28a0180519600120081141e03188000e500441003102d95015010030101e40d00001d03c60b1141503a000762000501c10000c505245c3c0c0e69004620f0100401e9807407410502082880c418020382e440c41c208010b0b0b0710407050801070b1038241154130408199040015030301c120341d0300c010f840c0120b4401d0b08114104d0b8072000c400905030040d020142c0c5140d0b281150001700140e05400800c034030386d024421030120b15214000c0c042500c640217501c94000f4070070007108184200540c4001c84003801 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 204906115 1250 204904865 204904877
    0xf06080708191b0801060f09030203070608091015050108010504020720040e250b19030b0a05090708101401050304080702030c030d0e030118050c13061d09070b03071205040201 77
    0x302c0d5200502810303e55880e41c001819450050040d82e40295580c0e002c00c031542008a425850b5500190b41c41b101802060108051007011440e154000c100c2c0000342c0140840511840310000c2c00245508054851107001801c040300008850901e807088411480d0803130301c0e0981c2001d2500454908660250000d9080f07a07480607054179520092000e01111091075900c0500074044a521505507016504080b1068404101c141c0e030254044d4001040229503060110f960750700c4400041e60b03440c0d01c3d032150350402020010058107940c011200e52181049281c1c140e20262180c900c22074606424095a021a40c20400308000c9403040d80a402d07100e1000f0b08940c43c98515001090800780c0c204407940200e240c4211643e89443c0070f0081c120381c0c110b40050307a5420045900c1d040e030740d9040904014020914030000601034040c6070403400203820405000d4030381625808440444120454841900b801130860105040c40030b842140c1c05011740e41c1d2110240001026100002d02c000380080b814042 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 204907365 1250 204906115 204906131
    0x507050408011401050a090b0607110414040506070210060f03020d0203070b040b0c0c030a03090504021e0a0f030b04050603070b0a0306091b1b021309020102010b030a0506010f0608070819 82
    0x6000d002e140364200324100150030f07551502040c0032113112150002160581001e54540c0320340c440c40c0560315015000740d0350411030040900450300901110a071200c000c602c000410050250020702a40100d085508407041c2204000042c7c0845810340210840b03245e6050f002c1001d031514030481c120050000b810307a1801942c804540b6090b50065002c400c000c0404030340700c3c68080060002d0b0119110030740c0501040503c1340c0d00103044081a010303662042b6070214144860303c141c2c0a282650b00100c05113556110380b1481c0142066240702244e00000b0f00341910050b00d0300341345c0202402500080d004110343ca0410220400a401c10010f490405071758800004104080740614251890300303004c2040104410316008221400b98401441c070403905016500040e02d0716031030100031101c01034001030b6140d06440100d01400d07034950b8055040c0302d0080400309004012030708504840340c0c402c00502003907031050f05403010f140445000000c40d0010000980035845a88100381080031444005507040c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 204908615 1250 204907365 204907379
    0x30515040f0e01021602090106230c100606080a2d09032d090b0a0207030623010f09180f111c0302060a0c02010207051e120d0902090a1404020405070504 67
    0x45c2101d0886600680c039074015074158203040c040035002d802c1918043c030110788150441030180814689007150500001400c4850100500c428080c103e01e0840511801e42e40e040010314904d8142c907590441c510305401c4a83c10030030b41e03183c00d52061a19a0446298440c0c0c14698002e00250400b0782c14010604d02c1d010800124901503031005a00301c0c000405849905030003005002d060300002500d039410060100c00da600065044110b80d44110003040b0400c0344000701c81d510301c0078090034507044806000400d0f4501e507041c007182501d5401404000c582a5181031201c203244c2c031100030b085584022100d9011481c00403006041000280607841494200c0400c1c950a440c020003c1d80160000024031486074400d01030240740100910080d400c1c000c1e15241c807604c03410402c29210420820600320500c1c0b1005204803182c101c0301000b45503c4104003441c0700c0240c110000120f104981d070100040c803030781052250460313030070508401030036503640d035400e1100402c2c024080b0800c0c4141484001014 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 204909865 1250 204908615 204908617
    0x70b040b13080f0403110402030112170c010f0204090e010b0d0b060f06120403020606010810062303070f090509011208070c0806090106030311061605160204020403030504060f030515040f0e0102 85
    0x4008207911942c0d00c03031940c00c01c42c602d05246e038901441740c0d004000402514580140c41c0802540021440f45681151400b80b5507502ca1100d28400550a006003001140059400b4204440c01541c00780036003280030038018201d82c5441115a8040d038040081c00210703c0940050b40c0c0402d0180c0f10205582c8010002505d580002c00c90b400321182c100f08000800d13906101c074a4105d1301c2030034112114180001c080c440740109000e03003010424026401c07924403a404811000d84032038645071560303d0405280003051040c0501128000c10011140000e190600225550498200b510b110000d608107130b0b5810020752000c1000d80d40414001c001140d610380601c021400780b0281000002c0325855841c018201040c02003503450a44c2243c0108078102c03c070350134500d0652046103480c40d510410012140c1440007c100042d402074804600030042540080045c4103641e9582c45000398007500b04000c03010385104940d2940d0703d8141c60714042d200c2c28940c010504001101d00082445407207601c2060032 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 204911115 1250 204909865 204909877
    0xf05030729120a09030e04090b0601050901020703020a0e010e10050d0206090d020910150206040f1412030712060806061f050d0e0303040201090b0c25050409030f1202070b040b1308 79
    0x3040f40e0b80c0c0324404c00c2503040440e24820f1002078809100360384064507490b0002c54000c04070703418040001202481030780b00784402c0303001d50350041442e10300a031914216800e10b80c09020307110743c0110100100e40c52400c414000c03000c84100501c6841e03109280d600384416900022401a041203105c6a100010707606e645506100340311141142c04564a032031401d20021040080580564000b44140408120010013070600319400036048500030b0110943e0600d407100d03c045082c0c00403004401e000480ba03200300c90305024000214207000391901c60340030300c1e1118002d071000d9a00016418000d030001002009e101c0820f152410460b00303040030400c00d0016030340403403101c180e29040042080300310740e0843d001ca03001d0881c40040a060a244800766942d4031881c1c210314900560f82d22124160328403900300100030b000301507c103010f01d090515010780803450044001e0003044801c20303c0c400700110342c0300b130700c0426410408641498845498020200304003501c0c102190308010b2008011500170001811 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 204912365 1250 204911115 204911131
    0x6061e0d142802180d02030f0f1507110c15090406092f0304061107120c060606050f0730081e010509010303031e050106090f0503072912 60
    0x103070b000b1544159150518401000c54000e20511004210a2480341022825070060301c10a19640f441d00000e4a00003500901c41c1d420f2190141d41107044ca0045052074a011200c004103000c0c2d11021025984585070355451680d0740e010810540c40b61808034052400303400b00d102c0507840c05603a040810243c1d0342c950045500940c4804800c6699000d20301c500c50044640313034880b110480318000c49442c41c40054000741a0a03151001c1150211a010072120520f82c81039a0f0195072801a0002e02052400310003038982c0782ca0b041000a00320300030400c5821002d0302d900f60341d15200c0d03644e070764424803e0254001000d8038010488010743c0c00a4401406210035151500c0c0907030b20740043c11b5070502002140110801d4140343c010082034841c51b8045056a6240c02c01082400d04040721012000201c80940c012505050000542a070002180030940b0305128007454041d403940285a6910f00a200342d060741d50010401c096030095041d410502e18103481e81507460b040c0010f9044281d08415541c0c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 204913615 1250 204912365 204912391
    0x51204141b010207080106080a12050904090b061c0305030c0a0c08131703090f013501050f030a211103070c0f150804030f1704050105060102010506061e0d14 69
    0x82030b03603010004035000f45407040080c0009800d11020945510540000428501202512300d031030310f004038151601884094010880203010782000f071912481951103e000d0801c10340010010030a61346010310140e05603d031280340d83c4410450b041140d0080500d5420000c1d0400b10384000390110300140705002108403002d01480c1840f0207540f001d0f075809008401580200090300302903c48942ca50104442400d005120100510369219058908440940b861203042000c041d4884004101c5058500554401310074201d8202410b40d0748409950140c800056211710100701d41c89801600180e0031149000e01e41780d0a0021454919088200102c90840c83c0401c01e21212020180100007407038562181c04401d2030316036003d414034601410140420002134006020360b801a909001d45940154034141a460a400e0143c000e0000313840c180e00550800c0081009440d0802c1039074844101c207256501385034034400d89500c155000907402d4100d6070301e850b00d9040303079030703843d50010300c40c401040c049 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 204914865 1250 204913615 204913663
    0x412060e060603070f06031e0e070303020f0a0809040905070302060310032d14010b030a0309081002030610080a09120f0f030203010b0409020306060706110a03060503060103020105120414 82
    0x310300300800189002d009030300c642002c04c50303900280810f808446281c10001107c0c0081410030000780d00c0c0c1c0001065560900900100c00d1b10001401307002c0f00c1c0030b5400c0d29100d40c086c0480f1921a6200034003e0088801030103640410300c0d2642c8141c01c2144144200c84d555a40e96001c00c0464004803100720440030900c41c10814031000740c01d20500f416040145500c0360114941e04c2c549900755800140841040c01c4100c0241c40c5c09610100c9a000c00400b102c081d45c0440c40d0040072561f9071b008507002805620b00515550040d802a03030302850300104521110415214116018180180700c00c811a4840c22039002088102e0380320010b864aa030b0b03500c0140c00c00020054080c6182008090070140304000411a186010b015582070b11a507010140c3d0300d0321181c000a02d41c0c06803020280c4030301d2412100d85100787c00d900c0140303110089910705000303142e995800c01d41c8802003440045d020440030429000410b901c1c03950607502520548a5001c03042819607818a02030503030002103d20810720300c3c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 204916115 1250 204914865 204914891
    0x60311250b0106050a0507060b0a0f0b070510020a230f190e1816051308031c060f090c05190e0f0409200d0b15010e19050f0303041206 59
    0x10450140c5480d04104c0d2801c003c01400038410302c25590b01529039a03448415440c580da6990140d00103110102d2100301445e103c242c0951298400341d401c480c41d00c504264410000841c1c0240d5802c401680c5507007130140c01a02044004000c01c402070540d81d1010041e0910111114010707100d981814203403410035181e60703203024101c0c0d51070b01d01c0d552190b44060790288214034021801035000100c0c601741c040c400384142050360540222121003080707a1403000045001000000600400344642080345402001c00020804903003160007080381c0406005424031201446410500a0103070510b0880d01c0d25000c1581c900003820380301000e400049044842c80d44515040300203221800003207c0810450080355600105040d80c039842c0c200031901038110007125503850502e00c807915000510000d00d450300701d40001143c049016400d02181034160303150403034140802c0d41c40ca44040d20a103400340c5800d2001300302c80c007800e0003c2150b05100400c07000c6500c400071005881018071800c004215070304102c4c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 204917365 1250 204916115 204916133
    0x9060306060c02090a0c02031b06070e0a0b03071d0303070501060504050117030306100509060a03090c0b1c091104140f0109270201201507020c060406031125 69
    0x10205040004850b82e207809a5101840680c00c000c10030b01c00981c1c00d14400d0264114011642d45160103c0c480d590300304c5049010503032600c40c8820341e480507000d400c060100412110395000b10b11900030140001011140100302041210784e0107010441d03000007540000345903910607002260180d442c0c0c08100658240b900446c2d000d00003000300e50013070001d880c1d1042e03542d010080050780706524001100030703281e004a08540b04084054880c640c1c403064031001401500380040c00300e95085080800180514042c804d85401801c003003c1c0c2a40311440f41d41d0580604441e440545049850950703242e05a03803240701e806042140f0144404543c40c08512541c2492416440050340905200c04c640225141600111800700343c1e181c000c10325556400101d9600380d1808c90ba481d0070380441401c03a05101d00040081c0d031818600c159081c15501c43c03208030380b2102518413842d0019018401401400d00071381101d81c000e11041500303030500940d030341040e25843c0c02e454010340880c01541c1800c1444600a = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 204918615 1250 204917365 204917369
    0x30f0312050f010b0702010e06120103080c0712030c061e0509072310120b0411120709030b01120201020a060c050415090e040809040e011409070806060d0b100b0a09060306 75
    0x415034096544c9040144d6515100e050b034000d04002c054820f5020700d0b42c1d0704095503c0c803c1910348404196841c3d02d80f40400d0360110804c50f0841c172400b080001d4178116041c4640c1050340c982c0d1420a10092503030f481001d80020729440c2d40c100c14103c0c0f400181c0329184959445500b168000301200c600d08a441000c040355100c120440440d43c02c3c80200e6519000b0411682c0a03403403429254080021001c50700a08070355022560050801d4424904d0b003283e00b015090449a0000d84085515505c00c06c0e0340848c01d81c44010700c500e010000400000c000c18501e50b4501d4018016074116009613a81c0100301c9040954541c0840c4010900340a001400140d41244604500706000c8290512016141e80c2e01c0040c001802c80134001a500358035201d5800050003029190001d104000c1c070b6181c05d0401000031241d0700c00900c520003000420700ca0018049020709400b40102d1113244032510f90601504c4003c1007801c032180c90581c00207113240603e00408400140e591960b2902c1d08203c0000c0035a0300c16 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 204919865 1250 204918615 204918631
    0x150c0e09090616110304080705040c051305091506041e051905040b04060503030c01061707031502070203150c040807150806131104030303051602010c120506010207030f031205 77
    0x80c000308090001d0001d80c2c95004150b0101030500c3d08032403035003141c5500381c81c020f80146000c0481d0015100342c00042c4001a00c0f401c5806010440512000b12914000c200c4040303d8003075010700c10051800c0c180035042d002a10444500445203406010403d01d078841e40c0440d83d00b442c20541400800c6910140c203000d80310486241d0000c003510b010100360300d181401000d00c83d9a60310400300240d6220343c0200010f01380602980c0e19a00c100c0d41c100d008258510448800d0900b5032685408400086007030003d5941c0855480760610071140400000e42000100b00d800d80f066500c0d00100e2061001c009214541165070a42d4945c00c010801d400d2010b241d00c54103d010b68040550000c0b0b8100c05050b9121005441c0306c003a0210950045000d0010249550740503200040d021050542c1500014443c28100e0782030004018501c80407800c83d0101016030b00066410494200d130004a0f410594024a0510490707080070380301c1c0c46803c0c6000b0a00b03012000300d007a940186091102c54007e40e5400f0f140c03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 204921115 1250 204919865 204919879
    0xc0306090a1109180604110a17180303010b0301031202010504111c17090a0b040602060c0f0409061d06010905010504051201270309090504150b0d150c0e 67
    0x12020400490028006020140d240c25503800c410140d24140d5066410003800080c10249640a5032088141503540130301941c141220b0349180300c00c0c44101c7d0302a0310196106800c181d2a141400e44001002d8000d145008400b00146100c010800203103019110316003000790b070781d491441c080c140700103000c91450969040104210100e585001e18100c0782000f50303200e181074110707602e01d6486a210170200814003c14000e0007618444100d000d4080003c00303407002c2e0703807098403a96441c0441c0103074811031b40160701c2940040d15000550b005030400c01c5003058101d090648545220003590303100e42002c000400c55100c4003200d10403060140b90404070030b09080c207503103080ca40002d1641c81140503982c02849103454042c0c3c101804d520415a40b00d008150f030724540900402d03004180f68901d01035000a14900f0301180c1d02081d4450340c0d02070380d40725407000110b8005800010282241c1d9844435401071518520780040b505001d200c3c010300600d07640009103c0000007001d00300c1300741d2501c140d0041030303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 204922365 1250 204921115 204921121
    0x903022503110405061216060f050c250b0a0f080121060203070210050108030c0607080705040302040903260105030607050c0c0d05010e100203010e0703050702150619031a0c03 77
    0x40d00300614110300c00c0e140480e05039101710109210b030b12040130610040c41280c682d135054200103d07181c010754005689403811500c0d180d004071420301460700c8009450304401041542441d046000c40c5a11415509500322141da0b42c0701c52441e50007103a101c0c404165030040e4903503602e1780200c045015041d80d401c0941c403100220113502d02d50501c014010304899000001c1003096000f048510800c0401c02c0c8240322640e1941c030b00c2a101d806c043e802281b0380c4903034030100d0360160203601200d00c01c00b4169a00d0342030510716000c0101410209800341c050213001c081a2520036181c0d000003c0b017540e1000907094a500d000145840d05100030040300821200b070102d014044400b1402c5103500e4000c0320751819207140d44c20468010076600ca24103046208a80f1401841e20054000d54100d44a400c88030105950348401901038032401c42d420f60058020f1b0780f0050001d07001a070b0342e40e007204000d0003d0040322401c42c003918100550303030030541c1c10007514039619890702e100c900602c0d80b00b0b950012203070541c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 204923615 1250 204922365 204922373
    0x708072010050403050408030c0304080c011713020103090b090a0c05040506030c15091008090705040504080a0f14130509090a020d1203020904050403080609060d02010824040903022503 81
    0x710051112a4046881e41d011505041c8108251409481c2100a40340d5030807800740070380d07620f81c0180b00e918014040d83d5400c01c1c69600030711001185008401c0180030903615154901e00d480c640c02c00880c14190303960405c0300460340030790b01c0900c6212103200406e107411a40c1040c0c0d09107025039000070703c0341d4185410881c15803404035200c54240da05446040540090002400541c05801c0c6440c0d004280c641100c2013042d40003c42c1c80c0160a201d0646040544520510003560422500508017480402c072048200384500d0110f140150903107000d42c4401280103060340203500c54010410900c407008010700c02480c010580e140c04c580903600600180d40150701003442800c00c2c1c01d025201502100000c50078a0080d0126600031030014810009882d061a003d041c10909444844c00758200d100000d400f82001c0c4800b100300c68058540b03140070307130b10010081c0303504042e0030440c00143d100c4a01900300d500c4a00070004140d00c40d4010300500398102c0401038100389440c010911007644684200081 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 204924865 1250 204923615 204923623
    0x120f1712061f271703300c0f16111512180f060f0a0f050613051e04080a0e030703030906031112090a0302010605040b011205070e030607080720 63
    0x83c40710003101c2c02010103010001400c403015030202e1030101c201602401d036202d0220040c019044801e02c13001c0c0d049103003040f168048484102c40c40355490b0400100700a0b2145e4005000c83d42c102142c124941090101400c0b10310ba0040b008030b03914401900203981e2454900c102a46a4500c0c440450516030901c00e60070140c100600800709186000c2079841c0003501c207110003410b0b5036407581102c90302d0601035202c1e0040c110403580b81c5007141c80e003034200034505064003409000307440041200880b0103820400c0c1008007809040c0c1c038100301d041201480720040f5005503d210324052490a510b03006101000341079005030800e031510907080890113200180e00600b02078142c1e0034502e000a028103001180d40340500c52281c03894503110458080110340b03d40080da6810300c62003a07000b80841c42c1d9030340c107100c10f40f401c9001319804117040b200304000e680a6540482d50080c4540b409002c40354246000c6800c0030001d448030350010b50300c4000c000c00b05030444110b86203000c5040a44140c800444005a11 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 204926115 1250 204924865 204924887
    0x1140303120105090a0e150703060b0414010e3610030201080109050a0f1b0f030204050d062310031a06011709100c0c050601090204120f1712061f 64
    0x2061030610042545c0d400d4aa06c00078294150340210b40c14168580300050204108071002000a0300300030003c0340181e015001d540c2224540c51510741e601e81c1110040da0482060b02c51603400c1800e50302065089803650880c00c2410019440101400e200d40007080c45007040180803085841c4040b10400060741d00080442c1190b10f50140001c00741c480361105009000f007000b020480d0b6080801502c03200c009481300c04500c0c1050f032079011440001c0441a401d0340a1342c41016802901e500300c440c0070035410342098554041d040c0c0c070503401900041c0603101c80002640c950601d403140c000144108140b1400c0380020807450101c818961800c04002130840344002c0450311600458400b2a46580c01041040c00d892038003d814080c0c3e9422840052500d50762403020703156441050b00000e001e0780540308503000d85604440940c038100907a101e003083c40c000d1050883d00541c00640e00c4d050784000401405e1309480c1403000a00d01e00305130080040400f812074001d418400c0b640650724400d0b4201242c1d0f50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 204927365 1250 204926115 204926119
    0xe0307030203030a20060c030601030c0305060f0105160204050106110d03022b142a0c0a06150306050f0609060102010e0a0605090f070305280308040204090809031501140303120105 79
    0xd12a000507004122030041c1d00400f8850b20521b0181f0162140c04405140b0851081c2d0713040103408050075040f400d0302c030140c0c0c0154220111650855055104200400301c2c40700c10b551149843d0096800320b000c45500341d100c030000580300500305200720b00c140001c000112881c0303410350030801c00194002240d500141c80300940c0c40f10100c20004540d940d00a031200e000005c8071495a46031604014a110303600034110fa12611815004001c0030110009880e00103841e60024113581500395240e0000700b058400006241d80800000000108a07015441c41880d03001c80d160185d040c00710500c1920140600600c0c103590411641050b0341078005601030200b0b0704240081a280c868503441170030088813803001da00070b0164420110034002d0000b000e402051010310002d003502414100c00b241c2004198000380054880c3d008100946066000b400b5540e02070300460340b170540082d00181c0341149602e50341d0b56200c92078004001c0070000c0411195004415406903140c6070601d40b0030700340c9030f20500442e4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 204928615 1250 204927365 204927377
    0x5071505090d021804060b01080108070602071814010909020109050405040201080a0b0a05130504110a03020612250c200d0b0408070b0f04210912031403010906060e0307030203030a 79
    0x1500f5940c1341139406404119601c0e484c901e80c2044c0c24105c0c041c01d2400042d0380460f03201d1000150748080040c02d00100c42980e40980b11031810300c05d1401625814203109084203440d001d02d20b51600404209900802c0e1a010004800f0003510024240d0450303a030110f40702d10304e8441004003503604280b6441d0f00050388280050345841201c0002e2003000641c20081c1c02100c000203100e12403070709030700171801140140226242c041e540002c0000801450100135003200c82801441c400c12040c2410540102100d40c048001d01490070103400e903951980c24450025100ba40d010092082c7d60030138441c100411810707a4025202a000f054070740c0c2c1402d4000380034521020000d003d1080403000e41d9509540f00d04041051b00b409034000c01c41c0c1c6020780742a00d0040035443c800c089420300d003e07103504100c21603e521001c4d51038002c003629140c03140141078082c0200e1170341d0000f501c4c0200c00118041c0150040014109007019001402c0712020340115000340e02402060016030740c004291000364116103880c07 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 204929865 1250 204928615 204928639
    0x21216030e1318020a0803031308030901091704060f18121505040b16030b010f03110702090a06060201180206040312090b0c030901080a051308220b070507150509 71
    0x1248184011001c0c00318690f1400180c41c1a07500801002d2000780e008664420304152201c0d000b5441e80b1041d1544440803074440d40310000568114081e41d84500712400000d00060700361226074407280c0d400c25000e04024002000d1000030b411100d03983e038441c02858140902100d043c1d400100c021180111004070f04004600c1c41045001401c0d82c9a651a0441c180400e0919241404a509040d070f0ba40c5200b0b0175491a0907400b41c0303e0b208142044405030343c0ca10884000c00003c0d0000c0c503444210402c050310401c4a000507858800141d805141603a80001d2181d240507402800c40d95840c2080c0c040c4460517a0001c0560380d14020f4409494001000720500c6040c00e00940d45414950b10546406001207240011560044050001c0749401c0c3c0b81c1608941d03441d944041144c4040b6070307403e0441e01d03850148001c28450f002038017003e01502080707074030744a10321411070314031880c0d0b8070034041c1d50400180407040110a111100041c4112502c07508842d60004019005028038900c0500443c017403801 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 204931115 1250 204929865 204929869
    0x601140405060f07050105130b040b04030306090e060a0e0a020a030602090303070f05010905010b090c120903090a0807150f020601061b0804090c0e060f070212150c0a021216030e 78
    0x480c0d00400780100460782d100c640980240c0d807600702e60b10540d04d55282c00c002a20041c81016081c0107260b00400c50302d0165142d68840c041d81c50090002d50826540752000300b000c40310740c454403480c206c03000000c100320b02d0480c0b1080e0941d90404501c0601d50840115940181c4901034180c007541d1380240c2c05030b220750b0543c02107482c1d0302034410040c01c110754640c00c11043c0481075002d034421600a00c004d0009410102c203101622100ba00d0083c010002042140908041c032241d050300a20303558103513444c005420f40090300c200103603085030055070010711003000400302d011101004a403407814506245489490069103440c4144201c0c0c040c8a00100003d00403820b031000910b038540d00069140c0c5841e101e00402d4014045140d000003c28520400003025140c0842520b8011030b80046840ca03041c084d600f4802c1380c0b94a01260103840c803030703854802c00000c1c8240340c90f88115448446162034120300f41d402490030518094600100c5420450b15540c40c00101c8007a401c01d40604120100b0a800c5d80 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 204932365 1250 204931115 204931117
    0x191a070f0e040e280c05090123011202180109090c0c02120705030d110f01060302060301090f0b0303040902071208100e070c0b010b040609080601080613020a0801061509150206060114 80
    0x81c00220002d1000101035040d01c041c2c0c0e03e0000c0500500b2a001c2c12034603842071000b500801e0094244004890060301ca42703403100c031b2404418400c1850045086031709600307000e040ea0000c0002c0e507480d0301007148281155900491a500030004001c0031300020118600107480b00000b014041d02511004060b100c19200c200408001448041d0440d110301c541158001d007044a81c0c101d08400780100790000c807180340c05005840c02d480d00180240c0c6503910f0b001c2c0c1c000c0103080000d004e190083d200c403543c11941d503040c40504000c1810904c0913039a0643da1a09072250f0014080301d00500031010305101c181e40c1e1608400c0c003540c03031a1000e90500c0e140c58a0661b810900003000030400400f46001017024846000907004581454a5942d8803079194501d840d00d03420240242c8103194802000102d541d046140c0a840301c1d400600051354240c1c40740c1c005030941b0410780220800442c161900d0200503400180741009180281e042e4940015070344000b51100700242c13000f07040025090904400494040c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 204933615 1250 204932365 204932383
    0x13060c02071a2106010207090507020a080409060e010f0b0a050304150e0f0c060705060604020a051606050402090c09060306010e0f0a0f1e0503060703020c191a070f0e040e 75
    0x98016000003160300e04035506500c030300303c1c0401060704107140e8540e0190810b05580542c005802400201e8100f00440c80103240060182c0111f120701151280072519410003000501040400441c0135420403a02d10090700042e07128203100126040e0801540741160291903d0f800c042c035015680f038071203040c84a000d8001c5282004120f01c1c1810003030f4440000282c40070702c0c240d050103030384000c1e4805040040300e00410b0009407041d0040d1000508920b40b80e8010090b08120f82040c0b41415002490050201c40f01501101d05a44d943c0c184410340c6424a200c1e903118010b11000343c6402c3d000340201c5c605000c05070a07617050010b5012028010358415034034150b41840a400e00d641c040c0d41c0d0343c070851682e42c3e603c501c00581c2c40408202c0018030444051000f69038024004004644820801300c0095010f1403410b1342034096980c256442401183d09102d055004492542c480c0c200110307540041d45000e4080030510210030b010b03c001c0da4209400001e541e20888000030124003a6103107500f0441c01da = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 204934865 1250 204933615 204933629
    0x1107030c141305060a1e030605010608180309180402010c080c01090605061206040206030c071e020301150806150307170d020d0f02030403080705010e0715020d02010513060c0207 78
    0x100c01180001d0340c1c61505014000444046012014495240d400c84074165000ba403c062081014003c103403100154040c031030210819100065503a4440f0803c0790380a0300311200045000c4140b12800507444801106d103101c5d072002c3c5142443c0d62000544074004d40703114201e04818800001c00b568003400005410941203001141d484000071441130090482541c12140c492403c00411461b051400d2407246a0b40a01e00522968a0300e03003c00649402c01804008200c008200000002d5222240500200039410014142c10143c2c4101429121b640541400c15540300e002007004450000354281c00c48290748a5020500350800868105140d68010341c050010404803144103503000504c003e4104070030f60035283c00040d403070300442d004a440c0d05110010b80c0305000620101c0d409500815409125034000584001c0b0f0110a80c1000426070100000c1d100a42c00111080d405002404000c041071000300240d10344650307800301031440c0c103002500c03407903031180c0d00f02603140208007010281800d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 204936115 1250 204934865 204934883
    0xf0316033203190b0f0f13181505090607140c031801090e0106080106120e1903020f032b0908040e010503011821020c0a0303120b01050316110703 64
    0x48200e100303650381c0c41034914403e9508280b80703d05a9100c60b10925001c0c1d10000c0001104404c0c030002c000400700c4010461340e01401d85d5141600745031040c032810110411030710040d01031201605001c45c1c07140d82c031850383c0055424141002400c84001c186561b2040260a050215410b850072041e402e00884d5500c5996100004419800c1c1d000b01c8548441501c00f6a1000d00d40e584401d050300c2d03501d00a2054801040c0c407640140001c0b80070301c401a681400306440040e00401000c5800d282401c4000b80c02e0302d0094000300036050560500c0221030440904004500d000303082880649803240d94601c00c0c0e682042c4640290a0029581000d041a5000081507465075114a402c4505e05000c0c032445200703603e84015003070f6110741c0d5107180c41c0003034020b03100c2c8810345030f40145201c000400049400441c000c02040c0206507a030409800c01031400f95a40c00c104115100d50b09044401c050821b505204081c001c00414a80c02c004030b840b581c40314580001c1b120080d440051515200da0001003007100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 204937365 1250 204936115 204936197
    0x504020d0e060105030a150203061f0305070206060603160e19080d030e0a02101b0c080309032b05070302030c060a0207021905060409022a0c01020f031603 68
    0xc080e04400028a460740665803541d80c1c80041540e903000e0700030000c042840c0c0300e0410101c0d0340c095010350351182c0d0152a144130080c85818168a001c01c03c00100d000c203580b102070100d80ba9040060135404501622014503500300301c4404c100c07001214200b202040804030510b400764807001c444003c07240c1c0f07008058030707a1903c03500c194ad1564111030654001910f48440c046080e100016203d16194028040715505903400d01c04540c1801700004140b11046440b0440e00019101890500100b13881c0d4007441c1c0300c080c804101802c000110219407402c0da48004045098807400020815a003800d040ca2036560400e480d040c1d01358010040c038010b03030340209401c000c4500f410b60010500c0e00d01c2120a002e020181c07446910003d00346004298010000344803d228a05540d0b00803c031071190400741400441d015490313068101d02a08081040da04100e41c0400696010801c0c7c1d1001c1047c034010394200440c129110286411520002d010440264262213040000181d4403566070742008824907100c03 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 204938615 1250 204937365 204937387
    0x3120f0705030315091003080d0207020d05070902130e01080601050103020a020a05010519060602011a040e0f0a080702090609130b130b25020321090102090a0816090b0f010c0804050402 81
    0x40314890340c4078045c0f00b08000156800128468031030a5951200318981003000400711a0025000950200d81200d411704101000c907004110600042050320070250f62042599031350540212241d11040c49030044000601082c280450030301d040d03c83c00e00e00140c60310342141d000c0b03281824520000d0140e5181c0018080c8041d94044a074560b5000c91000303004080d078940c812402c03100c80030144100c44020041c918818a071a4002c404080303100d6007208c4400540f01c900505100f03200004031012240015a40b00310700f05614816400003003114035042c0380c0b800040803031468024510081441380c003400016981000345525281c1e541d000070344109180303403000d070203102000e5a1900340907108546101180c0c0b14400400c80781442d00641c0d5203d410703200343c02c0000010300c020b000c62281e03540a20070304c445500c0d6810503400900182000303200c0c1c071031189a800d80106150300704d0628a42048070344100350b1603686004440920038a04000c5000707043c00c200c440c900864201c070340c3c411300001d4005185 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 204939865 1250 204938615 204938641
    0xb0f060c03181e090604021b0601050a0503060f070305090a080c0309090a0612170903030307092318040c030605090a0506090303040302120d0216031d0f03120f07050303 74
    0x2c1c841100103003200b902c1c1202008080384003141c41da0000d503080c206102c1142070a0141e243c000401030005814051400000c0304483c1414915014990003a40104074510303004401400601c4140c0c05085a4140300000410700503000300400e0a05803100041444800100030100c51130fa0000191038440010100043d120781c4520359803449944600c1c04185080100e10840c000c50707491801c540080005070740d6162640049038a0140030304002d01c00c044882d00d06000070b62160b1480d680d1408418100701c0e803010000d051041d4011030415131824210141c4030171001d2492a11b40c68000e40441d45c49241c00d205021554100800060a100078440b070040c0c00210a24118847c00036500503035610340b0391a0790307800100c4000e801130b17000494400c4094445001411142000480580341c041003441c050000d6a030900c003180040c01071402c1c0d200a144499200c405d0300000c4592a450007000b02c0002e030f64034214080d103081c0c1880002c80006420550f000c50380400d6000042ea522807074000c07184002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 204941115 1250 204939865 204939877
    0x130c050a0e01030201230d1508190c090b01020712060b04091b120209070c140a050d09240302031f03060c030b01020312150a080a05010c0f210b0f060c03 67
    0xc030340213401071060003a4000707840d48a41e00d246c0016040c141c818850740d000e848041402e83c42c81e41250000300e4141d03801c0c007070130609040340200b00c00c88803c10320f0820003c404a07840760403010301e800706940c5180e90110300e00046500681c1c030001c40c840390303080c004002c000d880da000340e1191030040c034442085a041e124001821400e09082e804543e103d1080d4050a4120b00003540f005c607920004144d5401a4100c61215000e0002ca156880c110885540303072101c0244141c40c1640405c2c060310707085501400c0c85010b010150000c4c0c001e1000080781d01d580203190300da98000d058001c800501c3c0106403d00b00d486090307015280e4003065a5030b0402e0320040030707580e450b000020301b0f0400e04082540004201c40135400c4a2030110003039a40e00c5d9203031100c0d450042416910080d051030016400c2410007924061a006800016603000e01000203051204818130300418400c60803090700d82000d400c52f5441c5c0c250507044000c00c407020f0090008034017269600c1440c1c0e0100e070100e00320b21600000400740c01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 204942365 1250 204941115 204941117
    0x80703151407020a110a050f130209090403020303190b0d0b0a180c0306060905070507060b03120a050a0206150120010615120c0305130305090f040501122603130c050a0e01030201 78
    0x1070305c50315105108126a0902501c1d8100c14040603054442c11b002d100f101044600c1c0d00014100401c1000007200020160f0f420f81c01a4004018400d45800050b846840075506100402c0b40c0078138600481c035a07030b90400c80a030862100400044182c2c03c542c005200c2103d11020f0308000c0c4071949002c03601e1503203030701003aa0740b6441c10303501003042c1403644245d9010b406c0b1b90b00c0b038030f0419080f503407240041c200803900c1035018040c3e00390700301d01804454007074902440951255074032203070390800080c40c2c01c0307000300308a030240072156881a5a90b04542c4000324802a000b402c0c80460f070400c04a80984600d40c482c840307400020050182c04d581c041e11b50b4924101c002010b00c010002c48200700c00340d4000360751800d905019054003000280c000d03070050000560103042c012100002c1c200040489009a002d2415600388016200c00c01c040d2080b070841a030340242c0404003018600f80d901906000082001d10a01002583d1a0901c81c1c00901c010050900400303a12415403030b00720300444c12800b072108034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 204943615 1250 204942365 204942383
    0x6050402191d0c04050105090607111801050906030a0818010c052d010603050d0e012c03010b060310031b12110406120f120c0c08010b01020f0601080703151407020a 72
    0x3490320b00c2618120344c110b1350160365850a14000c2000c000d05540412070444d030300022032300500300c2030326000801e440860701045016000c0d0300d4103050000320080105005d210342c00c0201e03510700003111300c0d0a9840b01161030200310b80080da60300050300c996041e04c001908601c200d051000400c42c0317400e1140315080400c00424180400c00055034242d410901009080b50005072000048038406e0125282c0080c3c145000002440c00c0c280308202044035801e9149190388a02d50b4401c181004d00441d038500c8000e0703582920f1480c02e50800d488208841c00010294100b07603007a145001d6034255040003529641c400101421b40c07500d401750701ea05580700b032140540c0c18450002202c00a49101c0c0d8209074011078180e0b0152226920012410310f83d80f030b01d10a11480c1c00c030080200301d00c21400806090428000250484158006454491191030783d070116840f003401404100004140d0100301d980c410b001c8080c20108551540c05040b840d91840300640c0400701f0000c0403507002a41000c2c580c00384e03000c0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 204944865 1250 204943615 204943621
    0x1501030b010816080411060310080706140313020402041a0c070b04033c050109110f0d0803040503160506060906100e0f0f04020c1f020301060c06050402191d 69
    0x640b880c400c100c82c0b02100f000070301c2c070054209004190036540584280403c11032100000c0000d902500305032654807200e055003a003403010840c10024000034010701d091542d200b000140e00c3ea0060b01c801444144610050a04102103443d903030140c50281c68082c2440700e403414610107500054000c0c000a8a00384504c4a0001d0700340314140c00c41c0c098940160518542240400c07084440100c141070181030b1040300e810441103201c803041e604e22810b11880002c20701000505111081c0340150f60180c1c49030490301440c0d00e80c0c0c1c0d1041036400c109540111003680301e5507a4145282140214100a9120b078401401c04080003001b00e24548208003c60b14803843e6264013080c012010000303495200032800f1241040801e10b4144050410313414001d05041c0c01918a60116007a42c0040c0b42500c003e900800f8500c0c5640c0d45800c154100700d00c02c900840c2150b1426000600d104094403000d0715459507040440c041d0744032075288030440d001010100c043c45603500e46034028040400c501d0400d00100342c000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 204946115 1250 204944865 204944867
    0x1605101826030a0b010903120906030b04111b07090501030c0503010507020c030c04090c082e0b01122415020c0301020405100806031e03070c0503030c071a0f031501030b01 75
    0x19620701001102050440d0b0f1500c0b4404001c0c000610414140200d1480001c0010030101e220380400c00340760703180400c10b440c0610150a9070310000704c5600c02d6082c4030310070b852440c1403401c0c0d583d00c00001c4a0440140c0c2900e998a0030300701582c0061003204d0034800080144614420340101701c44003600208915601e458049880b042d00c080000d80c103404c5408001c02d5490f1030b411100d81c0c02d005002c0312407116a1050f92a01c0c2004c1c50034496000c01f404074001d012a06525400c12400d034a011081c00f80480c04c6000814190f02407210340c05150380c4e14030381c2c100c00c60312080d00c442641000c0b03050702050340c40d00c0b802c400d140c0451783c503034006100d042c81400e22800d044c001e5a0440f01c028003022089440030406590344080200030300e40503c941100d01152554207102d8190b07500180c0055541e030052400c001c86801c002c4d42006000303510801c0b015600b000c0000705c7c1d13811118010105034190300701d0b114501e07080c400d69051040000021040c0680c0d0320010310f4100200109807010000401c0b40d0b00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 204947365 1250 204946115 204946163
    0xf010302030f1b091e030609120a03110712090801050c0c12090402130608040210030603150515030a050c090f0106020a080906040302042c030f16051018 67
    0x1903442c0c1d014404008200050902c04881e114040c86800c1c65060001110214000008000341c0e000c0b0b207091001d50f60110300b41803102c01e07000303007055019102c0d082007120000890310501c81d00d1802c042c1c0e03400c106c2055800041c00c2c2c420b42e0343d00c054401c4803c01134081c000e014221034003035040703035501c2d100104a1101c144401c46404c800450083c0c07500031510070000440346c01007000b807a000f0b40c080260001103443c07000c82c40040c005644030300f021070030907005001842624144007028149440000c0c00840c2044080e200d500d0038042d00852a503580361900e403041d040c84005280c042c46901c0f01c1200300040494421041c007800c0d184422540e440807020814003800388141005600006041408204103000410a8100151820f850a50740381e01103012aa40d9000d8a40607a180c1e85002c0c00b0440b0350040414000890703c0210300b081d15601003030244c0c0c40307800401110115142100b0003000006d2100300d0f0070050600cc2000904000c0300c940c2481080034a04840000c1003000070350a101c0212 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 204948615 1250 204947365 204947371
    0x40c08060108070e040203030d021309051e0a05040507031202010c02011803050316030603080307030c17102c01080c01111b040504050c040903020c01030b0a0b070303051b0a0903020f01030203 84
    0x540141015813814540702c40000e0b016106a030940410814402140186c2c00201183e418880000d602d4030300d0440c0384021218007414540c02c0054071004260000d04098420b41c000401e84000681611203242881c5003200641c0014425420001d000c0701d01a010f6000503220a00ca400a0104503d5130300e8625001082000c0200451024400302e00541d0300c0b403003e02a968280d04001441ca900c984a44000d60412039524000070340343c241d40789010f607020b00c10079100181899080d1460515480d42e02c45010035000f40e00c899410203004042e003006180302c0400d0321016602011055840c0d19905403101c00c04000e00740410344103404011340410000c1c14400014002c1d031301c01c0c3ca001c0c0320000c01018250250040d00c40348034502034180385955502c41c44030030300c0c400e070003c1520003242800901034813100d41643e441058410740400503490301500310754840d541803400144e69581d411803074104180000d6031440c1a200890307241103950300007252506070784c0202c400c80190310145004609a100c12 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 204949865 1250 204948615 204948629
    0x60522080703081003080f030a110c0a08090112090b090c03160509130615030b09070b030a0b0a030b010f0f21060905010e15040b07030216030c02010c14010203040c080601 75
    0x10003502000c40c0c419600190800c0500c104a84d01d250341c0c0e02c4034509500310100444409100000780502d040396480364080220710200c0c0307181400c2602c1140d41e107502424001400024000800c040b07a03030f100342c0071b48182c100c8000781000b600405042c417503004e610842d1511920300c00d4800031815403500080001d0981c00c80450340e0441810881030180300b600142803080d415072100704c0f0030001107050080c81c604c92400a02c41090b03928600302089a01400b03089081140c015103014030030780c48240c2c2200d510080c6041e000c24055a2000400c5130001c190b4005444001407000200e051505009008201c541c2d2005005c88a9140c9101c4031107480a83c5c540b003130114a4542ca580080c0310b5420051507a030080c1e00025440000194071410701d1096142821802141c1d810482001142c81905400000914003141824042c111003480c031100d107000617050007000f0720280210ba104084646c903a42d4007584074024072503482143c901079042030700c0441d51950a91b2020130614000102c45040b40e2072 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 204951115 1250 204949865 204949867
    0xa0f0e01120b04110a0b07080309070f0f0506070f0c03140c01050a17091203090a031202040509060105031b04092a053103240b060d05060d020d06052208 67
    0x255500c0741100b0340c0801210f034220300800d0703002031b1842e0000080c200c654000c401c890398a24103050400e0030806180c0002003081842207090001112040401c1d0590307900f0b8801550710481070405480c6851401c400401c0d00f08440b201008202c00c8074204402c0c8240d80007141d504100c3c0800648140c0180d003240700000307078141d002c0310180c40075416460b08070072004d0a0300d200001d201d14645c1c280e80304660b1005907030b025502617010598881d4003100050500030045007440e0400d0001629402d0141070b16042240110206032540065a00ca5000107481680180d4580d503c0754044058140c80c5030784840103105078403100034000c0a048251800056556140c540038418038030311140c2c40600d8010142c00d05241c0e40c07069906201841d000918020315034000440c07111640301e0a840106107d40f00c1d20782c20305540600c0741d00d48105807111400017800200d40d030b5580301d002c035802051000c000307035203c02e1028100c000d0000c02c0d03005901030071706404a40b1085c503080501c00700c03005442030020940700c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 204952365 1250 204951115 204951121
    0x8060609040305070b04031e05030c120c1204053a1b0b011d0106020d08070f03020c0316021003020a0c021306170106060206060d12030504110a0f0e01120b 68
    0x98001540c0d0341c4184281005401c040a685944000200c100c40807008520552082c4134440f01c200348298a09a081c40c0080c51846c000381e240b5218040c28243e0700c003c00c8034802144d02210260241c40c6981c161034400e0182d847d16043c520358800c150764012000450300e40c24401c01c1c1e04e00c80c50030350040c0c441c1e0808020115901e4070403100c12a03000715102c0d0007402d04840c10001074607040aa4000d14003400906124498030304040c811200c1a0b1001d41950300190041d5006504800c0140d4450454103105c018085102000d40180c81400f05500c001d0000040c8034204000d01502012054004c1d07851745038500c511002a401c82c410707844100c0224400704401d800514140005082100101c0c8004c1040350340c030100c1503948030b411483c02046035100c42003032003490390421030107500180c1150100d0343c03280c1d1900c900c120036820001e030404041d1110000380c10f0002410911509800140000501c0c0359108005414540c0502800301c4e02c4070013000014000c10031500c583d80e819004004510103031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 204953615 1250 204952365 204952369
    0x5070305070b0c0408070609091103040201020a0807030c12050705010b0301180b0c04030c06021e01090206030a020c1608030a031808030f0a060905040606090507020a0503040b090f0406121b080606 86
    0x1c02400c0c0206013003002060108060103050003c00241d1651222281001c000105452070390038151400e000c144104000340c2e0f4005001c2c0c0c0115000140ca07990b6442131b00381140c806441c0b810243c200300d54006440f10196004c001060f105018a00811244c2c00c0d210425080c0c0b042e101c803840000500290250126054010498008000c1c8001c903142c00c1d901d079912100c180c0c85500403c056000b20030210b00852004020101c03020781c8600811130303100c856000400d45e001c0a8010401b6a50205030b400201004004000924016024000c185070382c8803070841d503a038410b010b10340000b8140f00d04050100050090110080d600c661004e04660b588804440c49990040c82c41c0301c450b40b1420001902120361140a0007a8064100454100d052000d00c0d025940040c207884115401054020b001c10404010b4900f900c4114002c5503031601004001010134407183c05c055842446d101000610302d100035042840c45100e260040605040c4900d885c41c02040c6129206807900800300080340c0e4 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 204954865 1250 204953615 204953633
    0x30206071202091003090b0115140a020a0f0c050111010516210618380f090a051b0a1707031e050105090112080d0c170f15010507030507 60
    0x3481c01c540107043c00700304800155010042c000d40c602099a48030014180b21900403403601401d1640e40100255034035220083c003011603848860084400441c0c0c115400d0b03c00d20160901c1074100e07046000d0004c3e0b0381080003c0110501c076050105100308428520160107004541c400e58408403640c4070321025803825142e0780740d084500304150300710160941c00040d50b4810000a00003912840c03113440e0820b80420110381344208170900d81401d0b45a203540d484c0c41090415146500120a81c1c060780003100895141e00010041d103502a41c10380c10001d120406502440c4101005800802040300d0b04003040c0c1c0e33a100d0001c004001070495001d0484020b140380106030441070b946000203034085200382c00380090300c0490642c04106c2c0c0719001000f41d03142c521200c0c0d000d84100b10449549071a03a5581c1c540520506000b00700b050303220582202001e0280c00320030403952004042c81e541e841c190b8005010407004456092803a007084080032140d5110740c007917900485c2e040e1640c43c640b04103a215100c00c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 204956115 1250 204954865 204954887
    0x618012a03020f030106050c070603050105091503120d0b0310090c03030309051005090319030203060d1509021002070806010602030702060703031802061303021806100c0312020a0c0506060a0303020607 88
    0x18540c0801c0041080f0604900560003002d240d520b840c1c960030100062400d003d1264400300406080100520542d03488000340b070341001301400300b01588452000820f0414200742000034020301c0100301c8a02d03288460700301c0d88100c2003c40a440045080d035050108660745000c0c081d200c0c5018007810703c000382c001e510003d411401141203032100500710b0b0714001541e404940c0c10840c1d030404070f441d1007042c00300d29000c0310300141d5050a60851400c030001c160500d101c6407002d030003800c070720342500c0720103409602c009005500a00842d22035801c04074003a40c0c90145219083c030301d202c2e141c0000340701440401918100c2c0c0e4001c052070f1500c00c242c2c070120058404030f01314684141120340c81d600165202c0c3c0092208402e109520000e0710310798010015500701e140407000154080b40c0810125a8810800d0794a406241c24040004071603070600700e404140900e68a4201031001800b410440e0700141d12202551040e01200c900e0343c0d4501c00c0c0031603507800d0301c8028056403001d0041031101d070050958443c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 204957365 1250 204956115 204956117
    0x90e160e01120b0a14040c080f0c0703050706020406031e0203070206271c02010606030e19230313060e012a0b010e060f0a031106030a020d0e0618012a 66
    0x240010b040000245013640d241d102c2010b2030444207200030181454010b8222242c0142012010351800c2c04840000280061072004140000100d00c0109401340080c0c81030590800c40440d101ca444c0c1c24064010200341d00300458202403441c003180311050358000c903446039070f0580c00307080545c0304d4140d0459003a01d02409410301003421240690390000401040c100a14a6080702108044462002e400c48413103030031482c00c06042c034000c50f200c10340000340e5416030801110100102482030921820005441c030841402c086d00c2402d102210f5400405811200580d02560126036a51001615495065554035021415400941da5042c0852030000a44c02070904005070030711140e9039003408241c090b0451107640008400780485800c080e0ba441892040a5440703049007403c5451721484a0760151b1682d115100000c0022800c1c0390076010703260918008441440250003140c000e5803600c80850b000c0600c1d01222098800e4050140200b101c001c481c0c03030008407400710510a5004000c0035a9a0130 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 204958615 1250 204957365 204957371
    0x301080d180e0a09030806010f1403090102161203050c04050f0d02030708030d020d0b0a18020a02070909061a0405060a090207060213080717070315050a06090c090e160e0112 76
    0x5509807454059a100f48400f01e40082c07900c1d0a85000780000d100030300030038100900e1140302c8182e5900032090300c040200608119840f075846403801400380c418905101c04c082e47c80200d4000304003c4160406042e407054906002566840503860100d001c0c1e0300c6181e612641040d107240460030250300c0e0b114400d00160a58945a41702c48080e1318650103c1c400f40002d03503001a40c90845280c41c03140100940048491a80841ca41084106080c1d11a00e4a80c00140d000450030103050007005501c004101c50441840610359600345080188507054091083d03030000c034513041c807620342442014402c4070001c2c80b6500c5603081a803260700a42200c01e040780c81e150300300315001c94038100580420082010600400085041296a021041d02c0c1002c2040f141c2c0070050510000b058207080b016000c50300341d000941540d0300c0c0c4490003e8500c9500c69040c0b180303010102d030303a000c1c0c0c0040040103490b03450781c0d1044c141d107030315500c40003012001114400051181003441306644c403d000041e0031416030300001c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 204959865 1250 204958615 204958619
    0x100509030c03121b0c0603040311010912171006091e05060706020a140c0703060911091609080705100e06040b04140f040c020606060f0c01020d0515060301080d18 71
    0x82841c140010401600001000c5840781011001c4c000d5001041d4050018101c40452200030800c0d901010340000e0a10800d000884c4003035a003503100240081d0090b41c4032401d040190009400e0541904d244031041041c480040e4840ca46044500300711045540c034845641d1600850b0a40c0054501c401c185202c1050700009244e6500e1003e0117215006090040c0d68010448000c0c140314110140c045110b10b0a00c020000c4240110389501181d400c0a03000c00e1001c0c040c540003107600319998899511038080170510583d1404c03003074014001820360300d0b00600c0540722914140e88036250b1240a5006802c400c008207220f204044101c183c0101805050400c0d40b110b0a04000b034109800c248902c1a034421894414600504841c1640c0b000f61002c021458850030000e4807264000c06a074024040059404111030401007200e5419110100864403030740540c031090082c000079180300c640070014000401141c9080002c03207040303d602c1001030580c040e400505031042031001040c40404100c1c2940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 204961115 1250 204959865 204959869
    0x80702030f03100806160801090902040e06181207020a03060c03150303021c030209030c09060111070909050705010302040e0a050c07020d030203073c0c15020715030506100509030c 79
    0x550b01803070043c0103910700c42c0c1c10910f5192810300c0c0200700c3ea440a02d149a01c0480a40040300306040d1604024046641d01003400403401030181540000042d115260400c0380300407000300d82800000c001c10542d0108400080b0f44c080c64011030034040c3d803003005900100001745440e44488460041428041500e8202e0300c1c0701502c840343d942c41070300982c11485001e03c40240000c6d0702552031034036080860901030002c020a0340c82c012806958041c10203003000c94001c0c0e00900440086c01e81400480355165115207110002c0c1002103c122003502c0740d403401013140d40c001e00030b0320700361440440d43c0c0660341d54624200010301400340c0640c0400c02c081119030050303124525064155406034008680d2003e0724907007150101c030380d40a10031a10001d44e8501e03034580d01802441c250310303180381c241c05ca52141900f000d03c8100816404200c495000b4034038500025000700c0c400c41103070818403046412000900c030035015600125160b035440000b81507901021070082000d05160140034044490704002540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 204962365 1250 204961115 204961117
    0x250b04060f020705030303010f0e0a06090f020a110606090f1306020d06081908340c030210020105011223010c02030c16030c06051e19080105010c0f03080702030f 71
    0x821000205048107168000c0e40411030340c0000c010650045285625191142c1c64040841c055600c6d55621080031500400c010740160b406889021002c115400c8807001e00002984094001c0c80030031241d56008080a40210710035105401c09001000246d4807480390000795400244102c090048414080c00031584078409082100b8141000081c1c00d418510590310342120406000401030001e124480012084030556114031003065034601d9034051131000301840b4601034410011414401ea61b001840b41591410003100d00030380e4240e0982c925050100e09840f4240a1301180c4d4003407000040010b989060403012032100034031400108628441c0d100e095806a410307150050703201140540c2111800d00045140e0030150300c00d140e0540c40d5603940c0c2105102882a4000c0c80008100946080a0707000044fc285840d1545603a90b41d40d4500c0c04200c0d40c01046040b00010300b00c90020641e03500411101d4034450300804801c200b50b105136001c4581c900d00404038401c6000600003aa000802d00c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 204963615 1250 204962365 204962369
    0x3060506040e092404020f030f0d08270604020901061713080d0c08010e060a061209030c0218010603152702090301090c180501051f09051305060306060102030903250b04 74
    0x425041050905e80100f0440e880d00c5140c2c6440b0380c00c56152507010001c00500c0031183c0c400c608018100f542c42c20383e9294500f0409614030642c09502010090034030010442c244528400c4400f0126641c031014215410484003203888601d038004000b18444400340005405028407030010503103030100c15200281554141c990000100326042c0c0103000c2c02591900a6134003840507140790b80000c0c6800802032000b041e07031021103503c541d1004e004040c94820420003d181e030700600002c03244100300b0503200b1040c0c024451400040d183c000c80c4000400348039030032012030341281c0c0d0502d000d505920700700d400003032080843d51000b6402c02c4203400300d88007030052868090040c10b01603101450250810650101c12503074420042c50003005000e160785000038104810a60741c4014003070710003003100380c920900a0b04042e40c012039601001d1079002e001c0d0030461142a0990694501d52203d0005980d68050204402e5041e040411003500286186e00404144101001540b922982d2401003442c80c2e4001e07 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 204964865 1250 204963615 204963673
    0xd2a08010b10050a09030303150806010b1c110f0a1206180b060405150a0302070b270109080f1305040203010b0702030706090b120423010b1003060506040e09 69
    0x1d100c0703503a051070010629030000855080041c50310160340e00003000c03002c2c1c0f40001000d16603152401492442c48000543c054981c1c071040358041d585401c02075602e40c2050680a03540c0c4c9034407520410b02c0c506401458a01e1903441061401d060030400f411000d50030070b03015001000b00620391032122903400c3c010b12006124550960000070f8031103603407805580300103101c40d00401080004100b1a2200d4807044500e00c182c00040351070b0769290004034064811000041c0c16082401c040c09044101c5145101150000c000d020b4505d00460544d10f00340e034034030f4a000c1c041c0b55090010541c2ca5040c880100340e59000d1801e448240e944800c000790803030700300fa000841201d1000c9100c00c2141410495100500704500341003422500e8031004012910403001112448100030380480c04000203a402445182111070b0304110300180c04006a00034041c0c4083c02d4882c800800720302206a0091140c403043c1c1e003000d020741d40342c541000300210142401804104141c1304074903036040110b80003102c0b5603660500c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 204966115 1250 204964865 204964871
    0x70510050a0f0e0604080901112a0118090e0f0a0c03020f030a050a30020c040f1401090e070302030a0b10240c03090f0b0d0f0603020d2a0801 62
    0x45100c245080b50b4030040c003002901d2600e00083c04200c0c0009210303034407580c014215642c40001d07100488201442d1102e007030341d5100d4034581020040c82d50680100000380d00d268030014840c01e0004440001e0740100c550380c41c0038020014001c01b0303025000013580c503aa0300c01700c40540344060355540c81e0503040403094407a10b100200a00c11403414100d000380d0880201c0c002c20a40c2d16a03207038181c951464080c010301030101e050301c8040c20310f408601908000c8030380031041800c2562070400f0b900c4240c80a0304034400d5144c0603203490202420300c5180c803a80c1a50322882c40c030381e082c64400700003001800300349a074030300c5201d90000050f6000c00801d2802da109001d800018104401280140a40d40d00202c0800c80c02d8030541000700b61800414031101010720f0100e06500710307420300b6103a061440d0400241010600e6000c141d04810314000d000258003440208035421202c1080030480780c00d400020b5100803141c00c10300c08180c0102400000c08080101186c003407000c075100f000ca000040d805414a0b0b51 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 204967365 1250 204966115 204966121
    0x1b030501020415020a05030301061b06050702030d0b01020d0e060904020f0c0709111213020414090a0b060301050129040509070909050601030603082a010207060603260703050d0207051005 82
    0x30f4180c001e1a106646400100b904484d5560f4480d00d170f00050154800b00f00c11081d046004041c505a44510b09400c85800c0203103040c1082c00075242d40c803c07441004410305098204d80194800125418490311176075419000421440800007590300184c0003d42c8280c00303109150243c0c440d10001d0039041c00345001484140e01e0502c111054426924107080120010700090000380d40c851155079011508044144200720301d44000b90040151a000600c40c1e902c40081080c18480000c100e007540d40103445d00000360341d440080600b658005d0144c0f59644c2482042240000f03003103603a0050100558480b01d090a45078008038001c020101c4110001440032034003005100028032686401c16420b18041c440700e419910b8042c018441e51480c0040c0c064a0100c0040700d0070101220a001c540e640e009650301c490750b040c0794014103814003096a08140105c0c04002e603c507902c0b4030700329035810b4407180713820010705440c1510580c0280a41050941d020081ca10000300706014a84000690703000c0040c0c0c83c1 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 204968615 1250 204967365 204967379
    0x921010902011202041805090a0b0f011a04050303180123120a0c080714130311150a1704020a150f08011401050712022109010e0126041b0305010204 65
    0x480b00b40c3e00ba400103481000207014000440c48461280b00e0b030090081002e482d0300c04420303c1c080603a407003e032000303c0c4c0b01c05000c210500a0103a5040301c0d0f800c0c181518001c110b0483d004030740724622400d545a40100520380040304ac450300300c44045014104002c45412440d0701941e00d0000403064910b009001801c040c076440e04079000c5d5080302b0070f244204190002282d024128080c0507103154140a42a5030351400112404221400c8080401c0324506031a0b40e4030b0407007052881180c0d21403051f40d41c4034518015001010030365501c05495501c2c0d021000400a84c965401c0001d40142d030005100c98000c24807142101e80420601c00ba955611400006024014041c00041c0c000703499803203000e07044020981c0c0c4401035402c840e401c220320306074480e003819050f0328104003941c042940c1650141d40c3c01e01c5400303403005884a620280c880c5010072844030300454040842102401d59640300300c56070000041e5107138560b54407510034081c200e00901c00106403001003410394000c403056134000a0611140c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 204969865 1250 204968615 204968627
    0x9150e01121b0e0307081618050705030f130c0b0d050703150314010212040f050c0102031c050601171911040e07050c01110744092101090201 62
    0x490901c40c08200889880c1031a0321910a40c11190342040800848040d03d9903090001c00000d202da0822503803041d07003c0200c501d99000c288034150704417807040c50503034070100540180c622803200f980d65180786a540c0b101041c0c2d6504007030010034071103240c1a0810005510070350303540040c00c01c101607103859002941c0d00100740c46004101904050030504081000c000465804050ba64010254030031584400340d49030082c000c407540844040190b00a001c103100c20352044818642c045d60640da0070324243c500580e070340e220f110302c968100c00d240c1d80c0030348040c4002e46c490b6400a00515000d10b40e402c03020004142e0050544408010307134a10480c840d00820148a090628407480400d142020701c2c2050b6013104040c0280010203011000988a41c000400e500444c440c810000c481500e80c903441c18802001e0580400074084280700070b1102900f05040c03c0c003550780040708002424074808810a82040d5002071010329040145400ca924a150281c045201503066100002036480c2444c0001001 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 204971115 1250 204969865 204969887
    0x609050a0e0106030b0c0f13030c051f1418030105041b060212070602130308030a060e180a02010e03032a0c090c1e0c030a020c0103060906080712020109150e01 70
    0x7940c0e141001c10800680382d0250f0f25070000d0f107040705a448080c1c8240c079000038807509801d0301e444244a6008410040d84a85170800d5600030b8a540c400f494111118040301c1020110003004101c004050500e48201c0100502c0c29040204242901a600001090a50307105a400b1130b46441d8800040302655100541c2d90010509403005103000407902106103d280308044000d4100c6800043e4884027984102d10407006650000d0260790300e1070281b0300c01c4000c02e414060545c2d5203500303030302040d00d0442c4240984e044442c40750180540e5400303175005562412048400030380600062144146240d50204149031904003e01852554031000d00000d04200e00b82c1c481d207206d440b0607401d100d0324442c26001c0ea00d42c52049480880703ca406010118410701601040c1d00c00d521000440817a0254041160b1010403820b0b02c0074058651214890815246e29000d0070b11381ea40940f504000034084040c001103294010b04107101200c1e2100c40c0682d50354582650900400c908c4450307c0ea403561703c603c070f01c14 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 204972365 1250 204971115 204971141
    0x50f0714180c03060d0210030f05070804120804060b061812010204030b0c0903011b02160807080312130204090c0f12110402210115021005010f1e0302040609050a 71
    0x18070481c540048800c0300ca02a003003042d854400701c005555074641c15042003004d0b40090006000e95034141004000c0e044c400b11146c201800c02c0c0200755954050060140100d03030100e4000320300079290000f102c1d5008000c209884094460f060700701d040d207401000301030f4202103950282c1c1c510400014040a1865914600c00580c8100410800b00d01100d0243c3e810040246c1c1e210fa458400ba400280984202c070081070000c05c62200a107000c540010308003249103003911008a41541d0303411425224230043c4100000794004110a0110f000c0310b00d070f090352000b0f036030040c6884201c0d681c01103004c440504400300c0da03115070703100207100320651505920010540c8032600f804105066a0f80d2840c03a210b500b90714001c580100303001000340581d801344041d071400c0d0f25800c5050340c1d46084003915100c0c3c683c0c07142c026010b01e01003441d8100240c020641a42e610110841c00717607250246010201e03c0d80049410000c0301c03000040010fa0f21401003000529440304080340c0c41c1000d81c4d00c1d40442e540340c221300c1 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 204973615 1250 204972365 204972379
    0x5010e010b0405060a0c060204170f06090d0507170304030c051c09120305071502040501170402061602120a0309050a05010f080c090f04050109060303030e07120b0a020403050f0714 79
    0x1c42019650200c2d4140e650036070703c0c1c3da11140c0e0303098262001c0000140081016001060108501002c60030540303d0503018003c031100014600d8500340c4501056920030160742003100400f98103800340c4010004203118841c10300708600c00400154150300292012000642040d40d82000d000341042070140300005c1140d08804031075640d2010700390580c6881400ca00c04041031540301418020400da810380d0f0381102103903040300c030100e034280c00a6110340507041c00b0484403428107a00198001080e44580c1c5d0140c005031074500911120a00c0c071002c00c4c0201c0c0d1024030003180c50350701c86051003513501d654465240d00034100d05150400c130b06a10160440d504021105211144c03490b0f00910040e04000c04420803552000c43c040498021000c014000d5041410000006070b0015190312a5003102d0190b50304000c0c0d41403028050703031a02c81030312540500105140302030000c10149038002e90404105040189031650f02d9440d24107010104048141c1900300c04410050120610041c0c00018800c803100 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 204974865 1250 204973615 204973619
    0x5010c08091c120605030303070c05011503021509040e030c010902040c0503041505100504150f0b07121202090d0b040309082e0e011104060306090c0c020f010207170705010305010e01 80
    0x482c0400e80c2c85090a0300700140161920340e00300582e4442409804045d0a0700ea59151640000e4604003403031108403150b61a00340c1400d11307a8404000c00c07007925401441c20000f000e00402c0b071400341e00305241050f840f40d40c510a91817034038400c00c018080e0707108000001c01c840c511030040100700d402c21421401442010010040080c20444103440849440600010261a58580342018005513007150360008e1924411000c0040c40c1120041240d07500091204080d4842c000c1e90164040d900c8020500311181400e60301960103019800440016040010b060036092030014003010304804041d02c2d90f500c6841030100b8140e0014a840242c60001d005085103541140f04c030700c0103140e10b03504005154070300c0f600480d40203240d0814402d081424000703106140346000c0907892584503110313080120749030000c00298094075008010020000d078032003a02a46082d001d015400190030022030450003102d41c08101d2035100b0900846062540c001018041c2c1840c001500b180c3d030603002481e00c42950001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 204976115 1250 204974865 204974893
    0xc06040b1807140405150303160b01051504050607110418030f021b0d0f0f061b110307120318060b0120070b090a030606080a020a15020c0f03120705010c0809 69
    0x45600340c0a0651300083e181d036502418200b1012154a810360600001031442c41d0f204d000400003030154091083d107180c0d66a603008001d02200350300c2c100c040272070050100304401d107001c401411746203000356009007580d525500068121a500850410005000300d1030f1414107070b00000d0103004400038001400106885084180c80807030141d02c1c41d109409501844080201c0c922000c1007003a481a04001c1da40054075012000d8070000040d0b1040506210000080900c204000104040072030702651504400381c64041c1e40207a011040c1d401e00d905c031030441e405101c0304610420418000c40c0000b441c15107001c001062182043d0400138050707100c1194441122020400e2002c51b50300e4441103035110142030105074000400d82c00548954031309071001418680115421461602c22601346200d02d483d09181b000c2182c004403081e00503441007904a0103800e04401314981e5901c004e088942c944d0300441d5241c003a50040608407050f94460501d180d009401c02e40c13203a00401d9540203008041c0c2d072400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 204977365 1250 204976115 204976139
    0x140603100504110409051303030b06120f060a1206060911040803030a0209030f0d03050601090b0a080a05040201030e01060306090209341205011502060705090a1a0c06040b1807 77
    0x3070140304994821030241c2e079009800c101e40040860300d8041c007452500c0c074012295503800328804d03004281004840400c0d0720b842030440b07000309104d10140490b0307201d8181b8001c600000a0a86411149401c40850540c0f1943c0300d080500f0703c100c41c08280d142c103044500c0160b403280421200000403e0200740075504010050341c1d8009100303c001a1503440045c0003038504007064001103498010b403a021002d0cd13925401c0130740324100a0700c0b81d003586503641b04001d00c0e920400320110001024240418040c4402d03030080790b001401403501085485403505010300b1908564000c0700c010380e550041204504101040d95840301003102c3d1050f4000022885035054140d05000e03c4505104041c0340d120f00c2c0c0902840000c0d001403010070021580c40314207801619031090440c00146c40b503c80018002c3d445001114010345024243c0c40201d803a001c0a2030518840c01086981c0200a000364030a07880c0030820903104a01a00e40203e080c20040c40c1d1302500e0008030040c000b650403003441802440e05c494 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 204978615 1250 204977365 204977369
    0xe060406030f02040302040608280f0f050703060608031e0a0504050904060e01150501120507020c010c0309031a06150a0e01052101030827150a02030d0c03020414060310 74
    0x81400b06071034034446403060080c8120340000758820b03c2c0413000715451200007101c042100006499640094284c10010a022007100f0020800034450006c2c8001540100740074115522070002c54101c6503c030394945040e21840d4010b850b0315803000c526a06951040400b0320880c4136102851460040952401010f9205038015240240210700105040164503402950343c1d0804c0b00003006a6581000f900c19090f13540e02c140c500199007101a424410081e11032a03020351480e400602c0c0d03501c64240155078500302200203405104140ea0000301103403007a241c0c0384043d02d111300b55100c1c600e0030750100041107465214403413400d101445124122a00540e44070000c00c000d08019498104400c2c100b101154240c0e0040104a6000000810001510050442180000d00b00800b4020441c2c00182e01c4402d0000e41c2d900c00c04034610034121026400040101d1032161055030310300045608040309032070001c199800001d5001a080180e1014141c00442e105412113089255080c95420780316040d60328 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 204979865 1250 204978615 204978617
    0x30115230c0307020a05091005040b010c020a08060f010602030a050a0332060f0d050601090f0605090f040204230a0e031309090b0708010e040b0a090c0305011505010e060406 76
    0x4200c080030280e4100280020118412440d5a460030903070002030b101e81040100301d00660954202003510303e08014510720411185440c0040c941ca8001044003402c031031900241400000d01d9003002580703401400307e0180070307054001c0c040750400354201c080a41059000ca411500240085551603500c0701c111500100a07141c040781004a04c0c10600200d0303014101c2401c2038590004d5204594080e451482c821201220f603060344000102c10302080e00c05106000700660403010040c03002d01d24a0788403240700c0348600c100142c015100c8010400c0100203445089880100710108070440c0340a0155a010704010031122030101c0141600d000c031004090140b00f81c00381c841d1052058441c00304252000c0c07810303251400c06c00507643c00050008011a00055030303120041800141114002c2409504841c000445040c442c0d4558807110481700d405810612102e855154590104880c2e400300b401071801400005101040016400c4146829600a50600014440b9003501e980e580c800c4d81c04803001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 204981115 1250 204979865 204979877
    0x509070309020d060b06042c06150702190518010e130f0f0f05010612061401050307120501290102060a0b06030703020c07080a1103160b0418180305090a0b030115 71
    0x104c1000a06d90300070368001c200d100d01c0700e003074223001001c03c036880c0030703035500300680480c0c0903100c0d5010702c524403080134200c004040013007240d400142460344409599800a4003a2481c0c6612140011001480c16034507a004109100060208500a11944d038004031040243e41c84040d035961401056188201c0162203c078400c4000814400c4070b18890040e07503841402000301a4807041c0b00030b4104041d80081e070340b0700d240000d521a031604100f1080c2c16554014000c05201d8505030303400300a440d0100c1e04941ca9503c8603902030040c1c0342d220000703000340100c03002081010f0101700024513041c0020706440001e8140580c1044031784a0004a98100c507042c5005641d8210b00441d861030003805a0240300342c0d1188816003014030580c10100c1401210890580e5500d80d0300108011002d40a4001c64480c16000c20040000d42006600e841e0390036412000850380000c01202c0d0024036800100c00d5022a60001e2118240d1500c0700e503a402810b00c40240c1c40c03d5504007201200102c800140030028064 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 204982365 1250 204981115 204981131
    0x3020d0302031b01050108070f03050303130201020f0a03080a1b140904060e19060e010609051c06050711070506070302100c0c081306030c05160314220509070309020d06 74
    0x701c24802c44407540340c40c0b0f19140009250504403402480b00f40318004460003169004194070150802d410b003107940001c010350454507070340940b003010300582c2c1c2c01303c1c1948600500c0040b8503505200c410307000c0340030391950011071600d4035110701034a000002d180300241004992010171504404c5010b954034225583e25142e4400390b0100340245100e812408aa0440d18200601c10100709004964188007030b600380301d0955904243c940390744007801050045044588180203c2c104070028804c450308407031495440d98403135102d0344c0484105445101c0011110017824501150400001000344801d640c0d545c50200c080d10700075156003903400200b2149071160240715030b15118101803019140c005041c1366980341000c003e043c0c18000740c0305401c0824100806407800320b0164054071035003200300c115102203480b10f560445a85a01300c2036150304d0791b410700120510608038400d07803004d002c4002110051a041000708003410b44020010020142401c0940e40142c684194010116034010f902054941c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 204983615 1250 204982365 204982367
    0x6090907120b150d092409120c0c060507050120030a0b1e0603130203121206010906080f2520060c04030f1e060504120207050a06050f1902060702060a0501030c03020d03 74
    0x1b1501d424901c0f042e41c002d04000030f080c0901d034880c035045441419540d80452060600392018816070a000d0013510556078200308560040340203044a45c031030000003920000c1e0700070100300506004413500f194100441081400b6001e4880c0904001d01107070610f094000403411010b4400070016090300509002c00414004c02c1d4241c04045413517402815190030007016003085e0120b411841c00b64040b941c0a001240582d4095144141500e155641e1041143c5d0380194010302080098242840010024401e5018048140600703200d42003c3c1e4800d01c014040035046100500c0b5800700e0905078112000b404288484d0381d046030f0482e5070001d038041c466002c134103203007646410040c0c040c40300d01041c0c60341c041002015881240300340d1154007028035140030104201e944150502a043e00310744100b03000e1010602503c043c0c9400d02c070a00c08546451240b1510a00c441d580c0f09104015a00190621246640500902d540415a01e008200d55855521100c000103540c1c4000307400b07000304645d408141 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 204984865 1250 204983615 204983633
    0x6010f05040e040506060114030c07170c1c030e0c0d0f080f1c0507030b090c0d06051309030207061e030c0512041a0c0a02071406090907120b150d09 65
    0x502c10600e48400d1480d040c201551524001c50340c0c0da00080507021403886058060003a24003d951600d0494104031003580c0e62640b00e1a20080320001460501c64150030302010041b4200caaa200014070058815510024054902400c03403c412a00182c800c03004648070301100000080e00898400041511030618144602c00c0031000c0e040307110009604200c1c0c03882c40c62a5014484601e904110329600c0030002c50481d03014443e40c69000d40c444002c5a564420000074005407002da04000590720340e6a800140040ca0480325400105d03210984071040c1501030081000500890400004a80b42683c0e12100c2070381c00400c4200349a55680900c4403544240305482d035040824a07918014107050600c070010418038000040c40035081c0c800108005030300c005680052600b17800400100c1c3c1030041609201184c855581d400c402c00b4400c030b6802c1e681d075042e41c0c1c0c01801c00781c441c0103403041c0e0000060251010300704000c3c040c21101103a20484402c000032201e080400d18000600c1c00c1e60b500c2c1c04805 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 204986115 1250 204984865 204984869
    0x191a09011d060f0a0503040507090c020c1e030f01050402030c0409080a0810150e030d020705060906030402040b0409230d1202090a080304060e130603080a0c080c0106061d040509030306010f0504 85
    0x4401c08141340705210b8115009500503401401198141d9540310040c01c145c40340030b803400005030000021103030141030040c1c0c1c140031030000c140047c00a40030b150200e07203480d4141d410074000f0b03910ba02c107000030b5040901038503e040d50140d40a12030800c1648580c00c0c0ca00c00d9810990401440000180f800102003000d0006025503507048000c240804000401961001035018030a0180c81280c0d05040d000041c01c008032103000d051703142440042e00420542c0d8000a105a03007041e2220b03008100d9680d50710401c22020701c40e070b100d01d0f00f800c0291078050442141034520b00d02540182d030035900143c0c2200b9548024410b10201503900c20b020000710310b01c032080b5407040c140d611002c100403840641040e030040b40114266100034502d0610718041c4c068070520302c0047e02d0f0180400007140c4452140407190704607030184501520b080c075401210f0742111626800103000408256000c001034009240540084800300c070705101c60f04000003215181c1c8400b40c082418040072040580c09503019000741d80c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 204987365 1250 204986115 204986137
    0x1020903061612150b13090203070314010807050102060f0915040302030a111b010c0f0807110f1f080612010608011a0d030903021c02191a09011d06 65
    0x1030142890114882c0100c20885280049a049252466025580e00c2440c0795020290300d1024618034109154136540d0064018543e901d004078004102800c0c035000840c09685240d81c0051441041248201c640406800c04102c58210340f00400c40d5070380c0002e541e50070501034100000d031902c80a044500d80f0b61141010940407040d1030401007890b4001c0050701d800000d80c1c41e08140c1c000064131580c0c0701d1041881c12122448107515110455108070b0900e11924415400c0790180d60f0070b92030b02c103480d0b04850422102c902110708202c1c0c40703007003104070300b40c0c8468250f891b0000060500c101c142a00202003050080107150b100164560742c07840011008501000020000581c0710f21000c0e0191200c0b581e036072800004154010814200b0f0f01090006681568030240014150b03030800c2103e0840910b99611020b0a13081d00700587d651a0802c9050824801d064400354500300368408000c440540102c1082c1c020300140030300766044511007014400c10f8980106641354a00000d110780102d0300844 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 204988615 1250 204987365 204987373
    0x60c09090a0e15250c06020a050c070306020403020f0a031110031d0a0b0702030a0c0b13080c1501090501210807060c0c15050705190e1003150909050703021201020903 73
    0x40030003030070718800d04d00a410401e42403185114064680c00d400d0510301008002440300400b0101080141c0d02601c500700903498010b20b0983e00320550792421000c0c4d001540c40301e81c0060208114a401030300d403070b0601c40648460541d80e00d10b4075098190b00030000014080e40c03488042024662082d44204c942c024030700307010710fa00304101401e183d03120304569088401540350004900483c0c0004282c495040159582c01074a081c566240d000d980310207003040c82c40c100104054400505544c02401d402c0c0502c10003043c185414801e403182d1038406900c05e9884a2500005000406001c05010304500c06010700801c0f188042c40c0401c5184515034018050900c0e01d040c03049455071124113220614069282c0000700700c070051075801101d100ba02c00342d01040c800c205071040f9201c850003003218555a41450070390003d640c0c002c120200010840303440080d980301c004440c925900e10000001e4000c421081100799000d0340c84550322030250102a00c0345000400c4441000425012505501c0d00a0700391 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 204989865 1250 204988615 204988633
    0x1342050705070e0a090209100509190e030301030b090c040e1e0703021816050a1713021807031503020904032d05030f0a09030206010b09060409020c061602060c09090a0e 74
    0x41002058210006c9104400a20129030f0304420f90b03050000380e81000b040c20702c850721040c0741001d045005140300c0340c1c2e00d07031a0080300c88021414000746000310300a09010301d440c070f010b5003418140104110824031846c0350118000c1c010760000750f00614040854007030000d01003ca0b016601d0508140d1000f5804034041170b0380500205020300e182d00910588a441c0c000b400d1022080d103050050180c0d030400148100a54071054407140300443e0400241d100d8040c460525402040d040340400c2128207016190105000280d60301d07102d503002451482c10900d51150956000a20818000d0805000c0042c01e10229140005480902e0b6004248441d1b0342d036000e00048014006420403103c3c10300a0320303040e001407a003242a00900c0b441c01d0740b65000d440c60340c1c01c00407069121303007083d241c0c40d0700245c051002061010321840108524a420b4006090500d0414102d0042103a503805200440d00024140b211031004c150030f4600011044035003801c2c035030347c0041100090000d801d0403c0180304240c00 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 204991115 1250 204989865 204989881
    0x605031f17010605010f1205070509100c020901080a05071e05031501050307050a0305100507121a030625080604020d09060507031103010b0906030c1342050705070e 72
    0x1c40588200c1000c0203000c4641c0d540015104894038818000219804804010000708141d1045c0e03070103950f40c1041070070710718814089100c0c00c81c3c4625803000f05441c0c404500940c900001054010321000d4010b111400d17a0ba510a9210200e91058159045d6080c1c2c0940c1400d10b50200c00c4041c12003e000c562080c0d03140070111040b10300038400c541c064050792101240c503041203841c110640360408000c00f18075403a01104030041000601c1c0f40200003a5200119400c0090301070984020345042e0105080c20740e220805040040c050101610304041d000e4505010085400302070782c04035242440d0420356075240100d4007038410010800412480c15034003d04001c119405a40614040e9804110680410006001038030080c080e1002c1600b0511460800d07140401c01507074010100d2540e1fa0900080210b10b1011030440d0f000301c40054000801c4000c041c1c00d121891030421461440d0b40004130741c194441c40030f0f50030750341d4410401034001202c1043c070101f0811100105001030311040c3d20320345158 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 204992365 1250 204991115 204991139
    0xc06021b19031b0c1509091d07080114040b090a050319081807050609220c0212070f11060c15011703040e0a02360117100605031f 57
    0xc0300320045031034900f0781c006041e4210348000740da56200b000300d00040d0030312644a01c60f01001594808110009a0224031141a80100344100c402400503000501540d1400303424042d0390342002d841030f8581300642030f80560724911507810035041400c5007050340390480c1281c10700c0220711020344184000a40ca0700a10030071807d0104428042c0c2d1903800030744500080960a920808a011140e48091400c0c4824600070005100ca210010030301420400414021080080c01407480504260b41d03420080070389406000004209501c1b0282c98940340070303030b41e91024003150f500020b0141c0d09000700042064840c1003c07500c90424010407581a4100c6000d9042d20140c02d000d075428810008015262041d40002501c044d252410400c0800f80d0360501050001d4000c1038007004940c0354250011451651104900501c0c918001d0703000350035206400150001d00000c5802c90034001038010014000001400d20041d0740c2c207460859900d0b1192130024901d07d003030fa0640b007070301c0d04c0d1400c0c00a241c5040f24 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 204993615 1250 204992365 204992413
    0x510110f03030103140d0c080903010b0a031a0112150b060c0102120405160303140309120a02010906050c03012102010504150503010509010b0c19020a21050610060c06021b 75
    0x765035002241010403104e84503011b02c080d2002066440c1c041000082881d0b001c0e0254480280000424001420002c0c0403c034540d8030942c0c0810381d0851007644400c030012614058200c1d109010002491540d0740b101908401100ca00b09503650011448a03503600c4003110004265000290748465006141d042d0045c8150b408403040e20490840070003010b00c80140200700c070b400d5203a0780000b90411032680c4441d07100a00400e4580541160340f1020f01c40203010349800306140d0b0001414940134945a01201c402603c0d44031010414401084643d0907001002508000f6141e40110364a003480182ca1501a64001c5012100c1e10038800104940c03010185049a80450b403c0216903601c1c6008112849600c13400400d44e0001c02417a2840310510110740c200d5480601720350200c5a907018540581c48044001c2640c04415282c1541404010408650065183c94400640c00c4c500352003d008000c207401c0c01043c0b10f4020442c029200c0c078118000301600050801d403507060011585059100c0040303 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 204994865 1250 204993615 204993623
    0x10305010b030715051803031603020f0f0a021003150504020a11060a0b0f01051b0319030c11071a120a02090315010e0a0905010b0d06020405040b01050f040510110f03030103 76
    0x10b500c1c0010034040540300c00d04e1240740c43c1c40b01c41c9080c14507007840d1843c004610302d13580c15210801420b003443c042d41e02d00350b465502990147c5096560082d150303080c118054404155540402180350140e42c441e05c4d00c81c01c0410340e043c00295503610400da5004050240d0001c1e40c810310205040c1c11030b641200ca5030b0800380800f0b058030f5650341d41c041c038034085821252040e90020b00c00c100012895010300000d0501d00c079101c80032034a840070300f11803e245a200341e400181198a965000041e40c0e014095140100a2801d00000d10003059440a80c0e03042c00f84214030b1440703800392285500c0007800084401800005100320300918294040801035130210001c2c40c024426414039050304411005201d05030f170f000780c1c1400703065140c55049202030000319400b510306540c0c4807110b415a5540320000c3c0780b56031050b038000d61101c1c030700010001140d012114141c14400d0820071721180b80d850a080f81c0580e04200e502161000b010304049603000b0960813812201e2042425003241d940700000a541201c0c85 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 204996115 1250 204994865 204994873
    0x1002060901140408030606090d062c0303090607050d0b190509010503070612110d05040f0303060603060803030402060c01020408030a120c03060506090d0302120d02040306050108060c070b040614010305010b03 91
    0x4541c4148060ba003003180c0180c4800070900100711989461402449902401020940301c5101a00c03803100f03d41c440201c110480c48080c504520740d2445982ea082d4440d52003015504600d02076028641311070707004184504000f0b00040012105c15180e00c40e0990200c00742c5503a01600128010756041141401071502c00c4880304000910762400155000580f9001d981d41c0c100740200c802080003034501c80b0b03030007406550184084c10580f03005104091195000d0040d08081203442e090140807154160040410181001d078140060b60f40082181c0d006a41034412642c5c4103010600240240a00e81044d007550100044203420103610040c5101d4000c0e059004000d00001e021054040765a64400c0e55080b00b81440400c1203840c1c6040004000c9020f801614603070000006851000d5115104240c42d1640c085010700902c4254400c041c0035000302c00003045142441d203031514540c000c000c0e000700103100500004042140c2500106035002d2008840c001c556140d01c1c04ca4060012140c0242c02442 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 204997365 1250 204996115 204996131
    0x33001051207030308040305090d11011805030a031b17040f0b12010501032003130c0905040506240402030403030b0414010e01140a0810060f0f03050d110109021002060901 75
    0x150540c8500c40d0408590010001d440c5584d0741904c4042004000340d0600405002c4102c42d502c0d0081c28040c1984501743d202507000c04100050043c1030310f4101e80080040100040c400b540b40000e291083d10f03003505103400f5000500080c0c1010000180c00100002c42120071800c003403445034007070002c1e218540d4a0007061620307a00030b00c01601806040d0462001c0181c010002075001e94072600503000602c49400b03510b140449802100e03840bd0ba540d0806030817081c0250240401e01c900c5d04060898180300b070101d0300701768030360ba0780d10708010b040c8803422501c5020410141c1201004401ca0703d03000741040d5107a26060501800501e081b1071094000d134142105800158100070790303d8181c5103070b08042001c80e420260711a2006110040c9250049542d41c0c0115000000300f0004403841843c10002c149141041c650035040c040d0f90303004042920b4100f01c180005100440c4010350603045180010140034a00081c5014205100b4003039003144003000038070501d607400b0502d80c0c4030342007000007407120103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 204998615 1250 204997365 204997369
    0x9030203060901090c050603090f070807090e0304080d0503070203041d160806010f1103040801020d060503010b010206010602100203100b070302010515010513050409030c0813080616080a090503300105 88
    0x6079210200800b4528104014000c45c60207e000e95000b10519003141c0c0500502c090062400c24035801002c81c952019408100d020b0180c09401d10400360387d0051400d2500d03000d100c6a071603150003032000501034007100040303a50f40f0030020f07600289110703004064454010b40700180e02c50703070580b41c07000c40c0240d011449015034041c019860080c4010782d03680196124050040710b180d415801c0e9581c0714001044000751030542400500740c454404100011658600f908040c00c40d103408680c94107541120004001640c1c01003042110078000311130141e0b983da69003940d0150162190003404a80a0200d066402e041d415440a44a0b1614038024115849280019296400349034455100300c9101a8103002a0170182c2242c2c2e100d5102c1c0c1080c41c1c038041165503c0d88240c104500005c10020700080c1000008000c1281940045d11400d0403c00d03121800c2c0300070b003808402050a0704a0742c039a0640c0c0b04104c0208103d4403407405821002c80a50301c41c001c40031180a88101004204140f24008101e038 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 204999865 1250 204998615 204998621
    0x1e0c0607030b0f010c021201020d33030f2603040c0e06060405041104050303070302150606090f040b0111011803080105031c0f02031306030603060f1505011b02040c09030203060901 79
    0x40c8801480301d01c443c078618004480c03040900360200d030046507640b400da000050034005004040f81301076011400c42000d41e00969034130420100100014a106864510031285036000ca099981206060700a6801420301c80056014502030088411390301400c8100b03040d400c3d010354003a41c03041101032006a0395420380403411b0310035035120b07a2040d0100010000d914040d03001c0c030202c40d81d9080c014242640ca1001a08503008a02d050b400b681080140b110261072200f0040d0380000110342890922890f83d0100b0603288003101400d000d00d66400e81d41945a004a41000140d010480240020705902d140d005540e14480307000c4010480820011801d842c010548c9070408c4007003100d0070104400894104d50641044d4a0403096000030481070404101c04005031000d0001c0340c9000c50080d282d46429030460fa48101504034282c60480d00940840c4c44d0031410003119000d10705090340c2c00c43c2c59240c1c80c407005400c4000354050310344441c1c5042107400c626084122070085081c0c8800e82d803207541903800d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 205001115 1250 204999865 204999881
    0x3111c03140a0c120c030206010e010602030304020d0503121510081501051e070503040f060c030f260f101a0306090411030f061f0617040303021e0c060703 68
    0x114441d225040c080404040150900c41c140b4904040350503da80c8480e010b840030032210f080050303000c2010350309060f01000214010207030480408429803610328000d4480c00043d00c000d22403125001800203204040040da1381103101503844000d40e0a002c0605654014000b03602c5d40510b03207060107414060f010314010b9100f50488001d0249101e000300044400758000c1c0c003016040e11401e01d6420f840c0c030a08010300b045510800045a54600389580d03106440c000e68040803c006e21a0380402c0000d501034050f1000c03d50f40d040c805003092060300d20411541c0100205000c1080d5041001481070b00075220502a0351044080c424641d19503050000507030a1600c2c15544d0507040001c00c0003800c041c0c2c625070340a802100481500c40c03003540000d0402c111030140151030742c0180103000010040c0d0200d180301203040590900d00900c3c4c404c002d0701c4103050107800e01c51000b20b2000101494000c0e0112242d07a5a45a803403042c01040044080054101910025292103030000240c10140640b1070001c5e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 205002365 1250 205001115 205001117
    0x12050a05120903040e0f090105150609010807020c06070501021c110f0307030b09150102011d0d0e12150a05010911070b0403031d010b01020606190e070e0a03111c03 72
    0x450070390110446038219001400400d803c0c0300c10003000511101c0310401a0281c003034180d402106d42400845142075174000350500207640c901440c0d0010304c0c0d0301c1500303d482940e400c0c01c0c2008030b540d4600c4240c0c20b042e170b01110150040e10008042007000819402800e40b0140a904802c035800402e41c1101114040380c80ca02880108004000f00d400c100409103600802d24500850032240c0e241c04242e180c0400d54001f144000a400c41564640c0c080c0650b20091100b0040c4005280c6141501c070342e01c100b06d5281209019450041440c1500c65840520710b400800c0100c900d041c2640110700c009410444100c81101d10302000440c0987c480d0144105035040f00c404581061207540764170b50b8208000d04202d05140d5140114906032003026403500860b050140009008502040068207000c2d004003c988610308100ca021a040d02989e002405c0c2d031450203028465a60b40801901c0d651898440d581d8010104900003080210303d03165081480c03420f8030005001602580c21684084800c10014 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 205003615 1250 205002365 205002367
    0x7030c1d01061101090204020d0f1a01020c0105070302010b15070b090f030d05190f05070f0c080d23040b01090608010c1e0903060906020d1401060c08090a090507030912050a05 77
    0x10340d0f07100700c600540506480000140007a4164005022a0b018041958020703444004082085503507109401102c01c141031100e00d00070075200002d44031020783d100f481c141700d00421584240361003548510100e40c0d0180c0f4203c0e800c0e49659400303c40f81c100ca902242c100424034006a003121000c600e140c500004e210055092000390407001002c0c0400400d03140602c00c10300000d0901a445002e0340d000c40584070800202810300c00302c001c0802000303e502000344104095904002050203044500c0c800c800d0800090030700300641c2c4003149000c800c03041000698030034140f10a020b060074590741241c5000008200e02a81c4000b00c500f070b03440f0441c3c1d150104c1c000754120840846c41041e164610001454094031240d121742c0e0f82c03011521400000d441d8164003241c054801a01303880703204400e40601d400e5500070740c50070360024011714450320010160103022038811902c0d221462000040c01c00003609118030b1500c034500900404c54604240c0e0800103e00a01c0105402081150348001e426901d80d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 205004865 1250 205003615 205003619
    0x4050105180706020a1211010c0908071a070b0604060803070501020c0d090806040b0603070f030b010504110405130207060b1e0112020a0f110f07030b100503060709210209070207030c1d01 82
    0x700d070138086c0f03203420501400401218000c3c1c0400a10481d00e2115803520307600200c60034920030780e02d8000644c1019880141441d4907401ca98901c2c001d07101c4181d44640e5600596440401250140c8455031103c505440081089001c20406401428607201c85100b200d0003030b46c1c406011030350601c9a21820702c7c50340049012030040b41004010b80e900c1032001d0112882c096031140e0485c2c1d00031003a03009403207401d0b61030010300851400b4002e0008690301c45004a0805040c500081d20150b4105299190140d000039030504101c000e401c065107410300240b8010340010b0b00981020410603a5010500289108104854a6840c0d1083d101d50190705d80e2240001d0407003040a0350041407800d0116002c0c403400421b000e4070001044003001540c03151102010300d081c4502d903140b18041d40d1308258469003016080008941c1d00951100850302c2c240e03a644030712401c0d00420348500c0d140d04030181d007004402d81004036003a000181b407000c0300c4c418103c40e818190b48045410840a8580141180354005001 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 205006115 1250 205004865 205004873
    0x705030703090302150a150506090a05130b04020f0c0124050d031404030c0e070906171302100f11010509120a09241101050601141b0604050105180706020a 68
    0x200150503c240112884440d0707200e40d0150350721044402868040d11540101440000d0110040007080b042e6007040c1440450300000b550b680c0180101402019691403641c480300d01d94001925920b009402159904449036521803143d11007003444059609000600c13280e40c00b8130946c1d40c941540c01062201c890304080800840c00880c10082c0c04000b0340401c821080b4030b40500500083d48036001c41b0306642c0c0740942155048000400712010f110034007008025a42d041180490305000b80c506122030342d41c81044456012042007000703504840d8004030810340c1c80c0c001c20360314a141e00310303281d00d000084030001707003800e894086a032070a50b50440c8141da4072009405010741071103401070801c2040c0e641c40726103c002c950403018098107000d0084400d17070b09c1160000c894a110541c0e0078000e001501d0a8000a4018100500b0800300326400241162007401102107401640039502e00359611420300341001400782100391050110883d54048204410600140d218200c9100317030050540c000d01602d1b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 205007365 1250 205006115 205006121
    0x5120606090a0c020a02180f071404090b130c0e010201050123090402030111070b041e110915030a060209041802010f03050a1803021c0201020f1b0703080708041502060705030703 78
    0x1074203c1944143c40302c020040e5211501601088146444d84041e4580320030301e0541482d01901e88010310001d2440d00d6840310500c0116000d48001c0f00c0d02181c00c44132400881c52802030b1118404450b46454042c0070380703560100703222000306c00036402440280d8032800c070414224204140c0c8001c0d84511300c80d050441c10130601050f0b00c1800140002400c60b940c0f10b491429500c0150211401c85000c8100f004001c0740120484490300304000401c015840c554a8041500d910401c061180c254030b000509810741a080a0201d04405810b40d0848a91450484003a4100c0070348036100b141401e00103d1050814100c800000350140e644660500307400740250b0042030040d100c141015240c44103d9400d011400c400a100c230311075070007080f001708502180000380308209618021640108121900310150100395813003415403442071301c084606050110b14110641d40000c00400b00840c0010074030a00b40d000e00221686909a202c2d06160345000300d03110f000488103c00442da0070b00202c4c1006100782c0c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 205008615 1250 205007365 205007381
    0x306230606041e0b03090303100602161215020c0d09080109021008040606030c03080901030f2a090906090501081605030a030c060906050103080a0207080a0210081e0c0405120606090a 80
    0x46903020f806626034040d182c280d80100c1e15942d4a0f4000018001508242c1ea15440107000620192280c40c0120a10b0710a00800b4400c00220203249840201804500e94400b00303100f500300000c5649004950780540c41e0014070002c0340109a003100002824081801002d08440c0e00519640d0107102925040c1c540f8034011380199141a660310b00400014016446140510702074107030705449050610004090b61380d070342c50110301e050030240b070800d56000600042d03144031500703e40070301e484680c41c00c11944200310364043c1c00424100b04c00080c5284440e40081d050710480801e654210307140554100007a1110b128054141d488040e03840082807140e2070156100348a040d001c200c072003035a01ca600032b45200380c2080c2c0305003a001590443e142d0301080450700038051703030020b401d04e0421078000601072090100741805000001c80081c2c80b001c181d001100903d540681c1d0001750381400c9010024940241c0a800d0040c000c81c00d464002c6800082d60a01c0740d81e0052041c3d9613561486904005001c441c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 205009865 1250 205008615 205008659
    0x80106050a152001140406051f03030f0203070503120f06060304210c120210150509041b03170d0f0b091b0906040e040501050f0910020a0e0a030623060604 68
    0x900302d00c0d10072030828095407003c000304905172061410241002802c6450152a001c0e0328071340c1401125075607002410f09000c6035090f0600004292030940c0c144d046200345034005080340000144000c007400700d015018051011915002655542c1000344205071006990103800741d003070034a07461602030200601c200e04580b14581068400700658844a0380c004c900c0074940941c1280e801c01c2c030b5010892048200710444419104241460031000c51210000a0301c0034091301c201d03140750300d240d001201c2c140e0300540e13010003110002d10080b00f8992a0341c01c1580d9031a030f03180c1001d040c0c0d4901800c40c00f40b00c00041000b807090a00d41c8a800d20f6581002484c07402500a010500100d64030365143c00143c40200b40340f0480000b5464035241c52400c4983c010180085076203032405001e24044d0015024804080c070701001aa03581d0410410f440311903d41c0320740c5c0c3c6e100a005802000b00b01d043d0b0005040f945985150321940e500c80314034001c42c0e800841d520b58000311700340810041c0d00b0480344502208200c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 205011115 1250 205009865 205009907
    0x909041b090c0203030f060307060507020405040609080301170c01182c190f021812011103010312171b0a11120415020d1704031b0c080106050a15 64
    0x1554400105031482c512016015030404001c1041c201150403050f1340c420000c0700036000803810031501a120b401002401b0380281e41d240300040800c01d4951215036800e400081268503503035190b00085445e4003046c1280c04500400d001000b02d54042c19402040c54a00307048a070002d4103040406a510a0060607900e4003100f0b5012040b03600803074541d5601a0396020709070101c0032300c0300303069000351090780c1e0708640803510401400751484c1c04444201c0b00c2880171240e154001040c01c00c0360740500324418850b418442d00000010400c60785240d803c07120142c0f41c030390003403006480500d40054030b4100d4040011440c401c110f41031b00c228050046c0407401490410b407900d45568400130b49004040d1101c0f03c6814800101400307035202c0201140082d44041c401814844403d160081401440c908800500c084a0010900301401040e100c59440c8101c3c501d4200341005041001c01c040c2c451007611019480c004011070241801c400401c291003400c100420442c805090485841210072007195803200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 205012365 1250 205011115 205011119
    0x1909060b0d11010912050d260a0c08090a15020a02030d060305030405090c0301060c03050d0204080a03090e0c04030b180a0515070f030204060e0108150a080604170909041b 75
    0xa144010109224002c010301000c2000d01c10003d88680100e0304001381004c0d940040d1000a42c00042c0700c4d08004491030714580700050718210041200340c280718003003c00340c031408011450009034420b03451441155142543e43e03e82032451a100c4848480241c800d4040d90f000c0c0e00142081e400420341c4e11a144100c1b442c00c103c420304c20040f00c986810865098000142c10800791500036503047d00040c1c0541d4261039545800c40140c040c0200340001424040046411284002190f064030000e00884090f40d010340e10f0380c5001803c1c5002c1c1c0c0a016801c0c010080841d10202d90380c803c0d60150396218800011a4071280c075600d20110f0050b950038607d103c0d0142c000c000607030030710001515041d22503240700681407111010307018260400d01e0104041c030502c02040a2075110407204400202820038940c01d442d038038032484a4010030100c0d59080300300d840e00010403540008210b4407a5009080c00c58202c040e082802c019403084a403482ea00c892750b0008a008114854040502c8a111036022181c2c19 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 205013615 1250 205012365 205012369
    0x30d110c0409150207080c010b0a0e4201030c03050129041a0c0c0301050c04090c0e03012306060702060417010f0518060f0f150103090828081909060b 66
    0x82e100c001c045078030510111f030142c001102406a428000421224814031508121034104203102c0140051100c000c810060016040c0c1c4108000315112034030303191780403203800400d000880260300d0301c0a80001d1401808c03103480781c8a4411507069400e000501075105404004003245040c0c1c1c10240c1c00b00c0d0a00704000141ca80c524006024103284001c91706031141038044a03a41043e0f40818110f029074140f10411201c00450f90448081e03c1e00f8074000034095072613250494003031008421480e050742c640564000d1000c1d00c036240f010004182442d20b1850b0780d481041c80401d00078180001d400c030070203101c103001810f40011401d1a6140e407200008000300d0780c0307007900d007615002e0f90a6855010394810002c0c0340d100601007182e01a81e1481c030b141e601e08000b038020428840c01040c166003100c1c4640c002c00180c1c401d401051455401c62805034441c001c0c1c120149202c0d034100c5050b02c1c11400e1081300003000340600d00281c419400c401c60112805204240701018152080040303452564400d003d01e026 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 205014865 1250 205013615 205013617
    0x30a111002032a0703051e0d0e071806150e060c030313020f0402120402060903250609081b061804050a05040507170304140d0203030a0509030d110c04091502 69
    0x6100a481103821a81c0707490903210783c0c10f200e08074541c0c0c566810480507001c82e40010444858800e4404512010b400589070b546041c01750f1100c8a4205045c900d4600c807805000904c00203417802c42d0400c02000780366000107400c0b1503c40c0706060640c0c000410440c0554050901c0942c000e00140145140000d00c54017281581d10440c0c80c800d916000384466020b5083c0070b40842d500441c1650308500e400c0101d0076007032140d180180000d2240400080c41c1d0001d403018400c0d50008a104003444000b070202503202640c48002e402900d0014003c4500000c3c5880001240c10005060345043e0402a04403c240600b0b50f2000c02460021a07042c4500c1d400c5840c0d0740300b07091241e000288000b815040c90300c2c1590a003981e950040f07c0b40c05071400e901068010110840c0e00310f80c000b0484800405507080459a00888a08042d505010100d000c224540d0040000c2483e240d04600380c03910645004800c0d90080e03444100450030b9030040c1d0303003041241800d60040108501599400d00103100c5030010a050f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 205016115 1250 205014865 205014871
    0x3090f060f0912082a01060605030412020d05070f050102090604060c020901230f031c090906050d0807061a031603020f0901030f0f080c0d08010608060301090302030a11100203 77
    0x50209071940080340c2e200306941c0142402500000690410f41c0b00d920a03409220590340211088035007a5030440c86076105010342c540402d0003444030944d10f00010705142c1003203409490b40741450b50f0090f400e0f8030102e00080500850b868147c18140780d030b160b6508102d0202c0c400c41c0e4640d420401203040d0343d20100544002d010503505c9241082441c8148680040f0680c884141988078010b0581e040c010307207800101d002019a40034180c1d5009030002840c0010498041031003100100d07404148580c410500c030180c07000040c0a00c0220b94840c14446030b800683d102400f428014054180011141d4111a003203810480d0600301c10058000002d041c2130030700d1070652940d01307140310400c1141040c4940392940c0d542194442c05540c1b55488925180303030507440c010b00000d4485c4020381008150020740e201034461404690340f01050700c6020342001d0080c00340c20003084200001480703c0c03405001d82c10323046a01d98091400d0030407a10040d6000080500c2110060242d07040c07801a02c0d444d4400b541c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 205017365 1250 205016115 205016117
    0x3070b07091a0406030f050712020c030f031e13050303070c02010c1703070e03010203040c0b090105040e09030409050c0a1d0a05091501030606020f030301050d0804030f05010e01150806010b030403090f06 89
    0x20f500d0b8600900070381150b0b03000a080b0360603800c1c10204a00302d03401c54814240709030700500c0503039a403032007402560541c450301400500081020042c0325920b09990f0400071403440d00c000800b6942c8555010035541c03540343ca0010140e0f882000024940da04c0b51050700794040c4181401151081130340c0c0d030a0340081c1e80c008860700c0100040204050305510000e40050b0481c160000c500c9c50401d6198586d00040d68010141881c00c00a40302d020b43e44642d044034010540420788113103500307016501d59240d601c9071117904030681c1001c020608000c00311044480c00401500d5024240410081407610850452401365100c100d0420008541d03c50100c56071150202801c041c000c0c2c0b0003003002508507240b9070040c0c03045611041c284401e51100100300c81c15640100c0702000c500c0c04510b040785a80c4a25000108211952403140040180540100d4004026038000740104600072482c4100301829108400031503001200400c103d504850007550014001c0c6003280d0110b4480f13108a680d49881c0d40618 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 205018615 1250 205017365 205017367
    0x90403020a060f0c141e0301080a0b10060e0f060d0e010203101401050304150603080406022d0706080402031c110706081e07110712032003070b07091a 66
    0xd01040024890000c080700b043d0010062003102c40002008900310f0f2190381030094000500a03e90030641e00c840c20250300040950740d50f5038483e218036488403201d40085410510b0a0b01050342100001072500a48540d551080d11240c0e00a040203081200501425013150042042c05202d08103401041460415000090303a0703030900c091329034007105059001600d40c207056107205000c0d83e84442101d40040d00025403800d648000300c7d4940c02400701354030080c114140090005182d5402240003681e000d0300481103000c83c1c442c081103c40c0b403e4240c45100160300486820b02c03020780501062600180060204c50342d00d00c10704500c0c0050b42d501d40b050004070b5148440a4400d00040090781c0140c41d691524141358201031114400c82665110302d01e0414003400700061a0611039281e183c1c0c0340d01c65404840b201c3d641c07081100b481200d202c00550000e101542d036a1407600a9250140c9a50f800c17400030351034601e880d1295503206401070720b080d00b005440e410000300c0c8000061110b00c503807410714043d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 205019865 1250 205018615 205018633
    0x902040902070213140c031f0314010e12190e0402040b0910050906040905040311160503120903281b0e130f03052a06040618050a0f0c030209040302 65
    0x8044951291341340d01e4982024000f031850340303402040c1a04401142d00964607901d801c8130b4180e000c030000c6980100514044400024070201c00141c010714810f01c0f000308103111203094000c2d110780014548002004081200d5000203c01641003d00c3c1000303464803405059203c0001020390380950710941c01c501000c103000c1c2d41d503d0101c2c606130041e031003803c040b490000c0043c04117503903000f00c0c81904078069440000400341405080780a903c000104240e40e1180307042080c04c82a0061402081d0180c400c01600d2004504400103c2d00b80300401002090a1103c654141a010125254060110705900041030001d501000810040c582014640254609108184460f040f0080c44081c040820034030305e001080350b00440f40380450f0149041c59541840003028000c4178508040d907904400c01084007030422902050396801107206480503c0515210401c3e18005583e10a002d0315580102d1f00b0b03600003454060300341c88450322030722007242200c3c2d81c2e800082c070019003240c099000d03070880511 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 205021115 1250 205019865 205019869
    0xe1503060903031e07050c01090b07090503030702030715031d0c1003140708041106040e0402190e130213020c16170d030e070e0412082203030b0a09020409020702 71
    0x64990000070040114114502142040089560540c020300d8081c2000081211548240126190001303c1c4d030092102103010314014140e804110740607400184051004196894040129801b5603001001007554500f407650700360680110020708130a050f511911605101e042440141804240e40040c200e00b0302910107100d040684064010100b510302010400c10040e003d000f150485410714020256031b51780e16083e080d41c0e0307030180003903802500403800090311a004410340344518800c0e1090912458640741c10310048440b8001d52031a0291400050f00e4021000508070b12180004c051402c61102c1c1c00041080781d009911030084c5402502100e20a071203491200d100a01c0d014510b1208810000142034a45041540c04000c164846002d1a402c81c410408a8007070300d48552a013046040c185403082c050455100003d02080c11000060107602c2211000b6810304000600200c01c0c2800e59822801859a0740550364465108140031511190038030140002c1c01040000680c0c40100e401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 205022365 1250 205021115 205021123
    0x1009080f03040b0708070f170703021209210705150d0c0207060807050d06080d020a022b03050f07060606090f1403100209030319050901120c17100e1503 67
    0x21100040e80204000c0001c01000000c0b00c03500c0781c0110205864a00c07074542007c00c20303000140a825401011107251115103c1ca0051696500ca0f0302120100b0246c142c8194041c001c03103d22580c44000c0a48410001a01d001e0340820444050b0a0740c15594444001581030101d00015112484000c100b44690010358031640b0b074a4a206d0004140c0e203890010000c004104c01464041008030111703a08807500025000640501000c80c142c480503082e06000a40d00c400561040c4e201c3d20045c1070301d01e266140c03010003442c0c0c112180300030607802d070711070b1000d40f0180c1c0880080031452104000752400b02c0d544d4481c02c03016014030b42e55a10311601d0803007004410708494102d42d2000b540e41501c10325554000803040307102c400d02100562620709407400282140141c1890412010310034021a11a6a0042c0100000942602d401140d145100c07603071800c44500751014000b1030703440103250080200b40000302d584084820101801d0f6a100e5504074001ea0007030343e4070902400d07000301807151807400b40 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 205023615 1250 205022365 205022383
    0x1051311090603061b09060403050a020a050919110f03041124090409020406080709090c0e010506090d02030c040626030c0a030c051006141f171302100908 68
    0x1c900032550700307007140003a494030400381540001040003c0802401402c000680c3c030403020050140751600e69905003140c5400d6400e008034450320504102140910300880c03084e0081c1c4940c1c40600340c0401c00200d100092117112200140e0040903c60307216689810b00045120300c3c8a00e00d0340d081ca464800030320490301001400f80702509111806888180c075101c0070783d00310860846001c1020102d80c00450000c00aa1700010703994043d000b40400c480c030f86a00308003a000e10800c003145d001343c0d403040e46400b01c190a008042d480760040200b0121881c10300d80341c412181c0010180e4010392000d000090032250340754000c084007800c140e072101503100000342404080095401861070005144809038807044101e50040c140441c42110809010040040c18003880c0090f0080060540380c1c488804500054100b5038801c458a6036920080903150b220b0261400080e01c03411040143c5404202100c84c004001003100710f000c00c03510380580d80720544800030aa66454031070751a82480000c5051030044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 205024865 1250 205023615 205023619
    0x1502040b0d06080d0e1908060c0a0807020307030504030b25200a02030601050910030b0f04020f01030e0c01030b030109062a030501030b0604020c01021306020f19020a120c030501051311 81
    0x551010041142c0085e1410500c030030486949421611300e01e14030203091650307040113a05100745002c00c1070503100702e0014140d09005454050150b910140308a90ba88074185004001640501c01000000c02a070540e130781100241b0120f802c0303a880031600d0200c1d0b1104070380200014122640003900c040940c003002052080b0a0090302440119070003080d0341d00030605c610741c010255140040c43d10b0401802800c082d640c0241c440c0814100061a40000c90090300c090344501040c10f90701c242980070784a009002040f01e0098008038017410010342c020500784402c590103540fa42e90803800a00c251050203141c060800224010280c0080d000d503002700c1c000e092005061074500180003091a00d4680ea60284089030050ba03110170301d003c510b02a019044880c20714176105100850411307008203131100c81c51000411903020750840e2214000c2040016006034110342c03070344c0080c0454401d0641460080c0d0280c2d808500003135881c0c1d105401c440040310024a0603034080c01180400101030300e4100341c1007003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 205026115 1250 205024865 205024873
    0x9130c1b0b01030f0311010f1508010c17130213091e0b0103020607081908180c01090504021e04030c0f05040b0f011d0607080301090506041104030f1502040b0d0608 72
    0x40d995010081c10042c04081c00d8484122041d20415119010b051007185220b00288040b0b0001100c4201804030b4110340f038492222904040f0703102c84144528054018559a520a80c444d114002c042102004d040791814120081c100c4025807900c64403400c00d40e408040004000e851802c0071448181e0b0981e16580c4981140240c2e404100e0705001541540d40440740f042d981e007018035221801e03209805a85c4c41e06550b0140303010109421464080c40340b10b1038100301c80121040303103001e03441c0c0b45454103907404920204414005400c09a01038540341ea41003c400c81d447c2101c0d02c01d84c6868000d80d1044590355401c0b4018000b1421030002840145800c2d6002c2c0f160f1001c200004201032565102d0790f0400c02036004104000322800091200ca0b04064180d941c3c0d81c4c03507070610b04500d5009016202510342001c02050b01400c0521540c0c542d6400b80f01a83d0619003141e481450001500000741c60712146840f812000c0421480288020402d4422040e5189490030707200381031350300d6580134803902c0e00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 205027365 1250 205026115 205026167
    0x180803090904030305070e1e181303050304020d051e010c080f0408071a0702010905010e060f0403120b10031d072303120c250f030b070509130c 63
    0x407850701554002e81d040c180811142d4501100700c51380c00c16903e005500c0a00800030308250103e500c6007484032401613403c081c14100f00c0940c812280000c1d240c1e00b41902d802c00350440440e2041004d160098402400411925101e481d030350b141c003003405240e402540e03400401d0b03c2c41c86824802c490440a0600f8032504520b0014410858010010005020f540c80019030724100155a45540004c1e80101103c00c1981001d8200030300801001c0d004440e10b61900200140050000030005c0c0300d1650503041c410541d80340d99007114401800740c84102c88644504d901e03d256034a00544146030240d56a000680305140414081c81181d2500c0882c00c41d001820f00348010143c00803d0410401242001200c440c50f51022070326003144d18184102e00440030801c2c071074401c0013090306c41c1d05080200c08107400d00d6294403d202451003034410708040d4500c14000b00001181c4004440d841426420024288910b41d8042400ca802104101086560700c1010312840343c1c00c910043c5da1500c0c07502003a000b400c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 205028615 1250 205027365 205027369
    0x9150a0e060a0c030905070902091503040f0320150604111305190503010515240a03200a08100f030215070503071e0303110c0c010c021f18080309 64
    0x81c0070300148422900c900c01000380d00d00035048094141e07070003000c44001135170f0769600030002c1d0464050180704900e241c286000488040c42920b0055401c40e03122141013500d503074150364840d042e4450541c2030b500c80003c000300b500240080c00d00484101c4902c403c40c500602000226180f15462440c6818140480c1003004100042001030320000d1b2500d00443c1c00d0504800d580c000c0e01d60120f6030541c00c3c0070030051440d103012144004410150b515401c00060343ea1468104101c9490300d5410301d00610120b424244030b504002c1451528034200c451801c00f200745000c4070350242e81c0711030210708a102441440702c1503c446000820711501140701807070640d030000d4000100d401ca03101100c000072030000144502802142e0075180e002d81d01c1c01441c850b4002c024201540c080007500400e1034005840d59008040040f103203001c107080c0180c1072510740c100c01500c0c4003517041801e9030403100729442d61a040c8149031750150b038620983c031881d040b07a5590030750300e1040d9460781080d0313155042030090703000b00e03 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 205029865 1250 205028615 205028623
    0x411030f0402010c0203100c03020408010b1c0308270c0108060405070e06030405160810050709050a091a04150f050d1a0903131d130b01050607170309150a0e 69
    0x1c55070900e130a00ca40001303400028074103d1102003428245103426200d446040d01640203100b281c4000300248031140c0c5020030000d050000903903c2040448503500000001d02c65100154010760003101c02403000c401d80041902d68410b031617402d5040d4001d8100d01c0c02c07503070840c085581c8880300719000d100f00d04e451f2000030200c0003003500050040002001250411100340140408070340310b51000b803d50344d5981d044958403200c49411701c403130903e48030106115502c501c50301c509444015100c01c03816484c1440e14001000c0e91951080b100000400c40300c1207a98900a150200c620045000c007401d081050707060440750799a010a01c601c2c060000000000c44000f6020702a00350700151000d01d5440a90490452051000328034003a88030400115084c1c4580000104000e00140112096543d05102d40130b207848200d0b0180c0400c0000300100004c0c5004002021010b01ca28001e0001c1c03404620f00c481541c0066403041010f400070815980480b0703000801c0359100d040844140a8a001c00d884940c0b5 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 205031115 1250 205029865 205029871
    0x3060117012d0302031507120e031801052b0606091a0c0a120302120702030c07090515091905060d1203150b07120305011403070e0a060b1201050411030f 67
    0x2c008020341650800c1c02009441100540d00074054a00e0174074103031082c280c000c2d011100b84001c5940c2c49403503242281c00307108107511424444000c40c5881c41885100702040c4030148050f04000041140c0c5228031042c000c119021030340003141441c46144600e1410584007681c110508202102d4002c00c881100302a04050218a010300107640b2001c0e0500e0300e080808151010705008c900c04018240311303501d503005001e00d0038a504500c034192910482281c4900c5010f44019a6501510382440340a001e60310007600b140085044030031090a1002250f605c00c01140e200201062800041c6454001409035a034040805c541e1700011000c581d0701d03100307600c1c608120807081660380c5076040b1404081ca00e40c000a80708208005441c0c64071780c9401c10400d90a1600c2d28002410600000303410220088102d21082008015081c0c2030f0805011103c5803000514640401e6144d540c000341e642c000d44010054401c01d5241c051466043c00d060000781d5000c0c4402454a010802c01c10124100c0d0709013142d0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 205032365 1250 205031115 205031159
    0x207140603010306110405060304080702040606110606101b0305090901090204060c0b0604061205060610090623281404050609120a1e0309051008070807050c120306011701 75
    0x60390303000420017044500981d00007a40100000051005000841000d0400c840c4203c83c207005440d12980100d5032400307480c3c00e03280264448030104079145011201c2030940e07000d5250420340f640749110240c1200c1c40b00a4140d0110f500012060480c0c02c01c481c500d40034082d9104198a82480c000004140020a0b034000d0110054040411f101d0780d42d6400c41c0d0300800c0240c1c101d060410303143c14070300c2e01c510058070b0b02c0b44142e4014400c500e0442c000c01d1210219a02510341c44107695140301580b4a1020307204000000100070003e103080c80a50301180034460340310000008030941030b1040503002d01c0c049400443d400000780000c00c0659a04022030390a448c0a40b40d0320080310865200d149450502180140540000c5108a4004200d070350300303c04842c00f03070780e8810386c4a5403a401d2208002c01e550301d4100203400480000c07002c9004a2940d50070003501d190181c500015a480b2500789140500010854280042806682d6a2000f150301c0b60b0040c440000d802c0e5450a580c00c68000106c0c17140340 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 205033615 1250 205032365 205032371
    0xc120a0c0504260111040e330d02180708090102090a0902070302030d0906020309210d0b120d120b120604110402090415050405130b010501120912030b010207140603010306 75
    0x40070742d0304505200c205642c0c54020b20544a003005c0000b0300d41c20902400802c00183c4001803250890212505012007812543c80e1070400742c004407058421210007501c0d00b12013100800001616036042003014812400c01c5011b813414201001414040c000d024140aa030040c03103000126982c100c000c000f21500b2420059840d411880c059045004228080c48114582558203050007050340003507100300103450980b03441003450b000056481006c201e85920241d0140300000541c86a03500810744060010103840894161441084c0b91004003010741c0c00065100030b02541800040c01190781c003400448034a84d080c82c22a0f20760790380b4080148043c1688600203a003080c0c07500c0b00e904440c103015025105106004088072507404034140d0b441518000c91504002a254846050240f2100c50f8080e0f9000c4840c3d107400300441c1c0c41e050600514004c6540c9419450006502c080c0070b20901c1c0950320042031441803440060704200c107940c0f09100990a800c80404955215000c4032f040d0f0354840800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 205034865 1250 205033615 205033649
    0x10f0908030f0a0e060c010b090c12010302060702010504150c06060e16030f0b0301020c0615090606070f05030d0c030e0d0f1b060b0a060c06060b1809040f06050c120a0c0504 76
    0x4031050300400001c1c0350844000569120300c0407040d084060b001c2012784c3c2c050140e4441c95541d51291181100c0d21800100560052005140030001000e100307005150080c103044c0c580c20801105507822102001040781010003004108490041a000b450108103e81a0349840700503881c0507020308170010b041580d00c03646180c4406450f8806200d500c405002191110030a003a080d95408003507a0340c481410030404003490b82d01d0250740b1a4070030880a06200d0a081c41075070340d6201d1808800b03044959020600c403014208003a84500d00c01240260b50200c0d1800001503800c2c100104030a03104200544001c040c1003003030701f11014cd038041166403000c0c5c191010a051140042210400450340102020700025034550b11103019940180104810009143c0e64a0007000901c07882054454407a503881c441c8d08103142c010040790780640100e0040390544010380c0d43c581103c8003152008520400031400c0e8400b000d070b0f035135401e030301c5404807004028002110b003001d8064091449925540841c1c8448 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 205035971 1106 205034865 205034867
    0x901060f050c07030b0a1a0405040c1406070b0c0c060702030a0206060d020126070f0206010509131b060c150207020906040f0b0618010f0908030f0a 65
    0x340101890305880c16035640c0c0207001a80c540340150000000440c0600401034071600c01c99600044200c3c80400300c61500c070381c4440c118011480c0c101040b000545840c10b000542e182c1d0312000b41e840150b44001003080c4100600244400c544c0e20a2000003090000980f652003070850a40b002540c07061000c80c0c5c0c80c000c3c45100c1c00140d000c0000f140c030500f001d54102c00034900625220741d241d0160300c084005240044100703081d2601800c1040b1000380e106008071801c8100b0b20181080b03500d40800120032220284c501d00805010aa00c4170401c202c020051074905541001c0e00c8200744d0715400501141050401503480d2a04200c01d000e08964a00c200c80300700341c1c02480a28551a44000c0c0320003814400380e03502c00720340d98102d02883c0350340300380103401144c03855214400f000000d0b400061481c08500c0b002014400340c002c050041c12408000da403001c414082d00c0a03211420610 = true := by decide +kernel

theorem cover : BRFrame.Cov 204856115 205035971 := by
  have h0 := BRFrame.cov_init 204856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 204856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 204856115 ≤ n) (h2 : n < 205035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
