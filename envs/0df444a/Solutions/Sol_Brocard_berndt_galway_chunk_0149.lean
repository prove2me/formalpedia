-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0149
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:07:24.592658+00:00
-- url     : https://prove2.me/submissions/69c52807-eb83-422b-960b-40e26094bf36

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 26618710 ≤ n < 26798567 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 26619960 1250 26618710 26618729
    0x30801030311061314070b040b34030804030908031908010b0702030316020f060d0903020c041a21100b0405090307030c060902010513030305030402030c040506010926030c0703030905010504 83
    0x801054452181c1000361001101c260301c40c6d6640000c040a030007002e4401070244560058a03010107064208940c022801a4100c4102140041c4914071200100031100c0b505842c103585c8561300c6184c01d407001030041e0002c03895844080b0762401c01159000800f414a11140d46130026a45e860b242200d00e401003050082d49500244403011070038007034600280c58076000420300d100610046021602030707482801c80301101500ca0381340e80140b40e010418911500c0080d1810803451841400d0102c4084408221f1842801d0409141000c008083c0d5004035041a11058405410112549500a204516805010707070708110021340341c00804001c1d01c48d0710b0713003689800720901100e81e2004014101362100324140030052095001e01c25003d0403500143d4401c1d242d55980c1d043c80e0040520b00320b804c41002c2d11450506080140690303014050804030703804200d241c1344014000a10900b01b102580b0044103520003c0b032031058020300010250102c90007611a200515180c000441d800d200c1d501512040c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 26621210 1250 26619960 26619991
    0x20705100503091203090d02010e07050a030b040f0510060303180602060f0c04030813080606091902090f03010f0c080a0203040b0601260f0a0f020408060103030806031903080103031106 81
    0x90a001e0402164004003a03019558078890786424081c0c103400680b201d0809500c40035000759440c0d0240300b0f00014210395001002e1441c5002d0018001d1003c130300005000303d8000d40450100b1050f56002d644165000007a0b4500030000d0099200821483c481a40080c0401d600d03c40e0301d0710407440c0b60066500741d81c081e244590703c3d284c1d000038400b0041c0480201070410031001012a0480700606040315442c1541020a440e02c0340305031411a029010503c41d40c1c01000b8043c803200800050f44855210b0403000d6183c0c1e800c2c00025450300094032032183c0550a080908519a586912140030015180c039814899242c8034000c130304074082110b0091104039188089109980943d006400a170a11800f500041c2519482e10020600a4440d25401c0c03d5940c1403003140c80c200c1c0100145900141021810249000e22851355084184005000e02400b007011a250b80c03810710418403122110b4140105c004440d00d40100140e00034403007a400160548a410343c89600415030a00820310040074015 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 26622460 1250 26621210 26621239
    0x3031d1c03050a11070905011502011a0f0303040e0112030f0206040305030402043305010207050102010212041101031d06042d030f11010e0703021306030314070f060f0c0f020705 78
    0x2007951101a800084c0954600c000c08804020000240508004840880c0035450300c5922156103902c02580015a4100541408003540d01d65594025007000c8820403588048030011074154495900b0418900201038004030f081c0107046071000c803061003541c500380784100840040f030700c405083d180180061420404038002d80b4158000661000c00b040c0000f05074120702407207502980c114a594014225a50000c010070b40c1c05005130002001d003070000798502a18101030401c202002480203110481c0c481c000c0d015079120b54400101a8000a210300c0c5440c4075282255582c0411102250081d802d01404c1d10307070350b1a110820803842c0403c102501141c5e01554281c0e000010360b030124040041810300303a09894800d02910500801e0702001d011800d040d030040c01610401d00e800c9042c940d082200400010303622013040c0e400c1c8581c01c0c0ca20380d140c00851414000d03018920002410071800c1c000705204c3c0442782da00209684480b41c43c0d015030160350320b9081c0d8545116100e1107500c10001e907a10003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 26623710 1250 26622460 26622467
    0xe0904060911130c0212130605030901020c030403080c0705040b2101090203060123030a081c020405030105070306051815060706020412050a0b01140307030201030b03010207020a03031d1c03 83
    0x440c402c54040b0303280060308020814400744101c0021010740c0300c2c40004070198040c058070b0884900b00c4a002d141c0501101541c209950b1441b4034003c2100010001300100e0080d07042d034181c1c0180000380c80c0d54036642d0510080c41d03040308285803542d000341e20002400d45041d01c10462400b5000e0300c03104007941c001c07803a00404100c1420b03041007035403074001c0c0d0130050740d00740310b8207020305102190005072445481460450712004007440380207600001031030300812001c0050b0358000f83c4a202d00718902e2080014a0301a01841d801a40c2540c200400e0060058040d0031a10555105458091609011603000c0d1804a01a01c1d000404590b00350b907a400350030254001c103c114003a0710050715180d070fa040b22a004d403444400556903904905211001c0001700d079022030061845080d00b61160801d00700294594105100080c18555551000c003031131b803402c1d010b446c02e45400800b102c02d110794a040282ca8a070094941071802010100e04034030600c1d00354030721103c0741c0307000d072402640014564069 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 26624960 1250 26623710 26623721
    0x170901021005091905010203090709050c040e10030503040303080a05090c01090509270304090c1d06070f08120105010f020d12110405130b04140402030309130e1006150e090406 77
    0x381030f030281c2121300c04103070364141440300c50a104e1000143d0364a4200411403d084903908515486400c000500444013403600944083e00c440c603414109580750b440b505081c80440f0360004255010116001045c55089080c007880b03080c0c100340900903a074810302d116840b02402c0000707d0100320311120070b000d13504001d248907500007592514010034030003441007000e144084070042050b9600000b010b100036003490142c0c1d02c04c00e42130f08000d060b1f000c0045181e0388034000c10842038040c06000c81c014003800000d00008d5122504030304032590711541200c03404202002401450b02140710b107080c1c0269140700090091195100d80d1324480407440d510f1311540507200350382280306000c4003448003080e1035840c5011a602ca0000b0040000c151510905020546a400100f0203241c00840d01b003201507103021080392451801140e0b50b034103801c882d181000091200313080a059034451910f50080000c03040d0b00110682c0e4200e1080b0b821504150b104489242c8501c01d041d0f00903980c103012500250058026 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 26626210 1250 26624960 26624971
    0x4080901140301050d150b03031804150b0a0c020102030f0c0c0114030c040611070f06050417010203010501050703030f06030b070c020306160c02130207080f03040b090a02010206061009050901090504170901021005 93
    0x415681103d60020340749d40c010f51646c10100e0907452501c0d0240c03500303218416070610501e0b0b85030780c010300c0c0c40d40040d8940104407a84090143d85404413045a2003030040315000d106036445180c98440805a56544044e00701c10140482c01d410017842c2c00307903040d10507244961310b5804103a10381410311008440e46015840e0112a40c82042008100c200804040ca0003400c1d59a450340d845a190801004640b42c1c243c05090b180e910410041c0440c1c6d0380181114507080d054280840c0320851800035400420740ca610291400c4d07404414031044582c0240c2c8180c2e00c2e80201c045804076260081410440880602c1c050041030342883c80350014240050340100f1001c40720401030500340395440701c458940c0418954a19288004108000c00940e09401030304444503100a058040265001035036513034000d4034080c03180300b0200c0c10b9070950b8801c0a564014103005802c4407207a5035140d14040182c68241c904032101d01029206c0007980c110401a0b031441d210580c020100b00300010080e50051102404 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 26627460 1250 26626210 26626253
    0x4060c0c0b041518080c010305070c0b04050d020c06040e0103020909070305010606020d0f0810030809060c030c0a03080f04030801031203020d0c0e121b040203100e04080901140301050d 81
    0x910607511400b40c002441c800c0003010762000c42003402000b002d0021145502081001c000744488000042e62846046080c00d001070103440c1c1d400282c1e54200600b41c01080407040e281000100035000c101510031020075000c641354940e0b21410801030740654020080300c7c0c2a07101c0100054030f4003030041c581100342c40040c0c030601501c940f540d5003076130120740000025a1026029030081c90740301d9002582a100c614100d00c60741002030350441500814440035205540c0441c024000303a54503000c9420070311903d402c50303541d03100104502ea1908a48582a40400e41c034200246441d81244c0b600b0344581d07416598048168203581c2c1d548144d44100c1440c8041603070901101c0b403515190703c1241c82203129900d91000c100303c80e2007040304040c50b04007000013a8100d81b001d0150141200c952000400b400c860250712903a0f04c10601134060a2907102a1b0030003190b034148014800c100009080744c08080c0d035424064845150034803c41d01c0207125454104900c1001d03040811009440015500c00104 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 26628710 1250 26627460 26627483
    0xf030604170705030a080907060302030403080a0c0201020d0e070504050a090c12110d03050319020f16020f03010204060903051605061b0f030c0d030b0f010f080703181104050a0e0304060c 82
    0x80f01e03140746070403000004e4003081002e03052111201d000c00800005040600d015840c600e09607400512a44018001d1020b00e0745495502420f1170003901581d00169192004000f54041c075028103a44c0d61541c0b045c1d038000d5182c1000724124a0b010b01484501b10713001050403000d90f03e03007000544d51600c40c110a0b2242440c0b03140070400d50341d6100070740c00024043d9036010384900b00f0424090780707100101318410070540f04000c801c20b0003441c1420307554445620103644030702001c10b0000c200c401100072a110b5065100003404282950004420f005507405240bc48089005004a0440c22540c074014164400f00c103100c03901ea41e402c00d00c0c81407400c60030601070700c4818a00c640c601e807854018540300d02c3c5a070030210a503101c07141d244c420f22800c600c00300c4a00b400003e0500c00601060800340f0f0311001c1108004c00108518042c0d000360303100640c244c5600c01d0031000c0b400c2540c07610121310a4988540d080401288001510340120420010300030013031488d0502d070a80c00d0790700e096020001c503280020b10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 26629960 1250 26628710 26628713
    0x20d020405041506271802030402040b0111060105010e030a0c0909140102090f0f0301020723250603020c070e160e0306040b0a050a0902090a0209040b0109060206070315080a060c0207050f0306041707 87
    0x105140c07044846e40200983c036420a44100015a0b880c409400d04004503100b842c2414407002898a04541c000e0130104440c0e5441f5011038140b8609000140c807860f404040055819440d5114035601030158881000d41b0701c50b20a15806c1c4e1080e0341d0155802506006c007003840d031502802c0540e440700011700041c9083e581d80da6442030f0003078102c11525241c1098072040c403035480c1030000c0f02c00c101c01074074202c00c2042d03841e0412a840045003e0501055400f08142814803820004040035005001c215585440e25012224600b440d201050001a2844e10070300b4403401c0000300c090140f40d02c05142290f540e5140c1922004010007480b441a440e00d501421015869080361b590040804030805030ba5603840100784816035146104150402c0b2400500b000142e03804160141c0100b00e40c0b0700070984419004004050103500d4201640038004d1180c010b0400580d075000455050140d02039501c0f0560740d60420944d4026801041d8058100303100090003d01c0f000782103403017003060603103050a0001780e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 26631210 1250 26629960 26629979
    0x17030a050a05091c020909070e01090c020a0506090303070f03020a050313020303040902070c1a070818010c0c06020109060b010306051003050a020f130e01081207022101020d02040504150627 83
    0x541c01130030010a10b4182582401d08043d80d22079800310083c58090320302401040c540c41d05110701c0b05503030360310000e69410920030300c2885011900881190000d040600d50300b80c0726031080d503000002ca4201c00202003414040c0c000c3c0c3c1c91442c001c1d1035190960781c80c190400410512408100c1e814003040201142c41d95480c400b500049002c0e120740303451582024040c03c06070800300d66080651805001440010b0500c800b190344807545181011401d84041e0016038102242c102c001344070f90007002c0b0104100e68150702420106005000c14080080410019804c440450103002d400c0005440442c202e20b0203070300107941040107900d0061402c1c500110000c5203821a188016080825480c200b0143c451101c0f410701402d06035000e4850b0040c241b9501545116900f0020f001c1c100010300721070204403050281c01c00e0b04807107000399524584851150000d511a000c0d481c403591900b0b081400c40300d03d094881c019100a5120580c3c1c0004c40032480703501c01d03800c0e82821441140803c011800030302d17 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 26632460 1250 26631210 26631229
    0x60c0f030a02011a030a0c0302060c010603020a0314010506040e060c0703050d02040f080f030906030424111905090306041b0308070807030906050702030c010813050105010e1017030a050a0509 84
    0x207035503000180b0000c2d403002e603240680c840580a480790740640701c06404100d410a036401125812a2465503600904100e28007520242e072000e584018002000014400c0421107140382c0841c00d8002c02241d660312040000300c0301c41d1081000161703c000b0008181580c401c009120132806070910320708143c041401042a644107822102d15003a000c20100450752042150840035081003000e98106500c0d100403034698000203102030714a4041c5c10410000ba2040841d00344181c1020310140001c3c0000b40e105096984502c40c0200c0c148100048500c080e4407500a580071004014007900c000d403150313200c0c201350b80c0c5c0403030100b02e041c0c3c3ca00400000103280c1070010603000c0d00c1410340e56140c0b842e5050141c0241556070001051201c20422800180d9021449031b003c1340090919901a8440c0ca89640e00c00b1002c1200400720341c42c21001003288615600554400c400c481070840e0f00b20f40741c11010312184030590111505034420700910100070300800240900903c00d10704a070034403000c2c4000999408 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 26633710 1250 26632460 26632477
    0x2090c07020a08030c0d050a030608162103120c03110c070e0606181203040504060b030103060b060f0301060c020d060507120b0604060906050d150e090f010b010806060c0f03 76
    0x280001181011070a003150b00e00000c10100c009141002c2d10405001e03128480c40c42c584082180010b056001d8500030b500c4000681240d03001c5811a018200e82a40782d16010f004181d42002c0c500c1c0340d00006c22030040da443d902545540e443d400c419184049038043d028a500e550145501c1d064100500d4803040c010b8180d1104581c018407105c0d02c0c0540300401008081d0907140034000c208000004250009000720081d08107031048082250b11184850941c091608066405804d01c8070008111490102560590740180010800040008200405486080c1440303d1099040c001000918040e0203103040250010f4800c4070f9030780413582c507102164001c0714643c0200c2e40c0299100c03004d00061185414600302594818030b06401c00a0282102100348600c0d0208900011584090401074205121003049a070304c000e10b95840340d0444070507000440d02840244075035142168515014082e031122520b041c1c4504003261210002d108030360f0700201502225115244141030114420401487c006 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 26634960 1250 26633710 26633731
    0x10209101d010e010c0f0512031303080c0a080103021c0218010306050906040201050d0e010e030a02030712051603030b0613090c0207050102150a05090a0b0106090338060402070209 79
    0xc001600c0c0c03000c1c00041c0108141004610303c50000d090b40c0246019140c285c110710681d009042601c0d145241c40e9041c0c542c2aa08000031040c4007150307042d00d0400405907c41d8651607030550b143c00d00e4411314000c0102510000d0182c10041001d0305003201c01800700c00c21039681c0604501550040b9090000f094024031034040924010010301c4100c0c4900345d085503045004d04203908117500000c05a00820f004040c500d0380e1991a481c82540943c4040d041154403401e40c1e40350300c81114041d4880c1c00441d0f0640e00302d0304228040c11764a04c500200c0f5100312440540150100094038101d008100443d041600b10004100c0624220a00808440217104030303000400e0800070004024180b29255000905560201004041d1107580c002404c2d0301c00c0e240b160000d51035941010261800c84002d6001d020b00d00400000310700f480d441495801920300901030100c3e1035124652490034181071201d8000028014103103c152513000007e21504030310020005400c000840d00002c400610550b0f60000301f = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 26636210 1250 26634960 26634977
    0x1221040302040c03200a0903050a080310240c02040605040905060115260606070209070f0f05040503030a080a06050301060902180102160b09041407050a030609061505070501020910 79
    0x4600d80b074001d02c00c07801c1c80f6240500c151000501100120014401119800c02c000f040f0301485078440c1c07090000840d0440d0403554030b107525040500d955401590407464032222490042410281d40c840407a01c20b80302e007140850100c070031709c00b201c42c6814888201d030f2242c0c5036600010560303103034080c640e200f6010380043c0c905545008a030a9001c0314907a114014031451136240904040030702070f00b2075204144040d00d00d10b540c0d448001080c601c211074000b0740c0300c4c1c03007042400070361544900d180300402010344400b204000c02d4132081e030b030a005078852941d15510400408001038400c40e40070f42c02040c41000818001e44600001e0b09443d081d801c200b183c04d902190480380901d4922040020203400e0000d050741584000b004e03520f40c100c0740900c541d42100040c0c0c01d0126141d90744519281e20200d0801042400d0414000b040d0f540a8060040000e040110100d800d1802d40f0640e011a69003075512200e00c007122900351200e4201e0201511103550030710030b03000c0503251100d40756100805503079110103 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 26637460 1250 26636210 26636213
    0x304090507090b0c150a050c0412020303090303030f0103061401050a0306020c010f020f181e01050a17070f080a050c04090c020a080c060f1b0409092f10020c0306010512210403 77
    0x14858001803803041b9190520060111000e080d90449059465803244007071110b0f41400400e28500c81c00c2001501440004200001c440f1110305250680744117800c140312903403c1444c262400031081c040c1d5680500d00450810000d4903e034000c103c041020300c000708030714880b58101000c9030800c07080d00001003000907904011415000860030500360444410b02c0600329050301c082e0b1200c50802d51814403400084a01c0c2c482d00544001c107905104441c4c90b001407810b07010080c50300400380041e002103020f0b5004a001c0c06428080d49101d290b900300001d003014501900c542c0034265021002d41540034110461011400140050036284480b600a21040c1804003203054154030051858054141c0540d0b2800c141c81020304546c111058100042601021414040d0800d05000307a207400d440c2411507084540c0c41c0c808000880c40700d085032602c0181d00300340e40030390f1034803801c107862540754004200502c540e00d040721046044441c410111381c3c4d10441602d001d10f668014814801010402040400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 26638710 1250 26637460 26637493
    0xf01060602120c0d0f021002130306060b090d0201031112040506010e010506070c05010c020402120703050702010c021b09071e02010501140105070b04020111100c0302120702070501020304090507090b0c 88
    0x5a080c4075402c10580b820301031503141615032041c00e00d1401000504660034961301e108100c40220460000801c6655041904080310941c610b40f1080701c01c80c5c04c051001a03103994000545c0c42c0c3c6c1e14040d01003040c04441ea80110300418000101000e41c400500c2050980311504a1462055120f00001c0c211703541404651203c8050503440346204220401c003a0300058400450302c02101e4003802d18030040541803000a019001d00c06540040a00000030058050350541005002d812907400030401100b80c07450403038807282548141c0e018155226007141ca103003091301c11161721881d946004c140c00141c0206000390341c3c80891090b00145c1d1540f0040c03148160700300403030760b1540e001d003841c40c5010720310b90301c8200c412401400641072107844031040c03280680901203d80d1111b05640204003080004201500a4020a08c1e0a20400074100050a61400000d50000380d94058006500701441c00030084050a001046401000040a00002c011107044041c02c80070b50100040c2103021502c12101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 26639960 1250 26638710 26638723
    0x20906030601030c141309060207060605120307080d0e070e040302060f1501050702040917040311040e071511010501030803070210050c0a05070303061a0912061909060e0f01060602 79
    0x95109030800001000043d001c1c03d008800c681c182d1080b02855460380c0f0003d0740200072000f00c1d841d001d040080c081c080002580c001c194091040004100454860051184a40c001842e40d86a80d10800580000c01c600c13501030111001a40b00c00302d800c461504050303042c00c41c03581c050280301e11280244810941c051040507844045021309085a14111000030440303400c089103d070500c800080c4190540d169a040544880d030441840d00004101112100180c2c3c044d10003a9000c14070301040c0ca10625150040791010103040d0b004062050070700300c10440440700d00f4108010f100f40b07494400650042802103034000c5004003ca25180e241c00b06000c1d04000082c401e64240a15160030490030030090810341d0901611460400c0d11461146000c3d0020079040d048008100d610700c00320007203034a0000041130718110079141914000c1b0f401d01200d554450698043d03050624080350048585000c2c0c3c4000103084c003a18020401c040c0c110009800c0980c0114542083d94469505224003074040261 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 26641210 1250 26639960 26639971
    0x2060106020c010507120e100207050a0602010e0709150320011202090d0b060103060905010806100807120b0c0d020a110c0a0321050f0d0b030601050a0605030a090302100c0206040209 80
    0x142c0034140c0c6000c0000d1151054140c010310f029030140b03024000714407802c0580342200c00580214001500c001002e5591803440c802e07144141e18264020031558818003400203010907044c0100916414030429102030030360a003c0c004c041c54420000030125440035406100d800002c00c108260416510004190b085003400b10811240100841c00581c2c031002c815650f580d40010f14ad9030310f51942d4004802400750740d4003050149040400201d854070010a01c140100711403d4100c40d015074807005183c5500d11480340300d4580d030000c516040401c82020341d199100020240311490962050340c084126003184a94500050b51032410180070b0904114404000c5000c07581103141c2469595021f405070b0b01c808800583d00c2560303901c40e81e442d014074244d501160092007001e407560f000c0584200104007144008ac0310344600d0b0000522414040c074844166200c2d580c81624650b0386200141c083d08800c2011002c6100c2c07851075444240d040d1103080286440c55010380401d09080c010844c3c1c14001421 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 26642460 1250 26641210 26641213
    0x305010e060913110604080f0f010e030406120204050405010e150306090a020d05030702041e0c081302010c030c080a050c010615020309090703061d010e070e060406030216020604090c0206010602 85
    0x80c08055501c007000194009200c0074004910042407810030401c014040003d85c110502282c0440c00302008242108154905400c544901d0317151681c1c503081e5410603002c100d060300f04200c10b200d01072088095444c081b15200c005844c02e40d4602c0842c00329482640800c50701103003070050186d440c440d40c09a6401101c01c500400c01800c100c07541c2c6840703040075003000b88951030406d070b58401c000061040d6886190010004c0007140041149102d4074080080c00801003403815500f60899405544030600417880003129030601d000310303401510000b00c1c0103400c0d01401866440321001a40784402002070544660724640c90700c0d000b00d21142581d03c90b4001000f062842600c000d0007690000c1921849801201c82990700d071a4050190000e040f190410481e8001d94440018222121100981207a2001c0443c5072079a41d039400031a54488541c5049038450001c201c108851032103034000d06050315405161884041c0103038001210341e0710540c402c40900e5290a44225500d40501403e07006202500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 26643710 1250 26642460 26642489
    0xd0312180b06060a090f030506010503060702010603110906030a061e060f0513051008011103040209010509060f04021b0303101e0627050607030e120a0506010e0601020c061801030501 80
    0x50364411407080041a040c0101d402181e2901002d100f40d0881c402010042891440551a804e00c56115102406205c2c020f2045e400031604083c81480b5840c00c0b40c1d0001000c070412449441000280c00022706041d41c103100300502800412064441c1c107050346100e869000b1a0400030b0480c809031a007a0307200c1c000380b03048400c08000c1c58581d90794100c0c0d507080e0070b007001072559607011502c0b00007481500705460945c6000c030404450043c0c9070080d809540216218086681e80d81c0402440742d03000c4450300d804c10100640c065003130070309070040c0c50504040c40154008540e880c00311851a002140d00c1c49003001110300410482c0300c642e003284254050301440d030ad055810550702810401d00c01494400d854103d0300c4d0f040e4032200d5507003000050711000b0810b6541e5141401c004100d40c0580b05403a20031a0203102185618000007102d40030b065111010300801d81c071340b42800b800440c006000c40d05500030410110031550f980b0004225040040b100741c01d00f0329080c0001030032510140c000b000e41c09503a4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 26644960 1250 26643710 26643713
    0xe070512190618051006050604050102030d09050712050703060f05060a03120c06060303030b0306060102030307020d0809071a03010303020f03031e0403020a0206030903090f030109030905010f0207050d031218 91
    0x4a82410440440c2404480e107500c2840c000004114031402445019108810002000808220700e1841010b41c1400c0c40307843c0d181d1041000310310683c8116800340c3e200300700f10b1100720500c1e00030005190242041d075001c20f135126410b040d00e0000c80d40480319500040010300c10050309107c1d02010721841030342000549440c0c00462441c4000c0c0c040680035900682d80480f100e880f4540b100021588607000b4060980d07070b490003502400f544c003001c910a018803c001406544000252445411207038000c1001d10080d2406685c03000d0003074201d44050007012404540c041148101500c0c41c91790303207800c0369a0340c51420002d00345081c0440150282d082001030040780c80f42c01c44003a4948071799803180b11180c0c9541c03406a16200002c10000e4004801008002c80740101101804001e078090742c001174000c092404144c00c882d103600c0001c02082081c07409200c0340d482100340103605055401281c400315140c0740007403091500480c0880001c0c0c008685d4202030f00060041541088903007241d545980c3c140e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 26646210 1250 26644960 26644963
    0x1020904290d0c090c050307021e100f02070206030403020609070e07050405100302190905030d020a15020306011407050a060e1501031e0c0f080d0504030f02040c050f030702010e070512 81
    0x10004a4410200b52076035600744601d40790a08002d08540c24104140803400380d015005400456568000d8000c1d45011071620040840c040004000c200c0501030707000b0340078404c0000b44550002204200d40c24070480c001611074800460046019800400f81840c290100e180303010250781001903604550010f110b541e640007000e030307001d840c0c0450b03042c010905100c00c114002c2c0a00c9441d907000c0c06100780c194a245401106c504241d66040d41610715100304008241c0c0e4900301800018030008135030300b19030070740e81c0320342d01035a0004c1051409a000c0a007040801c2000c0e003150b00c0554654000800310340400410380b00c1c80000091801c00b909107421901c0340100007000520003d040c4d403101c3c1d900541d607810740d0850083c1241d800100c191116803200b4011203000224050078413a80308415410100500510a0364212a8469801c6c428540c0d503a092001070030030388000500b17010091204051008a84c2c2c051072249032240d000141840700000d4030391512489074002030180c0d19030541c0e42c201920 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 26647460 1250 26646210 26646281
    0x8120403060b01030f240b0a120c0504050a030602190e090a0b030718091401020f0f0c03160809010f081909020f0406081005010902040b0304030c030908030c01020904 73
    0x401c00070000705000910700580161558502e41941c1c58940409410204450990030180520681c010a50243c40c0c1a80c4400f43c0b02d000c00c0c40010803030b0600f000404c5040e54102c2c403401050340c40d18a003802d80c1e41010583c0369440c0d8104858054011444082000000311030725036440080c5841c403250408500807610b40030014014160700303a2a11746c48070040c1c5003084104000e0007203a070010a00460301401d84000c092500381213402102c00320303034407003101c6050094405211200e03111500d010070400e102011a48800000c43d168002070020541c1052080880f18029006002469036501d401d000107200302001b031500800e101c01203062002107168140511080711400c038001074600e8040c00010081e2440c0848668800d081210100d108040414840210b41c0ea0384014000340c0d8031481c00c00140c0c01a40908881c160041c000540030038070800b80080014064180543d41caa10307481e40b10306643c40b0b601c4000444e90002b804c1101c60a040c0705102d2440c0181d002c03402a20701d00081440401e1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 26648710 1250 26647460 26647463
    0x8030601030506030127030305010f050f0910090f140a0606080c0714060414071d0c09060d0606090501020c09090a0303020f0c0105010311090c0a092306040306020304060608120403 79
    0x182c0d0b070b9000038802d884c254440c0302c401140208680140c084841214a01074200b80210002400c0000016651308441c5440301035400c02041082000c40c01014000031034002032800c10401540c01000071800c1d4140701c1c40e0200e20600c0c001141c4c0041071002d465442030040c0180c1d13012803400f1400c003c041e034400d030340f0340c0c0151a1010701c99807000d490074000074440d01d255031007003039004c0e00e4140b00810000c0b25900380f02e1980c0070b0a42c0c400da0b645032a1600500d0580c120007040300c1c0341d000010034501c0b10100401030300800170880340c02c03d03040310004030490b00c440c2c005502141040b4400d026960b010003460f80c00403800c0310000c0e01450700700c24a07600ea00d0543c0303001b824035801140034002c1081803410780340ca01032558000c10556940c2d080c0740310046a0b5810490040f1041c0d40482c034095003040854418050301c2c0c82e0000f0007840d00c1e82c4a103c001031010441c1c4aa08800c494030061382ea807400034401107004d014003685030705041c10300030104c9400b58003251890384440150114031441c0403d4404a030b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 26649960 1250 26648710 26648717
    0x9150d060e01061d2703070305030414030c0604050f0307030509060306181006030b04091a0417071b0b0a08040f020112020705030307030c0f32030f0a0b09010308030601 74
    0x858041c145000d4816600020001d01c1035030094183c070400070401c54803540000c0791780b800307040c06418000440c0c000d0400507092034004114940210380030700c2c000e40d0018460010f00202c00301140390b803421500109100c0e060307030b0414030500081c000c0400c1984850704128010303510300041642c004d021131007003c0449004010120001c2c0c40d035900e14103010002581703c041c4001c0c40c5440804511002e60307070b002c0c14001c40c2c600760076920070342003034810102030a510104111070f800794070123003020140004004848202c41c440c06204000f90080103001014410503441da100079040c5d820048205854004400303210041c09080c120561040a03183c0141d000200400300c1d0402d400129002d400700705600340e040d80002103140400a001004510480c160b0b9000c2002483c180740807182800d041c00303007200154512072010410704034803e00380c1800b0190135028480200c0c0b240d0808890300211086840c00c52000d0400092039068080c0709024803080700e03103204540c15507a079600603000c09010079040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 26651210 1250 26649960 26649971
    0x60109060f0309080d05130303050f1014040902060c0106050f03030705151302030d09030204150503032704050907030309081204210f0605180613020105030705041a040509150d06 78
    0x1c0c0210035080700c003503004c00e000034440c6e860031001400341c405c00141d00b100040d140c400012021440080420300601922081c610380b0762030a8182612400c180003840d07031140e0750360b803103800682ea041700a00d40b42c03c40400201c3e196241030104070081040c151900d001c3d17041003041400240c8003185036000e115039204c0c003030b803a0f4484503407449e405801054002c0d014884c0d2869060160b400c40c040008880c82220241311500c1c0c60840c1381c492060602c912901a81305003d40314040218040c5049583d0030f00c0c1c504040402c603e03000400ba51401d54540c1d400f60090070042c000d0641c041c05aa002c2c1ca240700083c08100b45c404d03921216407240f48103e1244441060320003400754034800003c0d00961f00080f003041ca814140c1004001480306548519a0704415641e11030204800b05019106108100341034013aa880703a00103548070351009114108002c8108404a145401d4004494501b0f4540d0256a00c5a0500d41031040786400649885030245103007640c022250350b40c864401404d0b9100780d01044 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 26652460 1250 26651210 26651213
    0x1914010b0306240a0201020d0501090903020705010807020a02040504080405010f020609030d0513050f16050301151503020906030f0405010507111b060c030417011a010f050f12010b090405060109060f0309 89
    0x11100f44030356080211400026500d803125905401502844252007410401c59036a00c0d00602110801d810040142e0440350041083c1e60064601319800662401902d1081413964001400c484045508079440c010114042c803180d40c0c0210313498100300880c0005c00450070800e0803a5a42e021b65444000790b151500d0011b01180310441c1e81140150f4003008848034000f0040d2600c1d00d401845a40c140320102090002540c1d141c14060124a03c51240059002d00d05048499030604045c0a01805050b020000d0450a803100c1c0300461082d01260040e2a480c180b40c074165003522400b401c5030081240b20b039400c031240207001c203c00c090101c0c001858109aa24100402d080d4015a0001201c500010800045c13400109100c40c21690011000304000010b030013902051011060005001902007910090440d003e000280300100c4e400c195141030200c000d142c00030000d8241c00c03a007000c040120300224035050501816400c41c009007010b001080c146000108410080c071110701c20103407250300840 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 26653710 1250 26652460 26652499
    0x5071103010b090c12060109060c03080a060503151b07110d031701060201140105060301080303011e080303070302040314070608071808010e03070c0b0405060a030b0103141914010b0306 81
    0x507030060050704006951a010702051540d405c210480900080c200c40000d80e6588074403021010780d48961510f125204958504540c9280014444610541e481401003020384d0100040700b550702440454445510b461105841510194560904201001c0c0000c40010720800c1d00102080c2054481c0c2103c84203e040464030580c1c0710b0381c40415004800000300303000d54190403003080c41c0440520054180d0381c40d0300307202042c4001d101d150516041400140b20b20703103030f0241c01c40704040e180d0502ca420031b444404c130740d0550b0b01c10394168001c070358000f0702041003003400d0100502084040010301000c9281403000b03800410010004420846030303a010405000c80d080c00307080506400402000b00c41d00700b00e901a43c90b40072800656082013402c4000646030b00003401c40d4180c410240400303042c10b0500c0410350140c00190144c80c185921980184c1d2000c03441103c00b0b108020b6840c00084080c3d4140d0204200c80840002c90f0045154200501c1208100000c4a0304002d0a99000016180b15803c04 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 26654960 1250 26653710 26653721
    0x3020607051e0c0120070e04170301061d030d080105040506060d02040e0402180108071a1b0c010e0301020f04050f0a0b0a030207060c0c050a02150412140c040c0507110301 75
    0x42120702012501da0b00303080060641da121a00380c0307444004090f21081c100c03154844d13511010140e0701070031091140701c440000c1d050304140303d0350289c0b2885800b83c1e04608030750800d8000b080001c1d42e21300d0100304856212100c0410841c2500034080307458921500501041050194034052030320391001c00d0550300c0e00421070301549a600070031500c41e0340341d4942c1e5000c59020740c2e0580c4506d0785800c90800c0c032502c2540e001d040702d0b0890000c110940c5018000c0c4480006100520808035091141c0310062a00c4d01110b01050368100280203600d000c4000500480214103c0700d019a02c1800500c095143c84d2003100d0540c2c0080720074403118034019001071280103154121112505001c0354071000160140c0180060500c40c80c070501640000c0101140c4018007420094030a07448100f00c50054100380e5689514128075080341480c04d03840d0300c0b50a03100d21040008860031030161101400081060280c000034003421203050041810328040141355000b12100507007003110041c10351820355000d5101d03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 26656210 1250 26654960 26654983
    0x12090504060b03041101050c0703030c030216090519020a1b080c01090506070e03011b0503060d05010606090f080d0818010618060e07020c03060a0207050703020307030807030f0203070c0302060705 86
    0x60154a40b80c840881094105a80466542e194006103111540c060415154481881401441d0742413440d201181c034181c64000c01d0b010340c01400740c002e840308100c200b0140130300044000401c1d58100036086600d00e248030808200c94501c10b200c1c0c51035032584403030348183c00c645113500f00310901840c7c1450130300352180e540b40004541ca40100001040030105401c1d1243c20a6102c6203224000c407010716080c0d0b03907600800800044a242c000c000f40b1301a00145400030006031011190445569031315084070300c90b8004070301003050028200a08001c20782203c01400080014042c40400c1c401c1c041c022410250500003d0480080f010030b0001c801d51140c001000344442d1106c0b850794011040006004034092a00d00d00c0040c40002e02039800003648694102c8003400500642d81c0c1d18409800039040303030f942280e46020b40000000940d034200483c0d40a18064800740d580c0f80002c2c07501500d04d0424442d400c06540017400a00e0116045056140841c0e40503910b0076902c10061400350704000c0000d08 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 26657460 1250 26656210 26656219
    0xc01140d06030c0e070201090f02090c07020409030503010911041d090a1b05040608030a0804030516051509010c0906020604020d0c08011a01030b0303070804120c030210020606010e010504050904120905 88
    0x20002c244030602078588115101100e20403555100d4560407400d0b00c1c0d1410000e040115224071000c01820148180c6500c030001d0341d062402d0903015030004050b07514a46003500000d00100c010b010310301c0c00d48208020060358040040c9490301d0901c2c2c04019004240c00c0100d0b100d5180c000448003035050091044580d40100c15903100d0760f103000c095601084502529000343d01e03180c404121044000102c801341256030300c5404080c0c0d11b583d4200c540754400764014052413448501c8100246042000c0b141c6082e030b4050b11480c0d441c10700552400c480311280c143e020403ca910042000f80c3c2c0119202c0c0e08550103660244442c600f5080c001c3d8542c10541c800a103d619081240d0a01c0c0715003081d40d80f40401c00d907030500c5207003074400c10580e0f24018004054600c51040104004460800c20140300d120b210382400d4400c541e582d000103200004450088025030003190810003d5a80000c80075004102424002d060504002c04941510801030004002071641140641c20302d0040ea80d0304000c200040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 26658710 1250 26657460 26657471
    0x141c05011119020601090c20010b0604080106090b03060f0c03070e0d0302060912040b16020301270b070201050f040209060a0509010f18050403020307170702060403060204170a050c01140d 82
    0x404070a40e412000500b180103008507000070031800c00500a9041d0a43d0f50366410f405a100320140803004d012080c1e03210399941d030b40c14803190b0307c3d15540081d00040084200004245180003120010b507088150b50912076000041044402e140c0c85240c1a001958516459181d584020040d21054200c4041e694001c1200d0705500030545e0009800b071040000c0800e4075500d002000900c1840c6c000c60150001040c8248014442005422141e90965000900100d50741450a2a0700c00100a626426100ca50000d52107400d11803c003c45c50f03041b19181c4000c016600e0010300225000c000940300910404110b80424443d030b855804e03820142034003c0c170580d02da50756a424404840028070482e9050036204541040b22450340c8110b6109030b030183c020354a00022540e5110003402a200c40c2c0100c85428880c41015894400c0948003030342c401c00d0016a030341d091201070541c8040e0140e140302d4990122494000013070000c141400d8140c000c3c24507644001d820200900716028030101c3c0e51030103103000b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 26659960 1250 26658710 26658727
    0x10e1803070c090b0a03031b080d0e0d090605120103030e130e030d0e070b0d09030210090c0905090309130c0512041a0105060a05030f280506010801141c050111 70
    0x41045045850f051000c0010101450034071000010510001d00031074561400d0b0311140a20340f4200c44803a201381c14082ca07100d031404180703048400c08004510242c0c45190b00c2c03100c0c96005044c40001d41850b0a0007410700c000b5079680c0709481014040103040290b2074032000039503110724070b0500124009500034000b0020151445640c2d4001c12038031090103003400f400c00152000441c2513000d071015002208c0c50207113016000c101a01062204504500c00c10130f9070a00b01e04a403255414039480780811211180c94030014a007500c802806aa40640081106044a80d41c400c861504c100c140c5a001c607201d5017503203040d03455014981080706568181e100704420401e5841c65484100c800c44a40c0f900750741c039030301401064080d4600401c04602c042010409010701000510340c450503103c01c0720442110081e011521122054082850541f10020b0154968000110502506c001e0200d00c200c8204140010301c011041013411a1520f03040b031905091103829001500c80000c1c2d80d03205680e48111 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 26661210 1250 26659960 26659973
    0xf0d03030c08061012150812030415060b0a110c030a0b0a05010b070f0602030907030f030f110105090304050d0213060308180306040201080a0c0c0b16030b0a0509010e180307 76
    0x215110800240751200011144e1800d03a245000c0301202d652580c085498004901006160602c9800100944110009100c0c201008000020800010500c0d102c1c00d26181902c0c3e624074804640141e0307810b1442c107100100110007524449610752400002c01034010401c58140146500d0700c94140c040c0380001c40901400b0160b140c09000795420422043e07a0340c0c1000481c500070780000500c010185601c407070100d100d6401079138000c08100b060f07416003a581c0e900e240180345843c17000c602180034003c2c1000526000100030303007890800c1009104625014080f9a00d034402c60080354400c0c0c0083e441e0009540b0f88034a44d00c1c0000318240704022880e2607040010312a0000c5826803082850403c46a0a5040125606018540c182c480004545810b03c44c00090168001c0d018204800710010320007080d54518044d0003040e50310781c1c42c1c00d6000202e070300809481f5550146409010712000402040d242c60324032504480d00c1064288040e169904041c100305045510300d403043c4000314410040c03004 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 26662460 1250 26661210 26661221
    0x306010e4317090703020d06020405031b0102060709050a06050f0c030406030e0f07050f0616021003020a0e090408030f060d12090905070c05070302150d09120206060604140409020f0d0303 82
    0x16a200c91148620b00c0e9510410a5003c46005840c1e80081c00200300509000c10b1102c0c01ca4801c0d80054201611500817074504103030b013464410200300c44440368007103503014000580c01a1041c03405e80140c034108030108410881612422081020000e50b1148854440301940c2c0c41c0d002d11010b403941c40d41d0300c1000402034400c02d40e070301405000300e151441a80100240f803001302c0e41c020704102c0c5048225400c00039542c1100c1e00703050108550329004401a42d904071000070949198400603110a5620b0300144a10340d40f204060050141d00c05000101d0806e01c1a240d000c08816440303102e5a1f600742c042410000d1104006203250b9210514200c210380010342e440c00e5641416080099aa07003030340454068600d01400351031030700315420500150a1100c6e000000c031070102807141c64001a101800100d8501d540e040e250108092a050b13901c40c1d06008040d0840001c0310707180c0c1850708100d428061080a11451403003243e40f4051741c0c08540b42c4640703601180e400100700c101e2071355450a001d005005c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 26663710 1250 26662460 26662591
    0x50c0712140607080112060603050115030b07020c01020a151404060606120b010f03090204150801020c060c030c0d05060d0204050406020c0705150702060f07020405090706020105060306010e 83
    0xc40c0c61424076250100080d0035114040c51343c1ca41401c0c0e481c00c030303211034001c48480b420317116580c44120100108a090060604080a6420041c82a4950700f08071044030000741c841c1d42150401c1034100314680c2d00041400384603130070100300911903044035440f000800c1ca285030240b0f466003072802c21091040c44c0d404081115500d0701c414000b070721030070b56840071210040c0c4841d010071010385030319603028425404080a00c5c40a440051180e552001c4004081c0c0075a111840702da4000400561200052180d55088000c8034081c50650502040102181c040e19200f4022150754a0004009680740010013800d150017620070841c030b040c0713420040003a521071220021144240000000e040c01c05041002115610081050600249a00b081400d038007a03021408500000d20082c00540ea5a105081c05007807110010181c1514086010342501c0000f8030040c403d40050004108002010074516408002508400f41c1184203121540042c08481c1b915000307464018090350002506812120040 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 26664960 1250 26663710 26663723
    0x312030c0201050705040909151a01030f0b0d14010603060c05030105030c0102060606041404060305030c07050a0b091809010207051501050a080304031e031e080406050a050403020c10050c0712 84
    0x160010310680c243e41055031804001a420002005003900c1a401b400186118141040344840b0300c1e8440010b4505d01c81c0054002a006110072440d5038140c451480741d200711103800d00c1040c002200040303014044038000740290040101526a03c0401e512120247d40d00807020080c0264042006045810901420b07000303114900e5246050760000454a1203504d000301180c2c607103801c120b00708507150310241109070041d441d4800840001c40c188042d000e44011700c3e00901b0854505000c00c110009650701c40c00c0c80000c1040400c500741c94035001e08104206c40b24840c141503e806026500900c902040904140102010015143c034802d2a040c105c840c121240501c0c1030301c40030010f40701c0c0b00e144001090070380c43c111503500d400c52015012900302d02900f4448503036203c08042000090a1814a8000a00301e400700010429280300e0a80c00410320030081001349042e13a0701942d1803100509980c1b081403481403801c5030300d1213001110308152681041d141d02c039030740310859218060640001c0314030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 26666210 1250 26664960 26664971
    0x3040812060603060d080904140f0403030b0108091c090e0f0108010c0201020c03071202070503030706060f210303050a020c100509061e0f040201020a080c03070302070501020303070c03030513020a031203 89
    0x342c605003043e6070250a00502a240c20240c0c0e41d104000b81c3d2010030804d400903100c5d000c520071691030010f590310030440401089400e25091030001c0403500d94559a5041c06403804c02d1044101d000101c056100d400500d810700c905281c40e00540e606600c0d507104c012060400e178100002e1041c824403640c1201c15000007441840c40110084c5c1c240d00030100e5081c00c5070300502084003c02c0a40c140d148101247c2c1c010b4414494840001c6403c55000e160b050361640e0b211942040141c00b181007482c0144104402c42d0554848461070404030309002e140a02003580391f0740801d58801c01c5a040b100080b642108650448051301103401c0903000449038060280540707000500505412100164280321443e1829070b2035171aa00020310b40f03076000d08181d04500c9502c882500241c1039400400100f80110001c54a035002840e00902e0480e5540181d811508140180500d20b40c102c1e4403001000da040c00c010805070b4034140325640c0e0b5280444003070742c8194100400000c0c0b102042c40c00c003990700c142d80d05001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 26667460 1250 26666210 26666221
    0x20708060106140304020a051507120906050d0c0207081c020c04050c1903020f18121b040209031015031505010509070f02030c0a0305040f090e030f13030803040812 72
    0x49a11092052a001c40d8503410140102204a00115406840244040c41c87d41e21303900070901e04020f11850317041003a03000502d4424041c00000019482200c0e1501500351030030004028103e00035040303024001034403100c510084078003e009401c00703050f0346411948000200b4907080c601c0e40b0070b20340c00b60160140c2602c202181c1407501481d0305c03c006040b6000d1030708028485a025003100ca0340f101007015400e10182103841c8203c0010b0a403035802282e0800114054410000311350402a8442a1580800c041c032405840600541c2101801100c0058031007181e640030904009290707180420341e03454003010450302c0300c6403000320090742d028205010071034041350005001c840302030050350b910801d07440001d9140343c8620207a0301d02005902c10f403820107107001002882c0185c0e0b00304c21404610b022405000c5071640c411100001c2400403820320a01d804155080c0e1a441564045824403c0c00a0b0903901c580384080520000d5501c48034080d40d038a4a41012100c40e08210441d600c0182180c02282 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 26668710 1250 26667460 26667463
    0x20123011a0f090f0105130f03020f010201020711120c0607060203100f080a06020a0507050105130b060d0201080f0702070806070c0606050618011d04021206040501080a0506010b0304060618020a020708 88
    0x9065030a0040500e1810f2140c804203c044840c44801c1410041c0c20089641d10102c1d941d81680140001075444200c00c0c1144104184200304c4000d260440e8414800f180105203c04c80703c0245100584840c3d1200055806003410040b240146641102c000145035042050650066128000c680c0a4043c5161222400c1c1d41c070b00702510499002d80d00c2281c0034404120380740e0003403400d9642800c00e185041820742d0b4450a45104459000c03003010000c2001052101708070b05a5400001100c030340445c2400c66001801008000d46002201506500085d181d2030007040810082d100103000c461f010724091500800806224204458075818420f0005250030101c0030389110303d541c441c02c040b18421f0b40c1c004541c00806040b5558294440304c000c428207441c2c62009000b807524508040340c0304c1c60036a05010940b40180d000101607842504e500700420b030040340181c1515078030314019580b915a801d08101601e89a080b40082c0d030100303c003400041510754003c24105519800750b4040755611070029 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 26669960 1250 26668710 26668717
    0x415050301030b060a1a0306040b1216050111030403080304061d071503090309050402031302091608060607020102030703051c05010e010611060907050402090301020c0607030504051209010c0f03020123011a 90
    0x220006c901000e00ea50041040c024561041001d00b00050f46041c00700061192003a20140c0b0f0b441e6005412425150b0301030000d510040c040030700745036480e040a0b28406540384510711001e0032071540800418100b100c1034000648649940100549980c0e1090a40b074803515948559400c0824565003807290034028003408032541e070180c84691219140c0401d1001951004003c2c81c0b1281401c5101801651001a068010400501c4651200448101c0038005a034003034038561080340c042c028000141ea0010440f219290315103006600c4001d081011108154441b51480381141020b00114a5640700c100c42412240c00f6511b03410400c4d0036061594444900b51800126038200714070602c820708054008000007500030700014940003005242900700802540d400c0c0006c0e4417101408180b00c010055110303101b0000b07400b02d190044900000c0c0803a84200402030600c0d03011039440d403d16000703510100011850701d044181442116032080c40f81c40090080a2102e101c0c03200c01842c004452064 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 26671210 1250 26669960 26669969
    0x607030b0f0d03020a060603080c250b1b03030106050306150702010917250501030e0607020d0309060906020d09060c0c0f0221070801061d040807020d06020415050301030b060a 77
    0xc001d09400d000d00780802d00000300410360941c81006054400200948175030001103002d0405144c6505440d4015804c00e21078080b900030018200e05402401d501d09034103c400ca441100e0080d6403204c42845403100f4820140388243c00340400701c00060004c2d000002540303d001c0403282c003070303011401601c80200c5001d0644040c0c0014100030040c49034902d002040c8030b0002c5030b08100c076038603103c0c121002d0720360b0028a2001c19110a40d8002c01c410350b00b500504d00c0c510442005040a031502440080d910280841c6071800c16843d4440901402901c4e030000c5001c1d5009481559601030b01e4005d40041c103908a0201c0d20b0750316020070011070621402d034401555501101c00d103400c2c60150200f08070444006e101c03442120b980c1e00c51a685200030810781008200b0312002081d51842c00c80200e456006107104110040028400c00001030010400c4510107a812507100341da1401d541401c20081c01381c0d41000000f140701000a20000c0d800c10041e504a034492034000300c4c2c2d59150814400d106105208 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 26672460 1250 26671210 26671219
    0x30f0203040b0a09020f060c0106050a060305010e07080403350604060b04031106090409050703051b01050307120e06070e030601090b01140318060408070510050405070504180602030a05090607030b 86
    0x210300d003a40d0f55001001010b000521100301c440380540029401e5100c14040e041e241c0d036900c4100054145200c8160007083c047c01c0800c50356250120140001074001c00c0d100810490000090805010740c1d8103110284489244d8000802d840303c0710703440380071030040380d003280ca4055000424a151500171030f01580c50180c41306080502d16a00e851a0954141040380e1052050055001036107a0703104202195000701e0041c402c0302d107542812403c0030589040e1038055500b081080240f80d8002d421650011740611f00085040c0703141c40d18400401410300061840d00858040c040d400350b1124030300d01c1224080707040d235005990701d011000440b244a50311170b01080c1400f5070440007003040c0010b5644481e2100325040109107603c040c40c10008211400c460482d800306010701881410010108842d01d51b803010825420142c80b0580d60344800e220b114441d80d02d80c1c54031540c0c0100c02a440d014194045025500ca082c00240b410142001700d4030503400b440b4910018106034800c2c0262b4069400142 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 26673710 1250 26672460 26672483
    0xd020918030d33061d2101090210030510030311030c060114040b01020c33070f0309140f090c09220b0603010f03060506280302010e01050901021209190b0406030f020304 74
    0x1024251060741116031a030054600c015089204a400c140c03600b241b0030807000040c4503141e0f1040004944240c44180c04151031300e002c01000304072900c01c49080c5c07038050403c090b00000005c8202c0c82d6101e5080c803590701c0d02881000040c0c16642030036108902c40225002d100a41e0f4003001284d5508185050b5a4000100f0301120440780307901e600d40d800e01013010f2206c070a0307e00d00e46900009610949044802810b0020008103141c1e002000d40c003c0c2c5411503208850f0500800040c00b50010010f5007031054200c600800e500983c40300c21207030307802000b904030648908044503026100b510204085e0381c1e1810401c00c1d00302440e06070203ca0507910310301d00c00d5043c1402e45d100c943c0242801011190003050174801c41e82600040400403006500110306440882c1c11840010726668200054606220040c00145110780e008160240040a1140941d80310b4280c10f0002e41d80d14440090a94400c1000d18041401d1401900600a90303d09407402e0000710006100c03030040348011903003d0040d64000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 26674960 1250 26673710 26673737
    0x50f0d05060105090a060810090e0a11240909150d060f09020d150e03030105010e1903080c0a0507050105210702011104090c0305060d020918030d3306 66
    0x55100315040441031403d242031100180110b40d03000025007050000c03e42d0784c020001d10201c04005031f400750190741c000b8000580c030f15120694030016283e000b0440c2015010301c241170380b40d041c448012900700802d54030158007080c2418001ba4491140240030701e0203040002c181010101c0003105203031015100700b84801b169110b1400a00300c005c4040102d40d00d40070708800ad40c0d25420307449480c500072980342500b0000481480d04a4410381ca010b00503400c01d1004100303070f81c0c101c2d01e0311981080656a285044072000360710603502002c3d81004180c3c0c90f000c1881c0d02c00140c005501d519075846041106c41550302c4800665241c0500175221022080070503c9070801400d01c00400d42045060001190300e507100010190250401d81050000680d074108500c25075505008040c2c000c103040c3c540070412030203900401d4628400515802c1c400c003d030030300d98000c24820021242ca990344c2c1d0604000715012020700c042203c603021a10118000d9420507400c1c0312242141001c00c86010352074007181120380 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 26676210 1250 26674960 26674987
    0x30507080d020a120f05040305030a020717041710090b0112050327010e040216060b1804060203060109080c010f080601110304030b01051c050601060302030a091a090d050f 75
    0x1281111640c00a000801c4902440d0010740b00500c5a034031000b403424000c4039510129004203d050600314108030501020a400c40100c903001681d040703000d65114a40d0030512605050303c4c1d08151201070000380000d074860000d100780242080703281918490b051036180b51095440141000d45411014001004280b00b5403030034002c0180b0174010350741030050044025900c080303207458802855450320440566580e000c005001040012101141408040320011001c9521030700c00401d400d135900c031002c02d19522020510912581c448080d1f2040c5045e207000d03406508142c5c0d5203401300300c0014022610040100e8031401d11070060f912900075614440b03080b10304240103802c06040c00b5410220b181c6100050005001450244004490951401080c020620807a90907048a14420184100043d00108206045a4407131402603100d07254105c10a00600030020000c041c0305030402e014076a0708180307120780d01c5401c900040d55244d46210320306032a14400c0c17402031007034018100300d070f600d10080 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 26677460 1250 26676210 26676217
    0x20c010e0406090c020d0807030606120f02090303031003170c0d030f150303020703050d02010e030f030603071805060901140a0e040512030106080f0105030304060c0b070e03030a090e10080601030305 87
    0x500a01c0441e0056071000108115204400c00000607009414582049a0442d800d15004001443c00b00046494410001e120380d5044408014154891044071407440d003a805440c3ca8090040903266a4140300308960a0701034607110880300300c05054100d220508122040d12003a51804024090800c0f080400714001d142110141a60b03955a841000c100d880d4540020003551080e0000e0200c1e50660914915100c040e4080008682c104046d07890b1401003c0145c0d0354658400c4503082d200d41301c2c0c00010303082240a4001540134020505075038003c1034203401850042e00152900402d07a601e80c01094111000b021304c2d281c20180100701000802042c40850342d00030f000313405903940805010b10441c015442a13019030009682c1e034062106450361003e4803401000120f00462906141c1039001d0450004c0200c00ba145001c3c1c0ca0000d0b49190080243e240c404000905403944d0321000350026151000c40e00581a0005000740000c090301c0e5100c903c13400365106080104182da2840d41d0444103031b803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 26678710 1250 26677460 26677487
    0xb09010b1b0303010902070506011203210209040504111003090201080c07050703050604030e090711120d0b040e010c030b01030b03100c05130609031e030806010807050c03070609020406050d03020c01 87
    0x400c14074140000e0000e140a41021400541c0d01c0541f070500320300d441c80680002c01100b5403801c8210000741c1044210000c0040c01d80300d020003400c0440c1c048000c4c01401e2449420030b0901c0300f080200311003058100340454088551109658210313000700c04517051450000e01040844001c1788100404001800009108004490710f00351a0b40d505806c0000c00d40d02100402c00c4152688030070b1070f1825142d54041e000d842c000c148201030105003a0b50300402603e9008070750700080d18413044200790700f010500403806042842200000d0360030710300130700101048100103494550303e02c85940c464040c5401d10360b4000c00070b00c4080303112503009e001800481c4801051000400c00c08880c1d410550210000302480e4580000c41e07482c4d41070041050429109481440810300c2202d0f00089e0088100c581050081c41c00380400d0b40e41074801e981e00d100f88403c201e00c030720020510b241080061b4000300c01c268803d48003805001d03650014010803400e50f400040140e048500130001a501c05c010005400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 26679960 1250 26678710 26678737
    0x510090b0f0a09050a2f0706140405150105061e0f07150f050a0c021009020303090d05030c0c01090609092406020a110604050f0f030106090c08041103010b09010b 71
    0x1001070301c00240e510605a4002d1003c25102d00030010f0800041c421107503c058500d00b0388450340b002410300e52141000b00c0d416180d0020225040c3c003441800e6102946450310020300c1151800e040c00c081c0d0790382200541204007801c03c0000882d050504405545400c00c404002c82520380081002c14040e402988550f03140580502c000804a894148580b6000e411400700084455400041e801511001400100340328200901a1107242c0d0000e203200400700c802000281941407031001070708511a20b02010b9010000035030443c188500400100300e03071041784044442140c40740c001942c4034545441a040402d0380c28a04202c035000303541200d608510000600920843c41c080007108030810350b0009001a40084900410001840b0130001c510b08200d40003420309203094001140f00068920090003098a07500388001902d0940101c00038240c1c40600b4070040000c800b00038001c480440e0140d0307240c0c1c01c0f01c0e008140d0b82018410200c8541c4e000d890381406070300781000d14056901044c010b1400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 26681210 1250 26679960 26679979
    0x706051e040804031b0308030c0c070305010e01060f0e0f070807020a020411030703050a05010b030106110115120201180803040b030403020a02100206070905030c090103060c02070906030b060111010510090b 90
    0x1a0103008604a21a5110b180c1103601d560860406150802000689009880c004042800410345c0704041c0d07544034140b091807035500e5510000003408c000d941da00017819503080403542c100350036045d040401901c82444c800d001059591180000ca118241e41c011403085100b0045100c03640301d8040301f903111100c0e00450b08025241ea001c50106ca106000348980c005001c028009410f03490300503690004602c01c01404154100303030f00c80407184010320030076041c0f0410421607182c100084d081f8201d25854006881040c96907960030f510b00c0c0501c41000c80c0050000c0c8184070032100002c500070b0a40301c01d0030085007428200040c0d081e2560000e80300b034055114114000e00180d44200c07601140500690180005003000038010f40b640c103140c3c020511030b4200000c13488071a12001d02040c1140c2d0820300114141c02c2c841c400b0b9003422110341090b50780350305000703000c001d0050300420030b4064002030f41d40704440003421704040c0c00c80e681525007c06034654004104211a42c40d00544500c26005110340170 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 26682460 1250 26681210 26681251
    0x2010e0111030c070e07030903021c020a080d090c0501080906070c030e060a090f08010b0306040b0a060e01030506070e0d0b060d06020409060905090f03030702030417100c170a0b0303070605 83
    0x81d607004607080030f880b9805000144110420102c545820010380d00341030101ca038007075401a4541c0b603995011544102c085004182c4075200700042d51740f49401002044d610503907451340f40b004c3c02c9044019640940e42060010707855100f640303041d10a131040c0f0080e00460b1500001201c480c0c046440540070440048d00303d1109982d900010071080344c2caa200e24001c5451301c00401c02e4941c1a60020340c050349090b080c0d28031030718003040e0b80d9402680034904000c3c2c0c0c0d488802900051283d0340007410003000b00d000200800c0000514280101a03503100d503120600d00500304520200c0881004100c0754004010480908001c0c1e020742d8504d108003005400c00c0e445e94200300481c0e40c5070740180c0d0007079117400034860130400521610700450f00e04806185503103880180a5901c2c822885507108000e04010364452464080c850a18503540c000e100340075440700700700300507d24402d080420042201c4d00003c110958002d00c10640d503d10064095400c007822525148014000240b9400240514180081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 26683710 1250 26682460 26682463
    0x50405041404121b060f020c030408030703080c0304111011032101080106030b06060c0106180b01080906010303091710060305150a051306020c010b0a0303050417070308030402010e0111 81
    0x1000c000c90345458614034007410001c83c51203244a8120078031825102100d1022581c18481101c1c0d50007220100d40702001d5418040203104081c1d0484041c00f010034045000040400100650760003030340c4000150300c820321010f03540e21056400800380c411040208044d814820098203030a045c0b4103100d1548404588103a003154040c00c040354040a12000031800007018075909405890140001c200b1242150744401c100c01028010610840c80895500c5c0114025089403000e0320652600d10030b60a40c100c900005840f10b400740d0b90201d030142d00000c400640006045040369055521a050540340100091500c0c4181c04200518004d401d4000358102490181000951203400103051504603580343e581c41002c003429406002e404d002c01c0c050201400311000c04c505030420401a6a5420480003600401262a52a8200c16010070000c281f540040c040c20031140d8403001102c03104140024107480b248603000040c0b11100a202250155120360140d510041043c145071414410404829 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 26684960 1250 26683710 26683721
    0xd0318020a140102010614030c09040c08010f0606080c1801030f09060608030712020a030804320601050307050f0d08090301021213051b060304060c0905120a050606060702010503041205040504 84
    0x56180c0b09035824002c050350f42413040314020314442155850180c0010000703912401742c9600c05105061300808142808004c0036074800400041e0001c100740d81c41c00c1c0011300a0005403249070b003c50045400540100d04080c125424181d691140b00c00e031f403d03140010340041c03002001100030039a60b8451b6100085841c030800c0050301102c0300954680c15203142c01c0d10003052142c1c0440440d00000340304d1000907080040716030403070342c00161031a80e07540c0000c20880c92210410075010701041c40042001070040814107a059a1040c1c056403240c1d621841401000706610303102c40d82040c00b400c0040041103400700130344000d4000030000351400e214011420520340381903400101100d051140502002070420069421480c0d5248503102d4200650024a5900005001804c030586564210712128400d061800103041c00420f15800360100e9019903981e1325112000700c959100d00000b2030403500e03000d0240c89110f9070582d149032a40c1d540343e90b1818038082c3d117203205051000600000c101a911070090 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 26686210 1250 26684960 26684969
    0x40506040b0409060501140304060203090a060c030902030705120c0409020406030b010605040f0509010b0702010c02030a02120309150415050c10020d0911010903110d031103030106020102130e01080d0318020a 91
    0x42d240d9082080400c102c0e040e039132009041c02040c204140030f041805003520303485a040040140c40366240800750b4140005410010051403515000303810490b01a0f020028087c025002c80f1006521482805160740c1c214118006a034070059809400e07181a030400c1d44c0f030510140010624559075514000e4110081c0c11840100b0404102407016200b80d81c0d04a00034034080302c01c943c00717526040480301148112032000c4d04100740c46000c0d4003036440401000c4100c40c0d02414951040c88007203c1a9166046442e060340b10b03041d004019005440349038259019a44044500d4a04050300300d0f080c0e40a60280b003821046014114804103005030387c1c80581071144030840701003400c84003481d04110001d02c03003213001c1c1070285282d014004681040e480510703006054a8960843d0024182903a0400d00c403c4101e09a1000000120351303507506402810324000ea6403042c0700c460707482e062a82c961010034020203a25600141c840d45c0601c3c4030b0342002c01c000421604902c421802500070a190460303e410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 26687460 1250 26686210 26686229
    0x1415012d150f0e0901060806180a0f0b01030b03070501080613050901090c0602030307090e0901110c0a0201020708060c0a03020f1c06050316060e040c050c0609010b01140a0c031404050604 82
    0x41841c4158101c0009007000a8514005109082e0782000681488040c0140010004034200051564a580c41445c41c603036845841507a00d842c01d441f001d4050072014445182807800c1400389a07147d4082d001d0009404001005004070301d0426004607a8082c004000c82c0e803128076214414241071103841400e019501c240001f24111295003820280e51035958405421940304104102402d60b012002000303440d010f401e8108591540c82000f4003401c40301c100c400192000040346e00c070380c1038001048096a4803e8003690b01c2644e42d007a1041c1c540d84100c68403054880e04202c15958248698020308a213240060047d05044401076401e03007214140e804020280c0d0744003c14440f0340380400000110307c1e80000703500c003501d04025000702411200c00a540c056034407034194407c490701800540c0c4000d21050304840c00b0303103420071089010300841c2c0245800310304010312507400c1c140c01d0300848000c00c1190b1281802918190313421503044944110a81c4000b206010128144d40c802005100030100e0f800c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 26688710 1250 26687460 26687489
    0xa1a0d0902090414150403050d110408070e0411030102040e0f090102130b030a1a030d0507080d05070c0b010b040521070302031606020c0406081c0e0406121415012d 72
    0x7400b861805d203032412002015010901040b0001c1e031b01200301d640c0790600d00008201000c140d04800701ca8011a08000d0700c5014000d0007040d211080100c40b84900d00808060b03c2d548035a0b000c0c94201d1180c5e00a0020360401180010710708c0300c00464990300200080001403902d5105040c041c05081650002005100c00100b800f24002c42402103c0d0120380c0c102d4080d0140e02d0640009944072074034480e0394281b0401040e043d050050328402d0701c1e503406061105009919280400400400011800b203070950051400404c954941c8030688081c0d61010700034117140038001d01e04e04421044510850500e10808001100580b41032003440081c981d4082402d005604046000e8140030004d5521805185005c104001e0b4480008610108a00710b000d8424968801842145ca120201c0c80b0b49400038102100010400080c1304002c80450103000e6001c3c0000d83d0003581c54a601440704441c002160110052180c2c4110b410000307018600c03020240d11502290300d480003115020752141a2a65154 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 26689960 1250 26688710 26688743
    0x106030b03100e250e070c053c0a0c08011a090408090907181202150a08160302160b07030e120406050307090b19030b0a1a0d09020904 59
    0x4012064061510b11000c1c040d055000508990b114803450016034901440020700444136860111400544010b02001000d8a800d00e0094031a060700f4901302c80f03901c02d1020700c82d0780c14100c0a100c115250401da48001c0b07080c1d8240003150303000c42288810030703c0c0a80c0d81564001501114240018111400040f980c502012f0900c244555500700c0c240c040d01c401405c001c0040c2e8401d0450341c840300100e130b000300940c881a0046807000e602006026104805070b1011410445800001e2141407084803118101152007041d04030030302803460494086032411001c80c2c11140b04401e091496011413030300500340420740c5030013035400305403000075100b079038200080c4100c0e160300d40079092408406c4401469604c2120307248080c0e92080740b18a5003080f4000c008140d0f01c6209515000c0140988070000340c540318807003500c1003240152010500803031324098901c009405c000700040111025840c6014164410306030030090340d4001038218510302e80ea03007482001a50380c940714501842c055003044c203d24045 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 26691210 1250 26689960 26689963
    0x13020c160302130606020601090203090c0307061106010911030601030b01110a0305070b060105070519061508010e01050601081e04170c100525030e0c150a0206100f030201050f0706050106030b03 85
    0xa076005001c4107013000d50600950b40c00084841c1100c0c1c1c0707141c0c016500d6a6208240d42002c521080050b4180a04000083d1b0f8030782c0683c84407440281c0b542074819503681c0340c40c83c03002c40e22240d4003480d1080d4140001882980694440d600040060519072507122821074000d0502100110840c085400801d0f0b500c21710008042c501d44c030000c2820200d1901e007030794441da6035a40000180c203050001c1080c0080070810f0719000b035650340720b442c0100301c5203507100c210650280c544003a500c90198a0103000400c65031007101030078058502e1049100c401d80e0403000c54920200700610990b03501d11100c503840e020f03418860080c2030701d10315000a886040030015401c400e940010b001403011040201c11000300b48070407003006045500c141000643c043c1011001030429030070141c40d5500891490103981305c412540d0061242e19425800d49440f517a4004a40c00c400006010703403900344001c40d40500040d40242d0003004000d000e142c10fa41454010341e5118152203090b0402030000e5154940c071046400c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 26692460 1250 26691210 26691229
    0x6080601080f010b0402040b04030807110d140f0106030b0106050703090506040b0703080903030f160c0f050303070e03120a03020a020717030d0b0913060b0609040f1b1106010513020c160302 83
    0xc085400354071f05440c08402d1482401140800340000d000002d00d43c0802451402c0094100006000240000d1503400d04941c0795551a20f14013040c02425a040c8082c0c0c0188121401d0b29405900c00040380d0a1800499035078000b100114140100d412000c01d0750ba0314100944000d080000364550394038001e143c01880100003a09111070396006205014600e0b090a081aa0000e6031202d01c0f605c040f220a000c840940788058003519803034100100381d0a120000c0019407050a1035200e502c055840031052590302c54030203000b507441510a03c140014244250005c1202103071502c1201c001a0715024000d01400c1801c0f02000c196000003200d00d0340485c18001e100060400b2142140385140000f84491580c040340e200600c100c1d5039000142c02e80e502c82d0140c031003090001c0c1040000c81075a504490051000051100c03940b000c0505800b08a4070820ba6286049482c0002d821164a444184080748030b903542d1580170b1507028001100250707810808040002034046003074002c68074500600440744e1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 26693710 1250 26692460 26692481
    0x4110c0106170a080703050d050708010e100302210a0b070201051506071a0606130f0e0108060601050a0c031e0206150f061c0608060f070f0302040f050f030106080601080f01 76
    0x380c1e05801c2002100c010400c83c0320580c000e070080d60344800d10314084403a88903c100812000b0315143c14003100d03507400034509058441c04c04000700e141d16100740c0031082e10b402e440002d50161050f102c0814004201d103034650707405480401c0394400f03109540c940ca0945011112400140c2d035075010001c5501103561080c5240b00700350791007441d04130703181c540c60045081070107000c035500752180104000341c540c00f003155161654094040da02c6510780743d40742e061900f03601c2104e60400c1c0e620008100303041c0220300b80d0300a40c1d058440914205000d8002d45140780640001d500b8098420a404081d003454040c500c402d087c0b69018010704c2ca086030308520441001c0c07865130b000301c0008078280d00d40e444170001c84103141d4001074282c0300d031050300340035002a1056030404225400742c00d05100c40e0049180c0024022100b5071121090302c140481c044040340201e20801700d214002000c10829410700e52260940d02c031002c1d0001c1105902c030b131400307460082c00384d10011680d03200380c142e5100404207118404440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 26694960 1250 26693710 26693729
    0x4140d02040b031f05061804030302030414060106020703020f181902041206090203010c0f021f0e1501031a0c04030303020d02090330040f05010509031014060f1008040303020904090204110c0106 85
    0x6802d10513840d1f0041400803c001c0c02d0590000216090112103141207000d406640221001c0d136031101002900c4210304d1104a00503020406200389a14144192007200203c1c0b6141c00b042c0d40c3c03154030200c03880b25405503080a0360f50810000c5a141072541c00095100e004c1c80000c18010003a2040c1800c4641c11000c0b40100440303240d41c0800c00d5408902030044014441040d180b1490b441c030b80f04018507088000101d180300720314200280141d8940801d040328040c6013040b05a50704c44850840c101011220018803100401062001900070781c0075151000140400600780f0982e90301092801c0c03e804640c05901142081d420f266505d02130b0103550340003009401504052030280c000035114a54003c1d141889004912071000362410007503c3c50603640b00206210b40d00303c0100c04082001e00340c0b04030340a036907000b15103c0503041640c440e4012034100e66410400d80d45a8070114001d4012080290b07000b40c43d14468405a515030081030a03000c03000401940e10820440002e003150269171044244 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 26696210 1250 26694960 26694979
    0x60e070503061f181206050906070c0f03090306020c0604140a050304170c0312040608060f0f040f060b0f040512010608070303051c020309101104140d02040b031f0506 73
    0x540b03c040034000506002d00048888244904054805a903507120f0440a078010f10400101c6140082e10220601d014000401060703d40b1504291103c0f4103c40d04004980488058000141c0045483d07025038040c0c0740170540180c40340c1c1c43c4401c1c1e070b120800081d820350060042c00103100c045a00507065603901401011000741503a00c15490380258881da6101c061a01540d00c01d0310003d000312411003000500f5500740c0c07035034202a1120364001d4090500002da8010004185050924404952610081000384200d003040204009000010103111165440d140300246040100c0094030f0001d4003400d00c0c5444c5c03030510040c03209401e20340600c0c1394540e05010b41003154110210b00741c400d40c5d800d45051036640b0348018800f42500303083e04821400910000401031b401307002140070100016400428071a400110b8020020f0f4000c501540d947c00c03950000a280350f00c0c052803031b41c003a180301900208400012200190038815006460600e04c29100d050145a4125204141e40180101c94407500b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 26697460 1250 26696210 26696221
    0x10501140a05060306030304030f0b070305070503040f0605180d02030c12030f0c0706020702060307090524040501030e01060801020304050a0201080a090c03080309030c0604050708070e06090c0a12060603060e070503 94
    0x401c0c0300d8481d60b801100d000000c43d0441e01c05104450255400482c2802d0072040351908041c0c814040f503039580024a084c0201d03217054071500459010316040710505141441c0c1d0745600000f4040641000000c1d07502102d107030890ba0b0306002c3c00405035910380103075489400b03843c2c1c26414480355a1100000100c20001c000b00400c071a120b00c0c0e0004460b900803900c402036032501100034404c02d140170758080c4000c02000802076221201c0000d4900a5a02100a06c3d81440b025004140c0118501e0412014082031099503c01e5211105501841d0000724000da43c40c592942241c0c0b0640b000c0e9095000415a20b0035035810030b200070381100d02c0319000c000c46a0907446101040c440c90000400d0404004007180c7c89420410648a107825108251503070360405191003a6102843c0c03081d240c083c0100280010202e07100415135110302e101070418000b903980d0b0a0b104400b42d00c0308002c1c40520540740c0c004400d44100e40308a1000c0d24403501c00080b002d050100c030340c0140200410030410001e04008010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 26698710 1250 26697460 26697469
    0x3061401030506031b221505030f0601030611070f05010b1002030a0903030309140d0306211109090304030b0705091305010b1206030c04090501051501110703030809010b0604080f01050114 82
    0x610741c540d05080d05010800c900000c0c0c1900071501b14810101c1540c030841c500c0c4105607012942007c101c1403e000c881c0d50318401c1c15103c40c59540400c01a4025100402c081209034200c2c02109009400b02071400d0340710340e00c90742d044486040540346690364102010503420719001c00200e1f00c00c2400154201100c880b0010002d54080c00002d04154489604c042046465034040c00c0000c030201c1512810400042d000307005010600c69071071481c0c0f100304198076203c40090120031031a081b140b1358080403218018001d04000141c010507140c401004000042602140c80a0003a400b0383d07900b0741d543c4640c1e01000114a0505268403003685041c004106130000c810407079401d07542001c001c00c40d55075010006410310b0041a802c50300035003400355085c20840d065002030300c1003040050200c0c1442c5110300454142018460680c00f07a40064002d1000c00d00a110081c0d1181c08000081442c1d40140045905908180d000314915804400c00000400e02805094090b045130181103400c03100c0c07140082d = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 26699960 1250 26698710 26698723
    0xc0504080a030f05040b040b0c1b0a141c030f0e0108151009090e0304030201030e0106030b1305010609150503010c0f0203032206090803040212060f191b0306140103050603 75
    0x2e0910200100d108000b0b80a10140e0b0010100002000c0c0c50f19680d4046941651246160288901640c07071510903254018403070301c0e00100301800c0d488546080030030b0b2442180340040d40ea0390040c140c046440001c10281810600c541c840c0d1317182040c1010200c0003501d1440041c1c2e6143c140310502c010020000c408100c3c1008000089503c848140500c1805851611440e00a03030f4081d03040020064540342c00000800850303100f0baa04009000008100b58200e0701c043c00010183e00724240429140c021418200702428040d40000507aa0307a1404600700b2034600894254441d00400d0040015140a206040020340207003452040c20b129144020340b2884002c120401d4010500c2178030003003d2640000100e03150b40408200b011070000d0418900c550000c4808920074455441009405080881d20310300488141d240700609071070b55001c094842080e80083c002040c4e031000305036a206030490611481c0302240d1400030741c0c0c609084400144011101c9228103050420050051a84001442 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 26701210 1250 26699960 26699963
    0x903060604050601050c0a0602030709050303040506030105010302070c090c02011d0f06040803090f100b1504061209080d0c08060906010e030a020909031303060c0207050109180b01030f0c030605040c0504080a 91
    0x2010f0b61000d0043c1d805014154150703080348a0016800d0820119500460180c10030352030385c0c0d0810b5910f404040d9648254028550801c500b840108020750081d0044d01c80a4418109a074046407107641e510121804c6609c0400107030345407918080c0000903401040c540400c02d001615a90399401d2801e90713540340181004101041c00400143e034541c050054801405402041d10314441c414280303500038081c1c11541900ca032401c040d510903041102e0003107070704131001070310b8002c14040c0c0d104c0424010144881c8c140d0b40340700c08115400d20140d55100310001d50740c103a00c504a250500409020a5070801403445050000368400c84402d903070000390030700742d107030b4119902c040a555118001d801c502955420850101c42e410001c002c11074103410068507489141d0031a00b43c59034440045820003032a02c0385d0840d920305524519081c503041d0700302a16080317040c100850301c2088003c01d10b046462058407400000d40d07d135400d20141ca003e0081c115600c08516005080504042c02d160311703000030090 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 26702460 1250 26701210 26701219
    0x60504060509070e01050c0115030b0f010303020d11010204170a030e2710051207060f0207051f0207030816020a0503120901050a02070302030a06090605071e030b012a030f0509030606 80
    0x11a0191390b80b149046600301c40440c0000d001204464046105404003808221812082d14000807100c41c0c038814144e04a94140d40144811095046e0983d00c0000c0e149076800195001c120210b00782071801417207210b8002c454010301c42c01e001d500f0010610840e040a03244902d26110214044141d200041480c1c2c02d1000c0108d12203844650003036191b0100340d0310490700000b0103000100b0041010aa4004440042e211240708925040c1d0072600d0f090350f40203107030340f06d000c86002d1035000054842140101e0325a0044543c40c684036200c02d40320f50003211031243c0e0001c9174404502181071113656079006100030740003031100c220480c1c11420f050144c855071074100700c1e012607035001092003040317104011500582a00e41c024901d0415502407c0440c41c1070381d0b8141041c020511a030f00c18203112203090b100801c9040949c408030400c60184c460362806504001850038050a4103c01c3d89019a105058100182d10301c011450050442c0425445800a1040a0000da0040e86010600c20340c08176044a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 26703710 1250 26702460 26702477
    0xa06050a062d0302120f07020601030b04022d0109080307020901032a14010e030c0f040515150912030a120c03020c0319021b0d0b15031603020406050406050907 70
    0x210149007919865514008400c03020142c0a21640c040d4010030160041c92007844441d40c40d0310024940d120292018001a8889001080424010f044007a0803600c0100402000045a1050402260090801742006025500103a403940c0c001030744000500e0303c6c0c8051420000c640d0002010203005100251541c02408160118540c0c1c142249004070441ea003848c203a503448103000351036001201c03201c2c0d002c1440181d11070080d00d00041c4640c2500401804070b20b100c500c2ea01444040e141c05081141e4107032a89081c08002d0f03030f07030001c0c00c120032907a1000345880319441c0702084070243c4508000d90142c0c00411090b41c8096000b000204020381d000740100e141c03880141c048000f4403440b0a00f26103404080f07841007000d041448124003136003242d4210f032102207045005004c0900d000321307100d83c401e000091001c00a03d10180c1203a10181602441c0d85000750200403d023400e485803081581851001c2051045182901c5a40003410040e24100401824400410803424001d40510180300d80003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 26704960 1250 26703710 26703737
    0x70810020a0203041503060521100e010e011e05100b040b090307030f0b040b0105010813111207060503011805040c050402090a090f0b03100c0903030f0203070b010308030603060a06050a06 82
    0x80080300d00800e070300384011903e074100d90170080003070107140105c5108140f031f0b41101c5415400c0482c0680c035124a000604400100d211103c001050101c810311b034035540300c8410204410082c4101032903005040411540c280d000b078468000c0300d40c000e00000907000c02800034001003500701d0542d020b0764801c4180c3d55440488074002450042c055100603c0442c1c007503031807010030581c03000e020301031841341e0450301440e43c031400196042502228081c00700c1030340c645204007258410360306c2c55007600044e04d80b110301441c4200e82410324200c0d800801c00f041c40000108200d8100740c000750100001d034502003055042c6a40c1c1d0456514051040e00d01c00d40e008144031030030381e03102d070a01030042484003010480e01801020680c00351101c0c202503403090003200204c007002c803e03030300840070085203650711290510b05580d002c0d242500003403910003c520050008000140404084501079805070841d29160700d800c10425180c881c0c01051004101d0074075070100b0903900c0344e10905003601c20606000c803c08451 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 26706210 1250 26704960 26704963
    0x42408060d081e0d0b010206060609040209150a0315080106060c12050d0c021006080303131b0306020309101a0d0b070e0a0909031413060507060b1008100503070810020a02 75
    0xc406188206542c282005103407007015000501004000600a00c01c40317062000580e111b12040b2070498100748104411703007442c6850f07070042c42802c070014501221005144d103269025000003040502003655003121102016030322079044001c105e420000e01846007000b4009103d03403883c9000a000c42c07203018014041ca8000c0c01a5404411001802c000980041100951711004142201c48680c07400c0e20114050310080304a900c222030350205400600d0380740e51001015070f400041041441c01c040d4020001414900083d4021000d040080802c40b070584040130480e0300841002584124a00801c1b01c942c640c4181c04203500e070400000705a80c0c2e1958010340d6841c1103628000e0717000624a0740802d109480ea07008031585070095541d020103041c0a9019101d512844801800c200c0c056a810042c241c4102c1c0107010041c4144404a01200503001096004a80320300c0980440e02502c2040303410368400851000401c0b04038020701c5540d180c83c4806403280c454606483e1550340000303844081c40e00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 26707460 1250 26706210 26706217
    0x60406080a050604150e070302060c0106030206070b06040c0c0209060409020102070503070305061602060103020a0308031509010b03040b07050a0905040b0a05030304080d02010e030405100c0f05060903042408060d08 94
    0x421038240d500700101e0303140c4039032074410403241240c3c152100100780090031602d10502080020308001000224110703020400c084c0c01081140720b540d908c500b80400180c071002d0180c0203051048001c0595802c02c0b030108000d45110780020410401d00c618500c0140e03440c0c17035403560031240a03030f000105041c0500040f0b00b004604d4001581612494500204201000035001d20070003500702c0140d0315a05000e012a101c3c5820320019500c0f600303401060011602d804000d5401c6034600751003410f003e2031280840c6082009030300c8500260808010403092100d803480d400e0384030f003c40c44e00e0362521034031036405040380b825070003010702880c3d440d5a244070030340342c008889029000003011641c841c9e41d10032304244d40341140c0d946a0015400c1460149080340700005450130b0701c0d002420665a10b6202500f00e07000e0440100c1030301da2005648009010a00a100b0b0034003603101e03000030759600c90a2803243d040c201003594220700d03c4846070b13880c680041e82c0442d1607600240115a201425442820000741600 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 26708710 1250 26707460 26707469
    0x8060906010806121c0810050a0302090a020408060c0406020d080402090c0c0a02030f03030603190f030e03010207020a090f110415030b0102030d0c0215060409030e0f0a0e01030501050121110405060406 88
    0xc11040c17000509074030755030340540c0b154207a035401d8030954030811441c00402da40e04c215a0019854a414001860a100074550044101030f00600300b5660300c0e40c00e0300d8240f054408040c1c1e20030004042c4080c4d581401001055107180c20070400c2c5060582c045510444002c1204001c003502103003100000c2d0050280350482c40c1c00070116071082e4421044030b5141e900a8841c00d11034030901840307031901000034444241c201e03081141c01c0e0041c0c0072520306890721030100802d240e05541c04c0080c04010b90703c0207030003409090071050020b26030710000c404c00d00b100c5030a100c00030401c01c10720040150018045003a24064210f02e404107407903080e076005070310354000d0041480104d401d040303862029680c00900160910f8200400594580b50036080c0402c5684124000d00050304100e0116690708011901203048100500007000e003a40d074010300000031200780c0080301e0f02d035141c000402081145100400c4203100310f100111901c0e02d1561011801c0c50490344050190b621a000100544e82e250720860050 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 26709960 1250 26708710 26708713
    0x90b09010b0f270414040503071203090206070507060801080a080708090d020603010b030f0a0507020307060509030d020711041112010e04020607020a06030f050903250203070807080601080705010806090601080612 93
    0x1e00392201d055407061800f5203580e008514003200d13038502200001d00c8030b000c2d80c1c118014510382000c549868030920458603140c418503803101c90743c5005031210b80080c82c1d804d0146020b000080d0600000502112060748441402d40c098982e070000f048056044402c80740c1d128004955500d079900102e901400b07038004c060360140001c8000a00b00045000851144485000d101c69641d110340d4100100d40041e00d000005a00502c5041e00081240d44242d400c030400380100e0341044908482507080c0c0e44400c0d41156040410030245020f42400d01035030b511000c4d02145a42070020095840c190315105109a178140030405022030103540f100300c21103a0301034015144401581d00d4007000780140684940c003035907d9203010001590940c012065403a07400250318040c102c3e10070050070110003809140142e9150041c12000968000100024001889080050000c540c5002e40a1f8200002d40c2d01c8141801400347c10800d650b43e50315004c03580440c2c01d0820001c691204808607000110385601201e03207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 26711210 1250 26709960 26709997
    0x60905090304060807051206090a0e0d030e070509040807080a030204050303040e1609050f040911030304060e0901090c0f08070c02040c031509020c1207030507050601030b0a06090b09010b0f 83
    0x518000700050040c3d40150300d80d400b098599610880342e612038054031001c2a09114003045180c9040c401381e0380c21030310080000c40d03a20a0030030001e00b0401c1a03182d0001003956140d050101c55030500c10000201401c071b5a2420514094071010050712501038010480c050008520341460300950595014040c080e0859466540705c120130101c8420907101c80d01c0c8a5414000074481c42e100e0044201030741d2010740047d80703034062001408003821803900115040f420000050036151000c03c0540020125940c3c2c00c49054180001c0c4282d03103038180c009681660501d0390341e242007500000100c4882e0280d20b00b03082c0941e90a08200d80780380345440000d604c1810856408402985500003014404a031040380e860f175a9542c1101d000c91085d0301c601422508680e4001600300030220282c400c0c81d0083c14110700d000c0803940c40e1828a202600200c0e000910001480f812580910075480980321000c002c00c480f08003800000c07034850052280150f00d8200040d0742505204940a03148903103c00540c0c2c082 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 26712460 1250 26711210 26711221
    0x10b120402011103030103032609120a030207060906020a03050f1311060409020d0f0501050303090307090902150304060e0610061b0201020f030d02030402040e011104060516020d060e150106020d05030a060905 91
    0x811001d2444130b820030640444c541d0700c03249492070550084035654000d1002e142f442800e440d03a500a0807410040c19400d0001d42e010914134012404924410303200180c0d51070030f1f60009000c94101030a02c07404286040c003000f42e001c801070705406c2c03626000310b418084c1c1606200050071500c80c03030b040740041c18004a0410000d40030360304040c22046040350148132581e00c5d0800d00d6628050b6450301c0c0c2d41540026010041c8031b04690000c05824000307450044a0036400780803e00b60b90003950202c1e0b18503587c01040e241c11605200c159000840003008070038882c40e11000801d4410340051039090000200104402c581c020041c0b88140030b422010f0701e03203400810300301c0c2000703400403201a4022424400b0414019106100314812052099507031401c00d41407910803242600712041c00748046855a12010240c1e03200300c501c0500c1c511500c1c01060314640c40b04614200007040901050b00070b0741c00d0040c00040d40101c7c00c41a04240c52402c503450b9500c801002005d48070b40c0c0d0061410b20300d0b0070140139 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 26713710 1250 26712460 26712467
    0x90a0513020a030e030f041701180b010801050105010503060d06020307030b030106260708030301290d0504140c10030905010b040c020a0c1a070f030c02090705040801060509010b12040201110303010303 88
    0x42d8401c0d40780c604105200c074101c41903407284160341d800001d607441084244241d1603c0c540e5541041c0c0350100024405e1051811904442e507a50f00c1030b11515010382c0104200c00090080d04d01400c400c2c40c005045041c1400846c10101d24480010501340d00400081c1e8058869440300b202d01c00010024009a951070709800c0a480b00b640040010a5080010464003072001490700b04995208008500d941c1c60115020342030781020440b1102d0500204400c500d414441d005415440e030700040004940c28949032212300706540c0c12800d101d42d00030040d00030980d82d0b00c408407a00480d541c1408a40c040b05464136500500860400036401807070304014612181d4001010401c2138803c00f015840c4a07240c140828040807260001560104100b050400255900400441052107810b103200c16603410ba000a2812070102c41c240e000542c080790803c8074190900804d4020030041d03e03441101d504140c4199024400c0d5000a0707071008112000ca42164070402544191481c10f0782942d403207503107c1c50004c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 26714960 1250 26713710 26713717
    0xc020f130506030c01020c0901051c0b01030b0105011b0b0f0a0207080f0703020c0316150c060509060a0b0d02030a020405041703090d02060a0e0c010c030e0604170607020601030b0c090a051302 84
    0x1140240704e503030500300e11540001840c0c41032020041030b20249a18000802030b0403900c090b4114801e807205084800080e06201c0c01030702840c440c0e98109115030600d000184250848001c59504206030300a503030104007c020400d400112202181c8880e42d40c003200c0d28043d01c60560002c10846000500c80007603c811000707001d0b540d12039420340c0c0200c10f0f640105541d90131442000c407442190004200481c1140411501e400803090030300b501c0c14440c5407035907000c840301183e607007040380c01032010003800c8681441411074a4404458008161700d064000c42d41d00d450300d150007800307507695101080500c0f942041d480d8030040c52600582e664580310314550344a03440c44151740094495500491480c0d000c50003500da11884220041c11485030820044910814201c02a400d00c04c10009440941e140c45000b40040c1980a44039504010b0f618800791900d10014201400c540140c1c00610010386800c18158000300c0c00500c01e17407901c9900c000684404500d0b4055a84000400c50b004c804543c0c1d034019 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 26716210 1250 26714960 26714971
    0x110d06091104081507030908070b1503010c050a0e130516090e0c070206180901060f0914030604030c06020c01090c091505060313030306050604030602071e11010c020f1305 75
    0x3880110041d06441c0814002c60045280580001d182510140030303007040c45a2000c414a00800c61103595103030082d165001d04416a03075105884100a00003442140182040d034007500204100003024200900034000c002241d42049a80b2055100e20380da406000a00640c86070170410107801c184074bd803441c000d100c1c003110010076000400013a088600b01219441074907541d550b14034045041d401c011a6030303c45074031300041d4034a880a000e00c50301c8101005000c0e2010f41c032501d100b0b440b0074401810300e01d05984160501c0313040501580c007644010610ba60401d6150130415024082c2b450000064003d242c02d8050942c03904602c0307800c3c0110450080201e07040c00c00208055407902503140c0e00e084442c001c1640082e020000700d12290070760700c00390003018002d14000801c1174448002442540c405c0c2e201b650743c550041813980c140000c0c0031000420112002100c1d0760095107584000f07120418450303440c1403101700310504056458100d03002568100061202205e0140001c0150040000382c51 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 26717460 1250 26716210 26716229
    0x72d0215070c02010c080a0302070c030309050103140907050d080403050f07031208090a020906030a0b09160501090e0103030302070c08030a09150311030109050717040b0405150c071203110d06 84
    0x200c1d1800d40a555507040854042c0d4690300c21100c681c0f1014403682c00203082000b01607003044000b020801401034400a1842503548a0526161000040a40300203101201014041d5024085110000200d2401301c1d030007a00c4103500c5141030b0500c40294003d5070300240c81c5002e5207104906501c400314090060700d2145406d11160305101d0030440341c20a00301d030a04d005038040e0300414050700d842c44019921030001412142540c05507600c038024004d0507103011541c0c0d407041c82e03109603506041102d40040e1030207191074840d00745885454504101d040c44083c05041d0300107490001c1c8643d0705040c0000d8070030481201d98500012900502d80b40180c401c000e0380d00b84400c3c0f00c241803440390069984840310505403034110307400c1144420003041c0c0074050909000c40800300540e04282001c05510903809031006070040d240c6402e000d402c0c8407058240d8441e10001c10b007044025125401652203d94011026402140c2e031030509400a22500360000803c000100d03051004181c45e40200043e0be80c01203 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 26718710 1250 26717460 26717503
    0xf0a0201061d09060f041b0b0405040b0303030403050315040902090f0708070207060203040612090c030c030c05040924140c04080c0a0b0901120204090908030a1404030206072d02 78
    0x1948030b5000d24050320300c0308481d00070304041618030740c88110700d541081c007600c6401c0318403600c210b59907010741043c1d103d031042c07040100d0100058a414495990401421f42c051071643c60700da0740041c01440300400c0352014880355420443c564841d036202d449015400b40824400c0e050280003601111170454202e0001442c0ca000546260310110350041102d40c1c94000358105420b000041d40c0ba100040c000c00c2000350345071102d10101d924000f81c80011400b030000d48020a0643c00d20442c18980d40d040b00d4001e5041215910000704003100381454071807aa428241c040390100540c0001d001000038420820300e81c20706120040142c0e00c010011a42d2100032034003690084014810203d50501c01c011510704280700302c0b0a00d50151740c0800e6030744183c01d001440c10380c640e91020203d8032601c0040c1c4020380c01004011280c5e0b0544988008000c16101c0f4100b18646950000d503a108000c00c51003c1200c1301c02005226500016482c110030010104c40c8943c035001c0100030741e681480c00e854900d480301c40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 26719960 1250 26718710 26718749
    0x203010c110d1701060f0210020d02071403040f090e160e0a2703030207140706030603020406060503100320030307050d0e0d0302060705030c091305100506040b0904090501020f0a020106 81
    0x180f00601a0840b240b8624403268038101058810324050102c090039030240302402d11034101584014001400300d40c1d40162200c40034100300300842d000402c1d485569100700418004401080450411150300440120317406a000301e0705800e182a18842c001c1c200c923009002724002c445418a2481801614801c01141e5545207100040c3e000c0d09030103481c1c0300311500d00e03003010a1180d0000d001f298003d8a21442480048a0081c58141c45a11840010780d9442c014021854640103d00050035240f400038214241180e017646d00f00007910004100006443c0c0078072826107c8030343e881075000300070306032510b80ca03071030800944406602007a040040c4040e86040d0302841c0c90f59100003490b8043d4003c0000f6620880d00380c13503580c0040d0505040328403d000c03420f5140c1c6d94403449244c07800100750118040c1018546031201c0811500018402c0d4001d110500030140d402013030b10000312003110003244511090810900a2080030003645d01250300161100f03055405420410485416288001c0391072000e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 26721210 1250 26719960 26719967
    0xf0612060c1d0a15030b120d0801230d0c0503120702030106090c02030d0c02070302060309030a1e020c09130816030e0312162103060e010f030507031203090203010c110d 74
    0x907002c1403580120416418010484484207450300403030b0905002458003140c0c0300007000507200f082403502591042072020404d5900000c4107006080382403426825072408801d4541d05242c40c103000d8041c1070031782c8640e01842503200042004000207010f0b11000c8041e1604c1115641c030585040c2e000b0344c2020000180c0c02034502c80e803402c0c0c500039070145040001005400014068540320b0303600b14071071418040b0151b91102c008502070291000196a03407909084050000c6843c41440092845d89107581e855994000c80e10740500781c012074245d80103079038100051843c0d010f2a840605000c0c4c01140710301d9551845400000e11902a4645071120f281e45410580e0b80c0321100243e000801c0144103101da81030f11030114001151050300528a0501811170000b40c0d6000c81c2c00b803a0009441d120101b060241040d036047c090401094013400b107a0450700c50750760f1000203220081a04044950940c00988a54010010b0b941d004000b8002c032482400000e00160341d81c824030042d40100144000000d01 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 26722460 1250 26721210 26721257
    0x111040311090a0213060e130e060a0905070e010f0608090a08040b0904240501110a12050f0708040905060f0103091a060301020c0708070e18030405040f0612060c 71
    0x9001d01014028046002440800e6001510301410280c003070243c540c0030034180e140d4202804246e40c0306405980d05104000c41042d25942c84c2d6a518980288402d0030784002c1940c640c0103a000402088076081890840e1600e02103030702032400440781c5400802c51000d001c0c0e020007101d07031942d40c40086413200341201d038940940604c002c0a88008204c200429240304000c0c10b10000300900c0000d08400340020088d011340c0c411550f4000801039501407080f0341c1c2000d20081402c080d80018012810182d50380d1844070b000c130900f0420700030041014440a0041c1d8100c604043d441825942c840c0c0e40c50680c00060030701603c0c1d03140702d0342e80d4041c2c0d5411948a440743d417201503009100d8800300c1c240300102c1c0141000c040d050716019502080070003402c00c01000030200402d100ca004100c4585031640c0c01001a83c09022416030840403d03d07503101120000a445c00d650b0116800211080304549901c0100320a501c0030152541e0a4000c105000702580003001040c0b06444d00c085112000c02c86005085 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 26723710 1250 26722460 26722463
    0x4090e030a050301230303030a0e01060602010e0303060f0d0c06050403050105070302161203061d040b0c0a09060f0e100503070206070201020906040e15040e0604030212090d1e1e020301110403 84
    0x18418801040031700090b10455034030310702c44200302d8621a1070764082800c551046070128007841d12007022074a08502407140c80c0003058944004c00c48565003448040e04c038840501068403c441070303881c01c601540c40e205003400f4a9480382c10b030400590340314406002a08a03200c1540d065182c030300010f000b24002d0007202c111441109000d10085403c0da203d00700c4881b0242400704269550750040307450050001040400300a00008115502e0645010492803a00400d001d0680c0c605000310340d0311903040500982070715100c2c244a0b403c1c03030944104a8030328414408040c4c0c070510104102092175040002580a0740681c0d003075488580d5180e00c140d00381e10450f54401e4004004010410841288501e050741001415070200b84907100c1c1030024056801c4500c3c0c801c491782040c82400101501000101041e0a8550030755051048260001c1d180070070b00c000c0036121402403010302ca81c0c00c0004200703501c001e900080c81040940e003014042d040c012070300f404a02a42c80e2081c0458024080030541c0c0849 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 26724960 1250 26723710 26723717
    0x5010501150c020409050c060406031509020f030105090403020c040c0f18082509090b010501020d08011805071b0c0617010305190503070f06021c090228080f0304090e030a 75
    0xb00c00560a0000809507500b041d03505000c0c000c0240696942e00c0300410040103a507071b0110781c00014a131304080d10b8016522810b103007441009000115281c50090740e044690441d19081ca503961400e09070309044006450031350003850031008501d5190003080e0f04407041c00c55550115905800d0249010803096800384207129030040307030880445404041056050141d005081e0400f99031b40c403000301071311920801147d441c0d1358000140000d5a040050500c0c11040d450942c007154504610f0044408088060f000c14035160000180402e0041170b90700c1140d000e2824440e0000c50718100700d00c2c806070b00d000b01e1000600307805030180321072080401241a07e8104d0060304506110004505850481c0e0504440e01d0000380a4900800c4111000e8122640240400740c3d807280e0b03c0030354124840d214803240145a282c450b001d00581c6592402d88058445034000c00d0304540528841a0744004580c0a9103003846100b1898a26240100141040325107588080c0310781c2a980c078a1588034021211101d001 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 26726210 1250 26724960 26724977
    0x50f03011d060d020f1309020307090203040314040f03080a03110d06030b010602011e05060a0f0806070f0914090a1b020309040e010c020d081902120603150907050108040219030f0501050115 83
    0x180e00e40440301003c403803406c1c039000555003915808039041030082c0d844100420b90100402050580001d5028200e0541d0064545854200706500418980d83e000c0588241004203003000c000d03000e90b110241c9400081d9041e43c982100746214409010036000440d91444080c00019880d40140120100d034000321a0180340744161581180003018000c0003150f00900031031002446e07030101159440504100f034083c1c485440e01070000351980c0c5081c9407007003c01c20709000800900132280c021a92079101260050030585596611101501e18006401c5031441e0f00c85084141d10f80001c01801d80d2a4203507014800c6440807440301d030880c3c00c14100e54000d42c005042103035445200c0d0000c1540203180c5006401c00b0a060300c519000c9810828115040107808002d2191783d2130200320b918049080300d03050400c5803400b03802183d1500035910445050041c802c0210342155a030051181030506250804240660b5a0404081c00201050f0540325546024004505181200700f865110052616400341 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 26727460 1250 26726210 26726239
    0x11010909050601090519170607020601080a0309350307020a05060c150c07050a12080a050c0a03090314031f080303040c06120906062903060d02010c0201050f03011d060d02 75
    0xa0240c0d030091b528205031303200c408106070105442c3c800800fa8000c1c020b107070380c0c6000c010103441d100060b00410035580c0300c0c1e2640720000b54004244410303220104088481588541069081680e1307100c080c19100400840c0f40e030207580000043c1404500807907441100554035024400540b1524481a0302c030380120689007030102002d01241c4d000340341190307910f1501c00c0544a05040c64480709040b81c480404600e00200d00f035100c030349650040d084400c10844c50410500389640d80c42095607070400e040c2c8a0500d07100341402566203100c3c1c10321045020b83d0b01d10380301a02d0001442d4618010301c0c0c0034400800828280c00010540380b065900200030900a401d1000550300210705c080d001c0c50450b21a070300280001d03034074000e0340c00030300d83c0311180d505402034000781d2204c4005480032028412018400c04c106a5590180034600c1a0203007003d0445080900040300c0394420034402c0280c03250000000121001c14005001c40c180c41d24544a0312a280d01c2c0410070060f51000020b903000c0d440180c41c80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 26728710 1250 26727460 26727469
    0x904090c0e16091202040b1c0605010302041d1c09030b0906060a06020f15150d060f0c02190b100305070b04060906080103120324030f0b060a030503030403050c0106050d110109090506010905 83
    0x20106100242317810780c2115002d0035044210309204003210303402e8852004108504150081001c5000c0c9604440b00c0d84030390780c01880d642e074107000c410b2218001c6444049000d90092007010059900104400c00c0c070702c0c0040c40c15640e101f00f80c8140b40144800f40000540c2c91004c5880e48940304808080c0090f214010307034006080c103010b040301c0c807600d65031080c1c0901e5940b20003044100c644588070104003141442d0301c410031510600f112101f90341259aa214640b1060807820a05940c050601c60032034458080c4d0440016050308010203c1c803c00c00003181101d251009001103d13403d0b038a807102141c0340c00007147c204500307200007003210b10741000e0042840d000e0307000311005260701c0c21303150200300d030f4505640c0c418100c60384150b0350b846599503108140315070b504580d80e00000a940c60a41302c1c0c5140c7c0c42c1d650300d04c0000d0000d0f04001d00881c12408002d403e4005c000180b200818006c071000050404038907144a014125002c5001d1100c0027940031907a0080503c140c50585880a01c6443d000500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 26729960 1250 26728710 26728721
    0xd05030601030605060a110d0905030a0204020d020f070515060312180f06041d0f09150c1314030f0105010803040603110f0d090b0106020705060a050904090c0e1609120204 75
    0x100d05043d00c2c1d40d00441d050300c45901408954110707990f20001498040705c01400c100c0003101e904100880c0d04810320003901c0000d010101c05038190340059442c0342c0310619900174050b600e8500f400e008000b4050090140000303040c817000c040c040304464262104801c042c0d4403402690040c8107403038180102c1e5200c8500300ca0b4401403410250049a0074500c4100056865003da045030030300d10702040011408140001d28070780d20124031101c0722440d0605411032a5030702620f03580d107100072818070b0004980d00325032010350301506a80c2d058041c0070ba444001c0e9010140b100401a40644522103507400019414002c25040f80e412001071840c113420980f0403005000510643c0c0003e280401802c0702c0c0707140250007004024a00f420005000040d032400629180741a40000304650200d6000d00c41c0740c0d80c4004544904105041a41e134503c03032800480d010701100c81e000307071141030078507000a051f000030203070140b040890441190b0105911001641d0142e034034020054003070f950380e00c594014101769004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 26731210 1250 26729960 26729971
    0xd03050402010c0501050c191809150801051e060607030e1201140c070302070b07050303070305061305090f07060f020a1514011503110306090f070306150306050901080a02030d0503 79
    0x6600902c1442e100d036400d441d0191480d401028000402e08d04401c80c200c0c0d4641c00351441c1c94450010320116858507240c1d03805004030107140350f88000f030400f403d02124081005220030030082c0803a00d0414080c41012072400d120070020701540000401e5482c00208582451b07a250303c0d002d03404080c40051140c0b410a5040107000c1e50b6a0b01e58505c00300082d1a002881111500d8034695a001e4034500281040036942c0130002c4800240059800203a0100a8070b61041c024a000112a55103200207070a1400380e07440c40d80c0301c91811b800d00107881000b1450f03521a2100e241146e004036600c10302200c0c05a2902d6802005070400d00360a00010010791a000380e100c4224400b0030307202440f05400c80d4680080c2c0c084010558032040419999401d4060704d20060292581c007400c500e41303400456181c600040c00140513070006000580c425009604c00000740c0400c0258030180c11000310080c00810060042c103200700781c1a8000104003a0001d65544100c1c0d001d4040e1080c954520740a03691034001402 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 26732460 1250 26731210 26731217
    0x60507020115121506031e021504060e09011401120f0207050715020f010506010c080c070b160203060109020906090618060f04091805070b13030803041109011203020d0305040201 78
    0x88540035075030011400d8042d00901200000840e9940790404210102c110810703130f981c0c04c0410400c04511f10718603d04151a50491140d800c0403d8800101092500a9805001c0070046408103540346c0c884208004c82c1c0c030a580c1005070b643c03640c4504202d40360025610b80014088140d050350300070180c000b4000301c1078040000d4100a1155140d50400d1140d03001070701105008180440c01e00c0e810082e04210b051081c0081100d4204000000e0030740d0001140542403010010351441c910404001080080c0081c8407059116504541d081d0038581030240d06a1080c4140f40000c0b91a00071031003100d910b6400180128600452072041c013032a5000042510341c2c44c000d135040481c0036207a450007490114000b54440d40d5490030040143e0845070700800681001c11024140030000e480041c004007500d211b2450b9a855116050b0303a0541d000c52604010409400841030008000c0d0034050b00c020b000045405400980c0ca954640303072a1081882e028005911409080800500030351213503401900625 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 26733710 1250 26732460 26732471
    0x4271b03021602090a050f070302030403090e040218010e10050f0f0f1306030605040b0f040c060503100801090f0b010b1c020304020a030b070804171c0b030106180605030c0d020d0605070201 83
    0x200000c0140c0740c101c5e5007102c3c0136103a00400c0b03408455212540d40c4020203081c214198102a2001030440c0418004e01c00305000c01d001040540d40d4928050401d04801b40c9060a550b86a5018003841202178038003c400e0601100301060929010342000c04004020b000303502c0e150208020484200d0700440c0550b00484560610042034441d401058050b6000e4031001c141401c203440d00c0003091600410700c03804d1184100c10b100c0051000b211179011070307130345160940e00c030384516480250500c01540510050f618041d051001c021100070a0318825005042c100b0b51aa071391581d0541030b110703a1900c40b40b80d440d040c04080b0705900b254059a005170025010041c41750b260382d150503000c44255600e4000c40c0b031040820041182041541500f101001c2e1100e0030098000d0f13825074204406001d980c0d0b0705481e03c18960244d00c096202000500c12125044461480c142480c8000c200c14040c580c0603014248140400f418150301d00001150f0260107000303147c8440d00c4a0307000f840064001d60440d500d40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 26734960 1250 26733710 26733713
    0x70c0b090c0108010902041202010c02010e030a0f2001020703060e030f0a03020c0d020106120605040501090206131503050112020405070e0a080c0102010e0115030308040f020604271b030216 83
    0x14001a2060803000010312603120008009004110161300c0700022900400c000e2000e880507086066040c2d5080c2080e440031100751005941e6202c0940341176405124070981c10301800000140c5005041c0600550078800d03490082d103000d0704421805960150340056410000281d181e8030014030300f600703182568100079500e15003040d6544401c40711800070b0b4010500900105d02444002503000c0580004c2014601d005112084c0344116140901180d669900080c2801780c20340012040d42d60080284c3d94810200480e590810700314010040310b480b005002c080d145010b84191816240f000003640b00300000f50342040003500c001450300042002c0c0441a00294490b004020060070340700015100c2d4079a2040028215050b14143c13042c240e0502c0e413020454a0100300a00a4941515203407403240e54500786503c001041000080d000340c0006400a4030007000c0d5040e07032108070340c80d04c2d083d00c8090150881003925424522892000038155841701041d000354002c00c90104880008030b60401079 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 26736210 1250 26734960 26734973
    0x4080c011e0203061003060602100f090609030c050f0d050409050c0d09030201060914010f03080705190503040f0e040c21020301090501020a0810030b0103061a031912031a09070c 78
    0x3201c0c00085055004018840185001054540e902080389000c0103000d241100003551103005003042303d1b8143d030321034804030328404542068a03159040401072100c020346280041030b18682c403900b502c1034041c0b50400c00c04250f01184060b0030461710303590a030816082015103c01481c01070030141d1540da013040250b56a8140b4000c02001c14001d400014220303261a11b11003d40b240c802c2c65000c07948030240180100c034500781c000810390303410207100381e19501030b80b038554900344035260751380300398608041420304010000000b0400d0391008561500042c2e65061300302400001901c00900050a144080c0000381903800a42c11124801020f80103410701d44d000f203801c48440d114203803081e03500001c014118603080700b107481d000360f000a450888a491030b00c80004151060100606541e02e0b0250450604655071010f4000d00000b82038855650f0140060050349601310700c203e035034600100320800c1640c001e00c540b20b40449010050440110070b9010419003933001010700c020302a201c003000c0c01241c01d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 26737460 1250 26736210 26736251
    0x4061203090806070f090b0903160306060305010b090c07030c06061703030108010b1017040201020309120a050106080d120b03190507090506060a0c0f2303071104020301050904080c01 80
    0xa074807100c45481c00d0500342030400c10000c0c11034092000f03d280e90200240d200d4101c0c0c0848400c1c400c216107c0710b40314002402c108072002001c5180011003004024030141d584500112403261008109035000c07c814072819200484102c1c002c01d070103101081c08a8014820801c265200315000900c050b03e8071880010b00100e6100f0418030ba201100511180909101307540c59040211080018a0b036142001044a890080d6040175102d1400220b011a4020425139002c0d40004081207254030100ca500c03962540e88100c107031440d40c24070100041c80c420101d03030507803e142d055031000c44243c0c2030302c130150150148026080d01031290155500c102155034580c0b500140c820000780c61807a29280340030f400d581c406455a480b9082c100098801503410441e0701d59007580c0b02e160486450743d241480d0725059101e07490001170302a500c104c0461100040000c240d81442400a0300c01c0300722900a11040307020074011550032030000c40c0800c0210322214040e00c0040304480c0003045884040b0101e0f81c030b42e0f9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 26738710 1250 26737460 26737463
    0x5030303070f0908060c0a0c050c0603070e010201140103030813050f03030a021201080d050a120b03070801020a03060905010b0307080405030f0d050709080619050631050105060c030a0e040612 84
    0x8400d01210720001e60f122003800c000b0075103040200b6244c10a44000070080c80f500102c0710034403079041043c404005044c0704d807600f40c2000400c499120b2400f40070240644039000d081c42c3c015403904401101070b8182c41c41450507685c0590310741080c0d540f408242e2015000ba442c00366071600c22100c0c07128640c101040110712407248800050b13110420f44180e1040300340c044e002003160b42c0066145420003903112081d1203041034070340b411011042d60800c80400030922011000d4050141440c0800c40160540042007612455901042810358400c20001200d0080c001c0800003034080010640140c8030310040760300580964180c82ca022aa19401411507000744590081c407a01c4000300078a103a000543d00d0300810880c070280010345450001408a00d08408a80807443c2c2e881012503520344802c03585510f10035821110200c130440c13814040200120800410841d00c0c2032200205071824950184c5241042c41002142042541070b41030f20f041c1038418031745e60441d5899000240c00c8064480345020076 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 26739960 1250 26738710 26738717
    0xc0a02031f0c0512070c11090406090308090d091401050412060516030c0203030402010c11030d02011410030210080417030c030a110a0914030f0601061806090501080f100503030307 79
    0x941d07045000c00b0341d140c0c0c0d0030301c109215050021414104d54029441c1d400085490708405140c0c152504003d040b034201d00c0a1f4001164404003c1000b82e1a07109450300c5009464070328495545c4c09120f666100904501d10000c0d49000080040d0350107451803500c00d613014100681006e8403031803000c5100d141410107540858998041c44850140740007039050241c0189414000c2e40d880c15000781d92480090002410010482d03001d8086c00802c00407402c1e81107004040d14044851080003d0280c107114040c02c00c100d120401060b09481000064011039074003030f0141030307150a030f20001c2d84e00f104002c20940c3c4020624500d241790070484401584108003001d071a0303440e0300b0030414810850701d001e8000c00e5019020040c2c1e0103216040078000d0204c542401d00d6180081c03140d400b1034104040401c00705468401c010020079281d4125880d0304d906007511650210700c542d903000c101c0301940c562090b40d0200e00c1045c0400c50141035541c0d1158482e905a860400c110703a01c10219113158000c035280c2001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 26741210 1250 26739960 26740003
    0x101b03051017150a110316020705270c09030601030b090307050102130326091011030d0605010f081005090402060c070f14030102040b04050405040f050106060512070201051603020c0a0203 82
    0x40c0001800003604091138850422412502078501020313884050003840c4211507214284054604c02c00c60310015010181c442d00c84d49001800c001c07980030076014038900c420000c5002032200340748034040d0b50030000020001c120a03480c58980d40f030140400f4018880e180070030041748000c0ba1090005001e609030000c6044d05d01865410400d005108421102154030b20718172a0f80a850b80d8201960400c2408407004004619060402c0c2c0d01b1b42c01f5249207503a240408641004070031615402030341103034400c0c0c80b034a400c0c01c1d601008446c5040f04641868200e140920207100e9030604241c01c692107440600a280b501c2c82141101d071030403c0b070760b100e41020105841d0501206103208c14042000100390025400c081c02e1103813170f118501460041c580541e60380e20003c1c040c00b804541019001e0b41002c003c203e107036154100207100b5405040070320705074011500464000351051080030320981a1710b080010843d18031500f00d010394007140f050708843c81781001c2d00015075000e01400c60400b0305010070120 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 26742460 1250 26741210 26741233
    0x130506040503073f05090a0b13080d1205070c1a010501020717150c0702120a060c0e030c0d0804090212041101020111040614160b09101b03051017 64
    0x14003a0b11003500c4020324145241d041107103d24146807100409a000704a0202036a0204944501072000ca047d84032180c4000050518600070050202400e1400040c25482c1c440e5035482d038074886c05100000241e5145508141c0c102c0b9a400700d500106a450a001141d2144d00d40d00d8a1740d040ea600c130040076890034010031866030100070b164020a115210a00707440504401684ca0f0309490301d203110f500300c4841c00955007110440c100c071420781d4003e04802c500e0f50440c4100341d03070716010981200c0c0145085403010b1294054031043c1d4074030300010020031801c00114240034042d40004000c0750000e009000208000b0150700103400540020740151b003442c9020f08000441c107901500080c19640340088980ca01c42e001d00c00c030303800d0358600d0400291568102c8ca45280b541f1130394004100ca22803014501040140d1501d5140c0a841c1c41001ca85945418401403801c0350f0103d03a8a0380b01500d00401c44101c81e020380c110b607034081580c4a0700710485942e2001e075000540782250b0301e141038001070b54254 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 26743710 1250 26742460 26742473
    0x315060a02010e0f0d0903110a1710140c07030522080a05100e030f0a0504080106090902090615030105010e010210061e09020415030209030102070606060809120c0309010813050604050307 82
    0x4844c903402c001c00c030000e40418044c0030080d1a01000d013502002d45801c441688807000094000d0001000780041210308961039503e5a00b171214240800d400c0c980307540d04514607000460701981e9101a50f61600c0364560f4195101e81c4030007001880d4060f400300030200400da0001040003890000040c14080741c03149005824010b0b0003840c00010b511780301c651014030350b0000540b04000140300c41c0355035030007264070152124080e0b903000c0001036007407150108100c0d1b1f007a00203030107451003920392a180e912a00f041008403858040030000448061004100941c40f4110390601041c041c01541c000e4010300710036a040d40c0a50700b0607070030707103d4002d0302c001c400e000026510002c24190f2800c6040c503003445030004841c3c40c5414010101078002c205020503543c290304a56202c2d03803004040140f20340d0381c10b024000000895038080f8600951174103170381308410134040b1441c0010030f8000d9403609a5000043d100503502504241c03080540c120403100183c0c00308801d9008500420046850f00590f10740035 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 26744960 1250 26743710 26743723
    0x6020d05030405100b03030409090606091b020a0305090a030209090f0c0904050604030c020105040b030f06010f050412082a0f160501020606010c0302010f0f09020a0503070302060d020315060a02010e 87
    0xa004106040041002081001ca1001c1104010398004240c110010b400685140104e800c503490305460304480c0c00030072540d0b42c000c0c411188c0c0100c0c180507008409600544003004680032401507000b0105000001340300324020318070481c0080038103284a450340c0100b04038800407038228806520002002400e16010040480300070380840d644e41e19132400d5507a00d0348032540500004c091200c0c000c00d5104589c010001d03600030b0640750801b02e80300c0c50003240d60110380340d050b00d42501040c0403200c089865031180d030494007a06c401c0100c01d80070350201d1395642060b03400740744070a1003600c0075058088504a41e8200100d089000c0008003000090900c1c214200350350802d1002401881d400200001c0e6000304081d6804036003401d0603503002149007402d80c05010260407207400185442e084110700001d030351280485a0080d100300f54100d803a502070541c4c514003400083c1d4030460611000c111828903800a50384091040b02e101d0040c021000410810f42284d248000503035121868003485103400c1165 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 26746210 1250 26744960 26744983
    0x2030d030f1b03020909010e0412111c080f0c03010b2502030f03070c09050105010e0405070c0b01120303050c0f030c070f0506010902040509070f0e01050c0a080a08090d0c03090512010b0414010602 86
    0x811074107050740c2b40280542c10962080600c410600940c00c5402d080c8500c001da480c2c600c1c0000315149c030450008200300012500e50820303010000c00b0403080302816003564103a40d89603100ca0301e800c410035040314180303041901c8031a800050314208401602c00f480100c4002032220011a201c2259181c08000000940c10071000c003460328004204603070344014a215000030030303200003403c0c0d00c807080200c03500c0c83c2042000d8040e00c1200b0001034000c1e01c0964500005019983c10001900c0389070b505502803140325085140701c04144041043c442c00302000300380711841401300565500c03240e904c5504000c0240e21001400d0f81c0442c04210b03d0400b00c6603a503002c84c00d80b07061201080000c02c0038001755100400281080000310301d11540d16410031000c884503400c00d244503142d042d0900c00805e00303641294480c0f0107001e000030781401b06000b034418001c50380c0d141d1030745918a8107081c01c0c001d109032240320394580d942d201c2000d12241d450b9031040c620404120780300c90071990705149010f407806141c2e111 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 26747460 1250 26746210 26746229
    0x3030c0813030807050a03021b0303060112060311060a020a0b09071403010c0207060e060409060e06030c010c0c0b03070306090906090c051008060f041d0a050c010c02030d030f1b0302090901 83
    0x200c80c00000c1c3c0c0000a654004982d0425584450f510301d4224028002c55844000012100b114000c5081e4000061031103524240d0b0303420039105000034110140d42d100d1000902118225402e010b45203004005056840d86600c11114442d81c182c562064800041c1c6410700c0d0394110803000e1122800c0c00c07030015030b180c4041c0c00074490030749120002952a071040c4035000400c0100201a1074542d03030070b030480d0024802101c0900c80181c580d004c1024190080c1c554034440d110f48201d180203540191030080301d064000c00c041c0a49031a002c80ca680d9a40000d0504c1c003015a600710110700420a44500b5803403a015100c001100c100c285040002050a07400aa20404107841c2c4004000c0e4407482980c0d1007038050700c15208410341701001c40d014040042071199850801c80c0d9000030584002482111640588200c81c10812603500640b1041c0c400c16000c4d4258010741c0e210702c007083c000d030400020000301010006040090148038060080a2100d40000075000a03000c9514941588414050700390080e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 26748710 1250 26747460 26747491
    0xf030302070b0c1b150c010203060f0d08040306020a0203040e04030f1709100f3e070215070f05030406090801050907120f080d1107050f06060901050d080904060303030c08 75
    0x142c002e81d901014a404e1407400d8144820415075181e29400412041e00080303c941c803541c4d0981800d010b90012150701e40100c110b2003030030b00f41d841c0102107141c007681c00500041c50309086481c1e61020b5444142030500303620041000045480450608912843c0640d81d504030305019144002c0410a040d030403144100c0e07100c1d007031006800c03011518207580c200305040001d039800c04104040184c620f14500068000071004c03540943c001a41c01202c800124004040c1d800000110b102c142c2e00400030065006504a81076403084201c940040140702d015000d0801d2070a0b5560ba00303469035100d0f410040011f180e10208011800c400d00a250b00480b2520141505504080c1400c40301400b502c030161100c0c0c41c1000140901091030b04590f1407000084081c00724074100c484400196200344012140c03480340c411600208900420381e00c0c045c0301d0040031890107904e00b20030000080490b0100350340810f000c0100c101142c1d940c0c460b60005503c80d8401090201d5058406042024020702403002c4070141c5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 26749960 1250 26748710 26748727
    0x70306080706210204060306080f06041101050d090b190b2704031e021c0503070e0603070311030f090c0d08030f070302070501230c07050303040f020d0c0f030302070b 73
    0x200341c40e0196016850000658030880d078105104114100f00402e01c94400607000c10101d42c10380141064403040303c1100d1880794442d40840d5070390f404680251000d99444014411503100f10300030b180740040000082031800013900d03501018102aa425203d01c829084044861001030040034000c00b01121110204401c0142484e020f046160f41d40d0140c0700920002802c260007001d82c820750440842c4010b41189002c40040d54403800501941510969490030002a070b104108480c0320f2501582c4d00d5086960000500045410181111300ad05032504141c0780280c0c1210080c510848039030915074045d0030704e40030003805d00d1000b0308c4c4240079030900619607000c6082d5038200c0b07800c5102d500d110a5240c0d0341e803400300c00030b00500600070455420604030540d0281c5540b0710540c00389206c1690562610344007404080c9101d201380060480e00180001400b281c2001da01811042c0050b003450f00c50781490350703034400d01010350300180c0d070640c5003201c240123056042040c50f001e0040c0364120307460321030718 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 26751210 1250 26749960 26749963
    0xa090317040f0e061801030b04210509010e030304050d030e0f01020a030507120e090c0703020c010206010609050d020f15120c07020112050612030d060501080901092a05090703050402030607030608 86
    0x1c0f070041030520381d4034102054035601c60946036011502c0700b0310841200c1d612854000d6001005450a0300e1601d54810f000c540d10001d901c40301c940001c80d0300c80a1804100d03100554090810500f42075160006000000d00d41c3c8480c0303822002c0318030a556115009550008009600c4a040d009604651000ca04540020341110842e0103c80e00400310174050a020542111044e20107201c0c0c070b8000841d00d01b400b17040c0c1940e0000c3e0941610036001e40c3c0f00d18643c0401203949460912070000040d0700c001c801c00c06802d100b0103083c0f1307c0c1c0c0013400307107114182140003040242050485c011100d2000103210701c68a00307844a00c6801800303c0803e14649203032900020000802007051800c2d00b0b58400206907160740d45e1111000810b807000030b480e100d550144143e4001e00b214454240030a10040004282520611800b030001d0391002217030400440328010303082c0400510440100c1041424404511940d42400b818803450b00c0b50790205003442c0600c103043c20068081e140009060800f02c080c03220810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 26752460 1250 26751210 26751239
    0x1018170307021f09120804080106062c0105090d06020903160e0108060613020c0102071502040603060e0606030a020c0a052a24090103021309050402010207060507031b030e04020a09031704 82
    0xe40e44080702c1707202c000e802c0a00051241c0d91054015610700000024490b40141d5a50003045468803840360154402000301c0800314080e1000340000d4081118100e103150000c182e1a840c0e000d100e0050500c651303400824079008186a000b03024801c03060041040401c0c264489d07001d09807000c05040d440c01d00101280c844022104000b89943e00815140700c440025416509100e4120031078410710704030403c000e07000b90b0050203010002400c01501140c48004803034510b010b140c01030003161a55550445440c001d401c0f40501c1911409100340c40c10219504000040c101004010303e06001600713500360b00200700c0c044450500484942c08044001c0000d8101c81280711000004a65229040001203000340301d52100100305043c18040403072884100d0380080c1c402d9101fa001c440510751603174000c0c1c4550045c040b00400040c3e0381d0000005111020400714100343c800d013000003540f148840020b0a030f8110700e01d184002030300e0b44010000d112501000d0940010b01d8038a08dca05410a03c14141180 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 26753710 1250 26752460 26752469
    0x50d11060c0a0302070b04060b0307120b040f03030605060c0102030a05070306050f0f0a0b0c0f010c02120316051e180a080c0d1b030b0103050d020303061018170307021f09 75
    0x700030480030451400398040300e01e041d40c1700904400c02d143c140303080c1c001403e6840700c02c1d020f48600000441c514000c1c21b01003d625030001ca200da0a0b41c1e441c0e0718500d24600d014411010181c88460002d1070740c461704050404030800000258491a0120b14203040300d00c000c100208150408008112545401c0d182e04a01c1c0c41c192860f0320f64140c071b0700104416113402c0c0d200e840d2001d0b0014600143c0c080118509c640114941d0080c4040c40c0c0c1108e04903a2071040060741c40c074640041000c60700740c900140c401807440c1d409052580c100090000100710344c100301251915040b000140204040c5840c40da0001c0c03100c03085441c02c20b0315042150311643e80795101c3e907a9020b80078000307200d428400070729140404402a00d05071141d45480c7c4c90030b882050002c4c0702c12920740c4520a02c03400f2050000c0103907445403170040c21020f504010010200c69600251000720360b039000b407150102d1200b01d100080c09803000c4200045950704118414004c40b0840b9050000c1c01c524a4001000550780c0038442c2c0003201d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 26754960 1250 26753710 26753731
    0x606100509010f031509090314040e0105090a0906021809060312030a0f02070602070302010606090905010e061e10030b100504081005091603050606040509010e070e070504030b09030304050d1106 85
    0xf40d02d402020780081c000c50010340340c841020080095007445680040320410710a80d1460820400e00d030b12a1400d0084d40502e04005075120700600481c28a0040380382d003c0507101021038a03038041e84409003240d00c010070031210944404205000e034100314183e60b0308080c0942c01440f50107410b590010310b900024000704080c40d202d05000244060725010780d0407407a00640b003155160003915019000308494818000418442600007902008034413401d81200d0004680004681d1940100101e880003010300510b05800005014001d4413050740d40803c41d46146c5000842c0410b0300b08020556040044010070403200700024002071a001c10050111042c41c03e011a8680328840101d041c1507210900c0361f034003080c0700f02c000300b8000002801800341800340ca0030040d83d1240c42903142601d40c401107100280c1c1c481f000c100141e09402910950006152230f00904140d182c0d40c4c0c10342c8600742614501c1c3d942d0700100038001480024003100204074030a04100034094001c1c908a915050020301041d800d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 26756210 1250 26754960 26754977
    0x609040803091f0c031415040f022503080105120304120c080d03060905011706060d031206030305090f040e280b010e040c090e0304121b0b0c060610050901 68
    0x100700208084200c1c20100c00403802c0c000c020102d044000c010000000c000079041c51400911400325406c014000d580c180007400141d0002d109000c09098035110030846941d00300075002112aa0391001454800c0208003480343e043e2600b8010520307801070b0412072041c840d000d414000e07030340c0005c100d030203c0d402103040b4010030030036040c051290744003580021028002c0c10b00000d4659410b91165060350711500341000b15989500b0307004240305850208800c940d200d4008203140746410f48000030b0030349c481e14000495080d046049011ba42960b8000c8004c80c40209840e0b500f80385c0001c06214500701928100302c031781844801c0c60b9031444003600200b03004000c1040251400c0310484200c2c0c1d866003246a8190300c0d42d40700c00310f40d4400c070100d9050701c101c0c50000b4003260403401d03030007119200e0017200d00441c1850308190300440f1000d1760304802c50308500c1102506620384c0000c100301c0d0081c094220641d403038403d10683e9506045c0028802c5116101d400e8244500f150030805072140c40300e084c68101c03074 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 26757460 1250 26756210 26756221
    0x9070f050f1c0c08160b040306020904110a0201090b0606070206030106050c030706020a08090f0a030f110f0607081009050906040f1401050f07020706030219050a0909110d050106080609040803 84
    0x95a42d044007140001500b2080d4034024000c45001e00e40c203c5518208842d51040d51010500d1480601e0050302010f0004100030004129a60003815000000501c000348440d00200900c2080d80400d10300d02c0540d444411203810301c112000e51399407001098407101c0c503107082c9600150040c4070500800301400300101f1660803072242041683d110b03d034012401c5684204208010303290140880700516944142c003034400c0c0c80400401c0c0903a219a02d6110140e00c221200e000f5500e40e0854510031003a403040001d06000100c040005a0164101c3d4450215a0424080202031000c468008402e1141408144a01c3c01380005130303540e2003034002101112422442c81c12442c07048400f208070405600b010240b2694183d122081d5003d84450340881e800103039106815801ea00a000c2c000c402346551034103d602083c0608000c148400c1ca52400885180c0c850448004592021545c400400300100c3c0d80c98030000141324140c094000360424181601d00a80082c0780044002c0000f0702d2140040301191 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 26758710 1250 26757460 26757469
    0x6030705120c1b0c030d14090a170c0d0c03060b010507050604060501050111190f1b0602060103050d03020309032205040606050c0105070822051608010f0509070f050f 73
    0x222902039941c000c4650341441c4080352015007081d80c803000d860140c0b41c002050481c000404684407132003c0e0250900110614041da40c024202c010708141403c10801c46085642c2d8a0440380a000e0300403a550a40d82c3c1010014504031020384040e0140c01d80c0101480894070805e110030440c4c1c1e2044002c140c22480100403952405a510010a188585030170300c010002207402180c1628020f0341c2d0060094111941c0940c3c50190b0043c00100d10f550603e288007060841d26085d5a46015080000300c0105528012500c11910b0748640b005030024401401005414480e9104190080c5025130940c104504040d44034880c00700c0a03990501d1400c000540480103912000003044010820800180c0e5984060304942c000314070b014040d441c001c0081c00341406004014004e61261904c01702c0c00d040c6c01c80d0400308035000030023941e0a224184030001d20b400f50700c031350f0400380460f03000104462041c1e001c520141c0b140a402c42c20a50807240b030502041c0304904000c41150001c480b5200181000d50105 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 26759960 1250 26758710 26758717
    0x10f060b0a082e060e090a1b030e190b040b01090603080f0c010e0303070f030e030705032208010912110705031002090109030501092f01021b120604050d030e0c0604030206030705 78
    0x103c6101c060744005403864115a80c0c00ca00e810079a40c050055403144c1e00031003220000d0407a580740416504010f044284a640302c0d8100140c0e51301212020301140e600440d2071000346030100c0d502a0400d0810042214003150a801031504403014404582582e407145034601030400d00703074507030b481c0401c0d05052600c00750016070001003c107090342c0c5d0f40d017850352000384405442c0d14008042420061092519071001045840700c40d048400707141441d50f20145055000428600b259079044088004580f401e020302c5031590144c0315070031504c0f140c0c80008015100030391050322001e441d00200c108004070b0f180452900821406007070016540d10613140183d50140c001d80026050f0b61a082c41c0108000c1e0076403d0850030410701c000c3c82030300c0d0400401d004041c00e40004490060304041c03141811040d2218140000d004001e000f0009803000414440ca0890b0031113040c2c0300c0b60311103c80b80c01025054802c81f11400380840103802c184403014081000351080d444024000c5500200140d2000e00c21002d4 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 26761210 1250 26759960 26760031
    0x1021005090a020406090c0e030a080a08180601060801061706010f08070302130b0309150c0703030b1c03020606010305100501090302130e03070807030e0906010e0409060b060c010f060b0a08 83
    0x10044246c41e00040d2000388000004407000c10014501d090880ca400030b20049a641d00c040401d00c0c12001e00c80480303044a010700140c1c240002c03100c580e14030703080c140031480c080c100c10765400105601d0500001c1c0007001d00301861540401100c140603050740e0000c400c0e0300205680c1801b99964031040d00c100d0084c4664100c01c8200409440007151850300c040086004060340000c54a4072076030201283d140c3c010540e0000e040c18410030110300003e019404c2072040c1e0310f0060940700090242240c0c0480034685890440050304017000300b00c069a010321071a030300000a90800810141080000b90509040d400040d00c10142801c60b1030b9045a9500041c101d1420078054135280d648903e0f15546681108a046021440000c004c03202402d06600484c402c540594910303649044031350500008041c0004280c0d0180c0d203416060456899810041100340110130000968200541030b80c4200c41032034009a9004e034041041c135004030303445185d40390021051a400c00709010030106003100e0b045009034 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 26762460 1250 26761210 26761219
    0x30914030d06030b16120f020d02040603021b0105060d080706060510110d02031201051c0221061311010518180114040606021b030304050a0e0115050901021005090a02 73
    0x914041c259400d401040031244118000b403030648550f15216404100100c8000020309041c182c01c1e0794402a030854071801034108801490503000610a0081c0c0c0d01c5a01b054000c01c0e000107038003000d044070000c1403981c2da84c440001c104600300f241c0050811141c0503000350400314080b9020342442080e038803031001014010800080a50405405401c840c0241503d140c1c45c0900240402e40d54000f108032408181448208052a800c06041000c074403900c2c210010007250400d0694016121903094034904c0301a82107806c3c120492014252422100902d029003a800280f40d0030000303051120340c14130242003400c1583e2900c0c000101c0020700d070b004040c4540d00c0552a0a110030a000342c200c0d0307505858020154145808400c000d0100b5a00301e0301c260001a030052703c0d2581c0c60080c0203056800010300405884c600b40e616000a8030800310758000c00e1560325080c004121001c821740482a01000d1402d2403810f045d01d210010b51120400801030f500c1c5611000042c0ea0b0031014801b00340d6140d0b0041 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 26763710 1250 26762460 26762467
    0x1209010905040603030f12020301081207030203120c030a060605071520030a02070b010602010c0206011a090316080c0109030305030f06120f010e0105010b07020901150912030201090209010b0f030703091403 90
    0x24006d211202d0004814040f0b84030710385007100807845008483c1600c500700018000c000c100d504c002c503079030302100065086000070303c110b03003000300340400715802a8005000c46031a8185840100101e411980c846400d010081004e280042c180449002003541050300001ea0104128811280580b030b803038140741c030140300004000400e405980949481ca00410f2840780d560b032600c0060f0300b00c480c1820b2400240c1d100400401080004001d0b6410341c00c0603800329820005141c0c0171130f240104203244030038070a8844c2e00074004030034200100c0580000074603100022500d5a00c01030001c3c88081c0c24030704080070340d10000c0d41c652a01100e500700c2c200c41c182183d100c0841c4960060080c8860000081a94240000080c0f003040440030354050780d4005003000001c2e440c1c011402210a240700f262002e00c00e465200040903840741c1c0420780c4440c081c1c3c0011508014a02c10040511416000b003040e01005010202e13000002d0b80a599000f400c0c0e0074009183c6245042c91001d080341e06800003000c2c0b1000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 26764960 1250 26763710 26763713
    0x705040806010315050c03060d02090c0910020703020316180b031507030b0a06030501080d080406060e0c030103060f1e020d0f0f0e06010e0402100c030909060306020c06060d051209010905040603 85
    0x1403403200da031140c00b1030030005e503200d02d540d80c01c2a00c01600c00560241c40c5800ea800946460001c00760000801c410440c585258000490500c8095408440242c1c01440081080d0f0a00303001e1895081c00c8071100d80365160500b29510042072508014148241e603508090905031020840d40490400a0703414144138501460014040c000c40c05182c0e006d00403d11000070f00600900996059030540c5d00506141c0400301d604481d00e100c01441500e0701c0351603c030300040b45107910300710a00450a4034036242d52581182000030541d10703400005c20119180ca01e154181c18110b404c2d49111040c5444007503550002c0031b030301038003511104034024102440d002459288a0b00c0d80d2040707204240038000e48003103aa0342e041003000602e040350040d4024420261800070140305010b8000768522904042d9940741d114005030080355183d41003240c1041c0c0c002410203070082e08200c43d9510480c00c0f140318400d8089607882d69141d06010038500400b0303074046500c1050b6802014a080540030190041002c03036906d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 26766210 1250 26764960 26764973
    0xd060302040b0306102d03030305040309060804020d02040c020f060a15120f0605060105040905040305070c05030d090e060102010e010216060b09010b0702010e0d02061801021002040e010e07050408060103 89
    0x15200892103203140035550060390601095003445035a41da8004100c161400515441c681c80041c20b42d01d44101c4000d0b000b030400c00e00b11a00700558085e030340c0010240303440d1070003425400d0590005424440f100c410400182d82e0100d04413036180d4140c0b808101501e201c0000da00c0c040054000010302e005890030020303c000b0369801130400b0074824190030f0703002d0307903484518003058841c14001c1c202d6500303039040c1004519a904220303000a41890410701e0103640b07491710011110f042e10704400040002a210080c443d000501801401084014001c0d5289502c009440c071811481514442030a413800500641c4c000e41c800a00240000c00a65441c40303540b210b4400328149100840e0070710701d0840941c5039030a00385442d5042e281c0382a0028a89000713600151505003940707012540c0115201401d10060b2660009082d0740004c0040990440301110000383c1003000010070611840c1c410301c805c0150f411128003580c1182c945042d4090147c03107440d0216541c0c030030340d080b10065100c2c9800000c1013015 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 26767460 1250 26766210 26766221
    0x60105010e040f1806061a03010b0702010e03070f090f020903030a0807111509010e010209060f0f090d060203040b0912070611040503070b030f0a0605090403030f060806070507061d06041e080d 84
    0x45220300300300c02c0780c48001c0447e000d00c20351403100c0342e400c0510050000440c1600103115840c01410007807801c4655100207407810710344e900014400ea60241003003016403c5030107513100210715800294100351410002ca42d40f0b00806035240200040b1b003011a1219015035020000805600280d403400c246071500d0710440207055540c508190703e4900b0b0102640410710a80300c03001c00082c000e40c54052100171801840c1c00030404820000020040c0010325940d5400000f5424498840582c03645000d00309817101c1c078001803080030f05800060492068a54100c1151080391b1301000004800160814113480c0340225001103800d44a80400480e802070b4840c007540c400d8080c00c03441d481700ea0b00d070385441083d10254402c05420040c1311000c01d000a00a03000100008200b02c80080c440b6540c059141c9031040c01c0d50030002055002580000340961401241080c40301e1585031108201c101e0f2005030b0781c00004101403c500314401c6c03038410007410092041d01c4641c220145030780b2650750f6180c0d04c00511 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 26768710 1250 26767460 26767463
    0x100b0c010b0f04060b04050603041518030210050c090d0501020409020a02060402100c0804090c02030c01110301052701090c020a06141e07021209060c01020408060105041d060105010e040f18 83
    0x200c0541e16291450503014100507115171003a10760030316145c40c06100268101405c00c0b00e4440710491882d44650312446409250b6810203400c3c88406441e060203820000c150121401070b80c280b10800c141d655491040790303051a01501c0711669010182406030090040d500401c00241c0000f4080080903400a00c5a0181d8002c4a241007480d1002600791040b040c2403100600b228030522041285442c01d0b8007050b41a801c3e4010740389026a80c11b4030601319034040d0140d80d500d20307020006008904000c01050700084913084180b040e000c0c0b400e06000441814410980c80035242c91400042503c24400d840e0502d42c04a003e010500064211784800304048803144252082800c01c0a5000c000a104034000c08054003d040400610030b01c44030b20358003507051590005010412007041010900c0140011304802d806000035504107005c100565881852076502400c613040314411050b004196581120000d0902d1074009000c200850044d20a2809904040c0d10380181c1500700d140c41c1d8803000026 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 26769960 1250 26768710 26768719
    0x301030606081506010302070201031b020a0309060f0c0b0901090209100302150304030503060108040201050c0a060f061401050d0c0e091503010c020f0a031101020d02040602030a18030803040308100b0c010b 90
    0xd588901c00780f6650300c005a5034440c00e05a603c04a0300300d500950082c10744500603d000701c0e000c43c2c401c103000e2081014101d0540140d1101c1a940140350341701c08002c01030296490003290314192800d0080c010300b0302c0e62003c5c10320141840410034040c400d6000c2480d066029010b5030f85481c0c8010385000d028140c6c482a4050400c546805600940890440344141e0b4140c41c1c50b41141c030b038003004580011004004030305000041003120841c0c0380401070f103c0c01c81d00c600c030301103503801c101d0f41d10307a013070781c5507035208005201c40b0100388141a030300002550504400e51000041c0343d01200c10840303c0c0d407181083c2d1900b0400c40000e000b40441396035117106e84d044040d0000e0103108540b610403030340d41c1340c0c000c1c00340c4458100220407400644124004502c03003e10800146c04d015035040032408036813281c0e0007040964000a080201207801110798184040d80c107018485c100d00e07603245d1015500c80100004c0c1040700d02000940c0c170145a154140c00380035020135058990302070b403002900030051160154071a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 26771210 1250 26769960 26769971
    0x3b0a0f080613020a0b090a030501021b0c060c25050a0303030b0315010b19020307020604060c0201170c090108130c0807060908010209060702040b130c0503070306080318010f0318060203010306 84
    0x2440100d8440c40710b2a41c0501100452890301403142440e402900f00968040982e010010200b80d00b40041d001c40390380c00401fa04200c80c03084149203828001740d04607008607800e0080c110491004101c035002100005070841c903c0c8017041c1c0c1c0a0181026410065101d11078810200506500d603004000c620001d90031641d490240c0741400407074070b000b4451310340c03072141c2001140c002c5242c98489415400b02c0f030040724203149555000421a40150f0445400524900ca8007019913910040b242c1030040e10703014980d01802c00c051400c41070302c112281d860600c010b0f0004190842d012000c0c0041e0a900403500241c01758480640c292104090720071040003429059011480000602c06c4401c08040104998a0403419900f07100180002e0098160b01c0300c64281b0003070003080310340074038940340101e80c2d5038607924508010003501702d40fa1070f080600340740c1c03013840200501086c0300351040000e8802d0070100d1021812410881c003070f104010030f1140344e090724111002042001d0300034505aa2240405020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 26772460 1250 26771210 26771221
    0x30204030611091e011202070f030f08040305030103020d02060d1a040c091d0a060b040b0306010311090102060f06060d2910020304030609050115060e0901063b0a0f0806 74
    0x71805a003a00c0380c2c0c41340302c0c0d00448510040c9400003030000041810204401500d0210500490300180c009072a8404d01e54451010964041135081490015080c018250708254600819900050100900851500b5140001d5580b020180c0320040389980341402580340000408403420102d05695001c2c9050221440585006070780d41c0080e50002d000e01c0d940880e0742c0560702c08801003c4c184080d45640e170000840e000c000e91000388041c0412207405039890803c0700004088804000f5a00c00c446020f00c45405079a9010a00a810401c0c0c001510340a07241e00d800180035200700103540c4407031071800386c03040c03011600110408445009562440c0d203d0f0070386402d000382e9046413140007005030070802090001900c5036202113251130003000000751655603035201200460b240c3e04000d003c83c1c001c0d54045c001b0309c1c1c50017a550140c1140e140c1070b82c84840f2008611110740380030764401061130081c0c6c0c00e04c844505c594080c2480300c00060511010b240e81e43c1c9220f0f4102d1190140064034080c01c0f00040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 26773710 1250 26772460 26772491
    0x702061b0f0c010206130b1302041b080105010c0c030b1e0a061403030307091502010b03060109050105040f0905060105010302090103090611070c080c01020a03140d060605030a0e0723030f0a030302040306 89
    0x5214a00100400c46c2c88121541c5940524000400044101448205200150702c2d503104413035080c40b80710002d40004031654070250844605910140c1040b003948030b03100000340c00c3d0b004007080301e46c8015416120f844032924040180a02414848007099220405c400c2c20382d1a00420211000c02031500007600c6c0d0307002495103d00c022900e58022070200c2e0420450300a104551046441031840006003554441000030305000c401e07800303580801d85031001801540341074464000165000c2c1c108125049032030341c0f42034079120144201d9040c0b5034049030038103a41e4060342080d185280c0c089400c01c54030721482d2400e01c03c0d400840c401d4648043d108000319507101c00042107100d841c016001003007442c070140d4040319010320f820f000340044002441004990040740c0281d0307029001a886d265124580640c0500c1110305180707040c070b071039406050204041000074044245010303c11221342c040f0019100864940b10010f000008030f07108540030841450340c07603406441620710405050000214901604 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 26774960 1250 26773710 26773723
    0x91b04090819020f0d020606010f0c020d0809190b03180303130b1009020a020706021b0609090a09021203070c05010806030c040e250e0c03040c03080702061b0f0c0102 73
    0x245000d40070044402c0030702c64076000c0d08440c2c450f07204480d002450104d015003015411810300e00580d11400c00e01105681005a54199903640d1a042c41d50320038075000038000940c0311502130012100050001ea894070348158403e01c94001c4040c80482e40d03a100035525056200711028682e1310b05050500c0c086090102c1201c1c003034540001a800c4040702622203144540d070140c41d0b094101d8004000240b00d010900240503a43c1d000e802a00065241520107418503200e841d01c2801e280d408a0b08a01964801003520384800b0103895004241d82c4030310400c001020840800ba40c041c145034415906080004020002d1030b1280700032030030082e40c520046d0342e041d03c01d840c074543c0341e0450808441c841c1440e42c407481c2c412101400711101504640503504484220b000385d643d10010301413050100040d072201e543e800910144c042ca2842c6405d49032111110950f02005085240004d80b6a05540d2031400340c40210328100f40c419061034034001e005e6601c43e0309980c50310305070003400c008403010341c00890394 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 26776210 1250 26774960 26774963
    0x1020d060303050316050c1e010f0905010e250b0d0603020d080d0f0204030b0a050709090e030c060f070504030f08040506280e031c0c0c0602240712050402010e09091b0409 75
    0xc189101c0c6c01c00f0449007400440324008c2c0b5540da038000d400c007102c0c0d9a02504e0112406000001116020314402c5402c2104281c1030140080c2c5d0f50251030440781003040c0020444030462181e5031207a2070750b0094405003c040e40041e52114685100405005600c401013542001c002802c202e40c5181a03145401c3e801540f01c00350505c00e40c5c10004002603c1600040d40c0280c0d28901002081e0300d5101030783c211000103112412950001c40ca0f02440c24042020a030400701d1030202c00c0c000c1c900b0300b0005029101d103020003030441c1400e1406008100886040d00c3c083e2500500d081c2d20b800d60140100c5201d1b880060550100206002000c1514003544a00180c1c08002c1e0190524041c0d0140441117030000c52000310412404142c0200400c1655035050041d1120703901400c0c84029205541680e02e003a0340d00003000603d40d0080c0003956411070f9004140d0019180e01060701e95450005803504071608003000c0d040048242005071494010a003c08000c80481c04d420250b007804051108039103d8040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 26777460 1250 26776210 26776213
    0x100201090807030e010c0507090e0f16151103030f040201030f140606090a0504020c03120702071805100b0c0703060c021b1e060a170c0a021b0301020d060303050316050c 74
    0x3042c000c01e200f00703c5000c142006050004881c1100d544c0c981c40c00409902071002142e5444140205900c2071003942810795444c0010800040c042d004400420341d140f00310080c5143d11890b141c5424080c40312200b400c680202902c1c1c030391518800c200e82d403140441d0201e001034a020702c4881c1d01500e0f0701c50a244040d41c208200315030794543d0300f071107100d510000e2183e5018424480008455450b4001000400080000b035515151b15042e07241d400788015000a096400c400c10a001042d071101c1000d01d4020006404917039620340241c44202a4000c0e042400751a40019000c0000c60b000030b49101104e00c04c01c000c01265a01800890700d580c00441a680760b0042111125080d2410a400c15034840c0c03541030140048090f4400503800394855139824012564448410a02c034949405640d030026948050741d10b030000c0080300a4541030886481c400d203078010740c080c00300c41d1400d40c15284021641e80040019a40320b0902a05070b80044514803d010a5110f048900b0f520440680e04600e65520 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 26778710 1250 26777460 26777467
    0x50709150f0305070302040909050304051c0209040b040c0f0312080a0c020304060c05011512060c020304030f0803130803073b06070f0204050112060f09030e240310051002010908 78
    0x41c001c40140602a1108040640a01000c90f00810b10b204210140344030310021a6142e02e00740600006400071051103a5100600c2c0160000da240c41c174800390f0240e4041d0701c04071280d0703803071030103418458141e0172091605402c8a008010007443d50f005110f0182c050301c0d42c00c410354a0026071f20664118911020050700144010841d042c001c642c04132825110703070000b10380c50301a840d0f0201c00c5981c1790300121078021115482d40c00c1c032a042c03140c4c1f4283c1040380301451406042d1f1b10341d000d0008a4020013030000c400007000850f2a400c010050607480da01800c415507a0803c0d0f040103100b0409128802040900d1483ca0380c486c0031400c0403001c3c0d0740f410144050200c1059010001140c0000c24140c0e0703006101051080160380310f21415019090210309000c125406081400c2140c828244018141d841c1c041c0e00302c00719030040036808000d01c0442c1d000d007501300c5c02c120742d8000c408000c000c0030886002005110b9949854011744003034a005807000e0844264404040342602c0200070003809031310080 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 26779960 1250 26778710 26778737
    0xc0a0f05060c010f050f01050a0b040e010e040203030712030c021b0901030f03050c010915060504090b010506090117090a0b0f100b03060418050a030305011202090a0e011b0305070915 80
    0x501c003030884100c0039000007540361240e40144080d40d00465040d80001c1c1500014401441c002212801410b6003421306d03410316090000c03030404580d06000324601e21680d40005002c5540030000c440415520501c010b150410200740070380031f40302c154000d00c094042c1e44001545100d2019034100f070118010700d160050303403a64aa0010049040390241c08018040000c40c0391000309010f503076911403080c03150f40c03850192030900800300c072003c0d00942d20170790415044801141d00d100703500c2d0540350129160340e84c442c09800140c4917429043c001c4002c1c00311200800903c0203001c2952101c1d5802114580901d0751946d0a014040f4401c40320180310a4040f070041c031040c0d007110043c5900141c0940000750140403405205038013100250708484643c80703403005c0300405505015060040031000106440102d1a50004881c218024101640c19076907224403014550250002480c120400101002d050407080b4000d000c1c00003101c0c24000700740600000200000c030200c45a511206d5030b0b58001c980e4004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 26781210 1250 26779960 26779969
    0x604060801092102030903070f05150f0306011110060b0408060f01030b0a05040c2103090905060f010302130506161106030c04060305061f09080c100203030606070c0801020d0204080c0a0f05 83
    0x150b0000e104505c0103001c0c00c501501e08000c058050403c226038060380303d241204028581c3d6a50840d088008020f003c44013039803107542c0035207420500900f8104e89000d011440c0619002031591100c141605106002452011803c01002610180000c4e02c01030384d6421074030402902d00303203c001e041c0055240001d1613429240c0c81a03410520a000c80703400c4603074400380d58040e002c4581d003420b03050340c40300580c504064000c42030000808480b1010b0025141c820000340540c1d40f401001c1c0e05041e000140c0c80300c0b00e1841003c0074040e16005258680358021140c45c1d4880c426031400440e200e0408000c00f000a140200a6a04c503c0d00d262040c0d14103401c140044002d44030107444c26822901400c1d10244544044440300c0028045564103002c00d49003020852034400c0b40185240540b00340c2190812061f0301000700c0b540941c0c140c40e12981d0b8065443c1400741a0b006030700403480340d407002c140018010416001001246d003020119107502e0a0030007040603c100c2e40c8a601c1c0303c415005010080c0d803c1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 26782460 1250 26781210 26781263
    0x120a05041e121b0807031a0702070b0405010c03030b03060103030201060f0938030f010203070f080103050a03050c070b0c0a06050a0506090624070c081504030e090a02070503070506060406080109 85
    0x800d28005403409690381011440d0001780d0300b046910000390000e0074040c88004000c10b6000d4054401040d900785089004c0e45644a02d004643c1040986915042410b019400c5a948250082d084404070340e52406c00078001d0042d401001d070381025034072000403442c200740940881d60020110000744490002d00070f820b58801d103a4100c01d40d8112100c40c1c8003c0d0380c2070020400000c440c0e400983e480c03070141c030020042c1c0021074004060081400050000c00c200050384a807441c0d040c103056641e201e0521607240313000c02683c01001d6000f8001001c0e5960500840c2c1031220030b01c100c20502c440d840703030000c103019504201c61064001051130002400351410b00700e401c55211a02c4c264005051200c000301106070702c20341040d00e203048808400c00101808122008540d00039218045031420305e81d40c018620300a20f10380078403030700044000c20380e42c1311507a04541189034000708490740c40c201854455150041140c0640c821460f1180018003a40c06000719458558059127254130000c8200c00300600c9803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 26783710 1250 26782460 26782493
    0x30a0c0c15050603010e030406050d09020a0509070504080c0105090d02040507120603060504050f01111b030d090b0906180705010305041a010e1807030b0c070203120a05041e12 77
    0x11040c94002007400310041441a03030340401c010a480c03421000740343c01d441c000060840c56600070031042040341e44c0308060380c40d450320b165000f0854a54078000078255840a820540d4044141024040e129410800a00407202e1201c10b0362800710500005507114024408410740000014140b4801460554021980051700d0700300529400084600c0c001110b540f60811119541d450050100f072000030843c6e0614240528000e00c401c0455001492007800f8042806048100780100c41002080910a6800a40316201c00f04920750f86810a010401400d0b00e12403680e00900b0007040c000040b1315658044020004020901c1d00c0c6008011001448004d005440c03000c0c1d07441c107400150300461000b03070081071040c101c403003a4105070211300c0c4641114030241c405580030b440c04000003100980c2859100141407480d5840b00b0781030001c00c0c00c1100d00700304201d6841d80090010081c642280142042e59081c101b8410fa101c01c0c110a41c8403807240d400380c00c580030141803030381300080d501061812550 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 26784960 1250 26783710 26783717
    0x60503010e040c170d030b032107051f020304031d03032d0a080403090603050103020d0b04051507080106180b03010506070804080307060204140f0d0611040f031103010e12030a0c 78
    0x5a5142941441c64131034098044941d00502d802d0a007140c0c1c14003c511111404a019240b52865102d071084080320b10780344d051241c500402d481081c020140415143d000c0c0c80c02c0810000d14807420580c0c000d40c800c90b0202c000c104d42c455030006080841c0510064a0130250095142406502c84000800007180c1d100c0d0601540d41c0c081032040d0700180190206580d151100e0420781403d01c5c1c0036140f0841e0f0303007124080600d06001040540e4981c01c2c1103100700c3c0c205080501580721803d1480c14045000d8041000c4500c0d40300f44000c281e030064016040394995507a0610f0f2403e01d4081c0c65042000344611800c0c000305000522a51a0113001848071600c1254000e00d0140d45405050650b08000026241e2079400b040c20001101403102e01508101c08a50b5001061031303c00000e01410380110740030305400c3c1d880c8520301020200e0400c450240405080414031a40e9900d44112141011181c4038001d500306810340a20503030000e076213009040207122260135036444015600040244800a8040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 26786210 1250 26784960 26784983
    0xa0806011d0a0b070c0b0a02070b0a0302072901050d0503070b0c040302100203030f010906080303070e010e040204030501021c0203130308040203010f0c080402030f0606030304050613030c06020604060f0501060503010e04 96
    0x75640d442c1c4020300800c41c500340700c3c0c1c99844034240703e11494542e50201c12150010803441d940030764080380120030360b40740300482521002c10f103808a00900580c04024042007955400c4c0e00c03107441a0003410300c2c6151210452170961f0f210300074481200e88404006009900c14460344000811503458694850a4540f4007428142d80ea0009204a4403640d482d1000d81c200106001200c0050701e201800750106030b00900400e407034042016982c0c030000f0842801c1201802282d106688500c0171000c0c846030080095449907100c0c10641e00030350082016a8222419850084c0324500600039030f03100d2012030702c40100c0b2059503101598203540041080fa0301d035584038008c44030144036110760981c3c0846035a0b00540e504e010f105061410550b0b509001c40c0354080c2e0308118142d0b0f000800c603070036150203803901c1d504e0350034680c003400035011a81c0009040c0340c0c441d4404100d140d8009485031180340680014481c0d01075400c103181c01c0f1903081c000d400c001503081005012103130300d208a6070317005481010007002 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 26787460 1250 26786210 26786267
    0xf07060f180f0303060806040201080c0d06030203011104060801090b0609120f031303030f0c120c05010e150f1605180f03010e0304060212030c0a0311160c03060c0201020a080601 78
    0x14800301d14201e0700000800e10410600d5807600c2000068a612001001da90820340c0010b4002c400c0185512031601d00080c440141e0481504840c00456000c8c00234000d00070f01e000750300d60a82182c00f51200240c0e0301c03000041c0c900c03171900507840da038803024082c289402c0c940410710419480398011a51144254a0a81403280c000c000074005100754460b203040b4036056140091583e508262420100300440603403101040d442200482c40414500381902807240b030b86030150242120320b0285040f80149001014514000c1800c2d912400e81c440709a5804d59400c035007107181d1091103d1601c00280148070440400074941c0e84427440160050a054400500100007070948140c0d05a0748226000450200401c640401291071034015682075203080d807410140d0a103442c00388254000405d900c070079460710f0240000341146c04039207100c006d4403901041400c09004a002030300c4100c1c1c0d828a04101124a540b041c8259410356449582d2002d003903c40000440b070046000001c5124840a405d41c01c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 26788710 1250 26787460 26787491
    0x50604151710030201030e0c0a051903060203040b0603010b010c03050a03050c040e1312170402100504080d0504080c0901080a0f02042304050c090103050712050c040903030905070b0f07060f 83
    0x1c0c030070010308400321000b03070451000405031030030b4000540a540c40945143c0301981e801032040b069850590300d004c0100c14500180304500280d510141c04036200106020512100000030341c8a00d03070a40082c0400003400f401102d65070a61170300a0300240302842401e41c00d92090304080e0308964040650f13820a07442d00e01d00a0051002e0364580c0b00c5000c030405981c204444491900b4030010135041201024403504103018000c94004c1c0000d100d0b982c1000070ba034215006405032009030043c00111440c51040c003c02820742c1d4028028240790b48120407800b0094544001c00605940340c98000d460240982d91340d400d96400c8100b42280e10603100c440c80103c01c8030200306040c026440303a03080c181c54141400c1070743c1421080400c16000b40030b44c10052000c41d100044880803900644542a820030850a00e01d04250741a41c00c0c80e407040c1802103c0d014564075800c0030034442e00605c2921034a954a02141c034680c03190211000c0d458005000900219210b80e202d043c8504a128002c02e60300358010694 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 26789960 1250 26788710 26788757
    0x80d020a0b0907180e0d03060f03060e100c020f10091203022b02071104060b04050603041506030b040501050a05070905060c0705030604060509100203070507080702120a06020c0c010905060415 84
    0x101072050303649503441001da800b04215000318506d402c0400c002401c0c000c000400e210540006481c0c140c440040001c0120100001041c00600034010071900061480003915140f08079100000d42c480c010280d045040c861040103101da900400d08811a003d01d002540a900305038025900c0c500d501d41d0309600b68003005041d0301034580481c401661a4120b10b801c1342c400740780a0b00c06010300c3c500710080c0f00c446003060807201503800071684180c0340e0f95140752080300c854200c14040c40150400f1380c00001c024040c68014010762003100240610340ea40c801080480d1000c403100b0000994000003040282041b00c018840c004800c8207a035503070b43d00d407000300340b0300401540c080f00c2d000da8840400130b003c0000e2010317200c00110f03610154518200140014824010340401501c42d4000099010441d607c0801d2009a50410803d603604000340381040300003500b085076081841d000e4440e9070461584140e9408050b105c00400c258281803e0005500e40200039544010900c182d01520060680014041 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 26791210 1250 26789960 26789999
    0x405010605040501030e01110a0315030c1401080702030909010605030709031709100207030804140a05030d0201090318030201140d021204061a040b06030a0509010b0607150501080d020a0b0907 84
    0x410b03650700c0c80c00000400310f0388240c590f91250b03490b18400000b0000840c0407134941c4101441d000c02d160701c03011110240041680d01c01400b11054000009103654103000720f1044007400d890703040300c6e41c2d600c0c0d00603078072445507484c080c1c0d0003401d200060001a000300702540d0421401c0c58031525064496403500c1c03a05600c25422904c5d10030103e80c11381c4901e04401d100c00f14800e50b2014040c900d1865884524078055030140003103000141d9013218260b12281c0c01900206001401c0300c54000109201074000c09109505400003082018108d600c0d1940c2c1c50b200c0112941a90388940c2040744824104035500940300000f0100e400b000b41c44109203209078494000c074091400040c1005844080d100c50b0350244441ea80250f0038003120802c560b445400b560381c00405400c001c00d103540c440c0146030050803518041a4007a1002c204e03070f0207124440c8003c0c2583c018655003004280d0302e40d0701441da42c000c6581e080c2c0c0144d2000034228001043c03140055000344012046076240c41d100c4100354800e4070541007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 26792460 1250 26791210 26791217
    0x3031112060f010302040b040905071403070c0c0e06030309041503021009080601061706040902030c0a1e0503060103050a0f030c0209011205060a0501050307061107180209031b030703030305130204050106 89
    0x3448254078081c907444000002c242011803a00d40f400c1c01c00d686c03d00071403040201d1955a0400030f88018000d0082000007515a404540e4034030704118090000c44004e00189c44100b034003a008182c40e0354076001e0f6406808024029800d1800140420002e0001442d402243e048072480000060300c52009000f400c6e603854a4581c0150706044c00203180100591080c010441c44200103841f941c940c100141e002a41901c011030081084c0c00032901d409500b01c50280c009014540009440a0030342480402c0e0070010540d1060340d0350b86003050760741c030340a001c06000c0b42c000d01c1c40c00d40065508041c440b016403190504500500d01500006d4152034240d0181060451a10130542040018400982d1211240b28204103550410020a03a02d0059002c0c1c2030611030b14040c0c0080d0075402300700314001400b0810700850701d10746140100d0065008003d0060003071051514102c0e00b03003101d8a606090340c10150090031903c1c90341c0c50803405440c0145c03402c0c000c0d40c0c00011882c05030303c3d00c3c000d250281420780c4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 26793710 1250 26792460 26792497
    0x20a03020a0f0929190201241a03090703150207060b0316030311120408010606020607020d0c02130204080f0601030506100b040312020f030a030b03010c03050f13030311 74
    0x5602400c2c29403a03040090800c029098140034000000007410140300060404075102041081400601c2c0b040d900d2101c00324040c00b400801d6681c1c150013200900b001a88003044803020351048120400c81070294807030310007080c21460050040000a1a40304d100f2000325030704950340707407a00141500b0704003841c03021a400181640c14450f05004d0401c100c0820340003007000210101c4c6190050099000040810894000061000c0820007001d2400c04a040401c2c0d507440e5030f04540c0f4001c0446115481c0540141c0d400500740600102c0c402203408100d032a2100801596401c026030705080ea07201c0b40c0c0f500e9003800003240d0b1000400c00300303a070028114010301d6154118207226181083c020044201240405000d0016101c0d000a44044982c0304e140e02208084921084e810b0205201640301207100c0446c2c2520904da02d030700040400709040c0c00030010000392032400c4042e20781c01c0710541c1c1041c60701d02c0072820400d045504110418000d10340022041c184c440c02c0e610680c0035a01140300c0c220f912 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 26794960 1250 26793710 26793727
    0x22505010e15090108060604080f03070605010605030606030a09022b05060603010219030e0a081306080f101413060b0a0314060d0b090a0206030103080a030f090c050d020112020a0302 80
    0x40d01c1c80c0c0001e0840720040c1012018a101d4483e00c24a08024100300400002c190940c0300c410a0f02c1c050040f810554000200902406650333800c01c0006444485c145000090b115010b20100e030b0003440042c1c840c51549c2e030750303160341009022003440407a0030031000031611040c03a68094240c161224540d019407449810b909141d4540030001d0146c511070f03441041030842480300845c02030f2500495007004030300d44201005460505001260160601c1c41c001400901d03801100700d180d003622501c0d1110401e98880404007103c00070200c881072150040c2000a004031405454031139000100140168600c03010108584150781540d446603144c00d0300818400c0704150507002c1d0302d418011051050b0114940745000540303034038aa0314050485150138001c590903800074440e0301c0e4684d4014001b46e03036075650b0b0b180400140d84491003100000b458807091085104c258001c85145035000200a8029130500301082100100c18100300d0600c6843c41d00307907400d07402d0782c0083c0001e00610780b4016254100c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 26796210 1250 26794960 26794967
    0x602010e010b01021902040e0f0d09090e0601030b150301060902090a060c080f0c0304030803040b011406090102060411010203041205070312080907140f040e210c03120702250501 78
    0x4031001a4401d904000d4900d6199900040c01c0807405090400d0361181320141c00814010110940d582005000e07540e1502000765001035070f2310005c81c195492407031072543e60404200701c1d009006041046d800400c0104041051002016040607281c0c45004a800c2007000103070071500c059000000003600890384008c00c8ca4081d0040004200a081c41c007003955442d0380703510440c803c00c0205210280040303201900701e4010002d540181d5401271070940d4a06280c240500e0565092040d030028150080001100c0d06001050f6203100c0320680041a13603480e96a1078003481a01d06200c94114401808001500b9100e40130802800340994094000c05055042140e01d851031101010f080c00704100a000d4080750015004089690444001c4541d40e032030b00014101070b1030080038136449410300403400c3c0101008101c83c215006500000c0346262494101c0c84440c0c0a45420642140c0050014403031281c5802c2031641d00005d1441511403003101c00d000c0d421000340041c07202e50300d016a0b83d010300040d42c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 26797460 1250 26796210 26796221
    0x190306110f030103020d08040518040506061c330f11040501050a0c020301020706020c0102130501110a06150905010e010618050603070e01030b040e010e0c0a08060115090305070609060201 82
    0x2030901107803600c070140c803a0481d00d12040c44002c2c00341841c100d000c400d011152007510050240100403a4a50654100520700e0040699054030903003e0740c004148507180241000324030744040d9240247c031141d16115510810100e0001000031180b1030300312000488100000021b0039402800054100030416030711045480c00050b0040200d02008188100d03a081800d46860303000070700e00004058400e102090190044400040c4140e002189040f040601900980038041403080c1c440344282d034503001150003569207402250a500080c0701d039000b05681d604041c4031030100718030744026540e5a100100440c2c40c00d9002424055003400180003e0790706c00703110740d000c0c00e0303c404041705503090500040c807510010b0403050511056003032400c07069010340c01000e180d9800500030010f0400e04c0604034082e180c526001000c601848c0060701003841c04018280c150f070f0086004014681c284016050602001d0703028006000c0700c098000f0015408006400180c105592010012480c01c5000303800c1d502d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 26798567 1107 26797460 26797481
    0x6080f09010612120e0904150b040905100204050a0e010e0f060301091203060f0611030301030803041403030a0b01080a0207051507120609020405010810150509040b190306 75
    0x4160b040c2d14983c041300e413951a500404003040100840c01220005e01110341090040403003645a44050710040700903000086202244c0c5500e4904101c0c0300406a106400280600040c103200b08040005c0060281c0340c440c039414208a4214040024000c80d407201039038001034099507094000d05001d607080385442005418121005002d0243c40c094603558448007040000c4440c420b0419007040049407000d035045900359654014154009042501d05184079006d28150000500045024555110001504240060002d400c400c0010802000648107221410109801050400c69142c02010400c003642d180e100945082c4c0c4608044000c0c0d03864407030302085205c05030b402001518804d807114019540c40e05080504814140111074a081807028044031990064003d42030b8a8002032020030102445008104840d44c03e1901c2c2c0b510440d114002c10901821b4840c0760940fa = true := by decide +kernel

theorem cover : BRFrame.Cov 26618710 26798567 := by
  have h0 := BRFrame.cov_init 26618710
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 26618710 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 26618710 ≤ n) (h2 : n < 26798567) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
