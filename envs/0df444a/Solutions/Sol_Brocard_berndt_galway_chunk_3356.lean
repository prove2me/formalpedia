-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3356
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:25:37.196613+00:00
-- url     : https://prove2.me/submissions/79d56608-c5fe-425e-ac60-9dbade160846

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 603417266 ≤ n < 603597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 603418516 1250 603417266 603417271
    0x201050f07140109080a02060a050712020706020c0a05070e0a141302121002040801140903030103060513061505010905060702130b0118080f161d040602190801050a0b0a020a02040203 80
    0x100021a0344075520030503004c3c011002d4aa00411525460b4001c00380040d06203c4003d2148101602d041c0800c080990000d02000407280c6000d40140c0b620120301d450070085c8510032001c94203200d120200c0301008030005810041d180742c0041c20015440b18002074003603c0d4407004001c030501080000414040ca040008000c507800200403d1809103805c0c911400c0c000c95002c0d072828190001010300803a8030900480800d911050703511550761500401450303c074001030000500740354850021882d40c00078100e603c20000d400c10400c0107a10090201c1003002ea0881c070810b03002c120703d030900080d2460044281d0301c500c2d80207811415940465200d0000074241c2c04d40603418003114079420420300070344c2808400502030110081c034000c6859104030b0300d40074a0040c680000301c0c4070030090040070100e29041d40c405511420502c501d46891a1803406401850340507011000240041c0d002580e1100415040f62030586274017a07825242c031001c403040d1003482e1250002d40e00c0341a4041c0103080a500459 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 603419766 1250 603418516 603418523
    0xa12020f22170f030409020913140906060d03080612070f060507030f03180210090909150b060a0507030320030f1f0b1c09080720060a0c15090c12050c0603040201050f07 74
    0x510306260512101c0ac460303140c0b11500044805400308440c0c0802005100d42220040f907040c2000c10071a50024074810700140040e001d042000d400c0c3e0382c0302c08200060805080b1800c04081600c0d19042d00624a8002501c20780029000c0c00c2c201c074415019105498000b0140509100412543d03024000c40210540c5802c0c01c000c845040001d2111041c4a81c640552040100c00d050003410351030070b41580c00d82c1001500c12942044541044c9802900711000b4a5150030b020a000d03206000c175948411008145802a1000108000b2002071101405128143c1051060f08290200107140f031000c401d405a648001c80400181c08040103d40e200c00b52035410134000f00306280b031503032900704681025008039800c03002104020400402170291110102080d11060305000202c4001004030b50602800781031038001801064054000360800314040380c00080d02c08500d50358003509590700710340b03100956441c02007860070211072a01e5000c0724086d64050303640300d0030250742d46004038040d4420031044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 603421016 1250 603419766 603419779
    0x10804060c1103030901060906080c010c1e05060705070b09060c0d1d0304060f0206070e030a02010302030c12240337050d030204050f04020a12020f22170f0304090209 73
    0x10b040d103000308010362042d004800003152841c80c20a826040c0c1e0515004a0860340060b0120b48880c0d0f449804031f441c45400c60b140c04007814000c02c0c4264134811150001c0c020b4003846042140540d0004010282030740b003a01e0305551552441c00e96910780d40c0c00d50722415103a4080085460801041e0480031b0031842c644001d242004d04001e045107198080c1e404900414204459003400035010701000d0f44c05040c60901c0381a4402e000002500e44924001c000e042c1030f404000b24000d100524103851100344030031902015820292100c0b1560a030b0140100e034038000382103801015040120f0304240300d081b09600c0300351000000c15001c0310180c00040a40041c201080b250022500030007103081440d8198a0059540d424002403001c000305000e1000c3c005c07401041401f02007a840828441c640340314240040c1c0b10b0017a00c05c11640f501c96400d540100c3d80030203000c24182c0d806030030342000b101c420f0754000080742e13500c403d0503840744244d07034540d002d03070b0010310080004550940041c4540c48000b0300131b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 603422266 1250 603421016 603421037
    0x7030e130e03130f050d0c0b0f0909090a02150c100e0a0813060e01050405100f090812030f070216120305071406150f0d0f020d08040b070b070806010804060c 69
    0x10b480d64101a816044081c07100d40c1c200010900030000d0340c040c0c24103607190703080d080b02034580303800b140618070408401d103800007220303140460b148007607851250008009180c1c3d81090084107585c2e4616503c08d9110f10741c0021000218580b104c221002c00700c044c4090101c2c00702500241005109154000c007071806440182000102800024030100344e0b541c1075505024244000100500030b0080301c1d50500104010600072503503502480000748405140c011055000c0f0f0108860b08a080d0b8807a58540c0300c0c0c0e0303403400740c00743c00c583c0034506c128425145000c05a454000481c0c0d5440044018041d00782d040206011a034122794185114a0007424401d00e41a200d035907500321085280030044451f000142441910b58204406001000b42181c3d600d4100a200e13000a90b9070800e0794000700146100d0702400c0840d00e0301e0f1020a1000d811154481e1550b941d44980e03001c0341e0051104541000d45c00c0009241140540815030084034183e55449160307540365160401821704998460500c10320000703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 603423516 1250 603422266 603422291
    0x708040806090709110301181e021605121e03180d08090f0604050c04020706060b040602151e0c03070c021906120204081209150a0c020a0b07030e13 65
    0xc090300070034041d4020146180703804da06508a4985203240c52103480d003003004005238015154084010110800c0000341440c0f00d001c00b0203030800302081d82c5a140c1c0007191461407200d1140240205074005e0040d07490304141c0c107221340000d101343c4684040244070083c01c4100104850302071907019607180d541c03607015480e1024152900202808040014401d03008020a081d810700101e41801c403034a0040c4968100b50f680c0c10340f24918815610b00031035001c642d8200b0300125410100051481550f140c0ea200d8035072200941740c0314042820042e1402e16008503605000d20864500305a0110751001c0d0103882c0c0c0101c41a169001030602410000c4508944000d84e40e541c0c10100f20302a51031443d0040740c90002d018080c880c00401a01c20184140030400030443d012a00716558440100c0c229a40c40c00703a00056201281c025400540010200e43da00d20340f604000782c0310505008503001042141c0c0c664400c00b0901c10404006e000822040004425041090305076074074044000007c00c05044040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 603424766 1250 603423516 603423523
    0x21c0e1c140c0d090506120703050606130f0807080d0807030f022b0c09060e0f12030a02061005091303031e0f050f09060f0103170f0f22180207080408 66
    0x121400301500f144a49840300d03600300101d00c00926040d21500e0800c202c032130b00031000040092015051645440004815503100d8044414200d0580300d501200b580710304110b03621040d140201070252098010210b542e44000491150000c001d5403121480c0da81c41ea0120003400026444c0440c00e9028030000d0a51200824407032810342a003c40c000c1c07441c100307405000030340e981d000800003400700c0d444090000e154014a0460581e6069074a8126140041d010910b03e606003d600d581c00d000c003191215005034081041405540f0106484580c01d40701c0d410820711020655944100c01c0c1100c01c000c00190090300f08400e60b02c4d000c95400307013045030081108155840c20880409841d560020080e0582103010141c0d008060280106007524001311211403941042c0400752000c8910705c100b4042180080865500c5902940415128640c0c00701000080d04080740181d20302c2d13003191403a00108590f21031402181c50003074a46000b0714a205041c0001d40c4070680c1500c4c260420840032036110000c0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 603426016 1250 603424766 603424777
    0x9070509150a02060f240409020609190602070f0f15021c0203070204050a0c0e09090c04060f15110309060c07081603150207080d0506040b0d06021c0e1c14 68
    0x160003070b080394174041071300c9000002c0c010701d5100d0400780b0000e00209940c1c49513030000c1500d02600c2c0016240044c2c00029014022005200d41c0120007a18910080220030703201000c9501540072954616250b8500c40c3c80300705907000740524000106010881c1901c07800b108289070505005a60789607900980211004108468050241e030000030040e0440c1050310486030701c081c40b088108420030032203c0003881050600315452041e00b0fa0400700c0c40c1501c06205d940b2081c0c50017401044495644d9102031030044c1d05101c0c4032550b6951100318540c06010f00e81c05141030007848080d41c80c00400e030713040241a4119049100035842486404210480304000c1c0d0004d40020038410460700740382d45803020201ea21186280601030041c01282e000800321020b44101001c0210085080c3c0c0c1d9060100300144292085582d200d28005410001d01c45541e00501210424041d2010340c60b45140680040d20320a2602020a5100e10904181220034242c2140014a5483c01b111400114100107402350041c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 603427266 1250 603426016 603426037
    0x21c0b0d3807090f0e040204020912150610030e0705090c0f1810020316032d0806120c010203041a09030d02010b0406050405060105070f11041401230907050915 70
    0x7540d091010294100c034601d00248200030101440d2401c0100180c529840a44001d014680100f0032403c2c41c1d60b8035016024480b130003011949050800e401c2c440b452501902c6c3d550246000300f04108515100740a9061050074020041c5103041c504420b11090346401850b810b44180144200b112a003000c0e402000d4044e08000b003805288409020040c03011540b08550341554410041d0204c410f1445003600c0c04250982840a101036404d200500c40c00700e0a440010540014000308041d039400c0004035015600649140e0346810031540c100ea81e941d00c00b820346001da442031108020302c2c4003010ba80d15111000c4e0030b2060030505e00b000823a10705030038002240050b075102c100b02c400c01d0030548a01c0f001000d040302c0600490034074000281413807040e4100542540a040d0702c03042889208040e1488071540984100880001d00403040d034400b00a00507400050070b4942c0386408004035002c490504000207141ca4082e0b103440740c0681d5150320500b005500084020816130703421700240040e102c1d04a0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 603428516 1250 603427266 603427373
    0x80903151801050405061501050904090303090c0803160b0402041401030f0b0f06060403021c0c140f12030a081e040602031f0f05060a0201020d020c01021c0b0d 70
    0x501504602249144090710101c6a241004100102c0c8000071150340100c29107002600d0315801000481c1c180c8107845549411508110113202055416070042004038040d1300001540b5807105841910b905c224a0468410320442490001040a50000c190840d20040c000035480380302e25032024081101740d00c00e0b90a411400c034a101403081e40703038401d544503411074610b0724186001030004080380034900000e030090f400385c075181c0141c0744240c0f9051071460700300355580c80041d90380e2085d501040001041c14003034401c449c410310117420190260410b0410b010302841c03c0c913281140c1140e02000c002c1c5400301e10000b94814800e030390400303070701f290003540908005a82c03443c121090314183d0304484200220200c2d10b00d42089540116403445040e29022a501750f500d50031179404a0180c003a5801c16504130388001898080c500c015402000c0700c40701603842c154501b42c03c080070f908030b52080b000c3c290400c81070040500061010741c1ca8039051320340241c04c203032000d800b0548400c015421488842c980074 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 603429766 1250 603428516 603428521
    0x150a0f03060605100302070c0b0309010e070801020a02010b0108040206030103020d021507051b0306041115040f0b040906050a0303170a09080304050115270c0917070f0b042108090315 80
    0x244030441e8503604861742401d43c6040765669880c0f040c0031413440703020b61003071001c0301117200c4140c00e401ca2002c0c082444221742221b6242c0144500070340c0300d100d4103800345d840d100241e0f200b940500b80e0244500d800400050440e0b00c0e40d001d11040840c5030f80100e074040c41c0e00641c140c104c80d502d400b91900d036000d0802400c4001004842e894003801020f810341c8654406402c2100003841c101c0b480d0080d260540b4180034815240106180500070707600240d100c10031a407808140c151071034018100700d40400400340209560345041c40041146800090001141180703034010480c001e100750ba4008200d10800a01c01c40c00391207550071a00700751421202a5140d04021454401480c64400075058140c14000c980890004080750b06101f85c0d89d00200b03a85411248488034040c4c03080300003c3c0312180c01d00b840908080ca50903198030040c081d01c0c41c041160400030899001c0d803403d031402e42d080502c00d00388814411004c0d0481c01d0382450f088816110801216031951024050440c000841e5900c010060 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 603431016 1250 603429766 603429769
    0x613030b061309020d021e03010905030c070605030708130224071202060105063004030503040506010812180301060b0d060303080f091c14120609070f08150a0f03060605 74
    0x2a01c12060380c20b41e4a04058240002d07a0325010001e494542c120740b00b183c40e03c6102d0b4405103130301c0360094440d8154a841c02000c01d001c07005c070040424a03121001d90341c2075a200c40c003c0d250360100359003040010742a00001031080c400c0114403d50240018040308800b1003078541703080061800640c2c50003d140204020f001c2104d11054042889620700140c0250340c14103006c54410b0248110b512102c010412104c1031813100121411050200d8104da40d0042c50070b41005041c50b801a54222440c2c8210340001a91010204000d0b0100c580504040d03d003030342c0b200c00c004070000030000059043d5a10180012104c940000424a03e4221074001c5503842c0f80d0304000c0d0081000800d80c6c0d90142ca00d10802a04080c00318481d82c00301041c0f44030980500c00c10700112020000b00d02d402c0d1003008002460320284090083d0743e8420f10045a11603642e0f6516442110038601e0380c51458089030150002c2000311441c1d680b054401c0d0000f400c419481503171041d1b1740004026a03802619125a20384040c000d6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 603432266 1250 603431016 603431029
    0x6030a11270a0204170106030308060d0812181923010b030a05210322030908060403092d0e060111011d0c01050c0304060f0e0904110102061e0c03060613030b06 70
    0x31700c0341402080200d26507203000d080440002c101e18400e641c41000714041104102c103807050070030700d038854840c11b2605e80416240b201c031051a0100724442c250a482c400103202e4000703200c0980c4500c0403154110203200c095080c660390503c001d4a0f54881c51031030340300e4408001000311140114014030075100000340301c0e13a144100c43d0703541c03c1a450800401000380b0308183e09003042d4845244548a00d402401d0880b41030700507401200d0a40034250500c003c0c503a00006e40c2d42600d0b00d41001c20542d4100203000c04400c02281c400300c1c0f041d03000000401c0b04015148403e0781c0240103040440451400400c11030844c0c0c50005d492450400f04071101260007000c1100005152086c01c1c414a0408451020b43c0d59000794801c0300100208550040d184501c119544664900060b03c0701e44203061502d080400081190005801032180d131001440324041c103c000383c0042c803440442d20881d1103090301e02d621640000c0019400c00010003d0801e425220001000258014410241c0e5821f01c4420041d9 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 603433516 1250 603432266 603432299
    0x301140a061505070f0206090603040606230315040203120c0f070501080105010203070618080f09011e050a081b0705150714190309020307090903030506030a11270a0204 74
    0xa2440d0115041d10030b6a81190440762010303007005075020075070303858070001b1040d1003103140c240d4105001005020800003940c0054050f1018038010303c2c0785c022010402841d40d46070780c82050740f542c00076040210805030400000e0704140058180c409854140c450008582c0c40805074070400d90020b500010815024070489014201c2460055004d503d40030000f5070740d009a07800580b225688002600c1400001e8070344844207503100c4000b680700c1a050032186c90b113410401005022461130000301420644079807841d0550714481d15280d0400100c0c280482c3d119400915614006010b40d02c0e840040300400c000e45000c41c4a02d0092542d00c81c11400e0290481d00600b0120500c0903d84080d90358400041c103035819010246814400040000d60480c05081c00c40c070069014050303c5d07000700c0c0044058029800141c0651028403841e180c0406055540985940103450401e40c04d200000030719045050481028500200c24180c01051410140c140415038a07400c9040c0c0c001030030000405000074604 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 603434766 1250 603433516 603433529
    0x13270b12060115020309090a0e0c03070b0f0c07050d050604021203030c07241103070e19050108130b070905090106021c0302090109030602030a050f060a15050f090301140a06 76
    0x40d409001554003603942806000b80b900b42188101d8014166100b00140d03404220010441402d0b420802c00080083c0b103142a04040e030300403c0000003040c10001426002c0700c142c400c40c685170140c4004900d5031904111003046040c004c40800052503a10148001c030b545005d10081c00242c03c05104108014100c1140104c1c25041401001180300940301a00c03001d940003a2084041c4c1d2855910720203d002020f258a001c501d4a843c0c4907030350100a01961040c40c554039a10910340101041001411001071480010305103c1802d11055208100c0560005003401200711080075541e5141c0401d6006c0b50242d00003030420b44c08108070f20f80b1010603401411180090400b0300c400202223025020700e00700410a050300082e060907680d11840c42e1030001e580102c1c00319202e01704488030b078001e01400c0d0b6130016031444400115002d4980900403d08460040e41c0464411040c040203441c250801060b0300d58251080c00000e9464400303000f4110030308003201010281d840d1044158003120260b80103603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 603436016 1250 603434766 603434779
    0x5040b0904050a030513050909060114150405040f1d030c0c0f0603060d1e0305090f03012711090a1e0b03120714010606050c01060509060604090213270b 67
    0x8030b000428824030042c0c05103080d90b5a00302c1042c0d40b02900c0c5103035200c140c0020740802080810a40400d029041c1d440e644015080c4001443c00c002da00c0481d8003002010304001c0008200b98074080d0300c0030001d032071001008a032900200091074510b40c08001c0d4584107800000713207281d40c524140140d105d0b2038012210406440300c00004200a070000400c030314040d032a102c4110080c0108005006910060041c200d44d0500ea03e1400400d1604110003c81c000c0d00130880c840d02c14a4180144816116180d039116040b510041c2c090b11541000e440c16101c6036044401400fa64071043d0409210310b05040c8041586400d9040303040c6c10900e0100b02500c59031802080c440d282d503000c10080585a10100324a8840310b9600304418440c1d0021040c0e03140b03612b44800014529002805400142403c6008001c00b80d40c0f982484180382c811180303240d0040741000207100d0340031254050011400000b01d0703421059128400c0f0503809800c1c86054254110306101124200c85d01d001d261146c08040d602e8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 603437266 1250 603436016 603436021
    0x601030807140c03060c040306060f0b120a0207020303130e0a0614101b0b04120305010803030609070512010b18031203070c052506090e280609021305040b09 69
    0x1164101e010349a401440444081c0d4910300607003080001e080c02600c000c0c02d850407410480320b090030907841703484116526401c0500009034528035114940868404141c81490105a1203c1e02d4090b000100401460f903400c0c00780c100540c0742000900f10341c06400101001007400c1000180d54410000c20b10007819082c41005d01c40356095010301d5100304002c0d07a014814040d408420740702d0300501003413081d46030642c0960a0500c482c880e00fa5002d58059000750310300d034141030411002da450034080d1441a074000c00c0070504030b01f0110786035544030f0018030b0468100480c0d5011124107e000303a00145043c0b0020420040b4a004100e403000350344422001002940e602d04210780c00342c04020403400c01d0108004480d42841400d20102610140e000c0d16100304000d510700645143d0b00900a11000880d0b070180864002c044e017810500071000703002e110b003c41d2203080f41b0b680c8510500e0f20098425444040000b80500f40d40081c2c201042040810710b100f41c2071905001c100c40c00701d404c50344603a00c2e00c001e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 603438516 1250 603437266 603437273
    0x60e010e090a2603090601240e2b0b0f010801020901080103060908130603061d04030e0906011812020f010e060d0510030b0a090c0504151e090204030c1502060103 71
    0x1e821a0655001901401021500003c500403800740701158040240c00000c1144c03d10b004035066041c0c520350b40900007665000d0421242244040ca0f118001c24114002e130f021610340300940341d080f00500c411482e1440100801141d140d10070300001c48039140364100780726008101202c00360140002c54000c506180032040000c020407410321010306072540d00c1d6924010b1224420407150080d0703241040e1111030340d540c04002c1c02006240b013207039030303c00c0391950b80c0c0340c811101f248a6000b6034050f510038202e038400a040280c03100001c0c2c01e4506101c0021810089020a40e0845004014440100092381d4850043c010790082c901c1101d030421200107582600341e03490f00141c4680300e88802d4002455507800380c480c42c00040640002d05129240002c00c50a507003590410102c003880364200115403542c035024481541d510344883c280201803032105101c03521031800d945a481103501e8010302c02d01c0d03031034804804980c0260000d46071601d410405000701c55001d4003011b50011184020080340d031541c4c5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 603439766 1250 603438516 603438523
    0x1e060a05030603030d02070b040b0f010b0703030b0f030601090e070512071503061e0501180b0405040b0d0c080f1c05040308160203100f0b0d0f030806011e03060e010e09 74
    0x11910500c580400400c4050310104141c9100161004c400c650781d0007141440404400c0c102d4040710408018070019542d142c0705244a4101d40c500b06440f8100489a84c0c160b0140104014054008540354080c0041d980e04102450091000304000200c040c0039039030003410141c40350001da02402c1c10380c011100c40e9400040440c21903109200705814001e0f860000c4019010507400041200200800c000fa0400c2c04860401142c100341c98104644a1f80b50142014103c0d600c40e20681113420f200c1048030307003016001825210b20040a132001f680c80780da103a0040203e90b8120341d8599101e10b0700401540f1040181529450041215940e5611403000060840c0f18170300000f0102c420114025042c0d84114110081c0154000d081d1000e040d5001513000051102c0c40c21404403d0500340c28004034105500710400701508805203441055417518107031500c4902400250410403841840c1e240d200385540001c44041c6e0a070340c00308480d03213803401c00a024076068018142004d020f4091088071203001 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 603441016 1250 603439766 603439777
    0x703080c0d09120e060909180f12041403010c080103080a050403050f280f11130203090c01030c0c05030726040602010504020310050112020904080d0204031103071e0b0d0f020c0c1e06 80
    0x50b00c0e8680c03107051807481d05042824112600c85244501d10300310346203079040ac000d0030583d1200d05041c4044422801018281c8034101c410801180d00300d001440401c1005008108001d150300b8014a46580c17039031090316100880c1391b2040c0542184004c1420150884005054a4100302e480f2480002d00d443d180e00301141060f00401101c041821660305031079101c14900075010b004d100310340340d280900825071182d69041c04240007900e800c3c5045200c40c01204102109600b090003182884005d135a07403092450050100140304512080d200d200025010040c8003821451b8004100e83c20f00303206061506030b040b05107810840c103180040c0081c216504034a5001a011100c0104a8449051407000e9114846440802c1400018084184215843c07400d5107034800394101c85445654686800c0640558169203c104403007500070004c0000d004060304840b4910400042c001145d0b000001c102e0b03020841c101c002c3e4110310310303900c400d19080c60700c4018a04a903400b2514425880c1c00217105100311c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 603442266 1250 603441016 603441031
    0x3060e0c2a010b0607060506150a020714040b03121b0703120503070c0b090a02090109060b0406050d02160623071416020a030302030715020c030703080c0d09120e060909 74
    0x280300d20904035407025048903201c0d00024200035500e42450400f0f201900049415600403122610554005202c80c0104d506e0f28010364068100b01d82440080098a401d045000b5403040c2c07a00c0005445540030301662001c1c8080d28100c2d69a07160a1450814100e00d10460000d46e4000c81070400101d110700744049003003215403810a81d20f5907612070030f58007010008005040350781144104060124005400b043d054021950488542ea0320f00c511001c1e5446801801c0d0003074401c4c0010010350340200c02402888000410250a08901c074001302c0923102038500641e8034645032110307490300c66000384240d0009160f0050a4038145062a80646000a2080500300704940010650501030301c45902c0000143c3c018010b908055507410700070f5a0b5000000240d44040c18101c4001c0046150300c22a4207400f1176501035230400e1321588041e128400028449604244204005000c1d000d80c0d200c0c0d500850700c0340783d610460103001640240948001c0c040c2c24003030382d801c10506d00c0340d903903241c54a03500042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 603443516 1250 603442266 603442327
    0xa022a1503070c14100e030c0c190e0a0204091a0102060624031e060109030b0a0504030509040e0717150a0f060b1c0b010516200303040603060e0c 64
    0x1d441e94101da0030501040064840b210358214070400c0131010404001a14401c1014000301c0340410000d5104d1061000b501590f86c826070794203c003814020600e58425a8440760341e441c03d80c0d151078030700c800038040f03950411590740010b00340030140c0c4911500320100e1000800745451806d080010b0f55558001d4440c500c10500902401c1c01070900c100c140180301c05501106499051545055000d1a40d80c1707503c007180744004000070455441000404c0440b0f40062001c0600d0f100c0b550014000c3c58054029020800c082000c0c0c0d01c980c58601610280601e00c3e4010b022051a04450103481c060994402002c0d8011040441c2d2403000c0c0a0159004940d4250001d96201345003401e00040141e603006d0301c120a40402c070440c441601000003030002c0200c44040c8040c01c120760045480b4800d461100108005d5810380001250800800964180410244102910358540000e06d942c11940c0080000382d107602c01409948043c4d105160000360010002c0d0602c0c1120000485200711000840340540 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 603444766 1250 603443516 603443521
    0xf091509071814010504020702031e0319021f2c0c091801060501030c0804080c12030a1e020301060f1214041202010c0f0e0d0201140a022a1503 63
    0xca0601811000300b41400b039411541d911920a82c0141c03500c1e282a02d00940c4650000801d07040a008450819900601616002042d000001540000d02c510440c8074407062007003015200462a480404400fa034004003032002c001c8011107801d801c1e60303000007038203410003459484a8003107405010200e502130300e080c031b84032908ad20503515020001140700d03406910942440116115022514204402000281318050302c410054094916140c545400981802d000030301080310400a4051203100400f912880d0b01c00d0600341495400540302100103d913542440c0d018081004803072520345100620039400d642c0740000c00b0301019405407a50040c03210320020360800e4203442e4841c200364514000040c505040905050203180601800700c80590f1a1041c03400c64031b401341c1241f82040200b030b5943d000d81c1100381c050000f400050301c0c049060000d441800da0035002000d0191000340055402406180c02c0d210020180101010390790041030404a08044c058441941900c6d24900303052103560f0342d4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 603446016 1250 603444766 603444781
    0x23070c0201110d18120b0601050f0706050408090a0501110309190e010b070201080708131104020705060c0a02070e0c030a0b130228091d130b070306030201080f0915 72
    0x40c400410440c45009001d1692209a04070790401c91380d00b050360410100c01c1d1104120f07140d001e40c140001d00b030031082c4800129030b98031400c01802c0386e040c29070700c081c1014007650b40c1c4c00a981055904590350f2a020a03005803504041c044180200002d20304000c1c803144081d22582c0b00d00c1910f81c20303401242402440950800000400c030010521141c4c1c0c41c450350794a40078400b894102ca2400c9000941c01804910418800c1400c01e014214400740861192070584c0c1c2c220001d170018680d01c0e0010340901c1381030042001444035620518010103100d54940103000001e0510245811032940c54524605100500880b074003603941c041c405000005009001c18001040070b00e0a001014110b4000140c00318a0080344d02c0c2d90086000010000c44000200c200c00d9400c5c012500071083c1c1400300d021040d41c4884104400d170340000d000d0702000c42c80382c20380e2503125203040b04031a8080407944410080085582c0507101e290310600a20240e049801d1680354103807198801188a40c14201d11030105151 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 603447266 1250 603446016 603446027
    0x91807030605031f0f020a0206070c060e010c080906100e04060b030111220602012f0d02120708010e071709070e0a060504060906030f030f03020d0f020d23070c0201 72
    0x30b00340c01002c40e40140080400c1040202c5031442420300d0505007140048610300c5da00a50741148190b4001d0009541c03000070843c3e141c04001030684039944c031207071200e544500c03c0c41008412211a40e034040d292604800c0c5d80c0c5042320107800c07880c034806800c004028890303840071a0303074005502010200701c100b0070000081c050702c1c149000000c281d00009200c0300ca1300403401c0e00f00c141c014170007160780c55541d100e105a00b02c1e0003010b401c0b5a0342682010181c84408002800d2172500720450195040c5078405241038201d8000e0701030079100800040600c0306080e0460b2495005081c000103582c0d1500d041e850080c4051781130864480c0d14000c0e48040f8201035428014800641080f660f01780d45480e16550000140140340324581c000c0c0c1c40c0c0400896812504d001c0c9909407500a85801d05e00e038010350303084402d414100303401010950b0900c0364601c2602680259004404280743c056168020410040101e03014501c210f20310f04001c26586003905c11081c1f00c9907025069003491400030400d0b0005030354 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 603448516 1250 603447266 603447269
    0x40803040c0f0b0c150615131a04030209010f06090509060402120406150f0b041a25120314010e090307080301090e060705040f05060a0c050a030c03140918070306 71
    0x2a82c2c00301c010003007a014803640142411072210000c642c0c1d200d0303044140040101302038030015081802010102c200c000800d00500b515240403207503019280d1354046a501c0c03400344868a104925001070308006500d03150b200517000d0a010150400c2c41d510740800900944c20b50310505008200c1400002e4241c0d846905440c208018040b0b54005e07858189003400060050101c0c03140c40807400070002c00c1186100c121502510120a07081d45003e0914141d441d501000c507014401211041140104042410041d82a0314580000c2490700c0e0320030707140019140181841c1081011300d0f100d402c091419502070368a04440c01900b44100c607884400c0300c9800c2d4440ca0b100902300704400000062941020b0b4420601d41e1034040589008d52509641207520384294031881c2554902c1a1090180f80340250050909240c00c2c200410440d4455803140d00f0001c5004055000c01c51b2580c0e07032418181c210038100f81c4e142240702c00c40d2529000b000000e55907944031f8203803440380712604001950349001e540140c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 603449766 1250 603448516 603448529
    0x5010f050f07121119060509030f030f06030f0a030f08070c020607030e03010f06032907020703031809060311030c03190b040f02090405030d0e0c0904120216090204051215040803040c 80
    0x176468042200d400c0070f09040340b00d0440781c003407174030001410020020040d1540340c2d01e240c800a203540c8580442241030703031f00541100d5141c01465501c2d507403001c0401140a4a6109445542c1e207050300b000301828100004002e24103000341e84c01c428005039108801c881c941c5505003490f42c0089000f402090040c03200000d0301050314902607000c010b00c04466072081d084000306181540a80c9882403c5032409019540d00000da8404901400001c1c00ba0450f18400c410003059400f441d6a40c50429095860644c816030b92040c2d5001c482506080c02d00100c070202074254000c0c584602d54250314189052591400b408840d60a001304040181e6801e8803032134960004c0501d032040c2030900302070303886e5031080da10102d1540c87c10024480c26040841c0c0400d40601c020041011641d964071000780c100002e241070011401050a00c120799084183c0780805070000798401a112414241804000c1000c039640318555804001101d880c0c01822a08030b034455800100f450300c0fa1a245042c40001101c0c1c0c1150 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 603451016 1250 603449766 603449773
    0x71401050711060141030307060615020a0c1a0409090803100f08060f15040608070f1d0a09031206060c0309050f1e060d090b0105010f050f071211 64
    0xc0e503a40300c0e020703403600b060b100c0507140709980e690748028402c0700d03007001d41c020001c101e6070b140c08040807202114008122031000000107142d050010f800c560041e60112004c903600d20041c030181030f0348503d03201201083e000400340e00041c1c0c2c8481840280610504103100c04517002458001c1032031050b5002806035038814003003811989052107160300100d0742c6042d0646c0c030240008195490807852800c41d04040043c2c0309036190011100002c00004140501d105003650004449403035500c2031100601400b0040c04843d8200b19810003100301030340c480d1008445d09203107500c0c1e104104e441503800900c040c0b000034030040c0628003501e0007944004d06000140c5003402c006400d94002c01c480041501c030b0b03601d000d40c144c0c0702c00030010404908024103412041d0703c07040744503190304408400c0200c1e400920107410948003284442c00d8442880f003c5513008140c1e001049256004100e09003140c046061480c00d2003a8405400740c24080c000c0094914680c04400b0410240140b202c3c64071001d421094 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 603452266 1250 603451016 603451021
    0x12117031f09061401050f040b03100e091b01020a030203090f030703080c0601050301050c0a0e040b0109081207140607021504081215031c0e011d21160b0405010507140105 75
    0x40c00003c051520a0964042415461011543c4079004980d121811019101e080c107091820002030f41e040108184103030602c511010408011b040301c41489450240020704244604001003002c100c0c540544c1415940050b1071100083e401100352000340006580611a41c1e882c4000a8980481c80c0e00c041c1c039440001940014500c03020030003034103948060b4020b00942c0c031440820b000c0e03446042c1240380000d00c0340b00120900c0c17034980c00c4242d20755414501200c43d02d44600501d410060300c90703407041d00c4800004024041084603801500720051082c042c00452a040002944540e00030700c401c00a0381020000900304031124041e11864050b0b01c200103002e2410781100484440201e490302c4c800d101e0780d4603140d41d4041420f5105d901e1211a41c4034a10341100300010744805070700b41d00c44c0500d001c000d82e681c0c3c0c0c5502c420044aa0702c001c48a07061441c082c4038407903030303003020740805840d0164490032000b4003840000500303c8044503401c2c600300b95150254202400d401c40324180319080ba500309070a = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 603453516 1250 603452266 603452279
    0xa0510050c0106080c15090112110901090e100e04080c030406090e061e0409020607060207030906110307030c0b070302130e0603010c020601081c05070b010e012117031f 74
    0xe00981c40580c4001c00c880d98490104550b10f4240c011115805402994180c017018040c20107031000c000b060501f400110402c1c20f005040d6902500c800325001c1020841090a60340f00c0400d01c0101004100c0c4032542c2000c964180d8100f4031806140d06480c0340601080c02c11042400f02c82c130060103042501e407200e486000050108140e03104900002c00a00d0201d01c0c80d24107106d82022800800c181c100324440d030315081c0805050204000d81e0b01000c14030014010410900003010045c3c482c0c0e5900581c4c0b4144100503001401231140150594014440c580009401583c02e020440e042814110035a643c50422400391043e516030380f0700241489070001d801c04000b40743d280503a204400038444485024012070f0349100074402c1c800381b90312040c2c1d9a841444640c0044140d00801e2400c0f40c80c10500d5190886092800e901c11510b84141c6c00c0100f14401c03020110b02d120114121005820402035210300b02c0c1b10704e03e61200d84114900001080300002611401343c060000c1c09400d4001540d03600 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 603454766 1250 603453516 603453527
    0x9130e0717010519020a0903020922120305010b0703020601140d0501020d0f0b180613230103060606080c09010818010f050a06141c05102a02070501120b0a0510 70
    0x1d407010440d44038202c5120001300c0318000d07184900280e5951080c681d2550b020407405110240000010900c10b2560401d00700c0d901e800641d03590701509040440607003400d801400c0300d0050303002203020380c414040e4000295003c1036050440b03021444640390050b801e40041c20008070365500424540c0300040080441d01c01d03401a044400b8401405c000d451480002d0000205c00c803060340c01d542c1c12450010300c40340741010942441980000c800039594034060b40c10301440c4078602d5099800800301c0010000c000c507500130310004d040245080c00c1c1382e041c8001500014041c1c000d465040c40300303801c001802c100c01130620b041d084480c80024050500310100084c0148800e0f01e00301c039124200200410030150686e15280c400d800a028000d20184000c050000500980c3d800c8401f40540b541010181100c0c1c010001402401c1d94000602d01c0070740070f0702814480041da202c040d90850388003000184e0700034500881920260070042500180640040d040c1c1406804c030380d50120070b000300d40098a0f41710 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 603456016 1250 603454766 603454771
    0x40806060910050a090e0a0c080f0d02161511010f0c140901081b0d060303050924400e01120b0411240d1109130e07170105 54
    0x65500e400141c0b40c440c07071070318580c0082c015160003904a01c030401c106030343e580c01913550b0015007082d00c001c0443c0d5a5556a6280310ba403001c40316500c07004000701079403011311421003000071900007400d030f00000a131021501d10700b510600450000020310080b0309801041c1c0000740c54002d4000b00150240c142d42480105030403a070010014018003508610100031804455075040140c42d019810340d902c8061000140d24003080a422410070700040c4015000c80c0141c0000c5e6100fa11055107a0742e610050107910b40160341088060044141d0f044ea1201682040703407030f0040c201060080c40f490750a02c5080c81c2524001c071645200344068801c140d14607002a60040e03400014003280180d0380e4008000301518003d001921894032000450000f594003504d220050030041d0445140c450030b00785c0000068090121415500800540c60031910818031030a003244d40c0308a035150501c1c188001140c0b000340d00e949220262a03681c5843e482d134071810400040105804006130303070702905a0307070501d020f00402d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 603457266 1250 603456016 603456019
    0x22505030c0601080d1407020a1e1203021b1e211b04060806360a0f02130911090403020f0d0e1f0e040b0109120b01051008070801181104080606 63
    0x41b0745501001d0080213080740c0d01d19800078401c42da20f90420482009100d144045408074062445002403a40341c2030001c120424040d03001f9007a10300ca61030290b20b5146100040610504880c43c0038072401268030a006c0480340b0580780e41c051030b12181c403082e4001c42c1d81d1519807030301e118002c441c0c04104210354602d400500103a80500071b80c0c0d0b907104010342c2c8070030648002950320000003c4c103039a8207581424140d002c00182c07140c200901004800c5040c00240c28003550b46a0301c1c2d03070031034041d404c1ca102915a03441fa007840401040d00981c6407850443c00e5455803078418400c00340071a09152080050320000b44020054408c402c420203009480340201e03403583d501030302460710700d80b078100c4070400c0c00b03404c9801d6503c2c0c204101c1001c008020060040300c10700c505001c2e5000d070100c1d03510b9840c021006003903c219036420442d414101007100140e00010040c00300042e403000c10400c25803181200703045800d6500521020007176034149070054000b10f02d40c0c2002c2c401c0800c000500000000d955802401d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 603458516 1250 603457266 603457277
    0x40b0d06050613060321090324060b090303040b0c01060905090f071d0402040f0905010507320f0c120f030106030b1e0d05100e031c022505030c0601080d 67
    0x1040403a400aa0304e05100c083c00c07076444600b407005480d10304001741c4207000d4030741341842450b6100d07968030a100010f01e40c1c141034104c5034280c0c500d41c0159407107104045c0110441485c245034040000039a648500d003d000c507007060105606c0d8001209403c4180070b040403c0081c0f0091808114003550b440c0444100e9896114071980050700e00c5e010383d4030340c03402c10a0b00b003903804036940c6400703100107000814040c803403c43c1c3d566041c001040b028420580a2030300b50b0789200381360b613450041440a100014900c103207580351a101c00618a551812200ea8011501c0b5580e2200310010b80c0e103080c00d511800e42c90403084001450700f511410031004506a51a0340c501304a1201c011092044002407000c11405170301041201c00b99520b0000001350391548290115036000304102100d1f015a029100a80031652020038483c0752291090321a40c51405034000c01c50510031614900182145900d81e01020003800340100000d011060040303071707002ca605508881155958954071551050021621130000b00c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 603459766 1250 603458516 603458539
    0x3020a05060c0a0e09060303071b0906050a0b0702191205010902041409060403200109050d030c05210c04120506070e030c091f15080708100e1302040b0d060506 70
    0x2074003405407070240041340e507840e10380c400350360a001d0b11a0000d81700c0d96040c8402e1182d00000344003920b000042e5030010394243c5006151824041c01c5d940c0640286104100d80f0347c0610201c041c0b0801d556501c1d404441920521455030303030881a0341550b8100c00d1a40c40e03884143c009210381500668841c2e44252030401409910420481c01008281d800b1405504045d01150110740705070300120300b0f126180e802c0740b0051900e0003100e003140c17180c03001200c1a40101c40001641a098800c0c00000815410003910303041084442c01c410401c085c078240c0c6080e441d0008149041564015240900403541c02d000102d006030a0050b40e03070004039203581c001011400c411003d07003400300b4942c82c13203200904000c031542c54844030100441c030f0171400f01482c000c0a4800040505105915030039080c2c483d00e48051078200103100510000006040c0e41c03c9001c1210302b00289920a00c03a190321030140c1902030341003c0c8610016000d041c800d032007194040300c0c46101c0028090070f540114000c180440340c002c40c08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 603461016 1250 603459766 603459781
    0xf0d0b0408250206031618120b090106050a03120905150d0506030f0a020f030a0506010611062802030402030a0b01080c0a051c0b0c0910030e0d09051003110904060303020a0506 77
    0xc2c02000b90030180600211710b44011080c001440d284141c1000d000d00044d4440c044032442e281e031b01005000c0c1140341c0200c28018045e0545800c0000d40009210701030030280400d240502c2ca01c0014030f214400039001d40c40d14460070841000d004001d00d034000441d030319603101d8010303001541c2004065141401241c5c2074900010701002da19083c0003d800c10805940070001c0110480ca02241c050107000040000600705002980c00307410161242d1034041d582100c0c40c0c0c507050b0020002401c00c1d502d200040780b1449001c0920680c0340c0920b0015a0783da0742c9201280c00d2110124004141094aa002107004107000c2036a14101c48240c80038460150760b8402c103e07103400e40036524620107004400c600d012403002c0c925035034000c42244080d1700d00690400400c03600805000d00000095071605c04070b05404080c4010388901c40240307000351059050100140b40d061150b01030005142d81e9180070700340030341130708142d448100c4010800c10865680703040194407803224503000c940b0340c0115000103d18 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 603462266 1250 603461016 603461077
    0x12011e1d01170a050601140f040e0a0b0a090209010b030c0c06010611010c05090a0314070803070f030806220f06170303040c050612060d0303090f030207030b010518060f0d0b0408 78
    0x43c0c58000004228036441c2034107025074002c1d69200650031062403480d021041d11180a541c0340080702038010409600c00e818614064000a8a0050fa0070704040300d810250340ca0440307a03030554414002d040d6590322808203c110300c0c810b609d0540320a010385000000c0d00c5070000001e04014040800921101030340d0401200c0903c1000b200c982c1c424407a10092010480320314000a88400341342c22200d1090301c8804981c5550000f1504803800e050000c1d40404140e03204202c80d07088107081e612079416049498010b40000c18090b401d6100f155141c034002c00c50703d040e410440060101c80d6074000140f8011202c141c136a44210b0b42074a032182041c1002a15061080860b041c0b503038140c0c0c140ca26602c6000c00c03c504808132140030303010152035013150b01c08528802000b028451282c1c008166103455450a0380c0c040105038001031044aa071802c0d8000c0d071104100d2641e0103202183d0505084610400155800a5620001d0442000c1000700310803c00043d0082111002e480c5c0308100184240051b0000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 603463516 1250 603462266 603462283
    0x90c1e05041a0a050f030f09010b0f010c11040b0607080408070e0103082d0f09090703020c0a06051305010e030c0f0102040f050f0f040f0911030312011e1d0117 70
    0x51000d4400c840d03042c00c035075502c00b900160780d40d860310514241c02c210344580207410031784414114076440700c00d102c2034482c24130812004960503103c284541d0741e80c100103082c0c40d03001c40007d03100500303031500400c0b0359a0350b40c40302c4a141c1c0001c042546404d00e0303091a81c07058000c0e008000d402c0c4620403002c50300c401168410f60489a1100d0720914001c40000c08500d050340f60050b08081403015601080200c80748405807142610b0180ba09440d0201c0d1800c0209516000d80044103040c4108801d08440401041c601c200c2500b044022406482c1c0e50301802e20f092039600c0103807107540307001c40303c0d046441d0100c0100349040c203400485460705205075105080780300303030300c00c2254100182404214504094280c00d4030b618008104462400d414030214040d1010401d48442190703981201038100901825480481d8005074002c0d401e107070fa44643c2070640d14041c011680c0026031690165009050616000050082c00c044aa41c0000084682c042c0305003c6c0540d1050b40300c00500c034400d40f20002069003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 603464766 1250 603463516 603463529
    0x6041d1f140f160e0d0f0303050a0603380c071a06010c11030a06111c06080a14120a02150a1b03051e0f04031e05030411040204090c1e0504 61
    0x1802d6444181c544007039100100040c509001e964900c10a0641d901010320b00320703d001d000c00b5000c200ca985001801c0341da0041a141810b171034018144040707101c00030880140d110201d40d105500c1c0c8031b840d8410b0050501e0101082000d4680704000f410554403003e01011841503500c068142c0c04480e84500d00c400071155107002070320042e607020100784501c403000c04940025080c0c440310711040e20b9280907140000551200301c48002407801c40f1843c00850300007002c181c06400c004250505800ca6155070b41031001070003010503010300d003072002c8050043d100802c00000700c0554940803000042c0d1248050091141803040c1c620000d4126082c5004040300c0101c1041d00415007203100f1400e400410010700709025168020007106414a45220720307501401c400d2291110516003460000c144403000703050900c3c4081e000d9504100d00c0d4001080d25000313a03005140c0501040c2c1200460300078000d0346d01484816042c0140d01c1c00054001c0601441d00d400300100c09031000700e41d039064940344282e10582c1d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 603466016 1250 603464766 603464791
    0xc13082e090b070f1b0809060c070e09060f0106030c1e051e0306030f0732062703011823030a09080d0e010806041d1f14 53
    0x11020010194116811918864000140e04100b9128440300d104115000710100d001c0600341442103030004659001c291070300b603880c3c40440b425640c0c441130740108148036000d80c401040400700f4801c03d11113000501183c06003030401d417428001e040d980e0fa00586a14284000b104008100d00e8400c0c002c8400d000c4142d11200408104541d09210000b19601d620301080741c00d00015900718809280035018020301003080307071241000070406061508007400302e003190380450b03c00c0181411051054803030850041c0f07801060f4910314440b2042554181c02e86922403400100c5083d120103211401c1046c1c0000c00b118044031030503400380740c01c8038640c1c0440503820000d41e205000141c2003000c1c040c11664030a0822090307090784a8000d14540180c5210342c04103504c40c500340081c1d1030401c445000321115281c088090408a00042c1c0854405011240240e031a884c0205041103082401e000010703820f41140c68200d6495201d041a40b160fa200c40304d0942002682c9040c030350340013691070040d090009203 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 603467266 1250 603466016 603466063
    0x140111040e04060f0f060801050c0301061719140103050d08060f040e120703022b0f05030403023c0a15090c030501061404110a0c06020f0906030c1308 66
    0x2040c0c0e0805000b07004488032901c8529041c1c46a84a000c0d01000072010311020882509010200b0700390303a0000d00d504902403040c00100001d5521071002c10383c00000c4d800c00031440d1102c514402ea00500ba1190014680c1002e03c00c0d5400022540854104e034061000d8400c851207261044a0802068814640c020b000402032590740c070307040d40704800c10000e00c401c13070398081448680e5100b40c5d00300d40380680260300310011080d00d03481da0300e80800b88105186100d00c5150a07820700030381f51003050903408040010120008003010f000b00180980744400d841c3d468a001103010840b07040441541682082c661900c007503d0003601c000540441c03c96101c0f1103100c00c000c03407040e002c005021440d0b054441c9000710390700002040c1c081c410b00c1c002d460300b04a01224205440c090105403055608280c2e40703c0401c00082100c203a210300d0141c00f13503a01500141c5d94840e005d9144242c0e00540e580070758052800400e015545107080300421401c030100c009500c50503514103425480c0c882c280d2581d1890483d5180 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 603468516 1250 603467266 603467279
    0x804050d050f04050a0803030a06210b0403090e09060109060501030905030415030209060f0304051605180c04090e06060301231305120406052701121505030607090314011104 76
    0x20786100380454080c1c0307040c0760b135590009001d090035a11a10042d08000103100401d941402400083e1505500b00106030440c2c07032040030340100000018041d1000303100400d007007500c6410a140207007a4035228102d14144000295102d600c20312071020024075020002809500a02850828a40041c00b0b1402d091070440310080150011300f41d070080560800843c0c03d80d94881015046030480030404a45910b00340c5801e03880d1040340c580d00e014110001e80e0800065503600d400c0d140381d00c1d00c45040e804a0b21a6038000c0583d0003a5007005201e10f040c04001c088540000807903c2c0310b400120000d20503d250710682600a01e014544000103000010000c0c201e8110791251600b51383c8205c084880705000b0300f080003a150400e4201e1000190b00080349281c062580804100f407881c800b02d01c070b246c02022000030304a00408001c01e080da0f40ca0304a505091004001428010403028081e5000351400540041000541e4001115102e20000c0031039a04141440348503c0c42c00c071081c401c1d1a0605054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 603469766 1250 603468516 603468527
    0xb07260108070e092e0b0103060b040501030b013506040504030906050a020a12030506090a060501050306040b06040305070b130608010b0901120b030d031d0303060303091014041203030c0804050d 85
    0x107114004c2d9100f21000b0424400401c0c0e840c007440a06040451002c504684624080c0c030f4848891504240c10258103008410b00041150200e90090a000803034020b00310050740c99902d048000000c08001740340c2030031110144e1608003258010b02c01c04207426540c05081008a03042502c0150010303034404400d201712400741c40105503469543c0115214606d86a440b801e8803109480d0400000f0348600c18415281407400342e03107400c0700c610700050120906000008181e400700030410f41c0b080c3c0d2031f00210b0001c5d0300d604080341c003c0c2d070700320003541e00d62030700c680c02d000c140e510207840c644c036070340f08000001003140c0f02d2090203041c0c441b05101145002c04000c0115100309141a1100c10559624000d00c882d036401c001100c0e2162190b1004901340c05d42e04100b02441c0388000383c811054100b00b04114040d0703404012500c07031843c111031034840e03841880703c1210503c1c0000c0e1402c84001000402080d0304c1c02d0581034540a62096400340b00440a080c130403141c05500380c034010541da210100316070840303000d031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 603471016 1250 603469766 603469771
    0x11110151a13031403070506071d01030209010c1209030602071406060a1a030a060e10050a140d060513080f03100f05090a090602161109091f0b0d0b07260108070e 71
    0x3134112070602140e0b0b00c0d028144030040d242c080c041481790841c01c04207000f00c0c51414000c0d00909086092092140019000a596040003400c10302081c032040b90041c020514200590342005e421034541d140c40c50401a07041c1c1a0044801d070f403254000003040c0786000e400305815180c0c0f60440c1908081c0c00c10b000340e01a000906a908140d0f140c0d50f01141401aa40c000d44c40b40005041c03982d0401c0ca03110510003040c1103038201408050100f8072504e031b1908c8451001d0203440d480180000c01d60750f101c0d00060703a5907500c44002d000740c00c0020910245560b16014601900300307201032844040c1e4500c404135030040c01c3c1c070815407c09400ba00003002c00c4a5680a60a028042e01015161188203514414002c682d940c003254404601c0d6058045400c0c40380ca10380e0312210103002001c0c0744100c03540141d0480a0004c0004206071a2022840340391151000d07408065804070304003410b406d01103006040150b40c18140358021211300c401165520b021110181242c00030805460040c6c188500c0b0080305400 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 603472266 1250 603471016 603471053
    0x806030f1f200d0209043e040b0909090109061806060806240102070e090a29040f0f0206030c031806060603190e030703030c18050609011110151a1303 66
    0x48500799141d1340301d0f0031080504e2401c7c4003480b40d00c1d030507540503081100c20011141e8210901c20321043c8083d108000450f002c1d48411240c101255032104801c42c05050721040060015080040030079520990840005c901803003043c013880100c3d1100d0781c00344e940e41c08660318104c070140740f0035080944036020100064010184191400310391202101d044400c01600c5000080c0d10949185080c4540d8500c1d1140900300c6410f02e007a01c0c0341001d550b0416403006070000d06108000d0300350404000c0600300d041c45030380c1d0245c079231a200e1610b040f0a2090360402c0f02d000c880d148101c40711410703608021134a10711443c0024401c504649031038140b40018104e0005400146179221905c2d10071450410240400318800e0350b004c44c150b034458400420102c46400c24580c41c0071248014401e83c2d9400c0141c0e4410f40c0207203003400f03203002d030f1405840c07401c41c4c10000401a00e242400344918052910042010740383e0741d460445070010016460708040c4529080c214071030550900c01d00c001b604d05421000301116 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 603473516 1250 603472266 603472271
    0xe0402010c0501050423010b0d32060610110a060b03070807120302071502030d050406111323010e10090302060c0c01020106060806030d0806030f1f200d020904 70
    0x4035a42d40a00311141658180c511810307855045016010701030700c00840078078610080c0000c001c000081000f1107074011009004103804051840d01c0d05d030b07025600001e580d2604d035840c035840c1080507240d00c0d0b99050714018000d050003000b10303404038011400044c4620414005110482003034545000802c01a94899494041c910000460040030440400034020480c00c06904050914001c2d140100c142d00c0300031255101014042503075004000c0d81c0e03215450301d0001c152541d56140c110010843d06220210110000c2001c03507220006080d07503c10368011203c0c5078400e00040701e44080d80c0165500c41e0f800601003c038910000e00746140a68038011107400e11185a0b9103907400076006030480c200309442d55201103240f904962b824040d40b002048c0c00e042890041c1000004681c6440e014042681032100304004a0b10f00c1d1010040202c603003516506a0340400c0400307480032a008212134620100a080840b040d028400c8800d0080342c2d9440d00703101c88e1800c40240380950194010810a940c0180d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 603474766 1250 603473516 603473537
    0x90a0e1f060f0b04170f0d0302130e070c0312020903070909260310090204051005070c0f080f060610170a020702061603023c0a0807120f0f090e040201 66
    0x60740b401c400300c003074100081016151030502d042c088040c2d000b545c102880d0752001c0745151094402050342005e1070f0a0740303401360740d880b030401590066680170752001100c00529130411442d190700007030390010710b4844e9841c034004204150790901079009484501d03515420464003041080724540c0480c2c2d019126840350700b03d82c131401c01c1d1001c0c480420b0502d100c5419001080080c11110004a98050a41c540b0214101030810012410b00001c04a244042c003400007610000e0061141a4000030601000b0038146140c880300d503039807619010180b40344070384140030100d00140b524410f910030b080c070690340302c545800d503540c40b412200801030840c102c0343e07508000a01c003588820b07001389030f181800c00e00080d802280d40340c028600344100c03445640e40581145059280424601d80f10310072400034a4460100480240690503d0400000180b5212000507694200300c5400c0c60701d02c00029640f1542c600d03403820301c400e42e1402d9034a068840002d112510902c17165000007055500700d4018500b640f00c21 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 603476016 1250 603474766 603474779
    0xc0f050c280210050301081b0d0606090c031a03120a0908010e03071205070f330903180b042102030d0c2a0509130b040b06090a0e1f06 59
    0x141841414004000c0c20a5036800540c03c20b00090001d4103031a10f081440c661402c00c00b90b848860021002180b82c10960f445107843e583c10703034031600550b0020420400165201d000d44001c0040d4603910000c00e040c0b841c41d046800180717080454900300a00640341d8031f000c0e10aa0090340c2d02128290050105100000c122000240300781c0465003401d400966440045080c10031350070303400c8603946c0104001080042c0001d4580c040341400c481e40440c5084c0405141c01851549400c010342d4a00c9010f00b4111802200016800ca044071034042d03121140d8251118080d41c8149603180104610041c0800c000c01c0016190f000111400da980f501e40e0035128420f500103801c201440c1344290005000942c24030034031100303001e140d0b04890000d850a1858501c10044410801e007840348074415a141000103c00206203071842b4841c03540131081d01e0181c80c05260440300d0074015103d0a000741c10200c0081c10044c001c4c031904078440710705801480d2481440c01c0303c648804802d4400444c0a844681c0010305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 603477266 1250 603476016 603476053
    0x8041e03050f0a1a15041109100903060513021c06150e1006110703080f130e01080d02010908042315090306060409020f010c030c020a0308030106120c0f050c 69
    0x100c210101c054155803d0078102018001d112018040811004005000020a03815800307114805e0640e00880c07038902a2105030294042d060000703401c00c4c0340d1018604016800003400064038482d003800c10a40c7c40c1c2520040c10903001c4c0c0c0001b5003003044460041483c0305011061125984194404200b03552444501c0112190b19400315405c0030307130314052044856125416a02604442c50850000250015080c0c0e5810321840041d000d1117000a294a0a070110401c0740c6103400c40041246074207580390000b11b1500001d1246a00a0060000001d001c51040c00f400c00d0103a0003181d41e500300707130030001c04c1d19085001c0a145c45000030342e000348110b035450b4a032012400483c001895915103c20405060034950010b040b40d114902d4400031074010383c0d0324820150510b40c2840d0141f2440d0b414030301503c00d4004843e01a6000070204000810014113400850589441d0f03514043c000c24050010016584000e65010200715000100880300d8818006030a000070785000f10749100341d441156501 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 603478516 1250 603477266 603477283
    0x14030d0c050703080f03040501050901051006051c181401020301061d01031416090605032a1e030105100302090a06053f100303080f040f02130b0901050d08041e0305 72
    0x1400c5c1c1c0401004240b00c4284649a03122251500900003417030501181d4802c0c540c640103010501c60089600742e00c4034846069200d2000074800100607080c859440d440e607000c1e52400841d1000c10507005800030500600940341207405548841e2140d004600c141281c060161552604141d0f45100004456140240d064011104082c038205078445080c402002241190800401e0010030014003040340340001d848200320b03420220001000c03140440303402d01ca11079801b660031403010f5840012050400100114101c5104940c459945402544142c0603806210a541e80c064105603042103954043da008003503a0400c20034030940103203c90404525048d5080c6420604418107a03202e00c00b44480400c540c00051195405501d40e1031950001c0c1030080003002006092080d201040400c035000d030400281d07590043c80c070f0b140c10f06a070040030010010004402d11a103d090300006940c148031030708202254024100324980b500341403450850781d4920003443c02c1440d20410001c0410381c01d100010 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 603479766 1250 603478516 603478537
    0x5240105090105091e1f020a0b06040603020901082b050711040f0f0905070e0c0a031a120f0c0a05010e0d02060d06080607030f05010e180f0304090e0714030d0c05070308 74
    0x424100d05c02c01804142150100701c10000030f04039124001485d000124416107607800446412240d54910100d0043c2030240d1000350024154000030602c42d4004c21051000403181511401c1e0300c01950306d9034000034600c8008808107404016500c041041200c103a01100c2c405480410f601c010304203020304503031845c90707040c44541d9102e50300001c03c002031040200034003407221881154201404400464441e156441081c15a15244104814603662003e020044020b021115030120a502c01d5100d802444803030b00035008240709040c107454504400c0c070a90304180d40e0342140c1401c000c00c5c44a202400da03000ea03800b50080c0104c2c0818143c41c020f03040608200c0d400b41c192400c1c51040581030351030580324460003d040c0382c01444040062034586a0003030403c200800c82d4810464054200002c0c801b0100c03080c08001004901420b66410400000c0026400c80d0002235581800d500c1c005242e110352945a00541800c459031481a03001540b41c900400aa465095403a610f2500c154030844495 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 603481016 1250 603479766 603479809
    0xc050d111207080c04090c05102114130b0a18050a140d0e030c04051312090810110f220f0609050d0b0c0c0a0605010305100524010509010509 62
    0x6000c50f200501c090341d2404015a01440f4041d030700e58407005105114010752380910700902c80009441c0c070030190000341004103032441940f030700c4146a0350045c00c850701d00c0030400760848004c0340340788044d5214061843d40240c0041100d0700c1d0040c111002d8080318601c494100c0c004000000810014030403c607005100c0ca1030581e0780184080a54141020641c014080c0583c030004611151004650011440c40484000420b5a9103d2070320218643e2494042c0c50f070301c075000c601180990082040000e99405108588450810607040800d036410850722061010703042c0801c59461703421310098003050071401e05000d103a851042d902e140000311544a002c01c001e04c0c850402c2559004060507003c0d00080c0c1d03880b410b4400383e8440d00681c00d805030980d0780000c0001101c00038900b00307021440780142d21110501c1035503980c2c1403150740c402580480c03510350392070079001c10360b10701420342e03003c21000d940c400d940403007088000152442e03001540704d241031100070080688159103d04101900400a0410 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 603482266 1250 603481016 603481019
    0x1506181107150e150c03010e0c070f17040e19110f041203140d06060f050f0a0807090f030c03060c02030c0d0509040f0f0e0d08070903140f0f1b0306040c050d111207 72
    0xa03046d0990127800710404010810107440802d04041c0304044c090f0300034881c2031100721031001c0d0711414440c2d070740805221002d00045c0b010f810044140c40c098998040c0c0305002c103103c00000780c1f503940718802d0040c80e00301e0104800c10010720001d0081c0710840c0642000450030945411f1200998060301c1074400480d51020103200d06a0000c1d0f0720410121180352880c204050394001c000507208501e0713404248a0050001019184030f00281c20107011651940e01d1816a6450328402e1680540022124181031880c0090210300c00030540311809951030040008a81c070100a40d0f20742d00000d01da68000e0b4a40c02d001c02800710500034994010921100014a0b4011122003418041095180c004203c215800d002c00f6030750040040301a03a80001c4560110030b0041c07800b074130300507800441c10114003a00850441541001c00c02140d40e00100c0074805480310352070101620b03120211401003280041311410b03c8241459484400d00b603200e40c66168114000d44c0018092445801d9041c4203944030420 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 603483516 1250 603482266 603482279
    0x81b060106050a0c031d060a02010e01110903120c010e0604200d11220908040302120105013005010e0610060801080a0206071506181107150e150c0301 66
    0x81140144110b00d80300d030800a001000030210104460080d00304070002100c180f04141249101030300c084010b2076a80d9031858503101902808174040607a10b25441c004860010040c000c0443e940c0400003005400d41c032120361900205034000c2c10306040da41d941d50180d0b68000c1c8007001a81e00030340c010707140744640840c410251080c0348040391120740509410580d1500107110820140c1e19401d084505460b203044c41c2d900c85090158404414424600308509a414450480f0042066a00949440495000c5444801d003a42c1c404c2c0304417104401d01409481c520390b1580c48000381d04c01c88100c00014002552141c40c251501e0509562554201c2414841e40c01e8a180952000b0071250038001142d6143c61800341c3c91340e00401d4041d00449002954404000e81c0204910210240300c40800030716481e00364082c04600007000b440e042c2c0340b50190280308170610742c080e503e940e603104082400d41da0050700d124000c0c01d07480841c1c01c1c0c103104a110702084503110b92121489100c0600003151030350726089 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 603484766 1250 603483516 603483523
    0x91b0b03040b0601020a02130c1106010311090c1306180503031305030105070f02150601052a12271f050c10200f040e01080c0102060609072109081b 65
    0x101042c1c15507001c001c6c0d400c0183c03299001006050b94111002603107655018081e201c207070703403a85000c00502814001108120a100d0355502c04034040d036031980280c0e11104c215446100f1001c0c6001c140301000320404c0790700c0c8a445100c414503d80032039414060740e9240828039681050240c5181c12004100510060800f44a0550300c2586442c01841e4035007041d6019403a409400140e056078442117000900300e901070000c03582d400100d10070107141f59540c0884100c130710301c2100d940d83d40c6018800070b56014810000c1035442d01240d04800601c98040d110480e00c0800c0301d904070f590843c160001c0200c1d030001c080b44002008445031070342540e94170302c4800d05091001490640150900d403c60404107091540840c1d410b2011500e000b90740c91030f22190f42c00040c0102e5116250750076407400040b42600d80805d2621b0104000c0c0c080b50180e803038600400c0b0455008a500e040001c0d14901480c603050350b640c011a800807084c0e180080d0f1803016480b108941d0b4012002c0540100b4499048000c02c603040 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 603486016 1250 603484766 603484771
    0x110120030901172802210415150e0405211c060e070507060902030118030210060608070e04020f0426010e0c010806190f0603110c030706091b0b03040b 66
    0x1003007141464441e5040e113034000010200412804401c015450b482190381c11282e0700242011910107030486030710001403c21007110b08441d41e8030f021044c0c54000085008403001040040740b41c0c0e2513a41130030005120000000d00c265400c3c4101d900242d0015500844500f4090365540450343d98102d520081c8200d0001503d20310049250500810550f00c40300c0000e81c000c412854000d0761842241030540240240840c065499442d1140e4025172083c10308240420034401d03002d031050354401a001c00c0c02c65903584180700c00318441000203a10940318406004814400400041c2030003082801440550841d40151280400100c8606101e003104003001c02082e0040000b44046204000d00648881a06800d5414405040c003ca50181d076031030036001004407417009070042583d80b202050030046043c41618042807404050f40811604002110321480010700114a8480c80e550b42000600f030f402c500b51014010104c0000e100c85542032440002c0280284441c1c032414142000380300d00201 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 603487266 1250 603486016 603486047
    0x106080106180e070c0f06020307050913090201021e0f03040f1d090714151206100c02010903080d0b0307060e1021050910020a080f06060703050304110120030901 71
    0x4424200000311080030504d41c0451a0304e803031081500c2c24500f00621080038200104400d00104c10132192507070042c00780c80101812524a040004da03248888201e03400032801a0040c0c001d03840c1443d0b459410001e940d40081903c00f00c0b45070010080c48a825030700181c01c01d843c40081e0740d00c100504200e90300c0c48201241001c090a2403401c0c1424525512401da119950300400300c520071598a507030b1800c0c4040142061620b150399803600011403032035080c0849025106800070f400d416a2244940c982c0000f29606850381c40307400781141c0740c00c1d400d40c120f800c14824403a1148682c030030b0ba0b24203000810007081141c5403241c1c1c0280e00c001308141441040e034004104841c0700800304048800c4010b060010810b440c00007400e17281d150b407041c04c00c2034065802110300c1c000664a1200c95100001074860114081402d40580361201040700906c40c40c032001d0700040052004c60003180712408800c882c04014189000c8503044240c9416401c42d252580444540010a09000035600301001c82003001a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 603488516 1250 603487266 603487307
    0x2a17010503030c150603031902010f1515050c0a1b061101020f03011e090c0504080609010501300510060603050a090203250e0a05090f0a05060a05070203120106080106 73
    0x400100b584d90b641518012002a43c801e40440ca4549040c0f0880d0004d00007521420032107299410082d0103031482c20300d40310003180703003034a002003a9282600210039210030340400854060303909402c54458021000b1880c003806400141000202c5110a00e0407880c07078840e004440341d01e844800f41806483c2154059280d0041003004090242d080450341540c407880c0390580000c10401814000181c0781e0846d440d103070f28015921024035085400742c8103e9110000300c1d241940ca10000c4c3d030076204203108020b10066289281102d1103160f03044410040c081d000c1701f250304031017515118071784040140ca4030035039941d52806008042d4140900c1e5031011a500080c0400006603011941d1808100f01000103104000003980d40c40c02c90350124001001850302005140c00c106010b0b00c01428240c42100c881e21130682100c040e8100440c04011050704800901030646d40c22003003074080c2030000c0c0440d0450104100d442445100010180d019100d0b42d07580502942c14400d02814020203141d001c4845036 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 603489766 1250 603488516 603488527
    0x80402090a06030f23061f17030901050f070b070c12300f0e0f0606030601120b19020703030e0c010e0303030117010b0604080105061c02132a1701050303 67
    0x240d5040301c507001c6070350002c5c000401840c00495404200708010381c0b100c2a004000500903043c2c0c545a500100d1600030440b98102ca40d559558010041300100b043d04940060045034130641c05080a8100403000b440700d5498200aa43c50040c1c0103411030f500c0000c1000c1c01c041b007040c8000d42c03200d116594a03600f44960701011503059101440c031513040407428580e59a419000ba0403d5411010140300c1d080000d000440380c26401c0c58a078103080c5138240440c8500c400280b01490000b51042c100c5819041101c031166140c1c40b4140468402054800784440f0f0003020140c540b814401800302074001e9400041304800002c81c00d08040c94800e0090403c110320840c1d03a02960088200c83c11034100d00f07103803d001c80c14580a10301501022074407503032050000c6030004d5004819003005100740804c80b191003074820b681c0000c60409480e5200650071501c0c0ba201d00f00d90b600c0c0742d03001c1070002003854403404400301140c030071919002000c1d00c1c0100081241354140310b000749500d0664090075088000d0340c00c2c007 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 603491016 1250 603489766 603489773
    0x8160308160818011b020a0b0907050d171309020d05010509070e060304020f0a060f080a09120806131109090609070e0d0819030b01110a0803060415050402030403080402090a0603 78
    0x12001401c01d451400c000d680783c9694010951004480004885c02c4001000300841d0194880041481c10342d9460003180001300103440102c0c510041c0e0320020011082c1c8012500c43c9140b0400c901282c442802c1d0400240b42880342e481c968000078041198090b0b900c5022100f0380096842c10380c03089015a40400507c102c561300900b2510080c481036500949a42e146c0c0000340e102004d00b04015000012940041490383d40000d81c41c150303407030b16283c500194841d1452001110810400038100d10103c8048940c2c43d4411a0f84c03a4010310000c00240c0e180c0030740d014a070304481c150003c0c071110450000b0406403a00308032014582c000070440e210081d900d80b08202500040c40c0010b450312696000c3e00410410080c1e005072030806030b0145204145c851041c20240c000c00321b280c1140d020070b04180486840c85000200480c00c0d6070310426542c01c54a403071040c4409271800803c0580c20001400c00403e451700c503032014600c61030082e5102000f03410240140552120003802403d080740c02d0181c2400071 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 603492266 1250 603491016 603491027
    0x121424010e060904020c030403023a03020312091c091e30050a03080f092b02010b030109080d14010b040e04030509040911030f07210c030816030816 65
    0x3c1d4807007503401590301c09554035114214843c1d6000250b101c4e20380350360151074803403800b8680c601d900108c51035201d28803112418146021915002001a84100004400c0110040c0d41e0f0360040040b00c12901145600c442040184180c00780f042c0006005030410080105440c40304400000c060780300041180c1405000300350f1a440c49010900303009420940880b000c01010310500c840c0e0000152801c8420300d140080c607813401681c1181c00322032810045155010b01043c0b21205240c400c010b140d000c8003400b00240d800031401c00b10400d6540e12980e0f0307441d41e1000c0c000e20141600c592441596901d40c0b40d41682250722101101068110440042c40070491110403242550384041c015000c6a0703a0749000c9032036129161145400509101c1d4441c10021100b41184064008400707803180100c40140300c1ea074030b800d03600c03550b81e051107107811407013800d0f0a10340b40300d4240c0d00420300b008401c1c1d100e49406045a20080412075149405002d860606900040c2250000a417807007600340200080d000811 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 603493516 1250 603492266 603492277
    0x7030f021c141015180c0c050706051914160219090912020a26042c09030c03090d051e060a0609060510031a120a030e0406080d121424010e06 62
    0x10000d951b10b02d40c0d02d406000c2d240314003556a0000c221a030f40368403050000d050303800500f0341c0d840b40b04620110100550007020074070442c9008600842c202000c0400c10781c542301e0700d014160781143c003100d1420801d0103103040140c040c092a1402045455080c50004008507650401808541100d014a00040d445804181c0164204074240074807000c107140ca00403511940d40001201d2465444040800b00b020a251404080c0410000015940c02e030115850b80710f440034840c117035002081401550318001264501090044040300e048202d030880a003020811440c40c402c45510a00800040c06840d0149601030040c1160501400746841c01107181c00285a8051040c1501c80c185501d0b1240b80c07443d80c1d80030400081c0a000400d84060007642c40d038410800503000130300d000302d501410781001e015034011501d0b007000400d04074840d1841102d00c107950000840d10f8948400301d4803c08024000060301640084c0c129400c000030202d42c1d000c400b00d07030040d1b5506103d0117030541c10503503803060107541 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 603494766 1250 603493516 603493559
    0x2e09050705091510110105060a0e06040c09030501020a03060821030705181302030603070b03011404090201140d05010521060c0904060503070305010b1207030f021c141015 75
    0x26842c0d0250f800c2d6180c2c12145401d4001042400400e08a0782c01000c500750503035800004c1255445240030321100110038084d1802c1c824820020034007a0a0951015580c03801601d03081643da5281d569140c00eaa104128440000703031a0081481710b4501400800b00f14648800c0c1e128480c0300440d2103c0a40c000204404e0600c1408902d1081c10080c3e40c04c1d032074070108000c090910301441e51000c0c1c1c009400a0b00c0141c0282b05087c80417913500361101c00c59050f180800c0c000d6110300d0308601044080c14000134200c2c100228030f104426480a0900600841d003002c44003c03420f0741c1030000307001c2107010914452a01c8885e0102a6880400c08140f40750030045840d0000e596080072b5001c03070081c00c055031107150075104031b030800014018103502ca801a044104c0b030748070342c042045000d5903032a40d09000c0074240508846040d401464003c00010030032558200401142031300385c90746c201e040ea4100c003080306c40e040300d01c008081c48c126129040c4540504691160200c1c00e2a0610300c08040322590b80307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 603496016 1250 603494766 603494779
    0x15020903120a1e090302100c0c050f01020a063903050604021c0b1203070803220b0a05372403020f0a09110a1803081210082e09050705 59
    0x30460203200c0c038064130145401805030003048210110003040f00c940b6200a40d0412000e000c08281443e0100074106180750507401480031a0941e2a02e20080c4800071600c40305031032590165009a560841003411058403140800c035580d0002c01c06030542d200144542d211b40d01c1001003e1100b0180b00400613007448116001410000704400719468042c00040741e01e0610005c0b070420200130801b402513202c0c0140d4241e0200343c3e014054100900c1c1082c00004104190500009071b25980c607174000c070f61214190000c10843c003400c0001d04072a00400b124001180f88140820101035903d00031000b000321030880180640844a40303c9c003295010303000092007840044505101a0b03918042d24001c0c05207080304002030b000c500070341082503010344001404154810703007500002c8603408084081340d402c1282c0c2c0345442d00815555003074050090510074014000e080101d84030000700314004842c3d0440f1382d20141d01041d4041e102c4500841d10341c0c021554101840b080c0002c03800304580040b02d4060354031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 603497266 1250 603496016 603496067
    0x30901110724023a20010603030207120305030f0a0902041a101128020301150509010e070509010c0501021b07210206090108181609050f061e0a0315020903120a 70
    0x40312281810b120b490341e412170b8803003170040300a010750158046a10a070200c44c01c0ea80d1702c20002c040c2045a98018012610900002e544014902d030388580c006140c00000a0f454203550024044801620401c00003074402050410b260520103038417500c0782c0f00750074100034007170348070304403940c2c4814070a01084111106030389910842054400d01038140d034014003e0100490a41c0c01e000c500c1890b1040c0d51003003140c030300000741c200d04c480111400b92290340e03212443c121105005603031034040c04004031060b6600b0402c502840b120170540e02444c400c1c48000e8402540340c94200e03d449000b081050402c1c90300e00300a00c005036501d10484507074030070a080c03c482c566509007469a0a801d82c4441a000e80102038a10b102c100d007441c0c2c00c0307056861540f001c12480d22a61403141c401481290625040708030203c880c0303500901d140080d08060700c010b00c0b41c2d501d661250b03902191100c0e1890740c52005500070403150102d00d014059184a5051200c03e10b0508e03152a00080c45d5544204409a14a112208 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 603498516 1250 603497266 603497383
    0x50a030b30030d05191103240d060c0305010801051005010e151201060201020703170601020c0f21010b1305060a0b0702040906090b06030607020f03090111072402 71
    0x1075510540c940f01c8100f1507403400a9000101c40d59240300c1542c400d141031080034141a018041c0d80c01140c94044008540e10000340242016012000040d84040300408900004801c0c0c000d9402d0130485036408692540361101c010b0a480d0094401ca41c4071030418002d010310b9a200c01030000380e04080703606105801070809035010600c60a0410041d030b403081000031900ba5015002098201d1080d6141400e080d61098090030000d001d4405034016008100e29900074500851121051702c030082141c0540c8075028481310903003104200c05480b99448040200076460729219145060a0308103042c0b00d28030b80103000803441c6009008031241000e003ca5201c06540f44c0e6070102010a5000354104940786540c01c1c0042200409c68040307100e84921400074084520109200c102198540015401c04440300015690040c078140a030400c0e00c540b990010701d084c00540c68241044400800d03194050030040f00034108412000c050002c0f10840383c0e42007074110508003000c840c01601e603403100d4040c07a120 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 603499766 1250 603498516 603498523
    0x230307110411070309060807090b0f09031501060f1b08090607050309030307030c02040f060b160201030e0d0807021e063c0910141f03080a050a030b30 66
    0xe507201d44680b40030401c80b0030540c02401e18410790b0455102c03450107a80d403c6040341c000c00c19004070b0001440038462005038801e1700025180d1070800034107842c590041120843c1030104240c0c0a0400a101540c0120301d07150880144500404c00c40046880d846c0d464860603210302c01d452009002c4c5000094178024018144142c840389107000707050740c1d9071b81e07020304000b41a0b105041d01a80301d01d1404000502c4c8c040d1502c40e050441d8205900903017000c4000b012010244080d410603818107444203c00480a0003d110744801003400c0c0c0c903408480e081080c3c000b49006800107000090300c17040e4a0400000800044140d442071440f482d078181030b2240d0505c00c601c9070300e80c50b01d9145135844505580c01580c41ea032010f1301c078194210807215280301604201081d103407058080181d1324564008603600650850044400f0760034030102c03809050340c90f42c40c5d070015804000d20400207140421401c0d030352503240c0202140c044080b190216000d44420080018a00d50303200039661b000c140e80072841c1c418051 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 603501016 1250 603499766 603499781
    0xc12030f03070813050a080d0605010c03020606090712020325050406091a0c060f0114180a0b0303131401080a0e0c131113080c03031213060f0f092303071104 69
    0x4c00761410042d00d45011002c7e40c01618900c0c000d41c3c00c101000c40c06500c180c01c2c5030112501030b801012140c807910140314258601500c00c6041181c161129403805005000660060741c5010002c4285206101507010703000040c43c190041180410040101c0d40e0310082c0601902c640716801c94031b485890500c064240708116085020740a40b600300150240382c0889681201c1c02c5544514455450404000780b141c01440720041c14907190010402c14540740d4040f110204020b81205c2c6805500c111414045450350312a03050794190600391050343d40e019240a070420510306c0240420b0b007c0700c100c1030702c43c0c041c4100ca90150400c94146401c540701c0c2d400c0a190003180b41c1007155100d80060120b103443c500d60240341000e108030151240581400400c1b950008a607092441194032515030714000d00e5880c02003994980d0300c94040302a401418803918001c01d401c8034000a18542916003d200c9131207869051480caa0038460210010101204903080f00f5407041d50700d47c0c0c84803003c00260081154 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 603502266 1250 603501016 603501023
    0x60303070f0501090c0509071b1401050c03150913060216120906090b040f03081b030d020414010306060807110f060108010e16060509060c010902120c12030f03070813 73
    0xe100c518402d0000c10b510160701e0a003d414503140540d190014415501402e45001000440845240600030010860000064814020300e5000f42110030480c1c00d640041d2982900544c001080c802d24000410510409c5481a64140c0051420b0300900883c0a96800c02070031403a00001d07940c10300880c60b450f408801d540315032100c1108078090002404603031035000e040003290410344d02003810300101e0150b0b4100c0f201c0181d0314400b207045903200c030540c2d003107050074442e0300000c100b84400605050015108030000c1241c0141c44510b080a0008441c2d02c44100c141414500b8000b40461981709880583c4203007142845401500100305851074000000c40d41d508500030f0400126a8500640004140302d420800729100c00a1006a00c040c0c000c2d980b0481010800c100302d107207210708000b805845650f0b1403000024100aa0340c0104110646a08104110341c000b000390000b1071a00101404108a806000750b0801c4a124605401844058600c10501a40300c1c00148030b9400b0f4840c3d88c060951 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 603503516 1250 603502266 603502283
    0x3060405031806040f0b0f13080d030b060c0d05031005030f01090c05010809060a090c09230a09030e041508030a020106050405010509060907120b0406300b0f06030307 73
    0x2000d003016074480e0000322844044030811860303000b10f89804401c0c0c809072003044544080b850300c0e100780051198483c815850008000384a6028401e2055400314002c01c80c0c04060003410741004c1d002012100e1207a4414440c01e41030060b10034460000800404021850410700d507640c44072a1b001a800006e07500c03072a81841013040b0844c01c0901900424042407003010203000058441005680442c000c8911501d0390380044001007005a1542000d41180c2c090b80a1070046130b11190424150f44040c5000080031a008408814030581602415403155005104110a500e0f035540100b480c102101007501c0780d611001410900c1d0728032a1604002c000110489580b400c0030764029004c2c5c0100e11900d48100d240100008240c2000114148521002489041c0e80d82e00d0304d5043c2c4a6452000c3c0c00e0102c50346e101040d41e44c5886074856003000e441c0c11080d000d0400d50466010030301c081100202c041343c9180c00c01c8000003841807600a500600d912416600959584000c40d14600458078050030460 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 603504766 1250 603503516 603503521
    0x111070c05090a05090604031d0d0f0c0f0b09060918070c05100515100306031b0e060a12140a0816021f05041401050d0204150f18030f110306 62
    0x250222101110740c2516030380302d240e5841004004070b88045407540c03504c1d04040c1c0090300080c070450706504520341d8000021001400200850107001c01080112158038003040510280441700c1c403c0070081111703501d0001f480341042c0d15820240a15000940584400701d80c4802542c0c9165118002402500e42100f851410003802091f14404403401d5400d40541d241800360b00c0d1290040b40c0c41a5030000c00c003109041e1550a111041d401031407604200f60b500d61001c00040c500e45001044101030841d800345060030f00000d2500720748080c0c016445001041010000a060301e000288400d41044031020001803541c00e141c28012012001005107100160b105001440e07144004112402612000c000400741040c490f41d024a50102d10080b400c10320080083d50845c0b030304908032800625000781802d07200000401660026084054444410120a942c842d171003003070154585402e1400c500b8440138a06120410010340c00301038545882c83c1c6014091207541e11a801c11044007400311000b51 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 603506016 1250 603504766 603504773
    0x2307050f011709210310051e0301090b0a14040b18030c120403060c0203130b09060403021c060b060703050301260a06050115030b06091309020a0303031509020a0e010c0302011107 78
    0x2a00034030036064905050f50710f1007402039407960503a8803070740440030b444201c0d609007c20891a03065004820101d8510542c1070002528280514a012442804072403030b9070900c1d090340802d50380c0d0604080d2642041c02c0030480480c44991009030405c02e06204018502540c2a00c24110301c11003003194141d101d8881e00c80e41c0c02d800c2c84001c00440740100c3e01080390600c0752200301d80700d10823a1140703420301c5040340042c442e0343c0f4244000c000004004003910714142e501d501040b4000d60b000c0600407101e82c40c000c0d81060040501a1010b030301c2c41181c0d8940383c80303001d640c042c0c00b9000c1030280009020307504d00c80e000301d07640300303076120034211b1041e41154040700071031070044050142405030400c3c1241ca5030705280c1142c0240a20403c001d402000079003491001c0c070600c41203224003001d000400351176440c80d02c056200c041250000d58001d85c1c002c100184010303100c410702880c0f580305180407841001002c0304d85a10442d241030b800024070b800b0000c01e1032030a040707014000320300c030031603240c0030000d20380081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 603507266 1250 603506016 603506023
    0x30603170c011103010b09100e180a0b0d0506130516080a060b0103020405210c0a0305060a18020907030c0c051c080c1e0f0c0601030305072307050f011709 68
    0x11504081c0c02803080d502d0b20b4003084403500080c400c0005408007800034250707a01d02905c42c0900c00ca6640f4008024035080400151041d05200344040c801070040300344140e241e128002d08480c40d00984180c200f085442d6034003641d504005100420710322184200d4402c000b0103000e40d9016800381b031521012152070380c02c0b4544903c00c03140d040300c0c901d20301814040300b94041d00944044506c01000b521030444000b100f0300803050002c015582c039010350f80c4510100d83d60700d46d4003000345000302e0041c04a840c040300ba80d01141c6181c440d408640c4856003d1500690b225419994003000340c1c84c021400741e869850540d0018901c65000300207000720541c040160700c04010f421070600e4640e40d1201e00b82c690040f4002c85110701c16000160721800148078401d0b03042e0400411450300d9a50320b40e8074001003c004281000c900723800032400070350001034900503c451039405588848a103914500342121410203241d813100d5a10400d03010b0041100070122a030b000704024161803101403e01c000b00c0c078159800c90f44 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 603508516 1250 603507266 603507277
    0x5030d0b03061503070504020f122502010b06190e12030d14040c1509080d0201062d271b02150702030d1d030d0c030e0c061903060317 59
    0x60310545000404240080c0e03507010007500084d01500a10741404c003404003a41c0440001003400004020405201c000300303605512840e502c48450340341c880c42d00c664044095a0300200d4003103a0400840780125550181120800f68544070400345800184405441860000058030b0340b2610701c00030006c46a00101c0103028081c00e07401c0070844a00606407a40c922101074174041c0c6010407a4409002560301d110b40b4035020411810306a21603a41c03000301600d00403000f10250b0050351110010044000c03100b00c900385030040114030308a004c50300118488224050322450444c860700d1000502c80780c150900e4444003006440043c85800041000500000602000c200046c410002622200382d141030001e4050781c001c0e8051490f12103140500b502420740140035201c0203019005568000300700b00001c2c140409000b1020542d0b8028481c058212440733458499043e0300407085401a030740d50303402210f03041990201c041c9e880e1030400314101c3c01880e85400042c42504040780026103a03044034060b09 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 603509766 1250 603508516 603508519
    0x13180c170304030f110f1504030b0c0a0f0309020118120b060105030c04120c0e010e0609071404180f06081c0302070b010501081306020301090c1d030c010c05010905030d0b 75
    0x10203000100c11100d60302d01c518400034019a1104000303400040c0d041c110341030460401003a0103000342e000000195003d00480304031501178000075003001040000d801041c0c0c000c1283e2180c81c03c1604050001e886040c94070342c00320405a80e86a41c100b1a070289208107241b1800c0280105140e8503040d200584454040c02520240d0400000510b55845001120700c15100c020350340d41071078079007040300410007a942e0381280d9046800e4030109040800d44590350081c118a6540551070420320148540d03040003920f550204107140f0b40c04041c40b9190000c48080701c501c14030709078288200c50380d19130003044200034120510382400c10000c0c2e01c1c540019110029602d03c00c20342504590081e00f80c080b846418801805a03600703100400540d80540199079001405100104005d401755490408981c000d80092650340d6881c66080240c03684901082d0484c08c800101c1000e0464110009a60706c80d030200c00350400100714008400c0100030f4004045080d0302100301c9446800086500c03010f040c0202940313 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 603511016 1250 603509766 603509789
    0x180903031401050d080a090b031003030e010e06030115030609020d0509120705070303050a0516120e040e060f0c0f040e0114040c080403030e07050316060f05030c0913180c 75
    0x110004003001e08036070480d0b100070030880c81d904003640e851895400107000b0506111111030300051301c00c4014011449134001c2d1030b8184003a400c51030007420181840300424100f0044c2c18540c00a030b1611000ca0341541d000102400010a000b50201c0142500382c11070040d850022071141d44404103604058010103050040d58048480d48241040a020300c00307002c0c040e648003003070400100740148014111a1401c1c68490300c2d00e2002440c0941460500304100c503141d5018480200841e071000302a682c031101207c0a00100891042481e0380d60f8010b42090031a03a640400308404241203c00c0b6090340444400d45500c41e59100005650207100b4416040341c00fa0407003050240e481d091080030070039480f039203034a00541c4668134210024a01512100c0d240c0c0304820011030540d03001c220340803110002c4000006518101a801401c1494100e411400c4c4a400d0041c0301e07445850780241c0d04440c00c10358071981c00313144aa80c0340c40074003405001d2010080e50701841034148090700002d00e041c0c88004061 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 603512266 1250 603511016 603511031
    0xa0b271501170c0f060f03100e130302031909050a0803090a1a1207140408010504140601060207140a030b0f150102120f1303052a0405070c140718090303 67
    0x141010b04010084581550414100203480b86081c60352000d505401800725800e0481101104a895000343e0301084200c0c4110700800850702030444e07596000490003802000150203941c065524028200d0740450901c09104046c0d85074411030b1400001d0000600c06080355030b6548001da2240c0c801c40c0001d00a00584a0106481030f00c000c450420b02c1400d10500d10b0051407100601d00e50781d014254030100010810442c0103407400102410240522400000d010b08081c6405461401c9440d1a0708554000300c004109054001c1313008411504100400071510031024002031100c513180d007008210040c40018040c9403030b45042442e201d103085410300b90000c144000160b0751502c2c000345801d02d0712401c01402d000346000e000500707000c070407a4407820401510b83c2c0c0d901d420300c0600144025081c0b4940c030925512031510512612030b1401342d504014070706011b800240307800c40d500d13005002480203044040801004100490052a0703030380b210940106030900000241800c3d050950009040001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 603513516 1250 603512266 603512279
    0x8060601020a0210050a02011508010209010201050105190302120307050d030608060603070312050f0c0304080a0b0112050309090903090405040b070f0e36010306060f080a050a0b271501 81
    0x40302c82603950011300550a413011640d08075101c0e130088440f0021035494505441001c007061281d44003030001080090f81b0b451566000a0840300140d214034481e550040e818000301c15401c15040c103490b0142e840750b4111b062100d003103141d8402c50390300402d9403090b04803019505a040d848242543c40d04425200036440d15002c041d50348480740000b82651161103d89030146004900030710400101c0c0c00402d041c17149456a580c21600903500c40300054103d50365a808000c0e8040740c45001d0404e854100004441d1601ca01c1d40d64018564124095920b9102160031007000300b0030340303100080050082c040ca280600c2e225403101703800d4a0910128120442507650b2a01607040ca148001c4042c000c0940d0003c1c642c001c80492502d03800b100c41e0340b0f062091b00b02c0701d50350711000240694061714020a40c1441c0c030f098660004596401504203800c00042600000c02c00b04005260b40d41107a9003100985680080710b1016400d03440c0c034501e030629029030340084040851452418a02c0300e500c00d40b540e0b40c422 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 603514766 1250 603513516 603513523
    0x41403030702061521150903040807051903020913060c09030308040b0c0f0a02010501031704121103010b120c040b040c090306020f0906031503011a1c020414040c0806060102 76
    0x2030710340c005078101a00103503404620214500305540c00514600d00c40d00c0b012103600d050800003030340001075000130140b2001c0f8821101d542d500301d181030b801585003a240101311915000280034880c45a003074120308512004004280902550b0024046812030800c0c0319020940c2c03041034402c580082c20701059075902e40c00b8600c041c0c03c0700c1e015112444290307240c1c1e4a0040040d0b000f82071007543c1d0f0042c00b003c2a98800304004d40669402c50700006015415428070b9054200d07000d03260401840b08100030320540d03403141c80c4041450390114000c44542255000240942205501e59070402e1005426070905000010b030342800341015501080102d11840901c4151a000c860500100f400c4e8542040014101d50082c84440020b000184c2002180e100080181c2d2084e100303016420100d000e00d081c14074003845900c2ca08201c0314010180c070941c40003c0381c4000c0301c11600d08180381da100c4a0f24223640751074202116642007805488100c0c40c0c645401c0e41c1c0c6400c1390040b10424418140003940070750000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 603516016 1250 603514766 603514771
    0x8030c060a18030e03010e0a0f1b180f27060b06120403140702030d050a1e02071701110a03091709221803050c010f06030c06050c1501080604140303 65
    0x1040b480110701c850b00e00340ca92609101c4000d8143d941c44c1a1140062001d0010b00c4c01e25100c1e42e100d101070082814a0f00307800342041d54051381803081100c20480c0209054814030000c450a4010035100100b40d061801800c52090f549884c10030000e204200100d04901d04400e58407420b401c10020f6661070500280f80102c19040d0b900481040124010030700848001150254610b081c919205596010070304103000f0030680c070003259020071401c0ca060f400240784d03000303045801d210b52500c080c0e899000390340e2804c62040f100321941e082c058802c2c8082c29040006e8a1415008440c1d5881040000800030800900103480c0c0e807e203500041d1030302c09031604903011104001c104011252080a9078491800301c007040c0303045d20360f5640c1417407442c465101d40d48103131a010b91203040d00d9001c000801c50a40342c0c0c1030f22944e5a24504101400003811a030354240955225140c815101e44801c1c05003860014280000811114080d00014004400080c5107115502c24030981000104802010350340b03000c107 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 603517266 1250 603516016 603516041
    0xf1410020915070f0f03030501061215060e1201020310030201090b0703090e1815101d1b0408070305030901090509130209040c090c05030103060e060112060506041508030c060a 77
    0x8000341030841d40c490000e03104090040003c20403003400c641c0c0d031040941170b0311801c03000b09840e14010400c03140c01c0059145217014862080c46594149400312070041000d024a0041c88216001d4070301c0d5407140440b800803024079100071950303820030100d410380410007440100c4c002030018401040001c03605058551380e80c1d150321081c1b452401c0c01c100d4801000000c004038081ca0210b048000409000c0190124040014000ca01e0604201043c1200301c100f94201c25207a010f0141591170404d4111107a5511480350200d002c00703080b1880390101e80c0e20031540b000c0030f00c0c440d008020003801004001000d9482003600c4203240c4a5503a03007408081d900c121420504039641820b0440542400791155a02a11503c081b015050716600303050112035060f020310002400c08001841080040d2040c3c040c000c00b0080113280541c9028403440096190303080c010062601e40001c1001a220741e00403410303461031440c0300d0400540301d5030b04641e04d810401260b0018030442001ca00d02c12040d10806150303014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 603518516 1250 603517266 603517279
    0x12010207051f09080f0703031407531b0a050c21040315110a1b080a26060f0402180d05010c14090310090f0f14100209 52
    0x10328a501015403440640c40d5100d49806000c00044d8014004200780d59030082070307549940e03050400404981d1000740c3e41950100c00c009114032079411080c0010b0803002c178200d400481d011700040c00503280e00a240d01d0b40f512003819007801d00403e4000080e503c01c41c0034612414070343c0c42601d040314658884c0000d4510410030080303541907500c102d001303001c0012960100d505141c031801e03202c1900c4010303000d2016000b1001c00e040c1f042080d81c1c0341d40e002002000900340803c2036180743e0300e03404e8841c12640100f03002190b00c1300701e80c01c5000260701d21130325088441780351120f48155001d00a0119455441108c4001d200b84400c1c0040c00070305103025110107415441807140c01010b200080d80102c0002e501100c400c24218015500c801c0d03e010210310a200214610040000c040d00000e01c1d031401800481003440030841d81d80b00002e000d04142c00e500c00c045641d140e94186020494180c40001d00b2510b038441c10352050001c1c0740745419407141c108017160399504a43e10810101d02440e10083d80c003c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 603519766 1250 603518516 603518533
    0x2010020102091e032a010e031605010e0a03171305011e051c1505031203130b10090c08060918060c030612030a0810060c020d02100e030115051201020705 67
    0x2060303030030035407400030f00034048034190060185280c034288908501000203928206000e10341d540d026042ca140c101003600100094281001c000e00300202c13a0045a0400c90100e00320700c01951441403c800540c2c120036400c0140840070444c030074a030b109100d00b070b2a000014800040c40c1d4824129500c0142c0d40740140400000045001c03285a03002411422025a031040d10300d5000d00e40d4444c070300c60b5052003414000d0051520084c1400c1489100c426900d405040c805c014007118440504a00554401c081196566600303029a03141505030300311100d49850311280314174440d000602035019480031a5800415030301c400c4003000300c1c2005079140081d6042030020800c0030301c4607400341d03400800080c5007170302e100d9090241e5440c5401088400b00081ca08a003401156601c0410644c050060f500d0401500042500400e000d0150400c00a0082028644a442080c4180f454413181c1d036004000f8040b1107854000c10518082d180030f92442916408601e1005202c140f00320740565078408090720941c0f = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 603521016 1250 603519766 603519799
    0x3030201240b07061a121f0b0d03030905103e16060605031203150607020f1c0602040b040603050a0902090403180b07082a070b070f201002010209 64
    0x81094620488442d1200c4a052820f5134403441110040113020001f01a402000c01e030b148150503132038460440c018900054035915071140d9034080348560b018100410041030f01c0c42e12034509070b0200781740005245080700e45088030340c44040032540c0000031500301d00004403400550301e900407566231660005204004001e51000703501005c0b18442c3c02500300160847d40ca4002c41d003011010411511404400420800ca0b82b1000844105d04d41c4295560381c2003440c40d60118088652092070303944140070165115071204212410a003140794081815911180d5509080e102c94002e409000042820303c0b001030481c800c0f41c0700701c030076094006040070b240d501c403a00c2c00d46507030005d810080410202034002084210300701c801040030620a509a0b962403190f800501e89a01200884480301c60f8980d00003104940c0c000f03000d00540b004c01c2e4015a40300d505140504a114146038000c0901c0d40244004040c55017034080f000e8040026540c0900454150200303d080340300e6502c131281d01071481c002c0d49105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 603522266 1250 603521016 603521021
    0xf04031101050f150a0e0405030309160b0f0d0b0a03080c010e0111090f12060f06040c08090a03030f0e1203090106060504031a07030f090605060a0b070c0e0402041503030201240b0706 80
    0x2048130140401c1d0046854104100c2c146c0700071901583c10768000420f201c50b5020401960352030301801c104000000303090950341c03681c9202d0510310590880004c264204d07018031030341c4454038041004199641003030740d07840c0030010341d006185000c1c100c1d4601012000c140390180118082010181c102a14110445040010700d0420849a6800c285801106c51a40e48100100e03800b500c0c410f203040c44c035458803504100660b11221018000c2040303203002c0c080e04800025030502000da150501043c260007401051005298034490402c1c60b10418402d44031222440004502a40002001b030122585814007510300e48100e20004140601f4070501c81a800c0c070802016401000700d00d0082912000b44000c001078800c44001030382c41a03665020722900e8501008000000c4c81030302803040c1804038945490100d00d00ea4480c0003403085111000508540e9550b003e241d60400160080b42055100d041c024000c1c1600300e2046a4007055190041c100701404071044119624409054601080c50360785102 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 603523516 1250 603522266 603522301
    0x1002030c07170a020315010306051302031b0f060409050a1d070308030a060b07050f0709270206120405070e06010507080405060921010b040f020c1203040f0b0f04031101050f 76
    0x20039020f4200c03040300603a01406000206420713905c541d500d0354190b08100d4101e81001c1c1c00c03004015400d81110380141c90215003038803001d882000a480c1143c2c0100483d08881640000c0c3e139200d140020041114012a40403601406800400b001448076501003032400c20701000e848652030340135000810001c2c107210000d40d8001c021000c041182a980c0c048110700747c0104004036480c0d000754a200303e9402d8100715407001001c0e90304080c46006c949c46038007203809240340f40c0160078070000c01e007541c107540303c50f4101c40e00c01542c424201080d18007420b18079100e03042401101d4050400700c0114039250320a50070b6035012500004500d2800b450102041481d6110081d03007604040200c210300707003012800000c4500015881d00104401c681c10f07080004030740c0520b568040140c030510440c017540400040c90840045645a120740d20303121414900c5903000c00301d20080003000d112080013058041c0300c00d00c0740900d03c03c1d214020320311603501c256401e8403402c03500070b0400c45c0d1420000301c9404c031010342503c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 603524766 1250 603523516 603523559
    0x506091e1009030605060108010b0301120302070e2d06090c09010c050d0f0237081b0a110306090d05160b010306060302090c0a1d0a05030a111002030c07 67
    0xc04402210108600c21030141a80e80803501026040042c8072641c0140741c5e104000346031032411981410b920040900060281c44d10a2000d400c0f0803042600811002d40a46401d2945000c541707004a42c1960081000200d04200c1e040810f0170341030261854202c60054038000d027038845540e1440c589002c0340e00904031141c1044060139036400403400a10400640700515590f64a4020700b004e00a0300d8003140403030b00a42c843d500c11a2058000603204d681d500c561680d4040e01c40032540c2d042050260281039900301080c0f4190b56200414500001c00303c80c150300c9128241800544401019221542121000c8041c3c11000c0c407140c80c0c5100e04000c2841c0050074101004080c1c0070b031078000c40c04009030021140240d6170f80c014400e42c038115603c503520040038110545401c01c1c04034020424400507030140b000780c00c0440c841030070b40c0d40d074008040074090103400c84411801500740160301110030076210340141824404c91100b14800310444400c04080c0300100030381071074003650410180c98000c011 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 603526016 1250 603524766 603524809
    0x70f0f03060b030708040c06020c06040b090105091305040201020d0e010f0c05070f0b04080c030a151112040501090308150f211e16050a060806120f0d021501050609 72
    0x20900c8450603001c0c60180a131581c4110180c034041c60704034094070058001c2425035005c420780409a1703071400100d030195000a46603030703204d014690060780d1074002c041c0c4490740001000146504c43e840d50784864803ca00076400c8640b001112032003a070750781401c401c040d800100820000c03242e05001c0d41301004440c0c850011985000d660369190300c41d00b00d5903000200e40500006003040513082c10400c640c2da94004070302402050010ba0385402c08504000c141c5010203407940d601c20204202a001d03106080000e0803500031514041c9001c034002d00303070070030101c000c24203400124082d5200080781403801d10020b803e130b00d205140c5070204413000c2980d4001c45984608400743c5003035200c1c00c0c021180132507209008030841c8201c1107211410302c200901c0c041d5040c107002d4000c0006030345283d100710860740300b41001d00c80c584494001c20b603681484124070010748900703a004041e980001844c05284407540c1d09540c1c29581c0d098003000125400e1040703551101c42440000c9081c0780096040b1301c03902030726104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 603527266 1250 603526016 603526019
    0x40206180f0418020f0303040803030106110f1006050301150803250804030c030b07030c0905092220120d030b06040e04080d110a02060a0b0a1806051206070f0f0306 72
    0xc0d0649600a8002c1070424803d1510740031820540740c22285c90508074040d509250a05540d0b41d40e9001c1485004200b08501c0310043c10701c801403004200109414080d1000c041580002002501c103a12985d03001c0e40c81c0801e0624400b1100444205540c0c0c0030018500d400840950300c80007407818074100851203c603900200029203030344002c0c40114825031115500304e01c1d44c1004080588010300000c1858140503400300002d42c080300b46026101d04403100b10b030b1511107101d00b115502e107a0404801501c61078a00400384090300805648011700300c4400c20040125005010b01c440305134842001c2580414286090f881c0250040b8080302000380010303003401d40e03428403c00340725030a42d000d45680400082c0c2c00c1b03808440f8080c050302d0b50804921b8500e003a0540300003e5491000401e0011010707a180e944c803000d40c1e03400c11002c0c000c121500c04132602c501c144103450000d00c0b82e0b10a1501c110100c8402c07551a0201080c100d202c2c0c2c2094072810007629190005030385500309100f403d420950395120 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 603528516 1250 603527266 603527269
    0x15011e090b07050a03020c0916140d0509011e06120b070c08120105011b0b06091009020a03240b1c061203020105041208090a0f15020a11010b09040206180f 68
    0x50308505002e14002c0c02d1308100f504000e8201541c00014a00420300003042181e0940904407001e480002440c084401642040304a6424050300d5010f4081c0c900344400c1c0700012105410850410607654581c651045614950030101c034010302c1802c0035102d01032071110203e13003440c01d00b40d4000740c181002540600b00b507481c111140d002900b4641d121011800611003540e2112105c502c000015040340000d001903226282c0c10a0020110381c03003110040c0c000741c00700725450714150051010300010f540b076645601020b006021040204a170800e001141c0c82d60f4144050310160480d5080310415148c920302c50b203070360442841e10010403025a201c2c100060160b4100d049811298065800024a41000e181c00104031400784611004c0181880c2070010301c10001c031348046582e5015016008181349440c050a11301c4441030f01ca0051361022071301403c03d03500000700c9070b0440040c03c001c0040c0190348042001114050710065007003901441b8250401a40d1020414204030040403100d2504a000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 603529766 1250 603528516 603528539
    0xe070503251d120f1c0c08040b1c02160201020c0409081e040e0703240f051e0306010b0705070b0f0a11011503082214010e010c0b0a1415011e09 63
    0x1940c04c1000e500900da03003d0002581e02c000303000d0310300f1841c14080004e019110302c4c2c2540200d0040030303100c07070000a1103800390406030102003858800c59415501e85005989980d23140a0640b01a405800b69010301e40c0300d0701d02031103420b0703507258454000313410720b0103c40748a542c0d800100490401b810080001080906122101c14400c1d02c007503801040145515204c280c1e074200082104d25001072007c0144442d03503902e118402912800d50304070040c0488408025202d210b000c040740e0305800b0350300000ca0b140d62000010155540103804a5001ca60f5400b034154081c812040900b444042c01d201e0341100c940704030700082c03041410000100d41078410100904000100f940115140d9100041d56a02c000700b8598001c440b10301440c0f08a109454010f6801c00e100c901111503042102c4d803000c4a5141e800f44d0104000c654028019509500d03145040350001c040c031802c003c01000e4014009030b0340810a0601c0100c429040c0c2d81c801c03020414041d882c1da108542c501c02c9081c00100d1001144031075020 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 603531016 1250 603529766 603529783
    0x90103062c040f0b040c240f03020a120213050306061903021011150a0f0b09010506030408070f03030506010e040c121d1204030c1409041106040e070503251d12 70
    0x260810606c080c600040b4a4080d045117480815919034100d078210603c3d0000c600c041c0310400c03410090f9a401d015001210088503507143c8034442c601c08562001c194410221403000e981040d401c4610340e0b241c003c00c000c0260700309050707030a43c00b142e030000b80b0042c14280b0f80c088044d070090512603c0024000d1138141400c1600140110300c105c0403007088001415030013480550201444204890f1542d800030a81082050140a00030781c8000042001c0040200894140d00d0700215540c820b440f052a00802620003500c0700382c00500703100c0c9401074a203010b2103040074510540c1c0300d00080307a54030603041014014190080750415124040e03040940b000b4021000081c0d1250700d42580c031811403502d5007640b03096800c142ea100f20702034503104035511420099500b06811900302140f1404400c0010310301e22450b00070740c2044071804180700c0581d411502a5000d403030740409007007108404400303d1390348524142c0c03030500090f03541c1800202400980c0707056201c00c201070941c102c038655404600d171500600 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 603532266 1250 603531016 603531023
    0x50918160215070e0f060706110d0e01020f09010e010e0a080a0b0f091f0908040e0114010c0819090503061602060108061501081504050a02090103062c040f0b04 70
    0x15101109800c990512102c200c070328040b1005580d506201c1e100400010303080c0140c5002d50881c24900499943e110159400603600c18001c1c402c0b00135410a24901d42c0000d0341c00440c40c2e041000302d103402401070080d1408003051f009000c1c14556030500448201c0140351940781400103c0142c00076a40360044a030000d040c40310000c044550f80c80c548030081640060414a040c00000184280c484005c00e5800c1080b1124002c401c980c2400a45d500003804080401020700c0390001c2c00040a221142a4074122509544a410007030f90701e80c019698110002c0f0000d041c00710030000202c440c607000a04400c501c0852070400151912600820700d040c900381d607542c11705070b0350405000c83c0603810400d03d0b0141803202c02505060500d400c00c0251040c0584c0b03454140030b145c02c0000c5074400c4052000044800007801444642407900443c03000307511208056001070304044001c181181c0340c041d1501a0710899240702d06a9a18171001c10070454050400c80c1c05025954600c0d010950003da050b0080b0300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 603533516 1250 603532266 603532291
    0x2010509040b0f0a0b04080d050705070e090f010e06100b1608031b040b070b07020703030c0602030a0b04020d0b01030e03090a1a09090403020d1b0210081503030c01091a040206030106050918 83
    0x1f080162443c000306031001404220f01000410009003000c69072400b00c0e4114405083c19840b5206914100801119092015807030881405403504000644500555a811030241d91a031503840e42d4140b8414081341d0000756401500c0c810014560900465001075034441140c48521206100c189591250340020540400400e01000340b0440201594211049000502100307107140d90291046031490780142046601000041c0f110340f00750081c800005000300b086507134003024074018004003c2070280c10f00182c9003e44905500e03c001048900f1802c00030000ca504500c1c0070454480007481001e07614034a601400884c10a03100d10500754041c0d4401e40280001c410030b82030082c02102c4052280800284000d414030250700c540004010711039440c60920324a40d54960b1403001c0150f5601459014403001900410303204041d17002c3c8100e54401c041909a41d20302c0541000141130984001e984000c0c204010400d20380244010440e111018003901100c480f00c84841d82000001c4172101980c89 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 603534766 1250 603533516 603533519
    0x1030608010213030636030c0204061806090c120b030a050102040b0318070b180a0305060c0a11010b06040b18180402040f1a010e010513060e030f070302010509040b0f0a0b04 76
    0x10700e00400300b2040003083d06100401d101d41100810000200701801d41b18511041542454464035002c403440e5000340c4103028007640c0e60741c2c1a14040c01d010000030203d2030b00001003140302290260201c3c00c1425914810300752070040c16540205444e40120354140704400000c40020028005040103004030040c2035182d01d40380c040d200540400309900403aa800c099400d025598604047d41c150114200c0325091255544021602030b51060304050400d1003607100b01300c070f03540501d002450700a0f25070741c810f048220f410340000d0903a4000544260b100006202c00d00c800c02905020b414a003a1086182484c002110042a6042001501c803a00042c105040100b9400d0502a00c50031205081c0e04108001c0780c0000f06243c8250f5444d1141049001c03c071410712603120702c080c1d40c085401c0c184542856076403544080c02d440301541ca080d000e070090042d200f0707000202155400450750181c441c0341c6480c0065080000400d02013181640c01080780500c6030070b0303884010501e4060418410700340d0341d4a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 603536016 1250 603534766 603534773
    0x20403140c01120212070c02040b0301050c19030905070509070215151e0a0519030b0c040905180a1506030503070c05040609110409020706140f07120207110f0103060801021303 77
    0x3e0607109a642d090040080708040c3d640844900d0f48504245040d4100c1900b40c4001405842a2201d255140d030800050104610000c00140760640e1091451500c4400b41c00e800d0301501c02403c40904246c210071800c00440c10840c030b070250b0240381881502c5454050700c0060160b0542a290025100110345a0461030f041001100650103845400c0c8450b5080b940001200d00c0894014540281d00700016035200840c0d1495070005103a1010903034040b89072001e901c05050f04540f01e0402201e0412001c500c2002da0b00c1c0c0602004400403002d0b24600303030036485268025002c5030010070380700d0b41c8031000400708500380081c190b094410561458a6031401702040142c2f00e59401c003040751850882480241c08030002140c04450050101503180d16040c00c0810003000d12480f000300862140e000c0080c90201080514031604554031010140883c01c4031000403402090300c010a0880303840d00703004442c6082c040c00d03d9020b905145c0402c1c615142c034a141d003640c01801c02000d66009081d01401013 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 603537266 1250 603536016 603536027
    0x7090f0b1c02070b0c0927040f0507090207030309171c0203040516030303021e04050303250b16030f11040306181407140301020c0706140d021305030c0306010303021f020403140c01 79
    0x2044003007c904207030041e20005e1118040c000401a10441010b0020000103020650007071800301c0b421519107280d81005009400b10110448900c0c4003c028003d40c1400300e0190342c524a12102c00800d803980c003204220081d8000751040d07505d4030440c201c3c4185400e42c01908400355209503400350b161038540240c2427030340c02d5280000007062130a000902898500206440071a20b10009070351085103801860350031110f14040280c0140004004c205911001c1d000031542001d440e5001c02c4a615541d400f0400c598080c80464080d074020802000800e80d83c0c0c200b45134000c04521b80e9585103510f0394904100328101111408160400001040032480c85105120120800e900079882d00c5098600c0603110352090089100380079411003100346131029071040e0f45200d400b4580031507840300200038002000f41a841440e129205418600c44503040100d1414105c80e41900140030062020610782c0401100c55042004140c2c244800004074107040c4241851064a6014280303841d1043d000401 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 603538516 1250 603537266 603537289
    0x141c03150302030d1d06041518060903060b01050c100b0f03150a021c02070b060f06120c0a0e0a0312022b03020706020f1207090f0b1c02070b0c09 64
    0x1608a151030801c096100404d07143c024000903e401c0802c064000c2c002e5040c01003001040d90000000304001c1000280e15441d0441c03c41d59440f0303082080c50000210007800c896000b07210014684000070000075805420948400c50141002818031160040e0503280c41107502c0322a0a003901d0391703a070182505103181c40b54004001540648410710382c54402c00e4001c080501940c2046030300240d94822407890b000c0c540355005000509555540043c100810072801c256449480366517080504ca85034500203046801341b410b080781c0100d59a0b034060f5000c0841e04580c0b140002d01c0035001a914142c0c0e9822180760142d0b00c9180c0c00000030b002418024506000340320b14484180d0b0a203249100004200095900320082e40b401681d40e80319403918070064003031100c9181c448003010641c598040d84000046204016070780c2e400780d40342d50b5008000212012442155500e00040012031107002e01212204808480448058904403450751503070001181224890441200811804480c0c54042e0325600e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 603539766 1250 603538516 603538541
    0xe28060306050f13061206090b060d030c020f01020304182a0203072012030a18050f0103050a09170c0d08010515160b100501030e0303090613141c03 65
    0x4a5241001c0103e00c0c0c0c0103100501e2482101c0d4107800b042c201c481904804041c000c808045c50b0245610714000003d8006410300b02c420440310300001d405810001100426244c040e90303040d103802d109409104c640200c504801e41180402c00001c01c41480080c44419009600000001d0003042c074100300650000c1308525620440b5421144080d913540001a00c400c0e07608000c0080740b125450707107a50740729030011481d95004005803144803c2e091b0040080c00d0008800d0f2036420300b0440703100356a54510341d540140307640080300780260b00240d442588465402503002000144150180c2c44407075100001e40b04818025400103448490540d0034080c10a090015051078001c5504000000c0c01d18031010f80801c81c50f01020071b465065806c030015102e441a0003410300400e600b8040d405240b550080e01903d8042424100b19010180300002145d1080350f070100a0101600d498541e114a01c21442040da106404105802020003090007401d030101e02400100303403900909003025050301c8101100701c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 603541016 1250 603539766 603539771
    0x32a1e07080405130f050c07050607111c032301030c060309121412040605060307061403010e07020718410712090b01060314070509010f0e280603 64
    0x40001941c9a015203081d59001c84540c03c0f000c608002c80c90091070000ca1380145181440144500300300c43c1e100421280e8091001e865030340e0341d0000107903071389204442034201c19440003240e14143d1114614800b8910340c40d21b0082030305040035031007001030f441408000c80c80c0780c0c0e0000100100980034081000a0036a07060501170010151225107100070040209410f0203100080d200307000c4c1d101c00c1110901c3c0c12500491400341802d0070700314020202107540502034407420f4408240e032401880444501403142a00360302d581e0a100d800380704484083c01000c250320910402080c200508405060707003044101000621003480d29102c0d41c21002c040e02120841c0710440c001165044081c421035080801020040301612080400c035941c68030401d03041541482c0a02031000c0003296a00d8a0403102582e5003440999102c030107103042804141c40c0003002c6041041914843d5008103031280c900c088a013080120a83e1480100e2260601191a904120340c0394202c05544610b002c6d082014000a1404 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 603542266 1250 603541016 603541027
    0x3160305060d0309030f0309051f110109020d1709091807050f0117060616050705041422020d0c080c01030c020106180e07050307030b09010515060403030302032a1e 72
    0x360002e0344c280000b82594600c50940740038540151400ea004040140000c0e102c28803075000740000c1003587d58201c00180c008500203000d035505004010105400408141d00020140e40707404111180e0000c0301c0c500802070100c1103141e580c10074043d200c0e40021a100c070040c00003140060510341c2d250081031103003030b00300c940310700c640d9111000000e00e09010720707840801d0710303100c0005405002d01492005108460704240080010214800e41250000d540900143c07002411040c1451070468001c000c41040c0c51101003103a0308800d440c2180350024140580c010a96103400041d042d0f2a00015102e030700c4a5180f60329942e00d4800c400c1c0e1a8480d10007041841d041c0b946251030500d298030150034140d00d03000c82c0a24140103101140003484000d0458800704d45e245016140d5503070440b1808080e51030003000850010f614103004003622070051059250a040d40c0e000d40c000d40003d0006840d420381d05848041d420801880d600c419920041101e1300c03a9070b03120600c4030441c0c1c0a50f5000c0d80d18014080c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 603543516 1250 603542266 603542273
    0xb0907060e0307180509070504020406050c07050612040b190603061a1806010507050f1005040c0b0a02030331050609011113031103030c100f0516021b041103160305060d 74
    0x13544040d51228200071a05458014a40c2c0c42c00c600c540140794801d10014001850b03542140060140b03940c0711042e40c0d28940c1c3c0340100100da0240900ba0101080c11500241c00584e8901015a2081d0075241328090526600c4607602140c3d510b030000c1300c0d019911503800068505240415100610494454071078080c6080000d1408802404e02410b2113004070b402000c1040512015890040c664225140d800001c080c0c0000307808250340940e529031000030003082d170001031012641559000d400640c519240e8500b11030000c010103101e96041c00e2110002c105072a010a5030401290258004000030306190365482d0031545089140c250384842001002900b18698050f00304813038000f40c241440c1d0084c000800d0540c4516032a0041c1402031070105800e003400c55100d444c0c41074102d08100603c3e541e1180711054981d0060390100542c6c03103211805a401c501040302c83d11800080d002051010400000035001c1c1c000360744d02c1e503a83d400c14050000d0f290f8144a180d6000d401140d03404041031003500c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 603544766 1250 603543516 603543539
    0x14150102070501080c0f0d02030a0501050d170f0c0a060e0d0201090b0612030705060705130e040b0619050607240c08040305030a0b09040807050c04060b0f13030b0907060e0307 77
    0x840c00707040c01320000016a01e0022a0142c0c0e42019440a019a8079403841c80f00704020b500c210784440000d86814001718850608240d8041001d07400f49031f03c10020030414000e135090b0403180c120306908008001345c0c40d04440911004480e40d22542d0040344401c400d03850641403a41c1202c1e07000071a0301d4849031002150103c402103800080c02d4403030030080480d80200d10300790312400101410501c6004e040c80a9a503202c0004d100610300d040c1c8041030315448896a440003401500c020740f10500031001b080003482c202d42640d03648410811003036111a561004a8034507041084203440080b180300d5079201d464407007007000007200940351041000c928800f0b03000d408010040c0000d4100304002c40020142e01c495403040c110100001c024000924041c542001075034045101240c07180030301d0310007200b035040c58066841907940e1955240c1c02c0c01e1542e00018502c1e0881c0f080102c1c0d41c3c51503100080402d0078000158002c00442000d05092401e00c0c9000c1c0581c106009214003030360040e18200305410300ca2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 603546016 1250 603544766 603544769
    0x6030703080d020906040f0e07020102070c0b090111011e05010f080d27030b01031b081902010c02180f0108150403030b120d0f020c060403170306180103061415010207 73
    0x103020740c0d071500c1903994420000c2c010079103d250041d200182c0030a505140e07003401d0084030b402e55458011596050412420b178000c00354020644002c000707083c8400c4130148003600c18080d041c50007075202e10014510900350b0340c22000030309000c028242440341c0c0031201c1c000c45001d0081380c07015031002403906d44040c2c0ea8041400d00c240800c200e10500d01d61401010010304900b421000300f00351a20303120f06005003030100c284002c4403400c2244904050020b00710861804854030708000d4002c0e0f109070308a800712100140d104030704100040c0850001643d03400d110569440c10070320711803050329003501143c40380354060304610803d500410f1006129170951052580c00b542c117240118022242d10301181810300ca0f03211152050242d0030003104104c0d40820700080700b070704990883c1c00c00707886502402042d104e40e00026200b40544800002072a040c10001e54120f03802811074100b0304134950100c41000020f8000b140c400c0d840b9603840f40107210100c1c80b1038010a4104140103030900680011b5030f1200b45 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 603547266 1250 603546016 603546023
    0x90111091c020d05030f03070e1f051c0e070303030c0507050309010509130e061f030201091203051c0e060c0319050a02090402070c080d090308121b04060f030f020306030703 76
    0x1c40d8101c000c5480b03004100d515981e00c01c0c100e0340c44000d621040703c4903410032241c0c1000580d400111850b64944200818114504c0318007808030b181d20000121150b601958612500071079040702e85001c40034900c1482e071824000c50282c469141107240060503034046400304010820144500c9012580100440b48500c3c4242449942ca501c0300e0041525540010b0140c0c5100d840c22102150f40346010600c64071031100029400c2d400d001c154800b11002050303000284c00078440e04010701650b60074402089e000740c041e08240d0305100700f180444044035030031300014034441d8580002041010040049541056100203010709610b4200140c24012a4210025000c103864101262108015604031003640030080e005540c0c4802d1400e00c218011014403502506109000340d100c035451007018580141c1c1e90040b10240352008055660b0214000540202c50081031a8044c0d00e0314103071000148014200381d111003400003c0c0c40005012174a42c0c01500c14000e00400c100030f56607401160050079240d1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 603548516 1250 603547266 603547309
    0x12110a091d100611160605070303050f16030b0a1518090b06070222060b090a08010c17070e0306010e010306050f04051f0f1d0d02011a1c05010c0809011109 68
    0x1110300c100c0c0f0380505d05200e441070001440e80072503207544c80700c02400c69138020b80b0706110303a0b11403004014582c0022070340c40401200c80c80b0b103908180d00c2038020301c1d81039400a007040300040d1516010803620000403158404140d8569004d5143c24030541e40384001c00d0f15800403c01d481000740030502e903105402009100d5078449030601c82c0c0c01c050000501c480f20620303070101300207503c404441c00343c1c0e0300080382e0318440c10f101d81c030008403c0414002d40c11040308a5480781d110b60000c41c201000c01d04094006018001080182c4115841c10400d40f8003c0c01080141502ca525608002080710009070003c3c803100e096030200300c040768000030a00715610f1215000d400d803140b100344540003444207a402e0302205051800c00341950340401803c08406a800068904400348034801703a01b200d00c82d80002c0e10215a10a884ca658540118124840d515103000148081400d568440c211121007030020301040d100014404400c2091054005038070800c50b01c82d14001032000040c8807600d641401c00c04400 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 603549766 1250 603548516 603548537
    0x50a0f030315060e0a0e090709020c03040b120a1d12030a1515030e062a120a14010605120c0c0f0706020a0b06150a12110a091d1006 58
    0x144264404480200031199010100d92a03d00003800140b240c02d9980c40f03042036100204040384c038102c2d80760084400304020075a0b0341c43c0550000203034005282200945c04184400900340100c1d43c0103202d46010302c46209040e02c0d000da6440100c0e1502000c03015a0803081c0b0420480707a00004040394034060b510080764880da01c0340007100103032880d960310741b500005c0c1103000100c00c401203201c0d16801e4440d8030284150460301800300d0340c2d04001c0354070303918126440c2030400c2d6824003141501c0c80c03080301c081540c0c50415841c1080c4c0003110705a411403021652032145007a0500c01c6035106024109030f03d8100d1810184030544025000041d2006190200006510740140400c101040c5c02c1151001503a04141c0e03203034006034840e054a6816603070303d103d0000040c0a450428414020600352030225400d202d4507001c1164040800e0142410141d075901c1d4400c14880147d01418100c0301030f0742d401c0005402e0000300c141c1d0a405e4045400414a494103000388945084008401c0d10350511f499040790 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 603551016 1250 603549766 603549773
    0xa14160b09030a0b100504090809091b07080703090308041205010e0c0310050a09020a0f1406090d03050a0c08032a03070207031e060203010f1e050a05010f0e041104061b050a0f 77
    0x82c525511450f41f041c0350100d1407080280010191041c2030048910381d6440d6640004195803403041030021207041c01c200304c010000b82c2d0080281c10207502915120707030b4064580d40d91000c43c5c0c0c4030360040111000183c1c030650420109004144841103258054129481c00d40302181d0788800030302e11240081c0d220400075035258450350042048907001801900c4040c9c1e202c0c20028a18203e009120041c0b0600c03030401c2441c04c00300708a802c5c0d4040500004020b1010b44c4040b038550304044401002c000b682082d0401040e41c00020318024bc00d80940b130220380c08681001010101c5414000754104014020440b882e500401c61600b240d40244001d204816215070408001401d00350041206102100114600c441000240e0644000c00b14800305203040480c014104501c40c4110395001410141c2032209520a0032410b10010311403c120503c083c400c0300182c240c2e00d9061180c00300c10001300301000700a500264041242c910000d01404070429070b01c840d502d880d02c540c00a04005c621000307800c100f = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 603552266 1250 603551016 603551041
    0x131e021810030203040212010c050a08070e040c050d0f05040b010519030b100512032d0c01090f051608030306040b13020d0e0606120c040903020a14160b09030a0b 71
    0x161000100001241c4802080103002900195004d901800c169030300080e8945052007403485c0012692119820020902022030390180c0090405003041500c0400c0181511399001d90350502440d610340a4445d503511074141c0c11038183e800028252401c1405104c0420b900f4100141074030000d5038a042050f646814040703818a190b03100030202000c6404000b05040c020015500740d032011682c64000711806490380e542ea0140c0c0031a020001803001583d04420300d680400000000110101e50a103c40b1003081e40c2191000d1030207440d050385a0000d0307020440140454080000b1034081000501d0230940c130107079203020051082d80100d582e40c8140015039698103850660802904003950764221682d0000080c1440c00c052074a580300343c1000c6203452400030b288114810180700180040504a02000081e00c0303808000d5055028401c1e005002c10750b007090480440c0b0000006000260929480804010250b4400501000d040c05403440035640401c4901006800c00030005141d120580030070346 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 603553516 1250 603552266 603552307
    0x130e03070203060f0a0c14030f150d030c0510020412110d021e0a080f03120c040807230a1212030b030304060c02010e030604020d14030c0714131e02 65
    0x14103100c1d910803c1320481884119611600b440c9005010b00b900800d03003070f10102c150021140c0605410f00000302e10515100005030300082c061010112a801310300891003500c1400800d40016005283c04000c0c88001c0051041c00c11070003030118501890302c0305444a101e880c2c00028882101e08003403000950f40d00070a011115001032104102d41e252a01606011001080301406920301d03440001e4080f80200d03203a0f007000a0f0401031494000d00b0b0b2542d003035014004200e42800d07401440049041c44080008901030480c0341102120a07811044480e407900690003054415150f10500303010b000c40340340c1100512984111070b062204900c446c140c019092031540690544404140001c469900c29114030b1428000e88501c6200c006200906442d42c00845000c0c0d001088600028001070050645d042d001d100007007505d003031600c040744507402c2400079444518103680705440500d1501d000700300c0540040800008100144554001d0b00013a62000c102010300307980402e4a0049510221503400c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 603554766 1250 603553516 603553519
    0x315040c0905180d0305060a1206180b070801120309091107021008070f030504260f1911031c0f020c07031505090a0b010312030914151005130e030702 66
    0x1150380fa02c12501c80400c280c0341140034540c032504507000c01541c081e2007800e005000140040c5140c80c200400090006c80d050002c8030803c2c0d403049008040340002e84010081889231120502d58140448001c000326010b811a0742a480301602d150000b0f5005550071040741d2440f507010a041c266003c024489014850020750409000710f50b840096034031242c100d20030100ca854509030903044140071001c80c2c2044800070040800d41e031a007500160b40c00c0c6030300e41d1070903001ca0161401220910b602060703000350076803c20075103658800c447c07055000410b035140e03c0341890003141003052140f1200050f580d083c401803400c590304d882d0b808103182681c04859240c04094111000250707a1720304007045030002d0b801d030307a045454980440c06960012829800044c0c100012108503429a12828503000da4610a542031540d41d86902d4000b983c04034490310a8a004800761540201a20b0700d2103102c0401040320009420011060103280e0326146c4000c080c4401400008412011085261440c82082e5019 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 603556016 1250 603554766 603554771
    0x1603110c0609060a1a09090102041e08010b0108190e1c12180f200901080d0e10090e09030408030f0c0c03011103041104110a0302180a050315040c09 65
    0x5500d000240d81800b481c0c6080441e180c5607510020f000031290020802c81c2059980222002245441c01c0207640200391200014038181e0350f102d0351410b11440514498400aa903070003000800c0d028807409181c1e11003800d1000d194a03014100b00312924125008454140e61080b50480d0b01c542008030800c00c49020649407051007040b40e0140c044921041c1e041c8540782042505240b03241903101d40309445074030258080001c00705035150901c1d05c46503c400b641540c004075503003074a43c3c0c1d6001d00500034440103010b89124000b00c0b50081c51085001c04003030080b070404400100281e0310400410446403a510b40c00071a80300d1190860030740c0b0550b88a00094031001c2a00c10003400359400401101c000c25086410b03150441013454240e9401010007c0703a010701303200242c08a80c039014400c6540c80010000500310113510704031100da4110070070242c0003c0e40801c1221903500000b002e080100b50848840d00920302c0d08000035076410760240860003004112000c2003c210540c41000d000d850f241405 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 603557266 1250 603556016 603556027
    0x140c0f01050a090c08071215020c01090b0105010e0405040203030d18050607030e0f07180b0105070c060e0a05030303060a05010c051504080703090e060d0201050a1101060e09060601080f160311 84
    0x80328082c0c640e242c0207031034551350b144000075002c400241c0740d8216108420050b90440b69502c555583c51100100410050b8007004000b0b0f1041c002e104001e9903600c07031001c100c05075060100040a86501004c280e001d58900002e0101594000040d07491010103600c004c141e4692036001882d414280c0300c0005d042d882904140400366070941c103c10b4001c50b81100b00d51100e1450040f030b42d5222102d116601650003032100340d20806100d030b003101c0314889040c10001c1c50001c444da16284403485542c801310010304058884407180c07410307103580c200070a001c0380110304504040002508000d214400c0030b06200c001c92107001003040030310030086201880c0109500c0e52400303091864090388413400c1280090042c80e004140c101c441c5048601900e00035100111a980c50ba005440681c0200c0c02c0d01c0030700c914094545150082401514050540362521450700d0502c3c5e40d1013864458090900e43c103100081d0200520010040116580415415000445151060380c01d0303004280035003c0c2c8120f40c000285 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 603558516 1250 603557266 603557281
    0xa0b030c09040e06010801050f13020108042901080616080115210c02010b040203090619110a020102090f090405030d021c060b07140601080d0c050304090615030e01020a140c0f0105 79
    0x10098106c4400c00000e02480d070b111007512800e00c40446510228a00030000c29001d54400e0400c0c80d03002d8400c0c240031040c0c128182c28804c50180a9507520307000640d19006200c03007541401820380140c50080456080c3c8150240070b420070105004d9001800e8001d1078030103540b4070844a20f91800071020ba0354201002454428000c2c06486000001643c00c0c4018240142080c0c0f0072030741715000400c003425194403000d0360140d240b426815030f02c05e0f4907161407000412b038450301c00501d42021250001652800590140404503401124181c0301d00d80b0340c810070002c00c80200c104c4403203001524005070785609507405040849252003042a01901d0400082100c06054004001c0039005030f43c54101090745000e01503640409000c2c201050b0400505003010900600051074810f01c03131025039045c291130781c496400300c45155015038401c0c3e003c48002440d541d094031808292261800082d803412303c0c0001c000d030840316990390003040200c00044e40d40400340103002d00b08a296821000b40650b041c01c01c0c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 603559766 1250 603558516 603558523
    0x301110a05030a05150a0501030216080c0c090606120126070b030403110d020d0315080d05030106170105030a11030c13021c0603050c091f0308040e0708060a0b030c09040e 75
    0x10703080088180f03004089172079401c01c110221109000200700c51841401c010045002e9000b0282507203180c0810071410000818032006040d900320300400400070710703400d030b010404001c82c0506500c0c0200d0080003800c1c0c000c0149000e09054511542003100419904003440441c01d0540c604040c0034042c0307200c04180000c00c50001d5010301e000356543d200600c00480404e440b100da505180d40982d00c48194070300010b00a42003241c0142c40700901444290380c84180fa410544000e0007c00041c500000601c080ca8005038050350603002c01510903607030360405010a030344031171800020b8681c89100d003900c05d50303680c1001b083c0d5a814014050098a030403404801010f504800ca4152000303420b000c6034110b101540c40f40004480c0c01c0750041c44c802c280030701440100c2c40c024010100c54800e803980c00580c401c050054000842c451a4125507841ca0004907000c0c6800280c441810410030905014940d5100302c20b640039202015102a43ca8958110b13054861040300c0c00c1350f40207410808040181000031 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 603561016 1250 603559766 603559771
    0x6281701031a1e04060b1810170d09120204020d0c03050a0c031401051309050319030f0629090a08010920060f07020a0b0d09020307320301110a0503 65
    0x30340c8a20400d4454051000c0040607401c1c1c0300f180b00241c840010007013422504150900c9030080d115814180c08501c0e80d03407661400f02da80c440b07182c1c54503400300414184c0240c032007101030307800c0090b0001d100010401010070146c0e00c14240e0010a81101105541da075504413021003c024034100030380c4012000c041e0203048212015185d851908030800340d00c601134041c0001501d6400a4000540e08010821401c0e018080c2080c00c256036400840700000d000300010714103195021400614041c0f50354006056403454404149200c0c1800d0f400c0003410807520360041442e03030b94000100e82a41810104070f180c011354135500c1e401031400c40c00050501c4198007961a482c0540d00c01c044c8441c124000b00808200700460ba50032803802c00c400c0c0462902440600103080c4024402002c1c0e40d500e100d22840c58000c03500100f89aa540d0181a00718a030030000c0708001e14110120a0703100702c45541103051500f000804680032045804c01c02410f0741c1c29845004001103c00c0c40340e80390400741d03c0043c01078008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 603562266 1250 603561016 603561053
    0x20010212180108010e0702030f03150910030b011208090d11040c0905120f0a1e12110d030c1d0d0506010902070c240c03020a06290628170103 62
    0x1450000f0070b0380020b0175a10f0b885200150029460002102e82030b4809074030043ca90b0040200c6d40183c080f035035503084051402007800000e040052400c50a1036100000181d01c442c80c205039014060000034221400c1d204a0403003215598090380141c01c20080068520300f6941d40030703240c13200c1e4140300c98000c141c803010707510141c03aa0740c1c1c6c0944000f5120b0390787d0201c41040b003044d84411140c0c400a000c40e99000100380c887d00001400105039520349080d00b11040040340414990210007000110401226141070ba880c0740034840007403d103501402d5101d0048500d40440700c15990340d881174403000528131070142d102e003c60b143d41d80c0d550580c07802074120781c800b01da110084c0c0300700040d40c1c4524414012003000a002000d00f1a141000540e0441c51500084095015124081010a84603c0f40c81e504040402d042640180c0c8200c40b424080d061000042c41500b05100d0070a51007607900107400590403c2140a4020724545416140b50940c2e080c080c410002c0710b4004002c000c584092035910214 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 603563516 1250 603562266 603562277
    0x9050922061802090a1a01020c0f151201060909110a1d0d0b0406020a02150106050d0507120c032f0304060c021507090501030b0d150f181b09020403200102121801 71
    0x201b0001241c6408041000c0c56000340c49480f10324007403130a940403c0d444551400070710b00e801d0b1710107030030440800264851804109032000c200000000350158000340312154104500e85a540080a03004120004880414641000607410941c03100c90681046980103803641c240c1d0700d400e04c0d00c540690300040503c1c0050083c407011200f8480010320141c16070b130035500c90078100716520b200d1000815000300384400300210b0701e2140f042144140b00b00a04a101c40c0c1e400716140750001d000c1c540001d5150844541181072020040a000005007620381040d400f82d80401d000180301c100300d20f44a544489080034092102c10704c00b219412a000d601115002e03242400301c4030300303403040080458185402034440142c454417002d0083c8540e00c1291004d200d40d50000c2c00007080f001711040e081d400c02d0103d032043c24000341060780510503003903080101020355095250034195a10031401c843d44440d030f10180c841d00194820241e000740907201c919030f40c800c00181c1341c01c5681040307a0f0104408003400e01103003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 603564766 1250 603563516 603563561
    0x4050a050f010f0806030118050307020a06050c0309190e010608090c010e0609040b01020111160b0603070503031b150c070b06300309030303040309050922061802090a 73
    0x1000012801c0d506016120002000300210080c0c0300e6540080c82035601d55a1156040c0e6000000408400410f00803002192200c0151041c82800c110036000381081c014140168401244000111014440d0a0b00c42da9403030090012001d800030303120f4104141c3c201e240000800c0c49036100c03c0c510b205003989011500400d20640040d2541e07004070368401d801400401427242503041075003040c500701c00184000202c800c90542e0220079a0454400303e0243c00c00c40004405100c070700740c659134000c0c000304d0103010100d2400c00025602e129900200c141441c9110013820321070804d000514064942000946c424904403130681102e900c4a2002c4981c41d04000c0403c0403414403800d200819541030b1240c509191460321581f200d10120100d42d0f030f492000700800c0c1002e460600285003c1c503c240c655070903283c1458104070090400610b80c0c40c00e060690071034500b21101100040c21650000c20001d200920040c0004404440c0c81020303401c0380d140030500807070502e50f030b000000701c2d110109a0040e05 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 603566016 1250 603564766 603564769
    0x60d0f022502090429090615030f0712081902070528030605090708120301060f0f02150601111507020709060311040f0b10020609070914070c0c0f0b04050a05 69
    0x262981c60301a411903034a40c00200003910030494030240c10091044000c0c2c040c81c0e0000b8030019001103c01c44415000b02043c881140501c06a9124079131049000e40030b48095103c015607515101c1c0b10707003c54001094000004c1c00800402c45402e0f0b0341901d141c92214050320006540c0361160b20900e4001e00b91803403100c0c0020648294515108445134003105102d2858039084050180a4052141da0080f0180050124003c00c40c91000480a80029841b51b1500e040509030420f41320695081c090002c645550b0b241e0b000c21888003454503e01d800101b519400012114200d800ea00d88000d0310903410365803421030342607003824070400c1d4079401c507103150752682ca078642595801d100050000c03940503002210340c90243c000501d05e5500d110001281c40d10000024040841d181965000d81c1120040c00060364091142d03d000d000c0c0e450b002e00c80110358080360504038400034112401c02101c10000403c000300d449006004200c18400181400e848055040080c1e01c0341c89000d200380800140042e05 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 603567266 1250 603566016 603566077
    0x1506160812041b060509031e120a0309060608071203050c070e0a0e061f1202040f05011211030109020a050415240806030f121b0d030903030506030109021e060d0f02 72
    0x2d0071025018000000c4442840483c41118482c140c05500271060b025030303d0300a80d17000c3c000380d0016680c040b40701511400c00d0001c4030700d41d07041101c03e600681d005100d07202d03200ca441c5103a2581480c1840e9600b1003030001a040941c0c0b80c00079400403d4a00612040340025081a101540c02c2d1054a006840c0c0390340b148950320035110041c00c8240ca40508004040303c0b000c0007020503002400c081880100207000f44202c034426002101d485420040480c1440068007914042d5070050340208058401a0001203c2201030320a8511440e1076031000c82d0320341c040c5440040280014041038072504070050400742c044100d2151703d000180070100186203450700185940341140c2d000041d101403650032600e20610390041c11990007140369410b210081507001c004038501c0c07540c00e0b0340010b0801002e150090560b10050041c034840d80c1062405000750f03071a03003a10000310701c00820760be440c402d010010881d207000314580818100e00d030401801d41c405140d0000d1004160351010301c1044020301034040c95 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 603568516 1250 603567266 603567277
    0xb0109060f0c1103030307090608010801020f0702060901210204090e0a1211071d0406050c032514031e0108071406031509100303081506160812041b0605 67
    0x380007801c0086194000d56018040e103000744000b00c0070080d4940400e2850b407040d80d210000841c1110700b0020039920401f502d014050310380080d468807125004115203800b4800c0040d02c6400700282014550b80105140307410250005000c8488800b0307018008004c0d0000c0c0b1800c0380560400070302070307910407001c0b4403442c0542c1e000000c0c026040800d001116245c5421440d902c2500c070785600442c40b40a00b640708906c07401a400e4040003841d09140c41c43c25a100507160040e4154103100380203a1207910203075290002c43c4080c081c04040400a42141d030594007200100c1e045000200f4090800c1c1e56454514001000114854490740c1c1c414030a544e81401c3d100d100100540112441058a000070046420004941c650b50589100100142c803d041c15140241088903140080040540200e035507a44a9040d409003c6030411801c041000c80c4140310282d400340403070290789010804450140d5100440003000300280e86020303d010b207010300205011941503c0605030008403039100d20116003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 603569766 1250 603568516 603568529
    0x50406061406210a15080d121a010f1202070c03051c080106210507050c0c1504140d0f0b091b0a12060e030c0c01030f020705150a0b180601030b0109 65
    0x100d0303a500300c3c0c0500c054044c007440c88507922140f0191003d06280c0190024050030b0018040d1107101c0326018004480c0c0881c003620f01030400b0026883c01c050044860482c0a080c200204c1070010050200e8801044c00c0d840158280b000c00c45106103c041006031043d03030310500440f41d655200506030b209064401d003150300040c01c01f10052254500c00e01900c0300300c0c2d031598101807500b100c2c07195560a9a804a0380038000540201c1d50891040c410421010028003e1b262103803510340420305000c0340d10560040300c0c0300c640304219070107507603d40010b8440c03141e40102480004030594034003040e138140107441c00c850603c030700340c0e000006546408800d60815002007140c2d0f4402e217480201c204100e940300c4203450390740c0c1d01c00140e00101c0c1c0500090a1a9500300041c0240c0040b110015048642c0c0d03d48007400300b813060042a000034070000d0100310004c5290200340d503076611600a180904001d081c05078121621200300005440f60024040c055142600c0501c2118001e400445030b8000368403508 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 603571016 1250 603569766 603569797
    0x1020f190f030306031a0f070f05030a180c0b0301050a091104030f0204020c0f070501020708030415051b01060b0405090609040201090b03060102070f0b070201020f060c0702100504050301050406061406 88
    0x10340001d280c18100c05000740c86410003152203a9640c4403946404002000d640364450210100004149007580306a0702c204030b41042c0b010443c1e40070000b49036000041c0764503007140c1d0720b503107a01044603003c035418086035101c2da241030740320745482603090984c00c2842040e0003180d80d241d000c07940c448135002c1c82010f03208141955007810300e0358a505803603035400e420a0ba0043c0c1d00704101008544140589090000b00b00000c14107649041e000910b050300591041403150401d00c4180170010070541d01120384482484c165866440c0c2c4403020002058040e05034807950f203011000030f041d90420010b4000c40e07400301c070350403440e0351403c0610600d44421900280051810a4280110001d031b00107036801c44810320482d00300c1d0f5264038520a030b001c90381d0420340e41100c022581104640c2d0400070341801c81d10142c0540322500341441c4540c2c8074058280c0c024480c00e80040f040701d115100707030b00b5100107100080c024821070030b081c10260010040c5005500b001c80c0c00000c5595241400c100702c410145006420307 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 603572266 1250 603571016 603571063
    0x106060c0519081c06050a270c050f07110f010f020a02010f0504050a0305031e07030207140d0b0708090c331918060e060306010f110609030901020f 65
    0x30810030403003140c0211183d0005000d803848142c41c01d4161080c2c40318050700080d007a07041c00d00300542d18001c0e500c01c035001101942d02c12804040d50b00c3c0c0a0280c044404081081c0ca40c90905880c036000303900026903001c80100303401d82440310a1981c0312010000f43d40c00f044003080030300119004000001800c002d42d100150030f80c01544a008008103008003454494105a1264005492001682e10503240c540c00490700c078004446003030750783c0c5c411300c0c03c1c01202c0d20f030600c43d83d006900d641c0700c3d2041140e0104161074001841d00e0b02c3d500299a10ba1103000b03802c645c58056000703483c1641c15503a02c541c500c94106900d40905061040390117040c0d5811121051506001020401d0207142e0180150000244440d070840f486e0740c0a81e8180e041c20781c070f52642080c480000b141d210754280d4050f404000204030310b0300254844000312900a1020301e0048c5039484011402d68020b40c0da048868254407031310717003089860034002c0050420000c00f44d003601d140b04001e01d4140e80d0740d100b150741d840d11907915458 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 603573516 1250 603572266 603572293
    0x30103080c0a150605041802090f090102160308180d0e0f030a06090303060303120c0e060d09120e10031a120f03040902040e0a091101110a0b0103050a050106060c05 72
    0x2401c420301c880c1d0102c50300180d140e5105a40391101c64241d80041d62200f0040c0614034103070081501c191455864000b2814194000895090000e4031056500100300082510003200f901140c4210350740c43c071005100ba001d868000c1c54128100c3c6c20708050340100d2007801d1000341c08100401200a580e8036000c50202040c01c01c0300c5001c4107000668184916207085002421394010f40401030b009840000d502441c6040c00380003401031074007041d01140780c0807800d205283c100380c2100076448103507a903640f60703104611b9000040802100285c6004004a00700200d503a224040005890007a10b203074421030b190400c107a0a403403880845000d00b18a00b0780c01c02c100d00300042d00303a810303400c04011901010000d0710254110f901c0341c1c12000d502900060180112110000c8041e0400d801030010081080b01c0e444607094000340b505030314100000440075202c000d800300102800107802034030384101540d60b8504181c2c2e44007002002c03205175003070400000e40c0c103000e14081707500160008050300b0703030b40103915 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 603574766 1250 603573516 603573533
    0xa1a0a0b0904051c17160f050c0318060903030c0f0d050c070e040203030f030106030b180c07030c2306060301230a0c14030702010e0c040218040f1b02100509070605030103 75
    0x1504c0420403101075207414070802c03012821805540c991180d82c5040280c603400401701003040002c1d60500030200080035060b5800002c0b200313850701c0b80720060544840703500060250302c142c8594940c14031001c644844181c1700031802d9a09a9582030840d495450b404605403018020a0000c0006c1d401440c001c00214440d418a181d000f8801030540c3c0c41c003d20401d20b80801c3d002a080180060b68514075040389080402225650b4002001da80c0650324260408a0b0740d4070490301d0040801404046030320400039100c080c005040a00d1900700034503480300100c1035a401003250343c1446907090203101411051a56800401201c5003004104a0740d96460072001810103020400c04020350544005c444080c1c0d400694003841c0c840c0d00109030390200030b42681c81c00c41c4181d26031b0b21880c410882c0c9124800340580c0e50000700d10940f070116104400d02c00c0c0c10000c01942c01c2c01410340b1021105405c140d9030202c0c0241903c00d81c4402004142c0300c04034201c3c6d6410450158501046d000c00040c008901e504 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 603576016 1250 603574766 603574813
    0xe0108190218010303080f070203030f150a05030102040612060504020309030406110c0d030e190501050315010e090c0316050403050a0206162a05041b0c050a1a0a0b090405 75
    0xd418641c0d01c0704015059140341c5000da200b500001c52035020701141c6685480031f150000c110380700442c01c5003451000401d401d0805822080d5000399640c28460ba902c524802d00000e01004008649842c6c1d9010054140e8089200780080c551038440041181e180c20f1007964001c240007401541414244002a00c21203094494000c80f4441c03003110107860740e6050f03440084075100e40c2d0307011282039841c0d00344a420b5022200014155003401014005a40d100003542d034061041c00d109141c05180500680d141010300c448030350001c15180410001e000303000001c2d40502c0c08603820500000a48102302e9a41c0900c1c003009160390000d0b1840000361810320003400c4106a041030341d9120408035a60001c0014941c0740c0387c6541000004811003802022444000500b82520b0601442c091002d1000c02128803100600610007028003020502c4001c000560303980e90300003503a007070340d51034512400c40b516012540480000e041c8014483c1e0350405900c254013a84d4000024038801002c44250503140141c1d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 603577266 1250 603576016 603576019
    0x110f1c091a0a050f07060c030c030c0302161106130b0912060f070503040c0b03150a0f0e1b0c0307200f130515030a060f050601091505030603010b060a02030904060e01081902 76
    0x14000980406c0141c407841c40c003104591000541c0450480d4085c06481140c0c01e40c0060510512215414260014030307180c0846d80404840d502d0054400013400038064150b0903005007030090030110b40302c00d081000b0003208608407402c5540c0044901000d58a40049440c09444a0024049800240140040c54029224081c80010319450343c9020b101078104070703001240341100900d8038003282000001d05010305a00c9100071116030514040c11910761000c2c00c4c0950355450b41a09026600912040d15070590f400c0013036907a00c24850500300c0304690210801c01a000c1c1c115103c20307403403070141020096408058420f40c03c984100c05010000c00004040f15030104100c940c03640315580038017034409214030902c0001811500c0d00307000d1048440040032141070040c400c0090203103048460700560611041c2c509640d40703690301c1001c07a003d8804210032036001400820090315035a004009004500b20650701080101d03920252242000004c1c46840459048400c5a24131001c014410500c00f500 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 603578516 1250 603577266 603577297
    0x504060609090501020d0e0c220603050a0f030201050106081006050c150a0614060705120a020f0a0f0308161209110a120b15030706110f1c091a0a05 65
    0x35600301d00016580340ca14101c5a6940c00135008250300b00c03910034045035011007030040c120b210300e42c0c02081340e0b60b036880754401420800c00c10401410580790080c0e0065a4000203503421542d45240881d0800c0d29081d045015508000001c01d4691040c242c181c03190a03080030040710300d0303d40001610130341c2c4201c1d1101094080c40c0480869040c1d1842040c3c080c403044000042c0240c50000d810b0050b090207401c9034400c83c07040110401080000230700500410f040003500d075a5000440c0c040e854190b210211001c140514040c000501042c11030b000c0125001c2c3d224074034681c0e5408100301e0a0b10304800380b0340119a4024607080c0c5468503500103940e540c07184c1d5002044140c81d100285400da0240c0c0200c0154030700c40314610400200c10700d0303280c1000c00621603242131646400001d444034031030b000d940100400890902d2003e0010000d450040d40400c00744e419943c0c00a082c60003450307540440c640030440c0c0840000d00108503c681c451650b005c0000282409040300e07044a2652040001c800b8125 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 603579766 1250 603578516 603578519
    0xc08070302030c15160903050703021c0b01030f210c060f020d0204081b03030a0905150708190e010e01050f03090a1b140f060a03111b160801060305070905040606 71
    0x81d01000004030784d80c500440072049160018880303034191041d80c505010081c607402c003000001e000003000b5040e21741c1281c0440000c0840301d81c02e069410700060241c00700b081ca80000062225030f030b100c0c00c00e03a4003604140354045a12000a00c23a0460380d11801c000030039140c038201c04500564007040307500c0c0108001519240103103218000340e811a4000c2c00d03141c0c01c1034401c03035060010002145402101076002d142407103405900609007480303522800c0e0107103030044c0d883c250038190384c000c1f2a40d041d4003940e90390321511130260241148000004040104100e03480c0c1010940c09810010700d58201603480700d1810315500003041c40e0b07410284c03402c2590f00c03070300d006e00300024040c0c0740c0c2c405202103040070100558a00010020034001c12401c19002d2544503c5031142078403450101c90015030780741004204042516500c009a2060320b082c0320900003000018003a00c000031135034861b032110441080841c0e03600c0311003407400c80b56544002400c603070104804200400b400e4202c560b219026110009880c4e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 603581016 1250 603579766 603579787
    0x50612160201020c12042c0a0b03032a0c120c0d0f050d0f030c081005090405070b1804061a070209070c05060a06060f09150e060f0408060402030d050a0c0807030203 72
    0x211703080d0514111040104062114002200101503c900c60320340781d40e20340020100450386680c1c00f030302c0040380a441d00c0072700b03410744c81c01c00803580708429140c1e08620041c01041e99544a00c80920404000c2c091411101810701d8610072910034680541e024011400c500020000780d00340020088510141b82e4041c117010440500075921200c40c20740b100c016240c2010001021104100c000000f401040d04c1401440e0f405620130000b80c90064400419644540c10000c0c5010004d50282122140004130b040600002d6038502d451900b0030390381882425190000758070381c20705141c3c00018048052100f80054588031600030b4100c1c3d05070520072402c00030b82d00d03200d0810350100c620700a140d403a0f1404002c103c0d40031642d11000c0c8520328080703403454280010200607240340038400d01017203084020511150360700d008440300014412280c0fa512a902c18005440d610b00b15010385c400d0140c001070030f603d60300804c115441c9402c6a918202c000029a40d0a01541c010403425021407006000c40000c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 603582266 1250 603581016 603581023
    0x4150e0a03171b150915040b07140d0504030e1c0f17040b0a05040f17060a020306060913060521060613090218010807090c02030405040c030e0715030501050612160201020c 75
    0x116044a04c44040a10f465a01945041c2d5a514070100a201150400c40407d440040290b00700e4a2450000f600c1c0004a00b4101c0c507018a40000305000d107803605000c2059040341c19100306000650721001501d402c000000f080000c18a005041c46252121480000e2500503214514540c0003125a0500b41c507190110016085a105c1c0c0740802d1001400340240600044e49000030f000c460ae6460342c15400c4d16009484450290840300d00d55008804110304d5521841070300c00620001d45a0411052200010b1f009000d0781c1c4502402051043c0c180e5022481e1400300f104071041e100d0052809840c0d45080c403080d0034410340100300c10703992061000e005a98101003012a01c10340003914000d0b5040810301c0b070030302c0a1079000a07121482e01d03101201e015000b1003550202d6a00700c0c0c0014202000843c00c3e4041e0030808040740e19406003c00200c2c1061125000200503002039800300102d03a00c5030148041841000340b04501006254005000c02c0c1440501070300c0340c15107200141c00c011060000c3c524 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 603583516 1250 603582266 603582283
    0x1060b03040c0503010b090112031d0d0c23030d2a0602190e0f0d1a0c030a2426030a050406180e040206030709030804150e0a03171b 58
    0x594007040d4100300f10510342401100034090003141c180040c0c1d45042e20390f01e171030008100300030103100b01036406540c900048020303036444000161090030fa10245241c03403000300542e030241031b03c0401d000100f07855a201c03164a001e03030001c015005181502d1050320a9401c5103008960f81810780000010261141d1036588441c0c8031485900d02503182c0c25070310320b200d140d1007030000500200100421700b40c4840d07035114001e00c9605000e44204034404078608110041080f480442a04c0000340e400f80080c624100c0010751291341d000c0c0003001001c004401c2c18044400c005225040191140000e100c1360140c0014840b000803410700160a10981c0c040060071600304035800d00100c2d802007000c101d819080040d01844105612072210030b80c0c200402e40c501d040300a40081d024400100001d00c1190207401680017450704640b03108d4030380b5910a00c4d60b40340030020078000c2c0001c01c035110fa204542003400c0c0711800d1b640d1101c9944282407a10034401c0154001c00c0c19800f404d04420350b076120f4047d05000c0d4a5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 603584766 1250 603583516 603583523
    0x313050609010c2001061806170d080a090f060203090a0b01120b0c0307020a12030c091d07050f12010807210b0615160510060b04030507060503060103090b090a1209050d08090301060b0304 82
    0x9401449d05003140448a07540c010140c03642c01010311301d0f4095520081c49a03000086000000d00300f0020f0909040510484100a2004c7d00c00400d00c203811a00203051915184945c1442a05a803505000d0028052000006107800e547c1e10224007044e0407440956802000c40c03040b10041d52a60320f0340b140441c039400c095004641da0700803080c042c55104060101070a40d4800c10030605103810140b03050064002c144104001c1c1c081241907030060060112000000d40d06c1ca64140755844140352502c0c1c11651180282d10f46145032105503a07443d140580401d1504500b10500940c3d80b10705004503201d900d200c07152980e10800c404012036109a0140d50114010700c014280d038403180c4812070440b84e541c0c0000343e081000b4042040010b0340015101d0591301030f03140583c0c0b00d072240030059018041400340100b80306180410011403940c001081ca075110b0048101d21b02141064509403801c00c000d0290703d42100000020b03402180c41c503c0117201e0240e002c2d00000c1d90b25529901c49400d5001039404a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 603586016 1250 603584766 603584771
    0x613021308070b18060a0f03020a14120415090305070206070c0515030a0c08040302030304031d10030e010e19170f041503050c130b0f040f06021c1b03030504170313050609010c20010618 81
    0xc023b1103080035502c501ea44042000b0810b0440545001e4158040c00c42e000380300f01000540181049007091141d4001c0c43c002e800d0400e44809540442034503001103076074a20f0140b42000700904035100d20050782c021070301600914555180e5880440307240380d0941d203007401030610300140c3e0001d03103400c2d000e20a40b110700e5400060300c0c030b0300c5560755081d90703038000f00701c20664404014901001004000303441459401811110300f8088108007842074010080361240700d10000c9800110341040301e01640c249982554204840c2ea282c007440890350283c0c60000000002d10354090181150100041c4045802d12400c541856035951010480007120b800804c0140c200e180002480300c00822030000d42c050500f0801c0d80d404201c4480c442e8541c140c00d0290030035031105e000c501482070451215100610300355641d66603140801440c0100d00341030008a03060302c81ca03400508011010320841003605142e90750302d920401110784a41a9141080b0604140e5589501c0000d601c5400c4100040c00c000c80e0350007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 603587266 1250 603586016 603586021
    0x120201090b01050901030203030307050a09031a190e06070c11030303071e0801081b01111b0a050904050312100f06080a0e0102030613021308070b18060a0f03020a1412 73
    0x10701c0500d0010b074002070040002000620050303a012055982c400b240d1300e0040e44801240004441005a50b8400f4052407070380d021282c0c0c240d030b0641e40c8520400c9003240040340e0401214001d0102e40448058444542015020801c198440c00009125030301904e000034144956600103419a40142c542c0c5001c9008000c00400c2100a0ba988034240c0c20141069400382d80b5003003806445020148102d0301031400300c0f0000456a0080104c00110302c03103082115613401c40e00b5200319001a200007810300c40d0003c0013000420f80780c042015840303198000d010714145001154020401c00006c1c2090f110309002d2100030542d41c0c4110003090041170180e82d43c00c001e0910350039100031201010350003262a401001040101d4a60400e0445d0344e4440010050303450b000d1905140610701c01d90454080c0d17001c0e40000140c1c80c3c400700090140880381480584034100c420341000000e1181603100804200d1001803c881c00d4081d6000d40420b04d0070381000f6840960280181c0070f135500c03c40000c0c0c44902c00000b0b = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 603588516 1250 603587266 603587273
    0x30309040f153311100606030e160b030a090206430b06130e030d060e04030207030f0f1202030c011b0512151f0318020d150912020109 59
    0x80b0b00180111480303107881c07a11034031218080c1d10060b08281003c0d1281c81c07498425512850344130312640c0c0f2901c180c403403030b5418244010280c0020b00c94040000d0a084400d01d00c80e0300442e940c9803000c00760300140f0301c240c504031301d911950304010030700200c1031b43d105400005038890703100910501d4403806114085080742a03e121005145010446030101d001406d10718070043e1041032030500b6040b0654a000365503003000102c171040c488030002c03201403d0100c21520727030b6000000b40c250b80d104440b040c0035080d2250324481c0080c100304c1b07002d00140e10800080002ca503510700717216440380c080c0300301c041c0c000e2098441030005080c2c001d40d180182e00002e40c4401c0202c0a200f840700000c40d0880120007030fa5071a4004000c3c0c001c2d8405001d800032004081100300c5a40c018046d006680504210841505203501e180c0742101c0d6811403021070f0071316034240d148800e400c15a413106075008000420780b18045e110070170168410110340300c810356100d070f2200c080b80d00060031400044640c1c0c00422171088914 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 603589766 1250 603588516 603588551
    0x20a030305070311030402010302031b0d0617121e0d150e06030706050409150518090f010b0904030f0e150c0f01020306130e1921050c0a030e030309040f 67
    0xb01240101443c0444003405403100004403034101350240390140e12520f81c4800c520b02c41111140307190b407100300041d945d45e0a0f2010781000c0704844150320b05190161141d0001902e4124105021034107000070000c0c1e004032406010f00090040c01c000310720f4140b84807040c1c0c0c0c41c1101d03821544038000c0c81240c1020440031104901700e075840710040d00a410710b5403070810003500034050b60245209154a81819024202c0c00c50b030660000c020007072000c08818410468420820401c2d2031100e40c901800e0b6045240400501071915a0f10010302a950b07035949a45080305c2c2881d40796840f60811241040310803280c1d80e03051710500b564940b1f99070031340c0c1c0700001c40080d803a0500640034400e559005204101d100e903103001c0d25441040c2c0b681404510249040d03080c3d0b05000d01249200201814800d500341801814000300c8184070442c02c1000444051200c182c515008107440c281980e4030011a800010b40314815554a508003d4101c07402c20400030005802e803441c49541d054019905e1990080342c0c020523 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 603591016 1250 603589766 603589771
    0x1b0c0f0906080c150d090b0f011e03050c060d090b090c030d0e010203040e0406060f15031404111909060b0d06050d0201081605070611071a012909040606020a030305 72
    0x120b000380000390840000c540160400048407a0355100030400780e040c0d010607008206410340c000309005061502e100050704280c42070242c4500ea0640000d42030a0b5520f1008080549401400810005440310101301050784608071004001e41c468188000050720012140d01400c003c90150465260030001e25151074181204001008a0180c80e0800e80e6004012a0700745c506450140e01d13690303070310700f492400b80038a94042002c901c091400000c080302428110604034507540e4041c000e06620309101401004156000f501013420090707000104d02d0024050000260000349007815240d81e4040301d03040380c059600048541d1030001c0c800640c0c103024492040a008202c81c1000c080c1c4450300000c0c002e000041a45818007600b0304500d500c1030245050324032195107e901070002c3ca544c4483d07010503402034801103400702200c21008032180c1003040702174169550f006005010150350380c000310b000041040184280c06040001800607102c034007840c800b400742500200f0815a180c40c0060449100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 603592266 1250 603591016 603591029
    0xa0807020d23070f020604180b150909150a0f03030207170705011b08070f060e0106060e040c033c0606090306050601050d0905010501210809011b0c0f0906 68
    0x80e10340340740211050b690081030000340315440764888003145080d02129008841c040d51001c40403e00142d0b501010180e05c6071198044c6003484941101000e00800400d04003070384088030410300c1000214188500040d900c50183e40b990440143e41c1d1010808001c0150005c0d081403850960600034140c04008801c0200300030021101030900c0c0d85180d07078441400b1300a490420118042914119141012403603905410001d81a130301c03c0c00d0714011a0200030640101c50040c00c149140c24190810302c5050111134403034407010541200c6408010003820281e0580051542d608c0d1403200f80300804001c013608860f0301c042102d8020310328004000d0008200d400d00000b5050070002d10589a00500d00c80481c3e5008001180d540c03603550060f14180525011203003400e00c2e11501c14140081508400e0403138441405200750050f5051101c658090f113814098000401000f0300000c95200d1540800031211a500008000c01140e03611992003006900180341d404001400b80411860340c4109401043c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 603593516 1250 603592266 603592277
    0xd05060123030606100908030f030105120a021e030a210806030d050d0213051201150902042d0e1006030b060301081f0b0a030f11181306020f0a0807020d 67
    0x308079000076a1908010034807070003420b0300c0030145100381c06120604060824542500d81301c0e0741800001c016a08244a0726206041026542c2110403021801101d1580c0180a0200d0100f587c525400000800d8201a80620548030b25401003603172030804464bd02e804818400c141d05152200414082002c1c1a0500c82d40103084142c1810b5040402c440c1722140c80d010141c0c483c01510001030b8040c506a100c1901318030700c600c88148403141984902041c0c101c030780520b11201d890304a610203e010b5409421245114403101084001c00e4012488000305003e194031441c0c1c1c4c44002c40749180d00705840c0704d90154145882809029014041d6038230b0100c0c00e403100780c19589072041c2a1b0f80c3d04500ca01805400516850860003181c03a80c205081040001d0309500300030f41d6a10701126402003114003550807011611006055181c0300841d5144000d00051110241e2110084001003d1032560100d803003031381c02c200842444004c94003030f201300b06160321038840c40e24000c0c0303000e030070294084210001c010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 603594766 1250 603593516 603593579
    0x4110711060301260106091b081501020a14070306060303050c0d080f060d0201090503030a0c06050109050403090b0a020312180f060606041401020f0307062a05030f04030507020d050601 81
    0x11303403041d03001c10301d08252808640c00603035607407107240103001c6900002c4450303080400400890041d01c2c10000d4410807983c8003010340e500c201c82c442c03006104252440c01a0403da100c0c1d80802d1070400119194840c82040c2c0f144c20340d0300d545030021a10160720480200e40041500c0e5400041445100030200903410030010b14a8008180d5108100c000c080a20a040c010840f4056900c00e80c480005802c001e4212503465660040c05001c3d809210001c07030b866810500042040c10540c02000e0080394180c0310343c01c0041c1085c44100c22500704810380c00451100740804403000c00c50301201c0c1d0003106d411b0070b140c40c42110304008070f09210100b81303442c14650121061041a0f11001c08a404071104c440c00180107082c0400107d04000c9192607813100c07803102140000612109a21840502c920541c540c81522134245002003400d62540f9103002103041440041e051074203094081e0b90041c4249491780ca00040b941c0000d00c9500c0195013517500e0340c01030005121a204440c5107042c4504842d101d1603008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 603596016 1250 603594766 603594779
    0x80105090703020d020712020f0f010e070b03091f0b1302070f0b09030d05090c19030c26030a0206100f0506070f030e030a1b0911030f070e04110711060301 68
    0x4050150001c010964006050921031600768141c8041c2a40409007a51040c50080c00968482110148904500545500074540d503014483c4900c80c3c1414000350082c10f2030903000100c030350001400354000b40905146030b00020315500f1004603142d800d240006004a1030400d00544040200740481c2c82481040588040f405804000030a1a4441d1001c2040d58596014600311b00422020f0300400c1e00b40800d0143c50301c000718003d09a14810390310141942c0580c0030740041400d2520018013003001104080c0580302c09070010041c6000003c01110081c01c0002c10303d459a4010000600160040424005041c400300803040c0140b1a041640e40301030308250010750a440364000003403114000039200c00070540640260400f4440040542c0c2400301503082000d0300910090780402010898036000c513801710503200d104001800c0b0300030b01d4210b60300c18440c1004141d01810600501140d44151031841d5140e002300324041030701014250300c422441ca03010200c00414001d040c85403100780b0050000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 603597122 1106 603596016 603596029
    0x402191e0201090206120403171303080f07050d05040f1b03030e01020105040c060309020f040609020a1b0b04120905030607030902010e0f1507022d01020d080105 71
    0x800400e201242242e10400b00258000c0b41880366407160790f0178400003640648681006140c0700c40c0c0c00c000a1a1500842d0104540d6903502c00b03c1c01015030041c0308a400845038001c6030310b603080603000035000f030254040c002f20301941d4800041c00d0040d5100280102d98002e0400f210301c02c2d903a041c203078441595010540100348040703e002c0982d4414400c0f41d215a400042e551302d103070308142d0f04034058070441e00241d1380183d42c400d1038002503486d41703d0301d8018003070540c0040e522210100c0260016500007500e110003600d01134010040354410904aa0165010312240d0150800220988201c2d090342c11498151046608108215405920488116000340c03103213407000c5421401c20107461494030105400c8450450070302c00303442003180036204643c4014400c100038400f0b06000c9a02d5188400c5081c0e44200d2001e115000d075805008440c205806450003542a60506021440d17 = true := by decide +kernel

theorem cover : BRFrame.Cov 603417266 603597122 := by
  have h0 := BRFrame.cov_init 603417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 603417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 603417266 ≤ n) (h2 : n < 603597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
