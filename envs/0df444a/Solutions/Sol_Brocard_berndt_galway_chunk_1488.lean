-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1488
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:13:20.488742+00:00
-- url     : https://prove2.me/submissions/5e0e2ecf-c8dc-4714-a414-9a522fdf696a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 267446043 ≤ n < 267625899 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 267447293 1250 267446043 267446059
    0x60103050c041e0f0303051209010e0a151407230f0406032a03050f0106030902090604020a020f1911120d1407020402181c0b0f130b09030d05010b04050609 68
    0x810101d00ca0050701c00791406890b13120000740e40b410000d0450300300c041c80024102c03d00300880c40c044070500c034002810203c078002c0d140e030044585480643c40108001600d02c141c640c0910049a07690209407445400681c482154a02900b200700c000b1181d0008896000c100030840c1003c112080c4003542c044500c80c0c0303808204242c104114480c41c0408001c448503403602c00d070a1a0a00e03030035401040c410003615074007a500303aa07604811401d503403003590007a4005010102050050034036400a16200300c0c03500455007594400e6098900c0c0038078003100b60b16201c0ca00d82401c0204205d00c0c109020b800001c592002142c1c041e08100c03a01c5041e444035800500c41c81440040f00d101c07405080d00d0713480b50010811503e610081c59080c10b50b00201c83c0340c5105007840d0300c0c42218510349030308020901d601310040400729074964a40c903511044c0a0207803800d640f0030346450000684400c2500e881520110042e544480303c0282c400d09440b8180c115110384201070105104546a01040e1002c45404403035160b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 267448543 1250 267447293 267447329
    0xa0e04020604150507020f180a0e0c120f060a050403090902030712050c0a0305070801140d020319120801050f130b010c0203010e010b0312040f0512240f060103050c04 73
    0x15850b4031495000010302d041c00d488144801303801001070400039000780d441c02c05804902041004000c085440c0c0c4c0c584030034010205454040e50341c0014401402d034000c03180b404075a6000542100c2c1e00c1c220303ca44560048844201d251403e00c116500000849828003440c1440e0750040c047d107080b4003d6140481c0c0c088006002c0600c94030007650800c0c40b881d0108440d00b0101850b80540e80042e40c04008241004042103495109180444c101e0b17845000028401603a40100b10310704a9440069a2510410138815540440750040e4005203209654505000e01c800001521004050740103038800e030120381800b122516508082906403106050000e20000300c20010781c0d04408100b00a50950b00c1c1140160752004154082c1040344011411100e02c1e0f4804090380c140b40c8224007418100140043c0200090b08002ca039100c080c0c450b417015601291145144516a0f10595903080c81d100000414016031154030b103062500881c0078a4180100e00c0c11184009540c8030b188039076282082819501 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 267449793 1250 267448543 267448549
    0x90e43030305040b1624050f01050603011503020702031e100c1b03030e0a1b0b0301030203030708090604030b0906010302040606030905060411030a02041b14070b01060f030e010213090b040b0a0e0402 87
    0x5e40e8842d5001c101c1c45030170180300c0030050344113181101440283c0e14244c08128044059041c01c0c0c1240d60050146246a08007200c820100f1054100c03603041c560203212420041e6070a2018080e09040c9107000c1c0740009003a01180d240107000b29880700c08074540b0100c0050030381e010070000c1d00b0315156205540e5400303591404600034641d018421406014600c4030304100040909400b51240407003110f41c85c22503d981c0380c407196220a101c02541603004218000015100034090880602c004003500c0c281603a82d00c402001a41c210b4200c922600101e006008501d003d10030710010b84190b2904000e940c00503683c00303544905c0503002610514009c0303142101036600b0041b6582103980035005120f00401d01c4140d810340c6182e4502c1001003180303400b0300c00115500c00c007501d42c155088088032740d090340785c0001561868020702c0b000d030425854103901c00c0e00c6070003400100300d14000d48100c14115803a00b0001f90481da003170a1901d100b20b090058104840d0f03103081900c025507142d418092070750384440c400 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 267451043 1250 267449793 267449827
    0x501200301060804080d0c02060a05071812051516030c170411040209130501141215061306060c0320070506030a090b0127050709090e43030305040b 65
    0x140806c80c00c0c02c400b2440e050b80440e0321400381c07040102c18040c90320750320015545042000d07107400f83c0e00c50802d000c00002d10b201010b00d09007030084003a0390308030701c4007804118003d1003103034001208890400203a42c003581c14400d00345d022a0520b811031b0b840c0c2e09420141001540030308050154103a00c505071a469a480e81142c0e003c600081c1311161000c090540f04024110034410400c0c101c00b1082c8905840c240307180b15168a1441001801c40c1c200c407000d601904641c080e0800d5007050700041592800d42c514800c1002514094940c000444000c2c5070082280406640000e9054036802e4803a860403400240c620640d182102c1094a90395001508001031115035809013007088a0310001814510341400800d0b6946001070644002121801e2007068800a80d10000001ca00b0a410131008c0c1050340b0400d01400c508065440400502101c0340308201d45961140d01c50600d01440f125040e402c2140c024041d48888440401c10304c1c58801503e40c1c0601c3c40b807500b0041c800a1550254208200 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 267452293 1250 267451043 267451057
    0x9060e070e12030d06171b1903050703030507050f0c1c03170112021302070206030a0e031303030e0a0f03020d02010503060a0806010b03070809150612120313050120030106080408 78
    0x80700c0d2a480707200701d0403010304221b05c103038a007041140c8401103403420089268080c04140f20720380b0341100122418421444500386080303200f290b10b03e00110004009100a100460290340d69039111001401e125007030003c0311081844030342c0705980c0041346440d0b1199050006480400f07039580c2020794102690242c0d01100b150401411000c004665072a8810483c11014020f0f40c01c003210355401001141244031703420703010398000301c00c0c00014081941c980018004906c10020f903030500900c0030358140c000805030812808144a07500000180c10200c00400c01814542840420300d4a107401040c484110701c00041e0400030000001030312510788088903402031008104035403042d030f9034401603160340c0c0040e035019000800c5840403036403040c1c0004a1580c1c4c9130390305c188880c0c3d81d240e14003040b0212a14000031300180c0120340c03001c007025101e003005e0351190140780c0c501c40e00c10380c403850b0450840e0500741c40c41c1400c80d5001c00d0018840d518200313481c15111641805070854480b4240601c0502444c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 267453543 1250 267452293 267452329
    0x3270d080702030903070b0c07060f090e07030b03060a4b06080f0a060f0905150a0e1e06010603050f07050906090604030f03030e06360601080a0c09060e070e 69
    0x4001410b47c2da1000113044018034003090f28009030b02c8240c116940d582c1846d030740c4006040704c0d005000200101101c9a002075141c00d00258840300000440e003000011a01002125542c0d140b6440d103648000a0305280805481c11580404a00f400c10030032000000001000500120341c86803548110343c804009403c2c18811102e8180c000c48201e40d441d413098104030380190524801405001c043d028030003200381d100003c0c106107080c1070300e0049550341c020206840640c86840d820103105040c000e148000c04070707406e03c41d1030810705205130349444d506170701100c105450f01c1d04001c25801080401500070181c9c0ca4141c3e590030ba24400030345940103000e01e80354403a50001c3c0000402c10580d20510045c0e01c6600d0038804955201c0d80725440c0c400466082e122f040403901601f80008c480006e001c5800c20301520300c0d800b00c01000e403a510703260098000780e00a510081860b4103204044201030000c06000c401448820704190640030300110140060060224140700d00405541d80340100806034411 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 267454793 1250 267453543 267453553
    0x6030d0c141507020f011505010c03030b060d0b0102010524010f020a0c090f0b04090c05010509060409020a0e15040f0302060d0905100c0e01030e0601141201090302010203270d080702030903 83
    0x2114402e000380000c0d104040940300d5450620055481030141320140801d00c4442407401d03103440c00548014803051030031010141daa188801196a5000144c41781e0807000200044440e03401c000a800c40704007030170f80840c504801020340341950600c900c0014000d000e1070120684144c101042c0d2600c11035140003800c1c803502080c04203008980d540000d0f0300020b4041700b0721160795030b801400204d074038100d4041c01603002e520f130520980d40900c0042102071005814949425a62096807040703800c00310100d00051089080401c103880c20003011105070842e151014a081c0c0f910509601c0f582c810b10000340520b10100750218180700e0b9031302040805407c003042e0788041c0039025038070006040040b042c00114400c004404040d510a1140311000080c0c0001465540d0926100c4004140e102c034005501c8025034031002145a0300f03000343c080040c406d4001585034105442c415600740718040004905164100e40ca9403540c60008902100d1003180c2440803c070b49420340104e04600c1040d05083c1c151081c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 267456043 1250 267454793 267454813
    0xe060c1b15130c0e0a150605090d170f0d0504171201141c140d05041a0903010204051c02011d0303120a1512050717031e0d0c1e020606030d0c14 63
    0x140c1c0082d01840061841b104000362180c400340d54500401842c90b030040715200529000401025501c3e20b6171000b995494104081b03400c032100207900681048000c03d4031501401308000c00810303203000e601e01d8060080c1c200110290303c0b04030308405100301032001140315041d05494940c1942c412001450b00c0381e40d109192141401c100352038402d4010003141c0f003180b02c0895054403c03015201960340071250007800803048541b00149410802c400c0e03603d55400c0000040a45d94107000245d0b03540da40c05100d982000d0760002410682c800d040b0b08840c2032032001c41560070354000c000c44804000c095100107882d102c507080c0f80001d05a42c198078500041240c00860702c41c41142c9041c0503103100e8030480d90000e0300c0d0444024414002c280c490101d902c14448101114240000c4500c180044081c0300c0c1403801c50300070f8005841d400a50040460a000c818541e520340044180e030310880301c0c1c00184070a00304800829520307124801002c04221580c840c001c200540000b80001e031305002c200b10780c10056 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 267457293 1250 267456043 267456061
    0xc030c150515030c0405060a0509040510022107030b010c0f150c0509040b030d080402270a051e010303020d030207051204062106080d050d0e060c1b15130c0e 69
    0x31008001442071013401304110f410b18240c0a0184251000f41200d11800c0c588001c1c0a80f012018000b200c0340c0c0995500407080ca003035417001e032440020007229061003030a103d10080380007202414450806041102000a40e600a00504502030380990740f260b0001c0c3c0c0381080b50844c1418441080220b01b0010102d00c40c0794820007030314092004803010801a42150100750392004501c0f80d00c0040f8008800003005480d10160000440500301c03e02c0c885c800c0740103034000818038111440c0e00440e0f52a02400702c183e121480b000c00c00581d1854a208550440e11701a590365a00030041c82010380004101003000010310014040c04217000159444503211080601b800d4a8203032031000030083d10440215501c10307400340304d007101c8112024003500341001d2011241540495038044241e07482d454152072880082100d90311402c030715148552140308040b40c40035540484000e800080d0700500000500380b01d1201d1a0f60061001d45030740c45640801d107050b44043d80c9a40c8010316842001e0708001d1024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 267458543 1250 267457293 267457321
    0x133002060114010e130b0102100c03060609090507090506090f06041418191d0f060103060c090506040920032a1804330f0e070c030c1505 60
    0x2039004414282a02d1607000442d0a8240e11540300e40c4100c0d29041038400703190a5210704180c04062043d075009500b042c400200340d07040c036800d80002a0317030740400b0000140d021260700d016083c407141c00d01c00c138101900014012115809820320407140081c1844565459115110749550b01400d4540c8956484c4400e071000f80c1040340c3d550094448201107220444007c18980c8120a80e04684040c48030f40101d080090442c451280d020403400c00701107102a0081200c00b0200c2c0c95a40284820741c10f41c81d21000390744404400720f050182c0a48103114540d0b960007610243c90255000040314075145441c3e1395147d00b075103481c4400400c0001880391032600844000000c203400301c0202c602c00e94800d00341c1c95500c900090300350381e00b10304090f21156180035001a503107427140d401d11a9400003981164240d0003800c1022800f1a41020000c1040c00162200e403c0204600c040e0034103107160200010300640d44003800101000901091402003210b400440a100c02d1138480400040c40c09000790341e0b40d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 267459793 1250 267458543 267458549
    0x9070e0d05280201090902070c0306110309010b0306010510080a09080a0504141504030b04060b03010e011e05010e0f07021507030b090a0515060a09050303030406231330020601 77
    0x541c041e222001c20301d000b6680074954641e06950301c400883c50b1500f048000d4000c814100c0d4082c41d420800404101d450003004850851b540c504c550701d0424015083c21074012502640c005d40010004020a5807000ea1840440c501420054103030760f1101d1145004207549200104502008141c02034003030303484005041a01d503000c9200307640d00300009c104440c10716021044401e01c4820041400000d0700c03101110b8005114030b00201e0030a9180c0000b0342500c0e881c110300c0a1aa555503c2e241904002c51002c1c0c06100280740108255414903800103d0340200901c1175906076480303000b0a00f441d108100b264070000e01005603004600b03003a00020b000d0090710307001071301c41c13110a00880d0f10340301d040c42814003a250480070f40204100110074404207800c60440c1d10180300c42088001026203041c802180718611804000070f030008070350000c581c000c00c10b00b000e404142c0013601b003000705034046d1000e16100d904481150070001501490406940d40529001d00701c454400038141c0440d0001407060503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 267461043 1250 267459793 267459823
    0x1181406090a261308010f0623012a0803070921110d050604080304061404110630010305070b070203190c0308040e06090705030c070209070e0d05 64
    0x664071a14481c980d108129140504103000000f2042d84a07010108101e40d14210b07258090f003031040c00da5100c151806190302084150b511880081c031a008184507031009002e8001101284810083e112180214004909414040c0d070409160520b8402000038901d04510840e444441417541f42c43d500304d400030f842001c00b0a00250022940032600030304448040000020b00c01072030055241c040b202101c0d4160150001d041010b03403008500d081c401144502e020701d85041d62400c1c14544441110b8000b001095416401e40510001602c04c0000c40844441118840c0d20b40e9840c80113059400c0340c03030070087c034810400741c600303030602d8071400d03810303048034000c00540340e02c1d907911940c081d081d1154980082d072640004400d005054400c2800786c10072409144288010b5803a6a500c0d01944c0c010303001800180500d00c2001954a03000c60120b078840c0079450424110300300201d240b4401c3c01540402403003258001c0c000f0702482d12401042121101c01451649030300b4160802507190314150803d000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 267462293 1250 267461043 267461053
    0x20f03100305120c0d080709090606020105041e0302070e06060904020304122d140904060303110105010501020d0903021c1209030303140106021e1c03050f060d0b07050a02011814 78
    0x851a10160103403000712100c1800341443c03202080c5d04480c1c04000070300120902a818201080602c1c0c203108490162005400014003070511b0705000b2618203040c61201041601d10f103c0c403002a602207101390840d4109200c00c1e44945503840015518016041016040b03840841040188540c25001c0c040e400002d464003000d12868080c8101900004170801100603280c1d1000582584214012410300311041d018074104284007000900b91040c0e83d2050b00090201c0901c4504014284100350050109000400201c60781040c0035026400360303c03000c4e208074080c0c3c088003528032035901c14007145a4404030041c500b0400308400b03402244030b4002640064544502d8400421070104400c1c12b89071240c00502598418400b04003c1e1040d041ca070f14000c0c001d403502600c89800b01851001d81003103980340400e140c6007440f218140800001c1003a44510040b424100c007042c004505507810103081d1808554651040b80103902500409003800395000c000c030198001d00200a030f400c080884854140c44c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 267463543 1250 267462293 267462313
    0x50a17030f090703030509100302042c0702010b0102070302040b19090608010e030403020904060902010212130e061909050c131205070b0c060a0c20060a05180c060d020f03100305 78
    0xe40d984115004c0100441d50421192076545400c0b14000840280d07843c0251600c3d48940101481045500040404c40c2d0080da4141c044041c00005560003d20791008010f0780c41710f100000d556590302d20010340250b9554510040ca07807201c0c0020840b0844500d00c026a980c1c7e01c0600c0401403440e03204140e141e510741507000750880b00c003108450449400601907032042d12240c907804010082410124154852045004015601400a040c810310038190741c00903140381c45c06070344034800c00078005031103098840203614400740302010000a032048044000341c180e032045242e0700750b4880d1000401584540c071400013012120f0002007400e03140b0800c00e03502c00d03175a07412a900040c043c41d4184000c50f04400c002030800780ca154002d818840180c40d181148131205c03505009007011a540d03000c2560002c2c07041108040f52809031580003030304805000640b404514069032210b0000072524400c88000401043d00c55494054810b10800000b01d142d403802d0a50b4040f40440913848116140d0045840301 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 267464793 1250 267463543 267463561
    0x10908010c0c0b060303040e04080c07120302060403030504030207050301020412061406060f0a031407050c120a02031c111605010f0908030105090406090605091b0a1a0304050a17030f 80
    0x203140310010030344a403681c04182e40c0e203002124600412030364140c84240310006010603107415403400380c0e0081e50b80c0d80e07030b60048030011400c003140c80e00211111000c45000b0000294001138883e407158041c03030b0001355900e4904e0102d0905015511080e030540c00482c003c15982c010188048002c0d11401301000b017940194041e4140c018201c80d505d80c0800240140c5104001800041803080b40600d40001d00e05419048003085c01c80540761140080c4001c40d40c415511003c20041f940500401551820b081d88048000e581e0301c16465103e02c400303504414079070724071401e4000802421032a072407a034940c000c000d1081c03481c1d0a8504256040e6007003a41906844103948142c50ba2950031007552441c1d13a0a0409000f00004050300071154a035849115001080b450300c690380c000e030b200c100940464600110810501964100a140310704488070082044d104410a040e00300403a4201c0f55403680c1e01d03070624034244001014094096142d150200c001400344900031481101c1c1c1c0200c1010742e80700c0c1060 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 267466043 1250 267464793 267464801
    0x406081f14100302060c030715050a1805100f0605090717070804020a05040513021207051e0f0405180f03040612020a0e0103021c140105181005150706021801090801 72
    0x8009000b045150038400340c24002e00600143d00340f04100c0385458842d564040f00f05602c1102081e0480c0e5610510041c9400390003a902c441c41901e0142d00b04000540382d803901c031000c8844a0a03015580c110500343e49019410050080c48001e01000c000d142403540544121102c03969002404c040c10002556940100700f1540115009031100380c40342c0c01e0a00f40700c028040900141c142e01e07015410040103039641e40102c101000094040d1001515007070a00070500c0b002c00f4078240480803002404203548844100a146c400c0480d00841c4a4480e074810301e8280030481c1d0b034441d0360300a07440e6440c00d4900000041c0304aa0f00c40d80d40c049484000c149000803402035080000014084142c0c030b100ca58820780207840014255004490b810f18060520b40456000413035007040d50042e08010400b41c0f40075803d4000340e80000d07100c80781a280c00c0700810020b14050045070320445e521120140c0d5110301809440807107a2080301156034034822095a0728140c146410240001d86051021500c4038040c01 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 267467293 1250 267466043 267466051
    0x306090705060f0904020c071703040b03160e03100204030b0c0405032d0d080a05010603020903060106030e014215050c0c0a0b070c0506040e13020406081f14 69
    0x201400303903503007880c040107090380c84a180144486070a00598204d640c552006120000e9800e00030b0190031b103400700203505a04d4810300300c0100d0304240400c120500706901100d500c1800c0500341912210802015525120b035000d403150107100d075241010400c1c00d2580140181c038010740701d45115907203414a4801c3c4c1c0c4558001c0a805401102c4414100d1400d4603440d8a00507070851b000035101c00b60500c40cbe00c0c0500e080080c400007100c00c014000503601c10700c20b080c05407090f0301d0158503080342e10340442d03034940303062199108056030b80c040700c54506020f52050a040c0701c0c020400c00b0910b146026a0922085102640507168400c0c0ca242d6001a007080b1450448030300741e5400350300085901040d1241e42010a455205000d00034a0721407582d40c152458002e40602d100d002c0d107618044c00d0204609030300d60001801f5900400042c0842c59a06406c035030311601c0d001800c0805441032000c01c2c094003082d48404640d04c1500d030a407a1403540701c2c10040182902550030040d40400d6050404020000d071 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 267468543 1250 267467293 267467311
    0x1203040f062f04170703020a0315060e010f14030105040308011e1805012c0f220b0106110c15070309082505010302130504020d110c0a110306 62
    0x503a88009040c0da04040c03041078001110103448904008072407030500b00401d26100d14500007409202503050142e8026501c0c1811004000701070640c0d01042c0031800c0760002a00d4010f20741802200d184c0c0981041004e004803105d032481030750b96051000d0061140d0b0198079142150100b0b0301d1664281403082c684101c1c0c050303442101c0e43e481c1c04501c00c0c804110703075500c030f00c4482d02140100f0300350b445250280021720401c0001555625051820344045c1c0d440325082c00c0366032541112040808060103080c0c00030020300100c041e94039290001c1d0030206008100305184c00b240750040d07051201d811145812111591110301c2461841d011303440c0c8401092103807540c41514410320f5226417503420003500076940b00c0c0c107000e00c190740c03a5032810746040101095804140b1100e00c1d1140740c00c080e2a006c000800080c01c0a504110320850f0301f21080c103c90181e24069940440e250b0340403142604079008050860391424dea51740b1025040352188442041601c01d07011120b03c0724207a05002407110320940303040d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 267469793 1250 267468543 267468563
    0x7060606080a140f100806040b0a0606050a0c030f0504091503061a03120315031603020f0d030f0c03260103020405090303060a0e0603240901060603020406090317070b0f09120304 78
    0x20300c0714403021130001c0c01e4540f0410400c200441c9410003008128001d0340201d9404200d450b0044140041d2415030b080f5404104091007032519054100e00061001640360520101000881d441100e040c00789031b100d900c903d0b0600d10b20780ca080720b4400e030b2041580c1c081d020070300500d2000045c0c400303003800110074203070586c2c40101c0015113100c41e0000b554200c071400e0038030301044910030006403800b021440c406121401c031034020002c40c50074101070031100f50252482900b1140c20785029050010020300304c018810000130200802d4030a071030898008008080100c00303141640c0d43e4440c10202400120300562030817000c41c0d00c01000009591248100416050080d42090742c81d20000002901c016014440d006104401030307800208103006100f0251100c19030300d071000c04242074801c26440f003c14144100014003050340d05c14003040aa9030403100100645440c10040842d07482078040107000c6802d54014000d8128a024440780100140000c4541c0c402c0e200010950a10065500402e170b5242 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 267471043 1250 267469793 267469801
    0x3030c0703020d0f02060f0415020606100c05151810020c061603020405091306050a050f07052206020319080705180d1401020c0d1d090c04090207060606080a14 70
    0x1001800d9110341c454484e22040402ca5030100e41c2c00c0c0c100510301400200007060600250780d60f000122041e80b00741c802482c550500c50003082041c20780c00400010401c2004599040c440304101c0d050381e0314a004444085440d240120740805060400b01c0c118a010f143d58401001040d40207841c0b030b0f841c401001e080707140c03508c18003a030499200f011b80505141c1c003400f0004540d035580f032103e031207000c10880788800c80c5942d04e4040700300c650041036001d0740b510f80303028040d002e4100654036030300210347d08180d55941d0050a10f00000030b04980000b803800f90480020076015400720280020314661410103003d501d00510588810004036109000200240b000c00c00c10001c105618a00000262428008607141d45817480004240303423003040640c1d000210100c4c158020050041e69040902d403007d450914800d02d14840041207001034418441040807030b0450310100308a83c010003001e0703002c640e80c0e0ec02d1704d0700c2b0001d00080d200e0900450079034000200e241c56203001c1d03c60081d1041d10010707480d035a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 267472293 1250 267471043 267471049
    0x15060f0d0b160207150305012d03020103051b190810030323160f020a17060a05060a08070612050705040506072d0303050118020720041517070503030c070302 69
    0x102c8001001103105004000805107404010711051a44a5401241c55030428038080400c0c4984500c82da150034250011242c031806d000a00e00030303a58246408101d40d2640648901c050086d110740d4600c0050001e8010a410074400c0c40e06d2850b8215100c0080310341c0d80c1c1c00d17074807050b10451101401142091400091030b07801c50f404079031550b103503014050170308038030644003a000c0c08103100403034204241030501019071521a5030300d401040701d5502400c030840203580c902e0720b40c00080c00e01064180c6400101716184d54070501c0b03801420480040f1034145640b1f000003003154507840c0846400354a0203010039121846213040380d09984016141c00d10f000d42c55a5190300c981100000d5284c82840406d16042d801840110508418003917a008070351941030035030501040032512000d00010744100541000a614200041c0c01500d0b80905900940c407090003080c041c046a4943c110301012410001c5038807007420381e111072901e00c02021101c10903210014141d59201d15901d458030350344503c404000507e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 267473543 1250 267472293 267472321
    0x30f04060311161506080c06040b21040507060311030f0f130c0b04060905030705010e150c0a03050c1b03100e1606051c02040b040308090105070515060f0d0b 69
    0xc0e80c0103100c0c5080700c0c0e01e000314940c420f0107401320780c80301401e83c001000f0000740c000c12001d0060007010384000380075840014060b21461140d040420f5003c1200b41c3c0c4480d0341580064908000855041280303410b01d001505c03149075018680c0442c0c68100c003000d445540400f0361380b103048201440c000a0702d80c0e8006140512008100401780c4c00b00200d00c000081424809500918400040a441d28200309002c2c2040c00d2a8000da40298440002080740c3e03030f4443c0d036440305041c00307072001041410320301c0a822151041841c10303480d522400b0811020983c0c004020b040f0505400f054071b100b2040307142c010114400d42185694076a2202d40d14100c400c0141c0e0103914000c40040031204110f44d0104685aa04010b6000c0c40c0410400306102079556500c11110451b241d10304011480d10381000010b450b280a60300015001600206600e4000e134016012298415084022039404880b04603e00310618402c40d0030328003825900d44a042070f03040105003d0641743e8481a020303070980d51210f00034000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 267474793 1250 267473543 267473561
    0x10305060103141c020c0102070803030906010e061504060e0f040b10030509031e03070801062a030309060203190b03010603170d090c0609080c0f0f1302040b0d0e010608030f040603 79
    0x1902030000d2640c413006928815801d10a626000fa101c90148400060b060450f240d02002c025082041000040440401c01e1070548043c90003045480d1514401b00c0d69078555241b40c81d209000006011410381e42142c031110310f500c0221804085801e400003070000f501c249600b4107820074100021a440d042c002e401155220700c4032021a82094041c01030061440e40c0bd00b91503205400000c148107900d54810605400350000f42880f81c1400452120380c0c40440a203c038400304240038814600416203e40c000400306600b0000a5441e804c003452000d81d0f142c06400c11410303480ca81070614507a420107014040c2140c0d00090f000c00b001c031500c0c4241509902078040c0c00d001c10780d500d0000c0c00060070111a140605403a54847c05801e0030704421070700c2d14403a0b108003131040800c61070b42006540c5118040010100035240443c480f11001070300400303801781e5042011841008140030929111507440011510076031380090140e04c0d07075010402e45911642c1540102c000302007105001260094000c03580d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 267476043 1250 267474793 267474833
    0x91501050c0a0b010317030421050d060e07200709090c09110307030606090333020a05120609010518101a0904051006080a0f0e0703030503010f0b03010305060103 71
    0x1401c00209407050420030604011100b401403d00180240410508881c0c803e4010124040c51741c2816200c00054022101038441101100d400c1450124420400d50704204114070307040c4510382e21101036005a200480745040001c1612102501c40c0910303031640e0000c66a03845c00790000504040c01000504002301c03080e60032039242c0c00e00248a034840c0c0324081d81c1c0c868902855444c1e0404490003000d540c40340d0b2241d01081000355050002ca0328481c0241e600700710325050001c071001010281d40020f1480000a0151440030400440094104000b048100340c9c845201c0380c0e941d111303801c001c0380e51003e0044ca42c02ca11081d074241c401c2159030244030f41080d40d84034290010780e600c4801454000c68420950700d00030012800d0fa84500f064007840b070300001490784000c580b909014000780081001040e8086250301ca50014141149036030080295400c80c1c0143c3c1c46da1512030070050610380c400c1c801c0103500d41d940440001e10010315401d8030b050300da104000d04026480d54441b28080b58060b010504 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 267477293 1250 267476043 267476047
    0x1171503011b05040302210c0f04150f0812031009182906090402090c0306010e060708070b0606070c0e0606040b030a1a0f0d12020319021b04090209150105 68
    0x8403034521a00c450441c882c0741d5503041d9124154814000515440e040c0402e000c500306c0c001c3d041450021842000b00c03013040d50000403100c1040300103000f60500140c8007215040e0503002103000c1e95010500000d54000c10104d0700c01c1200c100742c00381d07a40b02c00c880c0b14003c03410342c00f401d0102c6540c07a080840f100c0e912200c0c04021040a48a1185015034105c0c07808281c1c6603411402c80c0316500385106540210100c40702c2400385095000b16104280040002c0203481000000584d0f80e03024419040c4481405007000b900c03403c4a103010321310b6501000c41511a1403600f400510307145000300445403d550b200004001c1d06140601d148a411006070100da403001040c070002c550380c2c0c01c1c01d0255208070314244011810140c4601460101b442e1004260b0046000c584102131036180c4030b02c1101d60b564002103100301414000c4080f400d500400e2800d04040c6200380369085640c0d800070b061241400d2005482511446e4102007000b19610801c00a4010904030006603040484440080350440c041c10070134 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 267478543 1250 267477293 267477311
    0x1503090f100f06090c020c090619080a23120703090e07120b01020105060109051c080307021b03150c22121b350102040909110117150301 60
    0x3420201c840522044140d594242c2d1400111140500c200902c81c044c3c08101034294820000e44504058074140d00980902021510580311030102c021040035040c9481c580300d8494015580318480614244e40c220a1017151801442e100c0c00e5100311220f4800042600c058001055003007500009426024001240800501c2101c12005c0034418112940c4542d007100c01d551542044400ca140c0f4503046a150104000c1c0350b907000f0b980d40042e0390b01282c05a2012072000302910039155001d00051a8400c04814424800d40009000d0301e241c181090b44180240714000b459500c5028044100600c000100490794248002005145d1140c84030140d40c030302542d841c140c501100c19076001c0c0c0c11400034226010240320b0004031181c42e00d0070348005d00d0140c502c0c040b112100d580c24600010804041888140c2c040d102d020a608481401c4400a5407a40e40c0c1d602c2200003069116001d44c1c844202c005014020b40c031480d4100188a14820320048c1038640803032000c4100c601e503810315099966100e200d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 267479793 1250 267478543 267478573
    0x518061809012304030201150b03060d08040f0905061512160e12060114040b030c010311270f060909040b0903072a080d020a1502040b0304060603020915150309 70
    0x1d580c2000a03000500b60f0780c00d01d442c0081c01c482c0c0d803c03100320030b2280c0140c060003100702a60483e500103808445426020885052107401d51085a00c1003280741003045000403030224980080b44a580700303c9044140034010840c8444521030000440240d06030f800003d4441c0c00003081b000e525000d64584403488124020210384d61981c00c51b6442c00c00c5e80300d500100456500b0307c0301030a2143c1c068600b80102c0307560710017180d900d140840c0c03110705050310f03480c88180c008214016250700ad05e41031407080442ca02e00b40205004021103010780d005440151903000d4904006e4100d8498803805000b00541751f50320b8851205a14014040c3c2d5050b000401101c2c1c0880ca00c01e0310380c0501c1199040003903200c0034140001d12002d6180d40314410399040014080003054002ca142088542c018060190034054646894001d21490300107285140b03021041c48144252030780843c0c1a0303842918062444e80700d403078449160070049025554004041c41c4044d100445d01c1000c0c5401038090310446400d9100b8004e1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 267481043 1250 267479793 267479831
    0x50706050d0603120c05010e0f0309120c030d030c080c09090610050f0d060503070807060504030b06060712030903030506091303050919120b06040219030c0e04020301060207051806180901 82
    0x1500e00140740c000403035046c481d0a01c607112000c00254003c04036280e001166035280d0240300340080c410307a236161a481041c0e01c1030000511721100282034840c55040d55902134010086a5031040c0050907150015800c40701030320480d02c3d1001700500c090015030390f03c0c1c104484000c00701144030401101384240189131003690054000284620000f2500c6414041858588003050f8000b0200e6803100c242003110a4000040b01e058942000e00f04c04250340703140c0030681910808000800003001c0300c0200c410342d03605500000310703d4403a03503042c040b50f11440104691400162041d036111110740f101c520000b8090b41c01000c0c011070207040c10001ca625540241c040f4003855001e07000d180046551001003154028245500c100100e4085041000b0084800040b02c111140c2c001415034a120070076401c1d02480c0d42200ca8803004200f0f550701c1d80c550701b000b512000e161244600400c0d04614000b0242004110720b4483c40c40540b5840304e5504940c40d180c5417103000380c504100303950f94010101010300c101300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 267482293 1250 267481043 267481073
    0x1c02040b10090e160507021207050a06050c1015180f0207050606120102070305030f07120903120e070b09060a050c01060b1b0303070c02060a17090d0e010903050706050d0603 76
    0x2d6400c5220310b007030401400700c80700401100c220156565800b03c12034100f806d03560100c5c0c050714041c0f01d1000c0c40f00980d151204507044564400000000042c04940c0403004020300c000c8032003500e013013a039602511010b9524100b00341420aa10760070900c94240d000b0f14040c4041d4070100c0c041900440340100c80c0c00c070783c01814241e40f5504060104125810081d030020000c00344071008520b0142030b524020710900000d03001c221030130700140c04615407601c01c00081c1c1025086820400084940380340150403855000545000d041c1416803c940160010414501312001000c00a2a0500d010704018007039100344070000c00d00c5818849240980c40900c1041f001cac11507640081d54803120501e1464480c411148102960380c000c004000110703074051420303078900f90305407280ca0301c4105802e03050316600c1e819020002e0b400c3c150402c020b1035890004207400d82e0001c54540c0910140314078011a040049404090015030010380304102d568441c500404142c801c80000080c0e06803260750f0042a5400c480e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 267483543 1250 267482293 267482297
    0x180904060e062a0904090203030c072309010b0d180606030c090e0d14090d0f0b0717010b0315060705030d0501051e04020306030a06060803030906090c1c02040b10 71
    0xc401188400c0d0070040c41e6004200c2c00d11490003600c0f2150004084108681c015074210404118002c241c0c55541140b03070455401000e807034071590003004096a5807003d101320014a40c5500d140301030f100c04503100c3c000b24039005d0583d100d5a0b0070179500c0301d46e50380140b20582d004c1e59500036500c5510300c4002029000c07442481c010402c24070310304261f40040070640003c2d5090b40780c100f00e161001e100040c040d46001c4c0314208260720300c01c1c618100e4030502500c803400e9082400481014200f01c10802c10004a5200300b501e0511501d0340e01b0121075454400386ca0020300c0c00c84100610504c20000055580a202556481d641401a1001c112076401c020340856683e03001082024404d483e5000342070243c0000d0f02c9451341701d00200240c815900344001a24080c60740000400c001c0d0314244039442c180764215006001040d07603641c50070b03600d0b80111070202c1540203c01c0403945048001c5141c2100d400c0c010260344030380527804c4684000300c400c3c0c2c2040380e1043e40e544004800340c90310502d02180c40459 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 267484793 1250 267483543 267483551
    0x212120a030b030106061d0114030c040e0108060906011e080a03030e010506040b03060c070318060905010f030e0a3809011406090403050702030a0503190e0102011e0218090406 77
    0x80e20050300356003041d10315500c00c3e41041d809101190f8000c2140250f054021076502a03a078810005a41041c07000180c80c0c01444004108601d80300350000400403940180680c529030ba80c1c0d10034030b0361606010f03603646215400c0f41d070040142d03000f010400704c08403800400c9461070983e40c0b440d6038546540780c2c0c0c1c201c0c08a03440300c1ca0041107010a104e0710f0707841070094a00340300c840c01c0c82d0b0000c1c0d02c801004202142c1035501040d0030b000c0c144255840c41b042d055012034081c80716103900014000f00c0360f0f40b20f5240000c8000340c0b03580401d80301e40107604003600400000e150b0341005554003d0004c5148010b580b102d11300d2544841d11510b080d440440c409481c2c1c2e50201a400c04901150039191071803081c49a12418a040c8103043c0c84008809a10035094900300d51030b0007443c40001c2c24001c07010340141180c80301045603180d0a0b01401900f419406075140c20640300d04107801a4203032110901d0780304000041c46414908840325030010300f1003100d8000c0d8020246000c000150508006131420b54100d603032 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 267486043 1250 267484793 267484807
    0x518040917131e0e060108041203050c090d0c090b180a0b01030e2409030705030912070308030703020904062c040c0812090310020405060d110706090305090901061d0409021212 77
    0x901e0350002d80110b170a20b0906400d15180d00c41e0503204400ea43c500003003650750000600914100300c1030b41c80c10400209002c0b07844401781000703014841d450040301c0380c503854071500352003500d00b07440742541424041c1e4103000d455441419880003054003d0105041c151182554060103405100324403288440901e18034801c0040c440051401304c00500521075a442040510042130300002569202e00040310b400112186048605040505603130005044c144044107001807107801d03801400390190103440030054541d40d0519000c40c400e038400314448400c600420041100d040961041d445130003000310212450360307103c0251a0080c3c4140e4050445400b04080d2002c0c6800e2161240a00c0100020350030b203410200001c3e114410005114041580e0307691841041c403820303040d2403141d5003040c07080004a000b4100039007160b0044030f40522800f1640c0001ca590b6004001c03d00d0144003824103070001c2251902840014445040c0c00d0360311410001014810384401c000e0a00d1a01c84004e4850b26910 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 267487293 1250 267486043 267486059
    0xd121a150c0c010810031407090e1005061e040b04110c07030605090109030e060703030905100605040f2c0705100c050d0c03050306010815100518040917131e 69
    0x2201d00c2c40c07035040048110900c40c008800340748540903642c203c001040d085030010700d41d0b03190004960007400b20f181000c811881074100400c070031001c00760b00c14060000b503441d401082081e1001c58a4001c80c000e24103a010210709095000321100100a44001644000c01100c0702d80d5402840025505505c109070500c2049014040c00340c00408080080c4000c100c1954041c1401003c6146c160062002103414000d240c400c0d0005c8819903041019100882000c03050701020340124003c1c01d014030700300180240302040e01d110b1001300c0388248000900e00f8090001c040c42c16030032a440c440141c0300761040881e00f60358081d0720885411664131219038070740d041c0c034049080c204280c1c180d0f0140310840e484600071a030400100ca602101c24a0304140c250b8a125a070000d230319490b003a19410241d212040e202d8150031500030a0f9441c02521050400f0b00c91004000545041460003060f245440200403503031800c04014003070b811a00c1039a0b0641940b20850f1880d078440d200c500503c400e041c2081000112 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 267488543 1250 267487293 267487303
    0xc1e04060e0418122001060311030a05100b040b1314011208180a030605040c030311070f050f0103060503030d060302090a020a020d0807020705030717010b030d121a150c 74
    0x24000760b400340f00c0300c841c80c01d04500c006007940000c0e040031010715103000c456101c0e4000761040543d01e00641451407083c00c00500038203060000b200d5503050b2003064420b501e0005194180e00340e0040003400500d0495002002424105880700d4002d80c558070000200e40e00c20601072600d4500003800110090f94038040c8030321201c1a8004606142c42c0c010401c0890090000c452488a104601903282d116440100340b0780c0a6951000c2d0400d4900701c140410001c180980ba000c0728001c2e079030b080035034401d0b800d11910b0310f01510911119000f952000c1055003008981c240c40d402050600140c50f41d50f5101017070540c0d002032026512143d0301c51041c011440c29619640d0000400501181032044a2001950b039451054402d42400103082c006802244200103140182a000e010b4854042d540c01200b03400d100c800c10702c504c0b00d5081040035041c03801c002074040e0407080b0941d41d11841240d820500750060403004800010006c50b105011515140d20284055940d03004403076982c1e8050003c0c1641c140 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 267489793 1250 267488543 267488567
    0x60f0703020403020904111507060221070e0f0d1403190f050702060d0608030a020c18060a0506030405011118131104050f010e030a0b0106020d260c1e0406 68
    0x30501c18481800541c495464195015a0100711003454440f0440000c034000395110580314031050000301d0600300103007600a819012840711009001a85e04042d2040d186001c0b1118400660140c00c0c084503842c1c510b8014602001c060944a201840c81d102d0003140c0c9940118220582d10002d114140e01d0052400300703515426034074120084000000b03006040c2c2c800c00002a10401c40400c08030351807065035011500034101c2000b260707a250020fa00c003945400355441c40902c00d40052095288078081c450200b88100c0c0001c1028403502c0c2440c0400100c0e03003024005580a6590389580c000400c600307001080503010f80c0302d40d032401d00300990030008260709014802c0c2c500c0741050001340d64021043c1c00d690a039101218035402280c403203801281e40800100c0029132600c0344480200c1801007043c0300a068800d240e090791b03040071021000751600c0c40d1460a503880481e01580c0285051056003200742c00c6401d20f41d40c1e0740780c864440b2034414604070403485010300c01000035040065541240e416048 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 267491043 1250 267489793 267489797
    0xd110a02010c140a02031206010203120a06050123040603020705190c0e091f0c02100f23010b0901051e0d0e060a1515170f1905090a140c060c060f07 65
    0x291201c4e07510025164000c0000040c543e00e032030707804200640e00034010744420001151440f8414902458500042c20182c890300707010482e440d01804028145294600c0e9010310707212240d11749454090100e0096001241c1615180105060705c240031000e1100c00022a0080e4401c20b421409c09820804051014040c040b1300e0703200344403025041850b02d00d00c001d2101d01480014084810240036410142e154030961406450611045a18441684a1040a80517999040242603500300c9034981c1c02c405e0103028400b0728140b0002c1c10941c031410091040e0107880184102c1c40c200d203400d044564018034880c180058075082a0354043c18108040ca51042041c0d0042c89000b610440d80040080340d030062052500300b05101c0800d2a0080d420b4070003107200c9801c2c1c400a8904a2000c0d18003500540300e0320081c050840000000c40b50303e0040324081c5040002800384030700d56980d03c454040d019076807e00e00c2c0c006e5203400c820030350b2144040c0ca14105000f018280b0781c030300f44445c011041002000682 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 267492293 1250 267491043 267491047
    0x120309060210141303111213060e06030a05100e0a05160e0a0303050706020405030f07030b010801060608060d050a02041a010e03070e0c030a020903011803260a020d110a02010c14 78
    0x106000050b0f0005822070545005505494224101141c06280c8200c007504035201d202429a401d07a140d4006004039482600013070f42c0c3c00c0e11154111401c54034420f00c142e00c040f080c000f280c000d4200358045504001082c1003498038590350b00100c1640031040f2201c2e03182e596242c00308508480076400f10450980c06240c00611386c20a030000555041c81400702904201c3e011881800300300840c1e04881c083c0c00e0040459000d11080400503541d2a50350104440740c15243c03000207002d59050158105440c42625400850b9a40d4801d0202d900745410094640b841410304920158a45c3d2003038807011040f1007150910011030400251181800388141400f81e40001420080c650940c82c46c01e81124260780361941d29100d00f140d08020303001c0c042d80d465040d40f81074030444030f104181e0400340600388a61107403510082e10303400030036842600c0344c80c500880c51010300041959a259001700f402041c5404002007100d04016000d90b00c1e00310320324900143c0c0d514164481d4590b0012403e80b030324031504c0030b6a8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 267493543 1250 267492293 267492311
    0x3080301060e0a08070603020d060317042303060118140a0501051c0f020d050f06091c0e0102070e0601020a060f02040911160308040c0302101e050c060f10120309060210 74
    0x690740c0c5c5a01d125017000c1560100b811011aa0141c00140c01103030410744400c4181036944450720030b42e0051240d0202d0480103c4810100d0b02c4850b400c0c000c800004014064a84c0390243d14074000318408001203071140c2c0d482c920800d84210800c3c1c1e80c0034650288002416606101c203100702d01c1d8508032111010001c1d0108680055015498082e41b968180c0b4113001c0540145015450310f9190141001140181c8040284424000818a8001001c00d11051040107246002e50702000109125030040c1c21195050002e050b09680b00c1d50401c9041c41241d0800d40103450312022900044192407405400003810004003049019010000000c0d0b6086454609100c50302e03800882d04000c0102488403650004042c8070421050000a540251201810700000c0e40c0007040403684e140d007140f01e030940d1220000c0d0340d4450000d070b03144801c0040040c000b507240e0340811550008010000c002009080d2000710741c0040f40507010314982d03c2511220070190070b00b100682003029001d54001e04901d030030300e45 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 267494793 1250 267493543 267493559
    0x10090c050405150d09150b10030b03031e090a0f030209060306130b07020c06070506060a060f090b0c01020f04030f2010110c0a0602070806060a0e06010f09030c03080301060e0a 77
    0x44010010000510b81d4a040d81c1e00c14801030284004c01500302c0070f006d807586002c4629504050450001200c601c1c242c0d105480c81a03085841c52007120390550310a0020105501c03d03603201407100c0c0a8001614203141070000040c0c40580aa08225654100e42800300300b1030030300b01c2c4a036030010000c4010700701d42d03c2e002d0050b05034032218040c050240140751f408a403001e8000d009803030001c0009001242c2c0da18440c1007030350f91b462040e11042d0150054100010f160340c49882014540e01280c2d44032100b03240380c48410341064001c0c2d40c40b940b02c3e543c01c001c0b03546140455001031005600c1007a81d022514000d04003130704031801108a200c1600700030903c0d41850303a14282c801b04041c1190500018801c10b10407443e240040c500f2405400c180341c55004940380b50009005011036081d40c048600303aa8500040c440040e41070f1154960707603107480012640c1507014440405802c0c07668540102da150b070b2501d80e41041031040d40705440609000005001d016800050790300c4040b004d55204118a10341005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 267496043 1250 267494793 267494809
    0x611060f060303091003110a0525032f06040b090f010b030c010c05031b03090a0b0f1e1e180d030905010e120a0809010e091302220510090c050405 64
    0xd00d2160070190440c08425019500942c81146107c1c401c2d0307100c0d003c5000180c200d602c01c2c03220190329800c030507403420305440e5030ba080004260326a444848041d0810013180400d800581a00c504041240d03408141002c100b100501c581e0040315452064106030802e1802c002c02021a0703600f03a41840b050441c25200060b901614034428a04176914092a050041c15405014280b2980b0429492840c415050000107001c103200d007111a110300e0b60303694120452034400e80c051504400002e12081e44100804080f103420a00c03400040b501d840711000c0e80d815000f0704404205d0340c2200c007007892551000d21840c11300c60013505075500b1100800c6600c000e407044480b842480d0420845d0004944203465079840d459120143c2821900307104941e250000311500314203841c900281141c01024690701d00b10000d1401a95005460101003000b602400b064611105000c041c6001014400c00786030740c2c610800c0e1244008907482d450241c00e0203011420f4600d8401e02a080005c2440107010326590006 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 267497293 1250 267496043 267496057
    0x50306010e041209090903020a0512070b01140d0b09070608010b0403031d01020f03070606080c0405060d060f020f0301030f0203161503020304020a03050609030a081006140a02010b030105010611060f060303 90
    0x54480543c1429041107a650700d10b90030a1440c00d041c03000e644201a000134402c01c601d03100303000761a40c3c1c08040e2406021401884405403c045080d001008003019041d4500c610b00303001303400e03d04405502e8031030b001c445200303582d0503101e40e02c041c40802c03650794000d03025405820041d010303529091039501d0043c1410000c0c01100100e408148022100360300800c01112010790705400e0380e8482c10642445401031031705100c0c005082c0900503a00d0070070f01e018030440f44580340090401c1524452610740390000c2c40c000c5c4a40200c0c075408c10040000342c261002642c0203602c20204642400c125106040c10041c2d504a10400710380d241030244056050014a55800c0115107001a1603a0385d0340001094201240d00191a40c041c0350b09000391103c020006007020122511500b005841d2801141501f903c85c0c850718000900c50b40d005080d82c034400f8000c0030407681910000c500c400c03900c00040e085444c2079104401040c1c151003401d0451006000c0240d001304604661000b601c0c0c54000302e40c40b442868 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 267498543 1250 267497293 267497303
    0x60a03020306010306180905100c021203040c050a030c090b1503241305240310050a020c0709060503011104080a0206091801122d0204020f0405180709050306010e04 72
    0x400082d069900c02d9110300024034002c155680720b08840c1074000020710710031000f692680512100014000040e000e17650b00000f8650080014242d09040b070001c0e5040603100b00e0740c6503103a600c0058240d59284901300914007454040361118617011000003221000050f0034014040c4d000c0703d02d183e09060040e298001071710007120484002e00103014000d0010300a02d40e0b1302000f400000703110315a003541b00328898240d00517040c050b00045208107114207400040140e05520031010801d00418036000682c001c10744e101c002d42094500b01e01c06061107101c0e0440e024042c1c0d50b0700104910b00d02402036000d402c48450016141c5400c11611944a0040200180c011540010f00c0310640c0c6031302901052501c100010401c3c1546c45025100f440b2484800940d42501b207010b000705402041828a071681c502000d03c20180c1d5041d500b07120213500070f01410400f083c030078080083c1c2c0780c8507481d06000303c416800900380d0510b0034403006800038030380d42c00c00b601036403000b0010710510717020043d0035070419003007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 267499793 1250 267498543 267498547
    0x15070c0c1701110d0b01140f0d021309410a09030e0d0b040506071e03050903040b1804050903030106081311220c0513170114040f11040209060a0302 65
    0x7421500d400740c031070200e200c4102880061200c0106000b64000c0644940990300d104d20781c08140d102da842401844102050030340c0802510380500c0a41d030080c01d4500700c40741000c2e105030b500c210b40d1040382c00002c070107000ca10b507208100400d0b00d6042055090400008150703205600c00030304034811410b00138001c00b040c80c1d603101c0900c00d160180900c00c403120b100808002451304130b03150031241c03080141c408a5451184201080354580101d600c6001013049843d10510304890020403805041c1c0607162440a0004001c0412020798910042900500c01e00e00d440d41c6107418818001103440c018100302c1107400500041c070405078441c03400c07500000503040307440c600704d0f4904021003940c4001c80595804003519013400c0500d407510001601e00716140300100000081440262003502c81e107107060b050482507020038005005050b01203409440020000a01152980070340c003200c090565050b250301d640c1c4000c8000700041c4800e9012041070641c0c1c1542000d4000700460040c1c003d60605000b03140e00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 267501043 1250 267499793 267499829
    0x3130e071706060409090804060f0f081f0512012717070c05100f120923030705060901020306120a081b010b03060a1b110c0402030403110a030215070c0c 67
    0x30f04003590702030003004500308008032851074110300030b5001c0e1081c4400305d00310001ca4500d0900500c0041052071064a5554507680c1d15034154440c12070061604a5a0000c0400410241c90303198140d014000c1aa0000421004d120791074009656054a140d00403030005a480000880040d003180300030a038040400d071140c8180c0b41c550303054001c1ea000581c01010411032044041c2d40072008800419940d12190391122030300d40307000c0c140c961305040175201d081301d07003500c440c464001003622070003104031801d8900749002070303541909154080e1440300850790003005001052800b1a04c00e0440c04010f00203003054810742e501c0c4c070440d0103400c041c00e10420000640060360309080d00f00701c81000e40101950518980014248001c004156400c2da1003401441044a02400352a001081d18400c00c02401e08112601c100000796200030012030030000c803d408100003000c100004006144241c001d4031650860f480c4600000e071009009004010104040707201055004003a1030a89a0521040410038a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 267502293 1250 267501043 267501049
    0xa211a0d050d030b130e0a03030b040509070303110f0a061b02030319020f09030d09061103070201020c040504050c03070f03050d1d0d050c030307030903050c0a0e0f0a1d03130e071706 80
    0x10005104d400c91411b0001116510f070002c5007001c0424400c2c0c5040014410780014002100c104855108007079020600600c04a40030780520000f142880f01100e84050481001506000e80c109c012521a910b50a00000b00b1049083c50000d203c054130046041d850320340c298140210912408030780c40c6a00041d42c82c0005500c50031114003e00281c00c4506c51b18800d80300401100c40340c0314150004108043e0700c0041c210200442d0241601603009110807048401000010708000d0421503031407240c00c0300d8032000e0303c0074018580281041500c00745114030b1130a10f035081180840c1050208000d140b000c04d40c203c06145d504010130000d550403444c10a0b1480e04602e40b0f8220109a1b905d84400304080b4101648034a070340b03040e03034031a4040d80d40c80c070b03400c0e824011060309a000b0710042c1e00080700091154500b40c010b05034403915140f004113140c00141010207040711000304031103861b080090a461942940000c2034000e0160580c88061740c0b41080008124210001100824145020109001c1c0d5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 267503543 1250 267502293 267502309
    0x90a0e0a0209010312030606050906093006070206070c0201081914010b0403020a050d0803131e080706050f01082d070b040e0a0203060904080a211a0d050d030b 70
    0x10740c00381c50419696120f003421610031305503083d40b500290800c4c1000c507180d4442c00c25211543d0000c1d1440781007400d0b14040203805880c2e00d906456441010320042649240020b102854000c041e001c2c004030b0602d90350080c04d01600812280074007150849800040c1d81c0403c8980c1d10601c1000108483d02c04901000003404d4040f0070310304034101d0f900010825110200040007201e2080310782042e402d686d40705108401c501010094844001400015441c4a441a61003441d40c420402c03c80c0c8025101020418440a000305458826000c284902080b82a104941c2c2240c520120b0f540d040d0325145030160f880101c145a5081c002042004541c0040c08046000203410300c0402c1d195030a80b14050304081da0054440c908507500c48401044400070380b0300c21070b806a0000f51012206a6443c2c07030f800a141e001050200400010780d0300c1c188000c034056440000910810000718024051008103540504010f403c1d6200e000005800e2000407000110041c10013100c2c1404617010355001e000400c0701c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 267504793 1250 267503543 267503563
    0x120213020904020d1d15011406090a0f090b04060e0f0103060e03090307080d1416170405490605071704030f080a0b0607110a0504021b0c0d02090a0e 65
    0x11405c0280d0207035150140030001d41540c100c00203c8204000034080c0c030809550130722403103002d104280009030720390400000500140c10040d02140c0310030b50350034410b4080b696541c00f120300c0c10b56034800701038145042e000300d0000b0001d0541440346824600100da43e0640c0611004114581d20310305200c12900070320903150302d84801801c1c0d8502c587c5e9400410b07119400f0340c00c1100011a4201c21420050b2040250703402c80d0848050810755410036902c000203503d00e41414403001005000c005090368400f0020203010b03107801c80d881079645c1c802403004203446c40303c0045a0249801c3d07a01011100c00c0c0c400f000e4079150019008200764480c80020f82e081c1c41c0d0a040c0c11920303405d2408000906410030040c1c03030f40300700f40c1d610b158030780e50307481064022134542c1d0490035032003c410400140460040d4000d0b04158100400c550140399035200041c0c01c9a0007000c2400c000d071a4556034500c032407001c0c405107000407c140c03040c5440d81c1c0d0035030000b08890b40051a000d00c0300d82d2201c9241c5100b8081100c43d4074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 267506043 1250 267504793 267504817
    0xb15040f180605060402030412080c040918060b0105041202010c0606030605130309060e0a060503040c0e070306031403031e1504020a0507021f050f0901050c010606090f12021302090402 81
    0x7440280c01200104480001c006442c014140000b050303190a0a2080343c0c4926040142d1817640c0c071a4800440701d0600147c10740390072120030b000116003000759114204807001c0f080c80309424a20030749000e00c00c5d18020040e05061002c240420000c00c42001500d404265091800045281091500c50018096900b024094910b09002c0103541300160b03604c1d0351f6242c045d4803140703202c6a680c50100c40d80c0f000507141981000070540b04016580c0114099a0024031541d20021001d450f00f20340a800c110031640d03940003d8031000c0801c1440002800074602d1025080030710300e14079000c0e074080380303055510380510035a0300301000182c03c005042141d1140201c00510a40d520428030200514030741021800f44d10941c0204440d41d9070862ba441d01024844150701c6040c01d02d4040380340360065170815103080c2e0520800700410b1001c118280301c0e81e4042c0c5a55150500740d41d0401d9001e40c079019454200100d14034a61500c400540d0300d0b103400d42c100003900500542c0d00c03403601000c0b802900174507103040d0b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 267507293 1250 267506043 267506051
    0x30207050a0f0b1b040303050c0f1f0c0201020c0303160212070803180105091203070c0209090601060201061208041e17060105090a0b01081305070512010203060112090b15040f 77
    0x410001010114005010300c40c2d030100c0791030702072a00c203c0e00040c40120a41100170481080007a00400140034000d03007850958550341a180032040c18003a045c000682c040c0c00020520324050928420b0018944280c4000c5062000f40e4000b10354030303c005020741101c9803980c000c1d18485482000002c00c44210000b64a455110034503100881d0340003078070341d003100c11420100e007401d10105205880c461307040d0200802c044602203108000e16400500702408000134a205900961100741d2694051810040100b4003036151920003805c503040b0342c0141020701c1d540300c035003004a480c101c240c80640380d8500654200101c0115910361001641d880540200364185a20122401c0841c030b1394100c07601034030f00340042d17640c86030b40c041150401141c0b60301040803240850b0300c4494030800f454025203d9401c44074800d03143c45c0080c0c0a00c041201c1c00b90141c3d000800c002c0e82d940d21000510302c0c1082560f017070200f4401c0d1355480c240c000008180b500070500d01e8080700c60668442e00000b001c15144c0e00108 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 267508543 1250 267507293 267507313
    0xa0b0f0603103f021e0609062109010c050703180f03050c0406050303030c0d05150301051006020114011503020903121c0515060f21070f080703050f130303020705 71
    0x80e07041400785600c09100a140d1a215081e030f03076540402003070568002c03c42c209041e00c0000c041c1c0e254514944c0704da000442405480c00e280c0b81c0c01c004182461340380c0c1409a400c50300c500300001d0300c80d004040c042181d0401041e80c0010381c2120a5820041d807504100c04190014504146110525407110101050211001003400404602c40b840c07814191001d02400352583d05040e5681300a40b405801541c04100e0044440c0c0e883d40115041200c0c440c03030308104d81d0740d5000242512400d0354107007600050b408040114540921804140c0131441d1213180c0c00390f00d040942410005840003c6050680020b2550043c0d54180001c001001418410036240d43c015015000c4441151055120803171412012411035981d54400e180481e200404e0686484c170790b0300c42301e4141d800031410301201c8403600710b40c264203500c40b84280b0302c21405540d0322074401115070801024564060041030502d0b14001c140801400010b070881c0d030000c1c0b85120207030b0700340170b61034214020312a0000c0501103010703da07022 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 267509793 1250 267508543 267508589
    0x1905121302120c10030207030302040801020d23041e0f0f080a020c15092407050307060605041407080601111606091a04090c05040b0703080109050a0b0f060310 70
    0x4900c58500980d4010390101d03810350499914809221010340c0b11100c418405000c6100340c00500401e0b200340743c0035060a5540401c039003a600030000d800b4129031910346400400010484100c025a140c1e03288003094109074035185003940300c0500b000d9845014000220074132030441046490582c1c01991040c0001c443d05100c040d0f9080340240d0030050045662000c85071801c01ca04d0a00304080c404480c0c40c003054041000718480314500307955070100001e005900c0314420307900600314160140015660311107003480d00c90104c51240e0000381c072031031030480498010300d40c2488442c2c0c40207540c1081090b51319201d005841410801513007502c613105101c0c03c02d40500543d4000c90854045844082020340c80e040e180344000501072842e05150780c00d000401c10243d06411280741c000c0d0030f00b4864a455214419030005a114440541c0417441800c0108190485031141c6a80101c85071010060340b0aa0000a441c8c0000e0350100c500c10000403010403480300f20021740c10024a440c401c3e801c030b040c003840c4030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 267511043 1250 267509793 267509821
    0xc0c0607110c03010c021e0f0d020309040605090c27150c060108070e0411040906110903160503150415020703020d12020403030503060d030c0209070c0b1b190512 71
    0x7440301a80500c1402c0411410b05001e040c504021039005480c4c0711003518114821502c80301e040384500e1141260880c064403040c06002c4540417540c0c080c41d43c0b0020b50041c001640c00700e50009009050403820801150003e5058a00d842004c0202c03081c0499150900b00200101403440e86c0c0c4480900c1041d00c514064600400801c4400700580320f640e80e942003020749440c1c05116008080e0402c000103400102440034902485500410004000080e52145800c03a1002c0098502000c80040c041a0900c4c0800190a40c02e05125100c0c50107418032001c00e4413074402c0d80c07040710b1860b0464041810800c00c000c0c540756030510342c05e04544414040c10000e5540308011030700030114201001c108100489070080724141d0740c00d0348a1514540312082400b00070aa0010f00703804000e000004440141d441403401c5016400554403415205c0003410321023020800a4440b44030840d0308444d004084003a0f80550f070300d60350840d200320032250b20204152142e100f611085c071340c001c003504200007030303100c000132 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 267512293 1250 267511043 267511067
    0x160311031b07080f0a02270a02030420101407020d050606090c03040b18102f070c09051305060109091202010510170a0c0902040501140f030406050c0c0607 68
    0x8850480e0b030f071076140c40c0d101d40865003507403a25000b18120b003000d414034003a25a15200d034050700040d05100300725009142c0006603181c80d072007900042488180601010314050082e00c08408400e4944104002a03411110444c0c92061018004540480280c98000c2e25130480e0060500303e00c001482c60426120b41040314003030710070000390004c540a40050000e413403250345c0c0103510300d000d51180780805a2550342d400458609105a2841000483c1107010301c1071200ea00e0129008100d101364170111080c841c1c00140c951070304060110501050001c0c20040881300c141000140c99100d04495220310103203e00041c0042c400c5030000508114141c0c0100500303806074508010071002c500c002c9085c0d483c15038886482540c55202031040b0000c1010004c40c60400ca421a000d01231556940d00c0d1401969114441695001c142040b483d6003007040301040c8000728000310f142040554410380c887c0009000a048959968009401c450508048a0b004a000403c4400303d180041d00148040c640003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 267513543 1250 267512293 267512347
    0x6011215170d0903030c0206030a0b120c040605011701090c020708120a0f050301080607030e0f0d180603020c060f09211b0106180f091a0708150616031103 68
    0xb85a200d1a44100383c09420340b685a52200c45e81c0003141c00f00200364002914000c1410b80d904080040350b581c408a6441040230710340540b106240039001c10084508592003035041c002040146d1031541c1c0d15664440c10f48220382e0000031841101101240381402c139810900062140400105031040110068000c41415640d0b0382c080702d51801c41260179010a209081c510b030b214030042400203000350000303019210324004444c2d00110a8195a181c60035102d082c0c00410400a60740e51410018092000545003a05040d03290841140c40c00c0d41e00c420041091142c4841c24002c9011144240301c2c001c256600d02030291100000c804410800da481034410040100020309224440501030142208641d40e03024019a05001510090090030b006a103d01c12640d440301c4600015000302c0300310f0891031075041c18965920303114902034407400029100f420045440c1440481d00d9a884003228803c070014400307080c00301d20360320341600c075044140f0b4580d84501000c580e111040740c11a01c80604401c800b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 267514793 1250 267513543 267513553
    0x130914031305030d0e040c02121602120f15040311102408030d0c0905060c01020901080c03010806010302060d0f050901051e010515130308040909031709060601121517 73
    0xc82c100350756182c40d10348130008681135503600300c564034096000d00d900c2266401552454000164104001d80c402000e051850740d405003601e0541c1004501c990040942c04010300c015091100c202d942c0303100940e0b40c60460860080004c1c01c02d4401c0100200c0c80e070f2040112060540d985803c0006800c9a0610b40c3e000240d6254a45484c205001048225540c00c000b0b180303490090380441018019a1010b1024010304840001f15a100c00c4024000c007420321700016160100800010501e880180648854500234001031211800116240b811039a0440780c1d56501c0071200c280c01c025060b03004044500b5841c000411408802c1074010324403602d000ca44003200e9a0004032003a460001c02c0c002c42e90011760b104003a101c5200d00704001c0030309124988400250075030741c0e6075412143d80541c2242a2054070f4026403810981c000a01d1800c003030a43d1310302c152618111002c1c1c1e076500001894030b41040103030941001d400031558001d0460004003030304800d10580b00e003083e10f0721001c402802d100034820 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 267516043 1250 267514793 267514799
    0xd0504030f1b1104020f040306060e01060503090706050a0e09240d0c0e0702010209030601060e0a050607030806010c0c050a0b041502120d090510050403170a0612021309140313 77
    0x4141c0c0544030303040307405581501100e0b0a4680f0b610314050304801039007090b400c004400c1c54030200e4000d0300065104003000f08520b401d000810312117500c1a400f20041c440f046c8184900c3c4d403c0400c0c0301094500034038040341c8030034114404641d885c0317400112a4104402d102030044a209158121443d044241a4503141e140341c40140b280d0b1001851002e400070103138030020300405401d02c2206130800000c0c070000d03003002e1501e4002404c2c4039003a4410004500c805d00120302c24101101100000c00007142d146007800c0054a0103440441e00501040c1001b00c098180000c100c41400c1d0030000e0003015201031495a1a005403014075030003806100042d40c0c50480c5c4c0e2001c01e1002826981c1c2c1c203036200880c0c1c1490780390f030107242c003501035007108440d00c0c0100040c6843e541000e200f82c41c4100d00a079541500fa0b141c0d0500010032540107031400308074600304a4280600720108001050496044c0d03481129909000b201c039006180c400c1005250260000c09584e12032800800740c242858050310413481265 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 267517293 1250 267516043 267516047
    0x918051501020d0e010c0f05010507090807050a1406031923090105060a0b0d0603060f0c1b02031906090206121008070509131a070908070504020f0f0a020f030d0504030f 74
    0x18050f440100041c03c0c40301c00038030303c0d44200c42e5601c1140c0714903000c00100495175586400d55038200c079443c001401c503080810150000f0007480b0014001079585012480c100316030103a0301c2c0c07100c0c40c2440c0114000808107084a080c1c98404000300250320301041508940c0c03440c0d45100c1c2c1410701c0e040e00000f80001249408406119031400303800c3c004c0040300c40360714054601a080d0070203558410000da03100000404140c0e01d0190301071034841000300081000e41c540014001d0075000e4074200c031401110228000580300000c954007582809140c0d030b10000359501d0004080c2040c0000290070007000314409502c40a8030326054002da00841c22510115281e40b2140e540c2c14051084582c41180d08001c940300c1c0c02816444000e26024a440c2c445104032a2040c0d20300302426070381a0002142001c08000944060220070040c0c24100c0c0e05502d46040704054180d0782c091001000c044810010b03c103652103008000c02c0c0d62040c03440c810740c0e4552500c20303510b20003010200c4060700451581c103100b110180c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 267518543 1250 267517293 267517303
    0xf0215060603040b0402060d1a0a060c03020c0906060d0f0921050406120906140f0a0b03030f090a03050a030e1c020105180f03030c0f0c012a0201091805150102 70
    0xc0c2014041c203045507a02c1e1160421218040e1040c3d80040041018080c505420b015a1100e600389042d44076002d6252020b10801084a500c610300700940c3c080080002640401d950a00c08400c81c1d80b002c940e00c038400002c4562098020500d44946000011032145a940e040302c05810f0040d90f04215100070003103060800c140b0281003400007003042000707004450052122400000c1450000960030744655180c400300c62240c107500004201c7d5400304041ca10b1488211584280e412506016012040005c80d5480c0940c800000d240080032450f800951110301e4000000c6400204aa0301503510b4100034240d0101085814003e4589180541c0002000b245031700d041e980c10703940d140c07410003119402000920b280001d1035022100c0461401c0d1307a60100054a403061120024210149000100900c3e09803801071183c14000c0320350140740d010103525409418404000b980c2810030a061004941741e80c8150401c0050135005ea80805080e070700d66002c54071581c503c83c3c1c20442640c241c001682d40d0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 267519793 1250 267518543 267518551
    0x100b0f060a0207171c0c0c0b120405100b0a060e0d12050a03111e0c0705040501060f020c0a030302071701020904050103030906030f060308090d0809060a020109030906090e0f13050d0f0215 82
    0xd8a002244981070b030300c140c0307006d00c50b54000c001e450009038985254040310750008812202e81c0784031105001c2804414090040701180b200007c0140341c45801c049104c415191140c9014446441500c0380a5140d0b844034956080e841011651980c500c1c40c0040c0c8039420102d0598000ba00d0400d010302d040345000c01f114189802002c83c1f40c401e483c941c1000881c4c0e80440d001106902950710001155282e03800368a01825481e1111a12030082c158002d03c0c1c841000c080703910884446804002003a004203050050341c0000201080c000090700e072145c0a0302c140c0303002c25005840c0c40000014150f0095008040d254581d505000d42780b00d11442c14190f5055000243c0620400c1120031923030b01d0405482e6040600c581c3e510742c01c114107400000c2064224403501c00250351205440c8081641c0031012501408160408000881c01e2518001c02a00010082859a00150081102e1068042d148500d9691081c01c0321450760424200800c1a09642c096201601c148101f0310070b0a0305010843d880303 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 267521043 1250 267519793 267519823
    0x1060306140f01030e0105010305060106030b03031222050f1c0e01020c040209010306050406090603110d05280209090a0c0b180d060b1806090f09100b0f060a020717 72
    0x7010440c5007000240e24000e00960305242d518010014100f8082c0140c03030085000701c1c05400d80c1d624000020f800c1c0c52090f404c040c400d402c00c006006450355642140ca41103003d407600d50b9441640143c01d5070440301c100e0030140080c840c860550315158000a150200c4a420905020701ca4080101c03e030394441c20703944881d001d41c1080403100c845040c00d6010349404001490041000d03640c0340080b50454a094200c52700f41030f00c540d001e00a02940d00d1510740c14120581c0d2021018502f5140c11b40c03145010080007110b180c144a4030b00d002110503071060482a001440c201c558102440300540d604524801151801120040001c40607441001d5a070001c0310b6120500c19000c42c0c034100000c0d016105005c0328465035800a40710903403900c00c60b900c80c035000e480d401e0742c86003024410040212070081000d40071040810821207881750100f00310180746114031000c00e80740440000030304101c07011001c00707400100100f201059190700050103000c0301d08020320f082190000b49025a01c4054148407424 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 267522293 1250 267521043 267521069
    0x1211061b0c0901080d0e210c180103080304080f1b010b03070602010e070e1f06110606150405040203040533100803030103150902030102070c1503060e06010e0d06050403080f01060306 80
    0x117030740380a120f0007075401000030480f140032451409080410304028100c503595600c16607081c00142849103044d800514030403c40c0710703550325507982c03604584402003000704002c602041010703a918002e401c0e01d50b80700b6480003009070707820312140c2503000745045440c4500c0383c170812000044042c018416409104503180181c4600b40c00c080b0500001c1102901d04814002c0000c601d03600c400100c0c00b068007601c215644c40500b541200005450590302800380380c4510050508100060030300c200301d03021203a080c0c60141c5c42c1d82e6035007000b904120500305a070a001c0701820307400c150141c070012a0008031070030701d000b0384964a41410342e0940c1a540d016000ca50740c800c20050003c50b01100815080d400307016800701c0d011800e030340442d00303a800c0788004031124a8034100030700c10300380c103c0d03602d491080700c0e1301e0104081d42c43c2c42c03040411210040c20032418042c6c1e07117032400c2c0192a0341e40f90b025440e41010040c03009003010728008096240890300c16029004900011902e20f1103401080c3c212646642902c0f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 267523543 1250 267522293 267522313
    0x4150807060e010207030605092b0c120203130f080f010b090601030b1f030f060801020702010903110f0616030e0d0b0106260901050106020f01060b041211061b0c090108 74
    0x1d2081c034003403403442d8150310680f03130004001040f901074540704903044800b403d003148100112030104400982406511640a0192802d81e54070a0f100c0160f60340000030344070001c0d80312905034114816411401d044414440c408984050384d2010b22040380d10800440e044590810051400c0310b61001d60b1640c0500c092020a06540c42a0000e08180030300400081225526581c0e155015010030702c254080782d261407860150b2044c03481218000c0100380c0003907140c0280e40d8002044082c1d01d000040ca142000f41111085440c2d1400f044101f000103841140d5a18400305000041d0b44021811000a80302d46c05a9902c0c0c1031000100359003e601105402159007000741c2985c0040c4501d40c01e10642c0010724102c10004044459203024410300000001c095041c00402810410f0807015251300da814520108650301c8180121400c0311405144070408407500d02d02012011040074004e68004004243e412107140085507071010082180c08803004c8000300c20602229040c00d105030480d50300f04020350307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 267524793 1250 267523543 267523547
    0x302090405010b03072409120b07030b030111040302030106060e0a090905030d021204050106150f050c07050d080d060909020907030c030b060301091512081606090b040f020415080706 80
    0xd030424410000898400c06020100b403030962180c0c0452907889540d011146200d035030703001600f00100580b50501d01c20342030034941e01c20703510441e40092070009150700103880984240c0c0502080071000300248260752503100445901c3d0003600090b842546006e500040072402a552030300324460103808542418a01038104004251454040e81c1601040080c022000d082c0d100910780e0201081038550a4109400c06a084500c90781120000d41c03040030b400c100aa0300f24541201001891901d280c5e102c484000c1e007824542c0d1640060780201e1025015010803814901611611001020820070580e4410468094520815000e0b400c049684040361007640310703800069801905050210305101094017180c90342c0d100745e10401616555085481890f407a020041d801007070420041c02c1208015141e400715445400c0704682c407000718200d410200a0150000020700c1d4008400d4007452800e4200904e01802c4034204a100e030317260010241c4d240080000440c2a0f803c503c5c001c1840c0380c00c02c041 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 267526043 1250 267524793 267524809
    0x60d030507080a03050414010c0e040c020f0f0d0206100f0302040207050a0b0103050303090d0e10030c090312020714120d03050a09050307151409120706090b07020706090803090a0302 80
    0x250100a000c10100c400319000074001c0c02c051002e0740d00001d03549800c3c2004802440104040c4159904081409451a40c401188014890704882c00280c020503940c1c00c0c0d141001610902d1850b008001c01d00310500404a40c10001904c2e0350255402c56449403154402043e80b406410f80c08142c000341440503082030b0707010308046407180741210b1454080f915148096042684121441e910003c01c1181080b000d1284018445003800c02c0030000300c00c0c00010f840e06441c490401c0400d42d1300d50004c0000c910410000340199008855031a00d802081d000a4441046000381c052500904440f1216403d201460722510210103028128001f01410110041d02d409801517410940320703c00d080205505100524560b841441d0840f425200441c10350140d55001d61030310361894450042000480307000c03030b43c0f80300446a54000c559800d4240740101c0145507034800503202d0078960081040c03841e000a050001e540c1c064440791a0641d1f107a109503581d04c1112105070308104662001c000505007403032 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 267527293 1250 267526043 267526069
    0x1050c0705070f0b0a03110c06130302120f040b0d06120503131d1519060306050405130807030c1b120201081f090e150903030a1404020d021c0b090c01080a02030f06 72
    0x1d031f1500c6c101e181c00c0b07507510b401c0040c0c5203806d40b4424985000105501040329040c00f0000e1402d20b0705210f14205d0341e0f1842d024034802e106c001200042e00d00c110001c503902030310240c14194101c840d2081542002aa40c1e00a40c0c101d0203090032000010480c002c1c0401c0c2d00e400c1480810030101c0315900d0080548802c15905e9840350010000c0d4044550340d00c4070036065002c0d000342d5400140b1580740908020075184041e04000b080f110903c544170100e407580080390000c9825090041c0d41c02c4052809260a18110082100074428203001192502054078a40c094500076130314240740e52204107904061001c291085102a080103504000c5402c80da0404100301d03c13101c05843c00c0030701c601c000107044841240c58490f5a0400410002003088521480007040c4403039603003680901c0c02e54040340800540d600040d106014102000800108251a04043d5a03005a00c035041341460100e181e0b4428840c040d45001c02c0781580029000e24291091381e124440080f0003100c1c0ba169203003031000010400e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 267528543 1250 267527293 267527321
    0x4031101030e01140a0c121107080a090504021215040507051813020c06090f0c0a05060706090f03020f1005040f02090c210402010909090309090216020301050c0705070f0b0a03 77
    0x10075041c0104c504808841c0c8607010000300031942e1900401e00801e0b0017082d038407025942d480c200c50400103241c0c0e0300a861940703a000c203402d6a102c42d450b80a40300350200c3c0d4403a650241c00055000c01c085c080d490010b000e40e584d4005011500041401c0206450301195920001a010300001507440811034400c501100068651400300c1202c5000605036800244041d03080e912100034441d800b0010482c03c3c4000442a024000004090002621144130740c82261301c034480124071542800700652005640d107902c8035603410400b04614020751598100306403c41d260083c440304074074014580c007500d0700c80e6501298110914241d94208000305201400c100025801841040d148442c9107440c0e4100d00c80c20489160f9518103803000419a0312701d1381113841c0c000c1c20005d5410029030403095030000c1d19918280540c88170400703452060a100991406035066081c1414050070080203002030018602910684022540b1903001a41414a41c8036035510005d00300700345080c940c4283e20421010882e8 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 267529793 1250 267528543 267528551
    0x150b0402070b090703020906090f150f040e0d0311070503030c0a021903032c0c130f0f05011806062102070b090d020601090c050f0702030c03030a18090204031101030e01 74
    0x360b1150002410304689020303ca620800085c0194a02400d040c2d501003070131130352801c051620040c0c0002c0700d030340a444641d060300e14500c1000161303203e00406a07140750107001007042380a025840c99a9085492a100100e0b2504100d080050b200d10122940326411900440c59515031545034101680500401c00460180070111902c1d0480001c0120032a0300980c3c010484142c3d0112107203005440341c0f8940750000300c01220b590038540c045680f030743c105d02c11104d48444000303845020f80600b9922822141d1a4502064890194081c0c3d00c140d06031040d141040c9180c048080d21101101c1c0e490150301d002c41d0100d0809001e1005060403805c94140050000d030401d005c03a55807042d056416180380f00303d50011008070300340380c0d0304000f030030700608040308240585213a100002d0118840c0c404a40c9c8150750001e481e41c02d540782003044084001c1c1c06011643e83d2809a200241200c03494002c0300d65000075084002070b4000c80e4021385003500c2e04a480000401040c000550043c541c0051801c503554071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 267531043 1250 267529793 267529807
    0x10c110f0d180e010b0d0b030613030c02010c12051b010204120b1005150712080105150a0302040806010f05131a011b02181905090712050708010203150a050607150b0402 74
    0x100901c4c001c100e11000070351550301c8920b9800a94650a6045000707074003c41c100400041d80340d440a080f15003505200c0c03501280b600048070b2410b12082d01920200102c0e0009654139400001024440b143c0110160f5200c1079003412401d03446144202505808466008408281c0c0c070508540c0000c03100308214850342d030303907004110300141d4000c01000c06440410145e0a02101c03803115058210b862904103959030403c8005a0b0110500319400d01c000b50114448805034003035030450300a001c8080071905507681d00c00601205801d940a22801806080d0704043c01d00c0701030081880c414200081c211786411000011a0038011507101d020840020082d083c0250310f80d03d450304d8141d99a005940c01034078004203c006d00400b1040d052a20078a0002004602c0c1d40125003003040c6c803040034021300000340303505105250502c1c40d00310348040c1d4800000c1c07054000f100d604c00c00c882c090517141a000c0d0b959607000c10442d4001c5030005480c81000588041d08804180d00c0f0b0340400c48000e00050800c04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 267532293 1250 267531043 267531059
    0x60402090f130c09060f05180a0b031207060b100c080301050112060b0a0f091d0c090402040503120301051918111e070501050907060c0803060301060302060705010c110f0d18 76
    0x40c580c4034901403592804141b052014204c42440601015600d015581145040c42010288004c09012040b6a15000c002103603805025800c0c1c4441aa1403d9440e02894203104005240390a051481005000d41003030b80b0a0113095407968258003c010a402c6030b191000540d840703190710451900e0341c3c5e42c0c3c2c032010511102c000050010b02900740d032181c21400c0304a201a100c01d5983e00401c082d180c80e08008009200d11110741580b0460100c80756071911005002b03d80640a07e400241d854014840c00c9022001c5180140d03041724011034800b05004c003403481c4070100b80101d00800100b841c14444101d00200b1642100350f200c0d4030014281d00d0150501301440000c2c075a2404405280c40001c1c01005119090003041c3d041000300c005809080e00d01032016184a10540c0010244040480060f04607902035115100840d0068030fa903649a0721454694028600c10002e5030110302c050100c00342c80d500014020190a06110082040c8072131024142c1c1c2c0e06281080c3e141c1070f80610200811450 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 267533543 1250 267532293 267532313
    0x1412090313081c020c030d05090f1008040312060f03020919020a0203040501020c10050301031b090606050c060a0b03031c02090402040306020910020a0f020603061c0b01060e03060402090f13 83
    0x201900014101c00d104400500f00c180803031081250455100d90000121603501250b01a181179090034801c0e5907540c0c0d0400f04644c1c1200103600795200032890305083c007080e0071041ca18841c5200780c0e02c0e002c1c1e804001d00035200f02c40150003503200d032601c80401031006092810311517402500d03500740f0100c41c1000c1c0e07060000b40d0340586070603401a000442d0801107540c04210b003a85248085604011402400e20b00a0881c0414800a070521005000c4424608500754010000d041c1c118010700c13925448100c040c00070f90001c0c0400301d09104280002d1151085441140300c0c03820024061032420071500d04000c10f90030f0f462003404a0315400c1201007183d070744a2004000840c816a0003503140e032140c03030411000c82030602e02e800c1950000c0e1840d00c00100400c0c805a85284e044400c25180c1e2121000f00c1c00c03507150320800301124009503040d40184161118224100c865599032104952a540c05054a41c0340a4500a410100c5840071443c3c0c003425144040e400307507440b056a440842d187e107600d043c0d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 267534793 1250 267533543 267533549
    0x60d0603060c0e04050103080f130e07021b040504020a030201080a02251209210804091a09070201020c1203070c0c061206150c0210022406101412090313 67
    0x30b58074112010415000941e00501060407a030401042d80340d82c40744581031003032005000d80080300003048c001400803418a400a40550a0341550340d00e40710f540656a05040703111040d0402d44603852000c10701c0c040c040d1500c2507501412000c901461540107480b030110103030005221039002c1c0b1850103aa5120500303203550400d5003142095400890a280c1680c04224100008001c0491030030700086c25202101185001001004607404101d4140301a4034091130f0400c20f401ea00348101c058001d0364841004200110850f404405501c41c02c109030300302e20a02d0040384890304880803c0f150700091002a540c07280c46800c120940800c10f682e1002e40702c130240c2165012644042c403030101c1d08420b204000c06801c0e4000e4280c010f03210044050000c441041000344614286004254400d1082c860844100c000c03102c1070b41d9110038040c400d40710003011280c640c02480c280d4a404210340c0309007d08003d01800c00d040a20700035074003000003082d040003018102c841c40304002c0d141c50342d40544010001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 267536043 1250 267534793 267534803
    0x230a0b070609231b0402040b0c1f02031308180402030f07030c17010b03090c0301061401180302010801050d030507050d030603021c080301091a030118031704081206060d0603 76
    0x7002c805403401c0c030408212010301291091804030381064401001940034103948101458090fa452240009006881075400110303080c0d40114444080d1000090442c840182c15003800c0003e010ba110b40004a000848008240c500c030840d942c004110b065006000e0340d0300c00241080b08244900c085416a4810703150a2031070321000041000c01a03161161030b003034080c24070742212807241020318504050b406020340b140f811000804030708070100c20040040c8052001e0001d229690f903030a0808691012092800e021400449107111406014203a5000b6a54161034003901399003007000b8000c1041c40d070481141881001c02ca0030000c52002c02560142c07191950b0003107007603401c500c1130150a000e01ca00f044054107003181c1c818005400c3c041900d05544401030002282c04005024540360341141c078541e45c2651900c0d142120781e4102030352414942e070280e155018034070030309411804080c20485015200c240c051044094030f00c21007941c95000303400107012504040c844c500342c030100d45c640e9000b114 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 267537293 1250 267536043 267536051
    0x51510090b013e0607050703030b010e030f060603150f0114010c0614061804020904061a060408060711030301080d0806010e13050f06030c0112090203120c01050718230a0b0706 77
    0x814403010f1441c590403000500a410141130900001e0300764062240000c0904da12800100c04a074810f0096140400e401401c6903151500710017002e8454109540d0b660107802000c11182400c082e8450040c0111381c0d11440b19680da00c7e007454a81410381a01106040040074010740002c035050b8000c07074841c08035846443c43c02e0b040c100100038002c8086511a0308107041c40e802c0201603940e10b140c0d194000d0300010085110740c126000c03405445500c28030250701c80c40208012550b5440040d07402e200f00c0c0c894030780030140056400d0b80e42d900e000900c00e603100781d8046102000c50714425130000e604404d0604180c41d03181101000100801c40203120308040d80d90705e00810044041e5403a4040d00104181d01400348600c0d200300007042c60401c1444a405152500942021505d0402c20078030b140e0031088030b040d11401c0d0301c1d0840340648401d07600b14000450300c010030001d00203401c030110b048400e16a248000d1400700c21500c03034000442c42c00703680e108040400020f80d4403a640010060944103600c001 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 267538543 1250 267537293 267537377
    0x60f07110f0d090e010e0711030903031c0f0b06031812030a1407051303020d0f02030d050706060b03060a0e10050406080c01080a1506120b100903051510090b01 70
    0x7021102613502505400316600010000c404ca28200b964020080e468906514020740110034618841c1d04c08003502340c0f00004001c0c090301601c0321800b206110b0b0100a01500c00d044400f0000d82c0c1ca5854915807088040011030a40303000303176108014145041c019544160000e042c0e540494004440b03072485103894110b014403002d07040c00c949a01c06a1401c01d2410003207215102d503403000850000a000381d186034102014003106800710880d841c0c1c020101da59203100240c0041081d080031000b19015404c15001040d105c1e204d0080d40d200f898060101d00041e490070400305440c00015100844c1050300c01070104842d19035014070380140c08400c00074414038490304001061864002e05c0c10038100d260040c02c7c2e65983c2110203d50854540d8581318800d17002c104113000082680002c2c8a03400407103031b0250700a894005115004407401201a42d0078a1460342c90a410f0200c200c070300715001d0004280610190145a128000f050010702d400421804004c120002000c0007c841c0300305448807880c28 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 267539793 1250 267538543 267538547
    0xf0d09060603140f0f061807030807080421030203030c09011b031d0604051305040516030605010f170a1e0803150f10020703060b060c060703050103030e0a030203060f07110f0d 77
    0x200c5900c140000101030b0f80311202c0c2051b894074005070142d80582d01d1a486180300710b90401401020f50381110340c05035140704902c1c004515500c907200d801075a1180c40031035100b40350f442c1000c08416030940c02552465480055800260344610b017084d05003c254007802e051070003c240c2041c01e0f03d2113502c414250002c0d03a892a100d41c1c41c00100284a60002c210911440d02c1d02c00081d0700601e190400440c65840d240703440e03410003600c440c00240d00300c56518000b05020140e0401e45c1240c890f640f48000382030700c8001a80c800e01c0c1e481c1d050700725035002c0c0501800080c200281e0801003501e094030301c2c2840945590b0402c0c29401620350500401c0c04003201000751a0418410b412044201d405400b090744441d00030b5247e000303070700c4084c2210740d81d64803114131521650100c44021142c501610708615041401074002c05080c002600001d969500c90300ca2400c1101048050f243c009006240560311241da82d14810002083c100030001305210200002d481000f1014045000300b01401900c0388000c0c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 267541043 1250 267539793 267539803
    0x40501090507120302100504060e0604030e0f2e120c030609061e06030b0105070804090e0601140d170f0a0206010810021312050f060a02041701050702030f0d0906060314 74
    0x1280c0148095031180f00280d00043c011210403d145404a8250346a0070490000c040700c140d510407600615040100b016404440306007a000c08848000c40729942d081817150f180d400d85c0c44144118944680112020b03050f400c05030224202e8504800c0d0b0520b505403034000d8076410782610b4003003502c4072001d0102d00c10f0350040320054071464458200740480c80849544d10441403050205140e5109015000e591180044800117500095403695450b60b80310300000a080c1408960000e0181d90700210b00398030005c1640120402c020b010184441240d110001d01a003000901840c1e00c0080000c00d040f0704c0c50b18040c2031200c0e01030300980700c01d61404009500b0310460100c2907030551700c10011140311804038401d031800d84d070b000441401a08100d00e40103190544414001c5542d101d900200141000c4940040088c0c820340c0300c211a01d0308003081c5041c203a81f015525100503030414002d84104407690806401c1070505204003242c4c4910726180d00341101d54035082560035044041244281d1442044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 267542293 1250 267541043 267541049
    0x4030606080607021905011b0c0b1014010e04061e05090112120e0f09090d12090506060906060f0c07031205210a0e01060f0503070803030708220506040501090507 71
    0x8080c10030b9241c0960000c0d1640354a4016540c001d00045140090200035442034846800c1500844d0fa07c1960910140c0401540c0d1000c40b90005420001488003c0f07021180c0102e071706043c61050207028a200549840585061540d04075944840000d09407030009070b11a5030040780480040b1482c200000c3c01001d00058000c0d000744103151442c1c600003130046081115040c550716019100c40d010100241c1d60300c209c8616983d2000034035007840090728010691400f0a10551950100420042803c40680c0c99585010344150001400a000c0f4100415010341c040c5004200501e080032500c421003a513044044001046c2e40820410700c20003c0da8201c60044ca0700c1400c2c4181050410382d41c4140312101c050020100d9428640800d120f01c0158000c0c0080103011030017848225202c40d0300000d0b0580e2407041511a11901d6400200b402c00032044902071005039a47d0034565450b10361044071545201c6501c8138003020710541002083d8280310130b070b010754441c0c000030641c8816810010710b4503c50390 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 267543543 1250 267542293 267542309
    0x80a08091203010b030c0d0509010b0415050d0b060406030c030503030103120e0d0201030b031e16050406030c062f010c08010f060c2307030302030d06090203010b03040807020406081204030606 84
    0x1070040d0780c0001c151001d603811070301c4803a2416a260f0300c01e800004c090088100340403146003800180101c0358010342008130300400613030b0108000c0d6121403003207001d01385601c102c98004503d04505404190850502035203c0000350001ca0126035035905c044020402e54810760706c541000c4018010041d0b1195601a003049501c1c10050034402200050020403003c040241850f6440d1003150051701d00380502055040354030800d400060fa1515800e8860380203030603004c00c04d0001d2030007080340d1416128a03406d498001058000c03150424909a8400c0d5840441c800c01c0003d00c0d1403045005074100000c80d10781b15000000c40c0124511034090554401a0407400710403498100074016954030000403004c040e0028520700795001c010f02441c1c15801c0104040860340543c0c900070051540001c010900ca141126041068a6907280014204c4c042030144501304241000810045604400581112030000300001a015503502000c0d19100b10360440f032400c410f01107010818822144106c01c000d000c80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 267544793 1250 267543543 267543553
    0x150d051b07050f060f1b03041704260f060403080408070506010f0e0612030d110c0105070c020102060915060d02130609050a0e0102160303020f040b0a08101e030215090904080a0809 79
    0x16240c1d900b006d20348004400d0014201000003000d1011503c8603240b01c10840c0990b84da940c0d2101e600c140c10000401a03400e904062541d0101d40160000d2404480c4501e18040d200135102d6540440d0100005003081d515802c083c84500301080c424043d05000701600b050a08401d40f80546100210500900051003040380b100b4400c5a51804402c07510b0090809000003141802c0703400500050082c910407502c50742c64282006600d0740c000e012070f84100c1c001d8080303400564512080e1756032190340710620315580c0440780100e04d076400d203803400e503811601c010043d103036402025010f80c003152110340c4403c580341d4030340c0244409a0400c2c0b14560303039240d182d00290715110950081c86800c0300714010041c1016400600f034281740042c00305840140c2010381500e540c1b52011040181443e1095030070780e0314000d01c5900065072040070901c07040c5608244141c650711518540030801071920f00c10000d00919010040480300399120005035203e103200e200060f456000d00500100b00340c4009140080d80e82c05 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 267546043 1250 267544793 267544801
    0x85a090a0f080f16080d1508070504050703020c060424020406170711060f150d0201020606040908040801060602031b010b03060a090203070b030a0902030606150d051b07050f060f 78
    0x401140c00d05001e80002941d552006007188544951040280400d010200c3c0d503120b10401613a1802400d015074405014411040300084102c0c02031f80a2040b100c59a0189104004074100307a0415544040d081c2001810110007900c1d0900f0301000326400c4030072074980345205016003402e01821952a0360311008604060501d070000d0140d12503000d9103403401429000148506110b901403644548812040d26040d09044860711140c038415104424411030341c0740c400010f0304212840111042c0c059008156545a0005002c01400d03003c009403200302080101040c009001d004940080046600850740c1c1d44d69507040c282c0180006044000590401c400e00015640015400f80c10102d44c00002501ca640e5200103840d011035584004d101030300110030407000f68080e5100444142c0260191040d90303a41c1000c00c041c04800714100032a42400b8860798031155040d62107641d002c41450402020010304603102c252641200004491030781c8207083d20070304118240441500000d403059500780c01c3c14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 267547293 1250 267546043 267546053
    0x30106150504090b0a0305011104061b0807080306040f0510050f0402070f240c0c030f0822050c030f010b190807060c1b060e010f085a090a 61
    0xb15a2091540150712010b48840b141c0e1005144002158040000c008900240c0f00703000041c1c00510072400491000340d440c42200d501d62101500c4c00e94460f0243d403070000650703299000340c2c0025003415000b5a076031129952008880c450280207996040714007178542c1c508420880314140205c4024001d90050240c040021000120015156404000040c52058007900e25240120384400c60020b5820845a0004d40d9006004180450301a83d15800c42e2440c034a0143c0c3c03040ca05882c11075550f0104e129000f600985143d0000c560381c46400ac1d102601d645600003860560150404025a552074013003000c00e141a0a90350820a15512180540391410890765211801d0f0321841043c45a1200c6202c1000611103025840d4450010b512500360b07142e460041240c22180009401b2880a6245940490007400c0d95840351100302c42c80400304188100460b0004d82c004100320000d0241406d440c6006280300c1c5000d0754006466600380240c0f00988101e034003800151034071240d034100100d444c010503 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 267548543 1250 267547293 267547297
    0x705070306020f0c070320100807201b0a0e101a1909032310020702220207061109030d110f030c030403200604060e061b0c0301061505 59
    0x2a4110800588500480408003c00e210b1801d50303200c54000d0103400f00411118210421140094030440d002104200091104191f18400301e0b101065032540002d0342c040c8600740d400d4800c03c00c01e00e110440c400d0b0488441c42d00c900a000d452488007440c11124840c14088401c4004091116071150703e820201811441007605010324402e005100b84250400024801141d80c0e40c17201a40c03400d03041c80101d50040109126000c200c0318404001004400e4018800c84000c50f104504040c140d1210386e8111207009511958040380c021108800c0c0d103450710f8524021001c8104a144d0150342c51350b0507e420011180302408000c845142401580420703100058a094a440d05007030003a0304681c9202654a4401501c1000c44a8030000902c00c03048000030005e00110703442124840ba0f015441ca0804100519010025401c150203010801c500340c49140300d030705d5403040940803601d000a4800c06140c0514038402c10b0f412a48042800a9030707050034802e0000078054a20304081d01410090028054 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 267549793 1250 267548543 267548549
    0x2070206180109030f0f03020606010e300d080a06050307031a090a020a1202120714010f11060a0c0807080403050301152604051506010c0b09010e0a060204050f06070507 74
    0xe945041e42440640d01450030700e006190070200d0002c03104620f00e45600d5813088031601310010301070000820700f0355010b10f200c0010000c004200366072441c0e1101203100c541144501d00002d00ca0788041c1c0301d140390707030900200c04202140c0d5148145854074002c00310540d20b45501240c025400000d04201041032010b1550703170821460340ba400d0544038200700340d2902d0300524020354007400d24600021482d40004080d5030040c401d8a4081a95202010303241d00c0301d4543c8558007061200b49524009584100c200c1c3c4a43e01250400c660b40d0502756022502d0920b08a13801b9011b6552040380801c1250007864103984071030946001c51b028582541c00821601044c40b03040c3c03c9803404540c030b401d00340c020175404001020721800c080d112050806481342045c0252000e80e15402600410507101d07404d903031780e144140c41c1a120038005000c82d41d04c40c44030050040494009558030040284441414464203a503280500030240e00c99041604002020702c15581d114403500081240b400000c00c003260320812 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 267551043 1250 267549793 267549817
    0x50f0703030906080603010905010606020106060e0a031101080403020a0b130303050a05060f060c12030c0403060605010207031a0a140717070c021509150409020c0d031812050d060e06040f02070206 86
    0x2040d01c405e40030a02600401c00020015420b12902050107541540440e040b14003981d00d11500c200200c083c030081c1e01260001400c0e0040418040d0402d50160645030b411074800c1c41114201042600c4809001900781d51210443e0302001000080c140d26024481d000282c41c0420040c9080540000328014212000117000780004100c1c284094414404190450300003184666246041464140e159100b4002210013a15010303001c5403651001801c407086d268081ca4100b06c0202115240d10031580c014020300201d910b4080e104c450118088106020320710a46692150024540304090014001003030700c2c0c10050054170010160303980700101400004074040490f42e07060000041444100c21404418515600150029104220740d0003021040520000d41d100110283e0044043d00d0703441c2c03807a010300c40b0107560403808505846940d0840e4039050a0161601420381e4141094138003d50210103109140c1c001c000d5542441c5c080c0c280c5140e1500c00c214503184095000914901550080c010 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 267552293 1250 267551043 267551057
    0x30605091b0d0f0e15060604030807051c0f020c19030b15062a030711122b1b05210d1b170615070318030c03050f0703030906 55
    0x2031070301c5652045541c45a004070003404a101d4070b00c04000070340345940c02e0314528801c0c1844001d481e107618031500d00800300101298541880d603141c1c002103810008007a20907010760356601c65101c5601005499040c40c0341c0310701c0340305800300c3c00c0603040280025203039008820070740c00004920100c3c41400c0c00c0e01d500c400c4002c10ba8403092107031042800d5450f905600000700090f2049414062a02803400300341d20070710b00d4103401c03180d8001c9841c0d000742c1000820b20742d40224541094038000030300c907014034041000c8692003e00f02e000e9081e00311010b103e08045005e4043d203107920a52040424060b2401180004900b403490b69543d640c07000040e172078001c0114400c00f06d04005110508a42100701509014004806000c00c0ac01141e80c002142d040800e58001c0303488800340307152560b248540801482198013121000355050198841001141084410580702102d5030500a07494003540c040c2c4001c0c1d4841e415460014034029060103850560390041504100195000d05034005558651400c04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 267553543 1250 267552293 267552331
    0x6060905310302030706050c0c1606050901050a1110050a06080c03120702150a030203101202030c0402031902070b1608150f010c0f120e06040302090c07021504180c03060509 76
    0x741103014605001b030150741818203002030384100300040c1c001240fa81055035680b42c050643e285800e40c0a21903040411000d0114554960103080900341c918501d05001214011a000c0e05041c01036103400140c500365a90140408121544102c0e0080c180304001410301c2010100002c0c0d44000d041c801402c6560005008030464484001103803120010080e02c0761a0542c082d00940a5081110760303201e600c40030440000c0070603880307120340e0704240c0240142c416902c1800034480a54401401c0c0116641074115058003c0d803244003c09a1502030700340203c29003084c6003c00506507000d0b1540041103800c0c000e0007480a02da5101c118000000c5030b05c81d440c2c080071130042e180500c03c03440240c00c054440c010501071180e01280b0851040e200ea55101d60000e40720200000742c0103500010b50030010b000006440c9030703e8040141004e0307000910006206007507100598541d8066080408107480c0d020f075410020080d03004002e014002c0303042c01c0c001c1500302400314000c1040208a0007500314484407031 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 267554793 1250 267553543 267553547
    0x1050d061404060c030b1509010c08041a130e040c0902090f10080702012d0506030304030c0609090b0406231323010e07022d0604060609053103 63
    0x704011101d40d070224101d2034281040710040c12001400c0380800c2c00d1980188407880c01c000d2144078000e40041c49400d002c0c81c24011282140c031248101e0b25048200008500c03140d1003c1c0e40c4030f000c000140819030324400000410401040d0354450f031300c0300ca814030520002410030880e01080ea81074640060700c8080920005030311010800820340c10490706040f1003282036000d4000c52040e0419002481030b48881e144000112503514440c41b189200718080261407205504200e4011200070116810075469484445032500c503070b8000004030700071403030810026005000c1c01c002c000c000c81b01000282d240c141d00c2c40d86a0004451400c0d41240e00060220329030300c2600070000f448400400300844980f1000020f02c1008081c4145005501c91000044801414000d244103580d0745d4040c100e2010620502d013021048402604e911684040c00e443c4400002c2000714802c1d070040c100070413090700d000041c2089800281002c80c1c100d564582c0001c1130800f5589032003071940b48006040c0c11540605003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 267556043 1250 267554793 267554801
    0x30c071203090b03191802060307031535030f0d020309100e10060503030c210403050f060711010c0e220603080301080d0507120509130213030618030801050d06 70
    0x30107080f200c804800d001402d01d045150422560580ca400c005c0502e403040c000103140080c040096101100300300144149120340c00c48181103c03510103607540070b0740704d00c410b1010071009032102e01c2d4005902050300b0810b0441100700742401e6824003071403a01d03501d40c0d1b1904591240000880b8030540000c04501c14072410008811074500c110020411000c2c08160103448044900c03c582d01c40b802e16101013802d1401004480001e80c1c0c0c1402801c01c442c080c160310041c081200d1480d8140417061000002148081c04180700780000301018001c2c5290540c0301900075030076081c586040c0c0e0324101d50500b00e145c01c0004103c844030112407040380c42d035021040c0c412800754a809200300b0350806030000100542c400140d81a51500801c0d1703030381e28010071030440c3c0300d00842d503000d410413200c800c0c0690300d1800b030307c01855581c41c060294001904030900701401d0764041c0000811441401d9020410701416104004501802518038440c80c481e17514020b00ca9803060041c5440f4001c0c8000440c100701280d44 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 267557293 1250 267556043 267556049
    0x111801060f050f180f041a04050603010605090903090a0608060108071215060206040210031104030b060607020d03020c10020d140c010e010c09090605100f030b030a170702040e030c07120309 83
    0x740981d0384007440c000d04502c0354840003199004a01494081c1c65600e0640030380040d9511114035981683d0211f403c0001824000d8052509956901004180d9031030340e8508910800d610b10042d0740d0742c0c06400074840308003c1a40003500b0040c1e040c040c0440e5030390004801790090164a062065056903400000050070384241038214074081c50300000b00310b500440c81d43c1c07180380200c505448070b906409090f4152212a6101d11299804200500008882141c070a40003c0003510741400c0c41c60a0b4040354007500711150070b601580c0031070048030091400f49600840010b00c2d201034510310b0350400000d040b040b8040001262608080b0340064414802d50103c00b200350004001d001d108500d41000d0204a698004c2c9a0001e00304180482c0909082641c81100003840d641d20881e00004d1500320000d00341d42074682d07414000e209a020100700c8002c3d10386a450440c2140316070394180c0c3d00c10082111512581003085030018000c9181c906404a40c413001c6440640202d081c003201858200c82c90400c0390 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 267558543 1250 267557293 267557317
    0x20d11090106030608010509191203020708040b07140a120c080d02070b1801020c07120807021207140109030c030201081003060c030603030f050c060612010e19111801060f05 76
    0x2000001c40c0b543c580c1000e022550135200070840e5446014850f80c80d03a040d25003600c40c92400c2e10101c0000b80311100c004414080750b02d801420031019641d081025403003a0300c003c100c104080b680500b4015542403010800e0721180041006188a5544003901090107a02d04148002d140350582805001802c80d4607030480484215590302c5945400c217010501503c001d9090260b11901c5c1d6460801482100c0218521a000b80070107840c02001410b024803200301200d40c440141f11000050311394448000800c0d40072005088454101804011158030b40f1610f40e0400410701c0702040407803040d820501c10303660280383c0b20402e075960f03119080d500d0501c1c0e0f100504c1c0d140740180350042640e1503440b03242a24840c0d5250f1708641c0071010300301c6180c0191918048150080c0010a8052034030385807804140c0b0000001041c14011180030b03d0800c100c209070302c05881c00700d20106041111004200083c010100c44542612a00b201031b1455040d050054409109110890350f016030b008006984000c2a01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 267559793 1250 267558543 267558559
    0x30622090b0c070c080703030206221a0103060b01090b030a0504061b0305060a0905041a0907051522060203070b090c0904030f02010c14270621060307050d020d11 71
    0x2d4099040c0d40800742c180e5100a00301070100d8802d101094050440760954028400c0d500c4030325000c95190384060150300101c0e2120603843c00141d80001c0f64510300450102c171100c40d80b6504200094a1245441904121022400340000081c0e4001d681d046421040c0002d07441d961880c1810041c1480c11602c2c0007441310340803010100c0e503d90841c5111b4042500d981542940c0c8a80c8481a00c40c29100100310551341b0000020244847d2040d903808034812040361107140c1c0d200081004044c0803014031a0b140d0000400c51213008103185260710501e80e03118415131040c41d00e04029100c1c0509c4d04001c0103005110007180c0714007020001d21038088801400801c084c00d00d440e0103001300c800440418003550030820b003400040d0152402c070340d8042c0c0c1c0700c0340c1c2c615254600305c208201f0303010b07080400c202069900400104c2e4030b8035000342540c0c02c01c08101110200c029164101001c8009010511a40c419801070059844012483c1c500640c11b03100030550b4905440e140c688140104035458100c041 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 267561043 1250 267559793 267559801
    0x9090b030712051609090b0708100f0b0c06060d050307171c020d0f0c020c190803181c020102030d09020f040e010b0a0e010b0901110f1f06060203030622090b 69
    0xf02044501c941070700c20850340c4141c1ea40b0403211040e00e11072071014086c2c503043c0d07000443c424002c01a41c0d90019000c0d405c906400e07101c1c1c0700d0043c503501c650030082040c103010070383d0b50b0022000c20000350003c40c00c8480340e50014059442650306e00c50a500200501c42c400006546410b4a006a0b1000c58019501d80b01103100d84040c60025000901c51014240c18101e027440c91004612409501c1443d0343c1c050800340315424280a110300d201003001c0c25807207840c42d00050614062001e000580c0d003003500d000f12403a960040111110aa085a91100d9880e01c03a410040c1c0e0000100e441422060f180403e0440c41800000c000d403600354440380e0490306114120320040c0040d4400d51460320101c81c4c00046940390301d03000c20603403003d000b840c0500c042040740b039506d58000c161403034030030b00c41c42d0880707600b40015400c0707074101700304040042c446410400720000d40d202d07039010b02c401820303071840110304510701240051100d1079400c451981c4442803501c012042a5a90010440c69400402068039414 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 267562293 1250 267561043 267561053
    0x319080403092c0712050f0108071502070501140c0303040c090f0207030c08030a020405190305010c050a0e010e0a05041107061104030f2a08010504030f030b0109090b030712 76
    0x41140c0440014920100105400c48900c02810540051510801c3e4106058040110109001e40004144040e1805003c044400d6002d554071800c00321840400a514083c0e0071031030201d80307400100b1801c0140e400d482019a00041c3c2c0350031202c003481c00c0d165010380d901b041d0040d407140c4101141d280c00004100030a10408091900845440e6941048540c01341c0e081c040032030103a04002030010344d82c44250000b245440003e03540061a04000519083c0d494000461400501400f0a03160b084440c04005002080c41403d02e51541802c03c01c0c5811072501009015101c0c180e111130600510014022050715440903072405442d01400c100002111100700e9006508080c0040324968142410304240740000f1b420b8500f100d5000d0080c1088909503076800c0c10440c20343e04043c01042c0d00f032404085010308461103d0007417003400000183c9051508000701201150a000820315041c21454005e5036031002c01074044411840300007902440080000f420201140d00c003880d58151b5101c1101800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 267563543 1250 267562293 267562307
    0x70206031f09061d100501050f0d0b030109050a11010906270b040803070c0812091215040303020d0b040b0906040905150901021c0b01080a090f02030a06050105040e210a020319 77
    0xa12400c20504c507960f44040038414120680900c0e800910240000041da12550b806006162a03080380481d0741c41c241401700e821030300340400541c2c02c0c0e8403420700308082c882d100001e5605c0300800e182202c00c460505c10044c10194894118005c242d88000e081c40008110380101006400b8040315130350f545650300720842d03480d04004015102c0340c608050008103a500051810101c8580941c61800c00c01200f007080b29141c0d40b00504045400b852045004a401550106201e00e02c603440060309ca911981410007100c00e10880c541c080ca01c2c7c02080d111942d100d01146600180232180800c9400071450101c0c108045480c0c0110034412800c01e000034068103401074410300b581d502c1c96004a5001d0202c40d001e0382c0003031400c14042420304000c80d042a0f95a04131203034040c01518000304050380c60380864039141c040f20050380c0403950381006015034981802a410503046820003490404100e58030102d9155041ca01409800000140401458001c0c41601d0340c0402d0898240c000082011026000f0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 267564793 1250 267563543 267563579
    0x3061801140a050111070e060a0909051506032e02120c071b241e030b030708030702011e11060705030a0506090c090405040309090204140a0902070206031f0906 70
    0x3100310b8078001c1081d51041c0540e081180196005019440c5000c280624217070019000f10f8000440c04000b00e2400202d0142110040c0319100030f11100e880760b110005219400b400d224407030f411001e1044141032085070703442011800c258000e4906801c1605410091007030b2401401d861000c00c0410082a201d40e0113844c045010b00c1500c42d100545c00d04040d03180301d082c0910340c0c034040f0820344251840d10211960140404504001d90700a840504211000094106090010b81c64882e00c448500701030008a0051880c0c83c021414525aa80080d0085a100e20801c0f80c200f10040c401008a102c0c00b00d6981000c1002d007a5041c500303190400500c2a0700480c1d80c0c001850802000c1005810b10444044c0320307020701010242805290700c2084041e18000c4c0042d810040d19060200f0420481d100901c02400084944071400003280c0074408140d5907640194250743c414422280036807542d42c11240e221403d1485040c0c240310801c01443d408415401462442d80380c490086451b0b11021850030403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 267566043 1250 267564793 267564799
    0x14070b060415081e0613080a0507060f0f0606020c01090b0306040209040e0a03020606010c031e0e03030a020d03050609010e01030b0a0f1b1e12180210050a0f0c050a080306180114 78
    0x110700340c80704c0e450b500c03a0f06898174440c19010a42d6103003c02c03007010143c4414a45480d201e841c00b00c1c26185d51099903003088503410807998803600309082c002140f04502c01440180082c0000c4000d0303c0000c1d00c001c00301d10607075000035000000964030703641d250304840340803800800070420703600e02c1c00c085e40c0d1301d900e41003085002d845508042295503009041c5024507651540c4c1700351010324400c0000c010b038031584c3da20b0801d010b1409014101030b9018806040000e81d01d900034070b1800030010000b8203445003e402d040c01110345000521210607260000c40c1900d40103108122652900c2000c0e0006041784880900e0103441c00c80c0f62000c655000c203400415440700d66445401040c100d4500c03c902c01003403502000b00c0c00822103002400c41b00d41003001c04405a250f0141d0588940e008900402c085289005c0040e0700050200100c076004011441210301e40c0c40c01000440490341e80039610b600c41c50002d81540c0707011002403055540c900c40301c01d481000d0080b112341940d6800407913485030920180071f44 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 267567293 1250 267566043 267566083
    0x105071404051003091b03051f0203090a1b0906031a0702030c060402010f20030403030801060206040c05091b070b060108010b0708030a0506150a0908010c14070b06041508 75
    0x2201214001d607015140010401c84000c0103180080e401003001820880d159000503240d984c402d0f03940c0c91003000035170240300030308154404405800b6450446495200c903091060061124000c400644e4106403030b44a00c0c2c000140c0d40440e500d07506c1404a600062045042090200c10810000040d00742090318501203801c2c1c3d00d82c880142e0300d030b00602c00b895a11385c0c49280000d01542c401c2c030440b4251143c50400060300015590196400c12400c4580d2182d42e00000341001003550042400c0d005240c0c502c0604041e04040d80c4100c0100114805d2034030406c05e48011452030311140402e55000d0090910043e55200149043c0d40130060491320310707000c9a00d0f4000016240468400c03180c1899000c0e050368516581e016003c001010050a00380d0481642e50304501c691000300024081e04001d030719514089071a003800c245c2511076401d01e01c1d0400013520151640301407400c0a0710b40f000c2d03000c00307400ca599a030b20f1b010030020007085c000e9004d024460b0384001003011001c20050290b40410030410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 267568543 1250 267567293 267567317
    0x109030c060302041d24040204090f1d010903020703120203040f08160504061202060c0106080303040305040e0c2b091209050a0b090904080a0c0602030a0c0e0d05060114041d010507 79
    0x380c3c0c2a801112110212080303085c0d60006100d540e0901c00456070700400042c14034ad100c015400840d0031038603011904558038400a142000e444035003450780b00140c0d0090029840940e0000c0d16030806120041041c81c40e14520b1880c107001b803081d1800380c840b00b640002110360340d0060740d030f071b481149091440d5103040f450301181508160264105564a038400003174070880590921010345d005030361603d265582c88502050090b024401180214080c5c0d41b07082c0c80e80e04290764807002c00720252207496040f40400c599070020308018003a800074502c15510182d0040c2d4074210034040c02410750010300c01203204102c035501300d40020b5904240c6200740c40c0b0f80340312501c1e0842c44000744903005001c1d501815820004001031a044000c041248040c64500207030a880d0f81e80b101a40c100b5070304d50303440c80e40380c05100391481d5114000071004032040b02c501540c1e1406442c1d5540307502041c00350840112000340c1034003250710380c0c2d001025601c4202126001d90328850405c540200400c1d602000007401120b000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 267569793 1250 267568543 267568589
    0x50a030c05073c2301050408060f0405100e0613020d050a030305090c06040803090625050706110c010f08070c02031b0f0607030e0108040f120e090711060f04020109030c06030204 78
    0x140709403108104095031060130350080515904185410a04001d0100030109943e40180902809044a502450b400341041c1c9407460501c1c00c03a00051000e0742c6820260202c40b400000e40c9508241100c0c080d101405803800451007030403990f10b002d8207038403500880d0750070150305510041c4140c00001c11341c1c1f0288030020400c045840740f842002e000d40d01c140071a141c5450084001d00c1004990b12a0609030581e111410300458003c0c4419a4180c0044c20208811504140010800300910029061800c10080080c0440e52400c0001d13040003500d2001404140c0521300600ba1150010300f1034541c0c03440b110162550003d6240450700460102d180103d960a00400340e910507685500c501440c41c14220044903100c50090003030f1070303610440108002158803005002e400c03c406540d0455100c1c01132080c008101000b410680401c28400c42001e1400d9000c9101c0303402c0341d0541d02c5003c3c5510703a0300049400340215040940440c01002c0001030081e0580e0050003107802522402202485413600 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 267571043 1250 267569793 267569909
    0x1302180619050f060f12010f060207090207021f0e0d0807110108010b030a051017060f0601050f07060902030a02030f06090c01030915090c030803090a02040b04020403050a030c0507 79
    0x18480c0c01003140d0441c00398070315000e0060907500d85c1c540455824400d80c070b50b02030301c00b120a031b20103a804110740800344100f607810701042c00a404074001c203616100b0554040303205017040e009000742811600c0038142c14284180040585100300030f001500b10700860900f0781c803a51000d4000c0762194544540d40303145502824030302d81240c04070030705e00303045544518190010300380041480c21541a9040c0109030360003a4500c0044143c0004000c2c142841c01e0001a04100c40261007681070003014081606a030305001d04542e00350341d0115000c01c1c0c2c1c819901c0800c2c40c0ca0b1800350000e600d405114010340004000194451150a182040b100c110360380d0302c015011120420006803a08422108602e145601d9030812100948526111105140d4075100c04103160404e44d4440c3e16600310300f441c601585014041c0c014119021141180b1b054615554107a56645240e001024013070056205070500105000d070310300800c00242e5440d56104040b03100d032100c50450f42d082c480561598000750843d480061 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 267572293 1250 267571043 267571049
    0x30f0e0604051513050709020403060f0603020a05041a0a08010209030d050a080726040803070f17040b0709080a15050c1201060806030a301806081302180619 69
    0x141c0f2148910003008807200d10014542d915540b00d1011007000074034100604001886528001070715203065140850a03a180301060384d2406042c42c50500c0582d88145102e0100c400481c0c0c0018030415001030042408001081568030806980000a4039030b010740041c599044100c00f900d603e02e0b44848152000c0c022140720100203407a000c000b40020f409589010400201c91b036941c442c0340b285422079004200d0495046540c108007100b801100368114887c6c030132a030310314107202910300c007511042d50009000610207444059104003003896540189a010060040701c0191840c1101f1402d0260920700d00841c007000146c9440001030b507042c1588141e40824208030f2040005900c0c1610403524198058501503141c0120f00590300090300c00c80014a02c61031810669070424615000e49151401001d20b003010300c1b020340404c50034852070404038000d5408508000a040e2a4600030b030503000304141c0001d41180d07400112801612080e21180d00c190700440c0e00501480404007a202480340b644 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 267573543 1250 267572293 267572303
    0xb0a0b0304120507020603040c06020d0f05070605060a0305032209050c0a030e1212090d0302040305070915090e060a050108030c1f0902033009010807030f090c06030f0e0604 76
    0x210110300065a6044082409641483d00c2c07800c0245980000702d1700e920540d01120b10500d0329504105081d0103000044551000742020402044000400b80c61841030f500010110b5680c3c0000690a0765200b9000c07000d503801c0b404480e01d44100040e0741810100f000030817000c0600a00e000a1000300a02895100780e240071151170401c420803000f0f4000d0140e0f04a184203501030401c480400528090140000c080d0004c0c2c400c00e5802d0044416007418418404d0b40f0170103004000c14030200300c0024a407400c40b0802d0a001484200c069400d001d0744660750000b042c16400c0031300e00c0c480d003400060745c1806800c0c003c108102907603803481050790f82d10552400b01031682081c0c03a072100c80e090b40c8402c0039200c448048045140c0b182540080d040580f5203040781c5061003900070268100c084400b03c0303450100580d0901d0300c0c052090001074480c2000824003410192180717107110780c1410030f800c9007201035440b507000040c99031140405000b0b4503001e40e00e100d4403450240c0101c0c21942c0020361a008070342103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 267574793 1250 267573543 267573547
    0x100807080123070e04020c0d11030705061b040308070c0513061a0d0f020a0503010e07030b030a320106060e030604111c052505030d0e130f0e070305010b0a0b 69
    0x40c00d0741d882c010081c5a10300707206003460802c11503192400200b21130380244c07024107041d81c13010101401c0a1603102024000780d00c20701900d00050300000c1c025421403600314580542c1801501500102d10945d04028078030140801c1d180704003d0094004010740b4022525480410041d02c98801160403902c2401c400c0190403042e2120040d6100003003254108100001c60340a50000402069a003c01c003603000243c0000010007003e10104c403000c1e0030405038a0f090200c0092080065035903200c2c20f1000e080384207083c4005000c0c4550401c014450030802c42c003c1341c00c0c00d01c012003034001c00c400e2081c070340441d01f8060003071040e18000c46c1076403040780c0c070083d45c580354600c001c10f10400c0e02c601c1140c0e0350701010030001c0c000414001c01844c2a003600f55520744020040208400044091a502c10303800307580400d00700f43d2015048825407280d8081a42c00e9504050f148040070041e10b4000304004c0d8007450130114984880d808214107041d00d000324028008201004c09001420340c2d540305500c408075017 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 267576043 1250 267574793 267574841
    0x1005090c0a0306020a0504050a0b09010311070f06022a07030210050a05041206090b0405060402010e1509121603031709060c1b16120c0608070f05070203070e1008070801 74
    0x19136018050031040d9203050390403d6200d101003020089540c0000707503424000705280d078456906000352901503c076031903813a040c205a9980c02e01d11030702c481401003030707030360003241e4221400c900c0070032080c10310504110f80340c880020800d01603c070b6400d0f000a071b00441100c04410402402034084503070b03444443d41c41c14a0076180c140c40307492181f031101e801c90300030742c58050031030103e100d443c036240c0210f000ea00540094186032002410501141c00d40c680100c1200c0504220010603074240c0c4ca07000b20640300001c0010100c444582808070641c040b01c5884103c1802000749588040503d81d102041c802c55019615003062003a83c5107000c403211100190104410125881600041c4000c10b80301c00845042c4000161a11100d01080c4c002b80c4080e03000d180b481c01400301200c05540100024142003a4600f0650401000110105084000d001d80025150115201000240300421200360161040c0c10400c1c0c4a61a46100380b04131002842501c00100b5502010f10640007031111110120b141380e80 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 267577293 1250 267576043 267576053
    0x1f0501080c0409091e03090f080c0a030201030902010c0203060a0b04051f060c03090b1801021b0906040e0f070603020901080703061508090f061614040509280e1005090c0a03 76
    0x41324121808a6031103200d0b42c0454090070034074000d034803e44800c0000c40c100041c00036103000c1e60344104032903031000c0700b01500c2d920b40420100643e0780a20780810900c81900040c2c0c3d0013000950b009401d40704180c1040019004c43d4420131400c0011030702440766899000d10803000004001524010300c1e400b80c01084424024500700308158482e01700681d007142d407114808483d40000b8901c40a0500e20740c0004c00700d6a050240d408110780034049080b01d14080700218054003001080c039409503541d1559414443c1c070030403505a24035903010407035040315200c601c0103010390006034145001c91a4000405c0c400c0e4028010002511842c041108d038034500300c1000c503055200035202803481c2c002e01c4100c010200c810b0004520a0000c2c00441c079140c981c1c802c0c01003c809802410502d02d5400b444144104d07500d003a40d007900b03e4402901243c0311740d5141840b5a003000046006481da500d800c0e041c094100c1d01003281603051b108d00300c00f0060b0b541c030800e820752582014003042c0e40c840440c84060000038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 267578543 1250 267577293 267577301
    0x5070c050d051212060a0e0f06010f0c08040801020726160206070b0403021e01200a0e0904030809071517100b0403050601090f090c06030b15031f0501080c0409 70
    0x25004008850f0364a011480c901c20f554000900582c802c400d00701040b00504128243d1001446280d83c43d000fa85001251101000b401411441c100a0054400100c0c03034883c460192989400c085c880c1c4d43e603075035840106c1c003d40c0500780881c0c200e0131145005105031520801035800d0249030580c2450709501c144d05070005c808040c01280e001c1000d00c462004034041d980100d10aa04c03036001400c40302d0001c40030f0f20f080c200100030f81c04681e051a4036010712513005142441c10300e4030b140c0d81036210040240140c072205074511035143c00c1a642c00420080c154000c03100c500070030261040e1801981c54801c00d20341d044c0d0700c801001c0860352a561095210709000f054952103030b000001f210f8116114910400c05611551098990b82d01c8400103000300095803040490f00380070400300300080300c0b441d55512651449846030501340b6a40e0064804d0b1030711240444c00f204038500c1f901c141c1d21f0cc0c11035580107403840408002c0703010380c004a401041c6540110080d0340210710854210b404c1c58500100d40001e4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 267579793 1250 267578543 267578569
    0x122d040906060816050c150403050f0417122704020c030f1804090305090609031006090f0f0b09010308130b040f06110106050a140411180306070c03090e2208091005070c05 75
    0xc40c080005c0505048c000c1c1c040c101410001e007003541e10710dc01c10901c1d490000d4108144c41a00e40410800008100c100c0700015403c08070b8200e052220b00c1280040e000340500da07030389091800001040e00b8103800c1c0b0001000c4204042c0c0c0003185103a24130044c4000c56155442c020089070080084900c249000380c064880303400001c003150850201405d03c174080e00c2403035000410598451861002c08452400346c0111610710002c200841603d10703000500650042c8009003000400141c4601840145600180501159400f4582d03450b581c0e081d180c14403207540720f09400292505640744a04406014203c211940201083e40031410182d812208a4a61060b039610035500c1c0c1e8520000000b080181500900c1c0c079071102111442d2000341810f1410040510003000544007508000a401c0900e50080d6580701000310580e40e548070420600c80d080c81d40001490034900106010051008024a1605030948000904004800e03040d034540c02104001401020021428440360a02845e04209 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 267581043 1250 267579793 267579797
    0x6020d1b02030f010c030c271401051b060103020103050106110703020f0a080703140c1f03050601110303041401061502100b01021f05010305122d040906060816050c150403 75
    0x40b615403c883c2d00311085c402404003ca074864642240041d0451303462401f043c400307200c0741c545106450921200902c9406034103050b40c1a90045191a40b080d01a200200b552841e9850255450501a0742d2224248822400a400c200000c90558130840000003032003800f00c01018600c0c11a42000b1503880e034003c0c915040034602c41c0c0000d07000c2080021000440c001c1d103696629490b28500300d8148070b448a9002d01908074811480e43c0410b407140c40062160007841c00241c503458480040380e03000e20341d160680303880c44080180310a0001000d5141d0305200010000c0014503900e0103070b1494120030098100150b085034840c10310b4140710b5001200d80d0302c81481901c0455040d01c40c506251580b41d0300031ba1206943e0340041c42080010808200600098140b55091900d41041c0e848860012004008803900c5450f000c6100c60185042d41c1c00b408400805000b42c54895000420501088807030f031850541c610400d00d030ba140204101c8078a68001405841c4202032290103116080c40038004400b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 267582293 1250 267581043 267581053
    0x201020d0c08010f060305070c030e03100c0f1101110f03040c120302031b0304050a090f0f18030311130b0f160309090b090105130917030f1006020d1b0203 68
    0x106010151061014034003468a0385002d5504020003a822050b880d000801403600c0d00c0c1c1070020036604009041c11081d0715180452401c4034032408a401e1402900184119a0520050584054004081807802c50301540c5580320090144103040c00d03504110420314681c142000741e03400c51500301000f1907010f4011059011855600c42c4c000700510b062590035801a0408500007d070200d800407030195030000ca100950415040c040041c000032964400c041d131646d0b0307485003130342d14545c503801250b47c084445104004c18a882000000721401c0540124000f81ca08045811140c605100b95200101d403000085611814181411044d0348000a401903d40e014042910400100d1408124041c440e558107070312203241c04140002e5500d200080c603c40e00c0704100510591b1181040c04071107001001011411012074101a61480103181800701d04140000401c10500e00d45552280a02d05c000f4003403003925584c8108036141c2199207c3c0900095001028506030502e08411608050006003607507 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 267583543 1250 267582293 267582307
    0xf1d100909020120061605040806060f0f0d110a051509040b03120d0903080129090a090603060914060412081504020a022a010503160c0b07020105090d1d0d03020102 72
    0xb00340b02181030100703134a60701040821201c00104039081c1d55116403824494100f80c18441c02c0381d22940028040e501409070f030718800e1981c0d034801160006940b0058100819181181045911141070502040c00b5032a51400040d59091048200380e0403030100b6680341c145400ca1003040050400b88a01d207515100728032256075102540c1cbd005001c220b10348640081c00c05118640546981c0d8160b101c1c0307081480003016080300e9600c031f02504002d42240040c05a82c3c81004000409116031038000d20071091425101004110f80ca62181462500078182c0c2824907841524041d034039081110010320302e4482d2001c05000354010561140c00c0000204450012081030002c1001c9820080d800323001a448601d0408100a803120000003800c46403a180012900c810004cc100e440040c00c51814480341c007000303800907407184001c1c1354035561004d02d03803655080c00d2000901034036050b100d005a0707000b01001c004445004001d140040e0442c6000030b2414510703e403c204003889844026825035400700101 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 267584793 1250 267583543 267583577
    0x9030a0f0f05030f03070806011106061201020408070801020d050c07030c11030a02060d051005060906120c1306020a1b261c0306030510110405090705040b040f1d1009090201 76
    0x680300c04081d602e0429281d06d0301500081180d5400780050381488041d5007c10f40000f0041103a13a803110068410880600683d03070450300922a5901a460a0280d01c002141b001c40c10340040c0104064000144101d84803601000741e18460110002c0c04903504039469400a01c18294440200500600381d980405654001c5090707503005205041c005d0b80d840040000b10307809a910000904000d440766400c000a400c003041083c81803407580310b400b105040000368a8072040d000c91780c00003503100c0ea6020003541c4080295942c540310200b140e140384003405c44036010302003c0c0c03840c046503459100c10f040c0307420590150008803a24002e401c02401a40e141d10b100075000070300d1211251f0199800030301c9034a14245a03080c80d0b0450210980340303041600030560b4203201d8050710155034044810b2000d030f4a61420555061050341e114405050010030005268011f907100c4101300c46041202c190580d803400340d030038070540e02103400e0b82200c19142001e110210b812381c4451692407040c180075441c6000a050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 267586043 1250 267584793 267584797
    0x111100c0c021207080d0509030c1207080607030c0507060b060d0923030702092d040b07030513020306040605100f0f060e0303030f0c03100306021902070b09030a0f0f0503 75
    0x5604082150700107032404606160140c4900d0381c00c0d44015200e080d0500c2100c0342c075010120841030800801054088880c0d0301031204400c80d4400400f0306a0f400400c03882030f62192003510401c0d0103801844001030085009004400f0a11001d0707843c3d9180a642c2c1d41d4100050000303842c3d40f07070000e9050040011240c23451181400381d41c000d040001c1040d0700076000c80c0c41e0b110441ca0103d40c40d0400d20561005854152555410074000070b000c44683d00d40f410b138041c0d407020010350656003210800911007401300c141005030240c1c401d13540600103a51008486805407000102c001c0d010350161300050003044403544000e80102c2c0401c103a6121a030b4401c0040750104603900b0180400e646801c0070407c80781c00600c0c3e903c1c81c040036070266007146481d50b14001000001001e40d170801d84c00000140c00561004c500c90091580090b0440d2594807514280c5081441c40e410140036100d11000402c4001185042e500302c075a000b8010011129140c5da44007142d031540104481e83d120b18405030001030070900c0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 267587293 1250 267586043 267586061
    0xc0c1203092d0503193e01091202090714090402070623060a030609051033082817031b180f0307030209130318060c02011110 55
    0x800c41d148074444060010810203035000c40e209610041030844510a02102a0321103a04424044d5003000e0071044a184181c1000d04044405281002141b503084035011035210600207a031036818207610341d81d26081545000c1806540207052100050f1140e115610410180d140565074504040415000c0b4007660850138045801a4450303854004048440702401811003003024420294249070700410040100360001512554032240d04805010080000c800b051140c402d040101c02c0d031002011004a42c0c80c081090603094400610000c0c0700649a03c00a03920302d000a4903041c0c480c8440f40000360300801124401c2858841181e0204001130007071041c0070408004180e580c540041c2c0100c0340e4480420041c80030a050104410808031900030005200c0180d4546490030808c0000900d04116544020350043c1e07250200982d5980c00380010891501c00d407503c2c0ca10003000554165070a4041c044c100000340c0c62580007003d507104d125901410130f0080240c4048007a95448203040e81d032000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 267588543 1250 267587293 267587339
    0xa090203030f0c0f1b0d06090c0b0304031710060c020102070305120301290313080c1006050102010b0102011b080403110f07180507140c01020c0303010905090d0c0c120309 75
    0x2040f0844a01d10070303c0608003042c0941e02810b030740c03031048903004102003200f44428002d661040310041041404d0b800014940d41040286822566401c0600843e41c800c40e421400280210b04070007442c1d0184050b6400740b00302480c040310090804c0000c4418822003141681148100440040810f1052160000120318000c0f1580d6a6051804260010b10381c0000c0080743c3d00340214407a41411810141c2e900714484048420401806040c002100e0103001103083e0940502d42060940500503440b030340441d6000c7e002844106c407a10f0040e4200d80c08602c1209201c0d8046041d602428440e0a195a02034400c6c00d00420812100d2101d625200035004070079820362002406105012020700c941d020300c00103074001d1009140030b500040c04002142d01074011000c0108492001d048290145c61700800650b0843c1d03101d682d41c6040c0d030041d03c8261004241d0f4042e03503007000c2d40c0b60f00c40c0702c01e0941c080d00034040d190b61928107010348030800f00c001c070b050381005503494011940c5c0c2070004218814402c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 267589793 1250 267588543 267588547
    0x1e0f0501090501060b0703020304060305100b1201050310090c0909060905030d06030c0b0403080d0905070503010906060f080601050a0e09010b12030901120b28030606060504031104050c0306090a090203030f 90
    0x42d140c03250840d040c070380050076140c00920244000960000403207050301c0c1d1624000c20980c0b180711a8080e038a440c0d4001c4403056402180303004030402c10081c2d2604952049084070480f03000f41c81c400c0200d071142e0b40003504d03200d0345003002d20070b00459030007034a8040d10078800041c086145482c2c25055030000c291904074943c54143c00c0060041d2044688040c0500d141d05d10325192959845802c0da00ca9038a00980300e03600c1d0210781060181c18230113240103007009002031248403190310b05900140b580340500031400209a202107003800380060094186c0e0400341ca010340c49406c0c00d11210110800400c011502c0d92903080c1c1450f40d8640c9201407035621a4030004540758480e80c0c0c0054845104101d25264051a10314109229502d240d17044804403001440c00c0ea030705000c0740b0b503850980010740010700f685003402c2c0700140d120350200051045174000c1c0049800480da4400f0001925419141c0b29441c0c102030002c40c140740381c105402c1d50014032910740061110401d60109003190011302991441200c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 267591043 1250 267589793 267589811
    0x6130807032f04180c090c0801150203070b0a0b030106030c03060507021b0607030c0506090303090f0105010f091d1c0f020a0b0f0705040f0801020409180b041e0f0501 73
    0x14002154081503110302d500c003401106503411200c40003285060b481107449115010300d080258489015041c1c200783c2401c0d0803510343c01100041d10303240041000203516017000141c00590030307200c00792040041d400b46217040203d0320b44048400014050303090340742d03480e601038286035024031540004511400d00c000b0000d01e0360414108643c40140072209540094001c5d4484104002004d5480c03801101e501d52216241d00b001c99001e014030030300501c1441030b04240448140c000025511601121080710b1034105960b5400d82603a8080c0300385401803407810400d200c6640642c00c201c001401070011110141ca1100c981881c242aa009600a070000400d03000541c50748084604111a00b41c001040840c1c0c3c20341d21860f00b2a001054039074810360b0140803400b0b80c0d220302c0844000340180c4c40090901515200c00e0340c000d60042c45002c030118a011080301c520389084606040fa950800c40000c190340d2140c0390a80442d0381060310100c101c820988000c0064104007109042c10701034400000c0c0204 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 267592293 1250 267591043 267591053
    0x609090c09091a090a020d0b01140a0806070c140102070b041509030e1c140609100605060702010e01050906070809031002090603070309030314041a01140105180613080703 75
    0x19090700041e41d52400e01d40044041002003d511262500b44906001182d49440401d0300f402e292101c001d41c003071030540c400170900889884640c141d50361464004002c0c1e100c8420800c842c0500e20400d02c951300300742c000640c1c82c2e004d99841002035001c0c0c03240000e0407010170422400ca0380714443c2218030f006144240400c0c00320304140079800b078202d402c5c10002c0040685014148240e04c800c4684541b03003072402e1008004a06203406080c1e40e2181852001e10b11343d4a03402e858180464400c401441000c10205c1901000e000360402c842d0003500039450165960011150a40c0400390a8144081006058410749540e8024107106014038060340d00c60b5016404c01d03017400030074200194014010b003d8011185e0310402200e410000d24100001c160166241c00d4029040070b6103842d0560690400b004188840000ca4800da5039211003641030903a202c0c1d0203200c076044000040ea000034000e0201074000d40c4212408031018030000c0c03035039041891508101c5041e034060341143c07440c0e4000c5041007007002 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 267593543 1250 267592293 267592313
    0x20a060e07030204050403030e0c012a08070b040308010e07020309010c020909071a040f140303120406060e0403111504030207060f09090c090501020f07030f0816021f0e010504030203061f09060909 86
    0x200d000d190214cc540c410301e00880a890140b0011030306400151140c42c2042215003c407041d40d0313840100100c2c245464103005d8101c0c01c0901c602002401c4003000141c0e07961000c4111601490143c40344c028100403a0288013024070020a100050301c80d100f00030610501441644400f1044c140302e01d69581c5c1070040c11400c078512980641041d50b4149030f0644295400301c01d9501d020140003944e0010758a9040610162820768825182a0107590a00080c140c3c841e594034580c052480c00c4401d41e020380e00301c150154800b11809401600403ca003806064030580b01d003040264146401e0b1401c98840d454042100c140c1c204260106034505c0381040507503010300ca0040520005e034054602c680c0b560700c1d41a62244089001404003a0000d00105140c00d025046071300030340c024214150031511040b107200d038010001074201c0420108e03004003031550b12800445064070741c050007034a5980c81d40c2c440260618a035458500000c87d05081c0481c11000d90301c00d000003440c1f81d00e8003148020003420b01445003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 267594793 1250 267593543 267593563
    0x50f070204092306010f090c1407031205061002060402040e03071b0e0c252405150307080a0f17130303030f02040605070b071404030b010e0a0c020a060e07030204050403030e 76
    0x103600504c00411004078980210801c4848a402c04103900c00002005c5980c1805980303980c1c00c103040810510140741d0b00c202d00065810720241c0802c81a116170041005550b14095604d005a0086d40000c0050070150030941180442004490900005640f0b24803a105010311204500400c00c0c0d0411581e0a44c0c48043c1d008002003880314078225503140c1c001160089801d03c0e074800810001c1c003508000401c00355040544d00722900c0354004480017a0400078000560302c80c104803900d20392140c0b2514021541c90210b4000e28028844030800e60345080c2c840140d5901034a030b00303484403103420942d20441e0050030406001c0c0e040020603821442c01500b01e60a5245400000b48184014800250003104a6247c01d03089504000b050b41e031000300719506107070843d0001d06005d000c0340000c10400d50410150580360800040b00d01651801e001d801124100b0a2110041c0d2007180f100002c10450384c0a0b08441d00c1250540b9042926500803c1c02c0c4e4105640c00c4000a545e4000034520340740c1071000e0300c01 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 267596043 1250 267594793 267594863
    0xe04120e030d050c060f01050312070c0914040507050f010f080c0c0a03021513020904060911220608032a0c031507030b191406091005120c031006050f07020409 70
    0x41b035414000803c0c1d881b04c000307011503011240081d0310014412001005001406141000d00440c003500201c2c4a403143d0540d01207602d881400004100d0f40f9100342c5c880c480100c10780d1030200c0480030b604101c80e00c000152010020a80c104103109030f111050101600e4513000b030b002031038805440b51007008c0c0814024174142c1c054403113410200059407500c0c0c481b5081508004046920030319070400b00500011105c0056005119468055464580c0c1c240340001181c5036404112a0344d13985080f603141e21500404000d014400782c6100a008520505490528010b00171244061382202c00300b0f1514001280c0794034070b15400b0040000c241d0341070242e020308032000c3c0c52002d40d4800800d0110400e00c080d028107041000884c1c10079000f40c6415007511800700c0c0081091f0240200010b020b040c50f849031522203400c48a1000003444032075000b044a009000c0b0008081f040d41c6005411030304c68121003484580700c54200321407009a515402010407150007103586904581883c005200710181000c0d005030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 267597293 1250 267596043 267596071
    0x207030b0915010e09190c05010f090f061107030f0303060311060c0607050306281508010308041503290a06030e0703060903020307022106010b040e04120e030d050c06 73
    0xa10440030110f04454100c1c1c2c9240300e07502d8201445041c1384003098040740a0303254002020a0007001c884002c1141e6007a01d03400c000010600c02150418158018201c601484900401c4518811084603c0741c07400b070320135100015126541c0032200d01c2e00305804c0d00029125501403090003030380346883d000c0b0b48085036014035010b0030302202510b45100400300c4041c44000b100282454030f90b85c400b1144505030303a4000e0380306802c10110b2a00c141c01c82c060031a0084440504580041c0280d0a06068a810142440c2084e1a0030074090030380810038100c10415888004000740b51780710244944149a1071080d1003030340c406003018060000d920360f00c01c1041504101c24401881d002242c11002e4be03405c4030006c60354501c1800c05a265100c0e000c030003500041c5041c1e081c0c80c8080458032005511100106403045030f6640c00600c512800f560060b00314143c0d01e00081070000d040c00c2410320102e031407420018000ba0b40320002a0800e008880701501043d000946608001c10502010758402c00c2210604 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 267598543 1250 267597293 267597313
    0x30906061e210102190314070e060d0e0c0604180f050621010605060f0d06060c03210b0303040b13050a0311130b06031e160813020609030d0207030b09 66
    0x25000001d0101c201d4502022810070048074400313404864144801324000400103812900050041042d0810b0484034140342022842c0c2c648200d1082c51521001000d083c106822000c00c0001070003800d03440c2034036101d1502445180c4e05c41c100034000034080c024580741c076104000e205000380e65080c110b01400c68600f50802c407059440d6000c03092503140d651101142c0d40b180101060042000b6002642c3c03103500410800c688142e64401010016580c0070144040c503a60202500c2140c0309503c0200481e9000d078200341241c0581d4442014414802004036640c013403034000c01d05503405504260300070103001541182400a9200c004c000700800d50b44040d41c1459a00c401122820b2507800d58414920041e01e5821600c040d0000d044e04034000303210660740d06200c0c1641011100941c60414029640d400281105044054407110700400d41c650a40a50b900070302410030300c9103500100d0b1310074818800ca00651304d08202007013203060560000c0411905504010280c64001008901250701c03102140f = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 267599793 1250 267598543 267598549
    0x16300507180b0a090e04061b091202040216020a0305030307030c021605011803061107110d021e011404090c0806060f0d0b12030c0a14011a09070302070503030906061e 73
    0x41c0c400c840d0040b08107611000c0e0309004885407902640081074004060042c841400044d52140000d01100d00001031060000c0350107a940303090754403031008246910300301c40c0302604007a0001d2101c26908042034440e0422603001401100440d041990651320120030010500d03018452070b5103100e841e000811441500c000d10804800c0d40740281410010320b003d1005141d022401101c0280d40d0100c1c050059040c110074048580e0440e80341502c10b201204800031607400d00088040f6070540103000e005580555030001e901e40c2c15040c200b10304000f403012034030500d00e62450142c00030b070a50001c080703081c41340758800514614000d404244580010051500ac41c40300c0800c980303181440700d1001c5403995a0034001108003682e601c054100e400000b84078400010003003401031856200b258407a19240b90380301054201d412450942d0000148559218010b2501c0e890f0b450348281c6030b103000342c60302640d03942c4d207401c640084d00d1450455101805200003890a01c154110150303401440e503043d80074a0b400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 267601043 1250 267599793 267599837
    0x3020a1103011406040c020106050d08130b1611011e120b01050a0c110301060b0d0209030d030629070503042601051009050907030b090705090f0702030316300507 71
    0x4601e10031796845c444c18134920700079001040101001492800c80c1052400e000b07119078401108a10464145880403808880c100182c40540455220800c0c007000c1595500205143c00c9000038103010f4180d81d4660740e40510721440c400300c0c50564030350400c044074407401001c3c1e480800d48103041c84004c1c01071074102e40c3e11040d094102900055400860201200864010000e40d0401d5003120b074001a5641400865001888a00c0307013901146c11a00c0b1540c0202c003101c0396402450200380395803400040310040381041c0c0d0140211020664031b0520f071a5995031440d4441d40c011480702050480c4800074814112015800039202002441340d8a407803102c04507014a1030044420280d030361320200d4200501082031801441d840300441085081202d4000d664081a00c5003922807690b40f000900c0b441c8134550012300402d801d40041d030460303c5a440001901c101c105802003082440e03101d01d1604500e0790f03858000f840c1007402203500d40b0010341d01c2005480000f0521803c0c04004c0c5200c0c03242140c1d00742 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 267602293 1250 267601043 267601051
    0x4020612040c030512030103050c030a05120a180f0f080609030313080c0607020f070618090216061503150e0c012303090601150216061209080703020a11030114 70
    0x200c0121907035245400d9041801d40c0c1c00c05002481104103818080030b00400550590340103400301d03051042002c0c1055521400520002c0c107a400000c680d1034811100c50103001c517900c8038100b00b0600c641e111a50f4030941c80590040c40c02e03240c0e03140c003008441c4424110034003411101e80941007070310740484801d0f541d10025040b00280540e5914100520000d50161603520a5800540c1c40700e042540000b50390b0113501880c404180601100002e640740107150781c0501c0c9001d120f49402030b03440c00034920002c2d0010214180e56082e20003511001071140e03c961036107406506029071403141503040c00c40c2070899050052921518018184c41d903140300140b401e406000c02d10346a05140800e80004a070301000c00c060920406011003444035248002c62070905035545070503000c4504001280c12650b440c50050981c451007061681401494891500307014244101c1e036020414038080d640e100d6159025940030780c010303042000c2c5003003000004122640d00c21400c070001d20402580081030036503020007070 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 267603543 1250 267602293 267602317
    0x207020901060801061b170c060106110c0a0b0c0f1c0206240907200c1005040312050717160c0503010c1d04150b07060501091506030f11030703090b0f040206 69
    0xc8506c00c10040b1144840c00101c1c01240e00d00d86680300c80c0d1a03190307108000e010300000301da040480261451800200c2249400303005010603071a07403400060780c200343d101504060490245008880d288001040361140c07000342d240341010301d05010b8000900300b620180118500c04200c051080700009601e806902205003101c00d241240c660160a4504c860f00d43e900c070301000e00011007074001c0c940129030b000c90303081d00b43c44101104646034000c0314607214500000301081413080010743c51510580c081c1680601c6840120014000d0f10103000161704500813a00c020350b05459204200504145c41d940140000c0d0000d10035082020b01c040d140e01508040c80d80b4900c0c0d014401e403642d5645030010090026070309000c055540c1c4030351740e43c48250300c0910241e5120b41400000241801548a0121a01c0103502c12002c1c003420701c9000c03409405c2c88000b840d81c083d111a030381884a1550001980110041c0c0c5002805d003182d8503003000d005800400302900340a0b140100800341c0c0b00c0d60100c030341c03200001c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 267604793 1250 267603543 267603587
    0xf010903030e030a1407080606060703052b1b030f0c02060109111201090207050f0f1e2e0f1506140f0f071401090c15051b01020702090106080106 64
    0x300030914144c0800c40240404403244d01481c151140071070300d442516080d00c1610f1680d51204103201c65817180b0900100000c1c010000c88a00480100c411134103c10a0018960820102900c0c0c5040e64041c0d81e5080e50011003610030031041d505803141c1002c9080350354040c0980e11807484042d403210720511030f0703200c183d803100d00e96045a005401180c0f0240345055012080f540c40341e0b0001c0094001d50360480d01361040c0c00c01000840744c00204405d00040140061494140d107030104815801c20703d0390255180328070492400c500305002d10000001406200c0d0614800c0c8004141c0284c5400c4003040401604c1c103429140404800312814096030321601380740358041142500c1f00305600ca0103403000c2d0380303540c081b501d0b100d0305400314000c2c60094012100a110f1500005a590888000c0b01c00245840d440741400c100c600200c0c1c94501e00844a404c0107428208030704a0050b500f220500c29112507540002d81c8021480c201580740c6c09408586841443e960400300007a03d900c01c0b0004196055004c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 267606043 1250 267604793 267604817
    0x5130b1e07080f2e0f090c05070f02220c080402100c110f03030f030108010b041406030d0e04060f170f0607321602150306011409030c03030a08090c0f01090303 70
    0x240c10044510504002030386428a541e000c2d4902010121b0154680d01420840101c00a91059003515801d94024001c01c902d0b407065801c1283c018903655403d020442c40800d0300030f1800552154003c0c2141702d4464502c603162500c100f20480d0207040101081c4028114004041101004896004002a6025a10321040ca00080e144d030091800313900d8046c1c0000008103c00406403c409002e80064506111000035003050040d0b000084030303000d40650140490512043c4074444917020148050030014503d03445125465061420341c2014000300c010b0003030300104000800540200b4914000540078508005400408018110764078086840784030402400065281d46444050b80c94425010760316421002c0026151005c5c00b802c5c0d110741707041244514100c8400301184d2042205a45085904041170501030b0290072441004c0d80500c5003413424049910100018099002e4546541050f032502c204d05c20320f800d4402da01356000d5841d42c02002c11598009041c1e10030b481e814241120f100b42 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 267607293 1250 267606043 267606091
    0x106020f1b0a360219050313080a020d08160c0b190c030b030c03010603080d1a0d3002030915090a0f0501030f05040206030a05130b1e07080f 62
    0x1400e504243c1d000e207206100c0d64110421026501ca0252a006100aa00300c81d82e001104901030441c43c81e082518030311503010058407960085138410703008843c8084924032901d43c140c250300407100d2800564485940d03510000e810100450340200c1c01909041c40141132200203001e18209900241800750701008202c0c407840300701e442640700151000030000f01001c201c00901510001400031b00a004807130780c507425428103000b19420340741c00000301ba14001050301c6030710048c4080142070001c0031844840c900c240e500c8103001c1c21054012403a0b04400320241a0703035900ca080000540710100984409801030303607008020f9640c000011103c481c049009402d440c14a840b4000d00a5402032010002180c4142a40420800c0e1903081c0d904010070380c0c0b10f986440c1143d90a0700c0107588050103100250b004ac15503004135034456400c0c5a802420000340d034038010380e54400e0f00c402c1c07020307000600d294054403180000c50360b0100052511a0050030400c06427558528041e140c00d07405541100d00101400d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 267608543 1250 267607293 267607309
    0xa0803040b03071407032a050c060918040f020103060503070e16110a0b040303060f2d0e0c1206040b0607110a1203020f010f020405060d020c0106090e0a02090106020f1b 74
    0x800709882c0183c1d01c149a06c2d0003400c140c012600002405e100b120900850006180e0503945183e0100081031041110b0f400c0051235080b2041095100e1612424070001d600303003003070490180d40720300e981c1c05203480c2920005d81650340d19002070340603500031401000301d520140700003030300b11011188040d0701c880302d00c02c100c0f00c412000c0c110183c42d105015500c0108841d103200188154049d541c10000b080e00c1d0034403000c1c0e03210b0134400c2100113984208082c03003103100c40c00c500e0f02020107068410400c558a1609402804d4100c0b006204103601040300901a01c0c0c54604c0c0b507201004450400110184000040305405031002c0036103103510390503403180f03107441c0c040d2850050401c2d500030903801446890000e40e600302d070181110295003002c4e10b00790100e02500984040d0f40004000c0740c103104062401c0f81c02508120303914045592111f0000603030841a1082c048000c01c0789014200c042154014070000e600d06a2010381154810340d0241c0752004007240380c14001c408440007440580e80c0b003000400c3c0c4 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 267609793 1250 267608543 267608567
    0x7050f040b042402030301060e060f132c07080109090507351902190911071110051801030e0609060402090106080f0705030606190504140a0803040b0307 67
    0x400000900480c41026a01c880805900c3c141c0c601195103c031004101c1e1a40003c0c401c06021600c0a40341640c103280c400058501400000701190425041c1905081120316541c00090f214801c8500001052400701e401003109201001118007420019001810140140307d060810740d92160440100102404028010725040c00d01c00c1c540d50a03000d40a800385070449000740c2412030f41c1c80d1109881004105020752038151034403001c0c01c031440c0d000d100d04003201c0084840200e031685000300d41d8000600c1034886c41103010b20002d450704d503585041d034454403034050070760703c20411800c0c03400415501004440c0000c0900c40000007452602c4010f80c090428803a202c01c0c28024601002001080001da00d48514021070300c1c4076159030780d070400369440385081d12060415400300c40010041c600620045030050700c0607206606d03002d0302070000c1d846080800070500006000007400c2000f0040b4400541005408032417070100780c2c0c41c014206940c0d208074401d03610800d002100081019010308112050 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 267611043 1250 267609793 267609809
    0x103111303030504140a08060a050903040e01031a010b03060a03020f0f0a0b0d060b072a05060a02010e0106080102180f0103061e030507090c08180c04020f0408060c1207050f04 77
    0x100d1a164503028009801c5402171a100c0200c64810314030a1801c500d51000306e800381c1c0058000c540300c480508020f010001c1100c40640f10401001500a02c2103520318000c501410302030001c2c1c8500d404000d01c444043e030016200c02014024800b41d0f0355a0f00100c400c4a90442d80040250980f0300805c00880204090950280c0b85482c001000d42c0044c000f03110341403440404011080e00d070742508140e070045080140004445459228501c1e081d846103012840c00395000c0b0342c40b156030300001552503200c02e42c140700503511119001046142402064081c01c1107800139801c041003140b0302d1042d40120704066119440702c0e441c1c1c0001e40d020385d0122010707114201105a0013040c40c4415484000c03907120880e4203116210b00020042e54038411011282910b58880d41d0b03d4803001c1925100d005168555180d900070200205a0356039140300800344143d001e02d1a82d150b620342040c45081c1a40101a007016080030003480c9c01159021059691040d0b04e401c2980e100d0002c840d004005000f69040040 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 267612293 1250 267611043 267611077
    0x5190309090c12060603020406090303111c0201021b0f0c130b2716090902090f031c0305010b0412083f0604062102031603032318010311 60
    0x1c00e141e408110b03903c14003124030040c009595074000c120b04911031032040030001440c2190600009120301e80c68003e03004024222032200d003a02c11040340d801100c0e024034001d42e500050124000840705000420242c0000c0030f4414003102e101d425407900700c48400e00d440781038402c016038541e011940c400d1000c030320042e0100b40803071404889540d14211051114800c050030030f0000c0c800034814560000c0f0417189a40302d02e03103c0c0c504451580a5080a601a64480c6400300b0b480f050747c804001b034600d03001200c01103071507004000314050308581307043c0c00428817010100702c1030052a20490040381c02c40d60140c600b580c0c030030600a044041c070541180b1030700c0c0c40e40c005080e8160701d01e0406c11502a03606d4101d01041549030001000300320b0701e551284541d004848810b5a004260041d0850406030016040e641c0a65043e80815007036410b40d04120302017988900e81001c000c50b22894810f0104c20801c0c018a000d0107a09661154050b03488014101a100c0740c40410765078110059654081b08050410 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 267613543 1250 267612293 267612311
    0x1b0f070b100305061006020d05071a240f0306160c0803070c060b01030203101403070e0f040303060617060d0f0803071e05041206020a05070807030e0301050a090519030909 75
    0x45001d1a0a10007611540703e00400300c0c01843c1080504001c40705180c0090426464041050340d05420216094940086040c1c0609812410410701807051030385211012005202101e115540c14a801a2602980c540315810005072000914a81c111440c24406120f481d1142c3e0f04551a140204c001040b1030004001e00c041d098003d035160303900314030924091142800f603d00440c22404200e510115245505000300150310944051041d500d0025007a102d003240c80d4840000244002d48824001d00030750030420003410f40c1072103040017901652429401c5140e60018100c011140a03220503c2554108820b208102da100c2c46808281c0c0d101c14002e4592404500c003800440032003544030040c1c203092101100862141044a00343c43c0c5d0040c050312180391030f440b000029000b0485444c1444010880d900104194101a0084500c20354800c000483e42105041c01d44070040c00d0320040c6820030302c0c0300000410104180c0310102d02001d90b205109010300741251480703056071101c40300320b01d031004013 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 267614793 1250 267613543 267613561
    0x50313060201020703080a0c050304150f062309060a090c090e070806092805060d081b011a060304030f020c04020a020c010806090705030606130b2b051b0f070b 70
    0x5000e140b8043d41b1b9600d80381c0d4800c420795040d1b4405411850015108100103000a000b001e0407110203c000e07007002130504604c001ca0b00171510581c101d1000c60b0480e484501c01c400134000421320b131000076960100349042110200714003501c00c0c0141541191150301c6c03081c0c8207114901800050140c6589500030741071404018003000002d540c0207002c1c3e40090006203214205401c0c541030240841464208403503400240001041d01401050b44260002c0c01c040c013044105001c2c162042a203469070400403000a0701600712050840140d49002420900d40748554507001502e51007038041c20003086e481c0c05908100e08103100716100344d0380244080b880302c08140d400940684400c1007070b20785c00c000380c07103010401000010032100c0704006401000000c0503410100054a40e4000142c5a405855204c42c60078034144c100d00100180140b10410b801010f94400203d41050301162208009505001a8036405920741480004c2401e0700042d5100d59001c0e01c5086030440352300021032414500707000000d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 267616043 1250 267614793 267614797
    0x2030d09050f09041212150902030907080a03090e04060f05010e01090606180311030f01090602031510141308010e0105060f033d0c02010605030d0c0503090d05031306020102 76
    0x101d078040c0d1080c80e105515420624400f500481d0854803c1969103420310044455000c0d4200302c80ca85501c0c0d039108200808109048805091141000340c0c0b81c1c40c0a0154600d0704001e5400410380da8031540ba10404250031071498800d6507902600038015641d141849000342035650360042c00c45250000000e1580c1507104c00302c0c140d82d0882c1041c000c0e00d175520300841d4207001052510080741c8c482d000400000c0d044142c1c08109100c0a0142c410040c00c1840503802c482c0341d014280c9c0c909030004204041e1455090000c3c0c0c4015040347e946442070701481d001000c0c100940408084000000344140780d154010320001d0081010310024400c54407824400c5000e0403050302c00324080c03c2130001003c014900400c408455400e040200c0c00c8003041000400585000c180181d110300c04c0502100d00b80c0040c40c01000d00040ca1600080703080c134038140c10f051405072807000000401070144138201c00180003000321038500100726441952402142422419441104040b46200c0d07540c8030000f62035901900 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 267617293 1250 267616043 267616049
    0xe030f0d020d0f05160f0803090604020a063b03011109040b04020f0304030f0302070606121401020307120b040e010c0f1403010513090f0c0b12010b04050303071e02030d09 75
    0x200703942540c803442d0320555260390a580c0c04004a8024001c03603031294100001468528091650400e1100e42a04c81148951040e00c8940654011740d0400003541400e02d0284018241860145124034105072402c080300c043d800720044091000b48034000e078040300780c11560724889c01402000300030b072503042c88441a0b0041802c18003071401e150005400d171030f0034400c0d01c01541c4140c980790300d10f03a16658215146d540200210090540c244501ea02250305442400d0240001611403443d20b11141802000d0203459a00c000036613004000b0811440d6000000c10140c40418102040807400c22002a003d0f08a000d01c1d8003080d0328000481010982c400244480215075445000f011a081c8040300ba040c4801d02070140c101034104003125100d10164000d00c00c0c1402492028241000707035a07010088001684000d02c074000100310b080b90300c018803141c1401002801c503d285828a0f00c00884c1d22030045100103811041c8451888600084400c08006241c2d0f005007691200003012202034503001a80c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 267618543 1250 267617293 267617297
    0xd020a090c1b030207030b0907030b010e04020424050418150b010810290909190c080907050f19060306090e0a02031b180f090c09071e0e030f0d 63
    0x94080c60b50701115003460400310b900740d80030f0503040f41151034010842001070401d200e14030441307030000046000100103d01a00c0002454811424503004100540e02c5c0500075240c2c44820310500440d2048850419040304c0003580d01242c42e1140310555140c103611313424013601441071203401e02d040a8003903108140d88542602c03600c0d100d84650303503c7d0a00d51118014100800e035080360903200e605080e60810380c0c2100c100780151902c0c807141e0200c0c44c003e83c01e81d5100d070300c48031101038411a02c0c2c030f900640f0a200351510f88000176113014002195501c1c520f02c1020702580f40d001c640103181d15205000309004512204d4049407540d0384100500505040c4580c04c1014a80112031184003000300703503080d2094004005040c03d45036456044000900085030a80c0f050780218003507402c441c42c00b426480360b402c50111201c40d24040024174200b091400303038180700b4400142000140c80d008030700460071480e109026840135200344001c1c5d60043d01e108105a052081c9190b55802c40c10014410706104166 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 267619793 1250 267618543 267618557
    0x4050315090d03020d09050d020c09010b07020d0b04020411160203120711040507051c05040b0606091507030c06140702070b040521010f330b070605060d020a090c 71
    0x656164540000c054540007810b401c58004414140d219030080c0020002d541030014040842c1e40c1c0e141d107808201a0303d2005038020342ca28a44900d04410507600408402d40d000d0b1514107640c0c001100703c1c68099000300f11100c4280800c0c1507481d2a40305801c8404200141030faa8820342c608640a242614800c070301c41e10660f0100c2080b48c41c00e005840c000c60b408002d4640010442c130800001d0b02000340340008104040c8030b0500084000b81d074080c0509003880d4006200d0500d410186655000100b505005001c20007000b80d05413102004103204e003c041d00629101c0c2c64038034007100d8550002001400e5503041c4100c017140d00764850700050003a003942d000c45445c1603130f4030001d0051340294400c050b40002d449440c003002c0445800c40c0304d40c14800d1000000c141d251046403004403100c0c1810340e00c100e10f00c1045e84010b4249c480b0380c0000f412501803a0700c03070507142001034006845040c03401400151110701180c12502e52102003050350354000c1050b0a15500d036910340000b403c614102030000b40d50 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 267621043 1250 267619793 267619813
    0x111040b1b1614010c0204020307051305040603020117130f030e01030b0906090c0703020321101202031b1305011701060e090307031110020a0306050f0402280306050312040503 77
    0x300040041030b00c5480200d0b020707400d1a0083d841c407500702580d07000c2d05000480080200699952008503c5903032a0340760700c0e444182c400b841504507109500032500032840c007070b000d00240c0c0c2c110340ca01c8400300281c400805c0c2941d54600c2e11a4804220784014215007008008030205904070956865040c02070ba0304101074803820003001507014094901d21703080012140402c0018100d140240b284e2402401100d18003598100544032490344400c1ca007040240351403d004641703c85010402c008c2c40d040460300f9a280326500001e44880f0b020070b0742054048510f41e042c06a40751307041460340307901e40c0e05000c200d250307540c904110440f9001100d900081d40b800b80041b8000b010026028010384005e4003c50821810b0b80d0240c03030040c0d1140c115071140c071a26062ba074a842050000740200e030721075900461228642014403070201070f1042140e1040e8010b0000c24001110709001c0300903041d00300c3c0e490110b101100c1d0700f60003c0c21160401c5030580959804050301f02ca0725030042049480940c2100c00e01d0203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 267622293 1250 267621043 267621097
    0x705070e07140310050405090a150615021c050d0b04020304241401030b09070f0803090a170a110109120303060302100801050d06020c0c0901030302010e06070503061503090111040b 79
    0x11003150324403824650344c10140305a0400b41d100951181d498000c9a0f002d071203a0b290200c070034000d140891202900e61200b030210180070a42400003601600081400c0010100308507080301c081d41e002007c01c20081000070700241c003604001442c0c3c1002d0021540ca0825042040c0c9400300d00503240724001c228840c026021072580b280301500c024920105c20541d0940d52141030400c0003411400103441800004071750410500007404c010211100210769407a18602880503000030b40d400440301c2e40b0070300360b9028203900114107800504d0b80010f05c103040f000300e840140c4501000d03810482c1c444152031804000c03d40c041c2c1c40101a070f8000ca0381190000e0320140c00b16501c080c240905a0405038040701c0500140d1103400ae000d000050303c040e2007902e0f400c0001700382d051030709a10940040c2c0d151180e10460701001d00020f41c01540c545071551940c074141003c01c0300c00d0451042070303003035101c00400201c40c00310030b61200ca44403c881900a075110f90342ca80a6a6a4212203a20301030340741e2071003540c5c02c0e0103 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 267623543 1250 267622293 267622297
    0xa0305150f0103090804030c080f12130618030c06030e0708010b010f0507060609090b0411041b0c080405061303051209090412030e0f031806041d0c0705070e0714 71
    0x50303001400582a00228001140030300360081d82201d4810091001000003252070780114040d049810090a0403121103003010f2401c4203010b4007516021003000b040205240940104041c1c2d4001e0034401c285c90380d40100c174921801d40b6440908440c031340480c081100c540c036400145608001908854a82d5154038a00c1d080700c220030302c6180840d0f0014424a0000d00440c007078980c0c64004d9100280195403403401c441500c50000c0c0882d49280040d04000c1046188080c1c180e044c0c20a4800f08008220a01e00401342098403010209108040a01d070042000d0501201c0260402814454a42002d1142030190140c5400121443d00a8081a21814904d2416584692002400381034191a5500d0b624007140d9240c0d842c000b0103407a1120424149010450210039502c1c800095684481e600111982d4a20304080148281c2d0100070030008420040002d20425003e010507051a440708041c200c0746218849004000d40510f1a0010f00d01c50041d2855200c0c04c210b07107454610072691080030100e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 267624793 1250 267623543 267623581
    0x507090911090f0d06090b0406110c060606030604020408011b09080d020c060a0e0316030204050c07051b0f090a020a0305010509070516171612030905030301060e240a0305 75
    0x10640600c8005820329200304940618800a0310b680700c4c0400713540b518810b42d0a14441034074504007c0c010300040068902c50f107001c1503450342c0071a080103d9688615250076014001c140b10300c00c00300100c3c199980e80e504550040c441c1c3c1c0020011082178024402001600b100c440004c40d403450400a071441c00420640a45a400d60240405800c10790412055811a10f0b1050070020001420f00158404200a81121003111540c4680d40d1441c410401503c1e0028150040800c060000300c0006400280c0d2458400e4001e45140c1000000c20100300790044044889500007015400d001560f0940d80c01040c00d05603507507051003540e0320356085c800b40c1d20007598007900003403042109036060b0400b1003510180c1c40c400c0b4a0350f040130101e42000795051300711600000716880308600c03480810664110101c04001103040034401c9140e00d480d01034807400144245c00902100080103403160380c40d040e41d00c601e40240315000039080303c0540c4158480e0805c04d0b1100209180c50046640075a0000c0000c00d5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 267625899 1106 267624793 267624821
    0x4030c060f02130602030c030703140c0106031a0906010515130509091e1219020a06150806070c05031801020307020a0b0c070b0f1206030a0203010e0105070909 70
    0x301080c140c4c8135805550042212101c3c515012080d0740455800d400c0c40b056503190101c016445120300580749a081d480c101012081107580c1541134001c0859001d02561591400c0f0400d036210020300540764400e8030903079030401c2c3d0300200000f49071020f125a40049010342e200081070074114245c41603180c80c7c000101c4c1a07800e071f0b600d00c040402c3c0c480342c50007403402020711700301c0700454418140b10403082d0b0401e00c5d6840fa560300030090b020180b6030119042050b211901d41d408003000241c054101140100c0d4041281c0701e10501b16098002c0d0401d010b0752070310030906080d11031808803100c464107500040c82170304003580c0c42c3ea000c0002810402d400594407006c90300300c9400d0910540081000744024000b00c00d0241c804020786c2c0210201d1400c2078015100d01c0c000030b01d0005103c030029819820110640d12082040d0001070140200c2e440d003640703071070f10380700308005441004220201d = true := by decide +kernel

theorem cover : BRFrame.Cov 267446043 267625899 := by
  have h0 := BRFrame.cov_init 267446043
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 267446043 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 267446043 ≤ n) (h2 : n < 267625899) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
