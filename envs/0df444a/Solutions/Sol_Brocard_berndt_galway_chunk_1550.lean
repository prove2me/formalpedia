-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1550
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:31:59.785747+00:00
-- url     : https://prove2.me/submissions/2cefc5b8-a0d6-4ef3-a94d-6e7022e23e0c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 278597122 ≤ n < 278776978 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 278598372 1250 278597122 278597141
    0x90309040e01020a02032a0a1506060c0f061d0616080606090a06081018060303020f12041403070302040203130c0602120d0903021f0c02070e060f0609150a050409 71
    0x310308090120320002e44910030054104071059561000c0ca400c44c6913007d801e110b800c0301100b02d640325038062400702181141004500c628502c2c1c2007000031568012004602c1c0d9907800311921401030155503401c0014003540548102074500d0784980400c4410421400f8005c45c1c0c4099003175500940024001e02c1c100000384014003c81e001c0c8103012190311044c1c2ca41c0107841030340c00c200241d80d0b500304000f50060070342d82c0305605000300c130b0150250b205150381c81001030328003a900340c865500400542c81d60702c41020781c0f446c09034401000300300110580000c582103210402825202c80e00c4d40da030001410790b002038500c034880c80104500c007020400d148a4000040c8030324005071051030501d02c1d409100d4020000201d074010f88400c11502018820b1000e0710030b0a016881600580401c441600d00070025015410054803a215000c5924655200003611031503000304001c1d0070145000500c04079410a84005070072840d1603048007120260540500075071202980d40795102c40c60f2042c8201511420013 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 278599622 1250 278598372 278598401
    0x3e010b04060f260d0314010603051501031d0102040306141b07111c050d0f05040506090d0f020307060c050106090b0d0b06150f04240f080c04090509030904 68
    0x80d41000b440e0481030351842152071502d580c1e0307421906002030740701c50041c03000c02079082e0280e001041d1907207416a201c2240740c00140b031011a2aa2104030684c01c886c410345d880d10b0201036209010b800c0398401d8201e1511000d041100d40741406100c01c2c40b03420f981080d0401c543c070716104d07403000045144420450346e01040c1450310070003c12020214000b1441804170244c11003d06030b4040e401130300e408000810100014079100549042800c10a469142200c4040c0020368803440010171584988241d90a0341d000420711443d1001c0d200c03c0100003034940c0380454030101e031108c5c6076000d43c1c1c2c2030000c40000d000039216010706a00a141c0b4a0840340c10341c0101c0080c9152128900310707600c510320716280c0f095000100c400b123a00c8040c00210400c10520b85022420342c0069545e6140d88100f02810884120224013084080d20b4500014005400c1c91648001109a41c0c5445114403c0f00c8103600210202e01052910f0b490f4403080303003074900840322002e444d84002010b04943c1400e224201c070030003200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 278600872 1250 278599622 278599631
    0x30319030b041503030806010f050301050130060f031106030714091f0e0102191a101e210803011a04080f072102030304063e010b04 58
    0x584162a010020411440405a8504440d1016101c940c041c2e088140d840781451001c507074038a070040402104440c0d40d800034200c0c55131003080034018403e8030b0698105031034100e0200c040503030100081c9107401c2040b9100005d0004228080e10303600c145809001e581108420160450415010741480c808449000c0c2100700100528980d001c0c0c0074400e894401c000b90750741da000640018a141203142902c0300e12070b00303004410351001d8214070f0f8002c0070a82078003074504124403410b02d000010742241015054030034142030080f10580040c80158000c0e0420013191040b501d40301c400e4040c0e01e0703620b001480c90a03e03460a02903503000400e0184207103903503a4508000d40445d40d07a02c01e1400306119500c014a10502c50420141c0f4103015036020345004802c0704c0400c1c04d000112a9110454031a032034000c106001c80500c0155036205072500c1940240095250501d005c07000c03207080094201818030323400c81c0d5052200320900b1501a03c4071040094200454100c580030950031a030b1040d00040c401c6260 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 278602122 1250 278600872 278600887
    0x180f1605090c09090907050111030705060601030c0c0c03080a17090705010e01020a1b030c05060a17060f09100911040f03060b0102011104180501141815030a0303060905060303 77
    0x50125041600c5040e1080c0500340c54840b0808200c0c040e80f61640d40c04032607881001810040040c20744101c0c1c1c13090b1f94558603086070015041d102e1040c0e00010348176401c00d00014011f540281c10110341c0c440a032500403a0a051501ca40c000032100c0e8004840c0c2c100c002441855060788220840300307103a100c0c8580e6416080c039414645e5240110320403207040c041002c290400c0d0740e0003400f600c0300d000d81140494440885042110300440c000d40070072038107034000000c04251401c00505072210550070746c032960796448000c4080e0446803001003203181e016440b401e11000c2620f03040ba801d4040e80c0480c007036401203400c0488500c1600c00b003055900110000344010408050030003030a50850303800110010324050346000407409404c1026840e1003107600042d00007041c8114034188030444415070380400090340ca40340401d41c40e0130301f40c0900c0d40c0a0540800b0829020200314a5600807030041382103030000b14030001003420040b600300d080e4080f959889080180d00128014180c0c000710440255180c8000e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 278603372 1250 278602122 278602153
    0xc040b0108060925110d0309050303150409120302030f070345030507050d05030103080f0c071a04090501080601030f150605040212041b03081c090209180f 68
    0x1005118901c00c02200c00810100381c1030700ca074003100c412405508078213005405805040719030361410005e010b10030714174603088240c880c0c4500f030030b010f0340701002c0c520390340303544c2c80240d2403281d02100180d0050b42d4807003860018404550884441102740c6002d41c42c0d00e0a4a0807000381c00e4010070f01001d140c240413046c007101d0320b4034811280c4864039166015102d0854040010601c003056500c180d240030782c0c000e42081c55007100280410900c13460846801343c56005044640d80000e00c0001c02084c8203003c1785100c04013800141180300914011240d400d55281c14600f907440d4150391010288000040030300840940d80035003400342c0601402032505514560f901c0c04041003a40002c3c1807800d1107040d10030350500c0740d00a1070060200402c01d44d207888155035081c41c7ca69045d141101c0e0701d1035a5001000c10410710120404aa40007402c0a0400794142c45181030703016008015840c640c1e54a07007010060f904e803800e41c2e0191042c0800c0030b40e020303040303d080352601700c005104038034540c40910003107a40d08 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 278604622 1250 278603372 278603387
    0x30c04152d08130302250305121c020903100606030605030705030616050703090803030405161509090f110304050d020f120a0e0a15030506151c0213030f03020c030c040b01 75
    0x101500f078191a500c082c00c0072410035403034020b21107820440b000e0f01d0040841c640340c003409603400f480c250b84a540d01c1d0710000220740300702254006c59056121610004c0e81d040d5014002404001d0143c40d61021302c902440c044a407240c11030303400310343c3d90501070080307003000c01c400c1c0b019041c00e80c002c2c2000c3c04c00d2400001018160307030310a010044006440e034100341c0301c2e1907802c0043c24002c04807030322401c0c80d240a50711036807a20342102d010743e20300000050344240d12600030410304045e00c68170115414000040702800d0100d03c103c8807182c0366000a41e034004200021031040e4056000f0300740180e00504000d081090b0b10314000041d600c040110303c01040718a045448916940c20044103002481c1c021650b5855640d2180268504c0a203c503054a41c0540104e4400d10088074406041c1000c50311218807401812002601c9258807002000d000289134024111040c0c205903240d1001d58a0380c07002e0000302c41c0d1400b100140c00000e148912410304101c1c07403800c800116400e22038102d0500c0020303e07a1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 278605872 1250 278604622 278604631
    0x4050a0315020403170a021b0f041a150417031e130b1207090506040b07060f0908040b1815030a1805010c0e030f03070b010b030c04152d08 61
    0x200c448801c1514500e441d035040740c0045074040c10b010021100b003200b242c3e00da041550090094000d03820000141c1c454281a40355800c8005c1505003c4081070042c00000d09544074036500c894a9103290710020341e140440350010010f403640040e5640c0c2040700b8070850548040c1c3c0045c295000380045c100039021144248040c030340c1026010f0f10b95a106150801c07021480e4040a078212000a840d071900c0c0e12603001c184a100715844407802d880e900c1040c084030740b1076403003509246d16080c4000b07400191181c2010301c580c83c40d01c2c0041002d418503164182c10b80d01a41c8007030213404000814201603082d8001c1c0b0b50319a5822034503110a81c03803406605100b444020b18000030296500202d01c1d0702442401e00d0746646810000820010021802c00b4000d84030280704184a07103c2d181a11450400000482d05003550091001510b6480c064a0701180e40002e80032410a0400f0b1001240703886000318110348900d1141c1d42c84040401603504009516040300d0510f48294103282c1e611101904248401e402 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 278607122 1250 278605872 278605883
    0xe100e12041505130f090c020f060c0c010605120601032a050405060607060e0c01110f031602061b0705090c07030c0816020306090303090f06251e0809010b0604050a03 73
    0x30248902c2003115644a0407400d16001365801c0b0000c00c0004509620a05940b12500100910181e040050f66141d6250300c884640b03901c4240002c2c04c000c1200040c00c010200c02e80045405078a40001400102c842c034034070b00007503100300010403c4c082200c100d2251360405500b580c504d1642c40030601001d1415018803030140c2e0300d40c00486c00030348030101200c10940c0c219404000d1420020380e002d844511018007180090380c02c012103c4401d601007040090000080000c503c0c0c4490042c601d0400c0808003810381c2d0246040c0440c08580103032030040c21000301064040c083c3c2c5030070102080304009015281c0e44200c141401780e81c00103508892416100c503084803603c0e44941504c3c0c8510a03219807880b0081d01400b941e400c0c4074102d00c0010107180200a03042c1034502c0308030a02d1680b56214411a6a00301c0da5961084d410a1101c40340420f800900142c85c0041e02000380c5118040340b40400e40242001414080400010f45028031400080d01e00845e181d41c0b030306e4a0032000546d070300c100d4000540b5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 278608372 1250 278607122 278607149
    0x40f03082a0703050418090c0b0a090312090e0405060405010c050304121d1503061315140102010b090f060a050307140906060d090503070b0609040804031e02040e100e1204 75
    0x1810b0140c4c1c2a54024190300c0388886a262055175614003801256408441003404072901160b89003107007080d5407402c03100d40d840d14100d904e145c84241e6402c290450060070300c9174015008c1001e103603d1741d00718132881c0180c1c0144070608003031138514211000b0b03084101c2088400e106100005150485000c208000303890300000400948032807180d20130b00c00b44c00b50b9004d580f143c55690556000340142d48910021101c290003215002020320aa881c43d03107100c05016a03000e014000158480c18240c40e004e070602c00090184004e1002c98406001610000c20002481080000034a811307050300c03010780001e40c06400100c2c6480402405880c04c0200b06125015a074000340c1c090310b81c0d8050700c840741007080050280d1006400c00304c0d12503126003400d40329980128005401400c090306030078001c0394000017891805240d078440c820b0034070000e1040506110f400c821100582d603940100300c2c01c520f082019242217408000414210b031031070610080390341c100b1a85114000c8050095504035808491080e5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 278609622 1250 278608372 278608387
    0x306010e011806022109010c0219050402160203010b1203030621030304121404060203090609060d090b0a0b0109050319020a180507030b06070f031b0b040f03082a 71
    0x30b03240c1d24244516081d61030425400540c00b6030000b05d6100705624030010312094041c0c44140c00c014802c07003170351502140009000c80014200f415059211602c20408555166150000907003a6800f9206038007000350305400804c194074007032141890828003250028426004d0135800340c1c89010060155104a02594100b5001076035a10184400300c8003006030307980c0b403900d07242155850130050030f0000098a4580703003d0800d00d00c04207e80c07d8607504e03001141050800010440c4650201203002e0308082d003400820b0070345c41c0d10301034440d40da8402c0c4220092031900d00c0c22542210b03050075840e81040f4054108001c580c401003503d40c1c202c401c00051a171448028000300314103000b5075110300301a05018500052840303040d442503008108a5505100d4000c41c6000c0001c140540c450152841d400c080c00840024000d040c404043e030600c0402c0d855070301c030544075144c00c21030032034080d142d8048810b268801c2560114449522410008035144001c030000038400b07489001c0d02544a0742d100004804 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 278610872 1250 278609622 278609627
    0x90914100e0a0e0a08040e090312010e25030507032f090d021c1b03080316090f03030206040b090d1409040b0a0329072102040f1d0903070201050306010e01 68
    0x10f200d1400000101d640c41d8a0074a061140c641c400d1040840007036088000c20030f0300c1d4001c800c569841070781d8450340340c00d41d0038607800c1540b441010b01030202d0b60f400c1401120b00c40350036a8000c500f10084e5200080d6a2819203800360030f86190300403004014900c40048828025001280003e0041c02d5400685075442036022640b41802103d010b9400780c18420300d500d910701c400c060001068442c60b001c01345a403030780000c07041400060000401105007800000c1840c01c400d00c813401c04685900d0280740c00ca0744c0d035841114400310368101ba00160451340800050000d044405500b00300e040c40280314201c210000100a003a41c00502c0c455880000352001c21552250002000e042d40248548903e43d03480c5800c3c242036481805103c1e142e8a40b41e03030b2107109160050618440e03051078407600d52542c24407005903424144014071546890f820310000c128001010f0084000c2c04050003104030032045280680e06e11440100104d03050fa10402c404401070368440e0660fa040503080c28241100c113981c9006 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 278612122 1250 278610872 278610881
    0x20f0c0a12060603060e0708010609050c090f0d02060d020d0b0a0b1c09020901060815010215010501050f07061b0210110f031503010509010f06060908060f0405120a090914100e0a 78
    0x14100303505086c0c0100f013550021488508903903202008000725680d4100000035504202e0340c0080c1c00c00c041c400c81155080624a46012040047c40240c0865081d40050055004213400c45180e550100300f80d04603018038891074a01a4045076551150751429a90030103034494481ea0301f071800d10000600c8203840d02d0750080c265442d4001c1021400d5a120b0710001d0000070700700c0c3c0076a15203ca4402c10801c55002241410f1290386a040e0f521482c0c1c02c1c03070b005442640c4950340c2408030400801208021400d80d1041070a0103803107040d01c18a007055018002d10b882300003190441098030b8800b032200c483d01e14008072400300c000d005001c6d40302e544c4d00c04d01003010742400304210b0b0103508042c20045040e40640c05600f801c40d44940c10043c040e100c0b002141c0070349130f5001d041545c5d0f000b800814070b4410100900c40d070180c8180300300c429a80c503195010740c05030070484c1e012000c81d80148090244003450b0040d804681400200d8810740d181c4100d078400700506a114401d002c0035440c011130340662450f0013 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 278613372 1250 278612122 278612129
    0x1151106070513091a0103230103020f191203080906010f0909110d060c09090b03120f040f0b09034e07080d06080106031205090307051807020f0c0a120606 68
    0x4041040c3c20031203484005c80880490640d0000b490300440e640d000d400500c3c2e040310381010f40c83c454000d86c216428411101d983d0003805511200c038168000ca004c2e040d11065000d084428104600c0792983e14018280c014003078802c00e4103070040320040c0300700c1070101c18400481e148401e01140e4407110382488090054941800d903080200c0030499024054a5006a002c0007855034903601404e54511390403085030402c2c9c02040d0b0607000014202a08003080380a40f6900c680c0502103403829503210300c807035041d0f01c455000740c0a451000c03c040802d85810710164200c44186180c0400001c0001c41c2c895072a6100301201001001508521041c04516544420040701d03142200d5546c11081c20440a160401c0f038652003003a06159003c10745400c1030089400310b951144110040048004e01501c56400101010b60148134221000417140e84d41e07100301562441c50071080401e030038285402070500307103107110303114040c0e00008816109407921a0607800311000450001c012500a1420030081c0c4925032 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 278614622 1250 278613372 278613389
    0x604260301091a0a0621020405041409060c070b270105010609051201020903030a081302040c0f02010f1b03020c0106120302011401060804030504050f120a03050301151106070513 78
    0x400c2103042c541c00806040501e11058101411080402581803298012a800520601d02110136102c0814410a42e0125071002604040c2c4400201d000c480f00d00b25005e04004009040c80b200700810b001c083d40020710641224a8422181c4442d115040094800002200c0030750030302d44201048180c540158220000a00035940c3d2254001d000e4000c6005451280c40c0b00844c0244805052080b40d9030460040e000d142440d031300030001d4400400040054203080d410020410059071544079005c942ca08588a0f1039006103c2ca100130b08595842541c4a41e061a007840fa14401c14046c5c8001c2910f4280d02d800b45e900c11031480d070903002d00010f6208001c00d4803240d030014101501900403503011840500c88140c0c3c2e030b0340c50204685e5403200b501c02034007180d0104001c0c4603a04114041c1e82c00c0c041e01410324001b0b181460641c61901c00b0001058000070008001400000d007072030342400103e001880c0c0605d6a6200c206230b02e490784800341001e02840300014102c8034000306070f803000004200d43c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 278615872 1250 278614622 278614627
    0x209190609080102190c032a0b0a1505060c101505091b04030f0f020306070908060a02210604090b070c06060510050a080a0b060c0102090907050309060426 68
    0x1926140154145805210081a10450042040702c014800c0d5800040100c075911040795085a094031501e80d10341043c3c007080424803003201d4420990308034114901c0c007040c04202c20740c0a030406226004001c2e203800340c07441c28503000c00d40011200c208078040e10340844215954611054000385054188060b1441203400e080b81f4945901d0021540c4040f1082990310740c0c040c0e03a8040c500d030400c48c15200e01180c58036040c0401e01c04184100080030ba4184a25181d501104c00c42d00001d280000841c1c0d80d20004a10920a000201040c48100e030807080e140c00075410000a103494905000050900640c00540600007504d40c0e52f85400415456420550100b418140840c00500c840751710f1205840c464106640040c07a030524040007107035403004d507442d0340c28862143c02c11505100041c2a00000070740f2039000e01c206682d1b5100401c176021052000603690001ea10500041034002841c0c1024007000388104012400c0105503203a0084d400158810704620b51405450462403c4101e00c0082801 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 278617122 1250 278615872 278615899
    0xf11120705010f0603050a0b07090314010209150313080306130204030f1406010f0e040309080609030706060911031303022a01170412120e12041505030405120702040209 74
    0x105009000d0640907000902951581000b0a41034502034800101254440840c00c4040ba013440c050310b40060b414a000c4800513900e4583d0704422a07080b141e40c50356580040c1c3d50341c0364075000014540210b102c0384e000d4110320780031008529182c08800c0190080400000152031651000c2d1130120b0b041e210720b02103485a0322802c040c03220b05580c0504945501e0810041c030400c16001075914100c138010483c0516039401c00d00c0071240c02c0d102500880c2445080344010134a12400c0c8a4984110044c2e002176484e141b40b800c00b0404e0f0b410551000e00c91914011720714004002000803258001c0400da68041112000d1504a180c40030030304c9a04d041840002e09841c425009020480b45203d0980c0c401d0350f0403007004000d0000a20035240180b4140060708040036080c00b039200d18100d16001840000c41c40541016103007491030042410105200004084c480c81c1c12606102480750130340d2618a095190640e1010f0751002402150402c3c3d49000c01d04008640d204d4040310401c850260881032500750 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 278618372 1250 278617122 278617153
    0x51b01020703090f141c0c1701110306060702121009060902090601021506090915041218060507020d06060302130c02210315030a2922030f11 62
    0x71804078002100644001020700d09a04e604050310761038001e04051009440400013a4440c82070342c200f1680b4000320321804625010325210042014020242c1c4504004003114212880b64401c1c1c0448003050060044980301c413004c5d52141941070300d10561504101610700e00e03080c1c5584600e85414144074644041100c1078114401d0b45109851941a03912554016a20341d2000c0f05681d1b1031202c5080018a9850004005a000103189058800202c0c1b034000924221030103d8098172300700c5030740c0501d4145650005014051001c2c1c6c0c3c50501031a800d10400400c0f6200b9142d010b4441c4200c03030440401c3c00a01e5010000655005207035012102060026001a040660000002d13026800c81a0b0b900d41d400080b04500724840b81c80d207032541e42d4030a00902c0080c0d01c000c4054061140740c4551002072803007503e0210840c5681c00200b114921000c0e0107074800d000a11002c013910000e280d04540030560000705c020301d0b41c1801c0056200840010455040041d40c5110300580300325424520b801d030 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 278619622 1250 278618372 278618377
    0x30417031809070c02010e0609060423040b1809010b1e0301060503190f050f0a080403120203040609091d07120201080a020705070b071703070918091e0201051b0102 72
    0x450000300114038214070030411803891011200000810704050b0300da001588100541c0c1d50368500280141d041410820100e40306400580000d884000082c200f45500c48030700300da03400c44003422074050010316031602c045817858000c0b00c15071000a4459000c00c141038029003202d45c2c2c495000d040300e0501c50308035800c06084200c0044c1c003030182d46800340208042c00c000c50780039100c4403420b480200388071059a4244400a5064082d5864060720900070f1503203a00744402034406014400c0142c41e103045050100c1306c8130300001ca0405640c42000104070003500b0403845002c4a60401c03001418003501c242e0040700c8820080d14800074020a600800c205020018039010035000382e1b1010f13050358604c0c030f1040403840387c1200034165601a803010007a07405900c0c01445614440c01d54071120092115400d2110f03081691080d0210b40713001410701c803071508422403c2c24403000700401e00070181c854440c0d000c180d241141c142c80240c0421107030000d41e40944100c8040860a185607001c407001298100c0c004d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 278620872 1250 278619622 278619637
    0xf020408030909130501110a18060207140102010605100305040b07030513030c0201170108100f050c0702101808060f090d080105191a0a03150b0d020a030609020712020105181e03041703 81
    0x10727401c0800102400e20790300800e007659041d130018840d203800c01c207101c5a0f1802015040d41159250580840c00341c691a01ca01002c24103501c022450742010302e80348240c7c200003001d85041600d004100417890060b001d9002c412a09410516030321409400100c60310001c5580242103640c01740d000040012001858441c9620200810061400800100c5c0c0603a4000d4a902e000d011040c4000700243c6040c0d0742805040549051000c0613021030503102030394080340c0d07001001c00d40125040050803e212000705a010300740c0c0300a804114280080505201d1040c001e8a01803114018600d60045501c14a80d024010214200d90b1850400084442d203a020071000c0d00080d041c8080c440030032441c241600182c901c24802281030080081011000350031900d4800d0030140c0342d02000540321100d02c002c0402c64000c81400301e0102d03500c40c01130b00b5114050402843e040c901c1c0c00c00d005060340030800d400c4150070182844291045450f4481ca0b600458010200f06210a0f40c12081d141c800030081048 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 278622122 1250 278620872 278620877
    0x2109040212221106031e07110105060924130906020705070803070308070e0d020d05240c04171513110103050115030b2409040f020408030909130501110a 67
    0x5070011804000d01c1540c50000041c00f00c48010240788040c500700c00555848804901900621010000042c403d0740058682c2c80100d022098a668600d0080c00390b81d9010400703447d00d11b064100340801c0303000700ca80c089841401e8403203944c1405155560301c00c0c03c10603500c443c1050001d4585820400029800040d04454034820341070006000c0d4804410740b00d59641544402c03600b99240b8009a6000840c50410340c1d10807401c00b01e010060340d4103074900031201d01402c01002c43c10340404401180d00c01a101c10707503d11030940700b007160042d0054221800d071540245a002e00d0201000098500160032903c008402501b40c10000110801610402224060413409036403500314801502114001c0c007480a40381840c000042d0060b0081d000b00d0b03045080540000c5880c40180c2c0c0c1044503030102d1030000d403180c0000500e0a000e1429015011a0440c191800c500e020b2800050703650700d220341c10388a401000f14070001100c44104500302d9102c9500403000f800481c81e8290b2008440e409141f05001 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 278623372 1250 278622122 278622151
    0x60302042d0e060408031008061905070201060819080708040905071d06040515070b040302030405030f01021303020d14030f040e071704082a01060302040c050307022109040212 77
    0x2450002d0064040d030401d00005003580e40c5a90300c03444002c3e8002020842c1c0005078080000d88032504000d9540318000b83d000b00c2007401e40e0090f055064400c0901400d0842e03041410a00160b8030200710301444140c1408907012150795407400141c0790040c4040a00b03a1075000c078000031051003a82103640301c3ea52681c3c0300203c0304407501d40c00341040c0061004541041060009001e0390a1514005081801c1032040341d0038103800d41d40c4c5400d01d200c221003c40041e000400c4c1007006013400c02880d1140340a00009604091a0b0304c0a0010202c0a100180c4100380c0c6518420034088548070300d01c0802100010b50f41d0f1003004500d0401654804c0c454086800705c1100002e09452007000317012500404e9408500454903181c0344d0403416002840c4404520583c41135160707041c81072410070308680d044100045807181c514010041100c140c0b070280000d104040042284031a804200400304407031003020b040032902e07135800c07001490080c49041b41c0c200d440010060045420850264803079207a4060503503 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 278624622 1250 278623372 278623451
    0x204080601050102030a0503041e0609050106061e0c06020a030209060403030e1c050a030e150c070e0f1b03070c02090411040f0b061215100807091a09010c03020106030204 75
    0x91780c07842403d842500162003403011400185a11100700444000c1c0400019000704c20f860300070403180d2a00044a09a43d600700401005030409416505242c0700c0a02000742e83c407000d00604640c04040000308074175400500c03461068080c0d030654442e49800b41403540c5407516858080d15810b03004042c0344c441d20307001d41104013410406201c072940d1036003c3e028013034882840c0e400380c40080c91500843d034417114444080030500b51440151074046a544000c0440314030f0075a0a0500d840040c182d2054408413034200721030300c072104440f15040b034004d60003580c0d84c0ea1880011a030410f00180300175031145058091000384036803c004c10700c0b0488102e9007000460380e2106804120749101c2c40c403a400c80401e01400c44000d1031002c0080e88000b0304040c030380b040c0c0b00500c005000d50142c12002000309d2160f4042c401c0d25540000d151001c1c04d43c4070850f01985220448070551401000c100038100400100c1c01c00406100790452402194090814010f54aa03144605074903401a5030b1189c28201401252 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 278625872 1250 278624622 278624627
    0xf0903070804090216170d06080d0c03080403020c1008060f010f0206072609030a081006090e06010203070c0b19030908090415030c0305100b04140c0c07050d0602040806010501 77
    0x211505540140031a10b814901030803003000c1c1d00901d40e00340456140b4500c071004101741c0215004440c1d00c0d800140e03610682d2404460031600150004070480d4489101ca03000d15401041030601a80c141c10950000d07526490103c0c60641525142a000f801c6200824001d98000100d540a41c404582c2598000851001192482d44079580d04006034404800308810782d00801d01540e442240a03d180700c1e5540310554400c8400302a66916803507030000039007483c103640c04400d46070042000814514241d02e40030005184504074007841c5001c49120300422820b0b0300800480322055803040381d101342c080e03641030b8022035600000da40304135000c086100c0140aa129109281186038400d0046040200a009010080859a680481039000700001001040d124040d00c40203601c80c1c4020706480b40350b1241e150607100090140d038029410001c0e641020203856082581c810303240524562294442a549454034005604c5030303403c1105451881d0901c80160020001d071040a07040b0350b4580d03a0744004 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 278627122 1250 278625872 278625877
    0x50a0506070302280f080703090b040806070f030e1c090602070f0902070303111204031206030203030304030807020106051e03010608060108120a300c02030a0c110d0c0305060f0903 79
    0x90060b0403078140c0d0701488513900390566500940322051441100d041d9981411459075178815107414030045981302c10154441c100b00050644034400d181014506602d280e070f1150040d181500784402c4407018000c2522a50003d00602e11900c1100d40b10034060003007400d5120018103a0340010350f09500800c015000141950071aa015640301c04100d2401a0280085d009090b0071402c241d01e51400d00c2840c1010800741c81c2d603c012002a40e161705161801030603441000915507444c500b065402c00150307802005982d40903400d400c25030201c0e5074ce05412401480203400c11907100950340c115070107040540f02d260044410540c0204484d6456001d6643c2d00e40c0c09114010310b50380080c03175104a81300e0802c05440704001d641000303104120480380c2c0031508070a010302c0d41140c020f141844080369105008203c0340f030000b400514500500102c0c018080a605600501100004189200a529450145041542c101c00340f0b161850f01c03440d02c1e07510f640044d150041140c001c074020401c055404401c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 278628372 1250 278627122 278627137
    0x2220906050609091b0f0d03021606031e05060d0803070207061b021c150518100912030b13060b13090b06191e0513140d020910031b050a0506 62
    0x11303d8004040303038a0072640300244501782d4004522036a00c8040752182058841510b120340c0140c050800800008180481c03c1d0344804200b508006d44814038440400350b000070b0840c0c8110201d0a03907900c401003000014986002404030000100300a4050b50100c1e08005803142a5100418001c81c13900c42d054004880101a6000b810840751080400f503071515a4081031081c3d1039850b410303282d00c0035102111421243c90b004a80c175204d14214507142401000310300350310280d00300301c0c200b440c1e141c030a0700145007041c48042c1076480350721200c5541e03150002d0000500c110000e012003a102c414000b550340002c00e45009401c41c031a000b14510b50740d4051800f6001026100b41c6c1042d4140070b000b251840b0140c142404c0c46000e9892013641c2c803800c2054081c01c407460b255a40d132141003001001d0b481d030341544141c030034008a450021499840340000800c00d6011034045000d5243c07241c1010100045500062180721000b00b4407100e071942150b41d00854000301c3e030700386070585c0d220203000951041c4107 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 278629622 1250 278628372 278628391
    0x6050c060109021b030c0607110105372909070c0209040c080d0906141213060209030a0312050a0203070e09100503102c0307030c02220906050609 64
    0x14801d420859028101d580d808490b0030840040030720181741980d000c000c15140c280c200a081001c0540c01c40302200780d000000c0c008108514155200c1481c400041c540107a0400c481c0d54030184100c0f40c0380800d40d43e000d5406013000398983c40b0400b00500220390700d0300d03140c00f084001c468180e8a00381c0f203c24482e07251611441a0fa01c80340c0c1c01c008650300d00510450707107401d0418000c43c003c001004011203220346611149000380c20010007a200344117002d4286a80c5c0b20030010890030030700205841740c0000240082600b4035005240c89000f9000c0c0801240d0544030f500e0029045c9079000c1d180310742140901401304503544400e1559810f03440202c3e04040480c4480700510428140000d0555020800104c101d50b402c4d1254000790818078141c0303c0d44034054640f0080c10120320300c2200c2981010f4010075a44007800c40896142e100e0054010150500c0f504400ba0740c150346443c0c03050000d84140e01100d00094104030034802c001c1810030345c00e58005140200103121824400d2495001e0361401 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 278630872 1250 278629622 278629633
    0x4060515030a180803010305011d1b0d260703030608010506010c0f0c210c080127030210150e1026010e010c0e1002030712050f07020d080c010606050c 66
    0x1010008050000d110842201000c0e42c60380f10041181d690295001c1c620540c00402c201d0114061842e00c4060360300841415040340204903c561280c0c10440d0904100783d40c0203585004c0d505082c0d8407068007071220b9220f140d660142e180c68000d40340c02403e0071842600c00b004038603203881502d402c98034211840c6010440845816010030402584504014400d182c00605207849403201c0700e2800004030303409100c2ea0100a8101008501d01c80306018000d540300030042080c020200716503260032a07522110f80143d14444000381403091141d616440d00c91001804403141200904400b050f00f80b03c1c4450003041500810b000d8050b200c0050100c404020700781d40b01e4032100c1c0100f2800716083c052040c081d036035031200d8060910f0a004500f038148940c0c071681c1218460360305000b581d40903000071108540081000030009990a8584030544144e0320700b051704c400b10804040c54501c14200d0207035014844c050000100002303007005201030740080000703102503070b0b440303030140d030703d802100c442c1e103001e8000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 278632122 1250 278630872 278630881
    0x13050c030609060d0507151704020a060503040507030614010e07050c06070e031f0506180106140703033e09030a0602090414010b0405010207060e0609010f26060406051503 75
    0x1c50090308a00001c0640604000c2d0780d803071506c0e02c0d44c0e81e40940148569460005151f640010804a01024040d412002403929600256281c4000e014000500a000c0042014031004010140203507078002e10030484d415210100c1042c03004244101c10324540d2510000c1c81c1980b00d00c0c19a1007031520080282456100c0786001d456010b0801c41054140c45808a04da85d40800041003c010f05a003440c005014100401808800e2000c20036040d2013440d075a0041202d40d61182c8085a900c00c810140c0340c981c0b2581c43c046001d051005258111010012400e062801c95403d00301802804081c0d20316490628540f03064581c09100705190341600b24064410202d90745030002c02c0f2000c0300420015510380540f5051036644402e802c4908001c170042020710565804006242c00742469081100091400c0c0001907500e206480002c2d041040082461681c540240a00140c03915492641040c991009120b000d03103102c1110f000d44210300346a000181c0b8141070310480a0b0030050007038589035a82c1c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 278633372 1250 278632122 278632129
    0x8031f0509070e150d020903120301050105030f04020312120613180f0602040f060f27050f01030609020d09062712020c1305010501180b0d0c030e0102070606030213050c0306 76
    0x1810a1464000200c2100b030509513181c18020081c100d61007200603111000d00c010b25141c0014850802d100410400050005a800030103403a0b110100c41c000e9488c640d03503440807908213041170340d40c0e080380315020440303044440381f03121858861300080d148664100301d805080c000355a050307980071114071006101c01b804034a9400e42100910f01070b5034050315065070340315031841d0038250b64413440c0016950300c8401e1074560b000c880c5c6104040840d9400140d601008495403c0102c1d501c0f41600c1b0740d241800801090b4022b4010000820700082e0454440b1144036104000d40320041d4121071641c58544511100d0382225002001043c01114416030201c00340d80302c607000c01030320080307005500c10001c0b44102c560740c050240c0c014841c1c051001c501c651405001504c0503d0000e100740001d10075880510104909109450b1011300b00700c1c0c0803c50f540c001e28180c000b04000c641c0c40d4415400007900c01c0600c1081c3d004407040320b100799500035910703003040c00181c01c889041c1e40c0d029845004102040f05441e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 278634622 1250 278633372 278633387
    0xc080a090b0c1317031902010506030613110a0f090c050c06070c140a0305040f170d05130b0309060609071107140a0b03160306050111030723030708031f050907 70
    0x881c3c07181c41000c0c0b2030311607a0040030210b11000c2d0846942c80014010602807401002c0554581c1c140028401d500b48040000e848000082c03031020600003da83c440300f40a400e80b070f540e080c42c3c0090443c440c80350f01c1350750710040031100340910450241010201c01c4214450300032030b44c103c407206014005540701c00c0411100051000c2054411035000c000c00c9603122014440b09410a100b51504c6a481b17241140c4402d9000856003c40181c02050044504164010800440040d81460201e03902c0c103003ca05010004926041544007481c0403041103504240020164010401100c0c4109241d45081d012150b0740702001c0305e41c036580c00900e0b04003c0c0d0908980080061500100b50600040e1504401203a54200b00e4414601502c4035140c0e000c882c2d00361090704040c220038a480d600d04600308203134036920702c0f072010018035110804c12008602000c0b030700820b40700302c030100949544004608001c203e1750402d8419a0003401c564841d00b121203e141020350071901d000d80031669075a640c403000c0e1780e40d1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 278635872 1250 278634622 278634637
    0x61a060d090c2111010309050309010c2f09090105040c0b0f07020d0305030718050a0e060312040b0a0f1b02091306020c0a1106040b0418060e0a0c080a090b0c 69
    0x90182600410038090078003014250203c004080c00311030b401402d00900d21504610302c28103062030030300100d01041c000b0044070742c0c00d0000c0c200604c40c1001458410382d06d200030040407111540f604c82404210700c0c06242104004411500e481d0291284e0b26103e080301d00590f4010320340c407030300d9004210402441010348a1511f8034030340d950401c8000c0e00072803a02440003000f100065800000c203c52603811035003e48924a034840110303000c1d03041c0804a0651805400341c65200c1c0d0050002441564041060000c0040000c5020b620345079980b9441c10907170400d4880e100403903510020ac241daa4031a80d59a20340b1102000c21040400c901d800b803200d42c00000d23001c02e0244003800b00b07440c007080442c0001c0040c59100e0f0000c0c650210035080c0490a950320070341061060600708010450365044070103540695013043e59400800c000a00300d40c0003455682d1105030f204a81e402004203041556000c0b0440140503140d841291b550b40d0b82c16401c40d12440c10060801132510081006c84c02a0707009000e10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 278637122 1250 278635872 278635883
    0xa030f05070605070c02090f04200301110406021c030203070c0f082205040b0108060a0303110f0601090b04060506070f110a0509040c03060b01050309070b030408190c061a060d09 78
    0x707000c81511034605981c001c442a601203210443e0702070031414441141540704100040810190400e9968403605030a1035029500440d4002c2000d0b003155401e44c0940340122071402d165545680e24a0040c0d102c2810683e0003400495002c51400c1c0a8041d001316486040d0319a17582101c40380030b0707232001440a80078400b0b5801d10360611011401860b0154a000705960744c920140d007146c505004c0200b900c659510a90402201d10b0602ca100d0300c03000c603448243c0ba4181081000c00d2182d1051601d01261641520b02c64803404000080c489802e03880340c0c00178202614248805610b400a201c40c52040200003044503140d69401c3c0c000c641490840980d40304000c01c1d51381219500c02c00074013070070002e490540d10b0554070f031020070401c0964402d25081640030b0906c0c03402c5250081039552190146d20030325650100c000001020005107004a620401c2c840d8505030070514117900041001c18444800c84040c3c2c6400191a420850181c1001117a04024600740c505805404040b000e0030783c1c0e0904650 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 278638372 1250 278637122 278637127
    0xf0b0403140c0c03070b040f0e0604091a0610080903121f03140c01030603050d08130816110111030d0b030c0406080a0303110315041812020d080a020c0a030f05 70
    0x8200000ca009001602c09003008090701502c101c03c050800c1e8050703201d0300c6d080200300010070009007421403038400c40300341c07207081c9509948040108028101040009000c2c20a585e2403135212041d100c0c84501610003134500c0c6d6800c0001c0c0500742c07200c8106903070440d081c0d0702c1803201541d640341c9180015401800d80070b8032001c1d01c450340c40016a0400c1c40e0002c032076548642e20244804103040101010351142480c00b40440c61031512100d40f10220115034904200310036002540021013070524000d000c1d4408041995008040341e00c10f55848008000c5a00c8506404146020740c400e000076609a4424800340d45008070742c00300000100603e001c1c55405000c5c03451080c01c2c2e0f550360f00c1000010144800504614109482d0050480e80041750000003074000b441400146040582034031a5420140c03000641e02004d0340b070b080d4400211000061201c00072860f0340c08003d0b404181208055410348880c9004e45903010071078280d010307000301c00c1410351080484c003010902c28918603c7c0070050741000d80c07 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 278639622 1250 278638372 278638397
    0x60f030a0210020114220b1b0706060303020c010c03022e06060504051201150501080c0d090c05010e011b023105101202030a14070e01090b0a050a030f0b0403 69
    0x1110b101c0e0444410340503075501c03c01c072031011140845090b07002110300c0d48114000c100d510f40c42d12010b01480040c1030300446a000952901d10000c01c0703203030240c0403400551180014901200501481d00089006004250b03190b01c2550154005041055154001d40100e50300c044002502e07140070941c9004a06103001010f2140380d03144506405064684d03210f50f540c9007048280405d04107031b610b618010703a140181d0000e295528040820503a602441c08030511f480f00284017041e4005d001d80ca180c11172500540704204030440e08010100c1d802a01d80c07900c80d400120040d02e01d2149219420005051a0b045c04018540340b2f540c03d00c005107964201400c41004c50300784000460103904003080390754038010f0108960301da40d44640180b1184442490101180e07020903141c0345055401808a6508202800d03e82e40c24060140038001c040100415985e403030148001400b03040103001e006115141000c985406e0010a04007a26000000f00410000f20768403c81c1c002400ac10a8040044001e9500c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 278640872 1250 278639622 278639629
    0xb01050918090f0a030906120207242711120d02070509010b190e060f070c0e0604090309060f030b04090f031101020405010905040e030c1203090d050a08060f030a02 72
    0x3001d803285140d00641620703102107054034182c641c00032000a54014520311000940c0b100e004001c0e5a0340b0701e0402680c0780000c4090000c3e00501800401c50707142030160841c001640c036901c002003000d0b04030a0010b004800c50700c4503c400e009854104000350451200045800140d281728001c0000c0e0940c0b021040d0fa255203820901e041c091200180c01c6943c1c00c02c41ca1915841c45400b40c1000031001d4500140c1c0c40c0d8203031200358420500020310421050540b1030360344030019203901c05203034a80741361f1302c904501d0020011103160054514080d601008150103007054803901010300c1c1d164450000c0d06042c420261500b90500002d10200754450403107002a40365401205203951044141900030816440c0c050420603460507a000c440e88144820002c913a0300c00b68a108580c000d0f038001070522700c41c2502c541148141c0c81d20101621541b00b8600d47c01150100940c0701d11001c900760f60b100002000f084a00744108099400007031001808110f1500e40340c0d4050442110040c11505d540701da0307070b021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 278642122 1250 278640872 278640889
    0x30509071e17101a0d030e180702010b041d0606060d0609090f0b0601020d0e0d08070503040b07020a09050f01260a080910030e0d030c09090608030405040b06070c090b010509 76
    0x1442083d0420400015042460300810300022000c2ca03800a440d209040480e840748815800030b4100000c003184251a0b88079a11103803000c03192450f8a070b034070313182820300a400380218849c11400b46182c1414054010000c0d065080085618070152409450b84010801d29800280300c5015255455a0001e00a030240c86150001445403000f144500070341d042030b8144074001001e90f0305540001600b24400c550120a12040d62000c641116101d4124101812940104000280f0a10000501141d02c1d54100050140b007071007140c07441f4140361542d40005c161002500d00100280a6400611030000c0510402440400a070707030401801714583e500918140d060b03101038440b900000340d5003100e4280304884d540c0d56001400c051081d1101401c41d61b5030b81d02d000c0b0924041568501101c2e001c503100e95000001001c0c0d00c0c50900c103458503110940d45962252040324400c0b86000208001800c1c420107668920380c0042032100c200f840c00021001a229100c0450304100d410400c808582d50740d10741 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 278643372 1250 278642122 278642159
    0x4060806120d08010f050f0f090c09120f1603031704021210060920090d08040e070905040c0306080c040b1306090506030c03071211180c0316030509071e 67
    0x30365048135454000e002c4586410754200c0d03405810154192000c9031207000c0c1c50688102d054031403030155941c0c4c25281e01c223800386140c3c40d40d002118800300c1c10b28400000d00b06007000c2121068510304101c3c00101000b90f00e00d4803004020524421304e14111043c5843c400da4014000740901c802507231512001d40c10480343c5440c1c00d040694811050020224500c10508080300014902001d82ea08680d2401180600000d441c031468000c0100c0701013101d00303404d603001480c800882002e14240030101600b6065640a000d006600c0c207a40490018482e001c3c110449090301c0c0a4454200a1010301c406820b1655a00f074000101d00251104030207d4800c1800030824504005401e041985c101420429410442c520079403210400740900d82c82840d60700d8425511407200150050103101041c000d0f86090f0781e13140c91400d080204144010090021032040d6500d02c58410303041a035810990031280141e83c0728080354030820090201e40c0304004551200c9503c107646d40c090b2952682e01ca2500c0010b0032 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 278644622 1250 278643372 278643377
    0x180902030708161202181503040506150d03120e06070504050102070b0304080f030a0b0306190c03050c0a03020705010605060c0f10090b0a09060f050c180303040b04060806120d 77
    0x1080180c410b81c00940542c00112101c1c030b8801040c080c0c5402030001486010010001d640000c1d2031514980201807032410140203007041c2c492101070b19039410395400495058900d4020400051280914030005503400304004290200d014100d44084908401304034601031039503070b1400020f180c01c104205551142d50b860351029a164100000241018020b9008a416900c01d005120024030420300761680c882c86610100c3e121742d076070800803000d0855160180d406024800074400c100601c403021042840821406000f01035110701d048084820031100d28403204001d204490100d4420f4000f07244c2c041c0110008100d040e12100091240d1380200120710701544000c0c1c09619000d4240444a195203414070104a140304540b102295080010042c4582603a0b81c000c0d9400c00044e544030400a07141301404121a2810f001040465070242a1052407140101180c0d22140340c00000c40302520200450300707042c249000c1066443e404041d01d243c1e4440015004904601010066204907440a5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 278645872 1250 278644622 278644627
    0x19050d060b01050c060412170910020306130f090614040506040209100e16140a1b0f051905120a0509090a0e060708041721070e04090c080f01020703120903180902 71
    0x185003c1e101444441600603260a01c0c02006150303103001c1181a0070ac002c41b1300241c0d4981c0c3e440e0010380c00e003c2103070001c50014502115510805020b500c2210303214401c080820403551009400d07100040c040310014050341c4000009001820142112600581400c1c0701c1c80116846400c0c0f400010030032946040d00020f52803d40d5541a84130342c1e2071004000600c1064030700410308a00801400c4079401003030b2a010030140090402c64050340844003140c1010079666545032a000140810340443d1082c0ca01e0320031140c21941c6640c22100705c0c0c10700312580e1580c0c1c0c64202e080c014440580e0005000302d681968449800034500014010948142d0f0a40e541c1c42182c5400c1c50300d0000d014181c00001c100280600501c1401003400c044000c1101a2040b0440541d48500c4110745003030650b05420740150030102050f041020001140c42618512010340e0382a00c40e05082500702d025141010f80023424003420791842e00d03026441040e2031800303442c03c09030042d0312030740c60002e441035507004a0703501e40d00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 278647122 1250 278645872 278645903
    0xf06110c0405010f0e071403010803210601090306090615030813080c0627030d020309010806030d050f03070e04090809332209060519050d060b01050c0604 68
    0x3440002100300c0111010071080d4103140038045160b80701d01410140003603140105e001c0700c2c01000c1002c0c5402d07030000d0596480d030f110000300b6241d41001820501e216041c160b44001c03184401d00d5644240c0040c3d562010040c03450b220440501310880c021346003d0f0b40c4403038040c041056019582c0245000d407500721b6641c0400c40c030418441c91140c0c00b000d07041d003000e00403203000c5ea114811919a421040d00c0f880c0383d032988103081e58550ba088452a581f500c20740d00c141303d0f280d0f004000b40810443c240c030340500ca9030700c560905446244101c070b10320000342e003000406842014400616002a0580740101e007071440f4801240407034240a0b0181d0700c1d61808131f60000b00c1d03c1c000607064211445240c0d4031707000f40c880748840b500f00342403c0103a880041001c5034018071b000f0103000f290100c4a44100080c00c0903aa410b840004000d030b400741c0c0b070107080001403c0e9802c1c0d0343c10761500100e400c082d002c3c80721103010313031a540010620004e42a04201c020482c05424442c1000a50b0150b40110303e1078154855 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 278648372 1250 278647122 278647157
    0x203040618081c020c220f020f071b08010c0528020d1115040605010e01081209060a0509131d010b010507230321070512040f020a0f06 59
    0x60940c81104000710a0621504501180c04032410b290f0010441c0505182c21059007007413442c00c41c85803c0755081e08050b6504d4104800c0e070441c5512082d082042011b042d6504060b4804d01c080f1100002d82000410001860380e00d240a00c01c54030b8400000603601d420340c40d82503400c20078049001420128122100065101034050540c0300328010500329800d103280a522821441c1008092000d04c61807801412020311071102a84841c600061480c40d00e032070508003e20017030080c4000e0001380e00001c113040c1c900083d58001241018001800d0540400800040780d103d85820010001e05020a4849071240da1403e40902035181c000310b40b0100c0c0d40c5052a8034441c5102c9418207a040090404c5203903000022100c41503007001c6c000100302c0c41c4410b08164071940746107422151200140c0b0042c0e405c0441813414400c80c00100300c1d201910381e16406c07078641c0940e000c1e512800c0c0070318001c034000519208c0b076132881520180c04030f80c085a031041c0070004400168001c0340820b41c040c01000c400300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 278649622 1250 278648372 278648387
    0x1082d0c190906300c0206090714010203030a020a0318050109150606050d0917030f01080f0a0209011401030f1b09090207050a080a1803030c02030c040917070f06050702030406 77
    0x203807624054160314544000182003801c4d412664510710070703203202c030b0344401000c0312410800040aa002d100c128805a002980e6183c200d8030680c890241d9203010408a61030300c3c21522100050b4010350031a140c16800300025805015410141a1303551920880f100741d50300b280c24480d005000024890200f41000c13140c0010f4180f4000b4058079111041c04855002000d41d101884080b000050b018502d20740743c10414803c0000210420340407007001242e0750042e6a41e4161000031040c0d03158218141402070361004082d130025807110030480180000d134400e422040c400c402c141b40100b00300075400072042c1299407a00301791100d0002042c4000e102600802c400e0024490520214035015280c0c030703030b80d441c0c0345564801440c6c94400034070040e031b0300e10440b40c400203c2d060f12034610180e43e8034600a803c91a00d114124000c0c00784008550702071030644a401425034100c00045002c5030350140c003403003076441200b0803140c800540d07603180d000c10420320580f4400d0016030015075541342007140140920 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 278650872 1250 278649622 278649667
    0x12402010b09010b0f090310092d0b041113020a020706110a030c1703150a050d20030313080c040501051c120905030f010605010e040b01082d0c 63
    0x168140070a219107a00e8111030796046568a0300d1494944034444414440307880f5103541140d00d807103172a40406150820742d000c000001d100c1c4d40e400c5801604116000f40121650b6420761120081d5042840418000301205038414410703811000821602c200003070840000c4c2410480940c0d000c20030034202e50701008640007501c65414507a81821480c548141c1d6241d400000500f04144000003404202c0d01c182c86c54a00b40306214600c2d00c03032034401d1380c01c044008001c200780d208050648001070b0034141482800f1920b45c001162445d031210ba03600251500e030030701780901e4162104111001a060401140c4405000090701501403c4400410401620811f8000d14030840c503441702c1c02d404400411010b080240c3c000400890b008041c101641c151005902254050060700140300d032699041d400007007552001d80703a03400b03813521074001c0c0421684c11010650101d04a03601040e00100031988607200e5078002c0168400701c4030b024070114429042520360b2a125000858041d0000c0c2075190000c2c3c45 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 278652122 1250 278650872 278650877
    0x70911160f14011509090305040b0a020c03011b0519090504021201030c050303090604090b030a140d020106060914040504060e0102192c04090f020402031e0903130e070e03060124 78
    0x10700350344500482c51318081c0c03050307940b000d50300c0c445281014090002d2742c00030200c4c0007035180c81e420b01038000394886459840307140c400d518121101002c0046518203051404481d03543e01c1c2460716003003080c0701040c50124100248420300100240a640360300003450303007031030100c0c24040c1940746141031040c040040d0412840b90b003050020309880c4d15080142c0f011544c1041001c00c44841440101382010007000000c1e0207000c1c251480107211200040c401058216035008100b0a0f9503030b0b80c100d448200d01c2c00f81c02c8420240c4140403416103082c2d008a60041d00480c8006040354a600007107089906c06014802100d88410710000c40981104968006154441c040100c1444120340002c20704200301f10680310f1551500341c9020711a1440d01d4407082d5501500442d0340c0c3c2841d044291403001040c0410b030400903804001020000c010050b9600101c442504449450030101203c4101030010f103207004001e0044c2014a540da400c0150314002c03c809a004540e40201805e551440712910010909 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 278653372 1250 278652122 278652131
    0xc090c120b0a08032205060a080103030e040911010e041103040515090604030519051b100606030b0306040b0606070506010603050a050903130b030613050901050601020c1002070911160f1401 83
    0x2840d00130086032880c02c210407140d481d018605581c1c1341c1c00032854201ca600030801040b900340250700240c2441c180d03070003a100c0301e100000700c01c10042070b1200c42000402c00c03002145108115405401210540c0000a00114280b0604035800f092a00110303400d50b2a40e00c0b0840301040c1040740002950050100e0010b00803910701510044e1052203090090348140305c4030041290510720078029200445604420340d100d2451000103d80d5807905545101c00c460300e000c0c40020621b01902c1800d400d042c0180c040d21650787c1d44d4032545c010714002040ca40d00207000700707c1000052020300106018040c0d985000079541018892081112401010341c80c1c10791080010180d402c642041e1101150546e40082e503880c0e441d000800d240e80021403d170b1500c00e007828103008a4650640000d486140c0a0342180c440e02d21034401c001c064041c7c220f0f00320260f046503030140715181c0c464102d581c400da83d00070700a20301018000c078002e62a00b01035081d108014501807410402581c403901c1c0b00805203900c020700c03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 278654622 1250 278653372 278653379
    0x30c1c080108121806190309030306060e03060f0903090a0303030c030c08091b03030f0c0a021c0312020315060712121e09020a0f0e1e0c0301120c090c120b0a 69
    0x1c200e00c1090320044c15903c640140050580d0341a08954081940c6d0302040b110060115029024001e80003049007c40c0c24400d010031000d210300102800c20400800170200c54840f1a4840d680b6403000d01805201d000410103810a0348528010b08000e40c402c0d640043c0300346801d14004d04a403142034924080040b98414040030500010724122a501000c000180c203c00c04000a031440c4508414070300c00314408030f0b00341004100880c0307120040b402078602510700e4a00340742d01ca941d43c8145400078081203154a51410301e16003075001e55800342030b00440680d5400d240300015801e4204410440c1e9a50881d901c020116034072070b006403699500c5031401e00c034500054090a040400b81d4811014045e66004035906564822070600c1c020309103086880c5645440307400d59a5000d0381103d4191310030020b800d0049003050407100b1148110f0806403114196400d207094081180007484050b50304448844020403c81c50030320404220105a850f03208408015214680544414090044c440c03000b0001c1013 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 278655872 1250 278654622 278654653
    0x18090614060306280906051008011208090a030b250516020d020405010b07170a02060112050f0f3009010309150c0503061c15050702030c1c080108 64
    0x5140000c04641d000d48940d2100040780050750750700700c4d00911400c0e08502150130180100c8036810746a121200b80840c9407a07005002c01050605044d4000500e00c0300108002041040c42c607544038841ca55903441d003002e070f00c000740d00003001e03401c141c0d44000ca40042c451401c50358900044540c1e100e03c00a4800f800c4000041d14038080d00d400700c40012030540c0410110340c1d80d142080b00e4076600070310401240d43c545000c0b0103950080241102c5981d00d40414101618103801903640b8041d8990040816030b0a080751150303a210050f000b201c051203420080d200c050400d00c80d940c8c0282c05c100061031018440c401484074105680c141c14150244d207165910516407100440758150b8003800c010901018620300034554902e80a13a4800c030b40e00d008030048003964410300542c081d040840790200b511301d11401c202035020001c1c0c401040402100b40248010318907401190b0301c20b2150042c0e90074034000c1600b6a007810703107583d60b007101d00b0340d0301f01e080350b84a400241d0320303000d010f03094010040d03101480038a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 278657122 1250 278655872 278655899
    0xa050132041502160c0e0405010524060706020906181302070c090e0a0818011808060f10091103091c0906030e1903121d0a02090a0912180906 62
    0x12495090700003440f11071130070144504108150340105010102030780c1e8903a071084000c00340ca0448065013804045403c00d909140c0204004e2610140000c8000f0013508014283d44000c6007110075540074028944299a01c60251020f91508903000c02018002801c014808000c460440c1d243d40c1f041c0010004100340c4911882035440381c040009001c03003d40d0034280742074503502d4010003c0a000400714000728255208415102c000e89030703402c00240d01c01c406e0380c290b00f0a00032a0782c598852070005030307080381e030304c10305a0050f0b80000400b500e561110b065006944076020252011500081400070f41e0400304210a424080c1c444060031505446100800c2c01c0358501c10b10003019100e801550354140240044240b8102c40032010601d001c403464064034101020507214a080e25001d580740c104280a1000e007030200001d000303001c0f8102550701300081c200e0301400315001da0b42d40320381c5080000e1120390848544049525946417007506001181400109070b0410004d5609242080141a041030745 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 278658372 1250 278657122 278657153
    0xc0405060111030702122b0f030204060f08060a0b0412021c050706050a02011b090602100b030c130f020d05040b090f060c031e01091508010b060301170a05013204 71
    0xc01494481c43d941050745030060040202287c000251520045122040c0b82215452040d865000c0b000b64520010340490083e4407072a00403c0022124810340340c45003003800d900000080c5400c920300d1701d032010800d540c2c0050b00000103510b0100b42c0b000a5180c2240c105c88030080381009090911420398606803a000184110360134040c000c0b81c0001030314004c1d044000c294030728150001c81c0e2003801c50b006050b90031512402c4003500880901303584681c040d01402c180c11001500928055840ba0240404c00001000c0900c50701d070307148500e08000031940010b190b5450340c400003081c02d04050403e8a10210080c0c0042800c1c0e0021007174030140c0c44e001c10f00b0340d07000d8080c0c090b0940701e03035407109150f040704052180c0424940441001191500c940e5102c20b50318803807410101241521000c04c58200c4103c2646994000018001004102c0421071242456200c8609039540c42c1c80c26501d16080d40e5001c03c102c000c0252902c0c1c12081c0c8800c04800b103064280700040b02142c0d044c01d44900b02410340144 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 278659622 1250 278658372 278658379
    0x16050a05060306010c0f030c1101021501052206030501091e150213050405040c0e160507140313180506181305070b040f0e07020604081602130e0c0405060111030702 72
    0x800259113a002d017000000312600710310000c40e072100c1454000e285502000302250200f585c40c0100505510025003900c0000700c80c880e41c0a641d00340700401100700520080312020386180722010b15001c0c22030140c1401144500e001040f094801c0c5000c2030388019100100840086c164009008200710541125045200f41801a41c60b04040c038004c031031006a411440c1c01500b80b4051100700854480e075001101c40702c403500f80d02a00c1c0e06141400c0c1c0081c21405000080d030038001c04c008960320040800d005101002102e00d401207010404038080403c1d4400b80c0d060f91003888001d100140340c02201d610100c00c0b11549c070140c20741500e500040c00007401002841d5000b05180c1d0400001b002002c01418400f480320b900d9603503c8102e900da2100900804c1060601400071881c1a8000104140560b904c0344040f401c1c0350300710750006080c414043c8242da2080c5503440c40240b100852180d968160391050180054010744024070040e564042d115a040010002480714810408025201d144c1e9045 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 278660872 1250 278659622 278659627
    0x1112107050f28020118031809061205010c05031003060509070b0315040e0708120c160303030e0c010c020108010b0d090b0c070c0b0702030307060b030307050a0605060316050a0506 79
    0x5030001c44140c040d404680010714000240c100c5504030542d10180f141150b07604403881c81c20380d048103c0c00e80307a0003c950826844221800c0b4002405196031000c41410629200e0201e41d4405005040d19016400000318a50b000c0c002c10501c032082c000c42c000c0682c281040b40c6581422446540720b02e200b40b02c003510a41d07403000071074400d00c41813148000420700010f85035181d041c0100300e80505248034401510451030020321014051010541703104844000014217410b244084001d95280d2282c21104024000c0a001810550400001402850083d50b000410003d11000c00340742c42c07120300c403841c18000885400360060f81c0c000400ea054803c011401c03501d80361400d07010030140500d81c400a040522020402c1a216000d90242485901401928040c503a44e800d100c003151041a501a425030800c000040105040740c02211800102134222440c1040584419081ca05490411108907441e2401d00c0040c0c0f40411004441000400c5002d840da49040e0020f0804074044c400c1c0d0307001da20003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 278662122 1250 278660872 278660881
    0x60f0206060909010914010501090624031e060602070510030b220915050a0507050304050307020105090a0e0a0501090e0c0102071707120804060201110711090c210108011121 76
    0xe405c004042c2da402265110800b00c40107000f4043c003406d00070400080c0c682000003d0b040750090101c00a036010b241031181551403040c0880c0a0300c410120520361490b03941c0c54400860042c85890010459a070141050768104000c215901c899080740a04050900c1c0c45005290782c3d1210304400102080c036060f440c0d9410004800189c440890050101c0460445501c694075032900b00511640c554101003299940e0808240e869000030740c0c01808945c400c0c070501e001940500020000200002c20b0441c03040d07901c480c245030701c2c4030440f11010083d071144010000c48155000c0d00c00340c04403040241000091041c0002d41d1016603100751001446141150803111100b84500030240c05907524200b1001200d0400e101d02d64414400c500041d842c2054003410311200109403402507900450680302042102c0400803818009000030107400d00c100505806080c101c8004191800710300c4100360030790b141110345400c4510554691041d40020030107110404485008104400350407102007140380c55 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 278663372 1250 278662122 278662141
    0x12060f1a0f0904150e0f0d030c080106050d111602090a050106050d110d0c05070314040e0a0203090c1207141206041e081315140315060f0d15060f02060609 68
    0x110745001c03641d034500000d401e000c0e000400d0f0b14610490751411503d031134040d803400300c8c1100c4e0140d084800143e540b10041c00718038031440081009442207240462015030001d81d4006551003055080e101b5180000f120b011428440d140e2940041800401c1126624065000d007440c4160729410080a5503a160003a04182038000d40c0c03403000c00140100700d0170802c000080c04a912016007900031444803611103a1304040e006c1214180c40443d0b110420944610050364003940015050f4003c60007030142c0b6003025250003004242e84030080c002484c4003403512180048841c1e01042c2035010300c880283c40d1000301400160f05802541c840e4084880009000d400004c45803507860091881c00001004155074020100ca074080e02ea803000b1542c0c4000307186406461880c1c40403036070443c550040c000503e480340b9140c82c003100014064400f502c0d1403804e2003404096404981c007030900594640ba600c00080100e041803000e4103d50030314204d0255190300195941030000c0a2910030f10500e8005202c215 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 278664622 1250 278663372 278663393
    0x708100c020f06010608071409010903122105011a04030b04020607021207030c140603040317060d060204030503030405120705150c070f230a031209020a12060f1a0f0904 74
    0x915000030390b20f0310b507114000200341c07810035030305203000a41076540c01c804404594100c03141244140c5402401a00d150369840703031071080d07003068400e002100301c0700c0132041038600d00203245002075800000c2c06d43c1044203000945158020003c03503100284004d0000503c1c10a807150040c0d0115252600c071001403000600c94205030300840b18a014003040002000b02602c0c1140c02d135182c04160040c40710380002480138600040f070707014001520000a082041c0201214503401102c081d010386102485511800f00781c4c0c4c0590720844440c2e100000301b1060141c14815042c0094442460320f19003052911510703510040d07166803483c0c0e03071040d0010603500e010240445041c258401c52120744810035007032101d411812076011490903806441c0002007584041145c1d000c1c1603041d11241e0342400f82e104000c005203d2890220380204281d000400c0342083c13900c0f0b00460900c22007000c6450181c041c1c1010a49003a03000400e55043d04e806a510316a441c0ca81a409030a03082d55107042581e2a81411080203 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 278665872 1250 278664622 278664643
    0x1060803090637030c0c11040905030f0c070e060609090a0b011209150b090910021608070507030302010b1507020405070201110a17060d170c01110d0f05090708100c02 73
    0x3410980c860b43c1d44003505142110160600b43c0701000b0f0f1195a031810356a0248140c0b0040100704401d642c010780d45096885600141e00800407a414800c01c20749400c07642d84250108460b41c0c0c01882c0403c1100c8a1484242c1c1c0542d0070744865080c4103881008c03a1507540094a910890342c0c030741c803403e81540d12070010340c1411030305c46105010702445414282d40c2c103803190007100d2416040c09d10800381403d00140503401800d80b0300060140c8861418004000d401211403810b20481c5c91468001181840c03000d0100c0902440240542c1441d40c07401170b08482c110020740d8054400c0d2001120810500c0d0152a80c281c0c0540b0042820f5850250403801030400400794001c800000c5010404a544100c250718549061130640c01c3c82d0b11000c00700b01e07c2d81c005100003003211126041e410500030001c000b4081c160351a2001003000506e00300c40465940041c1d0000c040c4c19680c400780c610103685030080355007091000000d024460308200d03038140c40e04c0746c0c405000c440c15111000d1440c003a10070403105070381c4d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 278667122 1250 278665872 278665927
    0x612020702060703120f05090309040902030a05030a0807080a110f03041b080303060406090b0a05040c1101050906070e040b181009060b03070201050c0a1b022d12010608030906 77
    0x20343c901d034070780904001c05011041020500e01105c02011807442c0c414140a0010b5400840c10078440b138007000003800103801c080360540038a00e044e10002e9403c01c0540030955498480401601d0002e03402001036400600e03c00c200b80c10202419103403540702c01100c000c18004040c1030354980e41c0f4141049550040d030081c0502e14805407000540610100146000c0d281c203c5090040554444044059404140c0b18690240c0d50b0f003010072043c81d1a42c000b034486102801c10312422100c81c03541c2c0d070031103104544c00d01c07041d0004e80411060302c0d80000e081d40320090441d0100300140103903010440c202d1407150041a40007500c0b0105004804c1800000020103088809004880c1c8070041b440d002e42060b0f4040740550700f01000301d0700429018080d101c5200d41036950301c00052620145404040d1103410a980140d05d00100d18066244c082c0c07040350030003131042d5142504140c0024070800b50102c540103441640341c1481406085404030460380900d0049600039100d80401d4003504030510287c642158 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 278668372 1250 278667122 278667127
    0x913080f04050907020114090d20010b060a020709060e04030816110307050c090c04080a030c15050103050d0807030e03040b1321060b060415050a021c0e130b010504061202070206 78
    0x106a0317415041804091600c000c07481c080c4d1244401d4550303c954048030800072a2803135070005050307480003880006c0c251004c03001040660001002c544550310100c0100016008400c1c140701c03424050040000810010340a01c803949040c2e1002011003074083d02c00c3d40c030f034454a54281c100e41d110f001d03003003080c009000690b50341e4030482c906245c1d50b1142115a40c01003400c0800101c03030021841c162021520704201034540d49240b654112541c2c04042401c417801050800e4502e0042450311442d4081c3d40306000524580d90b44441c00b0301183c0008141104240c01d00c094603a54420110640d400c446125005507200d59801041c0020482142c00061000c0030181e0500e000d8032000b4800c0c00c54a004442c06c1020700011000d1082a11460142c2841405018820319070144035600411100305144159600030000b162080806c0e468030f03d950740050b030459004191131900300d45081541d25468400c02115480c0c0001a04a0107503100d0700041c80404c5809194040c0c0c1901200e921039401800d099 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 278669622 1250 278668372 278668381
    0x1008030d060303080c031611010f02031006020c0f0609010c020d0503132606012705090706020f2a03070b0c1c050a12050a0902040908030708060913080f040509 70
    0x203125502c025400114078a0100c2d0b108007040080300e0040c01d0b500c900d040d040c006224140d804103005d07154030701c05660b0f4201c0c04154440c144081d600500c0040900e030880751030a5002450541c6820400d0300c01c1c840360020401c159600c00880712024400e080c12301416015000040d01d0842881010704640000248400d405051241500548100c035002d4841d4449104c10140700b00070700e0103100060b50040c0014085040400000c43c04038104c1c50380d03032000c914052404825200b0035034108a0329408240c0a000c245d030140414019414000010451440c0c8440300e000c07034007502600389a0100703407007900044580b020b108000c040c2202116940d650303103001c45282d580741c0800700c40400c18207400da19051090321a0048440c0440329566000c0840280ca000000802c2d002c2e0070f030343d0003d81c0c030300080005880c1c2d802409002c1d40911380715512850000c1020300700c08801011680716450000030000742203107840482035400e030420244d030f440b54225101d84010303100b29088540c1c807015030030070032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 278670872 1250 278669622 278669647
    0xf020c150103020a06020d0206010e0a0b03031c11120c0702030c031507020d08091506030c22140403080f060109030c0b03040501291306090212150303090906010305100803 75
    0x94101c2e0310a8640c04482070b51490126140d2020380c1c50030340140c0002e401000020b02030704c2c2058000303000c80030018224100c0720001345160321074000419250303040000c11031a14001e00c140301c4080701c050300301ca1501c900d0414818080c04014a08035007000042510300a640301004a600c030800068203c400c41181110348402c04401140c50000602c100c00390440028812500203002d0f5020310001d00710701c110304500c45c0c00141d004010030307094800c4040d120303d03964407410500c1c10303480c15803070a0182c40c1305100e031236050700c0c100c1401c00348080024040c0800644e200c0403241e8420302d82c500020303103a120103004a4004540740c4c00a0b18498000301c001c204510048010744c0500e2140d402040f41110145809a4003000614440c905421580c480100d0b030400100100c000100820001040c03a04c4034070640c1280c108454929404000100304418021408039401c2010812030045082550207000a00000300081c402410181c9400c0890b00b6000a25070310409040300c1415030341c48100d07a10300c2 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 278672122 1250 278670872 278670913
    0xb09010c150b0a0f0f06050901050a0c110907030e06010b0705060606031b0f12100e01050607020105072001230904180605090c1c0c060305040c0b030103030e13140a0f020c 75
    0x141e40e4043d40150001a00500030f2042380d04540068642d641003100710704040c0c80c00003000740b0989425804880c6458540d44010b03002e4441d14464500041180c080c10b2003600d0260140c000480005040040780049840012025405402110815502d59a514500308810f070181d4101c0f205660216690581440c500c0c041c00c00485004015100703a0f49402c0581040c0445101d600f0001034400010301c01030900b08014241e140c0181803103450044507a542e00010301071142d0848103030070404000380803980e109001c9203190658458240940400c4642441a071094140703062150369150078024012902000746201250885420000392404c0406103444841d420b0715140300303400001c010400031018031440c401454201d000d000c4400d0520070182d004040140064a04004564000591000358002103010313504c603964614444c4240c6081c08402120255042005403e00348900401d110443c501580488011804200b061080b120840240300d5070b4120301650080101d82d04011007480304 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 278673372 1250 278672122 278672129
    0x21204081b0f0f04020a02010e030d0b0f06040b03060f150c070f08010c08060d02040914030a17060d06091106070807050c030c030a080c0c1c0c0b09010c150b0a0f 71
    0x11206018020411814528001c505a403003e04507907208058201640503000c20b41c824000040c4420b40400da062450f000304000000f2603403207130b40c080343c00c1c14558010039054000380c502ca070400e41809a841f10501004010500601880c000c4068076910b9112807002e07640c1c00120503507a808030315040d50b103400300c2d8000c8186440c0354900c0052860b505218502100525a40b4101c13103032185400c010041c4052032040e072740951910000c40119505080041d03c14003075500441d80e507012654003801c46203030340000042d9406003408000c920b40b03130038000740c0010703602c00c00000e09032080d450300c2c80780402d00b081442e40040010810340308105c0c028005100c00c1d07014004136a005c59421003055550f0590841141e01900244d404800140c502c8002c1c03d2181c600005403515044020003081028030700c003514600d8a8803600d0503505011928400001410161030000e1030800c0182c0042d00024007e44d00800404c901d64166021044607444440240070080411a031241e540e0000409140a1700 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 278674622 1250 278673372 278673403
    0x509010306050a0e0c030a060f0f11030103050f010501210614010b0711060f090904051011120708010302031e0c03010911090705090109051e030109061d0307080d020a02120408 77
    0xa504440d2013000094200d41c0410080042c0880904c9075554406000051084102e9a03212201c1c4c12000301c0f10302079070202c10342d2072040c0c0c2c2e240d62450903d1450040001c0c002100340e450b04005002c0201da80f0181203418002401500c1d410156103030810043c00d026400e440c81a10f980000314005002ca80100f000c03c0c000c6006e0902c2c20408030400005104441081d5052241004910194181031940a0f400f80c00752083d80c1c4243c00040041e400e0325840c14161050b030000148074000c840c041c1c208180c21100f1441c002c0000e41c10b60380482e0340c4410740165800c0e150702e03071548090040020082d408003204050001c1c00480708501e1710040307242180310081c0c841c1c0c000c0d000240d1911702c103600341e03a8400c8059480c490820301d08030074048410200064074650030102c3c0d518030540c0c0c40901038840c03c50311541001403000c0c101c82c80400d2000d03040c1c1c0500269007041014602003000d0390160b541c0120215070060391900340000c16440d1400300742c80d07440e49190100d00090300d80d101180300700d503a035002c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 278675872 1250 278674622 278674631
    0x6010507020d0b062d040e0304030b04060207060e0c010f030b0310090b06030706020d0c06090807020315010302090108030f0d0b030106050a030303140105100f0c081c02071101020a0203030417070509010306050a 92
    0x402d105e40d0964500c002051310454500403001c00e1a00e90442101201e247c401c1e02e24240d1a5201c805008408490984135140c00081c0942000750300d1082e50000009100900b02c644200c0300020088841151010100340d20b40c8036603002650240511140307446001d0041043e0f00c1c0501d0300401c071031002c50700503119000711140000c10900100e565401a0300564400c251040319954200041007000c0003650744000c01d00c95a00140c40400c1603124002400200403a81c0d031440c030411246c40e01c140c1001000381c005106021a001550040d00d40c1c0441545004c11005040008a8010070413580810740c4034003280b90000c24140c055111150040c0e0a51249505030780f03500030702608404079101c810000d8154030741f2404080c45600c6494405118185030342c508208290501c50820101803c141440d45c0000c1c00000c10401805183d42c600c006c3c00a4117584044c2c1d00041e80b207009601c50094440c0f602000303502064000d10848020f445c00030704107607a6517168108000100b42c101c4042807580d00c0d2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 278677122 1250 278675872 278675899
    0x32a110603060312030901060b1204060f022104050307020303040b030f06010c0b011e051504060201060819141504030503073c031517070e0c070b06010507020d0b06 72
    0x40022a40b00b414064002e03e071034041030f07030f42d00b0036603000412481c4076540e14040440c0c5104c489008048007a54840d004981e4202400e01000305c0e1074140010390414070400c40d050103244012081c0388208030300c0c80f44d8405656181402e0f404d41c81402c0740294076000024000c21800e0007440a9401a078106a21100035510040155039080c046240542105401e500400008502c1e00185032441c00000380520b0865851000c5413209844640c2c03440804004a02800107035030905c900c20050101200070100301c808048801c0c800d003800b40e0060010080d5501d201142d82e42040308181402280800c03031160318081c10000c09030b40065502d00e00245901d00803050b00000340c5008142d2620480c0c00c0c040c03000d041d02406000c0c1188240d02030a140c6c036440c20b04408044405450002c0c40441e111583d0304148201890901c5041e401c0307011030340c0c6403200340b0900b80300f0b44056481246d402074240e102901c0305001a1401d02034008001c1d0b001c0200000302003080130034000315014500594200d100900d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 278678372 1250 278677122 278677129
    0x5100504140a0f1707140c030d0203040b072d081902010b0f09070c05060f0f060a0b07060c03060e04050d030509191e0812090706030b0913032a11 64
    0x701a02c083d046007901c0c55000013103070b08840403451840e000d1071418034050280d6680d85880154030100c55030b035049151501d0550906204a440e48007072032024510f01420b00d5844040341c0240000a080c032150140144103038103007011010002d210a05e11081d9103210b07440c00342242c0c0d01c203042940408003442019028107005000e0003074608001040da01e2491007401c18044042d4004050004200c0400d000c10003040c2c00303100d5503001d10b04079000e5502d41c1c41c0001d581014032001405a078000c0011040c200041071130103081d14006580040d02090390088102e045002d8011a008103d80d041c244061000300140010400341030107160b1020b00180e5500a02142c90341120709100c01440c000c00d4007440014910b0b015600d10406200b501c1080d400d040c0c9030f103092a00b11132220410710711501c00b404182c16007002100c008110328070703090040a5081d00170030f0321001c010300344000c2121000740010070036004d8074401c80120680c906000f00e4103070081180d01c00c0c0201140998134100c0030b428080c0d4904 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 278679622 1250 278678372 278678383
    0x2070203120405060a1404230301140c03160201061503021806091c021c050f1b010f11011e060f0e060d150207021906171014010504030510050414 64
    0x403401008907040c0300d000102900e01302580c0c6c000c01d0002070104004540c501d150113502c50361580342210600740e40d05400a05007112a0148a40003a00007801040103140f12001202d5001031792201c100202c0c3e508010990141030a0b402c0780c88800604028101d619a0590142c080d5402d0b0100f6070342c1c452509000c0c40315a1184030383c80ea4100c401d80c1c03130070440c070100340502d02c60481c4050040c8c081390180800d10300c03458000c6402240e01e034100c1e021095501004012081a03500c0402c1a07041e07108580001a1240650104020030b0000c141814220017901303502c44600b91040300041115220f150903840001c01003030040000d8442030341004a13585c600b849040d03204d050080d01c2e1070008107140d1110b0111501880040ca002e9400b081400b00588500d555039040300c510200300c6c00403600b40407000e00794500b00f90300300c0f092074006410031111018980c9813000329424501c010a00e51030100040f549486141c201502c148950103059952a015620103480395000301e2412094604040c501c07034070b59 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 278680872 1250 278679622 278679629
    0x1203080906180303240a0b03061203030106120e010905061f0b0301290f0c03090406120302060103170903010501083306100e0904030e040507031404122001020702031204 74
    0x798410301c0050500303804102d4099541402100100369503c500f40006c20740b0340240c00800a1402c08014044141070a25011411100010255003190f060000040c4880503005a4a41044e250403d0354039890302980b0101a1a80140c10b41c0c80c1403400c92210602543c108081c280c050f10b11036000150740f400481501c0c1a1101003555503040040b5144035904003203140f04031000c04504000021400c510f003c000d0150703508440265413500300303c00c01c000403100c10b030344404004090b11202c600000c2c2c1c042400380c1501da100301034100051a44454820f83d0081d8031b19a031f0590b00e040004a0400c000180020f200300d03a81400140d03082460704003441d040d41101040800d2084240400e0842c0340c541d440c00349012080c81c01651034540da40c0000c800100c15035090b0040340d06900460300c6400c0c1800390b25404044c5040a000309268060100c0c0031800c0100050905c001310b1621885582c840e49581031030014610221000d001c407000c0e014001c1d485070700100d200f0321551118800c41d050803c1034500b00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 278682122 1250 278680872 278680921
    0x30e04090b160e0d0c0302040b041815110c0f06060a15030f1b050a022b0509030109020628080106270504020c010204050a0e010f0b0a091203080906 65
    0x1641c450180000012071805030325003e1107841c840b540c01d1519010070594105001d02e010026892550041c8411a4140043c05000b40c0c1050b030030302c090821200c056208113502c041c0105042e002d2141100003000c00808804645200048441507010001780588503903ca09054403456100c1c181013203420b05d0306106418100300c1c008020201203010b079012201c3c0302020741000c603d443e55004044001c103d920400008540085504016a80e04205501024188a980c1110030704904640da48504500d5802010050001380107405a10290000c10035203070301500d03441e00c80010030083d0700c801c8260800000d0100c3d00c42c1c0000911440341541c117040742c4960320742a440c00d480400c12041d0000c0100b06400c0801c11000000d4641c4444c402080d178030080c14001610346040004020041c2440c1d480505c00064580060058202e80071289017105c400350a025650728124105943d07084650340403600c00d980c0303130105900307058200305918071602041054400319550400c070380d25040c00081a941d103 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 278683372 1250 278682122 278682143
    0x2403060103120c0609020904060c111f0e031c060e0903030f011202011e0f03061a040b0a090e0106030b120604210c0b011e121a190216030e0409 63
    0x207032501486514043d60700540002c40c80d20050707004100d2010b41950226003107030b40ca140c2e000b2000c0c0d00560a6101c5d00008002c0e0200c0d1400503000c26182240c80f0004041e1a600d14000024200c100111002040c9030703034202c11400559501403004040612a000354001c1c0c00340003034183c000c08021288245140d021b0441c1c00e034245000c20418000c1ca550803414403d200240000c65131045080001820155a4480410f111404001c0555825030712910241214150000d20201803800b070310300b6501003181c0180c503004614000c43d500400d036408136440c0c40183c800070840d40d50540200ba41c640d42503a42486a80070007a415640b4602280c0142c2801045448610180141041c081c960030407458020156010340c1c80c1c601c80400c1c01e903c8800382c803e40d0310366140203a00f1452068000c10f044c0d0f180c680c10008980390b091205007030421500d4030040601c00a0b0b08001780710a000c058548003030045442e0b50719100610300f030031102c8005802003039501c2e0b450526441c003400b58800c0c0540c050412907 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 278684622 1250 278683372 278683403
    0xe010e030406020d170c0310050414160903021f0507020612040203160b03060d1b0f080f0d14030c070b0a05180102091302070204060503010513060f15060c03090e2403060103 76
    0x10b06d5a0006051b10740c000300902c00006e4a50741d64000c14103062540c00030700c01c00b828001e007104004489074500380c003840b0040c501000503075501d10210500b035500c2c07401c0d48a484a0504121000d00c141c407402507000b0004555810110100c00c1140d00c03c40c42a0102d4421602c0002407050804c858821045510410800941141081103105000314810010b51000c0d07200103010320144055500b041500c41342d810010010003a080140c4101c403001070014010140d19400d00400c46910190382e1420882c2c000041740d0000319002c01c5a0803240c02001c08031007418441e00a01c05041c0c151104214203079003030140c000100b81032003114040341c0d0060604448081c10030b6001d000c0c0d00818400d9030301550720303900012640c034207002c1c1d50302c10302d40159240d03e580704615200088a02e0700da0144004c5280c102140d00500b0303115641c200343c0c0d403a13040c83d805002051030700f140d03e40f040d0307080f400e0401d482d034050210700300e851000700810703880380d07004562910401024181d6500742484064118440b105440d07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 278685872 1250 278684622 278684641
    0x10605060f0427020c010903120e070608041b030b150307050a0603110d050c040303020f03040807140d060e0c1311040b070f0f050a0b010e15130e010e030406020d17 72
    0x1001d41d00e000b1442030424112080c901c02c170f801c4903440038451394407003011808160707100350716880e4030102840c1046000001c03c0d6640e618034107401141d090029810208091103085012080406c0c0c0000300224419200d1038415150300701174408981045541062000514002c00c03d1410380d400640a1000145000d40840c090012140c01c010428000c000b511039280b468000c5900c61408442e07021f981d1491481c0007440e0190741d807004922504240000d012015010075084100e0302003d144109500306140001c26100704844d00516a61030502440100742d00402d9180c00b401c0111910510f000810b20366800303440040380700450141b0200405d06c509000300c400340040354014003e8040c0e000c0969510720258180080640351035204608001c10881c2c0c040707003d8090540000e0f020118189084a00e1441703800d400303c40d125000d903080404c02d100da19841448000d901400911850340112070040c1c0b6030b803090050b68014050071691084030703030058107084440b1841c944040200c1da514283c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 278687122 1250 278685872 278685899
    0x510091e30030e0604080f03040503060f0f0601261302090702030a02070909030309050604030306050405181902040b04060b0c0d140d020c01020d090303020d0b011b0308060d050703030908010605060f04 88
    0x7140c2d01143c203010206d40c441c0c04228440042241c8401141e0b6142007000300b42c81c1000041007400904601820003600460071182d0a411007000e0a0001c460804003501d000c4000c070540e100f03810001100708004040c84e03150000d500c00c50095910350310a407a80502241c81c1c1c40f0354000c0c1c3c80541d0003210100030082c115030026000343c5c002d1800290b041215500c9501b00801a58190002a02c803035047c04149418030a00780c21103c15009804d0b080440d0303095548405904030311180c040e0000540d0800d645481d08001c8526000034410003045441c1c003580e9515030840c0c00c0e50b000d0392003604111948140690309008040842c0486282441a1315035401c010f544103280c01421950280110517880b0314501400e0b0406e8401d0b200541c0302c0000d00c0318201140c50340810b250411603154088192060603805001105030186058502030b59494003041c0c91200801e4010490320680c17000000703055100c1c800c842580c030f101001344910307592441003200d5800b61704151100000200420011160100341 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 278688372 1250 278687122 278687147
    0x4110a0c1b05030109030801061101022b0f18060b030a020f091b0a03050412030605010509040e0109140319090614070501140a1d060c040510091e3003 66
    0x5a07880d050b1100301190a4980203242100032a42c8107005203c8107402446454800300c030306000314141000b0080c841d034848201c4000307854084130040f540100140079040200000001300081c0300014100c0c0503600301a15110094480e01e190903016440c1c0d150202d84801917030b400410041c80c40448504010705118054421003050300e8103202042c0b128090703005411400380b1514005542e1a05040c00c100400518072600201450a070007405541e0300301c81502c610141c15900040e003041c11003813090051980c190f02902c0614074060310004000000001c100007403480201c003d0000b1030b03400030b64402c10140603400200740031861740f030180c60030710000d00111030040001140c42150f151038500740201c240d51000101d0740b1000854001d540d0540300d800794403400e000070482858800a8107816001e05e0280034828082625141a194070901c05240502510950755003109181c3c0350715145954180f041450031002600800c4441c20101301501c0c3d401c49860320501c603031701c0d681d804680c900d06101 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 278689622 1250 278688372 278688413
    0x60f051e090d0b07020109111f1206080304080c040b18060405041118042109090b03070308040617010504021206040c090f030602030f01090507020d0f0912080904110a0c 74
    0x1400480801c1c0300920f418082e90350303500000740d08030190805444804a00d0115030140503080700e04070200010191160b41c02038203140511b501402c039a41c94018007103d50007002144404038012902c0c0c0c0c804101140303181001c4504004c00c0b48054280001d070b122401018400c408043c00148545c01d15070080c0e0750192044003440080e114000000b0002d1320f1040380030007180b00703040401c020480c00d43c1c242150130802c0d46140c1c074500c42c1d206000f04515914001c807160b4684440003400c4a40742084075401440c0d000560716282c40d201c0c48001c20184242d5400c44444444a0000460307050900c01c4070102c8083c08000d199968403a000c0c00054100700028ac000c00a00c40c1d40012504140c00a40740690312946003d03a0fa820305695131411184180c010040461414041c8481a0380000c1d4600d00c09280341005440d0504100043d50348a000d54010000388a44080b80010802c0081c001c00c581d200446040204041f600340d20001c0c0d001d514800008134101c0d81500380414071244114076149a0070 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 278690872 1250 278689622 278689639
    0x4180807122102030f0c160213060b0a23090a26190c050f1018211a27070b0d0e06011a0d0b03010e16060f051e09 50
    0x200c90021024452618100c602d6800302c140218100307416449604403000c280303001c1c20842800d400b83d554403000c0900910030701c181d4900004141079508500c00a1101c1b02c00d09440b400860f8014101880c0c04c55043c11549070b80071030032000d02a40301516400c4002600c03900c8446c0c00c00c00b08180c02100400740e0004406a80d1480805a104004601d0380064000018000541c50300d04000e150516820151250b0090b03450711080f5207865060b10388240c000d2030280040000c000040040700580d4002c1e2110004501400703410300c0e4409103038500588a070741c41d04c0b0a205046c1c0300750ba40c01e5003642e8800c01c00780041800000f1210f402e4411004c1450b0405071046d940c2c0e43c14103146564494410484540c0c0c84440c42e0410800600919004142aa0031111071150804182c491031003102c02408030b030f969424000384c0b191400d5001e8502c8200702c03001c03a0800c0800504541d580c440700e1189900081c14041c0c1c880a0912980958aa0491000c803500c3d203101207485400e201d0b00201011070700103103003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 278692122 1250 278690872 278690897
    0xd050f010c05090f150306100504080d0f141620090a050a05010503030a0e04020d06030212010f06080d1e0c1a0f070305092e1a0418080712 61
    0x203101e9040c1000450311150754458054040c0030074103d081d12424881c4400c141c03143c49602c0410f003181d0380480b0888547ca4943c2c034628054031507014035080844984181d6001891968002e0300c40d10303201c043c41d08d41d101c0307454229140c80001d205001c81c4e43d03013050742c20010700001000c0804500201c080000d4000f44c0454103008212043e80c102e6103468002c2d1142d05010101086104a90250605802651400790f9481000c0c01c42007841c400c2a001e00c1c1e0014001084000540c428005198018101061203031000e82e400c3c0130742440040c00718500e14149000503e00c20009403a004032445485983c00701c800184c22000034062403100109103c0c0d0f40642c0c40c00140742c0d22604510030480011880582800505142c001c00014020414146080140703c40100c000a001c9003481c2d00c0141c84141001d50100010800a109403c80a00f030402a030b90481a60401c4148400f58003a241000303500c0c0c107034400c045410b200c01c0028102080401540000c20560301304d44400700301a0420708251541d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 278693372 1250 278692122 278692153
    0x302010204090e0c040c020f0a031110090623060109050402070521040603050105090c030402060a110d03020903060f01031214090a0b0301051c02030601141206100302032104050d05 79
    0x1501c00c06a042c0c0c0c000351407404c02860280f141d10740386502440181b8a20051202c05d40da110060074002d02808915001c401d014030003081b0765103030b0040c1c2140c02e2047d0f940c40d14004000d4118147c010014002d6000d0307a040020104402c1c42c881c0c4016511207940501c2d000c1840001d60001030252681d02034080000c01c02006045542c00e4490000003082d03555141400080480c1d5060f00320303d100d80481414003500d00c0b803400c2660780040d01190070b00c0d680c5424140540b0050310903010b100150041d100381c80c2e1001d42650280c100c9000030740584007140d60f212120310f80703208240001414441c3e0b004480550500c070f02c46025002601000241c42c20441c0800681c14010030390040e04101c034000010701c00ca091000c07030b2a0300085d211205013445070070f0780c1c0060b4407400c1c140a0340c1103808a0351448220b0351703904680c2004141281c020b84800c1e0500210388006042d2600040c1d02034451400410580341030000a8689258194041400d1134104410013440041c120010b580b1485a0340c0b04005120 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 278694622 1250 278693372 278693381
    0x809040e06070219050f15190204051e060d0606090f090506030303070806180406090c080105040f03110109140703020901050102060c07110a0509070206011403120306091b040f0303021506010c030804030201020409 93
    0x421906147d403240352a1312545a010351004112001d980144000c205caa150404e000107401564016248407514507004a02580600d01c81c8041441c00d100000840b15002401201a40c140050005455403540743c0b010548109903007032600348c1d00420014505038482d00d0328542003900106841082a071041d0300021404007078405441745a6144d05100411238107400c09002001520001e004615080d101c1c1d03040d10000d02400f90511100c0c5c41c11202400e000e61107071a50a9000c1e45402603004c1c80c036221695410710b13000c102c0c00f42895000109540d030000a086210b00850304180c3d01c1c0c0040c036a241c801141d044000590804440e0101040996034405440e214030b00e141e0003000d0640c03404801c02211441c095a050190700080c00c00c3e60329044074800c5980c0030200340c42081e01519807011008850804d0200034640c1e9901080125820b80141c1c124812a03010350f085a0342d40e0342590080c3c9800b01d080e602140407401210310f050001c1d00072200b442d402402800010b092990740d02e002000c2e00d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 278695872 1250 278694622 278694643
    0x30b0901020c0607090b1b010b03190203060109060315090609120806041a010f1d060a02060708070819090204090219031403030405190813030809040e06070219050f 72
    0x181d401042c000706109040101c1e0394040030700e00d800200e136454030a0403e114801c41d4001c001041071011002c0d100c1d0800d40002800144c040c01b140e1000004041400c901084010224801d000302d1000017050b043e2403343d402500e4003c1b013101d0030f41c00107010b068010039840c002150340351784031000b007070124444410041c0d0b41942e640b541c0711549440c0041204540c200720041c40c0124013000542002e0342d02c8180c00038104000d05050030314203000104c002002c1c0c20740042c642c1c80100014011041a4049501405400c2c02e444001d25038030740e50815039403504100d59103816401080d02d03c81d05040290040d417200f034001340000070303d05c100d42c0204420f42c00f016200d08807808524030810801000c151500ea41d1005180918150300b0070f0781c3e40729116000441c0f81561008500744d1403050214140031140b0301d100305035141c0b0302e45580b807400f41400e40000009510807442c0006100d960140802c0c110300c510000d81c05400c01c1041c03250700860000315450b05985511400c1c8c0d9550507070008208001c0c0b217 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 278697122 1250 278695872 278695891
    0xb0a020a08070b01031e0512070c0b030403020a030809030406020c0904030516050606032506030b01120c030c0e030f0601060315050a170c0a03110f2b0201030e010c02030d1104030b 79
    0x156045042080e0200400c6c0c100c04030325002c4850a0011400115280c00c0d10a0340649a60743c0d024182002d050846c25500141c69051002003070200b0180c0004e0124170b5507110351102d84c2641c1c0c9030a4495164011440b075100940c0203c1c122409910382081190b034050722905055082c0094a8000101700c128020129959030000342407081701d107000c02c601c0d07418104500000d43e924a803203800c2d4070885001d10480c0c1c185915244290309983c028240451506410300d4100003040d62110000c000d0000b4101c450081010085c6c070450318100400d485e105182c2006c01400d069181c060101c00411400005a0001128a101003816038440d10818001e00040c8100b0307100b60882c1c005a410444449800703446540400c408000069508031110360b2288101c5d03c1040b4003c030039011442d0a01816219138803402c5e9680e03440d054081d00c0c402d807500d080c000e0368100091212027a1b240c0c22500c1c0c1a0021001d42d2040c84140466072260300800a10185821403604003562562007079144402550041c52 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 278698372 1250 278697122 278697143
    0x10b04090518160321120c171303030b01082401050408030c01091505011203030b040b12010c0f02300903010e100b0609060f0c070e090a150b03070b0a020a0807 70
    0x240494000c0c0b4021000f01803e170800540c03000c034800b80550152401540c00540c0b1640e201003440c0c0a64405d0028030b030790007910034140c6480c498040070402204801c0300428904803007000c40d0751081e960513100310400e9810252006102c0c0c1d08103920001040e82c2410032404101c0840c10320000c0c000781c48a5000b00001155111041c81d01708a0b1100704039080442515200c0104200e108100c601c40020303826040010303150f294080070502402100160540020007443c540c007107510154000034241d84180d44c0d121a41a2581040741c0b0382808110031f60788245611079400306051a040801c2098141911309031812102c440828217445a00442220a4005003000351582415006a481080b01203900c240f42c8101903000034605d004e40c2600030000c140104180c1c66001c020414240600041c1061642c86d1800104050785c0c2c10001d44210358100c00d40c0710709001f15049009002054000902070000c107800d094110425030468420402103125030030358a0086072880d0000c2c0446400794101d0030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 278699622 1250 278698372 278698379
    0xc030703020105151008100e010b1213110411040306140108070f0303050a030b0d0b040c0602010c08040b060f010216060806100809070b0315030709091406010b0409051816 75
    0x80c03c544004143c0c1540325012100ba006995503c00000501030050034010310588601403046000c0041d6001828541c07281400880c1e454800e5020340400402000380848a40d03c07580c1d1107800140c410701c018071a045100c050125480c0c0342c3c00c000e501c5a0520007180c00d0541e2a264070701071340c104000030003902140c0001072150b00000e00191003d01803d40352040b816186540040c481d12603038031884109a6103025240941c3c0da8100b0249203aa040242c3c00c88500381410140c0380400d0f03501c100000b540c030b0500f00d041054007610600303100d19003180c1544000d5480006001c40da528100d4101d0440c020751590641c45608905031074060314166895000c0d915150040c0718401101e5458041404448400c01000741000900e160660301c0541c24a0380b25180c0c4c0300758109100b14003010a90502805d007002c2250191948000c0c40103000d003600e132005000b80071070940c40d18020b0213407490b082d10400051107260100d800c81a003003048140d00c12004a00441d405040c040b41301214104035500c2c14082 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 278700872 1250 278699622 278699627
    0x40222050f01170f06011e0905010305060a03020a1415120f010b072f03030c010b040510060507061113060c020103051605090d020a09060605071a04030507060209040902060c030703 79
    0x800390302500f820306542c8200110a8a0211400240400003140784500002c41c96445194010340c41490711000d81d810980c1113002038020100740c0103a40c0064501800500c562803d40410800c517900070300856581814a150b81c699594102c141c143c201700302950b00300e404503014000b45022006990f40b0352103130901112013550b040d010303030180c14111070610031003010030060104d120060a603940114103c1000030700c0103450100c0f204425038903000c0803c0840002c1d1041d04100d10b600c0c000c640810480d515104401e60f0705106004010001e0000c0c041400080c5459101d801c0c83c6c00c030000902d0400f03e00c11318258801060350880390000301d0200c6c02c00b0455800d4000e45402c5000a203801d0031445482c1e100901d903001d1035101d107128001900c5e1100554451300032400107040310180c1404819141c480103080343e840a90308882005103000d580b91414070700b81459025903415941c51b031800c0e040703032034482c003a411525100381c1c0b19558200c1071006944600c014409000e181021751345035012030502 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 278702122 1250 278700872 278700889
    0x1b060306050312190e190e2406030c0708040906030308070207060f0f0504080303070c1e020d060f0b09280501080d111504030905040b100c06020904022205 68
    0x114065400000034071420111002940c030540c0d102200c04c0720205045404403050400a040c00b81c000811030710b03a032084511544800c090780c5c0100d08024960312150005000306a0f0390441180031301e03001c4035420b41407800c0001150000703030307412a5909083e400e84900900307030f002d607200101080d5500d004004250b001910150b11030541c0c0090a140307442d00002405641300c500303044040161800c10b00d9078890007042a40c0240c020f82e0708690b140e2501102c00341c607514031950f099801241e100b000020161608018001855001d01400e8084800d80d4406005e882d580681c3e40f611900c9240780e498540b600349026114405000049482c0c0c540c8d00e60380021410015502803440341010010310030154001008003800d52585007640400049d514694100005060705c0e04401055900f4001810ba008a004094807030480302044449200c00c03c000c1a10214900a004200e00c8204c3c07e01140c8031398042c014049000d08058540106078050145a070b008035803041e80c00f0003202e4140030354100030070b5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 278703372 1250 278702122 278702129
    0xc12050909040b1b030108071406072402040801020703030c08010504060b12040206211f0e040201030c110703031817060c16150c020607020105010b070206090604031b060306 76
    0x10650300d40300200000c19054100248090a0750f92940041102e14440c0280d82c04c0c1c0382414044c141e103d503100c121440c0c0700c40180c810300b100064404a6608545403600440b40c1003544420782e03100b001d081da465060390400d03c1511000296090000142040c800c1c0020400b15100ea80c0021f0001d11112002d014402d06801290103185000030038400d20340d03004225100750400e82c214079015559880021100d02c1100d03001a44144c6000d40d40c1028011101c140e4012480c5217031464140c0000c00300c4d1b015190382480b61003c0c0420400115000d0f501a50000c124683c040ca4480080c018580c005071904405520403000101d0080341094060b402c8150f6002903c0100c0d0101d4180c45401c15080da46d6001810300d4800f140b0009101c0d002e03c000c3c003c81d04140f5441000c3e400c2c082d40354a500401071013845100b00c00343c0100d00c0080c3c001f92061040034180d407151480c4038217001c410f8080c854a40c206404440c2c0080c41004044045500c130705540c8071015520103c0d9011500340f03080103060300c44951 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 278704622 1250 278703372 278703377
    0x7020106080d05030c0c07030309090e0303101403072301110307030507200a09020c0c18011203030e01020d0209030708070e06121906050144030c0d0c12 67
    0x140281c25000c00c241949084a10b04591651036104103015030340b04a0716010103d10070003400008158004900500b1102048400c200031106c4008654581c801294034100d41284000280590303c07802d01d8811343ca0201804441000341c481440e095464280080ba00816158420210f55982d100007240308820907140070314200910756601900324011405c009100c1d442c1d00c0e03040d00728079250780045a1415001840d446521765640b540d80000e502110180500d801343c5608001c131401d107102d441408005082480780140e20744004a5074030000400c0071002c0581310030120351514400d001401c800702410200680c0c400c0a241050700c1d0284c65030007150550840340003008041e04442e03505521100c19540f644010701b40b900040e0514407007e210001c55950314400b1814420203901c02410382d50680308041003072000040301c09411442188c0c24240045903d01244000c0480051000c101104401c40c0d0801c0f4032400110304000000035441c0004100903113071801e00c18004120b807400340060 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 278705872 1250 278704622 278704631
    0x11508070b120601260a24150302130b03070206091f0b060706090b06040b01020c0f0609120d0203030702060f011401081b0f070204050901020c071e03060606021005070201 75
    0x4074624825018203090340704880304020009603141d000f030701c500e45a007404202180705500c94002104000c00262800c10382149445850300c00581b400140c030b40003a41c1580c00342902e07498400750400c01c5013042c1a540803d0b40910285500314259071851000d41440b104840d200d02d40030b80c0c020f02e49900100303c4101e07940001005206200d55002d58006004800004186204460b010440034070684d04010710309441c00c02d40d0390512922100c298001c1e20304407030a01800c16480012070b650703206256242e40c0710902804692241c03030004010b212428001d8680e5400280303016480741051000212840940c000004019070203074140452540710b03c0c5426802c1065040003914031850503403410050600560602040c1080c0400040248a1f250038945035500c5040803e6140c0a0f00300030300032070286003020003044000b47d043c000e0303c43c0b20780001c0c0109000c500e0f000c00412002981840001c0781c410288011002c80c1080c040c0350064426900242014406089508d044900007131104045900d030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 278707122 1250 278705872 278705879
    0x306120303070c080c030417030711061923031f1a0901032301060c0b060a0b1215130603050c0d021509010201060906030606150315060f0e03070801150807 68
    0x3d515045000d4000030425124040d06141d01d03d90321441d04030007500c0006000010010034000014203500d0b102d0035034408403c442000b03200301c2e0f008400b04107101e0440301c1d03100c8003098401c46112441852030b10301d44100c0d00c2104001d5150f540240c0b5003041141e005081c0703840454003282c0ea0001801014090401900a001e0400182c000c1c246083d04154940e0004142d4180b212140c07120214105828561540c0d5800d01600b1406000d0080310281144400102c062801b5041d08003220114040689400a5810138501042d80202090403e81000320340c5001a1205186064150b00900b400140300341181480c511b4001d001010138896a4005064001601ca034803844407444030700c4045946420b020b5006070702420707064001c012403915240000040c04601e0b00314a003215419601c0c5105104d008404034147c44004000c5924800c4050042000d0351060f12200509031062610030120700c890000241801403a81c01005a42e4417a00506683c0d0310780d9030118000c140c10303070007046460325 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 278708372 1250 278707122 278707127
    0xc040b030c070503070506090d2007060c290a0b22052a030103030f09060f180b0310031713050f0f1815042304020a0801020f030612030307 61
    0x80804000071404115001004410030a99040076404016240c0c03624015580a5445006031088070000e5200642d40d022104407200b661240000d21001d400c2d0b136410040140d604c0210742800f11450030754001c1c0303c0b80c0c425000d0101c2c44541094090400341e0300b0b181400c1c0041e034101500240c880c00780c11030341e041c07040c6495852030404192200b0210780d03a61480843c3c0c000c00405c3d40380c06c4090b03988000000f41c0200500095041e28480e85070f108001a0031841151100301901030100464400c1c8030512446006901001c09000780c2d2102c0c0001c0c5842e00603407401900180c4250402c20ba0b070400a0081107001403442111005500490b81000500740086480d080c003449010300580703046203203584a494071291344441580c0940580440d0400420301007010100712651850403c00050b81e080720301c0c06020314445c042c0004240780f01d40d071140220300746410300644101d0340801101c0c000070303840e5000e00141061600303071244c03d0b499162000601c2003010050307c0c003100c59002001040f01e8181c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 278709622 1250 278708372 278708377
    0x3010e060f031905010f1508121e04090b040c0e06160606091409070b030402090703021b07120b1503070b0a030b03010f0e0c041401060315030602030705070b0c040b 72
    0x101c540c10728041518000c0b909100d0020040300001c90103510800501c00c1c150030402e41500c4041c010800104160282c000c4074000c0d00448549400582200b00c1007140240a40140d0200340511b00c020300c880306031841694042d40c04088441e848080d00c001f149440d00c41d81500003250304008200e103140e80002803041c40713005c00e041c0200c903000701c215083c80355a0b488040a0661104100b014841c0701c4000003540c0000c484801c9507100320a00480ea40003504103490040d68054900304641d245c41d074054001c1e41159209007400058803e0000001e80c08002c02e000a0081d802d004958400c182000403807010020400d0706000ea0079901c884660302c00246480c12a20b000c0a5030384c948600020840c06060041c5d07041c0e07415130078240a020b00c032901e9441100113507402c00c00c40348002d59050500050b15050b0401644000c1b041d40100449070007504007605a825080b450340d90300b40c4940d50003003203800503180880000c801040d80030801645610072a04a4640c400090906151610240b01071 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 278710872 1250 278709622 278709631
    0x9120405010f0e040f020909130b0402010c0f0b040309080c04150302010311130803030711010e060403080714030c04050102160e0103120c05010c080f100614030c1b01051b03010e 78
    0x1041d12240400c00034816402e40c110306100800905c1140c1140c0d42440294100350076882c440c07040000427814280ea0351401d903d020350b0000c0590415640c9400548003c4041c2905844441c1c0300c250210010300c2110003544654401d40310b0504445c20315803c07605d40400c0f001c170140030341d00e05010301070358003c810308500481e6424607005c1404035801c4003041d583d000d00b004010b1100c0c10300c140882d01c0c90010026601c030300c00c0b50ba0b41502c00c01c081207a00d400d031100210303600201c1d00a400442e0101e4402d1009c0ca9008101c0d080094106029000400796030b0b2003152070715502103003c103080c0710640c0d05202d020f00c4c000340754000c8000790303040800d034a61200061100802d006041740c400c140c0300303008412554000d500b2000800400c0913054010b4080c24044503050042c00b0800c0000e0a00408440041c007624203030756586c5e0f00008402417596541d400542031000014003849107010b0020b0465584500d0000c2170004281800d00308401958035100d0400118507001c2400180320041004000580c40f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 278712122 1250 278710872 278710877
    0x50f1801060f120c0e04050a051005040f0f11150c0f2a010e18070905060f040605160507120302060a020a1b0c0503030412021906020a030c050f0717060912040501 71
    0x80e0401403421113502c00d800d620499044031401c00304001c0c0040456640003c5000320140d942082c22582440115002110b005220241c4280010301090103201a0030780c6a120f002c011131300e00072000000d0104e100002070100403600000e00d0b806074a9081c4201c0ba46996818010304e100115002a41819400300a403c91000c000c030101800f603a00c00c0d11440a03a001c09807103420000d02135010700800c0f07602260180040f402e617003000185810f1482c02c13250800700e040205401c040c240071701103071039a2000d09290341c0e4040c494171a401080741801044020154107004440e02d0910f460007078104400244505951441402215031680e007020780744c80d21011501c511180c1e03410620f042500d80074203402007a014840031401060a40b0003100c000507883c002c0740c0ca820140501c400310b04200407240279140043e0801d61100740020702400c0841445446101034403030b581c6030340302490301e444800da101e1546280c4174081c0400e40301017804030542080748a006440d0000840ea109080c0384201e1281d03604 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 278713372 1250 278712122 278712149
    0x50301240b19050d06051009060f0f0207060507050c120607021504020d12181401090f0b04090c110d1e03020c0d0e2209020a0608220c0306050f1801060f 67
    0x40740c0e58154003005c041d240040c0071700201140c00d40001e0000d10180100b40c0400c0130000900c107440d0160100c04580700b00355000303011300c0d42004000c0707400340c200103070403521b81c4600e220245041d81c03401c4210b8074005c20b40c00100068540010001d262410b0388e000200c0d100889010300c400360304c8003c102000241c0001c2e80c0842c19164680032620072001143d0048802540312011480a8400000c142d10500076602d04000a4948080340101c0e5201e1003400d0617140c08000c200110803d9410080070030b001d600b0044500583c2e45107141c20141c3c2400781800003071444928240c6e0a0070164003c5105906103800c41c00d021800070426501d00c24807402e1802c0c000c0e44c1400b481c1d0b96881d100c144e14103107404a014071b00ba410134100c49000d8010148102e00c90180d800d00401d01d188600e901521402d0403a048038000c522300f1030809181500c280d81610750f001540c1010000c60b980d40185030046060030400441890842d03c2c1c040081201c00e52183d8607418600c0401100c2c3e09074001c082603820074550b0701c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 278714622 1250 278713372 278713387
    0x10f080121120e0102280b06030703050d17011a0304020103091e0605062404210204091a0a2c0f060403020a0b101a090a050301240b1905 60
    0x40e044034590300103008101d001c5800210b2540100250400e03c02a000c43c0c5044c81e444040041e41c110445455141c0a00e80161030003242c3d00f56000344d0420070107019603d0103901c0b80c80300340c1800480f5501c0d03c040360700080045a480003039030b6454010005a0446011121800c00e08403503840050030181c1095150198001800849220201800e440e060000304a42c004c0c40c00c1d901424044a100d48250315030001900f250101c8100c905240189100881c40e0a0410703407400010550318100c01e82180510348600d0068543c1e04c04c48003a5030242c580205901080321812150420042850011364241003051182d0581186c0c00542c11001c5c5c85040c07016141690058500140c10200018602c41e24051100b4181c0100f1041802c1e03000c1c10354903420b6592880c8100669245110781c41c0140c240400301c1544905d4140074224010303009140b0419980d40e07a00103401d48194202c00c171100c2c0501c0847d046c0c000305404031500180084002c0344d042a00031340804985540780009070080c41400075044 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 278715872 1250 278714622 278714669
    0xc050105090a0509190e030a0203030f0c070f0b1f081c0e09130510050618180610080c0103090b04030507020607121205010501031e1a0603010801020d0b010f0801 71
    0x10703000f0b004007074610303da1841c2a9a502241041400c43c3c1030419184c5010140c090b00080215207000f032042c0c008514680300c5d00010580c60307074020110f109602081c0b03c2040002c80c1d0558452009008240103401410820038103440e201070817606420360895a00c04002418021601c425801074049c02c119003610ba075101580d040e961002460382c016217101c04c2140804d088105448003a00400480305e10154041d40c12080f98000c6d201d482e030148240420b0700c4201c13070311210f150340040a40150201060003420b054a820b105480c01d140c4000c4002082c004140c04101000b4250300c2440d040c480490aa2243c82c2c41c0c040184c0040c041002c00240401952551001c40e9101503001801500c27007103541c94014004800900040119410b0500000d000d40c03003800703a88204200040b1130058400b0900c1076074014000c0c429041110a0018010460f80c1e41c0c03840594001c3c41c0c60400580d9468030481c7c0101124034001140d41403181c940640c814842d070141426064950f41c8440f80601c1c030070716070503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 278717122 1250 278715872 278715889
    0x3023a1e0207051006050a0e0402060a0c05011505030d050a09050d03020c060c100501050a0501080a0b1f0e130e0706031109091503071a0a0c020f060c0303150d0c05010509 75
    0x20316000c5000054490401070700081c1020002002c02003002129140c03001c101200c5840d2055a280c5810711011a0146c44d041c00248a2041c140c10a101d007030249607500c900b903d252a11404c3c80308000c0000b0011801c0030701105108231040d1402c1468000c2580e005031403000d503409100e0003030406003503030020107008010b08101038200508443e103131034a200c004c039130b85c2c204800d880c0c07240d85c00d10740002020f041c210064401c1e1041612094820307039415400b20004c2030f40034100382d4410350b40b802002c00b000d842c187d40944421255501c040140105090011500000d00509141c500d4101170869000b404107000007914500d02e03020401c54074510f04c004450082111150340190070130240b01c15042240c20317002044900f6016118607540e109a9440344000100684054503820810500c0d001d100d0441407040900c010900041b040b02c1d04042442034021401d52030083d403000040c0088407140800364004a6411103030445c28441c3c0d0359414007450994410503060100c0481c0c10149561040705 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 278718372 1250 278717122 278717171
    0x30c0a080603210d0b0a03150c200d0e09040309050112020409060b030405010c08100b0913050112021206010b0901030207060f0c030c1805090402060309120a03023a 72
    0x111030400c0143c18680c0181540060f0321400c03050b1404242c59040e042c50601d40007100c1e0402400030540c0160000c0307101074004400a00100040c1c000c02c000d02e2103031181210640d0400c440240b182c00c09084020b0f043c240000003e601c2440188104400681d101004009641007032802c80c1109443c0200f10010780943c0c0c0160f0102c0b818914081280d10200000d140300300d004400038440400100b0090310401001e031084407590810060a11102d01c40340020507643d04050803a0b02a11480300300360003100c9081c1c003c8900511603030441c100303618000394a1460400b03450041e20095242c005000c0307081c03103904070490526030045200c07005d04c01c090307201006000e41c0c000300b4070400a04d160f00030020310304204420b0200f44001078075400c0340c40310a0020283c440282185030b243c2c0780d6808100c4684c0000741108200e100e8004103034209030900b00900a60015a10b016844401d15614001da038119998007943c50319040411502c0030207028541101d0b00c480084c0018006081d40b0501c144005100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 278719622 1250 278718372 278718403
    0x506070e0d0f060504030912110105090a05030609010903110d080402011b06230117100905160b04090f18032d1d01020d020a0602030705090a140109050105030c0a080603 74
    0x3920403d108580d001301c0d129a1013540e88140c0f0030340f075001c40c0d6050840c01c0d8020300100c240000304c2207254016002001004001009480d04596a07000179141880c02c8966000d5651a04250010107400c0100341e503038201600e025008641d11014020041403004001034104505a5955640f00c1f640c6000a24a20b403c003400344264580001100261044100c00c0d400410b0340100000341120044580e806440165001c0c00d4140104412103010b07244450050f15640240100105a8030f030f001180c4008100004005446502d072200200490300e480014903109802d00c80d0764000e42a022040006460341030411117541440c0419202504e40903c008207022610045c3c02d19066400040481c08000014101030250f40d0b070f08012078440b542c0d544800b015a0003919140700150765a0080c41d8482c0880c54550704100301c6900007618070704281c1c000002e00c0c030070403418160741d68805681c001401c82030074402d2a505181e140a8118807440c5aa42c2c20010300300c2c0030801d965800e20146041580c1203 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 278720872 1250 278719622 278719643
    0xf09060f07050a02010f0f0905120f161e0f12051002030117060114010504030b1b07030e13091104020901090801020703110d020c090a0f0b0a0803250506070e0d 70
    0x2d162040da20094034505901140c01d440c05c021442e0711a07150741d00c1c11241a91034025662601302070155003507c0340e03800c0700320b8002c0a40c1200c00300300400c082c41d460400c450a080c000c51070015115006949101c0c1252900ba20356001d00c5009050501c140445401c681840701512190420508202c2c10203207007816203000100000d4000c0d003030000c0340382240d0140207840d41c590347ca110101c00010520103150100700240410004104148881a480b691120345004408503107901141ca5922003a4110045211045440c04905099040300d0b50300c0314400d010003000c9125110000c00290030240b84e8802ea030001115241a4402c1d403004000300020740095403916594603002d0030200d000441c980c05441280701c612500e61002034001d04ca204040e00c0e0102c5515884400400343c880d00805110858403a902a202d13521926030790070080400c80091a04c42410003840007500401100c1110340c821070b0161a0046500425540e4008800e814a11030300f0035000e000c02d8122641803006410b00604 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 278722122 1250 278720872 278720887
    0x933040b04060b09040b040218060c030d0c122d0c020111160b0f040305071e0f0c09050c0708090d0519050102072603040204150b0a020309041109060f09060f 69
    0x281c003031300b80180212800e00c5400f0710702062008a0140c00380c0c09070550f0904500700c1c0d5a00300031004221145c11841a2031801040b004404151281404048000fa45800c5403110440d130900c038040c1000c15400100010a0070b40742c00f11028450306c0c810807203050351801c2000c0070301d000354014080c1c080c2c00000f40d27848032007a100d40180c1544c2140d007034500c50040710003d4040c43d04404a20f10135039242d1101d5003080c0076610f0b12000800511070842020401540101c0402c0c3ca107030f80c21003071511410703907030043c40d040c06181d0084c1d130009005c00080840a0000c940040c2c0c400d0300b0703901c1d01001030701d45100c11030a60500d2407920018107a00701c031240e40c0c030f5080380c10700406400418a00e401002c1d16003124401c1c01c41120781d248902884400a10b0910115005252580180410b01e24134a0061546c58490905032115030090300c0d4000943d00008035007a89081a00410a01c100d680902904128200d00400e00302c1c401d42c20305140961000030030f2070803540c46034143c904030120720304031a848001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 278723372 1250 278722122 278722139
    0xf0306090e0a020307060206010513090501060e0108010504120305090a021225150c0309050f01030f0c030b091b0f030705070507061d0f0a090f0905060a06050933040b0406 75
    0x42c410081e07020740508800030a0042c0001803203030480c0d80207455100003440c4106100c1c000d205000c8112800d5480b50400914440001065800380140c000001124101490241d626150825141040c1420241000142e640c0407440300d5182c9d806a50124015060480c6c250401c08072100c412080d904c91400b20001082c03600700081510300c0201d500640050105080e81d03891403295008000541c5c0400901c00d5041a0440042050f018100841c0785070000c5105410340d140c0000340320009a8860502c20b041c9448541d03170f42c00c14400c200010050792101c072580f48030300c205010840882000030100b00341070311070022222443e4008003a07402141d02c035400144401008240d0100c02c22101c025100103240034003501565080084c01601e0040c50450f117174025091040c14492826a6000480041a800c0c0082803141c0324800c03000410908100070480c4024000d8603001490340003109040d9400e070035030768228900b1902a200c0d81c030851940e0000d8043c0219041c404e81003410105c00040120 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 278724622 1250 278723372 278723383
    0x10216031808190204020c01090501090821061f0903171e090a090e0c09010306060510050a05093c09130203030702090408160b07030c03020a020d0f0306090e 69
    0x804904058800c03540e03603540c40e0b94860710303c0d02c00c154102c00032201c180145010390003030600b0003410340042102076480e280c031806c44941103020794601800140b5901d0550b06601c0480c0b01c04410040c0c01d0150a00c00c020416211140560750300070f403101321402800a0003030b0345c80b000540d800031402281c2e0740030744c0030074003039800c0030800e5000d107080005000e170800c01c030700155212070801174a818989480c0100c400068801900c0480311802060130101103a250440403038013075406207101103030031441c1000b805013403440b0721002410024140701640c6041d60100481c3c030700364411200c2c0e52000644150000300d007a20710b50801308001d00c20aa4039500c20341d01e112007044100403500c00520baa43c41c02c4920302c03142c8141c002549900304100420041c902020000c0c0c120340a01802800c010310b0303a00d220300000348142c1c00c0e580301d851076080103000350741401000390640a41c40c003035007010185031340170799074010b800d1908040c0700d600100410700500c20760103c401400000002e000940c2a50441a00c84 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 278725872 1250 278724622 278724647
    0x4110c0a02090a090201020a03120e010c091701050c04090207020102071508070201060503160303030f020d090b0a1125060f2d02070803131b0e0a1508120c01021603 72
    0x492881000035800c10b0b084c070861a02d0754041e00644008603003590308481e142c50080030100c0e00c90307075182009000c2c3e00034403542c14518200c0d140d650300395041480307000c40c10000c64031280c0e280c1e04110402041c55030b08000c0d1000c680d80d80d90050380300c414610047c0d062143d50740003102d103482c0100e0702c041e445500c804a5030140310700e07800170840f10f0380f10828140c0307500c0c00e1600c489182400d0601080085d209612520020250010040c10a105540c0801c2682c0076100c051b1a0919200240400001280320300d0708521a0061058903029820100800d0062164504508520310a00e240c0c1444440e400c070f040507a402450800000c0c1c82070031300e41218076001c0d030100134103845150f040344840410700c01c03140c22a0b0099181c2d42146c0d2018800c18084103040011600f000aa80e031940d0006c80d02103800000d0100c034a84014580361400c41c1504031940344d101074905028481d02040100e4000c102d410001c03601c000071a03981c225122816004e0f219101500c0352450a080e6500241030b4411014880c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 278727122 1250 278725872 278725879
    0xe0102030c091c050c1216030c06020f0c10111906022d0301120f15020d0b0402120406110405060d09050c0a03110d1a090109050c0a1d040204110c0a02 66
    0x781043c050840e0100f21a03284010070380c4e070014051459618048006031001c108140c00c468400c50380704004000018030703610489503049070007030a0000d250103000581d040c1000d070000705404040d21002503c00301520008200340203c9903600340c05044203000017414150540c20710411060a0f00e0200000d51210b450701243c10901d00b682c000c90105c080301c1d40503491131142c2840c01c690034510841c821410b141c01c126a0844801c4400c4000341040000030b80c1103203509070042e00c400743d5040b044140c8036800c1c5041d10644c4100030740c4003109040007650b6049a0890f00006810b035840d980c0300d01b2031155800056005002289004c003600b05500003040b4188168284c4219991520611450320002d01004244030072611840805061040304100000d0140c11060b4141b14041654421a54140ca00c0c11081c0d44844010051140400c0440c00380700d801c0c1c40e009012443d06100180d402d14012011210900043c0410155035075034120002d00310b01440c404e941c034444030714082c0d41d403c0010741c200e00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 278728372 1250 278727122 278727139
    0x50703090e070f1d060d11120708010603050c040302061c0204080f1b0916050a0e04050a09020a060f140c070e0c0406320c150c0901030509060105010519030e0102030c09 74
    0x713082e000b00c45450b800902800190804500300c0c0c240002e4000d0b04203840c104407003031250703100c542e00f4114910701600d6107880d102c2865051850040585000416034810f18608000802c010b03101d40c8203c400c0090100b8006a03201c51108541d0f000c0e200b6540401e0300c9128401d5600310300500819100c0e9241a92201c810400042e2001e020903d40d08451364040c541036400c900d40d809000380001d2115854524002c43c04000352400a030440d00250768482d07860b580e0b03014410860800c18400700103400581844110141b2a04c3c00500140268501c0e0751105008241e20303114280810101020301030318071803282540340c040100c0c182900544a9603001a1002d0307100b2003050f039201c01038911100714140312103011102c050324402607440a4819112485220100030021400c101d1040c062814640300981d5070207607000050956101500f2403606420000c01048541c0c0c001040746c803040030500d48146000d1054009500900d982119031072694000810400365001c0000202400c60f0304580705036 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 278729622 1250 278728372 278728397
    0xa08071d1008070e07090b04170c181f26120f04050103020306011101050708150109080703020d050307061b1710050405190f0507020f0607020706050703090e070f 71
    0x1a07914a0034450411150884901880042c0328401c0482e0700205034140036100c29511013480d40c2039072107580001403003044000e100129a00c240724184903014112103080d105842005c940424400c054551504540e001c401d02c0142403800341c00340024a9542c034201640c041f044805401c480035056a0489400741c13050510360600700f01c099441e8948100303c024145410003005500039031000d030819041c1f1030000302c0c0340184842400741e01d00c2000b841d941ca01c074070700707154034642e445820310480c00d41448148030003405010000184a41200c0d0110b441150420150910508501c42d45030045e0030700c1e003421040311000e01010710500400a403503840910240020090800c118010f4410002c6e003084200200081e14081e0001c58001c0348192403c419242c0a504a5040311210034070f0b0b0001d240c4480400c551250180800040301b60310b400071b0301c0149030000c8000c0d101c0c01c040c0502814403e011849405040c41009101d001c3d200d0302d4040900c50070b060340064034405541da41c840c0040c14050340306 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 278730872 1250 278729622 278729641
    0x60c030a0206091519110c0a11040209090604200309060403080105041a0405040c17070e09070b0a03090c0f08030c01050702030a20010f09140105091207110a08071d 72
    0x4851a0403084030b2401d17071200e2215010040c190b00ca400c14035601c0345003041005000100901105030080d00800180715030749400c402c1d4941c8003a000d40300318810302a031a0b45032280405180d10640071100000c11250380407540c1869041c0346110000c0c10008010071400b800e001a60902441c080d445244c00340e0781e00e00800095030b8190151010002405090076041d080540000742c2040c40340c011051056200c00c00e911040e010000c1c40e000c42e51010604100540b804113900b0781101261001c0e2014509062682800e8814280b0396001c055076441c00c1428401c0056182000d806490644010556106540c0d5980d4001001d8500ac0b13504c1c00d80454842c49c0000120348018450b41c480f007981c082c0340c42c1080c080b01000d99800c402c1e5500d403e41d108030301005200d100c4080e03110718190484070010f040c8490031158001d0440340c00f80d01c40c28150f4180803120060f246c61646c00340d240e80c450826400484e16181c05075112a54501c10405d0108201c0510803003030a200b203481a240c00315035200c01d40c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 278732122 1250 278730872 278730883
    0x1050f040c05010f020705220b03010b0102070501050f0d0c080103060f06030b1b0c070e0103230318030a050709050a0b010c0c0902070302031b030405100509012705060c030a020609 79
    0x4101c000409070400895000380d04c4002e1108480c01503a42c51a9200e011a0108a00800f41300915135030340c001481c241201d01c921002d80708264000c11007010300a00103542c2d03100c1070148e14148800407401c4503503000c0b44c4e41111184400307810140608801c0860146c4004000c2c042124003600740a9a040c154643d4403950f811203400000900594a40b0101c0501000a02151410540d42004003a1080700108001c10050043d400c140c2c2c020340c5981003085402c2c04608400d08140452403140307800c0c001c0082a510034003800058548451080000a0303d845404140104503015540000654013101da1000d0f00c103444048043c00241d0760000111608d01d0400002454402800c40c103001c442c45070342c05481d10038820300407285802c0540c451140031a806180741402e80d800090140040c0c1081080340200d0b0155042840c108040040080d0440c00c00742046008814182d072900440016010000001c0c10b002e0304a42e500c0003208002c41d01c941c005031031100544034040204cc06a03800044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 278733372 1250 278732122 278732131
    0xb0307181d04170306090a020306010e04020304052d061603090b09060105010305010b07031211040f0b040303090b2b1509060801150602060c031509010603050403080a05011811160503040801050f 85
    0x546d84541d241c111200c029000030f000f85040044940c0f89400f01c0d01c0f0f910095010b240203000038101207201c0080d42c5289019105400d00784c2d1850002c41920880c000741725a005610406009101c40b072081c0b00320004c1144441c05005d0350340303400a1000130030010801d1410f840342a0f80034400c1d80c0c1c0741c00b0700910794031034040018002010f00c1105880d103c05544003194604d82d41007002e203004d6540d030852a855540b60014002311500060401c10150444030f560018540b24000500b007005204c500d80d6013118004900001003004004a001d915284e031101803000c640f0490809401c0d154580700b4001e19143c0a0040c081d860196100c100e070041d010310600303c807095801403074196104820010550006080b551400011207a051926520000c009010b0001690b0010b041c0c681414001c10710807001d001040c209280c0b00051150180180d086041c9400410001c2460100c40307039010f8640c401c0c40350b90700303903801ca4030142001c11030040010000c841d040c10082c02151202d0a4a120503601904c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 278734622 1250 278733372 278733379
    0xb0303040e0a0b030303072703020a030b0613060611160302090c0c030904021603020c100f0c11040204030f15020901091401020309040c0807020f03040b0307181d04170306 75
    0x7084401d0710301c1c007401e902400e012004103181100e800400c0c43c54000b501c0700d202043e140c10070209075a440e90404954401d814011081035840c40e004910b00f49030710300000c5e107034071140c4001810903204e5003602408004404030801110b5503400005145450001240850b80500b18802c1c0c210001d424004094903001003441e9030584542c112403100c0ea015012030407490200f8001242d0542d40c501c042d05292448031070f07540000c00719240007800d01a080902c079108821410761028440e034041c005600d0703d089401c0421540965007460504c03145281d139015030040c000240482046449004494010310a1160b0070549a01101110a80c021400c40600143e81c42004100225000180490b011010300549190812200c041815103205544ca1f1022442043c18080c42a034100701621203200d101014600b40380c24138900340c0c0244070141101d0b08202c07040649a002815580c00e920050082c03142050301c6280c0c107207406480620459065030145144000b0340280d01490048030f100c1d80c1c004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 278735872 1250 278734622 278734627
    0xb01141c060617011a010c02130903020115120c090c02070305010908040303032a0302091f0806091605030a050720150609130b0a0b0d06020c120a020304030f0807150c120b0303 77
    0x40e00460b00451000c1f0140d034011446030f2110302002071481006181c0d07000c8d07400455145030301501c040c01c01040d40d102d80d025108003401c01000c100058617a02c1500c41480c400b19807a903090004901c5c0c9510345d040501071794607055552007000213400c010021a8400d807402e118011440b104944034030f502c0008540701800c01c400301c204507071013036005200395240103042e40d2003111a100c0b5400212200c2074402c0104521406009a524003001c0083d80000100c9461410001c504001059404040c1000f04455101e10100c2e0780b950040c40c048003000505418614412a044490303680d07552440114903290040c900400e40d80d0030520324407480750500003a44000c510307440d0394007404401d004200442d007aa84490050955407581ca5485001c1d0080b0400742e05c8040c08100641008520003001d543d40c0002c02c03100c4581600071054500701c90304001c4000d0b184203207080010092184050040581d49481d8000310000303c96030100f8652512a80c0b4ac0304c050150300d115900315216485904c0e49980107 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 278737122 1250 278735872 278735921
    0xc0d260d1d1c09090c03090302010b0405010b0a05130801020c100b01021516140408010b0111010207020a2903040f05060f01230a050a120b0c03040b01141c06061701 72
    0x9080344040544164a00410401d0f604d02c0030b00c0440c0d4008080c800020b444825201c103056090040c0000c0450480d810010b9500d010070040e2244100000c1005001c40072507410207415180510030020849480250343c0c030000d002882e900c0760414003441c0301c1d0500e406030220840d440018020103444108252264a48130020100384101c0e200b440c0300208080381894850151120740540024025140003080c0030420038005000c660030002000c413030303a00c180700510160340d40d01d03500c4044466541c0881142c00b000b03103500c0c2c0300807a40c1200740c05521001081c402000991110380032114010400d41d401ca0301c400f0038403001401d080c400c4400d16031030703c03200b003102104999000c0c035000f00042002c0e800903551804a8800b04072580020030100b10180b030b070014003084c1151a40d000c40c18a1a0b2840d51515640f1120703810818060b8030314542181e9442e842c01d03240c140070f44400c0c0504a40401005c0c10074940f2101801d83c81c00f45d00030348802c0c0740d052401d90005018191404200d4000c02c4421843c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 278738372 1250 278737122 278737153
    0x503041202041b020610081c050a0c080301120c1205060402130924060e0115050f07140601090c020d0e0f06130306020d0c0504080c0d260d1d 62
    0x280e400903644666103180d0600c0603091074801120780b200d5134000d0710700c81c40d101c1c4000c13070310941035440030b48550084007030b103a81b440f81070003010008641c5080c51901d0305441c8100f00d5017215680c0d802400100000f00110b10f0b001c0030680d0318206485181c5d111106621030ba140044d04018000040c8942d00c0030f00454014540450310100d00c4400020004500206071a40c0c0b03000750081d919030b500c107450301c2c0e5421051030240c01408050103c80440041039494a0100c01125208100520400402080d08500d2051034422202501d4020701860310188500300e2090700c840d028401d54440c140741400c200440c1e4008289c44002c1036280d1602080a1024028031904039418000cad241e02c6179042001600056201400002442c040d520041e1a4206036906600712150800480c06100c1d00780300403c01303500e000900c00f1000c40252141d40d80780c4240c0c0b80c10701c840c03841083c1c4502d044188200c0c500094500c003014129103044100d080c04441c02500300711880c2d5020000c4811190801107007801c4c41e91 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 278739622 1250 278738372 278738399
    0xb0405040c110a060e0c1302090a08150a05190c020f061f03060504050c0d121404031205090d17121003020d0210050c0303100e0601080f01120302070503030c0604150207050304 77
    0x2a401d80551b40c0502c4003000042110703403000300118000d075020034075001608000d803001d4040e054407070080c004020195072820340028024070143c002d945642c0081c03411180159030034810042c8000600c01c104201d0006502ca0001d04441d110380e00c034513400a40d000143e54a0304110110507076001c0051411034071508007070700c40200b09403400d100301202e202d090f0701c2c3c101182d15010300803c4203a506502e0203600510401384428160610101400b007400422081c11188001c0e00d000d007842942c4601090210345010b0200c900505003501e41d07502e48030740d02801c1e070040080210071041200e040c0c2d240e61801506292600002e034000101c04101c0d40141800f81e414a100d0704281065070400c4540325100e8a1765000f2111180035a540c00000c0044c000d4001c0000d820800908280c1c50614007182c00c0081c8540520641d04d0540004000c01c3c14140240006005407001406032030703455a40ba00801d94441c01910100c43d072000313030310404c16060014400c0e1110300798410007a43c6042d140801084444 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 278740872 1250 278739622 278739641
    0x7080114060a020304030506100312020106080309100e030d1206120f110a0306150f0b09010c06050c07020d12022103060f0612130212160b0d1103010b0405040c110a06 73
    0x43c8005c01010012850402c80d2034891081413a04514090031840c00341c0050402007000c0066a0610700c0901036040048143c5e00703462800e4a014210f58220001254008140214039415000303100c506800942c1c4440d10071200e0030040c00c203116003540e900413202c40071000f1502400d80c9060403030040018010b00c4000702c2c80c43c030080038007000c4c54494940b44111110002c04420740b4812510400c079050301103001d41c0050926203421b07801c0848540020300a4010b92800178001503030346001650702201e01c0b0541c1e287d035801a05522500026151640006c614280c0c0c0a0141c42920ba078031440000c9014043c920711044240d036815511450b040c007418002a9643c0d035884801400003083e003048880300039120742c101e00f58190702407a090044c48441400c07240c2202c4d032900441e0040bd80000d021b00c20b481100c0d80a01c61544c0c1d02c035082a000000d020198408032060000400002d038031585c0c0303010340107072081107800f046210b050000c282c54001c0041c5100c1c410303803c00e5185001040aa50150058 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 278742122 1250 278740872 278740877
    0x60c08030c031506030702100f180f0312140105030f0303010506070b090109020d050a030e0108060604180b041d070b030106200f070f030309080309090c0d0906090f02040507080114060a 81
    0x4480f91440095440c1d001107450a0040c2d1000c2e541000b03200841c0a000710800000c0c40070008580c070000c014401d01c03001c4101801d040c00e03000901e02014440c0c40d40c1e03045203c0030b12081241c05944044854180000c1c46064840d02c5001a810320149010040320f0481d00e004003000e107400c1d0a50b5450b501584000d220314519540c0e120700d42c0268a0300400401c54500c18070182062500c41e1801400c44c8000352481410401c42d413040240980715101107900395413603014480d010a40c01124000589600c840c10360300301d81045085020600320f412030040d90801d40082d80c800580394030000b0868007003407185800040103012440b00000da40705110b5102c0340d03e242070703805401c4070f1600a407500c0c800c0e500c95007400324030302c030200141648021114041c0070794101652038104044001030710a0405441c0c40150300c00041d20000c07045180e405003849562110303040c4241c64081c1410030068584040c240e00070341c103100c005840340e4400c1e0f1003941a02c4034401845450b8800d00c00703204980c1c0045010805 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 278743372 1250 278742122 278742151
    0x2030112051002180d0524070206070804112809020307090803070b0105041a0a1701060501030603080a08130b0c0306100804020306011a070813150504030c0e10030816050601060c08030c03 82
    0x40034447c04400704039503030074003854900ca00304404028603002d002000d600401c41d001080c800003800c45031a92000c0c05048172007400000b940c1c0d021016050700e0074813240038040141000281c03c3c1d52034001e98400c2c4c650780c540003c902c0d541c4828640300d00c1605070040099140a0043c4003d150942c811411600d18012100001d0714005c0492540b81582d08001e4003c076a900c54040034600901800014000c2880d042c840c01d40346a030341c0c0707005000e441c21180c188003910b000120141030142e044060680c2100e0f40d4415800c095003124490307402518094000e80080c039991441d5806140072a000c0d07680980240b525a20b881040ea0324810001e25102c045802042000c0104000700c01034100b0b00410107003001e01c589400b80100560034565002c800b03005080c8010000318120341d510601700c8202c5070032400703256a00e401401c856401030300024002c02c408140b0400c410360110709011883d1260044034a90f903295a030940740d080800030014100d003420000074086071182000f039500300c00102405035 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 278744622 1250 278743372 278743393
    0x5010815130f0602070c151107033503090c011418030319080f090a0c0b0c0106210201080c0309030d0f021603020d030c031503030518030102030112051002180d05 71
    0x4050340d00141007540c6d85141c00c10284080b4076500903c2d11182040e00346414020b40d002d01d000c5e22a4054840980403a001054070b07004a5011480105820100e80d00b4075202c880d0070b104001641c0094030010207d1240400e41e6003954055000c05141e110000c0303a69003400e00b00c100d00410403c0c90303180190180014807a0a100e200b4048410400c0c61007a1100e00442c0380c043c1358880b910b10001c101500310f502641c0d000700810b00302003064054031005803109a489040c1a0b48a01400a6910100d038407880d034007121844040b030303000c1d24030800d02c00d0341d034501c060b01c0b0fa20380c01006010039038207200c5a40040100301051145c560001c240d8909880c809410954400c0003105c49600030a410350160704036440805000c1d5052160340400751590030100039100b035151550304500b840c0d0000405000c1d0006049181c41c40f0306812580100c0014000e640e42d68507449030070015000f481d4112054820484000c40300c62040c02a034000f080c0480c000c0055954070010000c4036070342c1039801c1e501030040d114680e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 278745872 1250 278744622 278744633
    0x50f09041409340317040f030b16030e12090d0c03030201020a02120c150702010906060611150915060a0306050403050721121e05150405010815130f 65
    0xb4440c14003400074043c6a151a8601c29014803050900e1508014007140440315a070340340d080000303a81e00003424624030381c40c8103000541e038400c0f030b0802d965021803000000104100d1443c42807007822405500480c0d200e80c000250300b03032a20400300f10526081540c1180503070300d522001e0941500024002e114886140c3c0fa1031505101a41043c0c0040c0d40016900310302036010040f02034120080c64602e4600100c0d1007856803902e0884001501d40055000401d010b070740700350090000650005010000560340b5030000d001100b100207201d540f0300079181600c1032039100c60b801500c82d521070300191001c00c1c01e82d810781c440840001c05240d4090081070020010500300c0c0305d4544503a00c07a49540741e44d15042c2c1803d607100d25001200101800d40d4000c028032160b40807600a800d4140400007140e440d07209104d80d03c2c05101d140c07520300c3c0545000108108000c5040f00460034400948081000340d8031b94241a4590b81c1141d007940702c040101c000b1564405070710700405011030280c0100740c040c140e1650340 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 278747122 1250 278745872 278745911
    0x10914060d02040906320d0602090907020109020901050604082112010f03210c060509031e0301050907140301031407030614090d08090c0105092b050c06040303050f0904 74
    0x30b40c60b0340c0e240d01b88060000c1e84606103140c1188108920f5507001d010302c4940120790104054050320900242e40100001030b0191107c41c80c000303060041d14901241c00030300030040c009090748601e505d040001143c0c2001022038017038840410281c542059024914080a80c0c80c60124490083c1000188400d01c0c1d00501140030300b081c0400901d0b42881e50030b010003103203c5200c040400e402a04011542e00d03030880d130302d2640e440d030002000c60700c0e86d10cc441050650152046800c0da0000d002e2840070800b60b42d00045040c0c6904441d000b000380c461900803212010107269005000c2410001030011901c1010522081d00101003150052070300d96a51005840b81c5000c0d00154640c081c092001f9100244005d5013a06a41e1400e103440f8070340960060399498038045014180040016422115110b000c0001607402c00107003040aa03203180c54030501109605001610103000790421300c00303071f480c0500445084a030176a0b40c150038031100940891459000310f400320740c07103a9900d8205801c01c030200764 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 278748372 1250 278747122 278747129
    0x40920130e04080f2d0f070308060a091e1a0f2103040909050d020604030f03090212120901020d0c12080a0209030f0319050f030109020306120f061014010914060d0204 73
    0x43c600c00301c0b425450b1100c40011704244000d6142814014a010785921000b03448071310f0340524094000b134442c240800c2c1a204190001e844d00360a125a1100882d29a10404800c942c1704a0802c040814103a0400e0390a17805000c4643c070805843d004c14892070704c0c0891100a40440c002652400051106a0f241d0b502950001346030365202c0c107600043c0a01402000005007050000d845540740c00d0740e00526814001090b54140f40e9608202415902e0746002401501d0a94049514529070a6088101fa4004c500034138014071515280c1300090348611000d107501640081113210340c1008040a4421103402410804455420320004030580d4042280c0c014090084002d140d4a034068445075030301c90312a048076414403100f00f1814940059207011241114015500180c0740d858510004901d0020140c9249803442200c000342c0d020b81001c42c119026480001ca40900306a450603201c0c100740141261a0201d20827440070810f07410b40840e04840c062008106915042e1250580f2089802c08d80 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 278749622 1250 278748372 278748397
    0xe13020a090e071706040e07030c080a0b1308040501120902030a15060b0a140904060302030a031701090e061602070b0418050136020f040920130e04080f 67
    0x90208120b2034404046030300000203180c50142c80b40100781101002c000a414213005e00d54407802e1502c2c0800a200d800c024545c01b5000e56000c59903049040c0e074407440c0082c15965825901c020940502000540b903c0c2d06a01000c10740c140b41c034140c01504c90b060002420000d171a00e072907200c0010f07601400f40e85161440344144180b03c03000031984e0307403c450180d007081c4001403041084848568000000c007540e50040466070340d540c050100490007803c1d666000a40610440c0e41c100d0806400070b07000800001c40090680c000da0340d82001c0001d44480c2c11581c0c0454001d1800300703c20065000c0c080c01499950700442d50382c543e8030300221045502c00d501c10032100314210881500c030300313050140c0750040071b00e500008a81c142c00240110030130080e0902c403d0062102134038007031142a80d019942c0c50880c1106064070f4541d1070865001400004004c0c50046000501c05101c40c6000c409490880ea500114400000d007072494541004d000900281c0e29404248003003140c08070f950300108007501114 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 278750872 1250 278749622 278749637
    0x9221d0109140303130b1305070e150402030106050909091f090201030e0604020a15021f020d2f0c071203030606020f07030818010e0a030821060f010e13020a 69
    0x2400c1841c5082402c540303030030142d0810400e21210a001c100b080100c140c0022000500b621040d00460380c0d440e031280018401d016101000921140b40071010784620182c400a5031191031050401c8101d120074081c410104805100001141c14445019613000b40c1d06011a0b04107030900380180c810b011902c0c4107170354598440c10003908550385030003200c4004021000074046410a540080c4481400d8050110084c043c0040428007034405c0245041401901c484070600c803000ca51480040e50240e54525085814041c5050b640d03200c0010000302d80d0160400e02c050f135405042520180d91000342d03040b01c68803610101092803e44040201c039003d2180c0c81c00165a45040c01c046d007065215602090340d0303007125034100041802801201e9001c038850400c18420700c0c0c071500680d01603c1e588080d503000303189044003000700190301c0010070500d96440c0380426174401c06000c0d640c0e028030465400e13421510100019130075501541d030200020600910800304a0500c94004080341c0110209034000744d1034 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 278752122 1250 278750872 278750891
    0x60609090118230627040305130e0f06150405150d1d06040609060914010504050606040207080904091a0a02120c12040f110303040311030c0609221d01 66
    0x10303031107248032100550f094803480c1182207071032041c000d00c001c2600307018581c0003040c01001c00b00c06620079401d0311202c2c0580064102420001c003550413550310504001d00300c1001103140111310205510542d442e219904c4259242014480002088a643d41c1d220106100200711640c841600391080390300764020340d4481e1080401c504c26600f5401c80e01c03408401046610045e00c0c1c0204615600503000310011031030710755070b2421000030548120003525035490b880c0283c0503038206402190085000d80221080c80e2074100402040741320b0614001c241d0134082040c80b203a8202a0000010640500b00d1988031a41c501c00014405104072031f8101c6190b8001b81803580c500300c444003942c0216107eaa01410280380083d0412101030190010b0403240c0b54445506c00c004070000f0300c031900c0001606490b11283da83c9000c10399911010f04042c82401049211000ca00b8580203844184d14014610040d04064002448100b018802010303001e42e1140c49501100341d9030342000080200c0e00c2d0000440101 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 278753372 1250 278752122 278752169
    0x1b060d0f021801210902210a02030c030d020d120f050c13150905061b0d0e0306150307150909020a0e01020d031a012a0308070f03020a080f0606090901 66
    0x140c1a10042c1070024000d41d80703414024100d13040030b04040c400e1000880d00e40a000058066402c040d03900a1400080c4000200711404503000100503c242e04481029080304105038840c00352454500050344200c200f4072080d84074450a182900504800280050086240390252201140c0d02c0d2025a0f0008a0610b40d2105d0000e0720000e04010300106440407121000800014952007800d209140206d00d60411120a503003564208103100c084a024580250003d090f040540c0d89040c070a009450014010590151141c00c190b603000703001c0e000443c14203030f540520b03865441909040101d0800007003455500740c8024241c0c02c3c410303283d040014130742000082c0303042d80841e604401c040c10031f181901c02c0703280b00000c0140200c090138450f540c4182c0f4991882500c00f81914006542c0906912805140d004085c05020702c19941c0c80c280100c02c18103041d4141e20030f805502c400605010001012952110364094010720001c0c40186040e028100140b0081070a820840342100040400c942418 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 278754622 1250 278753372 278753407
    0xc1205090307150b090c0c0c0901031103070803071a07020f07060518040b10030f0213030b01050f01170402100e04020705010b03010b0a0311060f0f0c06041e051b060d0f02 75
    0x1000c08209000d031420b218017003550f44070007401c040003481010074504d01c00e9509000510344824064411a1290303900d040c815510440d03a5003642c002d006a580c04a0101d201100f01d80070703950450311822061680201007020001d00038011000c501980c406d500c007022051061340c0080c03d407503503001e40740c031500b100071007a61040409a620039885c100d40c410444d1544802d050910559050010301803111565240203403040c000a40404c0115400200c10803900082d5070b810b0340e4043d0f501c03403101ca004030011b4035500126131141502004201c00074006207000d48400310915101c1c40c2075410a491000420180c0e00107500032100e03a5159417018942d401c09201c0d1186489040394000d03201455600e401245401500b80d00d0700a07600080d2204c40d1000307020840300e180e4050a600303030f03848943d41c5901e03440382c1058a0845a1a940c554281070951400c02c060110a4008000d07118050124100c0c070b228078200248142c1102c400c2c00141700c00302c0d5034821113200f295081805a0380d652480514811003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 278755872 1250 278754622 278754653
    0x905010f0e040911030a0c090c090302090a0e01060302091305010c1e111905030d06060302040e010510120c1107080a08030f090a060903090303110705060d0c1205090307 74
    0x45000350000d0a1540084401c5506100707607000684080c0704c1c1480720540d0203030b000030340d0503102d249494002c100c0b0340c1440c10300710350785100100b11070a20364000300c41c10991880060b5001200c1004a03121002c0c40c0d214411b054106c000000c1d85a940b40c0c081000d004c030442d440c0b280e4054140304503007400300a00400300107080d1071500b004c03801c038100ca40102c0340809118035420064505031031403401c002080251000380d50420a8a002801303440c0803540d81c0e0080c0c11080540e0b05090700000c02500034020748069035404400308111740e007802c1c1400072074140c4440c500100181c14100390000001449140f0403130203e07540d00c01c21814807030502417400845c0e52280c119039111040b51000b00b000e90342500e81024140c440d2440c03944803d01e589152061440c4064889480c0071582420160032501d108100d80c4680c664840f08110860304940310301542c40303081d402c00c400300095030088100754400c00400c0c0680c148861201c8464540d101103410440b00c40303030309901c00102141440301c0c41026100c06c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 278757122 1250 278755872 278755877
    0x303050309010b010f021e190b0103230a080729012123100213050f0f10080a060305030708040e100f0e2508011e080309060c0c060c0d090501 62
    0x4203110160000d41e82d44a9034507d10052a4881f0201007461041c231034091000c40d0300c41290070019103030a003a03419400030301c0200c8a00401008805201e6600c22400000b8a4124042e200c2c142c03054450108035072140e20101d070300400c149500001600201d001039240491203400c90b4241d8182074400044020300b031011015540a41d00310740c00990181c0948010041c40b172042c03054a000010203d141c014003d004416190000c20000114201d054011040b51422a00e0384030450008040c41030380c2070004001ca81010b03060828a800c1400fa611040e080442c558000848a65984640b0f06541103440304980f5928002010010b0090b41c071582d5030840391200746114030301d01d0300740a000b900459103d5955600d84800010b07068440114010301c4034182d09103c82203c0c110440001d182160902030192060f0440741c010348560402e0103c6000d039018580118500242b400130440d15030440c0c019900e080c41403c5a10360a1b8490300043d00010900e18014440003010241c054044015500000d04 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 278758372 1250 278757122 278757137
    0x705010509151809071205060f0d031404051804060c03050c190212070303091403030106020705010e040b060c1b100903021201090b1303080906070903030f180303050309010b01 77
    0x1c29030b80e41580301e400902000c02c4150740340c81c402c0c1c480384500c0180803465404100c0408004800d500203461070800b5090500c00c0019548034020030010b000d031500a2074209a620320200d0001e4065200320702049030b14801d07141010780d9400050608400031203001980030801052104100641c00fa44400d4806814248042d20308060b07420313a203001e181c621400000f50035448a03a42402845010341001e5152003440d6203090340e05014000d4001404126030310366401400019880b000f10590307050300d4003035000c0d1554034500001102d980e41d6080341d003507110380c2d20110f89500b42d540c0e4008208210141d0301600d0301140c9168030181034801b04524500416800351080a0942d0010071401603a5040b02c035201e01b20380015455004140c034000003041d5510f2802800200c0f240194040c00b00c500ca55600d0302503a0710309420b1520344001b900d003c1c0106200003000c2c00002e0040741414441c00740e80c83c0c9104001c45c03400f250a0804203650080d0085000042031100b440403c0c01040001807080c00c1041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 278759622 1250 278758372 278758387
    0x20c0f0303040f02091b03011d0a09030203090d240b0a1d0105130b0301050403020606030c031908072406050a050301020c0d031e142508010303120605031e07050105 72
    0x1c03c0c0644001c00a00c40d01d2404006140e40b00301c212285a45c0c803004060a03142c1d0384078034500000c48c44900103020510400000100341c401c0e140114001a5419405942008007000030300201c031072440d0040742d40e1004901c00c40c0140700c1000040100e034154071703000f14a1802c003005102000001350006084030241d041828000708207a0075880c1103500030707100c6602c110240018003004049482e0000d038103501f4607046c0410f240d0b00060403400f60808900307840c0808540d4040650ba00d4035001010703480300c2da00c420303270300483e400c5005002e50358055483c03110b40700708000c8500070200041c0c00740b948050f540d2906110a0030320712901c0c4098034054008500e4103602e49061903650340340d403032200d040640310f8880381030304084a4504190b82501200c14000e0030448001030500c3c000464042945078100641d48a02d09610300305885403407000d484508441e400e503102142c2c0e0014040640c030200b0313200e104c0016113490410103000321f000002c2c40748174140996041c460038a1015070010f41044018001503 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 278760872 1250 278759622 278759633
    0xc121119030305130804031101032a080105180a0504290906330a0b16200d03030b0d12180905190f060e010f090b090c03130321020c0f030304 62
    0x807410b823a042401d4401021009004030050450811061130881c00b80080d80c6850b051086e000f8160b00958540d40c04507a222001d020701c03c0e408142041200040d080030800300c41060b407003190424040d207001c0f160081c3c0d80e0f404200c1c1400070b800c020141410b9100704284150207006c0690400100c0e2401002000c0c8007040842d2010a19008a00701241c510340c05d23540d56512503004020001000302545404201d40c076550902c2c1c00130002e560013041d54400000e88030701c8510700321040d0030080950031070700c0150301c0880c005d10346424030b40c2e041213205229901140c10f5001d4242c00000135a241c9403003101549002d0fa0100302d540c01310440505020030b10100c40303804080000d9060b007036100024140203184141000d0011a8031150007a01d200e4004501401a2515241a503c4002d01489140380c2e900500400c11422140840803500a1000c10300341f015603041d6481080c02840d000303040000d030b0502e01d140c00b00340d8010f500b83e1983c009540d0380c416600784200c0081e051810095411841e26440f017 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 278762122 1250 278760872 278760877
    0x109030e120a0b1f050d05060403050a050f0f04030203010b03070501140a050f0c0f12130303030e01020d051f0e060d0204020a050c0d0c021f0c1211190303051308 71
    0x48512910240c000c000070700104214041c00240c0102944a0344e00348041051107020a401c13181c03200000283d404140740c1090b503140326070140c0c49001010301c0c0c3d07034680f01110503420092103c810414100004a181d04d02100a00700c0880900c5980740e03182c0c5544101400c40e001c0c01c031040c1c069000140308004c5a0b0700050682d00003010654003560341c40b10b0320800c90360361081c0484080f0107000854412074071240041e04102d180f0318041102c1200120802906c00303805882d40810201c00d5002c41030000174800e400c0802c503030210f0300c005401c00c0c8001841d0401d031041120004246880003c80306400b603800c90980f0f0003841281c1004c1040d0410300302042420b201e684011340503076000501c00c0130303182c490001c50f04455100c0041c2d802e40101600001d020342c091950582c0301c1c0800000403c002d02030710001021002c40398a540828040c0e9a41e480001c2e00599010024803c0c400420501004140f200d104841028080c0784480f01451801a04861010f00104441f0302c503035040b4070000720034904 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 278763372 1250 278762122 278762147
    0x1060e130c020f01091a010e010b19090902030405010b0a050a05130908091903050d09050609010c0305090d082116081005060c1f0506030d120207140604030e0102010903 74
    0x4201e0301e840030400d0703180440030448000a50728108a800c00d01803030354400b40c000085100205c07846d03641c494028a01c800c003802001c2510004201c2c18100c002c11020030380200d91300d41010420b26507114141d00498000700c90940e22651180c803404070500e0100c1f5500080c01c0e003210071401681c03d003000b0514120340c01888169695031942d1080a0082d00e00a540140d0002020281800c00f43c2e2080701c24598184402c54452007100c2c100c2d41440c0c05024038170b003981c4018108508224400c401120b003031070401c200b40c080c840304000003030903920b40c510303541c1807180141403503075842140903007030281d600c0c2c0c0d044501c64440800d170034890310408000342416111f8040c5441c1441d40c484a50030ba0609019610035075004100141160071450086850074840c00e229081c91200840c105408041d10800c50300103078903070030604c02c104800d402404000d4a022002500604101072aa81c0581407005014640271540c014020881003561000440e8001c80c02032009201c189195640501003001480c03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 278764622 1250 278763372 278763409
    0x120615120902061e0408010f0225060e030d061a0309061b04050a0314060f0c0307030e01150b090909010207020105070204020f070515090d0e06070809011112040e01060e 74
    0x1c0440040d0f60ba03140950780c2562042ea901091400c048403110015480340c03285042c0307075080494030885400544290b601c1102c0c40844c20382030303016000900304040d14200c01211440c0d034070b240001422508001804290203903200008819003030400e440101d190403000d0031402c81d0104100300203241d02003280754104414420000b40c05945031965411405250055504100588800814000d041103400c0032174840da410307a032461f220345480d1a80c0d40300407126811240410000324401500ca40e010040b42c01c4020000160314100c9454002d00341c208d0703800303040342c080042000c001c1482c01a01c4150800217a00085203040c4207a400a05240500e13000640300f076602054020343c004660040b81e1001e0780c410f00351003a41c0016001070341081000d50700b042031881849a11100f4500400d4030800104c4c009182d181800e00070b50320350031558040f114a50420000c040d041c0114203007000b00c0c440c2221140c00142c1c03100c2c00c00900f04010030050b03201d441002241c1c0581c100b6900c804130340c080e03d1600c91 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 278765872 1250 278764622 278764631
    0x5121204060f1403090102211003030f0c050114010801050c190e011223092d010b0307030f110103050c122d0604050a020a0f0e03071512061512 63
    0x7000549100c4000c4102c1494001d0001c01c1041090040d17008002081180b201e0103107003020421540108d24003203c1601d880510740701c05001181c040c80c40140d8801003440c11941d01d52590340c2e410b09403030150203003484000c2d20303c0c010701282e5800c0c00340580c4010030483e11820401801c02c0d00c80d00ea01d48821140500040700c04a0001e41d2007180d0000543c00f004605100300c185140c64100800c4008041041c04002607002c50700000c0c0200710710a03403840102110151600f0150f100c0114200c0c405500925035035944110016141804204000c2d070055202c500340d0352060402100c20000701110504043c5003404015030309101c01d098070840080400c4030410ba95846a60405080c404683c1f003099440341c203d05009030307060b0301d00c06100d840140d03020300031503c4101d00042130740030b82070b41040030a100c0e9411074080b510606110b05c00c520001c0840f0311003030380c69200600a240140c04000000c030034081c10684400c0324081c06006102da4004440700030442c040007001c0741032a03048902c103240c45 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 278767122 1250 278765872 278765897
    0xc030513031713050627060c010c02030a110109080313030e030f0d03060902040614031e04080a1808100e030417060f010e0c0f0c0a1a010512120406 65
    0x190600340c0650340c4050b80c06032460004514281641080300e40448203d031002010136582460025241201c5c19085561042e00c4415501140f400c200784031903420034014072104a00107402d0140c103100d040360340c0183d90350b401c01a6009103120b100345050340c25070f03040c500c0c900006030030302040b2a88a100c4014402d182c900ca454100c0321480c94007009907151150310400101703040007103000b841506040d03c1c20002c013039a40700d541090b4015440390101040d40e0400d60444005c03d40021070b4040d50030401550b85028001250032a120143d0302a1840480032968066007a0058061200b09071000c1c0c44c080e11030715100405542c0ca80400c42100f20980b01d640a0a41e00820020384001d80604000b00017400c8a010000781d58030012a5402503014000000180c00c08800c980307d4001d4041092892516513000740c0703c400fa502110503102240315500710b00d00400c402e11043c03044040020301031074147d407503c8100440d040c869583c600a9800c0100c1c100124000101101d04480311420a000240300b03 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 278768372 1250 278767122 278767147
    0x20102100218041401050a0608100621111201090219030c030e0a060e070e090a06320108010f020c1b0d02090906070201110903060727080c0306060904030c0305 70
    0x1d1140882c0c0c0c0040c10010040c800910608402d8140c0b40c05a502000c565680c000c200c41d015400c1c0ca940d40a4802c0200500140d44924600c0300708240002c11044100002040c11080b159080b501d13800142010030340340d0309000074130209801040f10000940c103005030342d18050041c40844800c1e80c2855903c240250000303001c2d8008100d034618030300039a2410003250501401400406100032103e001c0c660002c0340030080300036541d0058149500070051114103645181c02483d0002d203c4640e45070b007245580303680310210b2003007440054a070f02c3d82d0710b107501d45108542950401c50b41c0c0514540140003000f01030a002070f4010b23542d00c440705030045a0400e400883c2e25020180d1010350004075980c00c1100e0000c00050040c0030b03104507070080200d80d10840c50700131a4022400035031392507040040843c48261054038400000907094100703401c18500e0f60602020032104c0c3c0d000b14025080290504401c0ca0240485507121030195004100ea19281e500200349000c2100000c0c01e02a0216007090a400d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 278769622 1250 278768372 278768407
    0x609010e13021c0510060212070318180b010203250204091205040f05060f0318100e0c0103150b0a050304030c0b0439260d08010f080304030201021002 66
    0x4000030110f41d14050085201c0c00c0c0040c00e011412160708080109074840c100500d404202c4050b98064800c100382104840c2555100800c20b070100038541e5101070ba1040340d0384900b8020700708450843c2000f0302082c80035094034035140009065400c1403020059802c0c4580507905a0a0b013054100c0b410a5180b000500400b008000a003034060000c8040a0280c2c0080080050f00d4684030031040c1180c4d01d0007040464131503400c101500403000d0000c04d00c0004420807420606503808280c42200340d044004000300c41e1040c50b201c006621640550100c1c1d601441070b42c7c00c0b4107a401001c1c2045082c5600d5017143e1060610f0041007240000000d410b041c401c0121070480c543c400104a03041c1010f050446074401c9454150351151410302c1907810340c4000c1920740c5481c1e20202560324441c0e282200c3c020560004600d40442600300001400304200c09105a8607507070303444d844200c13503541071041c0c0300010134207600300004a40c800c0100780b026030707000111400b403000d40706005a07403010906540124034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 278770872 1250 278769622 278769649
    0x61d060901290402040f060e03070f062a0203120d0c050301140904030c0b0411040c0305040f0b0601020a02040501150e030a051203070507060e0d110109031b0501091707020f0607020609010e 83
    0x814914001142d4a0307403020382301c0c6981030700302d089401041d15820308199048641c030aa40200d0810a00c80c004986003200d00c031040f0041010304004200c0580220b4203000e01c015000911001c000780e4078201c0e1810b0712603514a8561858010b0466050140122800110500051045a039003001800305441342c8110040c00b03502548050701d9040c0b901d080311503070441e145101c2c49203044c5200c04e0800c40c807922400e481035802c206692011241616540c00150020b81140d04600030700d4a11005a20b03240940c0c2e0080407081804e02090501030401032144176840b58580c0302e03400a0f80130b0030128000180f4501300e010101c07021560b03502da00205131060f2080c004020001c2d42002d0700f00c6900d0a0214101c00c084145485030000004c5000c1118200c444032034009000c1400385050b80c880301c80b14000010072910038000000c98801c00e07150000581100c42c2920070130b003c0020301d8403c50410700f41710306003800706a901904080700c0e0340c00154a8020828030364100980407107031944544e140c442440e0706 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 278772122 1250 278770872 278770889
    0x9050613170a030608010b09150f01020304050402070305040f0b070c03080d0b1002030904060e2202060903030c0a1515050d03120c0302070b0c0304080708070f061d06090129040204 79
    0x1074000c0540083d000d4442c40c400e0340348652030091001341905140c03906030300c9540000034041310462242e041062045205004504520062101040c280c4a0f40b0041814030302944880b03880e1443c100070000ca400310f80c0c2003034030303d03c20520000001403440712080c001e507035220300100e44803e801d00000000f00719009a87d9408064244641c0c4091340200091081c040180c074180011512854000102c0380155030400c400b04098280304107440c0448c0c045041e07240b000304664a408500400249560000c0d00200940d4014000102c200800401740034081445c1d801e00b030204085d010040c088403031103441000d000d080e00c10400410107108142510f412910048104000720100030001e0003074000d001c080300c40000e07041c08680c26404032000e0f01d214a0340050028904200f650300c5455075000400215100300703146100500007003190158840c15840e41e9100c690b0000c04203d4245844405004030241d6403400310180703424642c0d130440c06406a00d200828240380c21940c042002441070b680710800 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 278773372 1250 278772122 278772127
    0x7050c0f0616021506031905160e01060f08060d060c11010507050a0e01051c1104031a0615030603070e1f0f0515030106021504060603081602030f010905061317 70
    0x30201201040400100c026804c48140c612001072150342c0c00401d8071a00d602d40c1c0b00090703d40441603250f541c40101c0d841801a039070b10340c0c800014084d030b250f402d421010081c1e105d40014004a42e20807014407070b070411440c02c3c02c7d942c20b1110201d60700703040441c8054100e54960410040302c500a0b016000c080b94000d00030406864418001040c5030042100d94000030060308004049603ca40c05460380100203505824824081010240c0200814007c035421078009003c008003107154000c82a0603804a5500030f0b40c0385c5007160400001131000361003410090300c14428808143c50000d4104d081d205101d01845081c0c032600480c00070302928034100008080b1450001c612454031684443c116042070350b150300c1200641c6446405030002b40508001a80403401c0d0824000e078400d40c0319001070040700c000170b0b40c0d9200d40b03074045103911500d840b4040304a0b480007401142001c0027450490000d0f03e0003088a11141c0d5512034503207402800400030305004201d10014030600a23803445003600c100d03447c41d6 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 278774622 1250 278773372 278773381
    0xc14030a0b0f09070917070e01092703050301031101090305060604050403030b040c030902100c08030a0b011b0503030615041505090f12060a05010e070c061802030709061a1207050c0f06 81
    0x1000b01505e070280640e080502e4003500e070a001d0015480085e5128940c1864080e801c1221503001880000a80c0003130050040207140100d5500000307512242c040c0c0e5501d5a258118200b2405a4032000103a82c10441c10544c00c001041012409640100c3c00700c0b03010409803a10706044018203490a00c2c680c2c41460200c1100d8502c1d0964042098103209640f2460700c9603030340d9000d40319002c96143c06840c00c101000000c004010b60341c4080c003a000305040500006600b82404113884241d80b108941650000003808907038a46070b0000b030781c883c1199030143d00d06410aa00d24482d00d800c04850f0b0280000450503504990343c0701d64103100f0000141000d1946412210004e95842d4140e8117081d41c0351800c0c0c0007040380005007801503c21031040d1a4000803035665a256801425078901d413455600400e108540181e4090107001c00410842e500404c0340c13420841100c60300d0440341c15401102c00304000b14540190740001d040e03400b800c80d04107151504104081c26043c4842514111500d000d001e0802 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 278775872 1250 278774622 278774627
    0x50d02090a0b04120b0a14040f08040902030a020a080a060501020c011404120605040209090c0906090901230702010e07140f03070305120a1e020c060f0909010b0a030c14030a0b0f0907 80
    0x1303c0c1c0b0701601c0790780e4103610b8101d25002203842c105118007000b4543c000040100b0f03202450204410312403480e05140c150344405060890300305442c1140100d40000d244200c465101d82c1d0250080b014100030000c040c60100041d6403403084500440c14402c0015600c01e480490b001075400a00c280c200f65800401180350007002018200c038124071410420000c500c0d880400100c07030810b800040e01134031071901d911080000c021002803260500f5900c076444070311800941050101c3c0a84020008134681c10010b0000e42586c0052801c0802a80704103010041d940c2c0903a04101180b9042e101c1c190094418000b09003002d55507000074000e42700d00380341c0c1060310381882c006000b4440103a580c49503001e050442805003d2944542c0d0380181d010700044252450040005c00b200b5103c600814074006028000c125103000907406503044440c0802c0e1521195014052640c0b119024541030402041c10103802806020107171042070800d9649050551070740f02c070b1451900e49034008001c0402c5d0300c1d054000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 278776978 1106 278775872 278775899
    0x5060403050a0201173306070c14012c18040804030614070503040210020102040f1d181905010f050f0a0c0207050607080c07031e21050d02090a0b04 65
    0x4e02c1219038920004000b4940305103001030310030740307801d203c944020058070400e0305105040804092a40391412016420101d0b0300800d800814038100dc215101c1c0441c0b11444e00780c480400b0f200900c04400d01034000c40e0b02c120400d00541080500c019030202d0240d038410003240f0140301182c01403916043e040000d0415200040c00d0955540b402c1c41100030035404110340d10510031042c43c02d03d0f0780418480c3d001461941038540c100d005040741d59141e1004400101d228003940c8201c0c10800b003034100030408111400113000c1820240600c0414110507185030855901d005042c042c1036002040390380407110010902070400610381c80f03110142e405000c14020300d000d5444007200090b09040034100070301c648081d0407000700d464070b090000400c00352409543c0e00e003004d400018559201d0101d444050b00000090303100c0241801240021840382c2080b142c490000c02e010903260340c0380c0d03507 = true := by decide +kernel

theorem cover : BRFrame.Cov 278597122 278776978 := by
  have h0 := BRFrame.cov_init 278597122
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 278597122 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 278597122 ≤ n) (h2 : n < 278776978) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
