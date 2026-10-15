-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4043
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:24:58.303681+00:00
-- url     : https://prove2.me/submissions/c2977a50-0ea3-4ccc-a7af-94c977396cda

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 726978417 ≤ n < 727158273 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 726979667 1250 726978417 726978449
    0x815130302150f25080402040e0a020402071a1b03060d0f1203050403030605012d090b070609020102060a0e0d030c090528150804060b1906020a030206071d01050c0f031201 75
    0x88800c0020b10f040c1c4e80005405c000410701503e42580414102d014020449040c10803d40c0403030240d80114400307903040085025a015080c020141c1e803540443c100240690300f4048103a8650325000c007800840c00b510b0281e20080c10017040c078601031500c1e81c120f00c00d020012450000100544400c4a08600103400c0c020005101c0d40a40b1444800031f0309c030524070a8003c1c8120390903102800b881600d404100504c140090308401040080290320701903880070425070003500001e85840c001901446a00780340951030000f104003c5440e44e03c061451801240d04001041c080b201e55440350861035200100700344403060041001804c43d010402d455a440c0e006980740c48044403c8000c045490100b034000c000140000c41c00d45c8080c0300d080006185031003110300080312100e4242240c0010f805688080414014950100a413035881002ca1070311401e02283c0200300c50100094001180c14448003041c1c11a200c40184000303404003600c0e8085070b44401e03900f0020103208000384101d00d4030740d842c0b840f = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 726980917 1250 726979667 726979711
    0x90818030d12051b04170c0d0f0609061d01060e06090c071205040308040b0d0f05010305030a1101090807060b01090f0803160221010b01090815130302150f 68
    0x351041d1003140c5031a1001015044419840030300001800c8000c1e190712601643c00d8801d0304006440070302400041c14081c00340d03040301d080c40c0c1900ea0403103912a004030410f4100080210002501c143e034896000f14051460380381440c0900009009003040140d0a40c4104003200705600260489090966204e0552200814000b00b03003015207030308240038420060380001c40c01c0108a410449800e04e0a13a1a02365070380c40c0ca88840c0c00940221047d1000003074045141645405002c1d1062840320042010794034596400c0d41d00d22503000d0345014000740c0c1003d18943c11081d480300c8206a044040299200304920b40800108aa071501c603022489030320010070780c102071b4100c14040d10290001549800c1c07002441c14615442c9a60403079100001000403100c80080c01e13010035071107005030008170b00d00d0301540000d00407215035041300400b070307000da440541e1420b501c201051b0400542a080c00c207400301410100c0c28501c440e40506c001e10000c10500c02d46101d40d42409109200c00b0440c5415260001c07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 726982167 1250 726980917 726980923
    0x1113090e0c040b031917030c030103061d0705090a14131406090723040c0305090c04020f030604050a02040f0b04051801030b040b09030d0c050904270f05010f09081803 73
    0x20a1054065215034221006011105d95411100d03002d1041459501c4040c681d1a203e0b5201300c4041e5203588000c00100100b00032405404412503d00c2142605500000c42031540d81c030181c45a980f00b08245c0e00420401e00f2280c1c0004401c0760400d03600c0b0321a00e03203490b030705501950390b07081100c40c0860002c0071140c00e4804900035024a1012000c1c0c0b80051408410032020151410702581084510305007940c1071f9501e10505c0300c0a00d9a482c0880c292802000300c0f0b08041800050034042d50040050800100b0040d0480340e01c808100d07800603554940d50004002805903030840b103096600c1c144003140c1c42000002601c11541f08582d90360b00d0070100034010420950a00c002051701c2d0b600c001290024100c44000f9601c5000030b0205c4c0e0820a190740b1b07000660300005401008502d000401400c181054040e40603012030906075003112107407101d1803940c0e0188500c0c000c0d024414124062041010070740103507044042e050414098044c5a0800c2600740c0d12915104940d44a08560b242c8141404 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 726983417 1250 726982167 726982181
    0x20c0f01140a20030702150907050303070b090307020d051c09050a05100e0a1d100b120405011407050d1404051e03070f1103071403101113090e0c04 65
    0x3100d124a4680b210120040680f2240074081007030f0441401d01902c1d485542e014521401c0d1640c02040c4028a807081012801000b90083e461500319850034041510000100c480c6c49900c4034101100740c6c1e401d90b10310304500130700400035030041c06204d8807028024000368040b4103900011011401100f00c2c0d9060b01c00e40341c50f20400b50072000074001041540350030b804140458296080c105007038600306000840c9000241c001c5260041c40c4000821148480b951441d4400c030103072805a20b060405443c103805d400b51421030000d103100a0009410844207400110100514080001c19410300c8500501940c11500441c11420714040080880780d00d8848654011a00710025000415045013113800301c07285400740b5071140c0b00401c00300000030780341c0c64400d03502c0380a19002d24079a6a18801c2608149581d406505a59540c050300c0c074150354085401c040741c180079613001170720026040822200d401260b00c020440440c501e00019610a140c101e44480030042066441a00540c400c0004a4200f = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 726984667 1250 726983417 726983441
    0x40e0a02090f010e270108010e010b060315150c0105220b0c030a06120c030b070c110d140d0206071e09050f0d080a03020c0d081326040603020c0f01 65
    0x52420030b400e40e50082005500c50080500a40c0b800a9840389105d101c00150440603a50042400104034000d002e2154081c0c4508000081c40640041400114680005003540c100c44c0608404d4190b1075030340b0701000301010750451529484181c000c0145009210489444480800321842500741024845420022607804030310400d460701d03204100c4005400041000d03910550701c0307102040200000f4014046644600943c80180b421494990100140600914188891001c04000050903207440d03140070001920300580b80c0b829400c100507007510101c81010a40107040d071586a0550100d0100d100300c030151114600c1b1008680030714482e440032083c9a0000f4280b4400b403000c1d107007103041c001d02200000c0100383d002e0160348444d41d255229408030004070b07500168921110b0024042034001d0f0f111070030501c1d044c0c90181c5d01089075860011300280160380c10200b001100309410032003035020708141d20a80e00c03503482e00c4001d0b00a40c40041c440141d8403c44818a503a000140030354080a64 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 726985917 1250 726984667 726984679
    0x40b040b0f13061a19080621070503070f1412070306020a030908031f170c130f0e0d0801050303070308060609030109120522050d03050c01091b0302120d200f1002040e0a0209 76
    0x1e008e0340301ca02400031a5001ca031840c041c070a80090143d40400501024080c03200021800302c0c0380100046100300940550f50164140c0508114030500104410b001c03250444000b60b503546100400b1070042c010303454010200000481408080d8411300d075042000301552040e03420540e1940f90f119001c041c00211101640e205594115490400e541e090341600c04030f100128080a0701349801c810307105035a84040e06503101d006402103803640a42c04500604d0705401551031b00d40316443c001d14103240140301d0340c000c0000055403c01c82e18250312440c041504420f00105161203410300410070340c4217107a06013015600b000043d440c1a0001c034204109c60004143e850045001c1c1d070241c4560b0020310640905540c1c1c2c90100c00410818021181400c80e02c0c0810210b00e030440c41080f80201c100c01469869500458180303d00a41001304100701c03144200ce0307030b032060108002c6070f031410001d600820082d0081d40200100300d58a0b0f0050300c04e4400000300225260b58580810b02203010b40d1021652283c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 726987167 1250 726985917 726985939
    0x120412032613080408120910051e180a0b0d0c1b1101170901060609152f1f0617070303031505040911040b040b0f13061a190806 56
    0x900c81c80c50072502c2c80e11940d8050b042559031003401d41440c95801d025041da039030018032000390f0b01c1d10801501c41045c2c1424410304211040d4180c4c2040d6200316110022018000303a0340020f00c1520030700005a0394001d01ca81c503101c0d03c03044000364030b400c1942c00811640c240824400c3c035a0203a140c404020f000128809007040c01c030b466180780459460625418040d2600516001e81e40d6545071a110300c0380d2200110b20300317143c004000c2201d6080c1d44240c01d268994041001c0e13070b5612190003042005a0450b5158407040304241441c0c018103041c03507902c0c074820a4485442003500803c415074908015038108501c0341e544100c9415034000d603e00413465004220103000081c002d5029a4492000c0604450841d03142d00c00f140c21240040030541c0c07400f4410285000b54134190017290074011040c2c1d000c1c03000b808400045890180054101441900c4031441240c00c4440360703101c0c10040041c040c04c40c04032400700d81d00a00ea42c0c041d18951500030078150034641160700584880f4001c0c030024010101c16 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 726988417 1250 726987167 726987181
    0x905061804110919082a010e040204050a030c09050105030a2604150e033c010b0307120c0b12040807050a080d0f061203020a030804051204120326 64
    0x40c0100009600d2070141408140c3c0c66032a07482040e94045141242d640400341840034aa1400804403841d50011102155500b1004d52000449159081c20309000d6090448800020b0283c02150000d50b00b15040c00d0b000020310500408131001c45503090010040c40c2d8840083c19100c0170110000b0344003004404c001c4040401c1c0c0800f070f88403041c2c0841c0da9414603444000300605c8981003030300700000420f1030703402169034a814070251010b2031b1620500d01c400710342e11030030303180300c20202e0b0007040d111103c4403002d44c04030000c1d080b072032620900900b80c0f00700c0b40c0c440600c607660341162602607455021040300030840000141c21900e0203555207019810564441c0d40720300140e0b00418086a060080d503440710001030100c005413070050a008408109114200c0b0b96200f00d0b9400e170b00c480044d04c440c003034007008244c000c641103802e2a007503d081e803015030300c505181c0d142142c482e078480070030500000c001500308003c084450141c1d07c04e03512528a44206a0f098548101c0c1d501c101403016031020125840c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 726989667 1250 726988417 726988421
    0xa120e15070804030905040515010806010f021b030f1623030c090a0e0a0803061003061503230109020a03060b0306010917190602030108060603071215021c06060905061804 75
    0x2125200e440e045c0042a21440400c0c12369401b61420080d0480c4070715810f00a6030070401c4a03500c81001c1c078145501d8401200002d54480c107100c24030011110b2184202170645040c80003a82030a00c1c0c400f1181e80d0b00c0700d0202c050842c2040c0c46003200c4613881c508605160280c41c54200307000d01c80100201203103c0103904010844102601c10a2103d540340d880040c0d400c1c05000307540402e030144a80fa40c4a241400c01c1c0400b8400c8082010100340c5025030600000d40188501c42c000c0b001446c0000780c00000003c480c41042ca800000b14031200318000028840d01c981e001003c11030910354003801039582d500a90415800305541c014046480306009020b4011002564151481d00b00200c0302da0000341c05610100d02e03481b0300103540301d42d000001807241140812805410840030340092a0192518808161120b8450001007120742030b0695007203070b00030640540360b804612104000044200c0902d0800500c0144202d8000c00d920320740000d107a14003032041c0c0d83e001d04280510b05800b00300c5410400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 726990917 1250 726989667 726989671
    0x30b0906010b030906061908101d0a0b0a0b0105070209010e010303030c080127110412051207120e010c1e030e01050316181703030f010e060d0b071101020a120e150708 73
    0x7c84e01612074000281600b080000781d0b80a00c0c41c110000b222140120300c400301c468451465091035008980d8074000421003505190300a030403840c001004d90003140101c0fa2803042d0000030350f00808200010820071008180a07049a10a4400f00604000f2200c10303280349000f44140120f80e00190040611440106500c0c05450540840014100100e00d1103212540103a000728096040078045103080090800c40400d03d00c1490740000d0603c04155510761268000d40081c000300503850142040c543d0190301d0440d00d07541e11044482400403c444440210903c441d0309900250600c0718000c1b03d07500580c200d82c0a09001080510010340e9801c054580100b401d40e411112030b4100c8000610402e500c1401c0e800d020703498050750341c81c1401074140000301d8040e04920316000149040c0f020640c2d0709805100d1540d807142203071420742e40b140000c1d6000080100c98504a50000550700c0f4071641c80301001196602d000f2040040f20829903616a440d108092414050b20f080404101c9050003400c68036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 726992167 1250 726990917 726990949
    0x801050f131107060e011109060f04051003090b1e18070f03030c03021b0901050f03150406020408190203060106031107080d1b110a0303050a0e07030b0906010b03090606 74
    0x105240204010301c0c011119411510301c0d03186408a008402c2000783e005140000300018002e0010b1051540e0202441c810340110754466140003554002c1d000c0c03c441660300070440207041d10700710f214003c009030103880b000748111124494035000686080050344148090308a803840145a80d96450301c581071254240007000039445800d00c002010003101340d84030090751196481555515040c035020f4940025550014121186822040c0240d140c814981e030445004458140c0c5518041c0046424100c5061541500038012010802440b070f107900288121443e41089030400040740100001c2d0048110000723605400080040050301d00c603400200d64108001203003440e0440b25582c032421a0b002d004056a5035448001b5561540c964030084e100841c000d080c50210100703207500e02c0740c50301c080c2d002c010141030351030000c5503d41d0100d5100c0e40701012840c003107404d095200e040110102404a03010f803510700c03600001140300502d590940740101c42c205c004004070b0700c032641081000275040d2568 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 726993417 1250 726992167 726992179
    0xf060a08011b030606092117270a0612090501060b0304030306090b0111030a0f051c0203040c14030a030c081606020306011e0c0305090d0f12031b0801050f 68
    0x400c80600030701c15610344005111490400c003105510150544585034410424800821400c100b0120303250440300e0051000c1a20956000051501030b0450155a5000c000401c000c5856410346009010b1050614000d03100c08503100307071002c00c00210910300d019440000f035503010780322500c5015420419040b8400c0001164203500d808010806800031142900042d446181c10022003c45206c1d240790280280b81c250031510f040b0905541e240b00341403060b410091445040c0030200c0c85981690040d40606000225200c15000010046d40065900342c0f01d0507400f44000a2201090702e00340d03030090020303001c1c010700c4010740c41c107451078800030b04140c4121004100e03040801101c59005444180706100c01a220b05019000500d10346040e102503c08000c0c4400064905400031200111198186040c503680c03088a00403c5200250220050050312202004810080d0b0240c40d60a51340082c0d604100a00c0107201750341241c851201200d01140a92005200c907080000d04440c14900290178 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 726994667 1250 726993417 726993419
    0x1506120b06090916090f030c0e10051c020406050307030f080a03060e0406090519020306010918020409050d080c070f0303020c010902030f3307030216051507080c070b0f060a 76
    0x49940150f048810303600010078059001d6045070014030f1240a4661500031172000750940d80ea68030540007c3c011020307070a2015000403c0301e005420741001503c5d020300a4201d01c03d8504200c2d01c5204801e201705e01c40c504090300451179040000d107803002ca9810100700e0461042035150f91203142e0044a00c0001c0503190358000c41d0304011203030214000c40c402c0304005810192070408500b000200c035020307109800411901c0b00981d8001a026040d1200381d10001403100104024a040d0040107030001d404c81c0c20000008280b020108025034084520b0f22403000f10790b00d10b1b02001c00b40c0701d82c510003829050b110f800100460f120350302420030200d0385400000c081e102a00002d02e070401e608c902c5469039120004980b00c5410b031101d07441d880000c1c80c205420030403841448044040340180180c040507400f0800020301213200e012000001d801c501a140141c0d0704c0e00e29204115021290381000c20781410100d9010303180c0c2011940c0060b001000e150381c035210036009850301800944030076880458100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 726995917 1250 726994667 726994669
    0xf0309031902062b380109052d0d0302071211130605040f0225050a020a08070501080c090d061d0f060114030a0b0121080a0509041506120b0609 63
    0x500684041130351524114501c8810001c4800e82d440b2078000b442c1080b0a01943c0b40e204140c07281d0a0812102036500b4020300c0701d00c0d0048424003019402160301c405201d0044890702044909094480745040384400c40c090040e00b070184500107070800070b0050784001c0c41041030302d0000800c0d400c040c0c4606028114582200c000400d505002404031041503502c2c40b0030072840c0340c1442039082d440d030300c2102582010300480e014200102d0728013125a00e0041e00700c007102049000e01150740c070b29a006091984250310745682c0c2ea0768008500529010035040e002080d04007520105a47e000100100205400c10f440e5071000040d080455806001d41000100c40c120110140304031030540200703a00601c1d066241c402021024034a40701003a001c0e0300145840c9000c219200034090546104605250440850a1116000030b0401402400403180422150401a03000317000b401c48500c1258140010318801502161b8496144985004200200d081c1d07884240c60b03070803440003000c0040c16103040c811284 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 726997167 1250 726995917 726995947
    0x30b0406060513080d0909090c031703010e0702030403022b1403090301151203051b0a03030b030d11030d0f180803190506060d0b19080706020f030903190206 69
    0x1c0c2190012400200b1a0f44030310840e002c146000b4a03a0000030021007555550240000d08980503800700d86850748648c500303000355a0408001140e000d075001d0044207030b900f8030034081d4200780590101c5082e01000f213000c10b0310000940d002d580d0024100461302d03586410310712030302d036001c9001a17800d21240703040808030b51761003118903046a10002465a0f03403090030406003150740300500c0740d20041ca40c8100340b14180203206685405503160030915034800e02d4414520100d00003810400a07032090400d02c00c100b613070641000816800a80450300424800e031000d81c2c8240c4c01d00140011a40144010b0022954035000030941c052802c0300020010fa01d160400405803500700c09650701d60340001888010102480e044488546110040207241456400140c0c0b5110740340b00300c1c52007030b100c00c00ca0700e040d03071104040036440120000e45c04607283d440315140e440c0c050b94441d040c0940140308e102c1e040d501000c001c40d00c0410008000e02405080030100d00c2c04040e04030b00c166003000c424000d80c2c18100c155 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 726998417 1250 726997167 726997169
    0x507140903211c050c0f0c03040306050a1407030207031e0e030a0605070809070e0103060b0a09020a02100f02090306011e150801081009020f150d1113050d03050712030b0406 76
    0x5092216900d4005405420040103426800b00c03c941c5010108032601c0c0c110416540510505c84115585907803245201e480d6002e150400303884c0074901070a11502d1600345e0b10030185a540840d0401559680c220160100d00402c08068085000d10811419162560780250618001401c0203400d003124103021a01d8820380020865065076100c081c00641358020502076805030001c401040c00c103007040d0251868407410711004040304c0d1280221100c42c0e0350000c040d406409550002c540b600000c5800139074843c40c50204865452529140b21000001402125003911f0302900404440e4030306110400c2002d000f0580440380010010003048081c0c58000f81c2288010315a2560b03103d5041669190408064900c4085100c0c41c000c103000050716581e540c1c44101c1e40843e0401c5480c40ca0642001080c40707102d1501d400d451406840303024143d104000ba001001c00554003400d00e03070f10303041070000e40c40c850200540072a84c10700c05600015006000080741e6003035031402180300400c040105003138403c2 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 726999667 1250 726998417 726998473
    0x70203040801090308100f080d030b0f0d0303091a151c05030a180b18120705090115170628030204060e0105100f080610020304030f0b01030b010602010507140903 71
    0x9180203011005014401d08000392647c4103104a1841c500b2070071941d581001c110400c14503449040d5000139944042441d10f803900060032024141c8500e1900500a01504c074044941e07440c01d0040320901c0200d07600340362103500d0850301010098050000c0011114800425009840000c0580c10009500b8005400d000c00039440303c441802c1c41001c26103070460160407540e0f504106101003c1000708031004525481416a829803a070401e0550b203e080031165041640c100c400600009460b42c4001c00c040e101d624582d41c2c040342d14200300104800a0b1003034400c6640400c0e10b07a000b07000207030149034181d0020300861550728016600c1e4003042c10785016034001084891210010455030501068010209447d1b00e401c001c1480d241c41c0c05080c121002d0b00301405862610382c0410214000c004031409182c200107844160860351034103019100090104541016645000185003401409102e0184110b516580c4150042c505202080d412411003650306106000d85100c044d107070282442007004c6 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 727000917 1250 726999667 726999677
    0x904060306112a03030414030702150a11010b09010501030c11011e110702090c1303061d010c080f040303020f040e04060c020c03120301050613080727060501050d050702030408010903 80
    0x80303183c0044081001c4400400c00c14460301c640307000d00300100460368003d90010518002d82c1100c21719610714001c07030304000e41040211801c04019031802000c0d03c001031207980c66503400c0403994885401c1c0e48c00c000c2c0c0e46402810b40d00c01481650302981040c0340c9440c051a0002000c10100240c9003519419480c154030320340c1000c2440713042941809403440e0580c041c3d10441c070301040f03075003c580d05400040061480e500c0105d80103541214000f080f40066801c24410b00005001d00e400c0451640c406001e005558a4490341c1d2401c203000c0c0d051207204201146140c107483d17489803400e80213035000006100641c0b8040002140401498820500481c010440050451243e0f0400380c41c020000140700c0c40303a03111030000d01d0194000f90480341511070035034040e80c42d000079052030242c0702410b0f00002600d025002c40030500c22084803040e2407880c040b0489008030389444191008643d090300413180011002c001350b07000070807036820140d0400030034411a8034141d910555282141e0001d030381200011 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 727002167 1250 727000917 727000927
    0x307020f0318010e12030304140c030a05010516140a08090309061207030608160b16061803140405090a0c0c05070f0504060905010b09090a090503070317090601030215090406030611 79
    0x56840b00c610084d210041e55100b1401600c0e03500a6901d02000388000d200984048068010f10014060150080c1c4041d080703074050744180c90140d020300307401c1361b4801e0740d5207030840210034162080139045104601c050b44246094640c140441c1c1e0004010500609448200034100543e02e8000041c001890790146914440c00d10380c6008041c0c503034991085a03a540451000c174450b40b034510f541c900725038000c40f42d5561032400d0038007400759854441000d08a0382c42d00045a046102002130307048094802c1d0303039a0ba036003400211001120300a502903590000d070700d8000280c902106034058031540803141840040d00c50b041d511140303440030f2a00003081e4407080620410085c20a13014110280c41c0000d414041581446000c1d8914005da234801413103042803c0100c1c82c41203940d88061080c6800c501a40e690301054100900400345040000c048903200c50002000480c0c0410b189050343c2c0c1c02003100600051100812045d50440c1c2141d42c2e000e5a2003000000251a48c468031468041c90b0f00501e03114 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 727003417 1250 727002167 727002169
    0x114090a0b1b0a030f2703030504030308090706021e0115060216120f06021c02160210110a0303050c04050d0507051206010e010e13140f0d0c15020307020f0318 70
    0x22060140115516407080c08050700103a0000440601307107055141810072400811803400b900544046c251b45881d9907805c001c024185d01c2070040043d6402511050b1517a1542999503a4984040c429080182c110242c82e01000320021039944000e1141030003c0350055a08a9808081d02d19501003409640316842c2c0200c10440e429420b0004c10404a01b0f0f154840c2949075800d1803480134034001d0000354000380340402d001e0550306a100c0c05801040c00c64503046c0034000d0284d80b800b282000e80c840c10580f004517012a2042182c240303601c0306c3c040030304078800e00d5940580103044042c2c0b88d1183d41c0c009000c0412075844112034605111f008000038a007440c5800207004141c070740b0a040c98056000320380144049007210340158111303420498009195600c1411201d10011440802090003507404024004d07001c00240e00c01342c1d60715100030703183c0f80c010030f103800d036010603074050b0040016203084120495030145601450340889940150340b507006200c40c1032401c1d0ba100c81d0700c004500e620f44491800c1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 727004667 1250 727003417 727003447
    0x1e0f1009200c011401030b060109090207030e040f0e0d0915140711060403020402030a1406030c150c0114040813050103021303080a030b091008060901051003020114090a0b 75
    0x14545200d04026110003019a032840001c010024040100d000440600c508403d5115920000c240c000407041175841e450100e03124503050b15204d00180c1c1544001c9800960b5108440040d645a241c1d103100d00005401d22025003038100550301d65998905903190344020510019401850366600c9007070550a00842c0000b6800f840f68010400c4107a58008078010980402c032400650011540b800c0445024000b81440c8900d4000940050002c018041c2c0c00c4030750380244412021114682d031003070f9109024981c0c0c44441b400383c0b95001ca80351643e1403200751610001c019200c2c001001180300755220400729800c00c41518122080c9000140a0700c02d401022001c0c805030509103419485d09590000070005000c040c08007400c0300c240044d214203081c0c000c3e4080101040094400615403811400c503888590311481407400d01d006050002d049100c040c460a4491703000900320410090864004480c020712241d40301103440c0080015808550340e021200c0014400e4444080c0c1d00c100003130100030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 727005917 1250 727004667 727004669
    0xc06050a08150121020705030f030103031106090705010c0218071107060309020d060c02150c0910090b0301210827030f1c031e02130f0f0e1e0f10 64
    0x1140c55080b40501c00142e0780b01c0182201040d001800e80451040c1c800b4004c000d00c80e425006007940300014641e40d44860400286041368040c2c2c440e0701c8a40450080c0c107407103840868511103da0400d560521081d8020701c001480140080c244010200d003011018001030001d4440c080400c4d40c107100e02e03003071650402c01c040c00783c80c003460240001e44042d40804c00180c0340400040596841c0e5082045080c0b0070080e1080c84400a1400c0b4201c0c14015514044c0c7d030303c10a480e80c0a078545203100400f042c029246401240d0b45680c0543ca541e1900d19003200e06140c1c2d881e4402d14001042e860808100c0d50703c050700c5200c1103602e5041282c510803943c1451040100d032410700941203d9500381c03207601d01290320b0300020007048a10b410701c1d088940c21030040c0b9240c41e115090380000720700c81a041c07170b41b540500000080c2402c0c0a507034a440f00110040c01c1160700c07900094203040c14050100282ca06041030300306403003800010f08081ea0030044403d0000444002138001c01c49000c12000c43e8149407414 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 727007167 1250 727005917 727005931
    0x1b1204061d19060f230906010920090301020f0a0302180a1203230a21110403030f05130e0a0605010311070618060903120c0219021c0c06050a08 63
    0x803490b540d61411002805407200068591030341da0140c0c000034461074002240040b4003000348030079490020001500a041501c808441e403040000100705d105d02c500c80d0b03070004052148112001110340c0d00c001304542c001d129294255400380303d91f680079089080544040c803119140035803103a010408040c20381c14400780c90b6114280d18002048645200382c06007031180c1c1c0625190204011050300d4050f2201c90385181ca80c14000050072900190340500c1d81440c8008000d80c801d00c40703035032070006010b07160001c4129550301420001000001d0252902c48200c89482c10098240701c249946040030507003e40c0050708105120040081d80203152265030060607003400c1c1048410042c1302c0c10b1350b881c010140000c10041d5240b12001d0b038014035108500142d03500100c2840048280d1400500c0801c02c4000c0303c003610300f40040c0d4034946001140740b401c1803500c0c40c100e600b00301064082015803a038012035241090307103000b18400840c090a440c040645400d032280c5984045a41004104a10040485d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 727008417 1250 727007167 727007173
    0x19061515030c080f07120b030d0e03071211010807271403011e0c030e060702011506140a0e01030b0d05010c14030c0304020105031e1608010b030702061b1204061d 71
    0x2018070300394130203560000101c1c9015060b0119103800391004004650446616209000d01c5003042ca61144c440205d01409405840d60603503035410000d650f102c04240188000e28060005d06154803030428513034040080e02c0c002d0303864950031011810080c143e440c0039000b0114000c041c071a0200a101d16042c07108194000c1240f00002d1440080e4003460107103001000782c40b1b07420324021910a411110005441005071141410b100e04068020211a03144250130720b18000e002405500400e40c003240d402090751200d2403c00c226030216212000403026905040c0d44980400c03258550b10310501e05140f107034000090b00344125001a100c030340c104603a030325003035000c01c104104280c2d400c0c00c2c0c80c2c0081c1e0a0a15a40741d85135140555204480b00300c400145211803403c0040301e02859001003450300c0035480342c1020b071b620741d00100303202e11048564001517403140010454102c80b880c000d2241a072203601c1d1134204400c0d51041c2400040a0713074280c50242c0c480c1b06451400c9044051a40402110001 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 727009667 1250 727008417 727008421
    0x3090109060302090a0e1302041104240903080c070f05030d0203070f030e06070605061516121809020409110c06040f0c2c0604050919061515030c08 65
    0x20309140c514040e030010142c0116101500c0d4941e51035485c09030205100031125454102031070182441c0d402d006034412418081c10808500b072140c210f030240c40440c50489011300b201c001d1800c205103ca0902ca0420046140c00404103006401415441e4041009040510f203000c025001030111904154030903005000c4840a04d9000403c48060b03560081d8401000e081504003070311b80101c10210207800c1040040d590701000f6039036116a202e07110481d03c40b034180340240401581c5000341c55208240c6203d45480002007500000340d855146664030b011106d038110014802c0000e0313999401001c4050300850148000580fa0080b0785001c0084100740d401c3c406203281096440f14041d10191290902408041c00e1104540440007e041d900501c1e440082060607000442542c990b50104c080800101044103032905004203405090220000c1240b410200b0a44480c2d011080044480039960311141a9030341c0b0345040c0780c0c020a082d1495041c1100c0c5441c02509031811039900104105031101 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 727010917 1250 727009667 727009669
    0x10306050f06160c08160f060e0f0d0f12030204080c030d0f08190606080a0b091018020c010c11060903070308010905070216031b170a060e03070c060c03110309 70
    0x79600c0c2103000106588541d0f9440c1409804460542c000180d58003c3c0d84019040c8040900028112101e1840e2070301519a6920200c4041019442c00c0d58425501034541c04140f500496460401e0b000340d06116560320725598002c3e042c3d20b020018000b00c0c1c0c0224040080c4031082c02201610074098020342011801c1450091682e40c0d04d035403050501601c0804108180404600d10b804040b4149080002c0d684503003015040c2e00003142c038030b03901c40d040c2a034040301410029500340c001c030000e58401e1a131905213107401c5050a102084d030328070f45900341700d0b9000c0c4c01024051144d07074143c2904c8210468140e81059403c2680043c840340d8035074000c222000000b5480341c400381c111004010001460340b103038003040f800d141e42e1500e015885401204003205220740a00c403d08100a0452400a9540c0d200030805044628081c801c1d113541000c02c602c0e01140f0140c02c142c031420800d00590340760a201e5a524800410b45402400010782200d821208242c0c00809880e204810000198203190301c02c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 727012167 1250 727010917 727010929
    0x3c14040807030c0b091614030d2a0f0b010b0703050d0b0f091e0601020c150904021903090605180c0d021201020a0e19150804050723010306050f 63
    0x2800040009000045240501d0721400010421950040e00075420341080080250b4400100220300c00c1042c00c0c9400207444566130100100414010700605011300c0d08040030b03504140030814041202c0e00c1c0900300344660140d10358081505100302d0b00d8030800c10050401901c2098160040c0c000d900040142c10301094000d801d642c51120143c101091440740c90b40800c0d00419100c50f4960002c0c103130000e020000e82075001107200c40e004e80c4c103015810394840004a0703441100940341d64020943c0c0300a0010f84804000038900c42d10050405803506d1400040d404003014685050800265140030b45000c010540c0105030700091179003003d080c0c8a0010050750b85618a8041d184c0c492624800d80d1000c540303038881034840c65441da100842d140e4900e10000b8240b901184007a512861204034100c0b56082d05000d510191844242c889500000044003907a48410281c41510a0b200d4101e001941c0c5000c0717084038040354200c1803a1402c1c070780e21100240070744010340c00c03a0b403041030304140500143e1100d03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 727013417 1250 727012167 727012171
    0x501060801150c1707050c0f13020309070f0305060a06060c02090114130513030e1002070e180313140a1512020415050c0609010506030a030c063c14 65
    0x4103400502e15074800d0320452010400140b0282c842441541d10040c401e000c0c000e41c81c040e03001d40d0145c01c00d180810a1500e8031f0228240e101720031100b01c1003083c80b180e0180d544003012800711a100c94560300c405c03100484680c001c42d01940202c0400c80d496040c1d008240080030a030805610300303000c80e8002403242405001d0242004d1740031f1000f8000b540ea89907182410040108204418104083c0025503c64110310035000324441c960902d0300360403c00741103404401c081d405003619500300905030403070080150100e014040c244030b518002483c144000c01242d0a1541f0042000740790041c1e11641e185050f04440c41429181d408014281c51480e030f001002d90b240c5031103500594401d84510080c01660001014400117900796803d043d0013400500084800710708580c0c0742d44c2d946810500340c0d4030441c4d0307940c0c140d00202000c1d400039005140b1245c05504c60480800d0110001204000d90f2281c50101720008641c1c0410640707514402550141d4050342c1d040c18445070710995440321000d040 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 727014667 1250 727013417 727013429
    0x80306010c060603081801110312060312031f06021b010302030c0d150e0603191101050d0c08010f0602030702150c0307021210150e040308040c260607030501060801 72
    0x20400d0788074200d0800110381c040c1e4200002e1307440381854a460b4118040710101d485c0402000f941641c010301c0314a40c41908040107600e090250300d00d9045060015000c40d40500c074611002280c0d481d22409584544815110011001080c0c0320044400c03125a000500303540001d2a095104d01d80300c80003050824080c05c000d43d9940b2441e4104a6620070b01b801c1560a520b00540b003203843d000d01c92504100c0c0d4001481860b191038a03410552100309056042c0e100b808039400b074038005402d0850040e1280c105040c094202400e0090035030541c0c48030070869000405035001842100c6061400c3c00103082c0c80d10080d03040103401e0b400304440c3c00c1040300300c1c034200e02d002c00c210817049010411500001d0340a8102c520080c20350034080d6a540c0344941c070000043c20302a4030441c50044513010002c48070102480d00841e211900c05680161020307005034ac15550741c0c2c01c0402d0b0100c1440c00c501542c5001010102c01c425151036a509010028000c00101820940100f00302a880120a410b40d54 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 727015917 1250 727014667 727014683
    0x12220201081f05150d050c03010b0301290c0607090e090c0d0510020c030414041b0f1101060803040e10060e31050a1a0319060617011b0c0f 61
    0x4059800d0b0350a5050742d900483d4814400641c2e1855401e050300541013010740307881c080c81951a07c10400c1d620b80801d0040700d00c2d0800900041201c11010010340124150a51546080b1000c40c425400c40350702035208108241c0c8038401b440780c0140e2066415000707221003010440c4505095a03010344440c008036003280f003211154484014080280045002c0350910401156070f0010480d160b0303202d4001e40f0a0555003040e2040101160605002d1401c0d100e460040c00340311059006029100d0003080c038075800400c00c14500c6403000d00001d11440000d00341c0d260045450307914281018481c0c640080c0141c00d504400ca05c200301d85c2d0b81004040510650440f044116008407842e440d41151556006100b800342001240c11251125400346004803041e50082c0b1650030b25103000d43d003840c4004002901a271204049800d000303003115024004c14418600894510341d81d807203840d90076910030b5001c0103695440880307065214051403a01c020384a00e06205401004a4498500601c80d074540031705101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 727017167 1250 727015917 727015951
    0xc041e0e0c040207140d0c030e0607080c070311120309090c220609050406050f0108071809020c010b030c09100312030f0903110d090f05060f0f1222020108 68
    0x304180a0039074003007400340045469154504140641c07480400b0b2110182c0600c5e500322000d14802c00d503001c0080c1d01501c030800307140c00781003d02145a201203029134030381e0014001425150424040384006500680241c10503180e0a030030049109003100306c0f014150b00420a040b92a250780321059840008202900d4032004402c0280c00c12440d09051941680d070001800314009802400301e5041c0c540c142d030100015503e42c1d0074030030102c0c0240702907404500110006017580c0d20a00842c042c50f1f80d105a00e1031240d5555003000141e80202c00303c0303000c13651590103060b000d0400700704040082d130084a02080300d0a0060799070040d100180000341c0100c0c0a096004c984130702a401104440c20702c1441000740486034180108000200034058801d4060100d0959a9030720480c0d40c00d0543d0240040c0641c098600010440f096005401956140206011584688650034040d1440007422042d0001c40c0c5002041c0c8907000b071420204d41800203182004a000d40d1740f0417489a841140c62007028160b03 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 727018417 1250 727017167 727017191
    0xa0201051b070b0412021504060501030b07050f090f0402040503100b15040e0a0e03040f080a03031b020c011115190b040612080a021c090303080c0c0c1c06050412020c041e 75
    0x414178607010400034006280234842084040c0d03001030304a90040300803c04507110000101c489100304442008400c6090142101c207140180d185458520020001440c0079500c00100e4101602601c0c03410307546070359852240c00b07802d00581c0b140340410100803aa20342400d14505c2520802e014010410440c0d0303600d41d45e070303102d0410070448015102e80b51200b14030b03658940710b135a0f81e030415200c118002401c2c0320442c241000440c0c65995180c100f9000ba00d0203280d1200112484610b41c01c82071024810500342c09804000c2154160003242000c80042d80d401b02001030005840240065a028520707064080001c00c401401c030010340d952044e42d4643c1c801d04800304a1515503400c9030341c8510100010081402900464000101ca1107505d840318142d684155200a0b07024400f4209660b40003502d5094a900c0c02d482003504805109008401d507000342d0320f0340c0c011600f04490860341d0540c0d100204190540400c00c001e40a00201d4090108011a0480d0074440148815003101c1549030b134406170701 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 727019667 1250 727018417 727018423
    0xb0a050f04090f020c0f0a0c06180b03130201091a160f020405010602160603050103080306010305070516030518061e0c0307080d1406030609031e0f0a0201051b070b041202 75
    0x14420300b4020311083c0c80c8400b000d8005d6010107141c803400d208200c02900c0c0c02da400f00701d4a44203500000301440f1185005004e0360303c0c0341c05a40f200e28090300d11501098650007240958043c0a42480d404001c2c4207030320024080034011382094007924103028200d2490282501205c1800d41007071414034141805242c0f40f00c100c1e034000c50081d402410000003290980c2d0014055684002c1c0740640b00240360303034503002e40c03c032502804098928102003000440c5ca502075003009802681e1441c0080c0307440060b19000502c0030308100700302c0000d1800207a04007140c1e841300d05040682021250185001007074804051160011030707541414600c007003813104a103001403090314001a00716100c5a03480f00402101401000c5400b80c1c86103162820002c0303840d606002582c10704c540c0d02400114600340c055181d10010003e80c0810402c9680f0070400da1600d001183c01070083c00c0941d130000708107414180403000705641d40f00d9001c01d80c210280030f9080132400454002d0b8015410007001703400c807a860b4900300d003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 727020917 1250 727019667 727019669
    0x4080d0f050f070b0f0114090f040c0f0329010819031b0303060302030f0f0307080d0912020a0507081c030e070f080307050c010f0806010f0e04060b0903070f0b0a050f04 74
    0xc680b0ba0082012030a0220034007106103d0030145800180c2c582c1c98001510360502c1404c00a500041c60100103140300d1843d00620703800c41e028542604807103136100c1083c15914403681080700c143c142001d0982c1e10100854010180000c1e0000d009003960506110369610015524000012948074114030305246c0201c0100c500501c002807556001080c071704014000e800540710490191288421441c80c060001c02e0460320f0700d5005001c0e524102454444440a0304480d080d805400d0380c83c80a407000811450142121249540140c0342c0c0300d47d58104242040c20981c06009113400c038400309400c05140361035041104549080000f0b98026540500b40361013565080030929800110000c1a640400030240800e248220100d44500039a48011900102d03609104400301e66502d000c14260360082c1c0500d080071315981f0780002ca0090b084001015500e044c0c0c05800340c4400001c07000c1d01420306001030b0303000e40a0440222801031031301c542554244642c0340800200310b800720310a2907061888049070 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 727022167 1250 727020917 727020937
    0x120f0114012102160314090102030403140c04021204120801030803240901091e020a21180b070e010509060403060b060729010608101a0c0304090c1404080d0f05 70
    0x54454080000003100601813100c254082a00301203603c021241d0b140440e80140300681c09035082503d1941c0760619103480d0018249140600c030b20091081d101c0e40b0241002504400001c0700600302400c1450003240076087c83c1081010120040c0301103401441100d400c054840c0300c03194102e81140c201c02c0700351525030415a1000300e4400018801003950084421072100d0402c44004c2c0c44100808002c034032583da11680130440061840c4012141d8103100300c0303829000031002c50640c0f40d202c452102c074111100d0441b503083e80c40c4203010015034440300719954034000382081c0d45803690660000702e5a0003103101c000c04554881a9400d16512000c0a54040b50703030200e0746802020182006281e80103c0008030031100c45104000030314240315402450280c0c49940c1241c0c000c82c00c1810002141e06440161000000d081117011180717881040104000d01c010f01d00010401c00c0301000900e1420f0b02c00111054440a000610171980b011500700000c14041c181495a560510810303105405405204 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 727023417 1250 727022167 727022171
    0x10207030b10080a11030115150c020d02091918020102060f0a090807051b0405011809060b060d020301090e010b01022a10050c0d020d0c0f0602130308120f01140121 72
    0x1401040f4401149405c0b00394110024000d05503070707411300360000300b49100d0090040511140811624054424548501d00207070160031000c0c0c0c16000715103130f2141510a0141d54000f484036403034114aa00c1010b000704070b064005081e50040e500001d542c0d20024200d492281c9449000c00d85900890b4005d0399501d82c0021800c0d01d541013801c06603110f41c0c0d8990002000075518001c20034910302481100c1c16140203000b0920301000305040b1000510250004a80035a83e50400c1610f95480c0b0014001c038000001000d66258185000b80d02501e0001c01701600a84c103149500d000ea0703130045401e0318070540703900c01a07080c00c948140342c0036101091845c1c190800c14446010405582c0140146202c0751040c0841ba01001c1c82c4100302e80d07511240e0541800030f91946640000500a0b62201f28100d003e50009810003260a1290020110a602c02c03607120000140c8a4685d0858160b8254010003100f076074911507142c40034800710300700c040d44d542e4100030a1454106003000000344414000300e040c101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 727024667 1250 727023417 727023433
    0x70b0c1504050604030810030b070f02010b0301050114271b1c0c02061303140a0e040609020a02100908040902090613090b010e03010207080d0e030403060905011e0b010207030b1008 79
    0x700d43c40300c9069901750000360302c110001d882d80f0820808a004c581c0d201c5512840703560b61140496407064040b415400310354030342ea41c40c640ba6400f4066a40078200700b0180b00a46042c4008100d4030007095821a20001c1c00d464144e0f00112080d20078660000911a60f40014503004074170500c1c2d8822400d80c400a03086121204a234421203a000750040085a002c5444944603040265002010200020002154280d0320741401038000060b1880c1c10842c05d0607048140301c800050300355041c2c1e400c02c000f9075902017051604690304002075650190010010092204540c030f841c0070720b01c5180181c40d40d0300d0700041c0c501c6807511420b0458001010080303000d0030080e110403680000e400108022070001c0c1031081d031511540341c10b1080360703600c6a201360710511346040d404c5801c0c00b0b011074215600060106000000100b1102d000d07140e44544520000142200f0010f200448441c0400781c1d5200580307030411104280c0d070002041c80c10740750400383e00d070010391f40d60071a00d0710040550402031490050410b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 727025917 1250 727024667 727024673
    0x618120102031003121b08090406170303040309050907020c1009120f110f031c0203130807080601091116020a171b04270524040c1502070b0c1504 64
    0x44400070303248102215217015058485c203d4400d40742d1240818403d080e80e51460000c1e41000062124046c05440400c0f0140d49605048028100d10500220341d04000100000c2640c411621000350000321440103d03814a14030080da80e0050760700b0540240001c40b600b0803014002d08015000304203803619404000158034100300720512260040f5400e41140742881d4480c034124499403200c203c080d0040c90f0402c0540c140d00035420702c5424035801c0d070104110400a00410b60f61840140961800600030103140580c42d5150480582c0b2000320705140102c800307841008501151010302490b0003148400d031003070002403010800c03a8805a0705901e001c030304400d02000484d41d1003244944a02c0c15100340314100601c0300b51900a40421aa000c3e00b440029040c62070072004102c1900510445441c884210000c3e143e1009030440e0001c50543c0030200400c1100c401054009415420180110306d45004406981d89885010702501300e4804184482c1d121020017849562203140e110000090800303003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 727027167 1250 727025917 727025941
    0x6032408150702071d0a0608030310140904120509030115090b130e06060d03030b0d0b1f2405070602030f01051c05030f0f220602011a061812010203 65
    0x1003030307040c018140c800051440ea002003110300c111144020950f81d9003000c214260f90b40c02000f010340842540d5480041032405042000d141300380d80b071683d4155410f003409500310031400c45a000034400c0c85c2103020040000c6003407030b9010f03117614682840e80e140c0c011240028058950000c2d40312580c08018000980030060f42c0003500f500106680215504014540e180144d685040311900f556200d1000f2542c64185515114a40c034000c2c500042c40584840c0080c0c07010703004040a513412502c100500003580116041c03100c40035080440070a0309490f2050520030029080d45139400d241e1880180300341d00740075104407400650b1150b0300315900e00d0080f02001001a080c001d460040c0b040c600e04c0c1d0500d0b41d60185100c90b10360014021828075100503040b50b4280e008a6401c0300f2a9070a00030309694040b00e03000a01480c0d007001d4405c409a003800002421142000d520101c04e0603c401d407111240c44100858000a17000040c140d020308001002c01c480e510036464410076036200008004603c8503030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 727028417 1250 727027167 727027183
    0x30503070f03020304210504090e150f0f01060f0c060501030501060e0c070804150c0f05010f0e030a140313050f0606010e010906050a030b13020a0c0510090c06032408 73
    0x15448111120391403420840403808101d40081c10540e041c52003003501612910b814280e00c6c443d00d0118641600e820190041d1107285c11045d00caa8401d225a8214500c0c210701a64400b011007500400380c45c1c210111505120113104820a010135464401411445042000e5a480d089a410b000a50f9030346409030003041d0074454207010368042c40208924007100b604550280350000803090070582803180c00c07212010b103801504140071500030741c440042ca10350105000d0500035800040c080b0344140322841070328001500c101c120b40003044036002481c0c0042d60702000703c0b2034048981e160740e15840f2610110306d51800291052103809040c03a8206000181c9c00e00c100c000380c1e6480034020440c0300650b03088803607024138800710300c00380041c1071800d100b5480000102001081201c00b0158403440000700d90154004200084079500c00720305000d002c214a140200e5421010003440c1d08a4491090841440c084c800405494141c00022b022070340c1c15881004440c12100c441305030361004441d40e15000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 727029667 1250 727028417 727028431
    0xc0f051e150f0a08011703120a05130609050a021509030a0320032a0a0b1503010b1504170601080705120a051b18070f030c02070e0f0f090303070c02010518030a030503 73
    0x429441b54204500100540d02101282c00e5402d002d07489034207032800600002080c0c0722044070210309220114801d07010361503845000368050101c140c03680c014008040c04a090090340d009041080b8543e036240000c00c08071840e054540720194004041c801300c10014010402030484c030001c80c0c41e4000301c140c0c4140c0300d10005200c4460240e00c00050805480c0c140d0400058414240d0900140c0a9080e007200c4011002c001800000d42a0440700044e682c0c044a0b5607240c00703100e02081c1484084211890f890700700740504003d051961504540b541d4a03441401201d0055030f4000010300402810042c13080d4136a480343c01d651811012422000c000b820840800d44602860505c43d0034040c250259039004509030360b0780156002402105070050140003004200314890b4000000d004000304005500486080c03c2305255810801051241e0801c007030446141c0b900304005100302190000181c654880d82820455100c00050505543c0e054900002d0758040c090700c040c603020540c2c45801144941e207 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 727030917 1250 727029667 727029689
    0x2030924040e010501020f1902091e010905010f1706040318090501140f06031e071110200f0a0e04271202010603020303041a040803070c0f051e150f0a0801 68
    0x41d510350b242c2d13541e02e445060003404052000e41c18004d802d08214ac180d01100783e001c2c540680c442100080001c900c240d000100640d0384600504c120755441141c0c81c000c100c15003071000e0001e1007500c100d40703c00018100800340030881d2010001201810b21b200018880c03070004010303940e0b4407040c40b0302e4940c81412280c8205528070b29031070b203450b020050300e000d65442759000796048941c00245800a901529800a001d003002c03c00c101c038030013000b07a1800c5e400c41400214110b144405500f43c000b05200d8403802e101000d019010020030340d5402d990046881d071500038250442d180c0850018280c9288800000d511554000401015036803464401403107920302c03d1107000485c508900304c0b040e5020007585600100001c01a030070244501c40304540070010201d02d032950301c08800d4950307400171000300c41d40c0404920400100308001004c5d401040266202d980389842990421854020250304610407078a504034040a950b0f10350a076044c4804281040e9601c00c801d08010313048a00910903000c0c125 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 727032167 1250 727030917 727030933
    0x20c0102011112040b04020112060f18290f0a03080912161a1303140f030307050f0c0109020a090b0405060607050604120c02180103060b09060102030924040e01050102 73
    0x2101c04812201020018210f9040d280c48035960b2a05c010b00290041e4100070324030541d1780c0f500c10540b0a5000a08850351682400e034500004030038490152040c180c409440c00040d130803290400100600402c0e50252810440c65022000030b903201413444010350004400c800120400604a0041449050031201008040315010b691551000342d903d102841c42c10510042000440300d005150820060120b00b41c05c01103103c80f64540020305a2041c0e4040750200442030701420140300c001505524840954514030704000c0183c46480b0301030b01d140310709800041002d40c602081d44918800d550007050040304640e100c040d070300644a03201c40c3d81e204d0b5107094046075541ca05441210000c541c0000608550780d01ea0303d40300c3c04016003110260a0014103c110001640c8080000c5000414444103905030b50440c108242140c042d68011400f03581d0040910449a80000a0310640c07078084880d16400410b03241d08010b07055000048080cde0702c078013060100700351501c0010641a1802079084031104 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 727033417 1250 727032167 727032191
    0x90711030310060e0d020f0d08120906010608090613171e03060f04050402130209060d0c080a0c030c09090e1203150f0306100308130e04030903020906150d0c090b0a020c010201 77
    0x44c0071704040294002c94072100303407020741000700c2c0d5850040e02440301141004100c055192900ca42140d484c4043d800070b9005121040d0008016074110000c0c80081c44a4500b81c0c105108091310401302414428511a80c000031001410882c1c1205020000010102c2e0242403004590340041d0340c184c3c031817004c650b5502080c0c201403181c03501c201e8000301020703401e2451040301402903201070407040d040742c01004040620341c40c41c01040321511359076450300410701d003e2120390b00300c4640c048031b03030300b0036051401c40802c00b42d00000e00c00039500d8a56000541480d62034410f4981103900082c1000c030b0202000b000881290003000940c0c00e1710968240c20030841120825450b00000c032810201001d60b40010b00125440e0f0300541142c044211021111507140c6c0206903440400720350440000f10b90580501c21410100d403080d820140a90700141c080d00e003050201a540580c2c070754185010350326203498008034461060301d03005050900c0c29030f80d80e40b28818001d4940000505e00e50156007042504915 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 727034667 1250 727033417 727033429
    0xf041b020f210c0c06210115170606041a0306130c1d0103060e040f110a120305160b0c030109060b19050c0a150f0b0301140105090711030310060e 64
    0x3142c000640021450350042d040040d00d41100902d42414460454640101d0311100020a900032411540301e90403040c441071150b080505030004c00074061694600300303049801100800802c052205c0411311a547c150210342640a581d110b10032140b8400d90780c3c2d0880c034020004502402069130940e090451106004040d07411213442100081c902400500202d00300000c0201140c10501d4042403a90703560b00a11150b16091318180c584071aa05101005c10103000c00070303000c1c110103032044001c0c4e92420b95210155080d955000d02030100000c0c41c0081c103038030142d5100c10258021809045801c00502d803030620741013402948011032424401081c00700c0300909440000c8807581128080c1c42c0d00e09003c07500b030340080202da010703403088070030342c0740040e5000c550414100840040040d0411081200303006a031441201280203901d0540c04c140880b0001c1e1707001741034500540b0480440e86840c0421a52460858001d00040c0004414001c20100001032101118002e03900d030002d001121041001c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 727035917 1250 727034667 727034683
    0x90f0b0a0515030405010e0d0e030f0c010e01050903070801090602070302061f18020c07143607020a05030a0309020103050108060f07080a060503030f0408060c0408100b0f041b020f 79
    0x5800030034982d070024208aa04011584244140d00110740c0100e6498a1450b1a40501a600208006448490507801d04002410720b41e2843c40041120341c0c8400f00103407000281c0c4001504205c40001e407860305482c00c002201c010030200001304808091810004001c0d040300030120014010100801c0c4a011031020300801c0c0b80a26282400c90303850b11840240407105d15100901c85902801000d100c03003c14820300c4020501c00100090515204003000840d003401c06242040171325920f048a21100c41c0c01c081e010648106205440d513403a591816482c00c1c880010050241c48000340381f642c8142d068200410b064800e0300c041c8003e90301c84003103680f00c0341c003160748514044c012400601242d11881d455034000c80f003803a0009803035407201c000c2800c640c84031581e12120b100000d42003001d84010402664485100da5006050070704107640f00c0e8442d007a50255845054441c022403002ea0f1301d40c0709078103100d500104200709007a8440040156000c1c1d2000b0540503014111000040c65000300c2c01c40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 727037167 1250 727035917 727035919
    0x804030e3303060f100927090b10060f0206130825050601050105030c0316091703130801090302030d231306110c074a010801020f1206130501090f0b0a05 67
    0x184a8508014000001c58000c1e101d0780686042c1030000f41da07ea1841c070071070b45003901804002410b45070414420740a140150310000401981080c0c254510744e003ca4001c2c3c11100c0c0b400c5404103070010f410050300d58009d03044804400a0050117003408a10410300b0b01004600c036505951440e030f40d4100644481c00100c0d848881e41d001040000c451040c0d030b0052660b450307168100504446c1e00c0780001101268400c0345040e05900020b8100c00160b0300e541c7d071b00000d0900c80024884000d041d03400035264000c126210701429100c504110512818203d1041284201c0061442c00d24050382c10010101c4a9030050b078005142020b070b000302c0b2128000f00c2e0500c44c0c040c2c00800a0524100c2441070710483c1d840c42c00c8581c41c8040c0201983c81d41e415400c0f0341c0d000f145203004c00a955619071b011500710180d03c10721240c0e104001c0c20044840c43c40c02d032800d080f00301c3c09100035070791158040380b0070703c1800705034088c19031504001103242c0189920061084201035802c002c5a803848040c0f21082100740181 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 727038417 1250 727037167 727037177
    0x10060506030c03040b041a36150903090603280b01080114180405010510120210030b0f03150a0605040203010e0406020a1407030f0f0804030e3303060f10 67
    0x14022a03041c0c4d00c0c46404c90710800c2408030301421143d5410039040c092310007085d41c01425020302c0201980c1c1685020740401c401400310fa00031a015025a661a041d000049070040280083c0d982c2000b80107070b65001e28094140c968a15080d80a03030f443c6240105140f101c4035940807403525000b040c3c400e11800c09410b131540782c0741b0707420140701c0742c494401440782c55840350044d610b590055001c00c803a0307802140309600100c1e140c1401084900c1c0407240741c201240010250b650407015136035442d4500304600311410700003040619100443e040200c032125840d018400e0b59404440e0380002000148602030818081051b1501e81c42004240d00c0b0a01c604410742404801007408521582d00502140d40300e0b08010810b405110314904040d001488142d002c07a41c2c5120340c0d5221a0421913528080d9040d242114052405a07000381c521503444403080c1c000e05500040541707845442841c00c2c100410b06a55502c0d1a02d16801c540056101f19401d500500e40d02d11800140d003030120351142092134684030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 727039667 1250 727038417 727038421
    0x40209070e130e1002041715130b04060923010e0109020102071a091527011205090304050303130f050a0f03060506041b02030a11061302010810031410060506030c03 72
    0x2042c0301928411501a105028011141809400f070f8401070009040001c4404281130404500d642019030580e070101c154440c840401c0001c83c0704960101a0551001c000030981c0c03581e0408070300800d29010000c28201060200109409a0408030155501d540300207024020700c0c0b0066500f60307158039200a0140e4400401800714506070315075014100320007501725042080c0078001565142e42451030041d40400040e1b85043c2d110b050304102d80200080b031002c8400500c0340c0000b05680c1001d5249420783c1d590f1001305078a15828412103000300703030080c02c5a032500b07074041268014040f0341c8190140903040c50000519420101c0b01c80088400450345014200c0c99901c40380d000d8007004106036070082c0c0da16100720fa5100c40c1604120311410650003507846008105000d0000190720030021401d6000d1020403110001000e0480d01c459030a2901041c5170311b0b501c00d04035007030142d50802060310200b5400440d02a40001c0e0501c080c3c0e11845042c400241d88100384030a83c401038846903120102080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 727040917 1250 727039667 727039699
    0xb06043203070b07060b0a12031101270320010b01020f07030c18060518060405130506070f0314010801050708010905150f01021f20090907080c12040b040209070e 71
    0x541308090140102150301c2c41540700050764400c4540203000c014800b007048009055008039114280c1c8072020003085124522201190490244120080d03d040f04041e5481014070400c50840d1710b101030005203052550505ca0720703010300310010015005200300d58140740582c200080542c00c881d0407000301e0b51028182890b6416404600012404094481c3c10018081d100d200700d02c4d400d0549142451440d040c080304200c162580549104034044000728504085a0080342d03c0d03030090164240105122201d5500b500580210704036080c5180c0c1000000500c071006410080c829640b96686401d82e03a254803003c0e003282c0064a4081c04241e4a02a1843e00d040105d40a21898414012104001c10242020f4907070a500c84441d0111030b141c101da4805003130186140c050031148405d9650410f081000404c00c0f0107002070203413041020a01c08900c1584080d0219000f610392a03041a1a91901d414002100700003940c0480c0240d10800c002076000b803241d8460108107074001c01d080301506810f1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 727042167 1250 727040917 727040939
    0x12060103021e0a0807090f050f100e1e091507050f04030303050402060702041505150a0c022e03140711061f0b0408061509040c03150b0604320307 64
    0x3070075000300f80c90101003401c0c10104401002004580c1d40403502950411082050b108003410f8021004100c0d82403262079400c402d10b0500391498200411042d0340c4941c101101141c0d484070f402c4941c1980014402007540200d60803103051450306180907140c4403d4812641481031110010003401c091000b4400a8802d41180d60083d00003085541044080d800103400c5641d428040700c0c0740c40c90414100180c1c1003480c040d241116403040d50381e042c092858400381410680b104003d02c1515084046080102900f000d0b4240c92440200c041001c0d2903100f000e0010001610f0032601515030b0350019401e240316512180685495801a0280351680c0d25490104c441d902c0c0c40d01c01d100c202450104010b400c034800780008104110042116081c00040b0ba00610b190700b002c1401100000e00304008100740b80110400c0f01c1d484000354401c846000704003801001604003441e4032200010b800244c91010f070140c1180c05910b468030400309222103000300c520f40c81201076690182c00c003400c2008060130b04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 727043417 1250 727042167 727042219
    0x102121c09060c0f0905121e1e07090506090105211507090e01090504110d08071e0219030510090c0509012d12020f0102031908061206010302 62
    0x820000300e200308003659440300303031203034201600c00140e1905044c46505074016441001001c0c04d84103240d40c0040701014949508002404041d10511824003041201080001411321900c1040d6040500c1500354410b848090b5881103404550400c40403895618000304494105c41000b0814018040300c00003e12441d11030401c22007060050014881c414540c00703802c0f07842040d4507603c4030034050800c00e40c10030042060304814410380c80c1104000000d182510695111102140c001210301060300d01400544075000300140080c1c41c0616040c9000c00c6050400b070510b100715035141c0198900d0824a85001441c071002d0159400701404044100c1c0e02c7d0f01c211030650081c2840e81c90162075402088254000780e10828607082c1040303408142030036000400c0041d07a600c0c1c0150901a2514924500849015002034402c8031480b84140e2240c1c000c1085407c4000f002d15004000c24400781c0c09007019000300d455074040d02c92680c42d02000f200c003003000c3e4140c0e039005041160079841906410079000103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 727044667 1250 727043417 727043467
    0x303050405031209010b030f031201290f0d050903180402090103020903060405031b0319350603010b060406081f0e0405103e040929010212 61
    0x100020704000e6400100f80d4442c000c0e0000110303104003000c003410f00c4d040c411804123885802c14881c4850030110100c0c1c4504449080100f03441103803200c2d0508059180d0060416010714000800440d94989800a01000005080104496603806044e60b44070301c9810107440c1a45e20041084c01c440c985039024041c0241d06150040c1400580000b0074600320094606070303260f43c00450480d6884140002c800000c00d5908041e5003006051004400001011038104040c00000c1000040325200300f43e809008000c038000e0020b0708445030004c0702c003108050325114000c1d420442c0c00e1a40341099005c0b00d044032141e0391541115030303540b07507a00d1144070b2902d80c1005281050400092102c1c00e07080c1c03580224004c00281a20f0b0201821880031a030040801420341c20201c003802500c1803043c200c20301402e26480074209618000c0603998124440d6411007107040b803920b80d20118003000d84080310820703c044100031201c922004010381e95000d410341030585402e01049521105021248070303400c4085 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 727045917 1250 727044667 727044673
    0x50903150a0f02041e0b0f1204030c021c031e0e040510050d0b010603050a090804030303020702130509030409200f0d15170d030506210f160e1605070303050405 70
    0x70081c01d1600341d0b0320540c17085051003c0748030154030107042002110020002410104d1818034401800700c0d0b14000d582a90001520707640008052601a560301c00343c6c02c0c1e00500d01c0309206920a903a64000007044403d400040c0f029141001400194143c100d6040d56901c81c100102208420000a4000108014008030081000141c5131f1150f140060055100354040300e242d42c10080002c044440042544c1c4400f402c00c1a194042000e8008a03000d803905890f0140e1b444240c1e0000c03400b50420140199119032500041000100d000300292080d959403090900031065140e1300c0c00c3d041540714103041c82c1d80e142046550340340c214440003052001c545c0030f4007082c0001c141c1c1500c1c40b094020b41c00050104008890029501c8091001004160007400d08015500381003011406043c1c0342950b510001c5255410600340d043e0400001c0c0003002020308403241105112008101264980300d4030340500158004038800e0f003000001483c40c40c007150345a0b400d2806584089002d0300001e4800c0d282c42c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 727047167 1250 727045917 727045931
    0x411040e0c04020408061801061503051e07020c010212090a260102160c0e24040605091303020118030e1306080d1805030d1e02011803020c040b01050903150a 69
    0x42c03624000352004025010150126240401030303201034001d8062640e146034503041e424800e1000701ca04850038085103190014842e6940d4400c091841d058003a00b01c0015505003c021640e0344c0000c203041c0d01042a800d07030f6000c0c10b900c024041c1901481c2616940b00d40d00000a002000700111a0079140400d0040303000861401d030025030072070b4807408540749030885138101c0e4024007101c42c40c580c004128100c081c5c0554a442c849140300c0c1c250111941c01c0d050b02104005080c3d40d51508a10041c2800070411314040c24500200f0450003002c0408070055401c2c40d410740c1402c034280e0904240c80b501a16600d511880500c1040a080301c08102e052003103a43d12000f041d0707008200025442540c050329420200402c07240a0515000781d0b5020070b12070340c40402c0c9000d046038004040800119001a60040078560440c1a40584080750103500e039a155a004c2c582071550020b510140000155020001d580c850f02c01110309115201e0403d0301079200030406901c0100354014107620090f2000002000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 727048417 1250 727047167 727047169
    0x408071a040c03020901050108090c0d020a05033a0203070b040f06110307020115050a0b09241e0304020105090607060605030303161107081906141311010201050411040e0c 75
    0x48401d940a454148180e2030510440c00c00c41c441a02400c42400d0900b01840e102484907038851440d5000360064080c00c01050854a4640001d0701422004095034800c4e48070203640ca0f082d606001071032a030003642c4c501100d1048507940304d5041a040d594013451910003942ca03070303045829003c0d108407100e901d03500c0103801180c640d214005101c0c0340702e1260b9a0780d08100500a0135502e4080e041d50900f21181c00030811030b6a1720b00c01c0c108454600c2c90a81d15100242c00280c00060300300000301a11104450500c110388007180207280301d0984d00c2e0003920b844003604001c1c3c01404100c5001340458001c0004180c6440c10b030000e424140d100318808030781c19494078046815a0000d42da0401c4005c0709035105030f10141c00011134030b041c010702c900510440b0319101030150364801aa18071075070000070760000c5c800e108282c0c0010601c83c107460203501c0c05007000b090741036040c1054842610510300300d0800014962060080c0350140750041c0c1500b4424080b80108001006e845005404a01c103510300c03070000d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 727049667 1250 727048417 727048463
    0x1d0301020d0509011a0109120203011e0203061512010302090c1314130e0727060609060305090307020f04050c0d090b0402010207060519140721200303040807 69
    0x5603041d20400803500b800c042d481942076074258200201c4910f02c040200700d013668400201c008880000381440d000740c1300307400401d0041c80c83d4102e54800946140d40890310803100d40046008141c04d48200110342000c0b0750034404c40c00307021100030002d10400c00410152170704c9582560440c1104240f54a085507944003440c81100d2540200c003104141d0a11407001d01d800000d208160110a10601070716010440f07454481c0d1403805102c40b1000440d110340d802c881c40100c1424074020502c810000389417039040282c646081c91044000190901d0001001c2290100a42e40c080758080c00c5050562000c4003000041e0600401c040007128003400b5195040360700380141c84172540103103001c5102d411302d0b000090800c01035410400c18448104500400b03a000a90010544000c0d447c04800d01000404103144900c030711000908100960001099581e201c490040d048004907120407110021040e400384850885526600c407a80007880054042a00d000c0188251b502c41e00f0000c2200400b041c40c2d0103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 727050917 1250 727049667 727049677
    0x24030b090a050103020a0b04030f061a150c010f0c0e0f0411130503120304050303070e1503190b010306050105040e06030a02090405060106030e1b010e0d0209010b0c0106050d03020a031d030102 84
    0x11610b50300100154104500784101070700039110424505811600d828000d804100c00050900d82e84003059005851905c1c9030450710782008005000d01d040300060054103800501c000c0750316510706094030441324558802c02150000d036032910585003070714504010f2890003840b8141d03080b0344c031034844291850310741d4000c0c0b81e0300ca260b81110458130300301000c0c1860070b000c0784460301641c2c404006001c04110b000064942c4482c50340b801d50343c001c143c000411282c80d10182103584400020017480a4907400114220345441c0a4404118401c1d80c640110261001841682d001c01c0f010442880800f0241c140c0d50b030b0181d070181c00c44094021039408a01d2303903401220151540e1f000b000060040542c140039803501001c40c03a006101d4050801a00708408503030402c0d09052260702c8030800311030b86403e213884104176001030045820f983c0d079203803400302d65000c08421041d41d4a8400b01254030f180c03d60450791580d81590081c503240405a0f003e4a40c100c10754040b0022590002030b02010b65400d000820b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 727052167 1250 727050917 727050931
    0x150f02040b0703110a0305070f0503070803280b010f0c240c09080606062b1a0a0b0301080307061d070602010c030b0f0f01030c0c060e1b03060124030b09 67
    0x2603030b11801c07801c00400c0c1c0003009054680b03035001890f201010981c07040036600b4640d000081c0419251152500928522482600820b02c19001c4100140b891640e524011401d466420034024216014103020840300c188070084e0100300c60240c82c060a5200b0a02c4000d00342c482e58802500c2250310a40080913a800c40d045200e107600c48000c0000c0382d0f40601000020009540204294100400000d80c140100014220540722840c041032002184098001c0586403011080000070b60742840b0b142009000c903c21406211a024002202c041c0402280e04a80d002e02c084c508001c0950b41d044d01a156000c00101d0b20030b0104104d845003401444072000400940e000044c1c183c80c0780c3d00250646030700c0900c45103d110f10030010285030300c85003001801c45409103030014983d10ba03550152402608542c1c0039002c0c44c03a111100c8001c040000d05074031000d0305039048507500c00e446130806641d21400d01845091031b40d11000c4100f20341450081e00300106d0507080215941008401040b0624800c440d90 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 727053417 1250 727052167 727052189
    0x210021b120307090e01060906050d060e0403080f070918020a1e050d051315090213090c051c120809030702100225060c030c060204050402031e0a0c0c150f0204 70
    0x2016080c4d0b0000507000042180c420a071020390300d80040640005410711522080c00b074000780010b010400c0740e104201810180032101c10906103820020b14010b0b04461080d00701100401042810340990b130340c102106c46407480c54040c10705d0300e0f0303000019402c80c3c2c01d000140081200d03500b000059103500d00c8004003e60761460b448242084190007a540054409400340500085407400b1500215203806065100940401c01c40880d10100f000360b866851200000b901e0100203400b0015601c5c40d440481d04202d81c0700244502000101c40900b1003284010300301c020b1890716900e018022400f555001e9051001d46e400c2c044250040340400d01c902c405d007001a0068860038021101060000b4039035410394078490107060038900050800340e00c0f1440602844841443c034010024641c0460f405807502820070341d1641800001d050003101101c41a450405000001480318a81c601c50380c20800480e81e101003030380c04d250311100180304140c80d01d0740c003039900c40141c161018124001000144102d007a0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 727054667 1250 727053417 727053421
    0x2030304080f1009110121060906060e0306070915020a232e0e030714210c06130807230d18090b0d0b01080607030e0c010210021b1203 59
    0x301c608101050750001011444e0880200104942d0310302d03030105841c2030801030200680405400e0240e0109140c4210042c100b2a000c10b81c40c4440d0481c50031103856031610907199000004240d10340000b261aa03001030746000b07081205162600b440322081130305006507403620ae069105e020000c6040d460000c401c0c2c11031861842000c0f0100f02e070070032401100450700c001030b001c2c02c1c0c24002c0b14402e0200b01001910380b0440e0091700814400c0350740c032950042e07807128001d0110301c186440303540071b840042c10400b0300c52080c2050541b44007266614620352000c0c04503544c98046100407001d4072102524803140500444000851a06141d6503d0740c090441d0b076144a00300c000245007201d80d0950700f0401c107482d100d00401d6001842e68105031401640701191000300c8202090100c901200d014004100d08000000d040d9004a840f50003203070310703580503c400b01604104559544d042c0c0810750060b441140c10030b903849072541c0075001c6442d400e18aa48030005d464549490070658401d103009003030001003 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 727055917 1250 727054667 727054693
    0x715050109051008010b22151d07090605040612090b0a06080c040908040317070b04111309020303070209190606030506191a16210e061c020d090203030408 68
    0x3c070b071000700001002440605514000b040c40f0101c140b40549aa04524030410120100754200c01c01f81c000100f04c00c0c1071196102905a20000c030580c22400510604c408660b030740c3e1064224000341c03a05601c4583c40c05160901c201c4000420181c80b000040e40c680c105800036010100450191a185201203001c5003040d0041d030034039100c024014410f0b803810340e8590000342131006403001c40c0c1d0081e490901c840791400c4a03c2051041001c011f1007003180c0d50410042110b008158051a0740030355071041d40c2c58610a110003214440040079501d07a03c280320034001403030b003288a00d1740181c120200c1d0503210303140c000e441d054404a80011010a40762002c10945003000217600c1800d19200c800049182d15140c4104010020340d0310409000e40006101e51805078441400350784036a001380130f111400701d0070748040101c041c81c202e14000a000040d00402c50f00c0c218042d9204981c44458104031400621541c40c02075100c0b80214940980f501c1c071000240c0d5050015000800310a8050024910099 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 727057167 1250 727055917 727055941
    0xa020f0105062202030615070b0f0c130b0d110a0306050306061804080a1418090603071503020a1b050c011101020a0c080a0e030105090d200a020105071505010905 71
    0x1d107180d000b0a5990070781030341484103d1410008225803280143c4d00c1d10340d03401090b0301d010310102c440d0088400060440c100846860b580d44140c003a801d42c02d4a545030900321900342e00c40d0b20540d1300265207006080c02130703507044030040100803202c04c0f0028008240400d5810b45400402c505800b2036544e4608010b00e0071300340156940700c1030403541420740c0c4840e9012030590100140001c0d10114002c11903200c00c90145074400c081036444040c10b922040e60740e0314010755482d1041590301a0502d4000b09565080018a00381600d228121520700030107003040132802500041d00791010091018503101014200c1c04020903100d005a000c1c02d10011000009000c001032210302280c02d0703104200030b25555500117000343c092a84081d0080e61140d20a500300c6203050400d864a40c59442c040c140600c0c414001a100c1c88a0642d8441000e420070040c00030450000c00310b01c80c00940c002000d0000150303c22001040c0c407510568600d80c45500b00041c01d8210b5170241c20016001d5690b80034003004085003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 727058417 1250 727057167 727057171
    0x90c0103050c1905040f0f180207020d060506190305071e060503011401050c011b080907060813052a01120204080d08090f030d020918010602071203140a020f0105 71
    0x2030a0501480c10840030041e0244509030040318a030390981220b00d00f00d0320900849000704008820680c86985910b000c0800b0081071290901850515070304650014141c02603c2c50f10350002d080c00c60300c0700a51208800740100400d00d503485540b02c142c4c0fa43d81e00c01c2c06003846c0a980164001e01d0001e0410b1580340901404a1060783e155424900c1081410b901004890550301138203098442e40c1c1850005070340c10300482084440c103500b40100034401301c040b50011b5011030850341e83e0040d65101e5031903982d11051a402194001407100700064045841080c040765841d01c00d5003141e514030000d100b0607034401402c8100341100700300741c5680c800540c0d004d03d0f18a10150106401c510b8145403031010740e5144050358000701805100d10000b0720301c00c8180040d5518112a00540b60351710b1042c001c0b5002544514102c511170784a90a030380700d40c103000d0b00401d0f068450b641c00520f42641401140d003089074480004034100413200518403a900311400140c100c0c01c1c500e400074409030000710380b154252000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 727059667 1250 727058417 727058419
    0x30316090302060301140418201f050309031603020a0c1505030133260603070501052809050103050a14010b0c0f1509190305030609060d020a030308090c 67
    0x208240c2440540c0d640c1048030304491a080f1041200407807040410007503c8900601c5d886c5151042d007600600c05154840056624942141c4801c9803400d004c010000000b0320300e0302c080c43c01c440d500c0c1d03805030b0043d0001c603000b50965040b68142040c4050b4812681c3c0c42c400224010b80008100d442041410718050000d0002c80c0c00080d0f441c500c8440007801e1b40814030529000707020b0740c0c540d81c070f002c10700ea0094600d10440204407a16000c0050010b803142e141c1d10b000b650b01101c4592501791302030003403026a000d400b0007809080341c24a0131004640607040811261f512b61849400c0242c3c1a008100c0c820820b5400d03140c29400500c1e0a0026046070320080c0010718060400e051411121405c0c11010f064566019000d500c030790f138040c1c0d0700346030503040044010703d4403940b410310a46002e20340c2045c0c40790b005001251188021140100c61408a620008010880030310201e1182d01e000320940740d112902070324030302600c0010b80018510110980c0282d011a08840c00c2c04000300c42440500001c0c04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 727060917 1250 727059667 727059677
    0x60605030f0105060d0f020d0c030308060f030a0b010b0a050d05040b0103060f0c1421190b030a0b0a090206120a0b0a09060501120504140f011e0c0e04090311010905030316 75
    0x140130700205d42070742905c0c03800503d5003038200b0b880b8045542e01015012400d40024004200030303202e02d0050b02c0b030300c41500d1151048801040141451a0002d500c6034503070340c01a54005d091346403c0060030309401c80040d003002c1c82400e100131030780c040c068411a40314500840c80f100311035155041c00740844032045444130072a400c085020402c2c0307070000350314040501c2c00803c09560b0941099000c540000f10405648a03442c3d620034440b00a012246244128925038420440075a00104043c0d8070482000000d11401c00c520006150f102c09034000b2096600150081d85458084044801407a5084800400c0d00c2c0d60b80c1102059404c0103421007010300b0750070108100003800e0400182030b941000c1c68080d6440d4648001500708200d80e426080c0410114007110f100d4198400d071744e40070305500c00c014030483d03110060900d10f029140c0900403404e003040d1100131805400e070082c440900002d02054003804522030124490020034454403d00c1405180550f440381800c420a0034010000b4110b001000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 727062167 1250 727060917 727060921
    0xa03020c09010608061f03020904060e0405151b0c0309060403150e03090102100203220c06110607140a0c02091f09020301031208070219031706010201110405040f090f060605030f0105 80
    0x1480b0343e8030030030781904884021b9a4460010800705c0180c4641850190010b0401070001021010480321038099842001502e5031204000703107070101a003044505080003c4d40c8244803030110140d0b0700404100e03601c074041d280742440b094041360789075200380d00483d2a00145150703952841c0440c03141c140c080e01c0c82800f56152101000c0001d50f0382d121000030599a56001012800c4805100d0800d5014060f4001d01805c1003500c2c14000f003d442a031140307002049a64000b400741324408a031071445a016a107481400c45040d40e82c08905800c48018502401a0110750401580d540c0c8002481240c031128243d1380044007100f249090a5558018101d060050005000083e120020502040120b10700080c80d661800f004030701e48078403140000c2041d8007081c20301d0141030b031081800400070f2840b140c900c201d03240c1030012422a0342e0100c0642040c082404180601c1c501a0400718241300c942c04046140601c648501039a03803188001103842035940c000030000c030309060081c00c0201c45940001c000c94 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 727063417 1250 727062167 727062169
    0x915180e0606062a0c0102061f2114010515030f0705151201260604050a080d0608030408010212010e040305070204050a090b04050c0a080307320a03020c0901060806 72
    0x10304000d8002485040080380c000b541403000c01c0c90700c03800881c02c14106000902d0540131074540c60030303403c04e0303005000d407200040d0004914180710100011031006451390303520702200c609a13407110658110b03502e0b4484080d00302241d07140034003200706801d00000040078100004004c0a000015480c28041d4015007890307c4140070100d501400c4402c00e84160015940c0c0d50716a80d02846036110190600045074008030b9071001c1da540f4040e0713103680440419140c0c803186a0280c0d56580031140101a5800110340c2d500190b0160701408410b00c0300710021542c84d0f182d41d540c608681040e0003960491394046901c00040420b52245401821810f4580d03a41c0c1c00d06032802041c9200d5814040c0c0199184d2020841c982d0103940304c010800d4008031460740742e05003841c142c0d84802a40910911404e000c41011495180c040704881d99903904c001146c0100000480105094541020780c218402d44008040c039580801d0280d039140340d1295026081480342d44080004050301a007040b802c001640c0b040000e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 727064667 1250 727063417 727063423
    0x60b030a020702030c060408010f0b1815011b0b06041406011409010c0b0a1506050a0c030e0a051f0f09051005090f28080c060a0807090915180e 63
    0x1a003000341e951855400403a01c0c00b041e10000b01e07008040054005030081c010340c0320000f041240181800018121801c0280c100744003d40c2841600e4810041020030501c40984045100c041c10018540c040d0302c00a2903011700544800e41e03002b0420010031403640751510425511541c0099040301a05200000800078100f02c0c1810310000d170000703540419a0b024403005021980d002c08081d000c2e10b442d41c903c402404200303180360b12114010b1000b041241c0150150f6004c0c2515030b8803c9200d99a64404860f80c1255005847d00321703184c41c01c045456240c0e2030706c001c0450340c144c1e842c4030401a0a9002021403600b1301e603c0c2e0800c02c1442080c00f05a8516242a06806261405a464003080800110a0080e40c10840e42c040691021945240d6203050800d25003c0101c071100c88099983d18519154100c1000c0703182e0250003045240700c100d000303c0d54107400400d145840c1903c15103039a604001c42d10210041004242d21190400020b03c20b010750000f544c1c1d0003d0300703000c04c11942641e180c1d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 727065917 1250 727064667 727064671
    0x117070f02012702060c010e10020a0e240702060f2802010506150d0e06101e240207080f030414061c021c0f0615091401030b0d0f030e010e04060b03 65
    0xc0304004c0000d001c00105400d40000407843d02d900141c503909c0c1340410040b0b000b540a4540140441c811b035404000616287c00007505810441c0c101c004801d5030b00c500415564811031040f42e1140060241c8000310103940c02a0260740205100710044c08800c0194001d02140001400308680c140b10810026444c1d00416880b82812001c860b134139060080600d1000d0030040317541d179440d8407503207040144619801c450b190864281803c0d92600301223203101000d0354102401003106004500303121001c5c491026200303d01400540c415500410b485a60580c113001102d26601e0740f070b44c404101406280f03400300c03034540721401c03c0301e00ca80703030105a1550002160b00e401008a4080d0b01099031502111242d46031820f8640302102080140300c4c1340d0207003004221078002d65204d80150314410b100706004441d080300740c3d000c140456a5466003100110060440254242c3d001100020b05400140f4130143c0402e0852084d100c1d40004a0380000043c6208075400c1034510840c1825010444105440100c039 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 727067167 1250 727065917 727065919
    0x60509011401081609180f0b010509090115150c0b010902091c0b04060b03160e0411030106030302030d0203060121020705061b1b0a0807142a0f0117070f02012702 71
    0x4510040e4200e802d02c450342c502c602c040d12440310007c90104100c900c1d14402c1c140c401c110342c1c0c0000b98596800301802c03070706072540c040000c5004200030700010003e52940008802d503882d01542e416180d58510241c80820303072068690503000f14015001c3c1c0342a44414010020307000d11652814143c1e201d050300d240001c0c0001c1d10240d51813100b03d03000c1e00c00303001011901c2039174208411650340d50040032440c01c0080f9800d60784410100d020720b03494035040c0500343c01c036a0554000c41c03c280c00c80000034000e51001d0012070500403118080c03034801211800300d44034140e021a0042e00c4402900b401c0c0c0c2032000061201e1029008880028000c90a08082c0d0f0208400b2101d8204030010580c0e2480c540061440d000d42000c00110b241002c2000c6140d041500400000c1a41c4044500038200780c0503041000e0707140c03440031340b040c000341e02420295800340c0b039481e052500a80110b0a0080c04000f460b013901d507500025103142500540540901644c0780c02c80c2c181d00c80c0407031010fa6000b210340e8840401002 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 727068417 1250 727067167 727067171
    0x60c05043012050a2a020f0f03011109030601051c03050a1206030c0302091f090b030705090a052a0307140d1b0201060b030c0406030b15121506030708060f0607060509011401081609 79
    0x4a039040e11002446400c808c0003400070002e841010074110640d811000c0c82c41d02c2845000300100740340c1441d00340c48814410382900c44812400e65501522036820280b0818100140021411103420305802950000e5000e108105a0513041d0b006100200c84001c05600b80c086403000e00048900050303d00c08110b86100000003035000520300081e05001055202a500280140a100c420701150740880d0050002c060720000350508806608031034518001100c04201007400000c25a5000e24031035078510b10701038076003858800d00020400464120320300b51990102c902c900c48248a0b02440b4290103441906160360840c5820821081e851003140200001c242e12068000c8090301c0d0461040d00b0482d041d20340c15100d0a0154a85030341c01d0f002c488080d0318011058800c1d41e07a0404a00302c901800fa03695420001e40d803010b00b0310407681c035034114954200004201c40404620395204250244403042c2c0041143d0b2000680311501141c1a0000c01454110107204103030f55030060501c00445d0841140 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 727069667 1250 727068417 727068439
    0x31e030f1e190f0504150606080705030c07030c141b0d17090114030f0a061406030a11130b120106030c080a0531060c05043012050a2a02 60
    0x21034041c2c25141407111003d0700300400c1c001084003040100c104000e207842c003006101d903110780495036200300395419000f081c4100007086400c000c1000400c0076502030308002a0200641d40c400f5000d50081814901c16000142481d6a00440e034041c0401c25000701ca00d036036400019298194204000f0040c03516070540005d61441d00d9009005610940303100b441c2c0c054491500e614440c45412040355003010350b500d4003502040101c0608842260308a00bd001c06045544081c103040081c4144810b4840e501c00502110404010300407030b41010300f9185242503114485034850115140068100d9014035080880081045d0350207040130354040080c640c04a00e50721900c0190103900a46007007101d20540c0c08403100081508030051013641403107040c003002079041c4d00314200c505014070700541400a101081602d0142141541076111480f0400c9a14400680d50342e02c83d010300ca0522400c021071004a80c00d40d80c10340080c85c6040c2c080301505c05180080b000c0c481c0b02c05c83c8404000c024070500301c01b55 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 727070917 1250 727069667 727069711
    0x6053c1806040309030302070b0720030c1507030e030f06040308100909030306050f1203090111030906030a1b020106030c090e01020d0c030614030106121103031e030f1e 74
    0x1954a180004110507101d803420a810001c0840049020a801501c1000c0c400980c401000c411075a415821070030019414880f2114507140c40740f00700c0348a5151244c24052407095581560800303104404100c820b503103a4031840c004d01040101c1e04524400c0d041900c0aa07483c0c0400320f1503940c030aa042c50190101e40c1c1d00d08026043d1980c13904842e010303924020301c1d10301b01600b607401002990021129030b00e000880d2010840350303035510340d0050010b42060000c0c05542d4000c4030700340184054401941e040125040c0030801a400c01c807201c507081911443c045103020000200c070510240148001d12485045494040d036002941c0304244003e60743e1420b24450300d40079815144491440700c0f0512001400e00e00040103002240a00001c4c0003545000c030445140511540c8121400340b50140c404048584400c040c1c0e07407101c01c05a416000c01c0003811216940240e4500c0d031407222005864403400e00e032594900c0010b0042071540ea01d1400c5108952008400b460a9804032000392400340d40d4003114 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 727072167 1250 727070917 727070941
    0x1030207140f0109140313030209060a0e190b12030a08070c0506041101030c030b0904060b0d0f140c0904053406090302030d08060d060f1806053c 64
    0x12903076040601416810100c0c2c541c064101c0030590740521007107985804801c494030303101e01c9000000500040380d0300080006051901e0b409610000050801d0a21176403410306503501c0034121814006520304802c010703c41d25640c800c24441c8001556040f1000001c00c2d070465491041018200902c00384200048006100d01324019045900c1400d03502181441d142c040ba11031468050140400d00309640b2000c80c2e40300344030f00030b18041c004240c024192a1a00d0307120041c81c25481081c0c00083392014080415112010000e246201e03036000b820884803c0452420416005440742c4111100c0d0148000703d00c000070042030003c00000c0c46416001402e880645080c0000382c0c40f8003089040000203032045d0445e400d40c0813240280c0550310940780044d0100e50381c0700110f070555403121401d2281000f141d4140d000b89810305145100140c034038040345021510341e100682c1100c0792a00c030410005009200c54249407a89850000460100c00803100d540a003040719124401200541c00003501c103000d00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 727073417 1250 727072167 727072193
    0x10e0706020d27030807060506030601171203180a0503040618030209010302061b0708010c120204030317071205010e0411040603151a100507020a080d0e150c01150911031501030207 79
    0x4800c0007603486d20b0500c0c04501400085076821b1003805040c000251090802e082d440a00b280350014104800d800d105050b4207070009810f05004031801142e100500340b040050400440c01000110744440ca0070130010a488107000107058030180010080006803255101c0a065030b03811038005840340900d04400c0141c0542e0050800d540c42240c800241e2001c066115100000c116910300c0e01d441c580d5141542079125501c401000100601100d1400d8500080e007950010250f14014916024107650001502c3c000e0f0000c145100b4400c0030300040040700c546c00f4120700782c103460500c001855510790300410320f0f8007081100f40d10703225101c070540c6624400c40c00a0340032001704142d4041d007034210018001d40010908038040d100412012841002c00075100c071000950351b440350151034851092000390300c111810402d000c4014403142405805c01c0c0a858400608011811001c0707151003c95410385080070010b00c0d40c50300401c14841080030701c0441c00389600e001c5c03c0240e40c078001442d00500d00000 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 727074667 1250 727073417 727073423
    0x3020907051e0d0e060f040204090203332401050f0c07080a060509190813181b140702060c0a02090405010e2107060c0917010e0706020d2703 62
    0x88102c00003441c56024054500000d0208007000000a05560700c1e98804041e580031514401c0366000400514007901303c42119480603065541800d502050083e00c0009031498061000c07014031420b52404001e480c4903401584110aa03a5241803e60071400342682004044e04011000511000b081741c01002c0350807a0045070b04a44607aa9207040082d11604000c00072143c060400300410742070031001440002c8a899840840041c0d2a11b0ba943c0e000b44d071080010850104e0718a00015000341c00040d000c1600004030404101c68081040f4a454089100305510034480c2c5004809007941071407065600c150303410346040d0340d41c0e14901c000310b140580001c002948032120000f000b04008042d04410790980010342110103080040000c0d80608650444d000404081440752001044980c5c1001c0341480d010700700005c00d180c0b035880500964480c1030800305940e465007041990248208200700052007948041e06201c0780c24100100100b00381c010b1042070283c03441d07107044103190200e108001158 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 727075917 1250 727074667 727074697
    0x80a0f14090d060522321009030e090106110607050a09120c09150f08010b0d020904060605100207062a0f14100f1b020d03090f12030603050d02010603020a0302090705 73
    0x11680b03000100300d81b12141c82040241641607407051000c007070301d0103550141014080c1100401802540d002083c1951094040100680c65000e5585030440c0c650301a01c469581e039a40c034101f0382240b5203040406060344ac10004100440340c011507100450009a90181d0798000d0170b00c980d410850b14154040e00854551490085121103100c010541c04084540f100340c840f001c141e440c0052402c95440f0394040b600050f08100010045c5400c402d0b42d58420b00c20380300014299140d0340810100070310140f1400160b0f03c072a00600c0307400d40088c0040c1d40c42c0000d4151840060540170011011801e10500901145551801100308060340c00d0855041d0500000c4a014000c1040020b001d08088c41c5a080c00d0b501c0e100c4014254055400c1086651102c0d4006002c0c1b1322278050214004c0030484c13003c0e240c0c00c00f041e5030200061040035500e81c001882d554003041503820341c21f042c0d003440544d128940c2560300d46913042005840745441102142e80403030742554103a50760f8009880b6840b0f11003c0c4202c41c0c4c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 727077167 1250 727075917 727075981
    0x70e0a03060c0806010f030c091202190e0a1a10050a020307060c0906120e0703080306150c010b040509060702190c050301020d0603060f021305090403030207080a0f14090d0605 77
    0x155100c0f0354280300308026a03e2640c41c2d030300c00c6425821100250b9074040043c1c010041840211135810b111411240701512074407100f5a100e021480311a803030b40100300d07001004414080290700600466404c1e461441d40c10051615000008007a45400d9040e881800000301e5500034860082c02a20342da81d4104109001070b4009200040541d0a240107100100d0021035401440c07020074403c203802001c00000414280c0e08603154800560001010f565000660034240c1e41042d42581c0034142406040c0004250741803a03104000545200910a40a943c03211041100456000072080a14210400003100a0000f070800c0204034005821180e090b40c00020201c40c2240c01c2d5010340b08990040c0c500b081602000d1034031600381c1c460142c08490303016503083c05010a00e8165103181c2c00c940310303050052030265035540d07207078041d0800c42d10400400e248000d4040040d400c5803110b0b404101e05550305203011603001c0001c9055080c001c000e4030302e035500c00006032441d60350421140007240c2d81183c0003180c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 727078417 1250 727077167 727077191
    0x90a090803101805010825050303040801020403021e0d030807050d0c080603100c050f300a06051c03110a02090c0a030b04020415110c0910140f0108070e0a0306 70
    0x1188103103e09071140d800c54455404404840c400d6506a4044102601d410400c1c9006491503072500e0103480585001602d000955a400b00020b10003002c05800144c4c0f51403450041119280115080c105891803a640c043e11507034840e508620309a034141483c10b0305844d0843d08440c103000c2d0b4800e103000c1502e4038107280d44841d08115058418801101100c00304903d07081138105031151311800402283c01800740c0700c04128024060042e1201041c2d0b915410791041131a120601d2581003d1903580c030312802845080300c0d40e4054603011300010341c1c10900c007105540d9810a4076070700310000b60403c00013281e600d034403079028800900540e800400e110b005041005585507550b0088801402080c03814101802c182440c0c001d5800b00d170382c1e10710180000e010f40c2c0015152440314414004d01030040e440e62000703da48c2c00360314074002e43d402180294220304000c8100c00e249959100359100d21074684005c40c450380d001070302c035030300414a16100410900c00404981c40d0103d50700024421810a0150081 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 727079667 1250 727078417 727078441
    0x60516020d14010c0c1101120f0212040c0e01150c32070f0b030703091401020f07030905010c110402161410060b04081c140d0b10031802090a090803 65
    0xc42c008500c020004a02040001c2c1da40f9910b4200040c66100c0710401d070340441d07000782401c450119248a01042e2114000206400c0307a11102190b2407240104003031201380214002008060308103260740341069414940c074021350400d090b0740001000900c40d001c0081080992480101c01b60404200f00c0b0b10f07006920b80382e0988039000c0251700c94416414001620003d032030940c0c0803100c00c2d020140c40c584600c04101c005e071500d0b202c01d0710400d001801d01c03040030030244010f0a410f4480d1520540b54201d9140c0180300e9500c5d5032081c0e0400c5000b122050100354000458400100b00b207a0040c0d5070444005580541c040002001d004075086030b02c1a03484000104101d546501060307401c100d8140c40d0100161b060003680244200740c0e1100440400c080840d6414031071401c614104240750900070682003019500c01c1e1009103800ba01c689410741a41044907800c2400390a42c14184046000312800300d500219200300607205044480c0801d200000c560f000e0446140c202030220313607900d0050f100b0f0700 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 727080917 1250 727079667 727079693
    0x20d0f050708160c110117130201020d030b03100b0109180905061303020a0305130506031602070b0c0a03121d03120c1c0b010e19050301110a0801060516020d 69
    0x301180d00074001900a0403070910b510940b042944454513070350010f865203100030a40c00c0d0481d040c0000e0064294a00000c25400d034490050301d241000b480c0d100344002801d140b0200724032018142000d4080c0e05581e004075542032400504440000d04981d150700480c1d4104260380701080800d5214a04040640250010b0529900540480d040b584a0807140e95450021030401350058005d00501c4c030020744107800074184088801c03285503c1070703180d5001500300c0d807043e200f04d550090292a0b12520b0340c0c060080300014030304190a103042c604042ca00031b0f01c40d0300c02c0c4002420007440c034001c042c2c0407000d0307441069008070061116040048078141e0319035076803150071007076405029000011101c002c550101c444440758520840d92401140085c00094000c103900e039418040c0076076a03076240d5140c48074040101840c00701603190003490b10f001e042c02c4943c0c2c5140d0641c0100f04000103551305030021031302d604407103451400660f500c08a00001c1540080c0380c0d0029480503c2d03c40003030034000c100701d45076 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 727082167 1250 727080917 727080931
    0x81b0a050c03011b0e04290a0e151207080303010e1608010303020d0507080409020a0f140a0e0907020c120d031413030503130614010e070503160e010210050906041a040b0118020d0f05 80
    0x48823058982990f601040c804659581c40c10105050750a8a418036154840505104d41c0440c7d6100d91600c04890464001740c0010003903820034410014070700100c8901c0c1e6081c03c410308000041c0d50560718025107402c00580644c0034080001002010000448200c031b0040000000031034844481420003408420000040c0e80054050103180707092040000403601041e4050702c4945c1a0a2040107000c060503008001c0420360150700700640c929203030010b1007007250907480d018120484d608840a011a0b803c3c00641e48510181403c0110325440020b1040c1c0300c98142c2840f503102c0da55001d000204007a1760750002d00040c1440004e401171042200e407181a201e40045000c0d85540d42441103d580c0422240452400800c507005100c030b0340035810180000d101031040d11581c4090315100d1080d1842031b0b4541c04503501041c03c10081c4900c040c000f624801d460700311400d1034240b030303124081c804006010b034508010b13108101070308101c2c00f035040b1200d84078903c1c0c0030b00120011045410052004881c02 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 727083417 1250 727082167 727082179
    0x3060c0304051c0801050d060207060216050106080f100e0c0613030303060b07030f031517030d0f0902091506070b150405060a05030d0309081b0a050c03011b0e0429 72
    0x2002d403c0060151441d030880842e0748400c0240e02e0642040303900c10040c0810758405070b081128401052150008142c00b1035680d01c600d070b0840080c5840340c2100d07035a61280d41d180e00244107000c40c51102044c80c0039103855034040480c12a00006403242410629040d49601400009110181e04692200c1c41e0850f03021741c81c00c019040da11a11034045125002d070040009482003403150090340a0740c4243c0c0700ca0b151132513010708544c44a00c000c1a40d0b8010300580300c958004900c1d001e050070b0601070f0010751a41c03d80144000c0361603501041420101404080c5c16004521000c400c80c2c89610030b035107103c0e4110300b00303041e141072041500c1e002c85c0c800070040340114100000501a800e002c41c0241c1151005002885c102640c00c50440041c1840e00007102d03022420001e00690206801540c0641c05c070510103448540d41a01d412407600b0001e80e00e0034026410040c583c811289100b0000100350014102482030400050005000b00440075040034582e41517814400742c003480d03200040c030303c0009a6030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 727084667 1250 727083417 727083433
    0x110c010903120e0606090c07150f06030b1531020d1a01020a0825050a0804080714060301090504060e070e220c05010c1a0403031505040207031d010e03060c030405 71
    0x1c1d8985410007154845c0c1c0040b107940102e0187c0134454024000c4a014280c100800039000011506980240c03135280800c5480781c5090003403008860728140c00803102c00003003c0f903414480205403c44150030748652101041009401c0c0c281c1e00084040e045400d180c0119030750b0a0141e581c900400e00307490f21450840a44500a1403035000150425403240c205a6480c00c0c5000c0b000b080c0d841800900e084014400840003540c0029000c01c11035000710b20500110f900c0d1406c00c4400c0386024010b51002c0c00e08807130394002245644604044a054940c0000c002c6400d6076142003000c090b08000191814031b2081c50400240d042118001a000c0e001e080390201c1c40001018060f001b102040d01c01810381950741c0e10800556000d2500441c0b100d114111080d00c06441c022240302e41d51003250b0581c007281e00c5840c082c0ca80380d030486140c40079210407a001c50501c5117545000f0050b502004480c2000d40410500001c2a8081e0308690511b80008003240d002c1d140202454403d60401d4074112003500c12900 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 727085917 1250 727084667 727084691
    0x9060b040b01140a020f0303090615010503040f080a05160b0601031d1c110d08010906051c11120109030c020f10080c090105211503030c0a06110c01090312 68
    0x2488a107420503591510015507a80c1c1d00c402070f5003d01d02440641c401e00b600f00c1444030082c40a184650a00e2014280700c0c6004070380c0390100550511000d04001c01002044009010030f4202c2200c160012402c0e0b40301c00d6202c209a4541c49030b1110701c0c405001d010034007410060000c1109101e42800c0e601072200104140f220311962441000071030301a0803040484025255410248511100e0342c980400c1d4a00107800e87d508020321106188005484030b40103100400143c085c5000400e41600d07030104c0c0e00c4030149000d4103908410001080402007804d0b4000303583c0d640d0700710015000c2c0400200482c0c1c400c0c1c03030b01810108415074100d0152003c460041d46516280c00110282c00c1507842c1d0f1000d55a51103c0c00301c45500445409041c0481400054a080d103000c04184645809580010440c1099030001d41034585800b44c2d81d1003680200600009508003041e07244466a00400100b26440c5581310031a003405502d0070a0180d61809441c10b0074580c0c000d601807900301c1d41250800c07001032421 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 727087167 1250 727085917 727085921
    0x190219290a1a010f05161104020f0d0b0907050a030c020a020a180b04050621010921180812070611030703140a02040609140609100816020102090d080f04081009060b04 73
    0xb01071300007146003489100c100c80e50000074820400d20841d1000d4108a900000400305c1e00141051020203d0210b40454803401c2ca01c100407201d002241c0d040710b0307460034000007846032142d10741070020141c0350701100640d94000c10907210150f50081ca1102d5440e1503c208000c00c0c00400040b004503070500107c04018105807149502500025214040c82c1d140c03d007000d42102c03849014000c0a40d600c08005001c209602031143e5034401c3c0850b00c2c49001e00e0048020889420240240303101305601500304504800002c0125a402488441c15181e44450030b2510040c44200390140821400004211590340d0540c09144441021040d83c2c080d500c59480c0e00b4224052070146030301003440c51000f880700180e00c91800d01c0c0614000c0c006840e00c055000410300a0344204243c00c0070a0100301800000b1151142411704081244002c5060820f0740e070000345000c1500001620b41100000c1c4000704200303c2d411100545020700c00c540c1824060402d5500610500304251641407500808044a00d0a4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 727088417 1250 727087167 727087187
    0x3043005131a09101b0503030115020d0903020f0d02040501151b0510200c0105062701050f2103031f05090a0f15030503190219290a1a01 60
    0x80c8415040000d00d00a020381104c0000350041808405411211440507162603200c440784150301950310703035240419031802e0004aa0010042d504401010072120783d01900100840380c040300c484e00d400c45c615011a0302e210f10201c000c2d400c1400c220000c50000b80541e62051a0651a07441d1600d64210b1201200d20800d4850010071076000030031a0f1108100b907030040340a95805101c00230958200c00a850300d150701001c141c1c0c80a9440d0380800c40580b42101d0f641d134500d2001c0c50711041071810606a010b00420502420344151002c070342c2c0150a44500d1030a0750f4041d44032849400c9442000c080710b075607403c00c032401044d25090301d0380242e902d140000038070100e6001626044e42500d682c0520340c05004c037070f134540c280259601500410040c42200b00700003140500055656648a5103411030324120005001080d0760180c0c40c1c0d8040c10201040c0d41e0010f40e041b00ca40e001100c40c4441e001d04410419006c5440c6442a6040c4502098140c2c891942203508201c0c070003000010f540103482e21440 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 727089667 1250 727088417 727088459
    0x1205030c040603021305040612031205162a05070e070c0b010b1b160e0c0c071211150a020f0610050105090301020c0313031401050c0304300513 63
    0xe0204112050003a000740644142455010904688560118045070502d500c80c540d0145032703004000034150410030405001619800c00d00c0300d0325008a8142c0c1e2000c407140c2820802c200b45a440752869050b16840c10b0040c0c60f5010443e20f420355050280d5245d44500909400d003e40f0808210030900410441801c0350380400c07001110303880c114000340d664219841080784c0c68040c021810405400b071100f28012000c500c1e030107030b240d07091040c40a0100f00090084403407520412030000c1074800040d48108503480e8140d681c041100b580740518001444100c042d4000070841c0703804030910600700c05080080916821035203040b15000c0f01c0c66603080e05550501c0f10b184011001e102e80d520a000511100f800500003524219174038031814a113a2104804010707800000c2400e00230081c80905010a03140c9820090101d810f002d600382203184000380000b08884908550381403026094a17090320140c0d029241d45011500054010304113610810074884250814480401c2e03006455150003000c0301 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 727090917 1250 727089667 727089691
    0x4050f010f08280f020a0303270e0c0304020105040f080d0f021c140f040b0309010e03040b09090402040612050a020f030a080702040c1106010609060f03060302011b140a0c03120503 79
    0x3d100000000d480ba0f4001d841e0041502070460140e2114003082004501c02d0b42c2d5451003103248a807210105200c240c0d2043c5403a043c0070208020040701d044a41c10284000701695641c455100607100f502c956071044050400c8100c3c000b03428800413401d410b13260030984134041040400d29040f611603e016800b083d0384000e4081704408203205050080c6804035400c1070501d8481004140b90481d003080d0b0140070610000020041101028024004080031140045041501b03040d000809806610103142c01181086c000806541c5d940d0080030003007100c05030310704c06040c16080090321090010016405442201020681405c000940080c3d00c0c0d04041f22a061000356400c2101030303d08441d0280c00c1169140d4000165a0140400c900a004c81d032078482c40e4a180007006040787d04482e014a048c10b150503002c00c0580d070070890403111a44500d42e4540d00014501c0c000002c4521218607920501c180b1030600c0410200c102004143e80c0503442c04800a05022400c444c98442215416000c1c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 727092167 1250 727090917 727090963
    0x19030815090624160b04021203040f090203060612040b07030506100e0f0301091416090204050d060e0f07120c050a0501170a0e0607030f2a0c050a0204050f010f08 71
    0xb06400c1c0405082c41d1841c81d210741340c4041c401c010034080c400d00794250750f21607443c4103110071450166880c074580c082e0f400c0650300305850070803034040001140c031032041d00c2a0008006031440c2e8803582180c0045d03419143d0380c140ca04160600d09481c0004807070302c1002c01d2a00d0045940d6243c100f080c1044030700169200b512200a06c4107000402441d80c05050701592512140300c000b0320b0b40349055400c0b00195000700100c3c21030000d03818904403298805500d040c4100424040c0343c56030707105040d0654006901017200051032050601d4250010710341032550003510030110f01045400600803810380142142001c040e281c100f0400352a00f01d20403180410380c02c02c103500c07a11180c43c20702580f00d1070b04403000414582645100c3d0411b40c04559900010f03549a800f00800140c0d0b2242c0c00c111162864400700141c2d07803000401c0c0b40c0b25202e825200b40040d10545108000040000181c2c0a5015009020b18105014012140c0c0820700410700100705040c40414210400500254646075a42a0701010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 727093417 1250 727092167 727092199
    0xc090105100309080c0c090c2d070501240509090303010e06030f0a050c0901090b031002131e030c050d03050706050411030118031d0102060a0e190308150906 69
    0x400c00c65072840d420b040e20b541d850004284c950014081e011306042c00360003400481800c101303901400400000301d240052050641c4a612604000198504280724456660100c0d03080c403d10300419200411a6082a038402c3344664908900c1c02482c00354000c84c01040e41f01ca0410444001c2145d01848641c424001088145540c1c2005900a08d018050f81d281c2003400c86c85904008012000b03585642c0f2044100c00740b400c0a4508030b0041114240400030501400000f03134072400e500741c045400540105200c099521000800c100429a180300c480548602c6054160740d26031700c1c801070381c02c00c13160000060703541007041108040320703410f981e642c0c81c00c206075482600a00f0090001d0320005000e404a01013a2000d105400030390000070300b0411200c005103001855140c00420591640300345c5107000b8400e0340c0028030b003604603e40741000b003401c03908800c80703038034001e01c1c0c03100300f002c80c01803010742805c0c50f03000b40745d06000d1b0b81c3c500d2050002403403c1c010b000c04400d0903206142c010340c0000b0042e0710 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 727094667 1250 727093417 727093429
    0x3050c0d0809030d050301050a090b030c0f1f18060215010b0a0c350a050f0d14011d0f060d0f0309030c260610060f09082a01020c090105 60
    0x9501c2800810300348014030b0082454149104c0e080e00c04900c00000502ca28078003000c10000401602d5400d0000101410120f610341100080740ca0089808610f41840ca580d410408002d10940c004841d0144041c084010303c04450000003001d030010f001e03404600f00d4408941000800b11100e0ba000305a482c01065081035844000341c00d080100c280c40d01d00c0050140300440c454001c401c04001d00c6980140c03a94084812120690328041c5030420100b20220b400905031500321803270890184e100d04074200804050000720040c80148500300e000400c0040700c0108000700e00b1003940c01e400302d5076140c4a01e4410345200380c40459001100d0000c50000800411040e0101c0f88681b90400c031040c4d4076034845200b00326540040c040d44581394407001c0304480c1c500003d650054a10014541d50038044525602c0403040d0145100300030900400b00821b601492040d80148003420499143e07400d9800302c000c610000b00300103100400c1001084826610000b0100140c490007445030314a64038190800031 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 727095917 1250 727094667 727094689
    0xc0705150c060c0702040f060f051207090606050c0622021002030d0906020a0f031505060708161518031205070c15050114090c0403080a0e0306181603050c 68
    0x10321030408210072030140d5414400710340154080724503280c44903101c3c4100070969403000d00310f128040c0f80c020100a8940441441c104888054442d0000311201203002405c3c42c0d2035401c12006a810000000341e0700341d010b0001c24650030298103464403074441d020b2a064104100303182d1104416a440c020001d4500048500001170850040b07030701e043c1d00b0b03003005020360f0310b941429030700030b903000c0f076600c05080e0482d00c03054070014103240400940f60841c0c803030603860030349020302070007642c002c101c0d007040255a101701ca1285103c88510305500a5510b06150a1060b041c0740d00c3c8020705009883c16403400748003034840f0030b43c0e0540b5401542c3c0c1c000201c06004000050038102003003066000d603808955080b41040c00c46903040400320f26981403510680a114500d24410b00406441d81002070395240c08040d03c00f80c80d407002d543d594580110f081100d01651205016a160084105002c1500d4bd072084c18034602003140240d801400c2025909003400d461444003030815001050204035030f02d40a20300700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 727097167 1250 727095917 727095949
    0x10e1c0c12050606040f020c011803080912030a0e03090d080408100203060d15061a220812072f040506030c01051b070e04080424090e0612030a230c0705 67
    0x504055609003282c1c01c0d5140c61021814840f005075419081c19480100cc5601044540040c441d0407040071a04019120041c10321a050383d882948910401041c011294038480040000d0401c48031401e01c4600d0390704c9442840002d2040c032102031004007150003981e03c41d0400401c08640c800164503050074112210900c40d0f505581d41d200030401e40341800002e00299505035000303440c1d035280c1e00c0f141010b1031034070f00c442e03c00762031007804118000000440d0b000c0c800d441c0d20a16140c221074501007000c0e401e440f808080900034440d11440440181180b1103a046003107405100700c0c0c540c1000d02d0388542e032140c042400101d04116500340f80a441c01122703000d03002c1108980c2101d031744036040710120405841c03c982c00e8100090410940108440c640c910713008021440e82106c020f594060080e01c61441180f0513072400600040440e0341d20a0172107160140c4a05503903070b03015411001011144200c0f01d5031403900754040b4131000f01c01c1c40010750721a181d0001c01031803214144001c00c420241c00821403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 727098417 1250 727097167 727097171
    0x8132102010c0b10090c020309040609051302010c06020f0f090316032a180504140f060411040207020d080c011104030c05150c0a0309060917100b010e1c0c12050606040f 74
    0x1c5c032030381d1034418090101501d901075906e03080002c0410040e0703103da80c0b11070005403c0405028a4003211666050b1055090800340c1d00310043d498000043e0040e054103004098011880c02c41c000411401050362650440503100c5030a904843c2d41201312560002805505100f0710781880f190340000f03c4801e8140c840b1400c0340710307680c1d4060500701c1711087d2640303e1081d0722141800200000610381e41100c16990003c2c0040c0c0c0000211190f0f103010081001d440682250751f101510f884560494442c207401801024002c00300d0304000400c0e0b444039071100c100398038007405d0380c04241c1284107981c103490b4000d0325582003901e00307001c000d45113241003401005540204080030000f07a0401c4070b410414401d482d1000203501c0d0090180141200c0e621080c82d000000300481c01d02a408508070450380c8981a001400c6081c18004941840303520013041d070040e0b11001d0360003505801d42c802c204091320030040d810700c10b03440700822000c00c4940000101b45504c01d901141e0b262030190005984c1080c08070340 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 727099667 1250 727098417 727098419
    0x171c0207090f0209030613030e063004050601050307060e040207050c060d0b010e060a020d0305090c0307030c15050403051f021c02071205041a09040908132102010c0b10 74
    0x401c00c560020000c50035031540010443c0755400e007408056800341e202c00000380c4200298030040d0805904a030600d114a2000802e5032003850304030201501001088403032082ca1118005002c0d990205650941e0248104c4000148038500094032800380c903080e47d207134290000c40c601800080d4000d200c04840398002c01402040c0d5880d03002c0075200c0c0c00e141c0e0b440443c03400507010000d0a2702c190760b05614000c510421048000e41d030001400d10010b10a0701d00082c0c0c84ea00e01886500304141801c91981c5030041007000001e11400001e02d505403030440190705001901c011007600c480c4254440148141c224181550710a1a0311502d141e11389482c0320054a44180300d800782e905541d08070f40102e5500c2d4041200e2050250006455a4065041c10134070315050400c3c1c080000780b04074240e0ba0b83d440800007551f04681c1c440f41c010502803944081c140b512410400b25642542c0d11038041c40c20392001c1c032100f001048900c0c0c0d000400036601038407003010b58489038940a514901c01040c103001031403030b844 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 727100917 1250 727099667 727099679
    0x10507060509030d09050d0305061008160207030b0717010b0301030203062a0f031f0302060306040e010b130605031c1d220501090f05040804060f020708070e0a06171c0207 75
    0x1e1740e541d548190094019120004400360440304080e0880b030094003244940480c1c145c01050380341d0404804010745141c86c2d40703503000303d282c02c0283d0001015048010706210426410804201503580c15078004c0f6030380d80e281c0382d43d004180024030001c0d6240d400400801d4040c00e010200c51081c070f909206480880c4001a001e440a0340400344003c10701c0300c00001c001c007000c0100d200c0307009010b8a070140106549140c0020340e0602003d040b03544110759031421310242c10310950084c0d00e00035018015a02c4c51600c0300d00200149141e2040c140a409018200400c188a42501500440322a03c80ca0030070110186504c421070950680f0355040200c0400d10300e0420308403503c40c4090b81007684089055030404620310240d445180b02d01c1311041c2840180000170380410151419244546880d80c0006064142280b07010450b61000c002c6006606020624014485040d48280c0f1940e90a2055940d50803040341450000d074105c8034190492030104203418080c6c1c00d40c8400350101d1045456440d11a0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 727102167 1250 727100917 727100921
    0x41b180806010305061005011b020103020f0909010306090b070c03021005040c0b03090d0f0e0f0d170403050c0316060c2301020a021f02030f07120204030c0303120f0506010507060509030d 82
    0x1c3c000740c41960240f020017480354a180d0055018200c01c0ca0101007900000c4070340401d030483c1035070003818548c0104000400500190039103c010b84000e2401882d542d5070f04140e8002e10302004c0548039101380b0000644014040c820301114a0360513802451400880c48018000b01070161045680b003400400004000130350801031802404080050706004800c01405480c941010711001c05100c1c03500b180c8a02070b940e991003d002408261120202d030b01c0031b884c09083c44d609450140d200840e0108000c020300400040401c40c404c0b060301101c14050b1003001c1814000900c2c819040001d90990500c0d0002e040e110800032007091b140c04210880d40d0f10f0804e030303081e43c00540900c00107034811600e00001030b40c02e00c4583c41b6140d4004086281d420040c40c60078015800038114402d0006004e00031856540550403640119008040320311416140d01d0000c010070844840444007030b0801802050b00400d510a150090005840e082d00d050101da4844025010041c04031100307000c2400070074815003141c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 727103417 1250 727102167 727102169
    0x5030a0b06160303050f010807060903060b0f06041d1e0a0c020c06031e0a02070c051c1e0308061e04111326060c09010507080702040606050405040b041b18080601 71
    0x113618041450724100f0100c484501d4141d006940c1a4030012707003001129000107030b050030b80b6000440842d1417a641b501080854032001c08050700301c0c4000030005145503d1180070780001c200e4041251441d280c510f40080b0345084950003c44c415903020104980624580c0000c44c0e20b142401603e000503c004005071300c0c0c1e00b0440b00c600140b41c140c0200420b4520790809107901001f0480704501300699a00e6017500ca407154010f5500170b81100c5511200130514450948100781d22008182080d080c014004008201a00080b00403542c40300c0800e06900d0080c92040460980e440645101550343c010000603000d45918411078810410141d43c102811840101c05080300066010090401c1c0d21001810200710300401d0154100c402480020400300c412600e59030000d19006071a00c240d42401c9101c0d200b0403000075840b6241c82c50001c1c2449d0404045d0044400441d4104030800c889010b100a40d0146003aa0160031510344403016403501030185040b00120b00b005500d03e10b6202c0c1000c80c035003042 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 727104667 1250 727103417 727103423
    0x4030e0d1410020c0a170705030408070504060909151a03100204083f0f030f012c0103021201020912100605220e010b0a03060b120d05030a0b0616 64
    0x1c1009503003940404201ea00120341d0800320861900708580030050701e4140e201e50007001ea1082c0c00c4036106070407040b42070320b502e2034002c0140d0703580ba603803a40c420b56200118031681c2e00660a042c000074039665a88183d030001c03500144000050030841400300c2c0201003a0300d0840010401d01d801c280d054030200b04900c0c40b1000f4150043c0e0300c904050300149441d509040c1542090300301c0b0341000017410341145c1030f030b15001b18005140b100104810458107900848005246c000008010004450f01401015040790100000300c1e0f028101c0c61440035210994080c4528115022070040005052881c40007103c911084001400c1a500400145000003025003084841d032181007129036140f00e03441100b0007010204d0300c0a03e855041200c06070b0300e40032840c10400460752030344034a040b1307030f020740041045400040030000865268540003005010800085014564598201d44d600d8400a580e102003016074643c941555030751495000a0040c42408541007001800244c14807250100340c4404184 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 727105917 1250 727104667 727104683
    0x1903080d3303050c0a030c030803090a06050a050f0603210d021b162408100314030d14060307150216060e04051501051822060f0906080c040504030e0d 66
    0x100d0343c28844e24081e428101c1e80c0c4140005001040020b0800380311900322640040f540c1d0316a9903a003144c9041c08000040501010f0401c0c0800c00d401d4000d5101503c5051160001c410507100c0100b890394404011500303204000700305040140200c0750070050031504501a1000d031501400d0405021014411000442d00d6401417400c2c00c0b80d160240f4401d00030f8107034003603040f000300368060000c010072800c100180240700112020441000314058802c01030740e045070b1413244000c81c04102d10b0780e81c1d00000a0b0006d00d80f504080004101e4003c200303a0188800400500b9042c0c1040c0c0425407510481c01644190b104003800e410912443d0001c0304003e003002d44070a402d0071400f0701480300f505d0300141244030011841803141c040b80c0e004020f80d04403c41c40f1781e82c0c0f1510204400410340070300134005a1204034090350544a800f03203181c0c0024054a8924070f5065040703a0380c226140c1035441a020ba005290016142c10310790b41020741c019540580a03181001c00c42e42c1040208050118a4400762403c4e1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 727107167 1250 727105917 727105919
    0x14010620030d0e0714062709010303080615030402030d05031f0806100e060904031202210702150112150b040213170a11190503060c0304021903080d33 66
    0x4e014000080070000c1c001c4000c000d507840083c1070340c4121004003e4100e800220030445580d4900c280314000c40142410340380e56100d0902800341c12045402078800e44054140c241d10f0001501a28000e503406002010b140303d9030030082d2141e410042000c160303442c0103640c458800030441c05e040b0080c915032028100c1ca0600e0303141c040c0c900485170403a4078654454000e001103511904042a441901440c10b801200c06400c070300e8000c0d02c0b604810184c0c40e100c0b040c2040030058614000c601668503502280d441c032403920090035074500d0034804c401d645074641110340c010901540d0320244001c2c00307250000b101030780c4000040480c0c200303110403040d80d03034a4103042c09045080103c403120003149100510b14064030b035a46201c04030701d206099000d000d110030130720710f40c07140d81e4a105e020b130034011306480b650725041c5080b007115041220f00782c0c03054607500d01d2a440c801c0881c10820550390014407071840c100d240f084180141c69484640400c010702e07005509030b04994000d0f640c20840000000448035 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 727108417 1250 727107167 727107191
    0xe03030706090201090e07082a07051f050f04080d09060501031118060307090f06090203131203090b06100e121006080601240c0215190314010620030d 66
    0x11665030025086c084880b1300f070120140c0c01816940e8813205103920418825000c075050410000703181d402034030882000c80e42404014021403003080300317051110303080001158804800c09582098840e070b490a030500011901141551004020b9201011004520780c60542e0313420040351401d80c801d0700d4130042120308004604e0704030407114840c2c440800d0100b141c18039200003030302d4031074520071280c1d200d69504c908110410315410a400070203802c44219161301d440c646a1f4020124040100c42040e0308414015005010384510060a07800024603a600d41e40ca20030b000681d4070b0742c0f110800b8404074090507811a5221102d6454074413503038020700b1600c42c00d00b10800c29078019420100b42904500014400d0f031215005043c008109140d9040c504000004251046282948047d4200c60160000c0c210102d8000c000c004203003021544420711540d42d070341281215802c01802440401503001048000d225068a500401d48080c0e0300c10803030080e81110346983e10841c140f019140c2c80c1c001903048 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 727109667 1250 727108417 727108427
    0x30503090c03070f1206090c060e01022a010509040e010903050a2c090414030f04140103020703230c03130e01061716030f020d0e011a06070f030e03030706090201 71
    0x6090400d0b001000b0250034501005a2003c981c00b0b0051560302202c860014814103801101c10160000040c05c03070551101001030007001c0c243c0c2c400380036100e2180c400030034003002600c103103032030140110607884240100011225503200c002410b52161300c0e0114505041001c0c0300f001c04691090701c8041e0f68a014100180990b0f00f220200020801440b184000c0c964040c00350a08402c4125441400b5a03036520388604001401c00780c0105922000c941040703500ca82c00000c005aa8110000c80c00c1900310100450a91041d03000c0103001401001400d0200300320f009a410014000c0445141400003c0c000c0e24907540100742095038501300c8100c100070b920202a02c1c84d01600813440c2c1070503210002141c00c0d00105002d81800720b20b0300c82c141141da01c0340c400d03441007001c02001c040566844107081c10610140c17512079004021743d482c080070070b00510300380e44072070354079100c041c0100e4200b20158481d402c8101050005034140600e0180c081d403256800c0c030061504611a64000400500754000104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 727110917 1250 727109667 727109683
    0x20c010e03070803220e070c0606090516030c110d1d0301090203030f0a02010612061505011112070f0212071409060a0e0603120d0605030c0d1a0c120403050309 70
    0x70103904248410311a42a020045401d081d01c054100d10203030182c030070b001001800643c48400019803400c14480c0407544403180c0665140250004d0200c10340707844806e0304440c0c040d0b40c2c00780c24240746066040340740c0c000c1d04400400e08882c14071024454a000740c0d43c1c14519500d98480c0082c001d542c1800c9801e800c001200c2c00741105a00801c460a550390110365244143c0407400007030940440e42040c03481c0b00b50408400f800d90400c04e8241d8a00929100c0090300d00401800960080b909000c90254440d43c80c80f200703024104020070b16a2920b0140d00c1c8650310282e030641713408a100c03209401603104d406408840168903802802d00d01d140882d08000e40008041841c483c04052041c095166943d2030000b00f076a038410140003268039000e00083c07074450543c047c0505254017003107214842020703600c04411124140c041e540c907810b10308100807511003000402452192008030030017890415000702175100c1000a800c1c0c1c9400b4004c84002c1c9146d4007201c040340020400002c11100d81e0081c01400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 727112167 1250 727110917 727110919
    0x180702030702030106090c02120318070b03071704031b03020c060f12010605040515031e04060510120f080c100f060f06050705070302040e1009050a0b0f3c07020c010e 73
    0x2050803807c1c0300030f440305800481400b400c0400300103d0071620078901c880d50340544001c2104d128035500c40c1800c050344c0084a0390404590340000c51001c00304850b40c42c600c40d81d807543c0e48080e20241e450150055402804c0180c0c218482d11003c1e007203d0320342c10700502003c0c0740050401d4640381c0c200b1080c810020143c008000304101480304021720388030103502d1a00c0c001b500d9691a141ea80e030300752400404555000342090417030007105000038031100f03900c2a0301074110b401582c1d451a845824800d00030174113120043c401001c03c40c444010801c1030010381034080c1040c00742d03003c2000c440c0a000a60300008904400c581d9a91000c1040656a41c0c840c0b00074000c6003011410322005484446d200d00c09444081c1c000ca0b11416102c10740d10050216042101e4203850810800e10309003030480d960b0742090700454202042501040c4c0f12120180d1040c41084101d0b44141d100701003188911140f0402e02d00c200241400c074003a540320030400268244900c2d290350040080351080d0300010f210700c00c0700e00c8071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 727113417 1250 727112167 727112171
    0x50304051005040e0402010c02010e1804051204030203060a0e0717061f030305120709090623030f0d0c030513030809030d030204050604061b05120a11010209011b0218070203070203010609 82
    0x10859a1010100c0a45c010f4090070850200c1503a800142c2d0502d0030031403190b610110980d0f00c8240c03500e07000d0b007050059000b401260341140704141a1000c1d0310840c08080c2d03050344480b00003003034944281c0003240d280001c4030540d0070a5645503164503940300d8101641869030011410007883c1d000d2040f284400741d00762100c0646080c0785032130107022442000c0c2014112040a40060350a03809040100010320500341c0410908c0c0d13a81d07489095406013600030b0000009440f60580c143d16001032010342c1e1074040000f0b001d80e0b214101d0156840540c030078084060090a000b04650411028009030056010306040b56442100c0420181081c65400a41060601c18041485191202030030b850a54807241000381d000e1418882801c0d110410020081c42840f50f40507640104134900094a1583d00c191a01b088028162191a00381d000c3c50140600180f01000c1045109140c10201e00e20a800900500002d90101d0365500080310216400000342c2c1c400120601141424452540100070f40542 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 727114667 1250 727113417 727113419
    0x618010f05061c03031506020f010b0306222d0605090a24020409020f070c120809042c0d110604151119090306050f10052b05030405100504 61
    0x50104500c1d9035252501290b0f85201100b05030096210718910701d2200c00c0322517400c0c0c2d40c11000f55150203c001c0340b0140d50810b02d1160311070800050240c0075680307040e034080c00000c2004010400310b20410091307030f030303600b8400c05408400c0e0710460304500c001548911a201c2c0207141803002c01e441000e800b800c8690f01c48a90040800c612a050724041d00d01c6018000b0283c91900105019014940001200a100284070070209050f0b9005003c030074810080c003001140c2d075504d80b02c858540d0b00c6000d403404008202c03200300c520f0258041601c0140071824240c141225501c40d0014a0914242e221164480754000d0040e41d00190310050752a41a801880383d840c142d0345900b031040d031444201038050b46418560600d4030301002174072421010484c1130001c243c500349008000d44120301c02900c08c3d51900b80447e4840d10101c4481d4801c0008a2040d085a8900781c1800704160709101544404070316040d07248100301d00c2c09018200c49008000030768886081500304901f45a580d81000280202004 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 727115917 1250 727114667 727114669
    0xc0227161d0d1b09060947090a020a08070203070305040b07031209060b0109090c0909050c04080307030e010f0f020a030c0804230f0d020a1403120d150e0c040911040302030618010f0506 81
    0x1681020b0054004c3c41c60043c212051110001d440c4643c1c030b03a86c0071054408100180b0313500c2cac1c01b07015481007030b0740d0341091901c80c6102a610b901c200e06010380011300c208000d200724160b0b074004109a51192511070340c02d0b62141011021100811801c035641515801409019a031065002c8041c0c5400d200c10170116105240142070094030740300300c540c4c0c107484034005101c441c001000d4400400d041410307259502e02c24a002000e50040c80c4000340424140d1240322980c9200303046203111000d9580080c0030103800c0303444c140e03001081518102d4141600700800f0510700112220281188080c046030002c004000081222070900701e60340d140645540708048000da99104070200072504542c101c00686540e0401003030500402c00c0d04115a107500003000103a40300140d0007c55a6900f040202e13801c0d40d280c0c02e02000c422002d4170818500341040c00180010031450340560200c40c0064800303071030280d03607038003290611504840100c10740014082c8444000028040d0728108920340f5000c10413807401703c2c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 727117167 1250 727115917 727115981
    0xa0204060c020f0d0f0506010305060f0103171b010c0509010311030412050c0307080301060e090601030615050c2401050109090c080103030c0227161d0d1b090609 71
    0x41030182c80ba01600c01d08140549404c880150101d030400e030f64a800070018107203190f8920080c40129614411040010340c81041449814140c039803011604150b1258612680155080b0340c0610301a0a20482d41c0e0042c82004d12805103c0303210f6841c2c081d25241c5e2000058119032032850700124100c010000c000014401250025080c01542030031604c46000ca20540e15500400c00010001c03807000001082158021010501e05c02048450514595a001c01107054030b6181c4200d178401040505415401d82c00360002d40300340b00d10b05080341c01009205030050700403000c03d0000582c42c01d2100052119590200c41c2e20040d064401c414821204021001004504144030103003c00441408080440d81e40008041c000340b0721680900c0900720803010a03905076020790300d8103102040d00c8160b00c1150300460340c0c035074904d07010f1181452205a80003480411f8072203903c1200d4501c4500c00301180c00301c603100760901500d00e01c400080e54904002c010000c48034090182480311062782c03030b8a1881c1d1103030 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 727118417 1250 727117167 727117187
    0x1205030a0827160501051612020f031b06070908031215030d0906021b03150405120a03020c0d050715090623040c0611070621090f0501050a020406 64
    0x68681119155118141402c015069851005804041a141480040000903100665040c080d5070064450f520307001034580d8414140400080340403441110f0124540c40b1030f5051144050050384e86403180d0000140c10b540c0080005a0407464203440070141c5117003080010780c0038045007000c0700c0640c20540325950324011841001142c10350500025001d452340e1210070300ba4600542103a03600500c04c500a400c082c0203000d0f14005206419443c2c0404c18070542e000b0f40310303001801600020900c2c640f010116900100305907840d2041e84143c640e107210420003805240034960300141c82d0303040501c1070707030418000d1a0501d04101d81440300c17201044009410008800d5402c1000991015526003036010307201c10100c0200f82e40b400401100c041c88481d5616114038032507035126803280d885074410784000c600c40c840200c071a44511400d0096902840c91801c81031082c1c0380320280103102903285c5c8180c034044001110060441082c3d0410400e00b405402e812a400749415414582401c000401d0a120 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 727119667 1250 727118417 727118437
    0x80612240901060b21060d0f0b0712060b040308091804200301200315040e0313050306070f0f112d0d080601030c03020405060706051f03150902030c090f070207120503 73
    0x4040030030003587d20b4032075965100e5403100a60407000e2650500c0d5020240413900d200104805001c14039103258a0300c6400150350b494200581003600b15210702d0256048040c03155004403007945250703000814401114400c5200c0c1d443c08000180441da80b40d40110382000e024047c2c1c4c100400590000c046094002400e000e030b681e00c07622517583c0b070301502d44c00c181c406000360441d2829041480043d004001000300c1150355240c4850b01d0381e42d030b0070b0659030030f03046907070310000380c9484054a81d060ac201804040200d003441e2400589141c28050380c103003949002180f9002c1c02000754504021003915200000c1d41640d0b02810400182d4000600702000007002c86042590381e601d90304500f0f0203039042d90302a1002a000580710243d601d8400d006041c01d03584c2d00f2000640340580c2e20203180359485501502d42c80f0b03481006241c2c00400600c054040c1080807079050003055150219500c8010800d8841d1100d1040425103040014029043c000e1903040080703074980400c0741901003000003080300c6610714 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 727120917 1250 727119667 727119727
    0x206010905130f05030a030b0604050a090b0a08100615020a030c030f022a01031103010803071113020c0a0c090e150c0f0a0216090b01080612240901060b 67
    0x25a900700d022021a4030b55004103420322000411042c410008081c141820080d18200302c40c88000041200030700a81c81450750101d40030788184201015600101e43d1b040c4044c1c900481c50303480b80480d41c24034021407862064155100e000b04020010520014100403860018060700c008548004000a9050801900b4821200c1144c0d02c07441c420000c0c04420a8084075081c903c440145400010400d40d484a5001a00b02070391650040002c000303e90485a002d00110303e041f03201d5443e26200c46101e100f20350b208050540040500c581e40c0000c0c01c42c0b41c91b15000d0410762011b450881039100070380e0003a002851400c03d4501c0c000f20001001051000a810301071f207541d44049090019100b64002d880e840708c0d0124810300d40d00c0c3c001840e140580c0100f445c40402c80d4070b0312908c400305d600c0311800c00e0000300c0d080c012031103d00741440c0b1004034215602c251020350042c0c0d455070020202d000302010400b1170040400151160a200b540050408000c0130740c5800c80d024100311300d550424000f500803607 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 727122167 1250 727120917 727120921
    0xa02010c020f0a080601140121051005061c110306030703020d060b030106060c060507051c020c07051009090e06091c0c0f12030b040c120f0f0905031b0d0206010905 72
    0x25840080000d8510b0008040300c10041d210341105481d40020b00c110032000c403070318a01070305540c001c1002e00300c1c5080d0000c011501e55a90307601100508800b030008000c481c8207150220b519151003004102a800b1141b4205400741c56210403002ca4040351604004910f081c400e006142e0b4002c20081c0440360126084008502c8604002c2c00408040380b070b50341d07d0342ca0b0000010701c280d0092882700216010f50740400840e43c41032400d60340c2e1320580010300c0301400221224040010039502404260a100f8100c9508589910105040103400d0b45540041950782c03504010003d11030244010000c0f9541c00f80c03c040c24456041540c402c40406100c010540000343c011000d8440c0c100c2c0450150003d0f9840f5105e00d031410100c0c00481511610400a070801264030f0740d90506005e1500d40041954400e00031100070700c001001403025450748814583c850320741c201c2003491402040b024a000300302039a0344510180c0020b07020300c0c2030002c00c00c00f50803004526454036008600d05044408090300480c003a = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 727123417 1250 727122167 727122169
    0x90c0f180e0a09020f090721200c0a050105011e060516030e0d05010f05060901050f1302031506030c191409060304060e030a08180f031b0705130f0506040603050a02010c02 75
    0x42181c80c1c8429070010304e43c81c1005a076562019070212101220111080585100c1002d102275501d0920900220190801c202c00d07400151001802c05240d0801a51040e9919a071154207407103080e804000680d04c1d00601c80742c003051408070080203180600300385242250400d0703014020040c1d0140a810700c44410041c074611344541100e03410035039000d0300800032000c030341e0f550200400040d644240603031080380c00441c0c0790410603201003566400902d0140304001001403000654001819000303d40920740542c0c02507103484000d14002c45103c0410754440740c000e07144900300c00340e411400b810880d01e950b04100901401c021615100d0091340c2d5199a5503844c202100508030401c280342c024030002850f00c1c221a408804030f4040d1045505110220154681da00e5480003580b040c08000d8001300005000c2490103440030074189080d005442003259180c001803c9010050000080141c0760344000050207aa032203265402141114100000360858507182e80e102d9084100a0500409580350019 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 727124667 1250 727123417 727123429
    0x1f18030c0509180a0606061707080a0b01020c03010e0c15030106140904060b07030804050f0105090309040b0a03020a0605070303110304080a0503040c05120a02120307031e0504090c0f180e0a0902 85
    0x4801540f800312001301d211490540010302d404e1003800009800c060200083c07202c2c2544003805004a03590780140c81d1a203041d18801884651485d40c15440f030b4801044540d2402e0003540c04002c541006005a203050105004040010385604078078808108010b11510f50088107502c0c40c0320320180c000d5120284200407500071308a0b50011070032008081000003c040d8407401844c0304620605c180c80401d007000c43c8043c00c0c3d40081d100c1e0b00680e0800c0c4008011414075030f1101c01e081c40010100240c450780c80d0046841d4030134581042c0c0009038005503913030502d5014000c0d03d04007d40404514510700c3c068445d07541602138410f205007007040003c04101880541c40c41ca4010303142c010301c80d100c1803520302e03a1141da5010751441280584070009502200020106c10340302d84070b800d601c80300700b070f2800090400c4010205444400c140070b000d0001248181e0680b00d07843e40401e640e225001c00d9281540090080c40d443d20800c40e4485801005221a0000c042d404d40c000342003c0c1c02040c540da00b480080c039 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 727125917 1250 727124667 727124701
    0x30f11010608011505040f060305060a111e070309170d0c03031409030c010e0304050a090b0d12030b0915010c030807020a0f1a0c03150f0f1f18030c0509 67
    0x82c02c0d42c207055000028074807100021382259006c070380400040b4080d088080c2a124075100c0548150046400600f00c9811034008070411403081c40d4040c82c040021448000350301c21800c21003c0c5c00008074a0604041c0c000007854051b2030040106603c2c0b46107003c90603610715480748007201304488010840304140c041e800810804070180142d4031103141c01f180c0c1c07942c1c9400c00246803072203608020302e00421440100480f010340710b020b03004110041c1881192409000c90309417007900302404483c02d40202d205485d1030782c241012982c1c04600c1a608404100241c000545004074501900c402f070100d5a0300502e41c00c0ca1164503081401c0282e4513410700313034103102c00c4403406000407418568040420507030121400302d495041091280740d13221140610308500040355240b14111103020178000a00c0c00b8280c45103540b038010308034514005040302207128020107200010003000200d40f07540c5400e030440310043d4aa26102c0550f90500d145480d030b80ca1000c0c0c07512a05005e03111034404a0032001d50078030075031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 727127167 1250 727125917 727125929
    0x1a04050114040b48071403030904110c07060c150606021f0e03070302030c060f060312092d0a0e06010c0209060d02060304030908010b0a0303080106050d0f1503021c030f110106 77
    0x1603c0e0340c1a1303415800500300c0500c01a0090042a41c041040102400c140c5c0d50030402900460401e02c540c8280001042101c4180064107020b1000c0340254104007d0803014000c1540c42c960000700304e240100310326003c0d00401d14200e041a10034000d155000076800001c0112408000480319459803031002860341c81c0030300c5440e0200164060603d90004000d20002c902c10782101d40c0c0b03598040408511000954009905410002400f104408504088d002e003502c010401e2884051003000444800c0350020100a03030085644400d0b85031078598503900c0140501c1503003038400e14208000928040200c0c0f4000d01c00c0d02075002184a644a205482c00340c2940903000980e6810b2904015080c0b00051181c1070031982842c1d45100c16040c240b5405089990580b981803a0340d0814906030740b6078006881203902103035123440030040340760103024030025039580402180382e0300e05600500c81e0f1130210042481024011641100000c0d505c141d65001025803850400e9090403e41d101038054a0300d54025 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 727128417 1250 727127167 727127257
    0x711240a1a0a06031a040b03120a0e0402131502060f0c1b01051e01080307080a050306030f151501031a010c030c0b0702010519050f0f0c041a04050114040b 68
    0x800e043d82c140d4001040c4940e0f64201040250103401048291190a1242a016008440c156800c1568a005400900349500700280c0d961407401c049001c0340c10185a447c03480741c0c0d001c8200701004007000c805410301d52a03c080d1a04d0718119201c5000200090044035100b14005121044404000d210112000c0340c10024002c03810018020528a10300f501841101c60b186400000c0035640001264049680688401e0030b114140a0a0f120340e00028121360301402080301001201341c00740b0074503450068088103010b803810f01c141c1d00340c1c580340b000d80306e541031524003140281c5044044011040c0b03041c09107084c04045180e0315007100c400d40300070300090102c05040140f203403154043d000380784541c64864070108460365110f0030714140c80080d1a00e4418400c0140861050621072640e154442c00e800481071419603954145c0c20304dc1010060056080303408a0140010f40c6e0041907104411085c40d2170302c0c105800c000c2e4100140c410003041000c1010901800050120000d89100d07001000441c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 727129667 1250 727128417 727128419
    0x11010e03040f1a03191a0d050115050a06050d1505090f040b0a050606030a05040c1511070906050306010902071e0809010e030303010614071403030711240a1a0a 70
    0x80e016100c1414010f4000038046403600381c20908003581074038800c50108102000c191501c4001c13000400b0700c0f43c511041d4081500070080607845440d90703c1103051050000003a491342a039001d194146542e0051880751441910410001da404030a44184a0900100040c00030701c40e20300c214048217a034002c46d00308000904000c4c080085103600c5d841203018014126150790f0742028941180c40032580b59078001001d00200b0700104d107a5100c00d612510483c2000e1100351200314281035400702c448010006081c80300c000541a400f407002100800031210107000b101e08003000207482c1c0605029074150305902007007040501c105030760b002031114800d02c854a200c110038180503a403079002e07080303950103c1c80c40c02c061880c81c10004100d17812610303d0355400050703103015440301130380c3e030311030902a2040503540825894000c1b088c40254002c1c603035a1940c2d01c030300401c0605181491000286216041d40005403d0081140100b845130f004440302000110072400400d9501a5403200580b03540141503d18 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 727130917 1250 727129667 727129679
    0x6050d05090c151909050108010e100b0d0e150103020a06080702032101031b050319052a1002120a2109030e040e19060c0507060509060402040c020d080711010e0304 72
    0x40105901c4130031038000c81000c582100305950010f81440350900140c0364600401600e80215040b58001c0703021044115241c0d551100340240e030704405905050310b80c1d01d068600ca1101c0801080c2c21608002e540c40804d03601d103400141c0220324a2044d00c0500541d100018080d40c400c2c402c450070b143c461915901c3c3c4a16943e41d00c4441242408116243c0d20018040c0e00403500c0c904d012021640010010b0410340760100105010303400b401e00442d514800c61503050440420010010301c4030051851200011069200b008000692180b5030810354000701441c1010420160444600000d02e08040a50000c2d072007014441458850b151548645086020010194410105000355000b00c40c284450380780e400e407894607200d10320000b9040c15000c07404403000603201c1c0c01840800c04a403d045082020a803103030819618100c1e82c0420f240c010b0810401140b41c0381c0703d9105041042c0c030007086c4004042c00b0217417080e00d001d800c05050049801c0030300c003508800d40010b441c41d580e4405036510b441d40d680d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 727132167 1250 727130917 727130959
    0xc2116030507030203090d12060509040803060901060807120902010504090218040606210b0d05060a0203250e1201061815061707052203080c0f060106050d05090c 71
    0x400500190815002c103101d24828000c0d207019407010b4018003500d8100c03500c00e0703442d0101c5d40e4821031042d468400c0003542d50b88a40410b8450b501441da020b94924100042004140058100718203014140050010140c0d0009212070b8482c150980065049001d00058895000b90381c000305140340001440444115044503204000302c0030350302070010355210304058a1b00082c244104e4038500c0c0c030304240c1d45100700d070750000075102d00050040b10105046888007402e0600c102c40000b2010b07000024800d04103051200a050a00d42010800c40070841240003400103074100c040314882c00c90b00720000c0c003a0f042980507600405440402c03a8031104c150401b203024000301c46006000742840180014814054683c10300790f0510f01c840600542d81c0c0030801d550542100080806c40400d02c201c443e4400c5d9100e1842010354020803003107440d110107580d410325182250751040c0d450f0b0485001080500d4004c02610311422001d60040762583c2d0b236044017846c0c07100501125a020300d40c0004207480075405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 727133417 1250 727132167 727132201
    0xc0b1e030411030706050f0d021e0c0607090905060607120225050112020301030c0b0c0705041e05090109020f0427080703390503070204050106030e01060911030c21 72
    0x54082d0744d02a40c0d80d14050b0f44a0003900c1c05c0e004041c00802200041800c0c641c000c02c8140c05030700e01d00c20020448c4503810001d801101e00704000358084824006550b4018100400a1900c46400c0c05079181600124090f8050f80000030300001d100790845116500a0110441c080c6501c00012a52015881c000c8543e05084c8a810701140f8000030b0a025400d0b140200c80c181c0b0f42011541301c040c1d203002e205080c207900201900405000e0b9680104059a490140184030610083d035100b02c6946440d101e400c8403000741943c03000c2da147ca046c5500585031a0010301c06000100c40000c0e428001c5440042c03070607888405648005480307442e91080010380c401901c0390071b00030340c6e03644d14022010130f504400d400c1041104c03c00807a44a400108003110442940303406101e10282d80c20000f20f6404141688c200f81c0000f000700b80c480d60100f0700ca6500340b0031840105031411060061010031780e4011600c0c8806041001030410014072500b4041010b10b91100c0c101c1002d880020750b181c25040c50403000c01c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 727134667 1250 727133417 727133419
    0x24060f0105070c05090603100e100e010902030606060a03060e0c03040506130506040803040303020f0c0604060c0309030c0b102402010c0c050606120c040f090506060108040c0b1e030411 81
    0x80480246965101c1c01c01e8540050b403184021041505140070024550402440301d5414425842c06060a12850040d2400069004028040b44d180c00b1145405d07102003510200c02689000c180d42c0c00750390700048075074201c0d8058684550f40c010818003240588225000030301c0e400240405e000d280400b43d0010341c03099002d40d0948100703444100c440c18800ea803a403006411548890042804182c1100056401a1280c2001458000c00c1101c01c54150041e04030020a50041d40412042c0440c5000751a0288034070300e410800350041c2c0c1da01404601c0d00800280086030f4810000e5203000b0f4a641d2440580340c100c2c100b84052880d120040045400628031000650900c134090024900490f492280716500c00083c1c0420380d41d02050241400c580b4071400c0040c0b140e26240390040e2074500c01c1d958101d2400300b0104800065080080c0f511502400150412070a1000c1101084820b0080d806458550220304d036287c2d180e4503550201e4407101801900c0c00c0c400002d000c1008108210981c40c210 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 727135917 1250 727134667 727134679
    0x1c090f060e032107030f0309020909150a020a120914250b1903020901020721030225030f0809030102030114040f09240905030403060c12020703140c2406 67
    0x54507035407080c2c2000d070b44481d03c1d4400030280f145900103800b80302000c041c03c146240008480a240d00015000c880681e103c2c03c940c0c10403090003c030089454281580510480c1d8154900128104014419810000f0440d41c041c2d50782003403001c000313452030100821030b8010200d038254418007000e80141c40d4a000310300245c94a800000070001440820340d106103500c441031094015a41400390041d600032861281140100c00010a400f001c141c200e1009480016034102e03002d100389006840c1024003560b5004078401c0610824240402c1d1140d0000c0e20741c820b5201e080b8000918040b8518014602d0a9615500200000c102544080401202d500c011101030080c0c3c400640c55030120b410944001e4402c520801059202400d0a407003843c0b6201890000900300707900342c07200d50179500309403c01c03140b242d200d006034410250308c2500c080d0110604002189412070642d400f500a80620800c215030120210314210b0480040c00311011000b4a1524500d002c01080d145448224080b038007541300e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 727137167 1250 727135917 727135933
    0x50d0f030902030a02041806060f080c0402035b06050702090705090a050306010b0702120d02061303050c0d2c0904110411070309060f111c090f060e03 66
    0x18803900803041c400350050050800022940c007888080c01001c203034a0403c1c10004241d1000901c83c0c0b10b4031000300524809242c10300d060025450030f02d90046680d0344103600501c288203801e2042c0748440540031888010b1300101c10344880d07141c4103d034031031a948102100c00200f0866140c020f0812091007035011076124015031103090641d00b5014665000c0d401940c1c410000307880c54000d90080404000c020100d45006030f03200300080c9005800d0308100098407020918004604150650101c0d104041d00030b03203c0030300a42ca000759109001808006441010017502003414080c0d0700b00d4040010541c152009000180e8020307005241084902d45c5480341c0706201c2103140b05802c0400c0c1b04c0b010050102c42c0984458603400901c00100d5203283d03005076141078800c12000e08134024000c880c401e468000306203141c0b040160100c0d80007502e2200340300044c1c4400798041d0000c14400b100100da14081c602001c041701040b00c40c01c0b6203030001e00c3ca0b08190200131840310b403c4182c80c00e40e070b4000c07002c8400c52 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 727138417 1250 727137167 727137197
    0x5130c0f03050d0f0806010804051f020d2016022103070b09010b0307090b03030d0203040f0b071e08071110150506040303050a0f030b0a0b0307031406300604050d 71
    0x21084d40100000440140121704a90321400525030414025401ca40010f0300c10060340c511290003207000e080b204d6001400301c0e104249030003490000d0503a0710500403101c040c12419103482c402c400b4180c3c0018080c500c00b004540e2201c44a402e02c41c540305201640420b00090107035250301954003a50310f2248400091226501401100e80e02507010380a0081c19141041d8103001d0130a81c0d900d507034140414081310b003158216101540c46107000300520302d210881820084181c0c20040c208170308000e410302c54509044004c1e840c0c0011500d451a0000f01e540c0c8604040b40c0800c544100315140e0700901c0c90440d12890560007070f03501c511568040443d0b0395034034030410040e88600d03c40240410403e101c0e094880d4060f01001100c80c0640c180850340aa04800180100126810000940c42c002c0b041c03061581e89441842c0304803405a10b21419402c2030030000342180e20701100d0191080720b580f010f5200151803060107810081401c129581420a8070708161501c21180c1804001130358000a0062 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 727139667 1250 727138417 727138427
    0x40e0a0906140138090d062a050a05030c03180a1b06020c031002030414030708120901020304020a031104020c010908040e100e0a020a1b1101030f090b060405130c0f03050d 75
    0x710f205641000c10450b0b00345000e80c0703c5030030041035254419054806100862114081c3c001108e88107200f03800c501c0054296510301a422501c0b03901006024010f040215802c8421a074019108030802d984036994215078072003a021951000900c4e00847c3c0700c500400450710040b24a20b0324038001d50b6102e0703407035220407a030f42c03940307545890341c981d112815000364606c80d640215002030107843ca03010003030000b404007072560703100b10400c4444400001d900760001e040640741d1504103842c10001c1d899030800e40c00184c03103a895404050300c0080003030400541a5203d904440e00b01c00100300038404441141808003060f00701d03106060300f41918100141614010044843c03c0d94010003d454141c0c8506441e0340080d0041101c5005124200a15440a1041d01c500710700c00c0d80306800c9200040b40b600c00040030380e90648a8018041e00702009440014030b8108142d030f11403020740d4001502c0d82d4400002c0c0304442801c0000d814418811800715001901c6132100082e03030300907004c594a00b003141c01c04443d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 727140917 1250 727139667 727139729
    0x60f150611030f040b0a030e2e0b090a0f15090516020a0525050a03050609070f12060908040f0308070c080307030e1011030a030c02010608030906040e0a09061401 71
    0x14030f04104220600c80981c041010780508040e6103000280242c3c0e0011944c684080c0c01d204480c2030906000f800d400742c44002031100701d600c040000340320002410700445d103079610145c01c11071102c0d00e50707143c0e07039109d00700d68000c10076814242d1007106629030700c4d07024400034a0144d451801c0031901004444144e8000500c40075089d6010005240109001c4030034020f038194000c0c0031400e801c0f1400b0000701c0e0b50744c2ea88194003550091002e07107014240441b00c0361821441d680403410364034400350200400703480400304d0200316421140c00b00707040c0c90030314200303c0c01d104079008510050883c007800b105001500000c1d21405100300306000d8019124003e056490045040c0200092110030208915043c004809806480c0303074280003180061092446046401c0300340051b00183e03581000c03050941c1d09001d46001000c9040241d46081607481c0455000d2081d40518400c1081e4440420090842a480100c807250080410032401d21052246808160203104403440b0140e440590b001031901034070008 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 727142167 1250 727140917 727140937
    0xc09011d090111040b0c150c09040c0e0306090705011205010302090c070203011407020f0d11060a0b030304030c03200906092205010f0b1503040b070507060f15061103 73
    0x810403103126169640a400001c2486809548520042282c1446603010304040d00c51802003039182d009100d5241c2c80c000a9003c0c290000c1c656400344950089144103c418114054601180e41d0049090585030806d021040c00e805220709000c109002001040c0801556000d0b0307180c8894000d44900e54058034401c0c000a9030004e115004034a50841da00c0041110301d10140c008242c40403160039201149004507038030340c0035811458004007031201c14440c190009030b1905119071025020b44c9155918278004240d1b401c0c103a07440c060702c0d0300b0741d5040003a180150b5210b0030103060151680b800e00d0f541c6410501c42e41d1400100803840c61309203002140c06100c1c40e0007a1540c14159900200a41c401800702e03140440030042503d40301c0820001e01840c1c1d2040b0600601141d01c070340354014010140420340311070801d0082801801b002640105030f80c0d0b040085c41c503009440340c0a03810024000d201c10200c000c0c0440c80e00801290302440d04003500c3c00c84503181c076650a101e20b04000a43c0328440c51440c4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 727143417 1250 727142167 727142189
    0x6020303013510090b06030304031a04020f120f06060f0d2616021503040b040b1018050601030f1104031704090606080f09072714010909050c0901 64
    0x74940042211803082c0060b0a1422040002c0b003025a40750a041d000405a0100c646403400441800b104802131a00410300394002c620709855900c0311500c03030b2002e00460942284040c049020355854000c039440004c8001c042c3c680100c6ca00c078403141c2c6e07211118040f040a02840c0001812440c0c580341218840d54041d060306103c03001d42e030340c60410b802102c10711080d4207840c0d44211010745042000c0c200b101c182c0028080b400103030703004000003600340c02c060800c020010000c001c00036003281313101a0010f510000c10a1240c440844c1c460b0811003a801c204c6580e40c035451102480000c40d007013980035101c04e807400c00c070000c0707a40059400c2d1070910b170104015900c208400c10004480c902074401c07021010030414200380e00d400301d050a842946e8016400104520140641340354140c500e2608150030300c000f020014500320898294204c2245081801a8610407254410989030094429106c01006603219507031155549801810004410746182c8100d408902d50707424400b200034103842c400091 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 727144667 1250 727143417 727143449
    0xf1b0409030818070801020418050a061a07050703050a12081302031f0204080102070f020a0e0f070f0302161209230f01050c01020412060e0c0a2d0e040b010602030301 73
    0x58039031144220f0b0034400030b900c110203000440101c280b02410280154003e860b0402c1901e0b0184420380e08050140c640d014544030b010441c1019101c0c02003903801502c028a0f8070b6901500f022130616807a64400740c10f50090500107810000000c841d4524100b0540b11007000c0e403a50b68094200301032100b40250141d000c120000f44e04501c2e89030019024100c1600035107050b031903071a05400c2e44c000751403c5a03623040050303014045252004d55440500000490010145005400d2003d41c07003010381403c0a01000d02c54612410380319404640805000b021004c80301d6403185440103010085000407400591000c0e004038840320700d4a032580080c050f40d5054a0301944500c1081904030a0040d03450500070200030786004038000f0b002800040451030904c20308084942031134020b480c584904d00b151500401090040b550301c42e890201500c1500b604008000811b9004644070281443c603034031545014000010341306242c0701c10900c00c520076a960300c4141d85e038207030990340c0b40000e0090261030898503071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 727145917 1250 727144667 727144681
    0x913030c020103020903010e030720061606150902120405010e0a0807060507020703050706030608011109180a061d04120906091404110a0507031e2705030f1b04090308 73
    0x1810017008010000a54061100400762556111b0360084030103074024003400702080b44003c4164442e140698125240c07500e150400b008100c80c0040c000c1100740d4804218800030300e00c14801d000740c40c1c0340e4011540d588440c010401c01140840b0219103660030018074801891003c070f10502c0544d4060145410851035507250005004001d20100444c40740394800000304d48100490401040f441d2000684030381000714060950700c035261101c0d0840400c20141903140c4810042402012102314103103c1e03500c442074a54090280781d40005118100c20180e00e03070482c04503504078081d0744503800d4400c41c0214940113540d030803075501c20507011403a54181007000700254800b0008000d070041001031a40c00060001419401603518000003070b102185000415410074600098446a1681d48004000048006100c68000c08000c100c5031140d50344801050200d00605024001c01415185c8098024904a9032815007400e0100070325202140d03030f00242001c0c8202c01c403458141da5080c0281d03407081 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 727147167 1250 727145917 727145921
    0xb0916051803012c010b030607320f21060f101107030c060e01030524010216090507081e060108090312100614030c09121603060b0913030c020103 64
    0x11900c10b030955210070314890b081d0030f004c10401c00c10380600301183e00010901c2d00d41342151624007103940207511585c1403001203600700041d1188080d0b080c441004250081603080981c503010140c030f001807840450b0503485d05a0301e001501c224107031040700543c505d462004c012010101038a4054000340708180c0510b0381c1c00e0613408502440e415083c114802c90003401c02d43d152440a900680d02030358445402d010030780c0d1206209183c0d14003403034148801d090806a4060300130280740d400c070741201c149030ac4d48050723402417203104c80c1112600c141007902c994489135400903010480303070b0800052441c030015002c401014140c80c2919001c054458103640c8e0140152005100a010b080540c8404c4c408280c014100036403072441900d0340e480c0c1022061074503201920001118401c561700c40c809008102030b07600c0d907406552004070203c40f06103203c3c00e405601400c0040e03000711440810400240403082c480030340c1100100b081c082c4c80d82d00d05c03a60b607108005800c900750140140000d40d03131601540550300c25 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 727148417 1250 727147167 727147207
    0x30506060d2003040605061f2010060f0806090d0903021c120e0102010f0612020f011709011b050415030509010b030703050a0c0504050c0d0507050f0c010b091605 71
    0x606402d51840d49000741000310f8100b03c0d030888005440700100700743c904103001401440030354140e441c4850820200b000e00000985418890300b60320840da104d0301c110080040054481c1401000c1080684600d0002100440340c0201510b510404010502c1f90200140348820403287d55076085585045030f0801c801028621507041551131000c9036103000c5550103c040a00c4000b41c2c0b40c0001000080b80064207403030000010340c006500d0007508010301c1244c1500219030795030440b8151180b00c604401a00c10041c010229500c1030036a00400004140540c8501070003003052041c0305500c8903848049401e0310945c01481d00c0d4a4103441e0104460f8040d402443c1c100400d60000710b40300b04c034800881d00d8540b40c2d62068805521200ca482c0070301030511132581c060704066401b88503d241c0160084400e10031003080c04441681d80002616070751140c000d82c1c0c20601811107803995150501580c3d0301038201e06085070710801d00c5402055000103082c030320310000012516141e042098101703001d40c0c42c08032 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 727149667 1250 727148417 727148441
    0x20303011a090f13022a0d05090d060207030f090509010620011d0705180f010605030903070c03080306040f0606091e0510080907060e0f06090d051219030506060d 71
    0x9070741c540030f60b07a84a00c041d0201382d40b050b03c0142c40d007103845010001041c8240280341c91400d460611600041e0110304041c0218103403c0035940c980982002ca007170007044050180003a407012403940200f55114000800d810740702e60307451445917240c03010480003500078440d070000324a8080001c0340302d0203581414010a0694000006c018020100740c83d403405000011880981041e90184a28900f9502d602401d60401c400c0b0a00e500d044003401c6070185040c0038400c18002c000c40040c04503803003002103e04c1c5691090038030110f03640c0d0345001881508141d03505446641070800013041101706208040450301e450340d6440061349009101c0024140d541c0e10304601c0c04003004041400e4544401000780a041603841244900d40340340c003d030820600e600f025040103003448a10006685600c225528100112011642c51929100003a031510032100020990700561030b04180500028028084041c2400c0542c412140301c034004504954044a010303038099414448100c4502160f03200340b0300010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 727150917 1250 727149667 727149679
    0x601032301080601091107020607081308120403030f2c01050d050f0403020118050307241805060108160b030403090e18012715061e15020303011a09 65
    0x80040241020000b604840215400a00104a20255445a071307115075210074407181080d1f0580d00040b018413642201803c110404030711400501540202d800040c48990300f141c41105c480c4841c3c1c40d56803c47d11040e0b006c039044912038074200340280b991103015011860301c03206100d1020b6101910034000303502e247c1008018480c10381d110f5014800c09014107d495120a22032500c0d150003804e4a01a0201703681d80c000c1601203030300245001087c0e0321880e500480007070320624911612030724030003950700c2d50b500f50f0b042282078000309020018140c001c60003142900e505a0300c40c421550f444c400d1034480d1061080280040000e216801d0286403c0b43c400d1800c40d450990b10f82c81030300b00c05010b84100000e030081060407800c1410910400b001e51001d0a100c10ba181c00200140c403180703044030006418101d0300d181c40c610442c903951001c80640703028507040703803861598034240078518598006c4e4400e9043d02216500c60364000400d0f40e0481300b00d841c498140e1024005121480c2d00b2010f0342d25040b003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 727152167 1250 727150917 727150961
    0xc06120414010e0a0b16020d080c180a092c07121505010e0109050106020114191506030e0f3702090a05041e02010e0d0804050402030903070c080f06060103 68
    0x3c02800010115030141d000c2d17903110700700b858908002c05100f5403010190b41c4058560040d0719046050a980000315035010340c3c4a46491409a00001e1101d274840d07440084940c011491003502c0e840081070036940390103001640c0381610103285515842102e08950383c80300d00b003013064290000c1a03442d00b500c0380101c031491401d094140416140700f80c0060702c0034825100140b241820034403030306006004502c002d0000b254038800c0051190805460100d5220100d55103005400a42c3c0007458030306081406144195500c3c00001c00030415044120054052a4228500b00ca000134411503900710616211100c143c50043e42d600884e105c4100c40c407103503031012050307015a0790740c00403510807440c110300480d0519203441e000e4030942e482c060341c4290200401e0030344003613603000e00314112a2100b55801541c01d0918280040c441c0610b0f80150b50050000003003000c460400301c0a1304400703108480c0211515100c406403600c0b2941c80b1100c0803241e02c070b4000601c0c0c942c400c6e040150204452069500c41c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 727153417 1250 727152167 727152191
    0x15060e1302150d020f120103021207060f0e0102010e1f0b0109050f010e1804121e08040b07030b0a08010c1416022b060603120c0f06200406030e0c0612041401 69
    0xd034000441b1201d0300b81007400100700390b04241a015440d552010045c1000078200840613001003c400c83c08010484513840010301a4001d521083d000c03c025404c0b100300c8a20100010350920709101e1400e0030302d0601800301c1da6540100117030000d0710790060442c91740d0640c3c50011504540d8502100342e001900b0074140401000300f1a1040c0294040c40801066101d9000c4c0640200c044104541c102403e1840207034041c6e9010413000c1d0001d62148a4200c6615085405c0700581021001c06a0107210301c1400520400154480c9120a1041d02e035140c0143c0050010b2106006124a2521005204241e03500500d40705c0507100042e5140c5001c5481034020000000e43c0c04901c15085071203903500c10f414000e1009696003a181c1100d80d01d414100d0400f01d60700c030400003540b00b000400c80d80c0c41e0f550326000c00c502c802c07216010012a4004a4031165555401030141507800000700040c00f802c040e440e62410600c041750700c001c5103101d01a26a40700d55403a0004850051140005550b854036080c0314 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 727154667 1250 727153417 727153447
    0x16032604052b03080f1014010c02030c12072c180a06020307050c0709050c1209070503030f040e0a02070804030209060103141302031e1e070315060e1302150d02 70
    0x2d40e41c080c2e507481000303240181c0c5d0700c01c0c440310203000c1880c507011802003001492070810581d0007840c000c0c6801d0781c4203d0301e80b0109190942c0452400d9020b90003110070072510f04001914000c58281d1010103803114a407a00c2060071a0b220160f141c4444c6004001407025641c00540911090903003080741c0080f1500c0e2a48000c0340c00135149a0002100080c100a0b0081708108200141c800641c00708414108000420200e110360341d105d050304049071000680800c8180a4a40140b01c098180e0355500041400138109900c24007614024401d404080f41c0c48101510980d405076a000e160700b490181550200240440014083c904160300c551038100d1410014421038081c03005080d801400c0d03001ca104050500240c011040000d08841e100041104c40000e0501018801c282c03900314107030f60000b2881d050242682000e800414500020f80d0001000d40c058400c4688140c000c11240d100c07076040021031407288034040e5000007030004070122001303218000d04589840140041ca05214201602c80d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 727155917 1250 727154667 727154749
    0x17042103020324091801060306020c0c100e061e09030708010b04200d05130803040b010f06020303040b04030e0f030712030305280b121603260405 64
    0x25000b01c18002c11016210280c1c2c86840740703644116940c600c503004210b809200a0181908030001000c004c0e2070003083d4408405190407540542d91400c10940241c0d07220599000e881c0100d00f107070b04c0042c0491194165205000004120390301d00050465520f00007403036a000c06030416410043d03040d0070b43d802c00c6450010411480080790080307206007004112089050b5a20401c401e410842d441e801d080303011148411a502c4000a079921210184010003161643c01000301b0000010b11045c41802e00340c1303d0488550003100c0342115103801c1d080342c9901041d5401400740046000ac6000640200c1045404175006018481d5008002c40080d1400d07105074440d106405064070b802c01416850f0003400d0340b00418641035007000b0b40346810501d010b01000780c813400072596810424042d07554003201c40103003510300301151965032030f500c110319480c142403008030f4041c40c0290003491469011a110300c02a10807648241c149850103060004084c400216078400400781940d010018010358500b407 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 727157167 1250 727155917 727155983
    0xc0d2304140f10181401080612010e12030103150c120f1b0305160905010f030203040f020618030c04050727080d050406022b0c021f020c1c031704 64
    0x100030300c1131040c00d4131250721843d0841c102211085082501c1e03643c105100079000a0151403000001d0400d81c46d0500501e41a80d03040064051243e98801d11980a40070b581a81c3c01041c2c0840303a900300072065802c0b0740d401c1020b8004100f03504824861111640d00651090441043c0407a0080a400d01d21196202c070001d668040ba58420902c28502c07610202d0405842c02c0381040d8610601f050000303405002650600f400b02754000000404004071050500c40d2594040c0600d91200c000790b5164191a40860401c4e00a104600c0162505d14050140a006029948070340f180100d521012034802a030500e4805c62685141a001414000c00c1241c24461000c50391070588460810310003d0a1444165210035100e00391409000d011424800b02403c46c07819041010020206202081f0118041c8081400c40e803000000b001e4180c1d000724850000050403110b414032000f1101d10a240403403855009000180c194148242140000b000b2940140c0581203840703107003005410300c035240d6803041151 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 727158273 1106 727157167 727157177
    0x40b06060d14040f060e151906050d060209090c04080d0e01020a022d010504030b0103020d02030f060403020a033507030608030c0d2304140f10 63
    0xc142d600020807841c14910702030078000c5504200c01c00c251150fa0078000c030021044000300e00803181b5113a9070b90740c039800e8031150841c004440c410030080811a9640902280ba51b881100e140701e800e220340000340c0c6d150b0307820041c040114806818454090001e004c2440000b1000c41d520021203807525010703c080c0b81a00040786081c2c0e2501c0065001116000424400803520000e683c1c00105520309036520440003004441c1d5220f1880060302c0703003018100610041c54a041e0003040b59000804076101c5c5c0200d844841c2c100349045e58101d0141e4412600316080542040c04a182c40381d0010b000c01d07805082c2044041d802c141504c1c5110030701d0034000007496841c0694003403030250558a080380e4803251010b0346070b0350710741d001c0c040a8081a01400e82000140355114403a202c0071550012500345450115001a000d910440c4241e02c5940590843c040d80c456040e00c03401c080d1940d0325 = true := by decide +kernel

theorem cover : BRFrame.Cov 726978417 727158273 := by
  have h0 := BRFrame.cov_init 726978417
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 726978417 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 726978417 ≤ n) (h2 : n < 727158273) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
