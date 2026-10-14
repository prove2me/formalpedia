-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0478
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:01:06.273422+00:00
-- url     : https://prove2.me/submissions/9fe449be-db60-4100-82a9-8c9370a209d0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 85791368 ≤ n < 85971224 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 85792618 1250 85791368 85791413
    0xe0a0b160206130807020a05040510050a06050a02100207030c08072f0310050a0612081206030303130311070e07080f0903040807060c1511040303030e0106060c020f030f07120507050409030206060607 87
    0x80c0b103084bd86850240098400031100490100d03241c440460305400341020041c010380c44030018290034401a0300410390a03002c0d190020a9003a251100c500030750040b0f008a460008410b100c0d0407503900a00c04e494014414034030024400e0758140001c1d40c1e020740c3d0f005406c2940d44c54010038071411242c0d0025004101a50241202407a1400d0980f0741e03030000a01c0c161298507050000b1240d02c3c022040740d1007681180c40c2100c80710740c0d07600c0840740001c5c1d19000c80e400784107040c3c02280c1700304a90005e034401c4001e9654a1418503001d20f1440c07a80c44090b002000302d610030b00c800d000d0200d02298810584e2400d2030000003c1599040c40b941c2d01101e400888102454089140240c040344001801501d0080d2818044030000c548c2c5113003200c126215240001e000d04180e4001440c01001401c641c41000f4100d501035100014682d0801e5115031044035901c4c518841d4004028091240794002c12003180c2c100009100c0e602d003c0d44481009011911614000032500c007006610075514194805c508003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 85793868 1250 85792618 85792621
    0x60c0c0406150e04060302151c021903140115050f090a1d0f0105030a030503090f070e01050f040504050c10020f0111030103030e03030703210e0a0b160206130807020a050405 76
    0x712508500c000b640d10380c000507000c0480d111941024015001102e5015141000c50f41c04074844030000d0300951a0f0088101e03403030600031060111030002e440032400a40c0c0050b41428018005400c0b43c1d581d50686005410741e500401c4180c030351607c03007900c000c40c6040403981c0e07841d207070745001f8984145690f46d68050040c2d600419107810360f0020240c550314015080400d6100d4110130b89407000e003403040320f506501000b95100000d1107440070315000f202e40f10407202c0061104a526090408a0b007040041203464801082545004592114200d40036a03080000c0d061513198251940c07400c00411380034148180c0c1e502c09847c42045030340c2c0840803020003003115007800140050306500a201c1500051314030980305440386400b0046a6001c0c0d8141c6039017003038109002040c450003074800c840c41d203401c0da51000c912419074244111810b182c451494440c40d0300d0704140107008504040e0409046512001c1000036007544180c024000c140c1003d6159156006880064801021600078a400908050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 85795118 1250 85793868 85793879
    0x3020a02120403060504050d0504081b06040e040b04050d0c02010801030b06180c120a0606020d030b0a170a0b090606011b150204080105060f04020307020d031503020a0e07020f0105060f060c0c0406 86
    0x18002c5001d07901c80c0023030312100c0c03460100482d0280254003030f110842d00f0550700040600740d400b000218040025006504099542907124201c0104490541d4a05e2030701e0108410844248885045070145040024031079940d074000030421181400024000c41d00c0310702042440d0740303440360316a00712240e184100480c03400c480350034840e42069100340d60505503040420704103c200e001d200107684181d40140b0100701d52110171405800007844141c0c1000f040d40010a400781c00303006c01c4204042100043c0b510341c5442c5064840390400500180086d01302c0030138418141e81c0301d440140300103041c6140e6001c2039124201401c01180b40c0c40200c910074800900000c85685c190895032062500700e032440110035041c0d0500c0180d1004a42c0540160444412114140e000e40d000c0c05150003c01c1c2405400398899004c201001c5c1c4a030045080b502c1c402d01040304d2981d042245104c1e80d0441c000a00c000c0c2440d801088481020803401d80c8102808103c80e05540d030308210f48901044010424400190b480c1e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 85796368 1250 85795118 85795121
    0xb0a090b04050a030f1704081c0e010c020c090f010b0c191a06010f020d030e07090203070302030615090307050d02030c0301060303090501030e06190209010c062d0b1003020a0212040306 81
    0xd002213001c108130422400310b05002d00f41c80c4000b120500022101c0390ba071036072010220380c000d140c40b90702c01030000c0d81700401c815144201c8070030300401000010328080400d0082d01e80500740c40d0081c41441100c080040200d4400e40d51811a0210b1604540751042c140500d42001c0c0074200c0c400e40120015012018440c04248018800460511218a40c0c0312240112a0b80d05000d403080090f9122084d02c4580c0c5103c3d07882207154044017019a5015030b1180094002c0c1d80c4240c0b1904002a0040240941c5280044d242c40031440c1e2070404078a03159812002c00d403100064410103206409819111040d91014031205000640040007000041d03160310340070305400d0750303806158000f038034000b400149000002004c034003450031940d5400d203403c41041030001a500c0080240c0c1000048000f020019400307015080b80c54844029420440c0b14040d01c03a000105200d0a0a4a86003000c041e080d081d02c954072801160042c40ca405a0b481c40d481c84d0603850007502040901101d04000303400024407005 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 85797618 1250 85796368 85796383
    0xd051e07050d1103070b0105010e0a0302030a05060603070609030312020901050d0527150c030c0708131d130b0402030309030f0c0a0504050f010b070606050402031e010b03130b0a090b0405 82
    0x551511000b04800d00f4103242c0e41e0082100003495801c03c1e8005100039802032800d1070391144014000c00400d920396000ca814000145822100c41c0e11601c10b00030b02d8581030180d0800381500745844c50119207551002800e041204070040c4601d540010790003002e9210320120780711101c00301d00c144518205450400000f107150300d41485030845002084c0c002c40008541070074058103c0d040c00c00c4540f6840c803c65115031001d00b00001481c000c000304800610307030340c02031725000e1200c204280d42c41380f030030000443c1c40c03442520207d0415034440070010340d490036201c01c00f081c540280c240c05403a60f0f0352000c0780c598800c03200100d40c1442420000c810154000440da5800311040e07c94841c000da44070b0501003074070401d0711210310103840b440041c040702c0e0200303015256450044d200481d2407030340c80b0041030817640281c40e500315441000c030740321450641e012151070041914894180c81c52400c54400e502807246a04003c0c561070b00d5102181d0010245d400611179642c11603c4007030903080c149000c86d036440c1b4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 85798868 1250 85797618 85797643
    0x7021c0308010b0f1e0d09030809070602030715050402030c0a0b0703030e03040803030106110a0b0c0301052e0f0306030b0f06090108060903030a0c020f0f0115090e0d051e0705 77
    0x1401d001143d5042203030f00381c0710104564400e90341001740f42c6507010100303090040e5900d0300d00b800340002d4481428a01440c840300d4040e8440407240e06005100604024158101030107541c010041800014505145404100801c0000280700c0d2240d200203820b040b41c040c080c030f90001240b6000300e0400303500700c01810710600c01c0d1010001082810f001070b8490069204403500d942041c4010406103000f149248100300741c40b41a01d0705a152541e41b105000d006440f205640007000c0014003c500305110b03090849440f101d1026046200424480b20742d4105440c500c0410800c07261080e500d6010780c000c58040c0d50b0044842d40785242824284440e01c01c100c80c0740b4070a0300c00170000241c022002c641140640841c201031482e55482d8079840c03008c0e14401001404500c00c1541d210041401403002c00b6081e1460000414040408003055100704030f141c0120403090300c0c201050108240000780707000a41081d00f003003038441d20392070b810107180300142e030480d444500006901420441c020498044204 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 85800118 1250 85798868 85798877
    0x60908070203012a1106010501030506011214010e060108160e01170a0f0b1504060302130e0a0524030309100306050a03060c1205060121021e040305060105010509090c090607021c03 79
    0x20300007581212000329076175410f032913500720034014040740d4441d41003180e001c0740604000340700641401d0a6011a0203690481c0f8007061003000510205102c8804190046001d18041303c0303508140d503417035800b110300280e007109110a518000020b079009044200c0c1451962141e008146010003401d0041c11607221040c0d000b0f450806845c80300d10348094480103550611001e5801c09040080a4009620014100c0e102110039500000c004030754440c160b20403520500040303250304000c00701403204944044564400789900040c210030751000420f484825004660004010310041801d40050001d50002034010000b004003009200280d00710540c04241566207081b21080c04620b2012120195540b50000f1915694000c507500c8108032800c03400300946d40140303041c2404084810546202e0846544982c01140030424007006001050042c9001c1c00e04501d4451700400264031100002d000c001880c0003c101400662100d03802d0750552035029110913000c800307281c0c00610304442d12398105d0018 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 85801368 1250 85800118 85800191
    0x60405060a061508060a0e091005090705030c011b0c06020a05060f060109030204092103150506030702151e180105240402070501150308090109060503040201050706090807020301 78
    0x803103940c402d440807a60b01c04000080308246a5080310039600180980d0361001800b83c007c2011541885120302905503c030080c083ca5040d03054010541e04010801d10b81a0066403082155450201d90402000001d10f807140d091000c06a001260368400100038206a40b458408140b0640029030219014001c104851140d601d885400301c0c500011113401e400150240c90400040c106a044020b28602c201e074400e4150111205208007855034600d00c5000a8841860b146014006030300c0030050801615120315600d8000c01c081e5480c9044101605d108106100203000480301c1124107051040c0c2240300d08070b42c2407078101c9001c0d440d04910000c0e042d518010205881c00340707020800029009001241d50004101410071000f500503080c103a606548560203000c0c40302c0e100020034069071258404035102d0b0340321000100009800e0f001102402001c005000150780c001d029a00055803000001c00c02c400c0070300d0030360030301d02030b07040002d4056003800404602ca45241010882e5503206030113140c4078 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 85802618 1250 85801368 85801381
    0x302010206090304050d030c05011b050901032714031303030203090406090510030308101a0705011808070213020702100306050906010f050d150b0a090302030c180622090506040506 79
    0x7a48500d2150950141b07aa014507000240a900080052400b5800004103241c0b52005a4001100726440e031001400c0002c070030f0751568043c4505152040080d50b101910708800c00c1c8400c04008020010b400c11010f0400400b43d0001002118507880010200c3daa48980e40d1502954076008508818412800c1600100b140c003030b2449114411a250140c8000d11880c58406441e609005401a07406942481d00815500a0603107010300e580380c071480b029503520043c10a6403c560760f01c0002204071200072807d00100703444a09035000190100c0b01140f40d004150000c0c4020f20640d44001e40005030002d411004c0390f01070b40040121003060f20100303481e5860300011105000a140d0300c038045501070000b140da00b00f999001c1d100e0008040500a099500d03403d40c4903c98101024160008866030b405004604052009000385401500c1d030710b01e070445840f100d003c5000000d1440b8000d68568110050089180280340c0031050307464030800240c0e615040c00d0303031034a47c12a0b05584a103d48008240b9 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 85803868 1250 85802618 85802623
    0xc140a0e06060a0e030c04151a0405012015070302130503010216110414090a061b050a05030702010b061305091302030d0807020c0301110a0e0a05010509040207081c0501030201020609 80
    0x129000050046107043c1104206440d0380d04844d82107038052041c41140390440d222441402c02c5039491a50900e030b00c610705800403185194180703405d10001c905202c1003102d640c00140b1800d50742503a0004248481c0c1e9061010f160092418020380342c0c400400078000081d07050341c0100880c0700c8180640880c82c2d04c0c0c40500d8213074450745080d451102c00c0c100c14540450b080e40054031803c030000744007240f519080d4425040c1200305480e07503525a0001260002040b40f203200c1d055038903000a4915030614224980035080c0d000780c1d88040280400000001da485100394031204c0850801048603450302e001c6281c55210226500405000d0000d96010421000d0208042e550f80c540c01001881880e246c2c0b0f1089508480142c401d00c1944038001013480651380038000c0d01d0310740d041000b1294855046540040c882e4201404142c042c240c100424402a40c1c000304036081301c3d5041d100035942e6000e0f85011851449190540394400b00703082d400019040d180e0f00624100c074000d0b403ca405603122241c0054 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 85805118 1250 85803868 85803871
    0x3050106111b15130b12100e0105010809031603110f0304051c0c080d02010906140603060f0601090b0c0a0309050a0e0a11091008060a0b0a0e0402160c140a0e 69
    0x2006060103440050071481d041203e1000380603007010107402c09021540009410544e50014844158041500f499a410103515154003903100481e40100300e1600c0803558012006000d203030304124585002403100c1c0f108004444420486800407800c84000b402c00418801213041e0180700f0b402840d11a410240c0c000095405840b001801a5201c140700381c0008544610038504840c0c81c4803000c00084c0380c0c241885060141c100b00d40001c00c0303100040c40c010007100d0442401480300b031610301c00d020054800195495100b03030340400e080010748a901c0140d4000080d80d0112840b60000204580705000108849079414466110b40100c43d46810402086107a0390058940e00342ca5840028a0000b442d000000d9580b21030401ea4940320b90140441d0214000b98440c001042801050003080d080c41d03001c841c01800c07083e80903800d001d010744005103120340c80700a084c403594003c40c0316200f144442d00805881a40180d4059a09640d0704c00500d1114561462500c6401000000100d0400c01f51465 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 85806368 1250 85805118 85805143
    0x302030d0e03120c1009110303030403080a18030c02010822050307061503080703030c21020c06071b1113050103240204030807021e1e030f0313050907020f07060305010611 75
    0x117000c1058041000720007840480781c10368401007480d5807030289407000d01c01140501d0182c1e4807071440b85403151076101607524603803070300c1213800595540c4c4021a5001049406490342407a0109a41d2218041c140030031158184019550050301a280204000080100301c144e2040c1028468211051400340c2c80038068800504403070030800105000910a07442081c3d0b0405a080548100582c00600380c024849480c800c07170701503800540721055090410030203902801d0340c83c02500321094952500140c0684060007031036040d946240c17045030743d19045401414403501408000e43c3da9070b41400c0c1c4e0304c00c510769492055050244400c100845c154000c0f82c0c00e40340c110001c2803030607020341d003880034800c503406000303040000090101000b0750b07612a011000b038000030b81c1011044c1c2000b0425042c0a06032480c4001c5920401910f40c3e80d151070303080442220022201010196540502a07040c80000c44481905026900f008a03089405071b010358143e8105030307035201140002c100c520340d03289680c4a00707 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 85807618 1250 85806368 85806373
    0x50d0203031902120706060e06040c12091401051e0907030305040e0903070213020406030609150909051603050109030e04150e060301090c0305070501110d05030109050a060302030d0e03120c 83
    0x111500c82c840d0300e4269940c4200e00c1203c50189240c148689280c20000d003c82e1700a40b181400c114035a501809660040c0d02100c04106e880d80314913004d4903858540e4030a0400d0768980400b00140b0004884000c16030351024024045840c260020165061605000104000b101c4000c506c0c0410001065810390303925454140c0341c94140b000860143c08010009145488100704200040c1c8611003441c0e042c4500e8507016841c0c50419401038165401504202e00162511252100614109032404219484541d001644404070305000b07040c012460500b03513044030140800002c10605511203c01c1900a5441509100403481040f05503541c440d25030355215120441805090482181c0c00d41004c8020000580102c9130b5503034001c010b405900940d51504240c408006d03070b503040b58001801c0e007030010140550858440003c1c01c2030106020b40d00e0320590711000602d4204855004030040c40d0000c045a8403103131200001841e07101e82f00e440f28002c0c081d04900b2031080d1703180d0081d540c0f410f00c01c802 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 85808868 1250 85807618 85807627
    0x141317120402060d24080705040c0e0609040b091810050c03072a0305042309010b07020109030611090111010e0a080904062112020303010f0618030507060f09050d020303 74
    0x801000350064100c580030180e41e480d2110a4117815902041034801440c05005000d151103241420207050303a009038055420918500503256110450210b003540440325540c1b600d441001140040100d402c29503000324140c400c1c4205041007a0420b484d0305030010031a450034214007400400d4640c04d44000f01815018001b1601c180e020b01113035001c070418600001803d151114216614850f04034003580410b10000b01400350685500d5100c10085d401440300020071113001c00301d202140144195084901c0c0482c1003001c580c8901d1901c0c00031038201005001c50461304404a185038048903455000c1045a9450742d550305043c0541d07061418102c011b07000d1541280c0b1030203020760000f031201b51f0040e9104800b068480c416900000074018421032012196500d00e0100c40c0c00c8071443d2040103560052004001304040306958500b03031040c0b407401520000d1082c0c59402003603081d8000400e40d01680da00030600300e6000f56212142c40156441a1110760785806106004c2000e1802a4141d0020803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 85810118 1250 85808868 85808873
    0x30606090c050f0a020f060c0c070f0b0406050d200c150402100c080702090a09030206010909080315040f06030b100906080a060b1c12031b0f11011413171204 69
    0x4020b0018040305005039050422094046c40c142a011204220030000215860007412010020b0704080c1003030a070700340c030340d5820108d0303104d00ca00451140030104500028081e002c3e031803e400c03203000b400b44218200c0b45860300b40c4894402da046030300d100466101d60b140602000385c06101084c000d50300580070803810221180125800041c02e8002d0b00c10950070024000180c0f100d00702c00c2d2041e00c4450002816180c180790090803d00186c4c480c4c80607904010303598000c41c00c880e0840c1c4c1c1040040c030543c0403060b10100420058041c00c01c00604a510340440001031001c0c11302200d104640070080c541200d61078084180c11181d0501801003658803185140d00050f4082c0d105810040c5e00038001d10001c071340c0302c0c2502d0f03803042c0016040750407800580050f00403d8160089481d07110748182c00c0b907082540c03203000600c1001031083c04400c1040d65448140c41072803e5020f4090951040e50086440c0f0f0440760b80d003c0c00c140c2480c200da41c90050b4074224250b444100c280c0f1081c1070703040b200c08000d80312034 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 85811368 1250 85810118 85810147
    0x6031b170709120c061b03080a1505060c160602010207050619020c120d0506040b01170606040b1611010311030106030203060310021c06081207060e120310030606090c05 74
    0x52100c002d0003103902012815245002c007241c2d0749849a00340440c01e6080c441d00401d001950786607071240e000101e200e040000d070001e03403496115591f4000000c1080301c0f0b94941e800011aa8000d81c1c20000000307a1742c0364441c0101d800700c800412401886d88160391541304900302d01c501d94018000750000c0300460b4600020b0002001c0180791403e0160034000f2002c2c00078100030a401541015020002e21039140c041980034981d03014100f12410446407501d00000391819050199181900f02c503000040d48a079560000d403805420501502a00c800003e415441c14807106141594180c001c00784060956200340500c580e100c2003000c10030700350b0b4607002c07040d8060342000e41559810300403401960024845c0f88094890200d0030f40e07125005810482d860300488206801644050f0800c1d050140303501c00240480300c140b41e01041c00a0a11481d50840d4213018044078a4410400000180581010741c1c2000c0420f5a0040c01e04000984c3c0d40c60f40030040b1850194510f0225100344419140240b00 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 85812618 1250 85811368 85811371
    0x303060102030f130b12040b060d0b0402060904090c0f030308090a1e060902030a080d0b041512050109020301060f15020601240e1305091005090c04020915030a02030106031b17 77
    0x107a09500f650b5038481708801d4283c0c0081d0000008400f0400c1048244852086c40940004090303981c04001203180d20b84508000b0300400c00380c0502c1c400502c4100ca40c44681c00402e010380c00c003000c1100b0356110b41c0c080c064100300c3d100a0f800a6518400700c3d45542001c12012680d65110304460000341890891024036049618103403401c99441c560000541c40901c0000e220600c20301d41141d5800c1c0a001000449041c810b10a00607440c020f41e00c5000e02d0100074401c20368014407044d0442001500d041c0d0702510282900a405508122000030586600902103080e5040e4206011169422180417642c0d03001c248078201032a9030450010302100f9091041000300c0c866413405141c810700d1440420303080c44000001900d500e90724000c110410301d00b030002030f14100c612001403089080021103141d94006010509111359070019150071140e0f101c0302c02686240c1c19102a5407680b90000c4448000c0d00309110f0040440d04001102807040030880c81151601d00319240c1f016111a00b1500d5201c5140 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 85813868 1250 85812618 85812637
    0x1020c0105030903120402061c06090c030e0a060f0207060207060204050103114f03140318060c0c10020a020103050a090339050318010228020f100f0e01020303060102030f 75
    0x9c04c9002005180301c4200000f44041a038013203003081c07038807001204981070b084074034041500e082900d500c0c80d000484c40f000701542043c070200c0d00d0192031640400034030411310300a150034400182241000500e40240c400c0f110240c130204071229880c2c0684460f4801c000c2c24a181c2d61039a0752440c10010941407910019017021080d1401a1803491500b82000031030510801d036117108032040003000043c840048080e121200903504150041d001411040300741c001c43c0e4443c20003c5100c9d401c8200801002100150043c081c3d1a01c504211001e512805a08030503400281013000261212080e4010031081648c903941344070503202c0b07a420300c55841640c0880e024182100081680301d00240c096924400b501500c040c42d50340c030800c203000d040c10114981150664003c00d081e81103042403010005101c011070b000b0300e1520340e101d10004000208000e000395020103a2041801e400380d1100001150918a81301c44100080d03131070042e60349010898102e40140c0c410040040d94590341d5016051428 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 85815118 1250 85813868 85813879
    0x303010e070c201201060b0f0c0c0301180303050a020708030f07031526190f17040b0408010b0301050f070f110307050d0f03022104050309090406060501020c0105030903120402 77
    0x2c00c5965070352101d8010822440c94145035071080c0c1c0701403504c80c60400101505500801c0502d1400302218454003035440540e640c0708000c90070003e0f4400601c107000007810024002c012210114802c14100044080240d00080c505800901c030034000d442140c40861300902c0b4541180e503903810422003071200030040c004154681482d262114030035640c400150a07080d0100c840d10404443c2000078001c504810601988004140900c074052068000d02d141d4218074074500400160601034001ca01180161902ca44009800506000400050720507240540c009004550340541014280e48003902d01c483c0500300c00c4046100c06008408808041c2040d0410030440204000300c1c50550b006042c003540c1d190042014402203560200c101c131000305007030608504200c2c620801c40369401811446001c62030001011409006040081d1160705d42d0050030b03188103160510701344001e49814880c560161044122000b000d41c01002600d00c5810341500643c180300150480c441e00e9240604242c0c0c120 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 85816368 1250 85815118 85815137
    0x60603060d0f0309050f04090b01170319053708090f0a0f030905030d020d05071103060a0b0411040302151e030403080906010e040807150609060602060603070b0306030303010e07 78
    0x41c124907025200b03c0c0030341c41e43c8907000d1401c0c09100805c040104134511881c60020342e50300054140a416040d103600c3c108031510041c0310151280303188140000902c0784600348106078410340c0c0c080014008408a4462000c465605c42c01c2c1340b00303103008642100d6480c0031044e000e040b80d81c860000300d5800009602201d44400340c1e89002e0b410a00700c1201a40d01d448840b0314034080c103821080400090030240c00600100013424002501c602600140508100001410358184040700e072100001d543c0041c241e841c14140084150000d000c0c1035000740c0605d003010710004040e021081601d0407a40c000c0c041228014030180c011030590f20911200d22018016411030b0000d0150501940c4500c0c4070303440d00310701d50424140f41860001305038072000c0000e4101e41000000740340d960944000f01da2108404601003206009040500701c0307600301c1000907103064400900b860f80021036038012a0f080d0240d6228944802403a42c140c4800c642c2c240c1c0541c410001000048a0300c1030711a8404102d29101c090b4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 85817618 1250 85816368 85816373
    0x40e060f040201140703030f0e070605040314070f0e06030601080d0903110310051e090c01050d05070908060a0f0b030c0a030201051c0603080304050f3705010c090602070f0806060603060d 82
    0x20b60040d14040d00020307a00c07043c100700c08523944100a4101e0541c40142115890018000e14501c903074040100161002c0c4144002c8000401140020b03002550084070441d03211030617005412012602d03940b180c405c05000064502010804100700210b0740e03142e03100c0740d0071902c0700d800c29448241aa41c1505c54040409060b14a0b441100c0c01000500d6015001c400d0f0340f00b000f810b5480103090002507400505004029a0f0044100c03140110070620104960391a000c0030f903854501903100c202c00f070080008000b41000c4940c00300c0d00c01d0011450400139503c250003450380d02c0000c412200d4000184e03c02c28400366000b0409001a15440b4440c0c01030045481d80d114113031499a40200d81403903020041c441001b0041c084003040f10b02d500d004052080e40b000003401c1c2040c04480740c0d207441c04070702000c0e21040364505400740210341020003070042d558110340042c80030307016106200040c00340c6c81000c907120041140c1182190391001c01080c15441d81001c000740c59201411181e4402c8042140400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 85818868 1250 85817618 85817657
    0x10b0912060c070203120a09140607120e031b0f0118080f0706090503060f06091b210606120a1a10030606140405062502120a03020c040e060f040201 65
    0x881d42c0240350003600c50400e841032602c6c02900d200d030080c006106001100140354041100d008468400390440021004140810350303038030440e00003500900080044110230341d08004040f800100a40444001c031000c01c068089030300c0d614021036840098140f02c2c01c11503100d82140f0f4440e00d034410803240c0103a44e6010072803601ca41c00b440c112658022000030840302c0e8128106800404040d00a8a050721f401400c601080f6402028540310b1001c54011811260381120021480307111828030585d218180000090b40c20800c403001e690818020300003400038140310702951001d2046800984d0561100790190740a400103441d0040a49800c120008166666012980341007030307507840010380329051030802084c11300305c0340b0221143c1c0c0d41000700300501d0711418100c45500d00c056030402c1a485401031750000c01544100069400074950150302d800e603001241c02e20400348603401f112603124070201400107940f009031120f00150012000981c12039004845107510520501d41200000304140c40c014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 85820118 1250 85818868 85818871
    0xa05040b0301230601201e07080106030305030f0603030703141e040905040b0105100c02010e060d06032405060a0e040f050d120f060b0304030f0507171903060806010b091206 76
    0x1480301503c9401e220295801455000d880c9000417046020389041d00c02466588101117100e04c02c1000c0140500c403040014000b80001e007407000004d005c0c05507a82030003029600705690301480300101401242480ca8000708503a44613501d03840740003107800c0c07441d00c5c0242500301c01000c85105007214298a4440c01900040000e40301840c8009079505150504043d600c0d8140c0095008220f03007400d5100d9079800c800324401050303092a0000405a01c02d021a03140d0061207900450f4504020001c010082101c95640c0d031103510440010b50412400d100c00c0c1a0349054440700c0c0c00c042c4007a402c0c88000c514561590303102d070182c03e00c1000903007550748203440d11444141200008061a085050b5405140541d420070405018240015400c00203156414400604028213000a1034a07031003189015405940403d40c00509012181c406201940060b03448050244402600340403e1300c034240c0070380308001c2036503501070003800310703a080c4407000055500409d8450f6000070516203032800c1032820426035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 85821368 1250 85820118 85820171
    0x1103030a050c0c01030506130f0f090c061701050a1203110d030509070605070503040b0a090f060509040b0603160f02120c0d0f05030910090f140c09090a020a05040b0301 74
    0x60381d854000b10880c50078403500031150740c1014244002c0c040942e80340c1d0301c40079401800200000c0c05030054a62036009001c1002c46008c844d040c40340700c00034800072442540858403161151444c040c406a04c28009590900071254002c403040c509001d00c000b4504c0400074140300e070174411032040c01e203076503d4500f807100c6042000286e210030403c0030003001072041000528070b5081160030403059030341e11522401107000d40d0280c20008254080300c24803030121003000f0071004400c22500340e12008010010351154011078003c1e0b080c0414003100c1d0074101c6c1228070414107040b0002003805c803d013084589000b40c4600c0da0443c480d4800e42c00000000388002e00300304c00d948005104240c46400c0140000380542071b41c00070b00a0a06c02c00640d4000800d1150a9400704000054090880d140c1a02c00703440104024140d0810500c180c009980001060a61014110f41d2000340e0351354884a150303200c4004900a401c41d003c00ca0400860030103030454540d8600c010004180c0074143c18884a11403c0003511 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 85822618 1250 85821368 85821377
    0x3090b03100f1712030a09081b010605060c03070f02060f0c030304021201020c0d03050403051201060f02010501091e0207111801060315050907230408010e010605030102030708040b041103030a 84
    0x802069503500403500c001d08100034408410843c030354805469100300c010240c80e003100000081c0c08191940e12052541d507020a405443e80b124044c0700b8001c004d080201da000e50300e8106c0100b01480c0c0039003901c03000208030000714901103940d640c0b060200721052040740c2104091100d0414400c1070780c09050b03c41030f40c0000315164905401040b02c00c0e10603402400169104110a4800c58000f151841c0052070a08021441c0e0310385290071503040c07094881c503800000c408000840d045610840921040c03040c1e0b4000e1100e642c03109a1030741110070341600000b00c20190500c5030100410394015000305400703041103034661654100070802040b00d48040c4442144d000d80140039240c2c16104486101e182540810021410840816201000070300b40300180b000301103c1742c5445040c1801075004001000b185501c032035890354120b000e0207030190391036110350030a10017040ca820140300350b91151005640c2d10020b40c03519211988000400350044d100400100d02120458408200509000040e580d8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 85823868 1250 85822618 85822651
    0x302071a040b16090305010c080402040e06070503070e1f020f190b07080604091a190e0d08090708150708012702030702010209030106121b150c03090b03 67
    0xe203190956000044048044a11414000410420b00000341d00c00b20036241c0c1003811141650559405103280e2000b4000d60034200302002440d4441007003802a44292402d00004030194280c54860100f160050300003001030000652680c8103000380c10500307001408809211181d000e1340413914071a0346200015901c160300514200004219040c00c01704100d403402c90301c1d03405540c0c0000d80003000e0320020400c01c110000c681507641d2944031560070740e4410b40005504034242040718a02c4001c8500281c0016010000044c03a09a4000c1c0ba149090540181840005451003512202c0001c1c1a0300c0203403046c0324003c984004200f00c48401120407078810519480d103201d0082c001003050b0455008107080514a84030140002c0c070014615040c00b00c00360300ea5440441c100e00a00408c10101d60541c204040055100e0a540c034400b403040c0030300c1c404004070343c2608079040d000c001c0d4810300305031b89405150350b150380f481034040c101011301c2840c09412080d0b6a03080b850240d0415541501d02c00039014 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 85825118 1250 85823868 85823873
    0x4090b0108150603030406020d0e040204050409050d1b110405040305040512210c0607032012040b06060c07031401060f0605030a06090b0609040b03031603020609070e040f02010f1101020307030207 86
    0x40300590b00c0300f0101c009602c0c1c1410a00000d44a000c503584200501c01c031142da6402e1aa1290182c40c06030070058000c000301c0e103041c1011595a6014140c1c82e011421081d10703001406940c940d801308058000d803220480b0b221500902c00102030051041d01004024400400d0035038a038050513582010550041c120f81c0c2c07071070740c20828145030803c00b4000140200080e12401e000890030700d5101055003800180000c2e101d503009aa0107074080501409400010550301d030311001001c06018900906412610f56195014803016110760742d002c0140d507001c0c01042000031041111511030402503030000c100907641c1d20080100308040e4122001040d40402017205070700c628800c09004144041c414400d561060012403100d10070040181e0040e521a030340958075460030812114100c0700d00c0e0110b0041d0b480c03400c00039241e00041e07400004034003600303000040c03414010302c409000b030740c00c102c100f880d080310340d8010340f145001b82a41c0024050f22180914003142e080c800346214a0943d203004da80e070000c1c0d1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 85826368 1250 85825118 85825153
    0x30f0a0c060f0c11040f0f06061202030606030f070e030304030b040b0a06030c050402160506010906050109290309010b0405040b0106020f070b0f07031107030602040302040e0a02030c040b04090b0108 87
    0x6030441c00812688220084016910511940d011074022a000d0100800200801c001c0c0002c00c480004444c01d0001d4000710300201d62100c0f007110000e81e190030b00440e220007501d090784801d9030b226510143c18404240c210303152400d07840d00302c40c10342003d600c680380d00c501107811a0440d40c016581c0d005201e04100604c8800032205521031440001000138034190341c0c590703500300003d008041c056a404111064500c0d642c070310a00c1d07219000740c1140c1c0c2d150b070340d182c10101030300e00f83c05490f001a09213a000212883c004110700070b15030035405000c072400000e080b45411500000c280c0e20140d902ca44010480d0b071240d1140c01e01a90082481c6900c035810801c0c080d18018030a60f8968081d40003610800c105080181610400e21805202075a10300d001e08007281c0142e01c0140b401c5075401441400010006294000c00c101c901c00e070340030700c00407030900e20050301c07840071410194058000c000c5044440c5015400351283c141d00901c0000c1c560156218485442c03426080707408139602001c200d42a03021034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 85827618 1250 85826368 85826393
    0x50c040302041103090a061d0105190e030a0507080a140c0f010c0c03020714010216080a1704050315091603030203090a140604030b071403090a02010906020d14070f02030f0a 76
    0x31203c42d03440d6013000250b15603142d9609802403e040c2e81c0360002040360341a80015030f10f2a00300c00080c08a400e14940d500011340d200b00002d1005403408180e45035880c801301c1070f07d0301166907894036801c0004035100c40703100f40e00c00a1406e0800c60403e100c2501c0c42c3c071320340183c40f00d045510001c4c0f0308502c0c040049400c58141c0030b8103400380a00d5001140010b580011182d050314850b45555907801c000e000140d18018031040324002080b08400301040d0f4190001d003a66003a80141d005080146182028003c948124012a90180c001c207507400e500402009006402141e080115401502d840c40400d20010b034503001100140c000080c0307600d0398070b03007903030201c002c0c1840c0240340300d10004038400145c40d4480c038813005001c4c03a500400500130300d004501c2c00010800c0c80552582d82e01e0119005900d511080c98200d0100c1d03003c00000c1352140c4006030301c06040740b06071121141c180000f40341d10510340001804850003c100006040181c80a0000101c04c4d4800310040c568800685031210300f1484 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 85828868 1250 85827618 85827641
    0xa05060d0c030c11121c2a08070e0904031e170f09030a0c0828080711120d110406090e090109050a06020d09020a06051c02030c0a050319050c04030204 66
    0x1450640c03030000140460200280c42d082144181e035103421b00203a1040599018000640c60300c1c26103044940d50060540840118000c000304a2003285114145c40e40d000030b407000710000351320716080c1c0d2940c100300d50030b650450300900f4408141c6219202405401c0120000800002d072081003c1d00c2451880d01c515030000c801d1030f504103030780c030300080c28039070f24010200d4000070051201c0092041c00324a408541d20b5203181203100c40070340312500d05450b40c03412001c400c0c0009010031001941403449886444648500a8007800810406c0c0c0251252500944091480d640d5a02c010300c113000a04401030000740b001d91204802c0f680382c00810f05441d0301c0105212442c0e418a00c030140043d0010410340001c9500c5600161100b80481e1820020b00040340f00079084082141c02080103500403001c0c11110240340806c10000c145607007880182c0c003042d104186103074802d0162040c1140984040c55000c16521942803020300042982c0054910a80e070b0018000c60001d414410360400d8000c50382c1040 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 85830118 1250 85828868 85828877
    0x12060c1b070312031d0303010311100c050a020f030102040e01241106060904060b1e030c0312030103020603041106030408131421010f020703020c1f020d030b0a05060d0c030c 76
    0x52543d00c0c3d089507a00545075500c2096568165060180c0014102c2c1d40d02440000440352250307101c0c0340030700300c00000318281c40c46550003025000e01e0b80e2183d041c400006600030050302141c0c186600340080c8900300d40714980e05540921000c5001049410074500800703144000d50310055031800f881404a011200400402c581144030074070b40a800925180c000005032054055076540f405c1c884002d1110b50701d580d034040ca01c05800d0145840c540c1c4c0c120240740c1c04038244c1e800c00b00f448040643d24041c8002c0401d405006200403c00362408201442d4024007840300071400c1010300d00002d06662089070304032035443d0040f500405540780f488401e4042c0c42141c0191107a5410701c00010030002d0300d6500359400c444404410010014203410103030031840301c0b14041d9111001c600e00170b500d41b406005002c3c018180100c4140b010809042c0c0d410811710701c0d030080c04110700b41c034004401070044080802e0300208848000074043c3c60b44d200804e00d40c3e4036040000740400c40800d0007015950801183d01c20030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 85831368 1250 85830118 85830133
    0x61706040804060f140a0c0308010e1308031f0b03100f05010905190302150c0c0301020f0a051303020a0909050d0e030705010e0a05040e0c09011d040b0612060c1b 71
    0x40314402220b06585142c1406a500842c2c6a42200e00700700e0a4101c1a15450100e148400507800c00d1003000c13070340e2094852000036070300c0d48980160054201c5071101c400301d4500f00900450480002950020404229400c1a80101c59a45010100e5900402e43c4907800010041c642c842000c0000143c01014140d541c80da28040000704003116034001c02d40300b6965a03098070b0401e81850040f00055901800561800e4100c0d601940f09401100c035011403030042c2e0394220039619047c400c130303070904142c600d00ba0b0400d0340c60741d400c44151b000503601d890989104a404400350396015000300041c00f1070b0034003140d0208149030060820300e03020f05500034003201c4c555501f6640d8001c604038003a00c60a20303001d090301d031940000802d039540a138070007508140b400e100707249500c1002c1101503d43c0ca0075203404089903070b18a0700c001403038902208424850100804100017800c2001d103142c00c14801032032030300031084a40405052040580f03000e4803d4000150040c00403c0d8036043e400721204a00141001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 85832618 1250 85831368 85831373
    0x10302030d050901142d0d0b01030e1902030304030501020f0d0b01030504050703021207180209090907030c030209061216060f020c0312160c03060606020c0d020f0f060d090606170604 80
    0xa40e0b4140d501c42070303802d010900d4035000402550301d102c0b020106c00c40c403040741d803401c80f21401503000551003c001801c0c8071001c0b0301940a0301400f84410750540c001c280f241500032880d407901094900072a81400100800408240f017400035100c00050b0300d03509a40d07410260102d00c100c5007007600b054107040c201000c0101040c404074071402107a0f019150364000c1c4142c0e103400c605080c2035802030811105006540081d04170350307030702401c01090203580c1c0c190203454922006a403007815100003060040810b405100606080c0202c4d500308202500c0b809840410411880c00c2110305550740e180710891503000c01040d9030002c00d40c81d05083c1800588941c802c04030100b51111140300c94442080d40c00503110002c1d02d000d05040320125009010111601d071a40f0b4100c010b4645480b50400510400784800c1e120300c6c1003035a05004c59401400310184e00802c400f4001038a03108103c0a5014005200014508c4258050440164419840024100c1c04e00f0710361303840d403d0102c20f0042d030b95000400700b000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 85833868 1250 85832618 85832627
    0xb09060f011403150601120608070806150d150227090f0112020d11030a03020304090c09060f08071719050901020307020c0d0804051003050106030e0a0c050103020708070204020a08010302030d050901 87
    0x604003614841c0e00540ea41380c60059a0004008081f401c0c82850010000350009008c1400810350f80321005403599501c0301002910701901c5145c401e5031160340d0107601c2002a503404841550310020483c09030400c80032548007034a010045c1c294400200c01c951081c0c615290180c0241d5000300300d5a02d01900e94108001c128171001d40c4c03000240912030307007203003001070007001c0e440c0c0294990300030304580310740d481c92038029269000f522841ca41d00b4100032280102500980e810000c0e200ba80e81d44102618220034101c0b08610080d001c070040c00b8294142c403c0d0700305134991143c07150200140b60040c01080441110446000800c4484143d01c10f00501c03c0f501c0c1d000c9480541d000c411600c3d4a40120380342013050346032086910a660000031104217203107164158004c00e04840e41c82c4c0f4104a1032881800540d2500c076001401441ea614040d8140070700d41c06035018185281c0600740150030034079280d0201c1c040703030b100f41307510740120704002d00410451408104090038541c491900c6410588100c0001c2c0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 85835118 1250 85833868 85833883
    0x118110306010e06090307120b0106020d05090402180409030203090a050a030b040b07050c010e0a14060f0109110c070801091e120c02012d0e010906051c06030b09060f011403 76
    0x2410810291402c080f1542d400b010ba41c0109001000d03500c00594650600d1555210f103c1c08039202c1c0b150f60000141c50740085800c1c4194005a00d8041c9003441084c1000001c0d84100141000d4140034090701c0202d440310310a81906510a800950750b0b030042501300500d03100c4a80c481d6102d10407445003840091380603c109500198041c2440303003a0b440d03042060b91603005000c180b11582d840c004100e0702c114400205416a240980d0394004980c4030014241d4968030704880d00103407903034a034004000e020100d070720052540c1400c060087c1030403d03c1a07407509201490703100c08005c2e91920304c00b01c284404d078000da02840d2580e10304004491190341d1400f484c450002c0d8039400344601940950f0569000e40e04505c01c0c0b8414450b074480e00d45420300001c484241c4408460000785460102100360350040c121340d0300742c1b140b0f07444090a0400030000f404060000f030701d82e028400e0b15a0000000140d04004050054032464050003881c0b411040060714000160307c15003c0b00187c64501005440210300d58 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 85836368 1250 85835118 85835131
    0x61c0b150102070f0b190201090f0b15061810030617010203010e010b090112110904020f030a05090102161103030403060c020607020f03040e0601051e040803070501050a14011206110d0501181103 85
    0x20341c6c10401010140d00409035910090400c1280010000800c010389000c944240313000340704070180f915540d05000a60141d1a0b102d2100080103100c01a207241403d204250b00c01c0b1482d01043e1680c071030401800d1000300b40c080108580d00400103000d0520100000c40c0504003c2c41a1401c180390350000810001c1c2c0780d00c000d003c050791450601d01c0881c00d2011101d500d54050015941c4810551807c01d03141c0c822550181081e1a1001195214806001b00d80000491905040764140c964a07a40c0d100b20307088030000d6051100f040700100042c4a0f00034000503072180e8000d40400d1605001c0030b41001c0350201140400e820405c028000ea5940a405e0b6800c140c0a10b4415141c02194800c400d00c00309000c2003000090010900041d0354100100400403544600020302040e1110701c804015100301d6140c9019119a40b4014000603840401c0e0300c4116024078408a041c00c081001c3e239546500c642000401c0b50303141e40c0140102c2220312284034807071a10090070000354540e03245503c40303400b02030a04c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 85837618 1250 85836368 85836397
    0x305060915010c210f030b030d090512071706010e07020a0201020d080903070c180f0b030601090203060d0b09150108030316050d090606080102090a050603010e061c0b150102070f0b 79
    0x1c90b050104115450b52081c4184202071101818904041e0184400c1703804080040d00b0104400c3c02410013040c036032012a01911025905820841081034a114024030159948500302000030400b00166503040c0d201a4a0087d01084d4140005a07056090080298003550702003455200180d0b4009625500c400c2c00b8600a40d1980350301108906503c200c43c0c0142040c07005940200e921500f0f04d400080b07800340b42d070081052103a41480002034580c2c0c000015819040080100100101f580046900c104002c1c81d2050300ca250b03a84000e0b0040707040c2c8055100d644003207401e81601d01d10380c988902400e8014001d5045181c0010044040910294008100000400d103014103451907084204020b83c40902404800c0c0c60b04141c0d4001e4000070840c5108200c2c1060020700d504010003102e040c1e03200d290130b0503203555500e8240a54080344844802070000c0d0768412401060782c5602990186100c4005451000d03a000700081c9004a0794101c0c1e8443e02d0031490800140d8402c000700c4000c100c5000b40c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 85838868 1250 85837618 85837637
    0x5040e0c160f0b070801050409020f04020c070b03010312020607030207151a030f010b09060111070303080c0702040f090611090d0f06020c0f071802040b0904090c080706030c030506091501 82
    0x160100d00288464006000c10000d944202c200100d40c038100e40300f40400c4c4d4410016a80c0c60003000161841d25001030340089044541c0580d40c10700f50000e01a2000b5002190036203951407041c103c45d0345c0268401c0e03e510301d6901540240756814031100c4e8109000e49010f6003042100c1c2c6510b5201c001c83c3c0000300ba56039644582c9003081c03d8051910580034001000d555082c141a1429806840107408844c490101800060b081c2d60103190b011085600d40c20041c05450308650303069070049005440c4418029040c40407030010b0391240250905002c048502107000c0d01c3c0c0389007030800e50707032002145450440b0038085245141c40d4082c801d240c0b01d411100c480303031041e024203015000f03124020111f600c5004e0003041c14450388001a07000c00f02c40c54140d4041d5460302c2d40115000724062409440765150041002c92110b2406400c05003640340900c2c08c0303400c415a80d21a82c0e1400e265588140040b035150742007201c1c440d41521402e9807019007641c0034405840d10510240003110701c1d01c0c40c1d6050284841 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 85840118 1250 85838868 85838887
    0x9030e10030608010c031d0601030507061b0c03110405100513020a0c05010e010c12020a05040b0904020904051609051504030308040c0e101802280c0f1103060705040e0c 74
    0x4204070b00512029008101074a855030000300038091a0984460400717490000224914001a040d812260000c01806919041c0320044403810003943e50a202c24451107071640c041a90008002e008511807040e40d29802e16510503c41510002041e00811880c4202e04004a4403000d600d05030480192000681e200070310701c4199046090704002400c95840c0101d0120146015800081c010038182c403100c2009130219540320603442070038000e40c0052814071042000401d10070260090203070080c000360500c0c82610101d421130f03604030343c0c15025842c0d90001980c996005504080500822b8841d803500e52102c107020340d13407481180300060800001200180034043c0c110143c00c0070740007810242240b420080c41c5100c10070780c507001e80d0040c446412120046248188201e0700e040d0f000b0380002401f91509621804e540b412800d40744240200580b4907000030703000c0b50f08804210311034030314400300400b143e00789480c08900801c9507007841810070041c020f4600704440c1c00d44c0003404804840d034402245 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 85841368 1250 85840118 85840121
    0x9240f0a0c0917030d1404020f0d0503041e0510021c0f05040e0a110a09030b0f04020306040312060902040b070c050a0b030c0309010912020c032506050d1409030711030109030e1003 79
    0x141d101c0e006600d402e030700b9046c0801c10480103004500807503084140c0c0d0070240801c00444100c2c04020282d601c00c0000304404010b00842807240e10306021411110755446020814140f0081d0781040181c001c3d180c210b000143c45050020700c4a007502d04020b003078070307400c1001c0d000d44114014041d005d00c540300083d410f040c0d20303003018280003115003249440d2800d08101500300c4059000407a0301010b04000103070300c40c1000760f089208a4004008140907100c685080d905803860210042800d6200c54000c1055070160000b04010709810500300c0d034449603800d11001c82c0200d50042c52258440400810140040500b501d07044080142555602e846500743e050040408010040408502400aa00031900403e80740c1c0c50401c264251801e80c503448500c10421043c03400d08005d500940041444041d2040c0040d10607403454203800174804c074050200d80401081240c607080301c1d5100144401c1001a428904081c01c0000e074000d1100c1c05203590301400321050440c441d4010010850010b600c035200e07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 85842618 1250 85841368 85841377
    0x507030c08011d0c0c0d021b090c0d0b0d0506010602070f0b0c03030615090a0609030311010c0f050d0b090c0403020316080615040906050c040f120803060909240f0a0c091703 76
    0x40310b0840301b003c0060350002c0d442d0104c43c4d03130f01003901080b01c000300c1060502c0703e0064070440c3c0044440c1d1404030402c800d08010706148541d1900000402011400503000f04401c3e40a4011a00208911441e0280044091080d50030414902c0030500440e5241031000080c3c0340c01c002e088035089001015807582080da8043c0d441040c2d800070b000c0030002066a002240c82007568082d5407080c490f08000580282601c0c013400c20040083c00303680f540ca42c081d110b1000740107444070044012540c0361500c0d0009003841c000303403030010010358001002c00031881c04000d0300006003021521020307020b241c814025240c2900805000203c42c101401034466505c0d41e12005204e41d116404010606046040c03041305d070071900500001d006160740104000d480c11540c1c0701e034558407481350761456480f4014016208800740c2102100d10440550007038a000b0b040000d8801081d030150140541341c00158100a244060440001d051410408032030340c50f403100c007000c1074905a114400c0e846100c05803c1d40745104 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 85843868 1250 85842618 85842637
    0xa0b160b04051c03020306090c07050a0b07050409020408012304052d030c0a020a0503030708031b07020a03050a15060506030601110c190e0105040b010504120302070e0a0507030c08011d0c 82
    0x48030710b40400c0354240c1d01850250300c0030703103201d1231560b81c10048004501c140607000e030007580100848400200250f4000382d00507003070318250341440c2e5104000010f0340c00540105800380d448100c0c3d00c0302c080e515081e02000c0350f16905c904090741001d4035099118075417110031218070f40078407105407115699640b403503140c0d0400c5c104490b40c890011190f25110100601c0403840340d41012800201407034004195110395400145c0a451a2920a085000046c0007152440ba41406008030360250750703100c0b071190046016001030705c0c8140e190704d8111011118582900b04503031501c00188801c1e155403007940c0e40042c0a08219004410560f402c0e49001c400610256003d803000c2c03c0311462075400c0024104440c000e603014840c590303c1360b0801060384c80c0c26031807a0020340e05100030460354410101035403480d4080d005483d54039868205800d010281160114801900c5500b071140203a030600c1924046807861904480079410021124456000110440034141941c0003042d48440c07180c04540d01e425 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 85845118 1250 85843868 85843903
    0x4020d030f140d0b030d021b010305040f021f140307080a09050a021011010e0c010c030f031103131505070e012003070309150503010b0412030c0606140a0b160b0405 72
    0x141d10070100c0c1c013a000d902d5a0b80d00034081c0e04884c0d0091800015031070b40d83c2c1848000795180001900044004101c001c0040d250000888007860142e01d031400700c664107c90f40441c04140e40740b6510040d0110351349001e0600c0b045002c20411244a5220600a0b04890341710008682e042050901c1d629040984c01c01a6000e0204d80001c54000e4220690204282c80d14000741b21040311010056101e43c070604445001c2240e410000e40007901c9051419081c640b07505000840491038003c2208135001203034261118140782c0824018008010100310041e20800014025031400010040014074048000d81c11300c076001b0001480c24040040440d46a100002100e031541e0071030a005000d035035244200da021174046e80200a50710301c0b40017100d05940d1142c5555103441e24150075071401c8072301024290100721540942600080c0179028240c0100381b600d901c5a15140b60004005078401036a0103c06902c0c07007080401c050740d05000000d0b0781550050000c1401daa5241440d1341805291000c2c4980300 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 85846368 1250 85845118 85845127
    0x6080408070b10090f0501030c0510120c180e1308030a060512100b090c040b03040303020903030d060810090f0204020304020301061203050301060f09030b16050c1b030c0904020d030f14 81
    0xf038443c52403642192280c0ba0144400481030b840c2800315242804041c01d400884401130040d4142907501c0300c0407000c05e180c9440c03003240c80c081c03078400c95004000f0100001d0804521146048180305590701400c90400803c0c0709003042d0640034441040d01c00020190a8040001050003506502c0740b00200006400c0107000b154030400c1c903848205010402d0de03090301d00303034140b501c0e41003a6104a10468001c4110b61405051a44022803a000100107c0415400b0815035a8a450500c040d220080e4556008184203090101081c2002c40c48032100c0b028514091103040400c0c1e1030b840401f82035405075001030307880d1075038000309000d0306042c0c0060f110000c4602010702056841002107040b948940d56481c2064030480c4221200070344d6100c00741124080301c012490606521b81d011a0306161810a10701d44003c1d403008900746100c400b0302980da020030000385251410140101c440848003140c019502b441d0543c0050030743c01c0441400307000c0080c140c140908281c082c801007071000740030a25050b03c2c2e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 85847618 1250 85846368 85846381
    0x108071d011b05070e0f09030f0d1506050901020111030702070302060f0c0a1b0b0708091207270e030c030f07030327060e122704060806012d06080408070b 68
    0x190340f0f070761150f11080c0d04000002186c8000c04081305004064003030140d071805544261011440d08000340c0c070a081e56442c0300c0d44403042a6200a04020016925450380380ca9074040003a003100c180c151490b00001082007000030304d035400305103001503980c100c0303a0702d440d100c07180c0d40d10070a4041d80c015100c1e140314149039030f0144051815441c48868903200501035941d1070b003140b0f0701e007070141090040a141d41441420124a402d686d00307131a244054044803c400d40c0c42c00c0b02e0885d0081540403501070b440494071400e001c0d4403400345844200c9104011803501d07555000d155034034810841081c07980d55000c108541094030a401244081120512103010220a41c1200300304c0740c0f8440003140c51130700c0c3c2101740a40c0c450114600c404a1810b0f19164103100050462002108080031180c00f000c58607042c4102d590740d107200300b10141400000400380d941c100b0425404480c0c03000c204181c2011404d6012103000200c9030101c00350717021460070100030703115032504002c1409502e00c001c014581d0003040101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 85848868 1250 85847618 85847623
    0x10212040c080d08040303020c0120031e09030403062a0f0e010e0109091104030605040b040203061b1801051603020c09070314010306090512030406060f050108071d011b05 75
    0x345000d045280304441e03a4061003503403120890b2401000c0380380040003601184c00799015000c1d5140100c0003140d40070ac1009c40044000450232244104080401845001c1d55a078000d0340c000d03a54200840721318140545d0650b0b9038021480020815901d031280243d0a00c465031800b41880d4004c050580c3c00c060b0f01d44083d00000405100e10000741740e44071119815846440004040c1c981a11400c00c0c0c0c43c00c1c0320400c07000c1c15800306041c0030300c0410080000010424840e4a01c254040d0810188500b801d20425081042c054800c0344100103904515070848103103401c81e07002001200d0b03000000c0d400038005170f40c2402074a01d4519503801100b03444003850340110341c007004020304030b44d10195560707004411307001c5964400c1c0900d0b510103104010700000784030f81e00c204803060003801224890340c1584200c41070390f4400c5604a46054941c1001c02c1000c3c401c08448000c2d04003420311407594501034000600c0c0101510048001101c0000d109101d41d000d0348040e00d8120386042244070003907072402e1695 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 85850118 1250 85848868 85848871
    0xd081308060a0c03020a080604090c0503030a030603020301050903030603030f07020f1203071406010b0d18140d08010504050403080402010e13050c0408190201050a1d060a080402041a1f11010212 85
    0xc070b4905000e03100b06094882c1c821100410f40e183c64050703207034560741c003030100a0001840407180386000280200d82682e007000035000c5101156000302d1074508500c10b242c02d4481c00350038510b8070b9000b8424006c4954010098442c1ea401c582541910340006000052216121400581d040320312500344504c80a40800180b00c400e020300032925210703003181e0110742c0d03c007001d1040c04e03600d074014025465a050716400104601c192010000480401502c079071907065041c0c083d20980b85d22112045000642120103180181421217007046140382c16203000d814120014802030400086074007801c2155036194203110b0011100c0e108000d1032034046005402c076400b60041050a1040c2c280f40025019164088040654103a480c40d0810101040564414901d04480401144034040c0324984d502c0d076102070802000c05a03943c01c16810b00d03005000403076181c00743c640c03c40c910b6048014495110f2801c40d03180001c802c03805421a20a015044888441102c004040355000040420503501ca104445 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 85851368 1250 85850118 85850131
    0x4050a060804050d080402090c0a03021c0b090a020403080913090605090607021e07150903050a030201091515060807030f021201080606030a0b07031509051e01080316020d08130806 79
    0x29050841140001d17075202d04102e034003e6015007550002288a4a054060403d0500300d04003d824444030600440702c0c441d510b0420070000e6a203c4c2d0880341c84c039101160381d4118103c2482146803038110303256030449101e081c0307820b40600403000880202d51140e0703000100c050f1700003500f04a00c0c1821941180c940c40142c4203040148103196110440c6807188003200d0075004030308001e20b201480c240306c03500707c0c1140302c241100b8042c0f6101e00002081c003d0000c5c03a80c9522a070f0000820084034580003c010038008902c2401914100c3d08542000c40c0007200350039584681440c4802c0e0303803402c8003100035001d02c2000300d181e41d002203020800c03039800303868281c10f031072810702650380a40e2824141507035a2903043e8040c00c0d84d403009020075580c600a80c858070500511110a084a90702c90240405aa0741034541843c04090b45050030484100006030b00c3c05001404043e41c50b11240c0c46910a2002105030080d01c946080c007000001c00080d81e0450301101e141014840311603584043c404d45410084408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 85852618 1250 85851368 85851373
    0x2130b1c0e2a04140c1e04050105070219120b0105040c0311030417130b0c010f0c0f0822080c0105090a0308010303110a050118030e03010504020303040b07050304050a06080405 77
    0x5154956404241c00411000300c0315244280d104081c8840c0d8403207581c198080c3c0003690350b89029030071600b0a640c1d6114a010381610f40c1e0740c0441d508aa2583c0f845c110307a00e04110414801031000c3c0c1e030b000044074461501101d095904a401002a861111060780410301001e0300c3c44011040003035040296040f100112030070000049000c101b40c0640b98240e0111540c0001000010001380f02010300c8484208884500d90409220106030308808203240c00c000704186010a900710409400d02034008001c0340c4034014401c0074000b10024281200d040503440a0024000c0015240c13076820b4044400d40200340403501241e052402c3c007003e15880140c280c1e4465003042d001401170000000c00c42140c1d0f50503a01c09010780e00e16141200e10b800045071415003030140d00c2d08000401d1090058041c0b884035541469080e84d5286000b07440040b044199a00a9040034104000b680d004015501101d06541417079544500d1840d1440c2144203a400259101c04100e00106525500c0304145100307038820000c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 85853868 1250 85852618 85852631
    0x170114010506030f0420090a02030901152621030609010603090803010303080402060c0d02070f0501030e07140114030103110906060304020a06030b120a08070c060801140402130b1c 79
    0x2449860301c0100e50314602113850402060005242c0c3c801c40c1e840100b0090648081c03440100007074244141074960903c13058004c170034040c55100030700c541603c01c081002c03c541c80c88d180000140340c0c4039914142c0341c00b0100e0041c040c01c40000c140226215516400303920768104511089103a215001620304138010b40780c1c44000702d0b00768024030603840710744e40000309035003160f1940e9070440d04954001c0003241c1281041c030040e190001d0401180c206004180c001d043d04505004c90f100e2a0070f070f284d001504044c10100c43d20f1030214049600c9051700d05010544115072640d40058814403281c88215031880c00000000091207060325044501c14400c840d0300c0c1031038498804000c040d000a07500650b00c51510a01000f415000b0703409003c81402c00380843d5000511560302a080c01101030007602d8003040042c1050410103c60044d0010f84114102481c45504103240c041100441c2100341c3e0146600086c03001200b1800ea1200c3c0c01880500c01c281e5444914051420050140b41d40102d100c41c180300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 85855118 1250 85853868 85853879
    0x3050601170a03020709090201090306090f12050a1e0e090c0901020706030b1c06060807091d071208030a020f030c0a17161b02060301030813152717011401 68
    0x10b0036981040c2c2590081c200141024410001084248000c906000d201e000010018200d402848442c6000e030703841c0c3c0c803124400d040c050800a541402d0300d040000c20071240c6115a02b14000d10030308042006801222002c0c40e078107440c032510303d06110741c0c00030b100c0080200a80c80740c2c0c02045081000e03801d07907814960b1400242c054035014034000350321003404490b01e03d442c0d000b64854058680196400b058481d5500151410102950421010b850704d60680b402c5c100030f41d810b030300b06001d400f03c004c0c15078a2520350150500260020010701c51440040415076912482d010340300204104200140c1c0d900f8025962140b582c0324802c000d0110303041c400740502521035903545038851140045c0d1f00b01440100c0c10100c6030a10454540c04808052044440150700c90b2406035011f103100307011259480d0032034103101100d50300550111180300d442020201125a0001080b0403004000720010b00c40c562081039242c030200c090300320314400446c100748001c0c142c205400c002c07280c012840a04802d0f9883c1c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 85856368 1250 85855118 85855123
    0xf0304050f12221d0601021e030a03061e0308030c0f04060f1704110d141209130507051b030c06090303061801080703020d02060d050c0904050108010218090a150305060117 75
    0x3842903940c04100d508030501d1085003134600c664003090501c1039031076199146a0b0010803000800c00a01980d00100d031074141c05d074052207494003420402c0c88205251140a502608040711404002c1c05143e01101149100e42c0c0c0d182031380c2840d4020340e980d60300e998844600805c9000c84110500015501c100900913a0a0b4118000e0140b5004042090f900c40f051080c0000000c074003104a03507141d201c07194003010b180c080c000c14400107803402285175203001070001c0003d100c6805e84c028034894907004c10701210301d80180c121400060720010700a164010140200d0640c002c603410304140780185410000e903c00080021442414201c3c1e02d00c081d059582010414480c0900990100390f1021034203002519040700301102c080c0c801480301d4508040e0700104001e9810983d00d135600500701013107812051606000c0c16014060400085040c07110703004074201c03d0720280c40000e00070100301001c02c05a80244d0054000025070002c2da03030085a803450280e9681c003091242ea6824012b8080001c10701c80b01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 85857618 1250 85856368 85856437
    0xc100309030c0204180602030f0601080907140f0109030b13051006050307030b0903071b03020f0108160c05030904060b071407081c0e090403020109030e060306060f0304050f12 77
    0x15602d007900300070b2036402d104c01015010038190200c03a102d001100000d6280c00118400d8500c24a6a02c890a1000001d04000c3c805840c52049400c8040f0500000108224241c42241c0844980030700d41c005200688400d0321980014041003a007808020a1000d00c8844103402032145003200d005013500405081201c07080d000c0e95605da0481e44082000c01c062060158000c9844000e0700d00d801d900c0d0352104c6c002000d9510800c40f03020602020410341c44c3c07540c600000c480d420f0034903001d070b803810800c161030400811b0110810700842421401c00c1c4141001960248000904100402501c414000801d41c025840c200d81144158250b280d00c0d80c070114016040b98105402400da518841404d203103080d088590724420021003012004031a0b83d4151154000c600980002641d10040d080051940c81b400070f603140181010418070442c0e803503a1084030748a0500316805da80f6501d40e450192b00b082c6211407482050f2203001c0204007024080002844100e80544074140000014040003154040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 85858868 1250 85857618 85857623
    0x4020f070c0b040b09010e041b020f0601050108040b0604050a0f1503150b03060f13020a06050a03140906060d030c05152232070303020313050402030415110403080c0c100309 76
    0x406005990640d40503c140b4051350300001d002042149031110700d00031001c1c001520400582c002000913907a01c0c03060211501403d020328040d000b51070319807254b010064016100300c0c05207640c0c40004001c7c440c181c0c0001c134148401c0c00c0c180005405050801516a00d0303000550b01e0f5400c1c1038022000e10701030b208444814202030050080c60361110501c0401170401040e50b0101544480c030781006a030381c00020740c081c060540310241c0314402e80c000141292004c0600c1e0b49407e8108050020000d030002c0c0e010343c4000b045550621700300507882d013241d2300701210a00904920414503065404500d04003481c0c803404980d8460302605010000e0203240f06130403103000e4494000f00303d0001c20044144c62f4115031555824190b500c50800d009a146040080d50080d001038001060400345004071002c80d070000c0008032015800c505081c0c85000070000c8881d6913032a07407543e52545406c211010401d4800940c1c20110743d03038541000c07248071900c403903062100600c12441c0c90311721041c1c24024440d90714103a8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 85860118 1250 85858868 85858889
    0x806031b0105270a0b09030a060903050c010221070201200f0c0316060e07030b04030e120a0302010b0a091505040c030b100906020c0612280e03070203010c1704060b04060504020f070c0b04 82
    0x23005074031100c0042035494000d80411804010300e1021140900007080442c0c0003201003008050000003006003c03001412010441e4100904406280d09210980c6180c18000e505155204981c9400500c14420804064082d0001080c0041240b1200c0e8003026018000c01d01403103050810b40d02c00703440702300c82c2c00003c3c5108506000309004ca84500c2c4000800032018241030781403002002540c0c03401c0541c0008070010f1303448060804560400d25045401010001c10030300c2071900e260300b80d03034012400e0301449000d15680d4981c404254840e03042118412400391030311034414841c0e0b40c01852100b550007120090f202e010189042410080d013114052200c88d21000d08981b144074a850007402d4205445100c80340c1c0090030000914203100e0801410810001196503010b00c0c8181402d4900d414001414010005604950980c0d0405242da0066101c000045c03807081c008001780080403241c122580007480440c00203000d00700314001380210b9025607181c410709540c602e060307101407241e4001c2140c2c20 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 85861368 1250 85860118 85860133
    0x10b0a06050a0f050a03060b03330303091210090c17030310061206030203032d030103030f200a030309110405060609011b08070614070806031b0105270a0b0903 70
    0x803882a03000d0300b80b1725100c1c41c000c41c209940300340812090b04262400c4145154a42d02c4466a1042c050606201030101c0010f56403032080341e00182d1603000740d2045900a00034180c825500384414800b161151138a403000708082c0e41d0310b04000008404a0182c0c0d12510b000c046008807602001064034400d45845c0200400141440c20842d41000e2079603200c2c0c0c0542c1c503403c002c40140d0301072014060100e000c0c40302e800071414030000d1080d11011144012075200d020001400440e601943c100130303c1586007010b0f052410b60710480304141c00000800002c1d4050840d11500701945500030102c4603004900d0030f410303c1d8a01003000100c440076a0110b5004a00b00f190b0041c2d035000784000d00c13450b4507800400c1c0a401e00c985416186511001c41241c809690360380308002d03910080c41007034200f149840c0003545458040c021a58079580d4030150300d00000286080c1486a203c0e02c2154012010024803204001d0120708204542e400100302e284500c1980d01c02064500941044d506016002001003405 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 85862618 1250 85861368 85861397
    0x70f02160501110a120f0207060c0206040b031b030403030b120c0d03080c0c03070f0611041202040218180106110c0a0b090406030218190603021e040b0406030302010b0a06050a 77
    0x504a060355150541c002c101d180130104017881c8141c0402d02c800d0315402e88a480d01000241400b409030004011b0101c0340c00450301513110760302a03406603030520500c1d5589460306605a0030210760400201040000001048101030381a0440078800070103030780780d4080d0f244004186461740d0002340e0640e00080f1540c0d5120110b441250451b070880d080005207445e024041e400141181c0c84048107564082c80040f00300101300360351003008110791885024034201030030304c0d11925840d411f811000e807060b500402c20098001c989400303201c401200404402c41145031640c41c0014003402d20884011603003101c0d81120001c4c02061880000d0b80040021355030b04e081070022485a04005281900603030b0710400440140c582122400180f03002c038464034582d01c5c00310103200c1c24020381000b803903900707051250400c0180c131882c05000c010548004101c8039100c000002c6002040d59960303c60740141401400001d00d03406501881402d4000e0b038032419800d481c0d01080d0362512030003c007400040c640a001120 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 85863868 1250 85862618 85862627
    0x90a0e060708040c1d0420101d0402031519050303091905090403080a0513020a0302090717180609010203060109030f080904110c060a0c08070c080405030d0206070f02160501 76
    0x74824420511400c041c2d840300701d04d003c051020107400400a030a0381c140014000c060810340c9041c04007c0b62003c2c103c0e100c50219820601206d0041c09000c2c00b4103101c0201020618440004100940115264071304000001011031540c00c9840c081c42c0c10307c5828001d079000c8079000c03055582c041c2c025032a1003612070911100b00380120310300b940340c04e02c00d80110356552441003e500480c0660345050305810546c09820881c3d07c041c0034403640010501200c1c0040c3ca400c501001180c0d0101c52080c0c0995415109880030494600580829030451040150401c1d480e0110f00030310a5400032a001581c441c00e1342800c03840107440007808513640f04001c200285501000604003071040c0103040c14804840045415036021b01100c5030143d2000c601030003542010400303654001c048580600003840000c074003400b603050140540040080c0e9081190a10003d00c089a00424001e0200c03103040700d2a1000a4a40d1010b9842400250701d155550049510000d1801c04007050520500c2038680342900558 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 85865118 1250 85863868 85863871
    0x20d02071a09032b02010501060207050405041109090319090e060d03020a060207080d0c0e10030c0306030215071205190f1115040209010801020f0d0b0d050f010605090a0e060708 78
    0x24050041000300082c2500c00703021004000060a031100d04086500c0013401e40c0d04040c001240440e0700d04001005410340c0002d40408a48098400103459116414915042e50b0b0410b0441d03000303e041c4043c0b0040100000040c0890041c0c1b405ca44000b4130707074007011103502c1c909100d5004e10645540114116242c110b00001c0013620034012945800c4050790f500081c0c3c0c02c1107000f950301010101d12503610f14000d02031446418524580110018003071000100340a1b0411400710804d607488091104d00381c000ea101001854009181e00c49d441c500700d0380c1e00c80703507071100904450300c9071250080c01d201801350303095500340004091040c880d080c40d4903041716128010306a20040001441030f5071281202409041c0e60200107080c80559407800e40103110084a040c0d00000c0143c3c4104a600d0110001d5000e4950f0800d038440b02060f140010340c0041c00c0c900c01d20030050458000c0c150349001e1880e05501c02002c0791010385603040540c1d1081d803040c040780c40400503008640c0054000500140c412074034507 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 85866368 1250 85865118 85865159
    0x1e0a110405030d0c02090f0f04030c020f0a03050619020703050703050a02031606020304030f020c0d020f060c0f030d0606140f030a0f0c170a020c0a02060c010e1b0f01020d0207 77
    0x904241d65940000d142500158482010484444161065081c000800c039404914020008240d0400130358004c1c040f48014409000c03c0302c0842100b045584024641c03003113070402089001c07041d88030304186845070020703925071206030300c4035060980101d024001c0c0c8000e5a05a260241403c070251002d0b2420340c096100c01c011804104880d20804149001801c011070084000507282c1c5458a4090030001582e0b00910555015411031101ba50740c2e01030366114958103803540c4c04c2c030721046804148940181c0c94014958000d44512a8040b4000404dc02d0504044d00c41400f0721aa948026500d030307000303100340260002041080c0c03600c01d244040115080100040005591860004070341c003140c420000440001d00e07104450b2100c10050750502d50081482d00301140b070b0910020030b241e0340307072110f0200030300a000118400030082800c7d8000d01c0d101d40321605842c00b00b4045903440000c0c600c41600c40c0e1181c11411503c2c1c103075520000350600c0701440c40e001054082e0a00056007a200d07800c0112 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 85867618 1250 85866368 85866401
    0xb040c0509010312080a060b0412020312030412090e0402010c030509190603020a0906030513030c02031005010f051f0206010b030c130b03040309050613091e0e060f1e0a 74
    0x8440d01d03800c450307a0095024000d2070440303c0040400910300c20016200c0001607003012010700c058a410021141180c4600c1c0503d11040240e1011a0810395610b02c01c1004020120030482449281520340040303440a66640400540b1500f1075403c100007583c0c041c2c002001e442c600d100080c0500c0003056240300092181840f04030610348000464181c4d0003140010342c0100b95a880e0a4011140d00b000e028241014800d604d4507200390440d1031400030010b802c1024271060001503441c14803214960408412092046603100d28020032844030900c42e05001c1c4d00952040c0f040c5900703842c184801440583d0140c00140d191090303c100f280c0020f000a90030b5403080088180d095201481003009000c00401142c4902e01801e003d0000b49071603001900a03141006140c5456061141c400107aa2800341e00080801441c44052030320001c2122481d202440c1c04400e160011000540c2407140c080b54410512aa56030b0710303800c44240720b940001131883d4208000ca00c5034100c0d41c01070642e040d8030b03200 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 85868868 1250 85867618 85867643
    0x304080304020d32120f03060a0b030a02040609050f0108061012020c150114061e070f0b16030c0c150f020a050406020c0306040b0402040b03010b0303030c1201120f0b04 74
    0x141c0001100108503042c2558001c820f42d0013000c40350101d606940c0120801074007542416500c842501d03c180c030b8842c0c02c0741d040000018803c1d0f0390654070002409213811003c1d1645003030000c60340251b005018031004039213611030008081c60854401c65a11806941c0d80d8200c0e11042c0a200448101804040034044800c0c00c4e4820441280302070301d40480c0c020010510001136400c0a603c100068000413020440c04109207425221030041341c10407100101035081d081c05840c043d00c4c41d4000c490303008115102810442c014044114102d0b800f421450305c51018190340d2020503003c61300040c01c284041203900f0243c00104003124881c8610311b45074640450703078003448070002c4101c0c0c1c0031008120215a0100341400055810005000281d009130b0080c006030500c0d8980302c01c4c0c1440140000d03c19600c40c1e050f5101034600790800c1204400140440c2c0d22820318464060301504604036650348440c1d00d200002d800051480040812500118102c051403103a8407010265140240b068800c0941c914 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 85870118 1250 85868868 85868873
    0x31c0903141309140103080304170715020304030e04060f0501050d09020603091c170c0a0201090c06020123040b04230d091802030709062102070b0a150b0304080304020d 74
    0x400c00862614100c110141c1400100340880d900301340080c09200e6240014030000750b4071004c4a801980200000381d80000800b07114145105980000b400e10b0790f039030f1844100184a401640c011840394803401020307001c80041c8001c5400920904809034400e2200b00b201d540104000d024511203001e000c01d00c2ca2031a0042852584251101e2040364007420b00212103030341d01c151440309001d0614249204245d1250303001046240500240b01c000320011749404624003d40c821a18558810800c0d015542c1e202000382c024810807100c0c80008c8109884140365202c54007079148600e510101c030a0b1603480fa500d40c082d420b15011184401440c001201c0000b001c07040158000d010495501d4001c06420051000e020603800340868100f1030061042c003280700d42100310002618460706d0802d600c1c42143c40b8000c0011181903040700414800244c003024054000d811030700c595040e01c030602149100301d0340500c00059500c01c0000c2600d06001103070000e9101380003190402e0000700462130884168 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 85871368 1250 85870118 85870157
    0xb040b060304050c030f0a05060402041d061f08010606080408032e05030d2a031e050c010c0c0c0605030603011407080f101404050a0e010203010b0c0708031c0903 71
    0x3a10b06880681c0080c1201599103001c1089a810b4041000076003600911603880a5540d600608000c0c41951580070b02291030700940f80d50f501d082030f81d00071503210f4105a41b8008885105454905046400700c0010440240501602e8100d034802c1c0e0b121840d6980300e071244000c540001d0820f60030708446405491003030850700210f850060460324403915040c60201007625101c11405120244183c04840386000c081040c00e18001181200c007840c070140642c54215020418044030704542140061610000b59000014007a9410f01c0c0d0005c0010717054544050b140c404860300c005084420102080c80390611503030245410000c054004200c4224411250305c00c800112548000940c0c00803c100d9006440c0030680c3e08906051402e1001c1400e001c002c0c0907400c2e003181c0040c0a9034680e40407590786150f07984008080f64070340b0000c644950f1200340c0e90317031107500c0007500c0c0c400c0d0b100b803140c080340102003c001c90344189910009608410700320700b10130024044084c0d0a0301840b400482540400c03811 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 85872618 1250 85871368 85871371
    0xa0206070c18050c0711010c0b0702010b01081b1c0609020a0c03170705040902131e051003050601120906020c01060f05240706020903120f04030308090a0f02040b040b0603 75
    0x340340c0d2030700000c0c00d19401e0300440b0122074084048500b000c0620594075035074000c40e40c2603a0000c0042c441c404100300141c0e9580900c00001380007003804420002c1c495419484030500d41c5c000d0341c4600050302c03404144068820a8500703a02d0714881000f2921400d4650441d064160000c8200420215525548081281c00200d094408502c0a4018074101940030291002905804a14048031308091320024018000c602030707840010390004624140c2100c2042c120020032030101060041e8500b0450291070b860b131440b91a0050391441555145280203002742846a5810781d01c10450001000b514030192605140544102d0750800161aa001d428003d46021b400d5076050b200c01c0c546040705000510300414255655200b0740c0f80c5420f50140c1320003c640003150008005078030b402c0d078140061b06041c0c0702c180c00021424001603ca00d440250320103001102c3c0203448050702c40d03890041141d00c408a00390010201840c0000d100010b2600d035002142e120005800000d600d14100080b0382203900 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 85873868 1250 85872618 85872623
    0x6010b0901080109090b0402010e0d05010e01020a0e030601030b0708071e090302010210090506010b07020a0b0705010b100306060c060509030d060303110c01030603080315010c02100c0c050108010f0e090a020607 92
    0x1040e08095030098006401800b940c04104030360304540c1c450a548120140000b41003120350b9603500b22998416400d0000b06400000821050341030142160003544180442e8000c41e0001807040d1319442c01041050499800403200c1701070340d44d060f01c11030f0003550013440c52062001d0940011140f0341910004034944c030300354846120307080c15800064680412034548c0309030503050008030400a1004a08941110350750122036468448074400a0904191070308041ca40710408180780061050542086001d002d042c2d80c4081d40c5c2c059410101c06592480c022000425020010400000d0b90380d8030036a4054103820a5030304125030940040144d0b4040e0740306800247c0c1c5000d419403d4501441074230b0700e20000342010072400e032540d41c1d601141d0000410004a0030398000070042180d01584501e100584d005061540042c0442006401444800e0b4107403502030501001060a5000b082e009042c4d40c0811120301780030707140040200361207034020800d034900c3c05000144801600c40801400b085032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 85875118 1250 85873868 85873889
    0x9040f051e16020705090618040c06110304050913030207050a060507140102040e0129071a16120f1b030608060c040f050f0102010b0a090b042d0504050f0601 69
    0x7280400451a54003a0004042c1901800101c0a00341c0004000e012220309441101c9150380e40c0000901026020803c40b10800080041004200850030036009441e02a01c88548010080c000e442d0f0341e00031070051a41100b41070002c2001c0c800011020b03c0c446109104850046403600d0200310700c8d200d9980701c04081341d00400c2d18001c001c4201c040c81485c8a100c030003141820300d0004170081503030040c032840a2031900c9203644004000e503200c0700080c083d1003400c0141d032410075180007190f01d103082460012480070000440c003980401d010441c240d4200d41d071195118403580554000070410002441044d603034a140d80b8417110b01e01c040f08100c3c0f01a549000601d00e18046400e42449030041600491040c100001c1c0050303442d104240b41034407416600850b070006100e0043c3e004001145030742d0350004504500090404841c1c0010150180030380701480b402c0c40303103582d000401c4604500c161501120501003180c12405134405075001c0d009a044984808298000c1d904201003a0800c80001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 85876368 1250 85875118 85875151
    0x160203010e210304020d030f05040e0702030a030c020a0f02060310031502090f03060103030915030e060a09170901080112050c06030408180a080d11010f06090516050306060a030209040f05 82
    0x142e01482c1d612401d504207110715031540c500740d40020030081e1499002800c4c070040141c1900681d100d00e05483c0a008418021301c2c50381400d4001941ea6080b00d00c030b08001030f0901d142862018404204110225449001140e07080c20542c00c12049400090203aa4030500c4800c0c000301003102c5440502e41e1481044005a54406002c10700c40840c03412444180039a00c00340c010000a03070f001c0c048808a40308803101900b420b00b000360071400b07030005040348040c9200340c0c028030a40441980c400c140306489202c0d4001050303050810b6140a000c1d051405000c50784010041080043c02c1082064152244095403200010305000507440d4009039401da41c041d002090007278006209101004941c03504440e2101824907081700d5030795656035043c00c0e508014103441441c41500003500010440c6600500a015040e201e110b1321004040c121506440c0290031204448003501600c2100e001e110040c000603d0455020b03003d41c06035001034080d079045540e402501084200c54412507010701d004031003403400c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 85877618 1250 85876368 85876393
    0x40b0301090608150703050a090c030b251b05030c0a0b0a050604060b0a0e0a08060a0e0c0411160503070c0306060305060601021617070f140316060903020105160203010e 74
    0x8590b5903820003080c80e407110380f9281502c0410701204e94041d08070301d0089165510384030070328081c14214000806440b0b04003000300c100000502d5242c407940d5001c003c042c0b40303002e0304200305003038442601440103e80b060080c50300d024480d10800a446000d5000c403460320700942c1806150100320f071415100c0c01d1550b801e214104145000d12354100c081103409202046c1010440301540c030844c00d0000a00c40f0000b074a00036500d91440c1c0308014280c08054903003d2504543c100050450042c5819490203600c45004440c9000e100e4080c11a800c2c4020a0400581c0e10580c03d0304070134044155007506c020700c88500050300b070107000c2d801745226180100e01c5929500c4c0c00b5181400c00380a0b01d0554000004094420541c0014141111015610144030380710000c0c84030300708003c9404c074242038140c5280c00300f40c085a08058040d05941075088544880440900280c0c8c4041801628006909413508001662289020700541070381d0094825003c41280e00190031030b40c184a440c02c1c241c01c00c0703071403410 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 85878868 1250 85877618 85877621
    0x1b050a0c0b01081c0302090f0f040f060806070201182102070e09030406090e06180a02070212070e010806010b070b0a11070b010302042d0207060209060304030e031002070503090909030c0102040b030109 88
    0x60404e12820150700f81684840084c2c1d80c10b2502ca40d6900580340040000410f94031600010740d00c11301d2403420003000392146900c0c1e4543c08202d5905000d0340c205143c00001c60032400715003e0360398000028914282d4088039051040c4d108105c500300710b11907100080341c038403a00401140100f50503030055640328a0400c003c0c1114240764451f5104c0700702c0004011842e100c00e200c290100c1d0b9012500c00c590b6481c4c0ba84d40c0001d0140b804042c0d0029400c810351910700303200042800540794a5680408a45c0c1c0c0c6110a5139940c42c01d0107a01800070040c4141c400103458550401c1c1c0080d071050010450007500c102240d55038000100c1565620340060042096081500c070b2100104000101c1a81d18000700a880240d13880d40c40051500300d5002920006000c00782d8103503400d0078bc0060002e83d8030b007481d050051030340303e0b0055041e200e401201c6031040e544030341c1e10846100310f5000014608001c00e9608120141600070310070000340c041000740d242000001c1c8000c00242c079410180c02d44a504060340c3d4030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 85880118 1250 85878868 85878913
    0xf040203070e1504090302010e070906050f0d02010c030305060406030b0c0307030608010c0f11151305071e030224040f08010608010207050c150405041103060103050a1b050a0c0b0108 80
    0x500e42c00021081c016140c105500c0c40806120959021840e00502d1a0490041c14214028412030151140101e000001904000220380088511084001500081102c030b0404c240b802804141001140f2000900a41145912203002080020300595940358003246080850340b840310302c5000000c101505400d071041d14064449a00200018244090081e10340300d2201c440c0400e0001205070301000740c1c41004140110940d2100e110b40504102c82a554031131070b0b412040303815000c0c1c2500860b82480c618000001d590b05c03111544500e0340f03507800740b003c000b4183d0586121100c41c9010910018103210050004042d0a40600e1b162480c03d034a85007100c1e51600b20801d2a401000b030400400c0000405600c0c6c510700700d804031184000c024008032944200c0d40560340280c00e1a28050800f00c08902543c85081c081e00c1c01d016503550100c22008586800d41c50130b81130394036913a0650b03c89100e4805032042a10a05050358981c1651b1252460306109a0102502d644020038a14544880b80c41c01b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 85881368 1250 85880118 85880129
    0x140f030708041e050d0c050c04020a03021b0a0f1514040b0108010e06010b03010308090d121d090f041101050d05100303020d180b090a05040c0201050105010e06070305040506090d05060f04020307 85
    0xb0fa0200b250b5640b50b4480302c0e00c1070210100082180a4414060140201c20341548028011551096070300c0c8050040d400c070f031401030000040001c020703c0b180d101181d403440a550103040009000360595a8015400d840246111402c2c0d440c51400c0110a0348070965015900480b104203140d850301d5003480c20b5480301040b000b125003024004104c612180004d8a0560ba400701d290707610346003c4c10103d0038111507480702800d10411845110741d800d0300103090b0b00841303440b00002170805800400f408000a07003030307440d00319901e418000600401d030180c0e80181003c0052501305e01e0300d2500e12402054030802d4410041644900204004141c1c0402205404070011b061031005c60700c03011035a02c2580c06500c03070b00d0581500000c01d00420b0b0307100c840795006004002c00c100008042808001e000344824010580800d00d07920341842d46290440680300c42550564480d4502070a050030f0024035000b0010136a00090f540321aa800201c0504c103107845404c6902111403585058010103240620542c0107 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 85882618 1250 85881368 85881413
    0x12050f161d090402181e0c091003091b0801022503050a0e0d0807030302220803090402070c081e1002030f041e0b01060905010905040e03030403140f03070804 69
    0x3000740e40e40052200521180121012403203559240049042e001c036000e034200d18054440304104c0b151a07090741d20380d00344a444c40000003955800c2e4041030380c3d10070704a00d96400b03004060401c049a200f500401d04c0684140303440416078080c25114560407200ea00840b40326500810102840b00c0c4401d030344a0403070110103080d240160a034038090598880c2c80f52910401c1003600d03544034103072035004d00842c0080c0e010b0f44c3d09a5490707803414010001d41080c081808016800c022520185403460707009015503480c080a90b00c0e0030441e9003008025400311004903501107174000001200e04c030034403c0026800c3d07401292080d000c20401d0840c28003070200c040802c118070504c18440c1002e81020440c0d03200e42d0084031281d44200074452144520001c4000914140e40b500012500d150b00141d40400c0712000c3c2c0700c00e0040c13600e480411043e224028605400c0780d10500c0084c000c00d106140000c04000000d04203403411410001c43c0615034411140d48000c103c007103003800200710032040e01d104000c105045 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 85883868 1250 85882618 85882637
    0x612020702091807080d0302090102060912030106032c01050f0f010b0a0c060b2115040b0c1b01020406030b010815030a020405060f030601080c150a0207050103090312050f16 76
    0x425200e0060a040e00f1603418989903c109541000920090007070242160868001185c0040107540601d5816005010340c0000c141d401800040004945a8840d00c1c40c1c2942c0c20300000f14020003907103c032000030841d0407428544259001424013034402c400400856036107045d07a84450480d0010301200310b206010b60042141d80d40150a1728085407051815122052145c200b66002d00002c91429034400e299100c0341c14800741101c3c1d04030841c060300c4142ca845004249100032150811a400342081c01a00300060b80007a596006001c0d50341c02c00601070850500501c034500f2a0090380040c000f09a1b500d81c1c4448641e0001d00302a4000001a0540600101030004c06c0d295000314400078003807615807000c501d46503600b0755802c2d0301000c0901210b000d0340e5140d48250362082c1490710035004180454100c500140c2001c12182000c5541d0000c001052824004400800850006904000722100d2003502089540100e5010f05a28129501103040c510b100841c40d04210b9001d0381401044c25 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 85885118 1250 85883868 85883873
    0x100b0c0708061f05042d050f070e012f0d021623010e04020f0c0307060f0c0c0b060420031b03100608040c080106080d020607021b0d051608010606120207 67
    0x149070300030b8640644001c200b200e00401203c4003500c2003006e5603082c01048040000c58655507201e2481807a4502100b032150300d0b0500c003907039014000001076000a00801c0c808100d8100b104c403601e01c1100d41003034040201c0220490302d041c1820f40c0014401070300920300030780300c030080c0740d4040d00500560226507101030740f0803607100b8607030311480c07141410701c194040141060340c1c80303034103817001082035000440c0d1b22035001d10141d440b0341c0051011609a850401e03800101c1002c4e10601c6211213142d01c076200e000c00c864454440f0084010400c51380300780c8800010039000c80560001d602e01c115210100d071241000c00d44c0d0b0407111018050362a43c05428020042d4241c0c600301d20008495107410f2105c0280c445062a001c042e4031608011090f44c201034000826a4001801403140006c51f030a45002d5203407103030300b00d03110a603070f14860840e61002000c030741c5286046a0301202e402e102e1022100020040c410750710000c10507500030059a55100010060542c00c980b03a0401180b07604011441d00b401c1c0d0303 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 85886368 1250 85885118 85885171
    0x41a03060622030204061203090f081e030f072009040503030106050d09120810090e0c01030c030209100509010306080118060b0303070f0606091b0f08100b0c070806 72
    0x2d4210300c05004000344002107080c000c08401540d00030f08180f08040c1c035504041d12040484608800081809a00155501e85068902c003500d079203901802207182c0100e42100d001c01503000b03120850004000e44120340c4000c03401030100710302c40c040c019814200e0f001443c0000c1052640d090294101c94100000a100802180c0c10745003070f400c1650711443d5211005004101d1048010401c20a415a03c4083c58116441500c01c0040301d10b00c4802d51f03140d0a03502e05941c0c001e02c000322503500503202c2550940c0250840d5141c00203074034005083c81d444c5400a0b104121003450480440c1c0c0000b222442541d150241d14091310030703a0000e01041781a40398094045c40100d901406d402c2d51003800102c00da80600c211043c1d10340000303140015100c68180103008048a11a1a990510b007611110314010030f10800c1c0c2c011512604e541013200c034094001d0306e40c0103006211522014242002203081c1035248c01038640a203e01009148060a0901c9280382c0003000e03007040e081441801c034100d400403a1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 85887618 1250 85886368 85886377
    0xa0902090c0c06071b02060705010209040509070609030221030307030902010e100c0f03091703030604060905040f03030506270901230117010f050702100605090c040504090c08030708041a030606 85
    0x284c50803007030020400028210074031707a40100039484035002800f4030500005402030055000220f030100200d03101d00980303030f41d514950301c107940229034580030802c05843d00300c0c5000c1e03403c04601c1072080c071060303009100e5007103900440725013001c00d03034411354201556445207001c03010700000c1e6102c28144802c000068a00010410000e01414042c0b50342c0c010503100301404802059000d030500c5945440c600306a0b101d8000301c070668010340c40c213000042ca03603029019041c002d54000c00314000b00703e41d43c7c45c201e0152000510390f43e000a08046250101403a866401043c202d1044481a403401e0074007116007916441c01c0b0814804491040c070342c020070542c6110604407104800e106417100800782c00d0f42e02401c075880214100a141200300650345801007991032172544200c030200304c3c00340c803801005031184003540c2d8545902010f01042c480307801d00d548084840c0e4080ca4603c030150756100045455603120910488140d040400e00300700014003907844050b45141c249442c0d045260130004621039008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 85888868 1250 85887618 85887631
    0x4030602090d0209010f0303170708061c020603011503060807051809010e010504030807201c02031e130b090105090402030403030902120706020f0105100302011103040e0a0902090c0c06 81
    0xa0014407007509030380304098440560ba0140c8044403943e580d0300c4058649800340703c194046000c840c5085c04031007800081c0e034818016a01e0300e40082d01c81e0804d0010004141c842c071115050240c4044025a5910018600030b02c2a0035902c0301000c14020010181c8206600ca4031059124020134000795070ac4601c0900100500311601c030280e40d5041d102405020300307115211b425440c1c803081c40145684100485d10801403038480c40780d9141d440c40010110a0030644070700342d40e004001000040072110012200714001441240d0620700010a10410711032181902840500c1c005500313000c1c09500c1600200428000c1081030400c0c2e54070740080c145104514050b442145c0c00000201010b019078000301035603030064890150f40800032100c55035107940d80203a0025100d401d06c80c805003401400303200c2c440c03001c0d02e204c80d0700e203881c541c019940b00e184070002018a000070703c0045440c00d035415130184112500c0e2300100701108140140312040d030f4060f101003801502003060301400b00c40040c84641100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 85890118 1250 85888868 85888871
    0x30f0f06010909021c0501020304110906150f040f15030c05030c03040809040e060a0507111b04020a090e09070f060804030503191e0f05060901031718040e0d021b0303040306 76
    0x20381c44d100180007030031440f02403029019100784403824890154007851060307109641a0b811080450208500e0303550440e50f180e88400c4411400c0c10310480000600030315418559054202612003114080110154020601043c03069200146980d458001c1c1c980c00c482a043c10ba103142005074070f0802c00d21008001600d42c0c200050071181d541c486a1040c1500103044080d1441420b04861031406000300780c91040004502c000c1d4120404030100b001c03180356600d0082074542c40e4510f01404082c0d0040b603503402c140000410000b408c4440c2491003442045114050588241004c4020f031012150340c0200003081801030030040080e801000700c0350091400e10020940180000403030001d0b1a0441c4181040c8890342002c0c6000801600082200025400203120b44ea880d44140003003210b00f4070015200921020b80c10140d1641c103001030504a41c0c114502c400d0500807004101a150054100c10b4181e01c9030030091401e03503050100c0780c071030000001b4060201c03e225001a6036030240e40400340506 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 85891368 1250 85890118 85890131
    0x80411090108061b0d05040308060103050a11070f02241207050a08070302130305030f120105040b06030609041109012304090c1403030702180702060703090309030b04020f0a14030f0f060109 83
    0x2941d0801c1605d081d00d024035020f0166103414603000f0840e000030b40301507000c00d0404000c5120303205203004902554084120540c14a0407a45580341c1b07041110030241d811031020382100740c0743c100030085c0003614030b10801080ea44161821100e595900c0c02001c01040000510500d0603540d404416150441e000d4034001d038440754424416003580500380c2c8010080d100c000342401d40c190001c0c0c0540503050b18038407458210f81e6994207000544501201c1690b10410030000164039180113404d171900b00c6e02480064032041d4098010840c40c48080e0045040c05030790f54841041805540403054880b0700a840034004440c2a50360700781e444100d070040960300030800710415055142001569080c0b60010301d14824074100c22007a80d2011400d48503280140604000203801074041e0080c82c084641c5652030181c1c051a6841c0c191040901030012079104008031681025580c034031500e000542000c5121051829890041502d4222070203503500c850f400070022040c03108808581d560450740310b01004103e1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 85892618 1250 85891368 85891411
    0x31202030408070b0c0319090503010f0b100c0c120308040c0510020a030305090f030310030c0f0308090402030c0f0705010b0102010b01090612020d0b0d0b070210111603050906070308041109010806 86
    0x214080c00c00c000003c1c0c40813055406249234802c0c07200e0100e13a025002005500b0000786003c0c29581e000d220590000744000900e49110300c1010540f13101e5006013580d002e2542c981e0740c0c0c2c24a0640c00503040e00002c003598240003d100380c447d0468000c040840d0004414080d80704040d4407509840c0c400380901d66200001760034004140024010b0b4414803007620340d81d02c0c0202045003900e54501080d00e103c14034901c00304d03440050405410070389422240083c100424a01080f002c1e42c0014900080800300f4080d2210140c901c60207014020700c03920003c02c51055007000203084482c517901840c10000d440c401007000139045a540503030b62141b104090b81d200d0701e1401c204050045000c03c50f03041216204a40300340300c9002d1409002d181c0650903180c0f00140d0702c4416065510000b00d281032418200000a401d0b044e0300315001c15903111341800d074141135016000404a411010040d0041460b00c800c100801921101c2e10b251200125500d1b4541e5040201c85030307840a00401c4542e04100001000702d8 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 85893868 1250 85892618 85892623
    0x6051c03023a021c050301050a090f0605060a0c140615010c170301060f03050604091a0603070302060309150609040302030702011103070606181b021f0e0d030501031202030408070b0c 80
    0x50304078101240c0b1044440c1c51000075510b14884009800c6842450050b007034052082c0d00f1a8100c0301d00810007180390741007185e5a0001c00d9000442540565501e000041c1ca4031114003a100c01e85158588c096203064508040c080e05440b14141c1006070001402c21003103100301303a02c1c2c110403802031070310b10440481d07850082004408440c0646548602200000310a070340040c0300c1d00d0000310303507030300748119207500e4103001c25500d95400052031100d0020b180c412a880c5604802d500200040840360b00603525000b003009580180da24000d10703004010b4404030702400c0d05081e80c00c8902554261001e02d8282c900a40724060f1050003810060414804003071641d00b00142c514850700100c082141c20380d00c000e0415156043e005c0202c9007804d003060a0501d190400c4080c1c404001500034040a80c1483d580965450200740343c8142559105002c184052007005a000c00c2d0440d51400283c950450800c501021414040b5104652041009018181c00840d120040350302840790b0039120079110b440d80c1e0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 85895118 1250 85893868 85893943
    0x10b0328140f0c0a080106030b1815090304140f0612060d0b07020102030615130e070c050a0503040503280308041707050c0f010c050c09070c140106051c0302 69
    0x9050b4031445078207110b0300401045418000c0002c85102e05003d550314040c0c0e090340c0c86480060051f5a5003400154840400402d00d48101c8910054404903a05240c000a84400550f49601d1076400401e003800b6a6604820004092008460313000043e000600000d60a220f259103518045400c280840c58645810b00c1c0c0302103843e4401d020090603e46100024005e4104451151141070305452032505410719204403405800e40c4003064824900300919601c14800181030340c42000f0500c41d8520106100f8451801118413603400796a4031131500080500e484032040420841c104104501075010024511140c0d0595060034550f038141c2d00c1e410100810380840182090981001449204124000c03d2040c0c040c401103502c144040f02d00e01c0115038910161030700801a9003d000b464100346403c0c0c02d019404201032404800d100045d6a80360300d03030502d880c1e070407050340e450301014040c1d0315202000c4400b0310303414810304101a40c03d440080d52816148100071451b1150300141000345400340014 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 85896368 1250 85895118 85895153
    0x14010c021302030a06060c0f06150812130b03101a04050a0905060406060203031003140c06070b15030309010c0b04020a050a1712030112231608010b0328 67
    0x180420700a041e2600d01950044401d1038515241840200f11203000309100c268250b00702041c2c5403040c03503a90362400241400c5024120050200d8800182007408000d484c0400b2424014a0744031071010040c9403055509400c4801c0201c018807c1090040303110318074000701c80f02c074104982002d6031499030300e09501c00c94209035004410100003098803401034100c20300a001c1542d00304407250b5601801c0340c032400107035031020400e01c01c840200003103036a2010f0280d00c84013141c1940c286600310400289540e21440048035101c20070b10800c1030a403c0c1c9100315034520700c250055858440a040000c011103c070200003000965000d005c10150b413619002240642005442900c106468064200c5040302c0301c220407145104d16070405030426901e4042c0c0c1d04881d0f045031803030b076800000ea4411000210000c03500110380c100c54642e101e80903040085681c9800e81811140380c2ca42440c0046003520300f5140079502aa001e0503283ca60044000d2030002c1c042411a2200035850039454440c59802a10381003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 85897618 1250 85896368 85896379
    0x616050d020f12161d0307050d0308091c05122806180908040504020a020f06100608090a030e040203060102010b0402030f0711150417070b07020d020f01020f0414010c02 74
    0x10003501c4881c24000c148690f40304418040c181d464034405540704c0280c0c0c1c0360100003501c2c1e540641c80748038000c0919880039401000d60b11140d4481000c22001e0072540c1003507000851400901a00001c240700c3d03101c0024103290310360030488224202810601c66003008500d072460642c0041c19901c0030103020302800c001c00c03c8900303003400200b4410020b0015801030003a1140030345144040d01010740300e011890b9500554880c1024a844200700003908524110303000d60041540f80c40402500f400ba062240240c09090803956003041c40c01841c1035401480d00d203a9600000d0b11101090b00211520f00d030103000c80d40948e0f40d903140340040703004d03110801c5110b0b00540080b09100784222885402481040141e036512401c01107805420364800d00c084402007040f40080100700131948800d41c004180b0031000f402407401341d40f0340d681d0f070f82600c04489200060700440428540c060341800320000e90011040203500381040c0b400d07601e20a204078400c1504c10a52942400a182d000b403151801c1250001c05e07 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 85898868 1250 85897618 85897627
    0x181b0d050a12030f06050109090c0219050109030f0c08090f01021006170607020703080403030e04060b040602010c080a0b010e0f040912021e060f010501030509010b03031b07050d050616050d02 84
    0x10104120110004100b0110307040043c80f010381c0845203c2c51007103500503034882180074500800c0d0001002c0807200171085015080c00404488407551107211043e100c0c90002810907014100141035803007040044041207041c4905402080d11329040c0e60b0350340000c41e690380c490740c4402c0041c0e00e000380c000c1c7c010000074105600011040c20700b0011200340700d514410740e026644caa0000300d03100d5056000041200e00240018004240300d501c48104084001c0d00000b07001d516900c02e05c205400c00d03401040140e44412104c0461035000001c10b409c801e10000c103110744480040040c00240140c0d0a40c0d0054124a0071140b441d61550048440a9000f05241c18810032415000b9190510b64090721600441c03590307504042d01c400180d05100e10f8281c001c0e40b070141d0070040118090a80984511815902c031005603111f59024402400c009044207042000241848502400c08217103a01c84e61190800c0540500810f001003549544000c0340c03d80313038080010501041d61075000e1140c0d82c00e10a0703c040b8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 85900118 1250 85898868 85898873
    0xc0207080f0708010b060a050301031e02040f06060f1d060c2a030d020f060106080601020319030f0e010e0604080703020f06010b0301030201081812090a1802070209181b0d050a 77
    0x5200060b1030102d0005d00c07a0241c4101885007901ca0008890000707a0304100400104500070001e81c404034140102c80d81a02241d000901a21041c0ca0142d00c42c560381c0d80100580d0350010901c00d80e0807020301700761126044043c580800a0201440180120700000703030092001024000c00c0100c82e00d01c1d0602003040080b01480350010b85401680e4020f1043e0f9011f113070f2503400000d00c41c640300810f80013481968203100c02125041009411507065100c20301c0110900512810100111440740da00010003c41c101c003118165540c842051102d0b904d00340d801d018094021600d9035025412142050307580d060740c076040346072401c0c00844045901401e800440c0e088404401541203074000d03030368600c1c10380791002100c203007109081101d4229405007421003407140c8132001070001c1c1c8400070208010b06035184c1118142c840c1c000d0465640e10390000e010011071070540085d5422103240e4070a40c40401c040784020303548842401150185040100e11130039580d854120310500c441c2e00405603403804d909803 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 85901368 1250 85900118 85900123
    0x9020f03010f0e0f131104020703180603020c03040e06180103030305040b0c091f030213090501170307080412050703080403050d02102715050c0406030b010504030c090c0207080f 78
    0x2c1c014111409900d0900045400b94809040c0c021410409080c200341c4a0500865500ca207002045074000b2180384550031a0390340f8805843c0e2503000e9103d02c010400716105819074104242c20001c28140306125118821000005a030143c8500c02c02c0e4402581f591000250b504810030724046450201600201c101541500070600aa20801d8440810340310703482d00f211741d4000e100c2e905402c203000e503240c0c90061686186090600803036080c0140b42005001100f108603090b50071030920785459100400c02c01d6440d80d5052807074200030010b14106115503480d48500d204911901080c1030444060b2018044140201c03001168043d4406544554a24105454030120302e00382d40540140310303d1041c02c15840c007980b002c00c134959000c4c1040f00304c410310310404000c0040301994804e05010105000c40020f200f46d5006a070b44802041d02c2d035103409401004c0c0d03444418682c0c104403051100f000000c282c0e2800c241983c400f2074001c02e402444010407443c10f0403552002889100b08501d0701c1403118003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 85902618 1250 85901368 85901371
    0xa031e0c0f02070609152601091401080102030f0105010503040503040b0d0b120a0b0a0e0f0d2115030602072109090b01090b09041d0709021305100210051009020f03 72
    0x1a000c0d51a6031340d44400940c0d01c0e40b100d20400140d41141c412407500e00340300d100d0117080c0e00c0300c0110889640a00f889405a40c40090300b1011520303584070141c100010a510301580107000f00d0303009520350720340400b0305403007030303106101b02410312101102040410000303000303550103014451065a2a6803542582002918180004c0d81c050030500c5000842d43d02e001c2001200685c011000c0c400d00d03141d03400ca240c014545111501c4260160102d0708002280902850100e18801e5840394000041c400ca6100c081e21407c04030304180e49007070b0015102c0b00b18242403400b1a6001040185ca41900e0701340078025030032000e003c441c1c01c5607400c20600c0c21604113085000f0f5981e44401007225001141c0107407940c2c8107a000d2142d03000c80610000c602c0d89007640003200d0780680088182c46030410160f006103040004d0704071840b4190007155403018400b4450750b00c002003200300c44a02e03101c0c0b940324020f034a4070003074421200b0035911400084e078081e22045180c0001c10340f0740070456549a5610601006400 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 85903868 1250 85902618 85902647
    0x6030c210a06050a050106030c020a080a050f0d021e030403080f06010507080c0a1b030f02040e0102040e04060e0606010311030a0507050c03040305070302030114060612062205040c05060f0a031e0c 86
    0x500400031582501c09d104115682c1021303001032075862100d8440e07641d1904084400c0082100030041a00f1484010028000d040b00c800c0000d6290803c80031950818041c2d402400e031958420300400c00440c1d8484407146d080321034041c180200b620b8080048030584150707030b0040e101305030010b0008041c4400040c0e4900882c010404c0c00c20034410b01e0344803c1c912229200181115a03c0d06c200300140c603050380b240d1040c0c80410001482d043d9103d600c1c0d2001041240c0555200fa61042c2c0c054201d00180031980d8484800d01e4200002d0496404112481c000504043c0445598000041907980110100c07500c1c00b035148101ea031510703034034030300103a0300d041c580022802942007141c400030000700240c02c0c40c043e00008203554100f90310101c5820202c500104030301e6101104040f82c444203403802c0d15841e25000301301004110791402d030507c5041842d469000e140110340400880d0f014150310015283c02c90490319020821001052150045094002d441c4900925003118129604d420030300f071110305003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 85905118 1250 85903868 85903871
    0x1502030d021818010815130501060e1b120c03060102070305011e201603020c09010308091207050102030f0711100309230d080916080606040e0606030c210a06050a 71
    0x6800111a000000030320409407107900091000341029a201503151f8410001c2407008118502c3c0c0c1c4500b13003502c25560114100015100920000402280c200d148903a01c0d002c14509e0038114140181d10031070000c003111120031000c40030841e030b60b109111200040d50040c000340300e00c511a8068905114003214804141071800c1401d45a9910600c04100d080106a0440d400c08400c0890900b400507014012400c500a103440c8640b6941ca09582d140698040e40c40c0f2a1100e92007014443d04010780c048000465201081c100501c0e0781c0042140c039895a641d015580b552001c1c0341c18801e0420f070243d15544280110100202180d00d680546022401034800040c4580c01c0450f10840072401c401e44049a00141d24010081c0d014961181e0403c00502c121114460040994134040e42c4e41e03044001c1c280c0100c8180541c5280c54003490019a15210213025181403407400241d035140729404050003040c2c809941c1382c41c844c40801c0600c00364072070f60036508c014555152402c000c16045543e2a402e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 85906368 1250 85905118 85905139
    0x50d031a010801082d060907050a0501020307020307060e030a0c0b07020108060d0f03030c0917070501022107060b010203071a0a15080a061109060406050301050307050105070c1502030d0218 83
    0x10741c824800c280c1200d5040b009410403144041c8100003010050543c204181c141c065281894101000424030a20151010305001e506100c04c0124500040d40b206045510503c41c03039000d603901245080460300b0500300a0342011001000c03038182421104060b1a041c080c0c078000030306003888001060100d200341d031160b1035035940e501007001c2e041d0f80601c080d110006104140002038041d0744038400800329411305d980c4007a540c4010804c015074401850070140c0014078100041c0d601080540c074020011910800001c2070380041b2101401004030140071030703488030344201e056402072044480a54111486900184801000c00e82c08003007690b4070180c1c240380040844084160840410582d00000082e08400425889600140c8003401404201d51405c2007809016540c04000f4001002da5440e095203a6151004050405070a1350115051000411030000040c1500c0300d01800e5600c0c0141e0701c21524003006041b4a035004038615101454800240c0000d810040c40c500d01e5220822210440807 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 85907618 1250 85906368 85906421
    0x120b0901061202090102030403020901080a03030608060601020c1e090c071e0f03030504020406170d0311030405030906070f06180605150102191109010e07080108030a08060405040f050d03 82
    0x824024070031080010602281070748540c031250010301451005104a81c01c090701d03600003c40c07050081c5d1100d08a81e0110f40368008158040c0100c20051500c0e0b00a0304075403910000103912107e041c80a2441090a500168020b11100218503006107002c2d110380824508888559555401039005440d200101c00303d95200e0302c081810502c00c240e0000d40c0c041104590356058015050103030040364000c0d2a8000070401100001221209a280100421000400c00409001c030b41100303a6905d45082d0410402002c540d0001c00c88055000070f0704c00c9940c9501e2410406408400c802d8010800ea041001c6000c4c00805440c3c03034002c2034012581003000740c64002c012050758100045550258000824030385c148044080d1000c900fa020b00340c4528500c0c008000035110641c240c21003400540100b0500c080b480e809940300d809080250300461510007180300c0030788140760041030785120f070340c440000508000800c010350002e190302c6400c440d902c22810601401402d42aa10300d0404007501c150f0429 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 85908868 1250 85907618 85907629
    0x5010f0810060b09130906141f05060307050c1509010f0c051c0506030f0303040b1006050403030504140a09020a1710050a030b061c0b01080d1706040f0e01020703120b 73
    0x200d8420303400c80d5103082c803114280640c03a0175034a00100955620084240401c582d80078001c3da8032619580811340f03140c201c1e00c0c9208400c44001020001903040d00500040e144c0d0310840340c0194503818259200d50942c0c010500d0081e0f020840300c0704c01075683c00d0203864601508a41040d00c009001400038241e00c01301101e06d03000344014030b03800c1d40c2c3c01e0ba400d418800325075202907044031010307045d100911102c0d02d10030724603401628200c5030205074104210302081c50502002c050201803501c50728162031900c00070401c0c0658091540300c0f440700b0440c032005940f0f01c07910b04000c010160041d51100c1a02c00080e110b14815058242031440c0c8000080c0c1421500d41d40c1c0d0103403030740104240310f61130031921501d00f100c400800c4290000c81c9004504600210025544030207441a94582c0256041603801c4d414011070700030480601542400340034210b10302100362070b4440402d80e00090710f01d00980281001e8001c1e0f45c00744a03039510014201d400e0581c002e101205501c0d6108003408a00c1d00c0000303020 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 85910118 1250 85908868 85908881
    0x250309090506010806120c03030a050904050105030f0d050a1b06090302010507051306110a060e070305012901030504170408070e01170c0910030605071d01020a17090a030605010f0810 80
    0x90025084e0400203416143c0703240c01d940d041c05680112458010540003091440e8001d69400c0e001c60004100b0000310b2425006060150500ba00030b0b2501801900980d6510341d140c01c0c80c00e09014010440c0c50000e4420310001c0700d17040045442030102c10481c01c00000818800c0d2003a4015400c000010341d001c0d01820489100c44840420054a10f02c0e05000304c07003c0440e840c0940c860700600e07400402041141c082c4240044031080900b051901c1c0d454038900711101d40810490102e0420010403000084c400e00250301d050a08020480c0d9445203003a180d150b5042da48880120030100d00440d032554000f030103c042e280741d0046c50385581d8031204041507030180d00c1010345240e4000442c03942d03282850140590443c440720741d00407514ac0c4995601040e80c0e411181c1d8400503480c400c65042d00c00782d05201180c0c2e14003e001600e003000041d168600c07400b042c40e4280da00000005a8040a52030f030000030001150007400421095071030307103040180043c043c4a003a68a01ca51807000012842900c07448 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 85911368 1250 85910118 85910131
    0x109020d0e01060e2403060c04081b0d06022506020405040c09050a153c0302090307090c050d140f0702061006080406020403020607051e010e07030807082503090905 72
    0x1a0150ba80c0c408600d017a0900507800d106104401000c08242d640701081440d008482400901c0c0d03c85003032100c003e1615141007881800c080c9150203260a54a5a100038281e6a800880c056903c5140e820360800c807801c15545102080f40c603070119002c3c13260542c081d10980f03070112028090890a10000c89040210b80038403507000c0710045082000051400241001802c141071084611700d4540e5100f0014500c00300180c0d0700000007a01c0d01010003100600e10b5401d00c01c0c2011810b06032090040b0f0741c0e0740720f1406600c07005592000c0040201e4082e40035125a205101030900411080310081c0940403819210380022180744400300e481c25001040251080c00d90418000400b854030b10101c44241c4040d0041c0e51030f5074200004000340c0c42d460010980a80910001d02040781c4040300143c3c5900c1e052038140041c0d261844600c400320010605004480c0c20844440c2c0320002030801e492140f283c8401e0040190b41c903400010b00360302020880f14000d000c0d460b001c003181d580311149415140c003100d45 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 85912618 1250 85911368 85911389
    0xf1008010e15030624060a030906060b0a0f030f1e0b0f04051e040f080c0309031006210804170607081003020a030b0702010603050106090207140705060f031e0109020d0e0106 76
    0x40d07000e205c04401c9a40311700868044c0111151200081030703207944400c5c04140069103070b10f0510284802806000002c00c100341c03945103000364031b54005040003024440c0008041d00d4450411940c0c016422000300d40c034151050481010403d19800020419105018095421101001030710310b03051080e640324641c1501001b8441400905115124500500880347c2c0100c9084001c0820205805042100c2b002c02c0251b948031450000c0500e0308040d01c151500990900d40b05011049911b40000000c0640d0541c4654907850391402c1d600a000301c0d00054020081d14070202c640e40e030001039440c003030140354680c4815500c61a903440c80c040050700010303401190181d801c00c0010107aa01450f0721500e14030000074011344036500c0e5400d5a200d54045250a0340101c0c109040c0043c406000b18034160040090448034a84004155540501d0f02840c00a500100004102d000700b02c80103c0e06120814015091390307101e40041000b50801c04500c4403040c5849126007046105210350419545074001 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 85913868 1250 85912618 85912621
    0x9040501050907170c07080a030e0c03160b1c020f190309080a0f050912070f0b03040c050f060c0a0c030b0603030a2304030f05060403170f04110f1008010e150306 71
    0x390584c8414003424031901c03a00b0800c8004045200300d0098407c9100e0350745d01045004246800d00d292030300003c1003502c40e800440d030060b4101c1c48640320364112000d0420ba248c8441038881c07e94104c040001d496103545000141050b000784400d00244103441c129060102100b154040c220200e410304000101000c104000504415003d10800300d008462450024038200ca2240400c1d28044007103a030040c40c0d4400c4005010801c6021801005000304e11403c0b419131400c0d03190051000228415035004240440403051252030f040c0880d0004408007045454082507031420030032100c140d01c0241c81da4400c000c0420780c940750100884200364400c0e83d070248804055542032012581030350f1240c018200400002000a419010415200e80104040e28462809060140901e00010306003d914440304041011402206462a8005810000f0502071011401c08240f080c4034400640d82c1c007650005c0c80f4400241c0c00030006059445201c7c1600302070700d40700c80c40da070079401c0d0b6007540d135054000c2c00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 85915118 1250 85913868 85913897
    0x3100b07033f0605121f090302070308030103050606030d030b010e040c0504090908070209130b010b1e0301080610090e0307020909010f11180306010506070228060509040501050907 79
    0xc581e14128184a010140002d500c41c901200400d416002c1d9150791240420070092a1040d0080400c2c5140c90280408080c3c0408840759120a81c80361081c4694481c050700034184200300d94030140d41e001c80c0080d62541c407414040e030703655002c03201c0030f21a1044030760f400d0069109000e040c0c0e41e26010384828a210615004001c054601d400719401000018080019402c185000310111f1a0040c0c8096541e4000c1e4010301c0b955010040c040105000b009048000082c10107120034110340100540710380701c400c10208031521844101a9281d264000f00001c11030907070101e80140104030303210b9400100d41d40e83c1c2da001e080d5078600e0500d45141c0c10900403900036050050180c4d42c0419400c00009100d1160030b107100c1164585003400c00c8032035010030306c0145d003c00302d40000a03294089000b001550314003070016000744034881000307006222190642c4c0000c6404220b0060035081c04240178010b5841c3e06c001005508a03007001845503091000019040c10802c0c0c065024414994480d602440d414 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 85916368 1250 85915118 85915157
    0x61f15030209031c0509010311121b1909050907020f0303150406030501140f10030c0506071401050103030509041d03030408071a040305030a05010e07021b0118090203100b0703 77
    0x41620542500449101c1800041442d046960180304d54803199216080c1000060841c0c0c50080b1184107241c080107901d212804100c41c0302d500401d40c03080c448181000c07016081060203048151160307501080501c11100e604034011a090720030a45101490781e0303d83e40d0072039440828051032101c58000304040303102240403c01a42d103d901c05000415101d9884d80d1300c0f801c55501d8484040c0c00c2c5c1005c018001c00c203860504158010019452a044186c110340300c240200c0001d2241034455040041c55500f082024881400000c0c03103200200259a96420081d10542c8030344415880f4910b0302c2084144400c980d0921401801080010b500307540c0c50340d55040680c1d0000b0030543d04568410070f030103285900e41450034410391003655005e40b00c0c00c09070491410743c1c0040e000310100796000400c214102d9400140b40c022024005c0000034459120801a10740c06071406500f18052102c0c24040351a100c941c0085011b0500c102103000503682e1110f41989501420400a0020381b03030788a40c03004120320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 85917618 1250 85916368 85916377
    0x906030307050610060e031c030b010e0d0b04110102010c09030f062702040b01050307121104050307030b2215050c0f0d0f050105090118020705010905030c061f150302 73
    0xa81200d240c106203440d034615094003200d0300200d42c0c4400d00b05021a0358480b5043d251480700f80e00402080700e81d40c0e055401c100304102e90f841055a20031024503070782c0c82103014400700c2c8000781c5004200489070411081e5600d040360142c3d41c1d0f0311001190707841540b0505c10a8103801c0c5076581c00e6500d034119613400900314150030043d07900a8075842d42100023512600740081550308140465801d054500c140001e40d903604110905104051082012407034001c04101502c070081400040c0460701c081c1940ccc094025600300c0c0340c05109800f004070401150020150046114049840c41d111030b0042404020300306480041045c0060005c0b04d1040360309800440d0007054104000d82420120302b090032003508080400c0d0055600c03010b00c280030604620806002d08010b44001045604000344948001c400e5850799200719030000e5402c4c10300c0002c1d0306c1074040544c0041641d544208107216242d60707080546007145085000c07403030000b107815681c1c3d0309411645040d0017504401c1582da0250001e401 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 85918868 1250 85917618 85917631
    0x60c0212190509030f070e070206010614160c03050d050d060b0f04050d030c051605240a1407061a0a080c0f010f0c0c0603020307140301030203030409110403080313060e0102090f09 79
    0x502d0b94000000641441a5400f038110847e8100041c174107414001e107041c0040e4001350a2014404802549900c402c04880c41600021341c0015140c0c00c0c2d16010207902c0850f400507005d4000c0b107005c40c0d40c19602100074611880c40d050140f140700d4440e01c0c010709512441406440c03000d8100410085410064403921340c0501070301740b0403443d80b100d44410341403019403200401e41641c40d1400740642c0c0340c0700520a001c150401013001500f41c4a05e83d059851051b0000302040c00a00170f2180010035800b800c407560030f40d0000c01805550050b110a511800e8001c00d035a1081501d0800426681c60010340240c003918004e00e2648046a001e00554016910100711010007c054a00c040814046500007000300629070b4010303680c0c500000010b0000e20245181c8e215503404200401c0036a400200343c50a076501e075a00010081021140045184a035034402010407001200300203003c001c00620314445030003814140441e52444900b18200d03ca01c0301c84661007140446040700e5814060451640040c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 85920118 1250 85918868 85918873
    0x901030902150a0915080f1f17060105040e1b132a080a0905030301030b0916090603110405010b070f03050d0e030301030c050d030c11040207020607060c021219050903 73
    0x3540e009203105541c0300c1104000404c200030000c00c00044000c2110704900440d18112202e8100f0315100c03400d41c040a4410b02000901d4138000074190010481d601c000e18040c0816042d9400722950251115824424284110f1070420305a10611001c00c1c003004402030640540e6010000c5010002083c140040d80042c2c1e5964404441d0304002641941407a507082450300ca0b070320711394480014a1880020135a80d240c604220764040003038000420340e2705403075100002d201569114041e2a10f810614400c0304076020032250001500b9440c2e5102d10140da020b0100140c10002d001c0500041d20006e10420420001c10080e04002c905544900b03003540740b2030315116150540b181c0d504401d4400000700381005400c000010410004188005002007c0545088000c0c5a03591000340050001c803c003d44941805171080105030f82d2581101e40040d4002c2c40c00740c4862540c284071009010140d056030261007507194042c0c06c910745006075022514220401c660703c1100040884503600000030b501e03090f1 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 85921368 1250 85920118 85920139
    0x30f090102040302040903050d0b03012702060712110f0c011e02010b09070905030c0d03050304020105070309030f0f060c09080309060a0306050607110114090a14210615060f0901030902 81
    0x6031780e64010000d00b070380a51707103140d158052800708000b00c84000c00d00c03034803e80c506101c214052500c1030318807140300b0010b0406295646a400807c0003840340100040420000c02c4407040a03503007009a055811a80100310742c0c02c000c46000031503443c1080c114188c08070f420391255050761602009400000a00c61001140300c0a075200401c40040e81a0303424408500843d60500c01030904022403114508110b030145c0c403a24007910042c00910004e0006410443c00040d0745007418014009070005651003118902800880c1c185261904e05600f4125001e50525403144101403141200b10140c440800c0514540084e040802015070300c90840f01c03092640358480002d01d96079210150607200c0c042c0c2e00304004400d090f0001414490001c00c0d1364600e540900c504011038440b5500b50041d101d2000040504052084c0010104450750304003c40c0c41400712602c0c0700105001c01d030640112003203204d10501000083c00c10100e8040c950100c2c8035114203103c4090558401d40140e0121400940000e182 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 85922618 1250 85921368 85921373
    0x11b050a05060a1b08010e070c02030a05060c1312050705041508070b04080705010507030503130602121f0501020703210c0f0506150901080a030c030201020d1401081e03030f0901020403 81
    0xd01ca400c4600c0c9040303c1e138606903078108000c2200302201c070480034503090308607604018120440c0e41002c0e00100c1044410252401151000c00160044507000b0040b504c00d0b00e0184209281d44c2d2080444541d4660440000100175a86041c0705040036400741c050300c0268241420320009042890031040c0c0303100500c100040c6000240600c101800c0c41810305507445040c4801149040c42075032102e030422030108201e01c042540710b0141d98200302500015134528170982400d40180c080c000c1c3c07000c088840c42c1c1c1070008100070003111240c281a1011985005943c841c01641c86200c04c4c4000740c40107507103482c00d0090310102c0320b4041195800381802d00443c069030725000240302d44001c08440c03a520003070510108204a8803d402c031080100c8480e42d296061058481d241da280880040900141d0070300e4104150017901030f10002045582d04100c1800d00c0401c0843c484000e1185c0200350044041c040074181c0c0344000d8800e96052203004528540f90103150000c903050081a400d059542444003000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 85923868 1250 85922618 85922623
    0x2041b0215070219030215010b040e0c0f040302130209030607080106020a0b0907080a030818030901091e0905090c0f030d05030402190b040f150c050c0d080c0a08070b07030902011b050a05 82
    0x22140240d006091510b011641f0707030241881a04107040210013031200700580f14200e06c5041d0301088205d00b880e15070044000100310760007583c00003544400340708902c8254862a9024050855084003140c4860700d8404040cec0d0300800c2030081c000143c00000c040c201117561139103a2500080a07204031104140d48511003030034491905d01c1100002ea0510030301ca502080096040175079103180d0302540c905883c20001812030340041c4610445200c50501c8880c0702d20004d14a00c00803c201d041c184180e14011800a4035070710010155031188001480100c014140040d4064200d000b07511110b285403615020800e174503d8100c003c0162400e9485d0118203449030601510043c491500d2030100c030ba05000d0054040e07003110f0201e10400142107007250105d81c0004043d80c03c22070588100840042e907040080e1580f0034084e070a580c62284040d418100070304000105000707070181590401e5515422411426502040d002900042d07012007496041c1d2911044104004c1c0700d24200d0304e4104095913900d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 85925118 1250 85923868 85923913
    0xd05010e0109051b060a0f050903010504150e150a0b06040b0d0c0908031303080a030b030f072603030c0a03180c0303090b041a03091e070302041b02150702 68
    0x903a51a410441c04010080001042c2c2c03c68409204900307a250602007445801411b500408001030300c4201003456000b0400c80d0403015000c0c0003806a440c0c0341c2880310200c0c0d0074200b010b040d01e03d40f5254481540011581c40805803d403210b444490712540e085001a02030444801c3d400f603030400c000034840180c00000c00098002000201f025160342d00003420100c00340e4400640b94204000d10005400304040f82c1c015243e00c00c20090719404407400c114000c09442560903054410084864090140014240300b1640c86959202030014445002905a1010b2000d462a0340c0240081005565404090304c5040c519140004038504480c0d0700700013400c036a190544440304503950501c10b150b80603041381c014140940c0a40c0c5403a10f041a44100c001c4c400740d00046101c80440429107500080c0300100c1c5e51044405d000556411401344a500c40d25148400c0344583d10b4451100c50b49ca040c6110701101080e0342d0041d10400003002841c3c1100321000700940114048c0004640c2d450b43c000c40c501 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 85926368 1250 85925118 85925141
    0x150309020f0a060813050708030d020408010c090815040f0803010308030406110a050403170403021f020c030703020a0b03151005070203100506030c120a060f09030e01030507020606010c020d0501 85
    0x2196114540c01030201c16107000a8041c050080750724148a203a400c82c0c500354203e441e0f000011940d00b03850409508064943e003201c9118013000451100c07648503a00078006840c0c00e030000f0441c0c0308d0321010a407040f00480c410301159401902c5400824502201004c3d4003030b015044000600d02107030b40e101c059500076002110704900c080140001d001ca18401e04031509960f10710f082c507240c0c1a040250140c0250f1000500002c158841401c0c40030920342560019039002d801c610060440c04100c4440d8914041c1c0a0010710a40013000d07441e280c00560002100d401804080405042c080c02c41e259600040410b1000c035100000c2c001251a900310510340ea5256a03184d9444045500c101030400e00c2900e08100050305213401d000169401046600c03850104440704c5440d402036a940d1400c0814001e40a0f010310f1074242c0301348641603180c1040c0c00340c6102e55078010106c02154010b50488e84180c50031030040c1d1000000442c0c41d4010503440d920f0600080c0380c1c001c680c03456a01c079801d40b940e00c3c001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 85927618 1250 85926368 85926371
    0x1b150e0d2601033201050c041d0103020a0b090112020a09051c0b0c090120010b180c0d0504030c050703121710060e03030f0d06170d1d011704110a0f0b0d151503 70
    0x800022000c0140c41d1050740c40709d00400b040e54910b800180740907415010791404020b0000b02c8236856030043d03407a80ca00e40681001551140720280014144400900c11540145130102c41406004070700c4040d5482241d102c007140310340b0385840c01c01c0c032025001480c0b91410710103c035101e640b00c59403841035103101740381c0030780041000c003462814041400c80c02088202e115403401c082c04240719000f0b00f6a203a040000c0c100069640e01c0c4e0a089581029900015003140102c00340802401380d079a24141804c00140c81b035440305503045642c0101100100d9104000c0d010510091018500c00c00103800c110340018201d07810548a540a81407a0703000420004005503620003c12856004044c00116175900201800716803140c10700c082e009988880790052003030440d50550b00641e0065400000110010080300060701e010b1506142402208620074403030100010000f82c642075020650003580ca440764054108081524080c026008850752180d00903001c12010528050084503140d440b25a03a80 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 85928868 1250 85927618 85927627
    0x1c060606031d07030206070f0812070e010503060d03081503160f05061309050613020c010207060b0906010903080705010204080607080403030c1b150e0d2601033201050c 74
    0x3001d002c036211038000402a06002950708000d82000c2005000c49805071101c1c1d80c1c840f501d16100075201600c0c000109503507800b24200f4452105c02201600c40d0388551266036000d860000152540d00040390314a42c0b001500c030340000060300c10200150030407128242d640c501001800068100220840c502d07605040180c1d080045641c140e81d030130006d20054950301d1410030088165400c001c0180103051145481d50f0100d6007503100c610718103880000d070b03400840d12200007400301d034080d500882080d03c1542c1055240483c0d4034025102c5801078405031924402e0724a96580c0702410b030009401668255828040094070310002d00466100d19071366a00c0e40c5003854140f8010f0200d8685040d61800c10000442c071081030300500c0d00c00c2101c5a0401101000d1703943d84096003000d40351002c620040d074015100326250058000042e118188810000318440000c082e02c0087c2c2c0b40c80910002d01a01003a11011a00045e070489403a1881400c0c44d24003504003031820614251001680c016404400005 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 85930118 1250 85928868 85928879
    0x120b270f0c091003050601031202031e09040c0905030601060c0501020906070c0503061312082503020306040614030a020906061611130c0206011802070204050114030c09011a03061c0606 81
    0xa035a1544a10080240c0c0710343d604644415a584405000062849640c104030055945c020400d8520440344211a1204000aa00882c03903d070051036000e4000c600300b9940c444958003450000080c1c400140007004142e107440350440341d074100d40340c0554065600b000018165102e0100504d40140208200d03514640741c10f003071514000c0003e2590781c106041c05070b80710000b40000040401c00210f46003498040e16488004d944d666411400700c40e612440f20454111542c064000d1440b44a04035401c02045548101c00188020310b4112590b06130018440700006292804083d40c002c0301c0030b03240e54108078807440281e0407400440010355000c5e80e0b601c05601d842c40c00c40000b07070001070403080510640e5441d22000e5a00c0c4418090f0f000021031508054000389441d0f0b040d00c0810703030024001d000a503560300000e0081412541030a0203402180c14508050600f016400e04a51050340305003101030b09055840c809400c090201d5502c0100b5034400e079681102030404214841c002d01c800140d951070321 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 85931368 1250 85930118 85930129
    0x421031403090a030c08090907170c0a1b0f05070e191b0e010201110d0504050709020a023403050c041407140d060b19020601120b270f0c 60
    0xe480c040c0300810104200321400c040810b50303c00141d0f15003050a80c20b078481c81e00d4501c0e4040c8948117600a00720300100641954020300c1c0e10f0880c5c00d4030081e1061522694414501446104101008582044c50748074000300d0ba0741e060b000203801907a0303010500d00b0075580c003070501a0640c070004034241500e09221546c4007020301c5030180f4400c0c410810a0a200002e855081c82414080f007060019140e1108142d034000c0d00850614905041010351b540032003604030004103816a0144c5061084180c04075816a05108442c02c0740c030030b0303001403003d25101d8040030341000c81045a0030a6512a0011103440801160418061132080002c2c14041c490b00c0d003440201c4030325034405180b40c503580040c051950341082d5403e07165007140c2030495613290131005506c043c2010342d11201ea600e10014924a40d030290140302c0c07510003101c0d0300303449050340d89280d14054416030402c05004100724501040080340f4581c00d0b00c180036050491845880d110300f00d824144040034a00c0ca0b01604182304000d61450417 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 85932618 1250 85931368 85931387
    0x50f0c010e060f070c0b0a05090a06180c1a04150201060803030a3206040c0504030b0403051201060503090309060c0c040c120b030616030203040215040303090914071d06042103 77
    0x1601d08103002e04819141ca2006c0c89002d00072072200781d610310200790107040501079030b201c03107812040a10500c072400e50b42943d41940d441050f00c50b40c22070807001c144440d1650305403400341384680d001c43c14541455089500c0c003101b54170b00415903503601c500042000d01132028512482c4111800074004c43c01003440c00c5560024070010907160724072030701100c05441c1d0912664006609460010324100c0e20f400965a500c21500081c202180650030003040680c05001030060540c0403c14201c181d03690f140543c2c1c14041501d20782001d400030b100340c40321410040050304d810000841155812400c410106007287d0300d070811540060084101a007125145009a2504c03400c1036000702103a00c2c0611542c0c00d41540549000101030f00040468199601c040ca0040c1d682c4041e80425640c039030300d140141410b540c0d48a10f410090600e02d01841615426125a1240c03419403110110b500b010221150b4081c20142aa64801414030001c251000d10210064442502c03400c003849524190401030600d10740f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 85933868 1250 85932618 85932631
    0xa0b1014040209010f14040e010b04080c01090807050907030f020a020a021f020c040504020406050901091b0306081903120612020306060303030103021e0a0306050f0417030105060a050f0c010e060f 86
    0x100201d001907644000992481c034601c0c509520182e2a000400b01503110348d178081044c1c19030690011484c42c041500500c12100504c045501540981c8019680c460280c81240e80039001103400b00028145200002d1740000d803441c0014080c03071044102e2049070405c852420050b440400e035901103042210300007954a1840c402c25007000003e20009660f1040c08041e14012902c03140411704545540e004480600703002480590301d0360711601d0100080c00c0031400e000d804094004d00400a40c000e2183c4400c0e034a04001405501e8a5810182c4001c02042d40813020000760032603601803665244100340182a000995194645c0c240c0101481c0a80103401507200e81c004000400050b07441280c00c041c200054090100041402d40c005141c04070340e60701c060b040301c1c20301e001c001c800c0c0c860002c20340c4154495500c0b1000c0b0080c404400744140400d00465410100c1080410381050050300540080415401c00626044902020900b5540c004e0481d1681707a03c6041030014101a20010a50080 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 85935118 1250 85933868 85933871
    0x2070816031e1e12020909040803071b02060a0305100e01080d1e0813080c010c050903060f01150e0301060312050a090801050c0409020f0904060b0405100e100305090a0b101404 77
    0x2a05540343c4104081d2180300f0320180e9030315681800125010f0f503105200091408042d4070781410080f13402c0e8802c440c01800502080300c000002c00303c40005840c0290044c2c195400c0c014000800e070028540a485044c0c6540f00000014000e9011082d00b8041c1000102900c50031030400c0c40a4000c45807a178181101744030200c80c03583d00e00d61102d51958401c030210003451001d0103c1c206050700744078844000b0380c00d5090265120090382c20400034004640c0a804498550356060030b0302001000170700503407620500403070f11480014401d40e100c0e04407510080c00010810750340d40c3c6007800b484460f450350020840c04130340700000641100045009100040003800989440c109100561040b401a051503039800309000b040c0d03542000c251441101c005d04100800742c0c035140704c411150885d2040e20311800c0382e0031403a240705205003440401e805007d0406209070843c20f0080e40501002818003e00b40714200401001c1a01c208840d4043c40e01004404601805d1a00d07003200210100c41c3c140c001c1c0d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 85936368 1250 85935118 85935137
    0x10c080114010507150e0703020f040b010804080904060f080a060b011803061a040c0201060906060e18060607080d090203070512060f060a08010903090f140a0902070816031e 76
    0x894074200c0ca110824003440d01c0c030b550744698944041103402c0c91900c030810a142121107001c51000048180c142d038000c460382100000e0a40412040e16004a41180001c0648000c02c002440080c0901078808000708040741060302c40f01191a884420f51101c0380d00d90002c10a10b080c0301c034610510182c15000e00e05003c0f44c0d000307541d40b4401113a10b4070006000590301d10034101ca1050980d500501941c00810038040100303010303070003400303400320b400380c001c02d5442c0281c001281c90141c1d82985540f00050038818901100c0324005110707480051180703801075000c0040c000002d0b0343c00c1c02403024410705480000c2d00c00e1107005061403c400c41e00050b02030048082d030f42140c0a0005282030f8009017100791443d099071001e020800803401580013154540c2404c0069041580200001e020380f481040395442c1150754003560710700b02600f010540d4129290990611014440303030010074205000300015481e244803040c0c1e5200c900440c0c541940024803401003a83ca070410781e80c50031000e800340d18008002 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 85937618 1250 85936368 85936379
    0x180402030103020d081c1d061513020d060306020a1710061d01020114280506010c080d020708030a0c020d0f0503180a050307050607110307030203070f0303090f1103010c0801 76
    0x403101400d8041d080e1900824010744407031622101c0080e4007a02c010901c00d64290342da40790080b40c1c01387d901c00c80324003a0100040502c01442040300305440004c0000003030420030b0310750b10001d40c41000e540d1103c079141c40010000c241b540c0010031000980d41d8454113052000300040c242c0d180d0142040e4404036010030100070b519408003007010302c01707410100d90604038045070044c0d0041c8040402032034041020420803120b401c1c0300c50850692054405601d03c200304070f0300410105c40d070841d101404501d007285150049000c0b0005803100141c0760600500d44403060711341140b00d810841355290314645a24124800c55410300c00711002c01803504140602c00040480600706000c0100668550000b60150303180c0e803003003040a80e05264005058982e103031014107009440388800c0302c61201103889104250100f41e400000c441540f90141d026500b411031a5940c0803074414801810b03010561615080c05c041260182e910740380b40e1140c09c0c0710032001da8010925003036039442e0035110280b20110004009 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 85938868 1250 85937618 85937629
    0x302031c0203030403080a18050d0e030a0b0c250f030306050904021513090e0a051905060f0612100e122506020c150609010f03150e031e18040203010302 67
    0x81244e41420102016691000d0707d0008284041411701210007100500c0705000c00482c1400c06920302c0c0e5511070455081001f4035588036022400107005080042c000342868001c1400741004a4112030f0742103241e1004a580154007144080a40711052020071000805404d44106402014180c404280600d46a0001170b24540c2d03032010354405c03030000281d10000b00b1503c42c0ca00b016000e00780c4100700000d01c00742d0072603036060079100482e550b124000710107071001d40490804e82e07260307403180044ca41551980e111040d01030000e0140c40d005150030400301000c030001e01908245c04c43c0c410000074015860b001c424170b05010348a07001078a150410600c0350b0004012803c5650b411706100030380c0180c144e886e0100081c85020559842400345481e10304880141c04071440c000c023070132500914566280c1051405032441c13440f0060264000691920743d4000b030785c11140205c3c1412003540d0419080c900000601c1035004915040b0b0280010034104c07894512011014030f82c0306460441c1950305540c00300d035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 85940118 1250 85938868 85938871
    0x411040c0f0206060d150204060918060b0d020c0a2102060c040501020c0103051e1003060605040b060d0c120203090d0206090106050d0f0c0801022803050f070c0c0b03010b040302031c020303 83
    0xd00809401d05d508040c0500b02d400058400e041e50011075407550f4400e40100103114174044d034a40740505512400c00300426000d030340c003035072580301c020b51038110031b200010002d43c4281002c600501a940b1014080b44011160140d0608104600e009102c003061000741080b100400c08a4401c02c03d000c05e04c8266800640d145034010282400640c641318940c90390b078440104a00200d8540502041110440e0303520100030441380300d10418000f854a40342004261182042d0031600201c05001581c03aa1440d500900843c4d40700342010420114105000000d030303071040b1010055540f011060043c0760364100f12003584050840020051036040a000581140001802030100110b2880c2501400499551100146651002195a8440488101d41160042c00721401100002108425040c0a030151600c81e1851b281d001c0e88980c4c54180583c0c0813140401c05490b905405280460b41c0510301c001180a0b14200e941c194413503246104041c070b80102d1400c034a14031801013252400305178000040c0d0303 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 85941368 1250 85940118 85940131
    0x2030c040501140d1112030901140301120b060d0b09060610090b0706020c031612080a1a010809030702030a050f1c020c011d030303041211030a020303060d05070e0411040c0f0206 78
    0x4d0f5124201001080206800c0e03691040007440350628580002006011060003078840c002e0815124945003094002407203020b21019a40a007039000689400415134801c10081000c0c0e952881922400c88104045814018a5001c14203002c880c0c41c103210700329010603042c5071509486003090b0304003899002e1140020702454000c90404034403135043c021f0b90441340c50400b900f007150040b403c081c0101003048600384003180351040031944400c124050740300c5802d8401154040a0740040044600c1000280803600500091041c03000580d0103000c910000c501882c010000d82e002c004000e81001d243c036980410640d11020b00c45622900486e420452040900700003003034881a1000c28503400303c0c2030f6002c0e4107000000c104810003440c002e80440828440d40c4244088a051581598a10441c0d0988015078418800034415142c6444006261440b070b1055803501c90381c6540c029203590064508403500d8003141203d0105040c03d2142c0503040f400b40c9407005001010400181d221040075008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 85942618 1250 85941368 85941379
    0x303180102150405030d0630050102090604080703050d0f0c030e031002030403030e0606030313091a04060608160203090f010c030212040b070218010324200702030c04050114 76
    0x4840341c0c0240070420a0318030500c500103092900b80792080d1030703a200700c00e6510000c2c070b044800f2440740c40c00082c0d8104411101548009104500707031041b02411070480441e0b0540d0208194070070f6071115009480203100044c01020a5401c42c41c04500302443c0c030701e004042000d004074034101650301c88910410917805040007170202410744042410f06070b168070f80100c841e00000030701040550541c050010840840c1c103580d05521403404054891241100207000002c2d500703030138000d076482c552202928108441c601001d040e01240401c066540681c800320204009100b00054940c03640064096021b03144055443d0662550005801d046500c408038100701114480702c0406008100080c0c0f1801c080c46159125543e82e800107405a109140480c00303091070300c0a5400c04c3c3c41030309845050329400326901d001c11002032003503484c0d418280106011241c07100d018a10b141c2d0345a10150480c02800c0c4a50350b00d003401e005151030b10341030b280f419000e2850000108803400c0c030265840c1e605c0d03404461 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 85943868 1250 85942618 85942657
    0x10608100608010216151107080d0c020c0108010b09010e03010603030522150f050c0708060613020c03160201120609060603110a080403050901121515090e011503020403080310140402090303 83
    0x4000403e00760800d0014007d000800c207041c00301030000342103030346030811080c00800346144040362190400c905141c0402c2c984001408000a8000030300441c043c185024212850b4150000e82550300f5940183c0100d580000c941015401d44103185902c02280d002c0300031020f1a2400000d182c5100d1070300042003102c122101c10006208504440000301c540c0200c8540d15228402a0344800003907030b04038482c017030100243d180fa129078004d5542c4405640301450a0925000a004128400210482c10042100c0c5071900c152498451030b00a8101c0450000f80750b82000e5018044580042c24184201c0c1b040c04411003050340728210541c4a945494101c0d124404032b801078422107010340303041e600c00b4103100d03121b030018031a101d805040b40c00c88260058004004902683c4021081c05000c4406030100010b016051621000341d00c030100d81d20300107250580e251242d06045d003042c1d8041c0108080c0c11b400308402884805542180b0100b183d046191990640c0026a20310809841c940c061501c00d0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 85945118 1250 85943868 85943903
    0xd1703060a050607050708060a0c020307060b0a1503050601020c01090806070e040f02120a0506010c021509190e1e0613050603010603141c1b0204021b010608100608010216 75
    0x4254000602c005840161218401e00c2c0c01034030740c081d81c043d54115100300c2e4000b03025810b0500505407a50341c56000b4501d459019210080074000c035141d01e41d081081800e0004154407001d145c0c152110255800040038100940020b0a0a00c0c2c54070560407c511000c0038881c8020104585410403514144180380806210128000e041d0140001052a1000c14030605c0c000705504020311401c900700e0100590345d502c4c801960380c06a08030f40a03400001c8071041c980c0991000c0000c00f01c03144020315400301285440f019031034204180c0c12070f0940c8010314040c04805203541180d4910580140c185a842c0c0c030300307140403581143c1802030448101d0f0b102c0d03012440e02e441c203600c40c0016582104040000568404d002d40d074881c185c2d94030b04d02c90800d4000102c00309109000303008010700d680c074032405240f801d9020000070750070112914100082071030109070300d51000d01c1840b0082c405c8001070f01a001802c102c0500316001c540c0b0400490b4010000f05503c100c20740300c50262030f50b0007408400080d4501 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 85946368 1250 85945118 85945129
    0x180603080c0c0a0504091a04110603011d07080702031606020c030c0a03080901020c060429070e01090602030c0c01050c0304210c1202030c1014070804140d170306 71
    0x2940003824000000884864400700070810340180e00050310800e00c02907599092000700e44159070061f01440c0650b5120191103205a4034580007030103210036203195003a80300040c003030354002c2e0f10003d185080d402403000d01d04401e003071180d400075030360401a040c0d00d0407180103912031280300084180c0314444c0d28248204400c0382d0603074140c8100b0750110781d105c000d540e005558514580c2005d8002c0303850040050300721007050003181d52540b00d0300003420785a11a0380c1c40c0203401236002e08040b1004520f942c10103000802511840c4030305010380e2400c400e020840001340c940039041d005141103410802c0a03000b04203000a507443e00c00001c3c604142c0d10030003101c2e000e00b140580d820038003100942920b03403c0d50700038040701c0c020264050b034071452a09660740780482e00114050f0000f0340640044681c0d016900d0141a003000100807801c0140303921107901003811160740140c40031181590f01190920415241004680d40b034001600d481c05420b15a846d55050300318080f04032800150000009441d60310740c0c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 85947618 1250 85946368 85946381
    0x111c0c08040b04060206090f0304031b171f09020109120201090b040605030402011205090c090c040506041806210b100b0d0b0f0a2601021b0303070306050d0305030118 73
    0x48a44a919a900c40e00c62034401d0f0701c10b1040c00c0c01481176501003110544086407684070401c0c610011403a00b0b15540d1101c7c0548003211269000244107500090400145825806521a001c01409610a0102608100e182030040d101c0b0024604550080180d8000c3c42550640d0200c45000d8418039140c40100d5100320150040d80d00c039040841d00190494121004e10700888c0700b600d0b01151008550b1000c41120000c1341d50403000d5200900380d1100303040140495810100c40c0280918058a40e0b02107403450384150300c80040c0b0050507105903c4060f5501c00e41001c1e11909142588201e08403403010410000e400004c1c03d0b4068072408a0089900e098199000b40716004c0403640701c41c0c10492040c003c009400d0900e025080480c08132000e460314050076010784941600d01e990041c4070030540380e2801c1c0c0400003055159400c01c0181d03d070f03151000e83c1604d20f03c140402141d0f246460b80c0001c0a580c06a807000d4040e110b181d480800181d04a01a039065072440040b2147c501c0704550300b500a00754 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 85948868 1250 85947618 85947623
    0x40624030e030f04301a04060603120906031103010803122a07030f02010b03070603020729040c0b1c0c0201091b06020f0c1503040f08040b09040c111c0c 67
    0x1d00007905201c0c0c100b564003468080280d1903034030135200400c17030f0b03003038401c01c0005101070100c04032044040e01c1111203582290240c100000c5d074603140e0b5030700e20701c150202620f03202042800404002295050103502400a4100300341410740d49004140f5950303010f03155038507d401540c8070008500100f900c4240c1c1f0058400903000000005d8040100c4a44c0e04c070384400c0d80068000380c404400c00c0d005008062180501070018141e961038030008030001d4200c0041140e80b052480c1d224004818800091203001c1d80d031030719001315801c1c60300e400c2601007295400703002c184e0003d200c098812400d00b038252021910b100c4001c50055101c80c0202c5c0109100c4400030888150302c3c1c0d1802c81c40419002135000e54403960200c401d04000c0ca8011541d407006480740c1a48400900c2e1815803007800100032b590002c2c810944800500fc3c0d6954149540d0030a40282c0c011031070104084030719187c1401816074a07546801c0115040041d162010313140c415900c01820403000c0c41d00c0c030031103c42c400c200f5106000d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 85950118 1250 85948868 85948897
    0x11e0f14060f2511030a0f02010806030f0124050108040503030a0f0b030a05010b0f0a050607170415020d03061a1e0d150806070206090a03120204050d080702040624030e03 75
    0x10004111007401441991003544e040120040e82e214905001031585417031a000800140f014403698011503a108000f0f1000b40c150103184160822500b09008038106902c001507142d03091600b0000361210660180d0115040168440501c030129501104580d0092800d01c00480c4090440071a040903003240c004141d050300c19000400280401035001e81c403040740c00c54142074014210410000200c2d401c0c01441d80c0844200200c0d00041d281d0f6980d00305030420341c20070504155803501a00c4501105c3c45000001d6081034800c40005903140c840c4801625080700c8a044020300d829200b00e481c002c81ca007101050001c51882c20f403c0c03c0045c280c1d481c1800026050002c0d135003007c8d0181507061680f03d6525075200c0c03070002c08c2c1641d002282c4903205040ea01c000b0f0030181c000d134900f01c03101c3d0240072250a00950802c0042490b46a0442001c1c040c1c4c0503007505c0b9550b41d2070740b040c401190180d5100b50280000441c4607004200d4000b07081205184610b804200712808143d9281076110b00403a820030718 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 85951368 1250 85950118 85950157
    0x20a0206070b060f09060f0105070212010e03041a030c0708090109050406060e090c04030b040b0703090f21090f0501111e0a12050a0f140909011e0f14060f 68
    0x401007210350b100303c4041d50a40c601d101d5000600500b40420782e501c59001d28561030303000903035102d50050302405000400c070301c000f04800601d040c2110b420060140080d000014240102050038807108290701d1a0704280d4590b01d0850380700581030294a0b4000c107481c500086041040e886250130070302170140200100001a6248c0c1c02900650004070780c0f901035460b00c1300117541040440c055404494002544820b160384554555010001c0208204103260b8ac84410001040e02032003004040c1d4890700d40149000300c000c03d11001014281928010803000600074804c04078a106003408035042800e04030031450030610441d040c4403c185144114045040941510b00400214140c215000302140e00500c0c0b90a04110380a1143d0804000496802c032200640d007480303092642c0c2162007540416040150b1a400541510f000380c1c0301d0080001402440600441e04035000401400c044061240c15442c200b50100c50f28929608544959030114031035000c1c080c980215520080740b4603140c2c03d01c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 85952618 1250 85951368 85951373
    0x50f0601090510080a0203060408160807030201020306040e0c0a06030509101107030e090106090308070c1502070312090608011a070f0308010602060a02090f12030f0703031a040c0915020a020607 85
    0x80a00f02d80c81149140341d07640c002050780e0f001c5500404250082c010f0280381d0b48a84a03100a41d00800140c142c44881e0001d24000c103da04010f480c0c00d40c801da00140e500c0c2041d80c1080195103c0300301314411a002224540c0656882c0b04111003216068140800c00741e598417100c0341001480344081c00d41500f0b0036407180700160302400809119200781c9403102100e640d481442a00c6100340108404191801e03410320100703007500007900c185486008100405a02c405581070401540c3e505d08015034007514003402003000c906541c41141e00d0350f18245013004d250003801480360006201d10b00b68070750315603484590304054204840c585904209517181e006094a801408a0001d10440b4010300980000c544012218001c031001d50100902c4647d0000303451082040c4220900010b03c0b00d0f10041041d40079040404000d02340d07080c0a81c40010b1a5041d0034282414561091001480345243c4180744a02130b400c40f040c60181d83d87c4d245c444284034601e0500340c6c64204050302c06503108a02007000c608 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 85953868 1250 85952618 85952621
    0x212040f052a0414060603130507031211010c1409011d120703050d030506100e010201090204060801090b060909030a0f020f0307060b0418030e2e080105010f08041e050f060109 77
    0x125150b056908000d41c40c03104d1001030b01c50fa8240d030132a034011000c00108004a43c1141c00000c01800f030029034560070364139950084d280f00221146000b0074980b0203850244c843c284158003c0c0692402e01d00c441c96a0660158454070601400034180513083c0b0420b280c4081ca0b400178001c000d000f0b07140c24404840c01c40495600e4070381d403008680c04e10807074502021046c424003403640a50800303409543c01c104099402c0e100d5040c47e03c2380d24110740d81c0d804003602680d598000c1c07000030041d2800001d141ca041e81000082d40200600060140d000481840782a00000048400c08130a03898071800644d01a0302c120f06200c11500c41c1601848081140800c0c1305803a8409000840c040340c08000b0005110449815a183c000c0c02a0104d9081210100709040c014003502901c825288200c260707000340b1424410072480a807508002030701690062040c0d503004041c1c0c3c21070f0300c00c900381001e0714541541c0380003110254038150042e00d03003481928010410108000041c03541c0240c1600d000b0342e1074080c0c040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 85955118 1250 85953868 85953943
    0x1a1b03090a060c080307030f020904060621090807110303071b0906141f03060305010f0c020106050a03080d091e050a02031204030305030c130e0702031201090212040f05 74
    0x501c258800038000608501512005042c690700420803419569400000d50003032580b0a007803a030a41d000c002c0494169030b24450320b030103040941c07130381c1c800b404174202c4080344510302d8034001035030914040212001c10601c2080c1d690b00e9601a2121465080710400320b400d500403904004c000c028800381610181041c0000c8806546480c20100f0000c1e0703070b8003010403c1100d150201600300030714203400c3c008141421640164070569090101e0410b942e43d4503503007103030920340036260165940c0c011914040d03420f000f1000200b034102c526201d0030b419500c41050910904091803401a5100e0101e8100400140c445040051034107581a2408190800c29164907203c0012403103070140340b200300000f0804005940c00d494050b503c0c10305580c2c1d85401e0440680c880d03c10b8560040d2a101d0000f941d16000344151b11410456010350380301c1600b80150b0b0b0041e10181c00a40e070f030700d005124110090101075203013944250010401074008140b0704242d800c217041d8100046035107603a07541c0807000a0101c40b40c00c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 85956368 1250 85955118 85955137
    0x402040c030501060c03080901060503100501140a06020d05031b0403080c0106080d05120408041a0d0b1f030506010903020a0f0602120405100c05030f0d050703241a1b03 74
    0x40c05201851801202195824028940426400003101002c244140741c1264004448000000c0c03603500d4a0010b49000d400c90003140941e5151001800112481503c0444a4000399054081c0d035040c074001946503411031480100304640840012002d002c1201c40100c0c2c000d1702440d40f0b075110703140c0c1440d440503481290718440540c2450b0000a941c80e0001d41509040900d50f103481c14005060010b141c2c1c104050015610442c1c20303c008584841c1000703503100034146241c00d0355980c140c3d001102c1c091341c2c002c01e1803a03c651054581c500d168141f401c0b002211051510380082c0300e80c3c64600680302c1070745940010350040a00e010104601d040c17003d0b11800d441c910f400b00c4204030801d85a00700c00d88558010140c04c051600980a50140a0420f46894501c071308240ca0820081c00c0c0a64466003140303420188958032603060002d080d800d0721a4400031100c0000d407000c00002250010040040d600c100100404582030081e0108221025180004034400c0049070906096038034650301d03000765540 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 85957618 1250 85956368 85956371
    0xb0703090806310212120301150206010608070e0120060702070b030408040303080403050d050f010314010e070b090402070602160605090609060f040204090203150a05071d040905030c03030f040204 86
    0xc0348240c1080f24607403010000304440c45004025000c0e11250210740c204080ba000000103038403441c440d03414003980304005110001c02d0384075031410410042030f200144401040d900408014004280d01042e0194000c1140c2090f84401030681c004840e2404266484081a00c1049100d200c0d25800310b441030003011580d08a0b480503444003418000b520064600418200d02040300300f0020b40140180f03a403040c0030f800c1c5242410000c517503200548a049404241034400c580051041000d508080b5010400d10002008602d2801c00704d01d9495800740280680024007150b2401e942d51207804403001c003070344103c003552514134a80c40d604024842c1e2100322071b424103010000d00c1c21480010301e1880340701d41000405083e2142d4040c412031000180099030440e49640244001d620100100454201c180017021128a4003010980441300040c090404001e0740807001c4014002d20002c051522201322400503118505143c258a548115151918140004420000e09840d42c182d90317845140240ca0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 85958868 1250 85957618 85957621
    0xf0b04060903120b0307140303040b04270c02030307110709090506090105072309010e09090303070f0315050f13050705070302070504090b0103060b0409061a010306050904030e0105070c0b0703090806 87
    0xc01c0013510346940000d601607000600c01c22124189510f810701000000e411b032071610f510341180c10f00c65802508102203207a800c4440381500c0070707100581503a00c403010804100100740c40c1d40c029140d10001d090709007041103500f05941e1521017440408000c1181800c1009800f03007500d02240c88500440c0d050781b0551800300007401c070a005130005501309a40c00c1c519081d40440c44103224040c2c014440304d604109502d084045030340c80d80620140640062001140c4038a00b017000148940c050b608184d00705800c050307810410604030300742001900c0089610204042d0450b0100d40160410b0f00344200250514040c040d603d5000002010040d000e542641c454548503c20b0100740c54014000802c945050001000840c04580c00a60302080c02840441d8054507034403080c3c1a50f02041c1c82c00c8083e20120340d2a109581c252180500404c01526500a90701c0c080d04c0150901007000503141c1405000135280c0104640d860070308000c1d2000502198070307040c3d0b608000303040d884580a0401340348180070 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 85960118 1250 85958868 85958897
    0x30c02150702030301031b03050102070b04021c080f070212070906081c020705040f0f150501120b100810170a0c1d01031218090207060c0518010c0f0b04060903 70
    0x1680911841c0c140e001145542d203542d44815144140700c112440c030090410300880060000c0c0014281d0718015043c240480c1054010003080450343c9031810240554000028001030f591010b13510f80b401d0000300d540e181d01440c00420203148400d6122901400b45480208402c011903100006484090b4101d41d8501d20800c801c603d0a02c04a0001000d40d216032804c0001c1c0c0b90075040103280d240300e0903012070039a51443e080001c0d00c0e45d000740f110813607407544418032195a010061320b1858041c00310a2041d00106d002050a440369020508100085480000d00141032002c02000074083c42603920b40b10002c1544490300c810521008440350484a140082d4400e000c0c410700006140c10400c080c0c0c540d29650380c0040c1000da0040c040b0a00a0100c41c00c1c01c6c007000d06070713100002c154100003d82d80e010ba500c1c0180c1124140d610000511000b0b000a1103941c404035800a100d98081c00d06d0310340d0b0311190505612880c83c0d890000c04c1c6405071030030070003002810b40209005500c40c0e03c271081503003003a1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 85961368 1250 85960118 85960153
    0xd020a0306060c110405100e070806030c030a0803060609010306050d0b0415020304021f0201110d050a0f020f040306050a0908190f1e080c04080106030f05070b04050901120201020705060a030c02 85
    0xc110240240c48140350710000c1780b030b00d030b8001500000d100180065043c3d44082040080c1000ca0302580410b1307084081001a04040c000338440d008101c000c2e01c1ca5400300d6071071510500000d0250b90180902140d0000715034040e030711030005480d0003000c0d4200094a072a010b20b0700b0004550445081007070f058065002036203802030781d008682c010200b941c03803650215903282d64955407120104564031070540070010740e1410300601d4080c5040d1001314091910044030340940390820400c20b03042c1d20400c1610f540c42280d0058400303503680008003003a991100c61414001e064a010050500e00000500680000210128031740e06210364650340c0c084c02040305d00b91414410360552200f410800314a00c1c0700d0a1048004691165a80710000d04154542c4840790071202107810440b00841c5034409441842001c0142400410302d81104a2400c1d04103808200203d50622580724503007540c427030036800c581c02130003c407004c4c24000d02040e440c1d500d0780308010040c103000c82c10348004d4003d0344ca50710841d0017070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 85962618 1250 85961368 85961387
    0x50f0d0504050a05090402030109020a06110c0618100c06060e01061101140105041d07060504240f0309050a02030d05031909020d0f170705030315040203060307090506010905060d020a030606 83
    0x5250342c001e04e03d000e060001c9604005c0c0700700e13895541d80c0309140051742c40301d40c41e6028260707aa44150031841044c400742e207441920b00c0401d200d1076042c400c03084818422000243c06480644a0611107448200305170382c04102e075007000b4003890502c44045902a41070a425041704e034103968076a0042100c40d9043d00302c4440c0e0168808a0b40700c80c005001074181030704000301c1c10102c14901c04030b15002c0a691420b0540b2600100005400000d0401805414a40300001880e803502c01c0841c290380104080d100c104002c00c40300501d92140092020701400f07000b49010190042c00f0341d400307548030820003850f5600458141b95100407850b40203480c03050038801c2d1031110342c0c090a00c251300c0e5101c0d11031030900c031603c0c401143c1c9106190384140fa00040031000e445028440c1c00155201c2c20007440401d0f000c9002d100e0340d03000320f1045c4108410390b500040d5210844401c0400000d0300c1c0c0b14400102c1d0301c22840c3d0480c5420520008000e0200c21403070f401081e0a49095404100c100d4541c4022140d8841 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 85963868 1250 85962618 85962629
    0xc04060504020901120b0d08070506090c100f08070c1203060503070605160605090c030f0d02011a0f0d1509051f1e050c1908040201030e0706120b1c050f0d0504 70
    0x1c102d905e043c1c0c0e00010b600080110400501e44071618844d680c0d00e0003a940074403400c44550f00108240902c1800c00c1003503071800e02c8211128a11079801c032000901c3c00040004041c1085180c00101d0001400394076003005080d0030040118000c020108003801900e06842850b01900c00c1e8680021124840c40544e50101c0c081550b44003486002d40700c40000c0c1c44041c00802e240d00030b41d0120580e81c0d600700450322062171040090403c403000107401900f100c884a40e101a00030403011285101d0b500c540000c0b0b40500100c5012410b18004d0038508040203004c1607041c1841e2034009400148400014a6401483c0007a0440540303014010554185d400c1d041000c00400740c048040c20b03111616400c074039805212006c5c03544c100040c6c007076081c1e150b4180c41ca0398408501201c00f030000750350b4035008610301041000001c051492801c00014480c419440c0003100503542d82d03021030050355032024001d02d400c6003011840380901c0141030064070f45405005200c201e21030003004019a42c018001d40b002ca51 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 85965118 1250 85963868 85963877
    0x80105030f1902040209060406080109200415030b040507020f06250c03051303060219020a05060a090204150806100618090e1014010f060302030903030402010f050c0604050c04060504020901 83
    0x150002220b11605044160407a40584c081c0b2060109848000c05040100001e17598403045500d00b44001d000c99000c5800e80c00a10410340c0003803803603034600e07080300c00300c403a40010850400104c0004400800c84403110303990180c00c003020300a10642c000740d89a8801401d0050364030541300c40a1411074070058419a070306c141c58035461454031900a9044510f001c2c000d0800e00d00c1d0008a64030f1a42c041550b4204984055010441107620f082c0408940b004000d1400100003640150320380f555500c0d0001d080d01259a103e4980608640303480c0c00118080e078ac5201125149038848009030b0302e501e021240c0b5040480050b030000f070600d1084c07845280c1c00c00c00103c2d42a80c5030034030140c1c0d40504000d1400803024807440c641b0b40800c08981c85011740c080000880c081d0903505000c00d2040e00c1600e0b500c1482007500500a2003030703103803011007201d4105609007818044d0b0401200192640d008203c0d9a04072805400c040009011003c0741c410100701c01150200b124903201e1003000308038010302d1205400034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 85966368 1250 85965118 85965133
    0x3010c0e13090f0209060a0306060807180509120c03090402030c091f0c06051e0403030b0a1d160201140a020c01050601050c0a03110c270a0501051507110612040201080105030f 77
    0x1402c04007043ca40041b009403264900365100c1e01c0e0042552160350104005503c60340b4200b080401c0d001c800058007903d810103204a0400303801c0d06607201c00284074001d0003280054404000e5800304111488e040c0003070400d5403a440c2040d1003400580141881600404281030748800c600d2841d60040740303000c10b6888801700102a91120350040c88018002e40c0c94980f0400491540303444404258810ba100b5074010502c514403800384408084240d104400300141c600c5103188130b8100b10311b0305602030789404404603205070f0010202d024015400e440b20b00c0c000c16105201071103607a50024008020b80e50024405c507120324004441c2442600e500c0c1c80aa041030303d00c00c000a10400416241310001c500711441c0e000d0600018409981030321807a070103c00040f151460f00000c03485010b03444100880200542c1d8900404145500ea1994221200c000b00040b07120400c13007401c2d0108554440509070079252000040031810010069a0036804035690070000178162500043c1040c0040e00c100151000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 85967618 1250 85966368 85966373
    0x1a0a06050c010f051501090803040b04060507020a05060a0804060e0d1413081903020708010902010504031502040b0316112d0a060905030a110111030606071103010c0e13090f 76
    0x116000000904625520fa00403103050800c0c5029540c007a296440d0400f20000170f600000d0070703100c03c1d90b0220066402c144000c00101c2007481c151303411203030581026680c900a80c40018241c4c0c03c00e80000350701440100d8000c041d903a01030b0105100d2072040c4d03401c0181c24200d213120383d41c1e82e28018000c00010901800b03e015845260050841e01c800320340905545038441c01c101e030070300c410722420545108034042840d043c1070341041350350010081c4c41c008000300c41d203940000b025032055000241009a2640e9207044403859503048a00505102c800281c0380c3c24900d00b40d4002e032031303402d0311030000900d0007007292856400404c5490800100f0380d01110f604895060f01904414444d4007001035002e075030104004141c690041640b190f202c0c1000d107945940c00b08015200b800413549210301a8544850084020300a0007100e070009030445010b92180500e04c1c0001c103460400300b00d1501542400074400da599008041c002040204413900380720f00011203c240102d8500380c1014011511201c40c1201 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 85968868 1250 85967618 85967627
    0xb03030a120e0f010b01170105090a1d0607021b370305030309030309010c110d120e19020906040209030c040c020115080a03200c0919090809041a0a06 66
    0x1803284010402180d020b55008107181410301045004407942d4481104603510b40c0c1c001c10031603110b03454404c56000e55060202241c002c0700001c010103800340e5a81d41d0320310f8250003001d21280d0005d44400319040d1f4500880c00a4849034080172a4408400a0000021501c1c28269100800030161a0740724405240350541d4080c941c0700c41060f0301401680780100118106000031441034264900a590303038100b17043e0007030840300c00d4500341d410090b07200c0f9510070390440810a060784906515000000c041448408402043d02e40020740721031140700410782c940c451060202c1c0f10903000703c407181c8030765580c0018401607103d000100760341508894040001072406520003280035101e0702c00041c14007042c500004500003280c1100e107076684082c50300d07010581e0103c01e5040e40580e81d034098012003600c2d05056914801410002e10850741c0078005590500c0504205c40f40fa0301c3c01d6002d200061041c10100f5080c0d20810b5100e0055007405803110100030030681d194440300d070103480204114580601140c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 85970118 1250 85968868 85968887
    0x60c180f060f070c0e0a0c0503071d09010602060a0f0e031e090a080601031502070b040b06120319080a06030308070f0e060d060815090601060c080408010e060612010b03030a 76
    0x1607000d4014050340c9074400c41c55020301129071054001c01402418806000c1002800070714045446051040d503c2d106580032091725042119428074000c000c11034100c41d1a001a28401990400d4010b0000521290300150711800341040748010407000b60384024201c01da41c120300c0070b46200c0e4000c020140c1074032000072810032188034440b142070038aa031100014400028551010706198049401402440300482010a40848600f81185425266507030348507600c5c0c00070710141030f100348000002d5058861130000c404030048003058940d189a0340d0702c0501401031500d038100c0003c00840c006035002c4d04601c211400e90390140c03288000c503960408100d40091900c840c0e1000c000307000000c0381e0030b07403510f6025080010140350003240c01420150a145088505158054401280f8080c482070010100d03101d41034900f00d241c10070b8030b1001410086654130851740441025840d2540719202948041010703400341400715883c2c0720b4980f030aa0340f2801e807060006c9040e89600104181d2014601900d01710 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 85971224 1106 85970118 85970149
    0x3070c0302270103291015080903030f0705040807030c03031727160306050105090105011110020a0e04090b15100903020d051c11060c18 60
    0x500103070622010b1300580803100c1c0041941700d03018440300c0c0040c000032841498202a0b00d4102c5901d141d00c07400c2010350042454071100c070701c80c0b104a80510b400c0d20003141580c8621011065410001d85080248101080006403000091180c1001103004002c440001403442c203020340b03550002607251401c0300e0024100400c55a0a5601c3c00b20034003000c0c446803c0c0303503195908518064800d0848881050a048000100b100e070b40c01050580d82d0540710300b20540d980c1c0006440e05814128a01055006424001e50103485d5a02078482d0070341074a405d212003000703080400c049810300d0b0000c2ea10120303c1010400120313001e40550280010581c0c0c0080c170110310710001041050f45000080c410f640c0841c40300b0a000003001030300301040749046080340c900444080a400c0501d41d1a0110160041c2c0c00014240c0e40001706613040d80030301c1e091104610040408010060b030000204 = true := by decide +kernel

theorem cover : BRFrame.Cov 85791368 85971224 := by
  have h0 := BRFrame.cov_init 85791368
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 85791368 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 85791368 ≤ n) (h2 : n < 85971224) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
