-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3627
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:13:08.762966+00:00
-- url     : https://prove2.me/submissions/c97131a5-5cf7-4eb3-9d30-241bf2fccd34

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 652158273 ≤ n < 652338129 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 652159523 1250 652158273 652158277
    0x1b06070215030702030c0109120e03210d09060c11060c03100302010c050a05060a0c0f05040305031e0c060709170d0909050907030b1312020f031c0603080a030501031421 74
    0xc0c40045020070000c4040c06d203000d0007200502802034100326103d00f1901005070442c0090b11600f4001e41201c169411800749801c03174031040240780071070f8540d07403000342c4403003c0104002140100a64035041f01c8000303550340700091405000f001d6003150040d850742d80014a503170000316070b00c83c007001800d0b00c24401548901c50003011700b4429011119081d9940e80c449041420844410758419a2140022523241d404000061405280c1c10003519040c11500c4e81601da214000100c2c40d181c00301407040c0c0310240c000d4119410a180c00082d039580b82841e04005111140c41d00c20745070344502c10020400d01c2000400d981c4012221510f42c241b85c42d180064080140100811500f8580034440340007020548200c14244034054001a40d00e030401c00d450050b84000d00c64943c401154415021840340060000494401c001040100c0c0d08000422070350700c001d4003d680008080038400305052a074035800d904030a05a91080751440a034003070030303c1c0b80c990b2604034000c205c0140b0125403414500d6020440 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 652160773 1250 652159523 652159531
    0x11805130603141b121005070905030607080a060b09030d0e0f041424090408130b0c0d11010b03100209130608061f060923121b0607021503 61
    0x1034046151603881c3c652a002c2c400310100703000706400140c1e00024950540e20b002c2c281000803601151880e480485c520f40c3c80d000600c103c400c05650b00045140240558a900c00511000701100d00c00d00c3c058200600510094508180030b900705a0b01007820301c003d80642d1361400001e0300411500c444c1e0203041390f442d0100780940e40c02400d4a40700140d5510f55000700303608024940c0c0180021b05152011540a604001c260704058820b02200c000709e42d2652840c80e0000c1d0480c0700d040e124044455a030b2113042c42548804442100081e055608010125000d40b803116162140001928141000780c01c2c2e030100015079a140d000040344401981c5150b02400140001824203100307007200e50701940840e680c80d00050b07030f180e001804000d80401e008101c0252940c0e00c01110103070074a044006010a00359000d010364110b8400750b1800780401100c1d85850380c140042114900d07102440aa5840d8414884841c01c001c0c0c80460391070346130a01e0000c03a08455405880310110004061030f09105030000b034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 652162023 1250 652160773 652160809
    0x10c080307051602061623030a0809030d0f0b09060a15201015150c080702190b090301110c0604030302071a0c0d0b0d0f06020903070b030408030a0b011805 68
    0x4442000d45c507180094640610089000d5080c800c41d414880103444a801e03480c64028030107181c0700380c070841c04001d8030318a900342c0c28969900c1d203648410394298060046e40d0b20790f09240003249035180113507030403c0c0030b04441036440c150b13261188001c0c4a1200c1c0300b80520071495000b0401e061240c1d20400c14252500c080c80c140b04501d000c80403440342040c1a07203a0101d1042d850300d100360650203150030132000a2a12880d0414450000d00d00604128124100900700d2100800c5e01c80c15511041ca144400304c004c600c80b400019152070a03201e0076000039202078007a41c0703081c0084000022072011100d941ca2a04028080d50b0398554085000e075101040845c2c0c074072920444490b130b0342400d40c00540500381040d400c035103d00118001400325a03540401c54460251140e100002c1030010390304516168015102607540d8a1210109181404941c000340c0c894100104000034441000b0195014001d40803083c0f01c02e526070070044900c03c201e400043c4040c0c9014008101524000c1c0840307040f52824 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 652163273 1250 652162023 652162057
    0x30618090705030a0c080601060c0b2205060a0903080604060e130201032004090f14060108041e050604020a140306010e091c17060123030406060b0c07080c010c08030705 74
    0x1070307001c00d084c01e0340d80b0412500b41145403414080e13200203200e16800742600380790150384001c00d41c6404050000142000b030100006000e40120900802541e04506400408603425400e0034009040201a2040150002104440030800501c0d250180c40e04880d2400c6c0420030603118445001420601e8141c100d0515603251045003001c103411011080d0036a10441e8039403114070704001c90096885070b101c02e092041c80d111604d1600c40340c5040f4a90001020302e85140669110b15012078040c200030283d9845036400d0117080104080003500520072442a01c8080307400d80d4945c0204090044004110341c15007081005000c41c0000c502c0d5141e00c96441c0c0102d1b00c508070084103e0911000003c0c850700024000326501d4031503030a602c1c11300d802c854280b07000042c8002403404034031350340030064a10140c1e410002c0403030107116550b04801c02401c0801038190340d81c118800e500303a0318152881402480e0250308030100340c542c06010646045a0800d003000d107166540032088a2a500c03150b860044c4040f5 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 652164523 1250 652163273 652163279
    0xc150a020d051317040b121e0a02070c08061006050a0504120b040515150d03090503070b030609010609060f12090f060509010b0d260715200306180907 66
    0x910301950f4003a2a0740b41102d804a100c50038549054010104451104441000101319030703a654812207290b1401700c00d82d64019164141444882000100c80031007161041051020030b0150b540102001c0d40b0030482e81310001d664801554481404803112480c825098804200c102e024000406d01c0907000e240c418503264035450503c3d81c4002104046e50300c801c2070010402003080c100702c1300895021007005209140740c121405080701d002c0201013802241c80c80e40082c101400b80703546601030440241980c180944401c416040c90b00300b220b40c1d5119004c2d075400040c000380075254042c15280560f683c201d1600468000341d451110303003040c000540eaa50034658000c075002c500d60307460191150401089078184050302e5401d45441d041c041d0b00c00d004402c4280d000511103c04501800d0001c4142d5070310008481460f1240e000d060405000c4040140c410002d13519154400c054201c40c1c800c00303241154050305882c640c0e0104944050b0031800700201841000c0c3c2000d203d070703400007101086840c9161 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 652165773 1250 652164523 652164547
    0x6020310080d0e010807051603390309060c17030612060a0b010f020c01020a0b250f140f071b080d0908010615051819030b0f0a020c150a02 61
    0x2c945611200080c000306190103c075070384040c64541000740e0780f5006042c40b55400000c0503000c1100b400605124a0800c00e20100171001c446088a89414100c103401c0644903415482c2c0d048d281e501103000070900c3e14042240c0780201000100141c201013152084665444010b0703480c0d001425050b40300c941c0280c40c2d000e5142c104034443c40742c5419100407800395100360001d04801c05103640c4034150f40051040c0700241e60b0000b4504250348d003091a400c845c0c4c0350f080e103001c0d00c0501c4005426039501142040880940c1080365145e600580d40e8510304182e9488071081e21700c2c003031101072000c040420800840401c009400390341c5180060041012526501c83c10149080c0d441014100820f0500c4c0040120880a1103130300010140030b441c882582c100c00c00010b02c41d00c1142c5075004680c800340e992840a40300c00061407587e003040d4800d80a09a100c0c00c0c40c1c504820304a07105004803500100146400481d4001c0d162054520001004003050262840d03031501802030681c601c10b542445000e034621 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 652167023 1250 652165773 652165783
    0x90c03021224060612040807060509070f090b090412030b0a0f0f09090f021e09071e02070b090d081c02030402131a010809100f021803190602031008 65
    0x50740781c00c000c0c941e0341e035201c456114070240300700c11282001100c000c2003080e03202d0404440c001c1860280c480d10a5481d842c161a00d4002e804c8007070b010910340030421007628070010f90301041d1080c40c0700c00c104c4a580c4a1102e42902c1501c00041c0d003140fa6000840d002501c00e20032040e101185040108800d0089000710f010041240e211440b0006010310820640c0101c503601c0300900310b009414010b030442034035411140102c448000b402075421280140101c18501a0780034260300060000a031030400c01c5004101c8100e1807241e000203405510300d42011800003903154101c505800006007020207800801c80c2c402c01d01c040642ea84081004000c0303900e540c4a14034074140901520040e181e09107801480709184109001ca407a403482c00b404240002c04a02c1324091100003403811801513580e02460505143e0404200d90181d41451945107040e0440e070042e2428114a0508030f286070b90120030580c1c1d8801c15400007031a40026188030300420026002158880522040e51034440e0351502401e1900f = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 652168273 1250 652167023 652167049
    0x4030210050a060501110304050a120813030303050402120a0302070302010f051c020703020f0a03050712050706020c0f01110f1b0f0f160f03110108150a0801051e0712090c0302 77
    0xb01c0c0c0c1c0340f02c01d01903076820a44000d221615540194100b40c00e00001c10362140d51401100b16204071944036404100302101228520108890900340d810364914001c4e01a201c05d6800700e00c80c9007025600746041000250200625406600415400346140c00640e540070700000f82004020040100346c107022180e04880d02c1e2065034100050743c0384424100203040c148003440800e160b4000c8d04094010a60040030385480700e03002032584100f410002c60a60310742c07040c14801052036001152046000d5804200341c012080010300038491180c044a2a1515209241c1c58161041051051005008415003000d62a2586208480742103041d125010314006601107070000a070b0041c1c0b003552041054080c410000e16403404500142811030ba10b10031042000c0c0c03015410407000e6400100200c00900700fa591451001d44401b0507103480c1e10440e4060701c403c803a01c1d026184403441c00541a91030b0f0382d81604c6841aa0394644541c03c81480641c050510b610081c2d40c0c003540c100021000d41d035441161a00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 652169523 1250 652168273 652168291
    0xe0304170f01110901140903011503150c08090d0305180a081801050a050a050304061409030406091202210c0301140f060307030c06120f0f05011d010303020d05030403021005 76
    0x11030300c1c09218990949003410804280b032441440310380c0840e60009608450781c00d030000120f40383c41c82040428010101032819140e01110010000140b000720704800310140122182484240200c03030085d500d54a080d0340807039480d8001c3c10b20000701c80c0302c2e40c000340d00010408001c1035082c89084200f440c01d0f032024016111540300082c9011010256107128841040a08003507040540c40e01024200d40a41100d800c14820004006800c101c40307940181c03028030117001032a00d10308007564500d5581e00140164000305a0385140407070009001c3e03c100410315402007005070711503261154074594210750410340001c0c0c0304850010140c1e503030038050600031450744601440c06e0315003002ca14046480c0074184a010382c10011051010564807482101a01c40c5401d01d501c4a505a104002c024103c02400d4003400c4e00e0410b8400c0d55651682085040b18a403818042a0b165909405d1802d14001c0c400200541d015000d60410749006401440d8054041c0c0195074101d61212004004e50b0400c41b55481 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 652170773 1250 652169523 652169533
    0x3100e0c120c10170106020c0d20030a03020d11070506032a12060a170a030f020c0d0f0303150e040f111908120a2102041203120b04020c0607030e030417 67
    0x3030b070700740340760600c0340103100311f00c000c0c80c0248400011508494603002c0c0a4500c0328030446240200700c03000004c0500a10290407198846000d090094070b82850a040d4400203600103c000390043c0000341040568000821482c07441c4c99020031884100b01c5514000961280920394607440d19894024000d02c800740751010095140160802020400356004141e5003055154142c8507910001140101d456040c01c1003040d829103c4000c6e8a4040c12005150f888440e42d80300c4010042c0c02d42c0000f400c24030039101441240007036407060003400d400380a00e91103600007a0014010501001d00540058054006a801c0300190030100c0c040c5180c0030b440007285540c007031040207280410000c203c09040308040250400b40c20400007026041464003640c0050034030108201420410750403100140200020300a030345006180190020b0407049807460740b10301d0581030080724203141c000c840e00c484200300607004a40d00c40704150001c000c01e80f5034865070300c000d20021688801c8881c03020041d00803900100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 652172023 1250 652170773 652170797
    0x2120a0b040b0c1c0531060e0c010c030302030606120a0203040201021b012f2a0f091306090519110609010c03080c0c010203011403100e0c120c10 64
    0x182203100c0038007001100c480c03c00184040641c0c1c2c02d540460030b40b0341e10004c01c160b01c0350410001c4640c10003005d8006038410340d80d55140d500524941d00b0005109601c00e00c403040c0791031108c0ea1924400c0410f50b010510030000900080c0c413a500459011400802d40c17410314000000d00c2c03078082012588041e6445d400030078401550b80410032440360056601c2c243c000601064002042e4505400e241050403d0000105142035075090011880060341d10403174003c0c1107124035032030b610441480c10000c119142c810003c044d0410003410178035800c02800d407441c40d440e641402500b11496010a840540e95843c1d803400145050140034408104140446105411801d0038219100d00702402c44c81044104800407842c0d8210115603400d940505190641d66143c0da181ca00901c90a001c0b0142c40d403000002052052201440c0f44c1d220b4801e6040b1040340885042c0541128a0140b0301a481e5010710789110030340c42d0664560405c42c2e01d590644a0000015022920001d21404000302141c081e1980c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 652173273 1250 652172023 652172033
    0x3050405030114190902030c0d081e0a02120309190c0501031a0f04090f0501141909050c13060902030411010311040f0902030c0702101101050a1401050d02120a0b04 72
    0x19002001081000f58030034145150352601c010981c0030311080305600c07440700c8020b40da824820301080540140c007200f030f030614510340030385117920003101c91303400003c80340c0e0786101c41e00311109544039490a50001c2241c0d00741030b1001442d81d000103081584501c600203010b10b510340f01e60000340c0114422201b5015180c1080f0005d01900ea10407145901c0704050140b00700c0c2d5030346583e000e60320540700381c60000b0805003c0c10241901c0b1098503000e0203a60170040340100903120743d01c08034402d00c0d40c0520760b120305d03103601500782c1034508880c40507000340d0103c031040c1c909241c4120100c1700381c0c1d0510b100240c02030b0703542101001c0e0f8104a505841402a0040e1804296014010351070700c0b510003003c80b4079050800c03002c0410082d16000d8018002d80c04800607030100e1507002216180c2d600108802d80b02d1074500c1009100308180038814406500b0000400c103070140e09e0103462808681207000403505e03800c003000d02c1114450074005980c0014148211805031b00188081080a40111209401d030728180c144 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 652174523 1250 652173273 652173281
    0xc0503240a0b1c11180915040201020604300e030d170705071b23010206061503060d0c0f090e12070201051303020907050c0105060a140d150207030504050301 69
    0x1e0034949909007940140c0a90f90000031624802420441030310034442410007213450720800340b485030000444c0c0301c400211400054807611a06645084030450841c5101114180790280da00038056402500814001500e02d0310401410740070300c0805034254000c500c0b81800003165080c00000c141c4910340d051190800348446e074041111800d00d1050100ba803000e211a0207001030084080043c0419240c0030000f9994100240781d0f10000400c500075180d60305810040b00501804d4040d130403528000c02c0a50010458034490000149070000030400c401c50502a0707880100119804103030141d03510000307880110034074081c12a90f15006420360400c101c820494640780800741c9a40d10032114520700c08030510840310030b00d0b82032902c10380341c0c010071134106004011b541000354003c40d1030b000c1040c1240d10078081c01b0307130413020f500a00a0340c5641c428081110104d02501990900c5684044118241031a03240b03603091046a644040520918044080341c100c0c00d000c43c005000002c0802042c0f03401d0003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 652175773 1250 652174523 652174531
    0x150209010c080a09031e030c080a0302070206040308041e180e0f0d0206061c0b0604090516090c260609060315013203061602010b0306012409080c010c0c050324 70
    0x1c0c0c41c2c00705034259100907208c0340d42c03500c00911020000a403000d40030f2003601a25681940580702c1601c0c0c41e02c3c0e03e4010406c0d0021b00070911518264580c1c400703446500c1e50321208070759000003007c415004159485c0b0181c8203400542c5c0c01c510032132800c40c050780c00400403090061348980c064980c03410003204001c140803100000b80c11041d2a0010280402da0010f40304c0e402000841e40054001c5c110715041e801e2010b031040c1404807540d10003000901c2d108503040042d0f42589507540340601ca0301b5950354a07a007024502d8030300411081400061050415100c2e094119100600f22064207008444010303124509801070f81c0160f002c41c4048161101401e9400014989030503141040e0001d50042691502c4c002c214080d203101036580b041c10a070007940102001e02c0c014058840668640b10741e4000c079000d60b10700500c482c1c60041c1c0165031512030f0b00354005071b803a200058202d1454a100449000401400c01e44006000080014083c1e030201301c80304203503e5510320505c29490009900442d0320000b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 652177023 1250 652175773 652175813
    0xe0a140a0e0907060201050115052d0c0607030606020f0a02090a06081642090b1204020f0102030a0503010605071a042a080705040917040b0c0c010507150209010c080a0903 75
    0x3030205410580c01c4010b590314bd40070382c14003240c1d80701c2004000600c601c05105c451800340c400034440707099540101e031103407003140961801e110440d5900002c90351918000c03125081074000784200401440c1409650b07802c03648041c00480c00c2500e82040b0b5041001c0b03451741001d01407400c0410441d403842c60801620220840c200003d8910340245450005040300740d986141315030410341290024020303041350001e042e0011305140c452402c14019003951500340c506921075400400b40008035071001007100d0702070304150766650035a443e010040d11513030829001159500ca03689a8005c45500903d505131280d07008506090403000c40d042c42034062042503564a40f0941c1a40e02030000c0c003000103043c011a1030a0340c001807080840c0c00d140b1040e041500c1d01c103813146070000c0e00180700300c0c842c0d0140c40d011008100361404c2058410055941c1d100d2242700419403810541942c190a1702c0740d000d00210041810f007008140b00581e180c0b0b105a00ca911031101041c0c00078001d2050100c1a41c021506020f50 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 652178273 1250 652177023 652177049
    0x219020313050f180712020d0c142505010e030a0305040b1b0f090d05010c210c08220501090b090c150904050702190c150e0a140a0e09070602010501 65
    0x1070013040c0003c030b11604a0103d8031000c804903d0a074030640303581c10040d80d0020110f480b00c2003402c41e1409000c0501c0d214001422002c41e01c0c1081011008441251010b03c01d1580c100080445a4010072000d50301600e888d540c503070f02c2ca000c580007030000300704143c4160f9001806252a2900201207080941440e001c4501d0120024508081c201218100d400036029103488080440000d14038184241e00284207509210420b4080c0d0b41055504c0004201a080042200c00c502560002c907603d41072400002502100030071285001c0c8154180381d150038540900c40c050301925131034252134201c00c0803070303207200349100304840d0398402d01c804410058100c0f0444c502c040c4c482d0b007080d844d00505000c1c4d07208980d0343c008520141e00810101007a01c0107183d18001e1940f4074108072070300c07103200e104054201100e489690183c51051080e14a14100200070115107414104003540e0203a909540f560000c0d107200002c00d00070041010184105100001024600e06080c2c0c000e0941b041079000d01091210 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 652179523 1250 652178273 652178299
    0xa030201081e0c0318031201090528020703030e031e130b0a081b07050a0215040e0703020703020d0f0c03080406151404060902120c030c040e13110f030307080c01021902031305 77
    0xc030f01c480c0c1126040b49e8003280a840d10100f04c0461310150822910342c84009004100303154a0b90091b000050107600c041002c0091200c50320303201d1046450014412001c00b400700090041078024003c00d40c98404c28010b041d4940ca946681603205802407000306030000c0c1001b4084070040700301d00000040d0401c05081c100d03283d0354603982d4000304100900c1003081680072034280d0081c40c01d0301e000f0314140060320b0050421020103002584a440194010f020b1240040a854094424080c21040607620040219442d8808441d410f42c060811542c0d5502e40b07c1548a655103405e60601420b50203258240b401e04100400c411510294400716103103005001e0501c036461441e0516174010059000c40f60399640b03030700640c4518400c2d074100703a12034060724047c0414200c80d00b0340052010320580b048041a03181d0380401a034182c0801780036074141d204021410000340d40201808008005000160810480426802d01e200121080000503400450702d031040500c40c103a80001808103850724009049 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 652180773 1250 652179523 652179547
    0x30f27120201062114070b0a08010503030a0e04090c03051606090e0906010303050c0705040c0504080c15030a2003090a150203060109060806130504141002090a030201081e0c031803 79
    0x30303030000c0c514803441d1840031010902817001c61950f581c2c145038007941c251684440c40300d07203d0340200c0c00350000100c1f241c0002c94242400409c507140d003646078981d403207032480403010000640071611f004c84500d400300b130000000170010440c44511a13003e116051204e0300344400104601040e034001c0000030040001c0c0b18a008010400e6819240c040c5800f0340d59560004010303140502940c400c541281c6403c00e03643d0403681c407002500c181c5004074240d900050616041040c0c031740500500b016150300c00c1000c500941d10341d502044400c50b00b81c4aa1158030703042c14a180846d08100d851801580000920764204080c0b10782c88040c202d4078600c11401d509202c40020030b207540b64001c006c18000040c000c905941d85107101c44603a400c5031030040c0030604e050310708941e580c04071500d0454244200104904075610034003e41e1403004014210526280c590b4004440a900242811034000401d04801d8080b00c00604203038440e8032039002260341c90500d45030314402c0e44100c540500c03080e0414441144140303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 652182023 1250 652180773 652180799
    0xa260105060a09030b0906190507020c0f0f06070b07030507020601120b0730060803070803060f061209010204051f200f010e0a0c09060302030d030f2712020106 70
    0x60400c0e5005622804803080c19141c1c1403c50300060080c140250030800d00b103c0020308903126100211291910342222808141034502c01d40340c52000d60454113086070203003004d03200380b406810f000b405080031540b20b1012440c0c5900c00d880c1501c7c02004842000f08550b003600403a9004841880104600d625100200590034803400000300202182c0e0082165a8402c0307400b0000c03004020520380e80701c02c102078213000b02c4c40000050030b01c09003002400600d481703000c42594021a0030031002c61541c0e449408224404400340b1549501000c02e21500d11480c02d1004014032801020000503611410b2400f0850b2005050503032046e0310308101e401c80704565000550750b10095443c80080101d2070b00300c00f014100141a98141d00940c070340b2041c480f507110001000030f2302601070440213941c580c442d5032a1040d40d0725408081c1d050b900c041c4c2031303074291407007030744452408000381800141104402c50100180225180405003090024005105115146120a85050680c0020840c2a1900e61115201 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 652183273 1250 652182023 652182029
    0x30a030f0c0201020c0a080604050f2109030307081303140109020d060b030c060a030c08090304080d0f0903020904210c1509021908030415030b03120a0302120c0a2601 73
    0x121400c0c41c0400c590003004800455500240310300c001e1500c44100036078a11040701e040e145071250004080c179404003c40d0360100708000520702581607200e520005000d0784225030f40384e014030041082c0310215010320050302c49031000c0009040f1040c514148011741c6410404110150703450050f0703500c010f9803030220041c17015510203000f007100901000003d08000010b42019040080000d0358191198541d220101c40142511a11240d403100342c215a40c82c051070240c1c0101d07a028070307280d111705400b8845920301c48003507103007000c410350b107a602141ca0490290340c1110090303541809000740a041e050000c0103603074149004d62200800c4d4450302c1e2107030f00c0c0b00c0480c0b02042d030342d02042040d5180d0f0648407114184014001c008995130b002040d41c3da910521a451050181d8882240d82e10310038080c00c00c003410010010031554488505001ea0703030303022242803018160700704450540040000003ca100b1101d45440c580c85010010000d0000e10094000381100d0003012444610307441c5605d003031419 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 652184523 1250 652183273 652183277
    0x2070609082e0f090605180111030103080f04170a0605061e1201020d05040b071b05032b0f0608010f0228020a05030301031b06170f060f1815030a030f 66
    0x90144260840b500621a0103000d601d0f10f81000b885005104050b08614001c0c2c1d50031240c2405121003618060886c0c0002c0c0916602c020204010000310f12100040d05002d600f07400040d2800b9503075699881c2550310155141e2035038208624030818030610b072080b103602c41c0d820b4449902843c0c0541070320b1800b10b15480d042d40300707a00304032500501402c00d5051f02c100c049810b904008604050515046282040720000c00140c50180b0503018445070701c0310311051a61010066041002d01d4060b240c009600e50b84804442100c2034203d4110a424000c40380f00e0140c010f4001401c07402d210407282035a80700b82c680140c4900400600c503071b4001840c00d0b0b1780c0c03c5401440460119410b60002c0341030418290018103e031102000100900000001038001d41c1101d400c10341c5c0f042e60b0785c07400755050900792040b80183c05c2480c000684c071181c010766060f8800c3d8010318100082d242480006c80e40020720010407945240700d4100400540e080c140c501307a40804800400c410102c5540003810b4605541503802 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 652185773 1250 652184523 652184593
    0x4030e030d031b2001090606050f0406080a120e0604090905010b06040b07170d090b01080d1e0f020705041b121802060a050c1902010f2d0c0804060207060908 69
    0x420900c00c51340ca05580c95180001c2c08042c0250800c540a07000600940d0f10810303011045055615180c0b0500c0c04492281c00034004007044d5031500c0600700d8503d4940340601400c0c13058540c00381d5481000b00080c01700f12100003070003002801d0550848102001d8540910f0040105001d4980d0040c2076840641c1e015074085900e840c500c4442503540900100c0040b040c5c10146c02004000035a0000c60603031306158205c2d0010304402c0800c40700c103815088840c00340d9507a10819031086106450200f01910903004030b039036107903454010408903283d004254194040006000310300a503c860020160b00c518241800011004c0920120980790350710020700c28100010039254650003102520340c03182c03210b015210201c440401554020342e4407030b0120b0001c3c11140700b03102c4c1913025040300c038a805030140c03401e2003500b20305c5052101414151181014005235403210000509460014409400c45902805c10f0368030700440607003250740dc1d0308199120341003003446140000aa8024080080030007201c04 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 652187023 1250 652185773 652185797
    0x902060912030f0f07020907020a110904050c131a06070b07200f0d080c1608031305030d1d15070f0903060c0215060423061804030e030d031b 62
    0x35182d8440e4484403481803074003140080c43c240c03140000e0030348580240c42034600b076500c1b020300b26295402050000c086102d480039104c0e0a0078a040e040d40d009118808036915000c031180042e04020080070402e4900f600c0d200e240e00319801201135509183c0f03007640ca403070a2000700e80d5000e20614000340750784d081007086000c4402c4070f840031201c02261b10b4000251040720007038091454032a2129401000401d20318008510386880784000c1b0b0380d04034110310410140a03170355529003040d6400980804140c0403480080c101040c8180000c08562102940c00100880408544181c071401d5100080041c0c2200c0c10780800002600301159000803549400c8600b14941c9a0580c1c11400303c0c4c00203888e1903d0034485200c03482c2c00060340002280445020811a40c8a0703040100b501c5c07171000c80d05035058540f030946902108819082c0e802a00040c1901410400070301200c3d6221403c403015000518007044629450806000307140c0c2d500c0740340c0b8050180d92604140c50144040024651040000040d080 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 652188273 1250 652187023 652187059
    0x160207030206030c0a02010b06070f060903050d150e010501020d09031101051b030c070f081506060903030f190302090f0111010608010606110f06012111031009031209020609 76
    0x4001a40c1d0041c01c1c0d9480307080014000c2079540080c6041d0016610b01484d6407800e00d4604190703403001d035202c244500d04000c4d5580e444007914030322404400b808401d00034480105218003884603074241c84000584000d01e440300c4420721b004107a02c514159001034041c1300d41c50360310081910589410807003080ca910180001200c2911640e0000740c400384681c103a00321000004001464801d1381141180c284603243c00d081c0b04140b08034806c41c01d0562100512003014480c00041c1640035000030282c0b400d03c005200428110382c81140074605010001802032190050000c0e0030030440802e1501b181000304a4010549941c0d0085c20541403104002100921040075001400680904402400744566440d4080c002544002030350b40f0600441ca140204140c0005425040795541e900304c98000c080c0c82200c07500d071804550140c6072162030144900c0389440400002d00d60301640d04001940d5409420300520100c40341c40d103e0005801c0840c0300c4056619041644e54108080388c4410781a03541c8084 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 652189523 1250 652188273 652188283
    0x90302011b1b0f0f0f05060601020705030d0e030a050a06060f0905010e040605090f1b0a0608160509060c03070305040e1f050f0301060f14091602061b0d02030f040c05060408061602 79
    0x10091221343d90403402c02c1000b500c595408000c83c410021074545440703d00059844243c58002d917074044c1c0c050014440b8492050360402541000a0266147c10210b078540b80d0800001180c04d48545445440800042070a4035503840146039904007040207504003034054106050190016000c3c1c0d0f260030210340d102005001d00d00d410b9626800725031015240554401c640400c0714500c0f03104101d00800082c90a0051030050b200d003d008103204003002c0b0256042c4c6143c3c20626010307030490410b000c003d100c070070104000c014030340c040c0d00d036684c81ea0f242c111015646c5000400803a1541111802c8000b048064a1220251007045480d940101c0050010a00501c0547d2100402d0300150b400000d5000b10001441c51558054884ea40380d551484640142140c6c0c0785459001a80301c400015007091180041c00c0c0034205030104039150a0740010440140c0e041a6044908840020144002c015442d41c07034500500e02a00d10a040c640b9040350907880f0500185071143c8900800c0800070f145e0b1090003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 652190773 1250 652189523 652189553
    0x1e080d0f03111303020f22110405030d031a0f0d2612061f0c030f2d030e19110a081f0b1e040c020f060109090302011b1b 53
    0x60542d12407880c420082080c80f0742e807209a01880b400341411034981840d0004000c45a00c0400c48400900543e82510007043c1900c03ca4182c0700e018040425140c1e070601008244002d13980c1d02182c081106d8034029502c00c0c2202d201071040387c81745981005c60b140c524185040e1904840d86154840d044c143d0b0713821441134189031211101001030034085401c0c201704424091141514900800d0494802407900c3c0c11490905501103030840d01d0b980300083c40f8980c1c04140c11000c0c5403401443c07c0d6103200c013031031616032080c0c000e42c0b49000b04c001080c127605100e99103c4410500040601000100c0310305444400b841000c0c11420b1030000f2001c0740e4503403944c1000142408000c07580305a9001d480000101d6000705000869400c04007014a5481e00c030803100000285001c2641150a280c810000201881c81306e11081d405070000e102c0e004402400840d000313003a515004107180100b80b600032b084079107402d03100000d192102c40032600a0f030720106083c14010741d07010701c049626580c01d0284612b100c2103 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 652192023 1250 652190773 652190801
    0x213021806040f090b04110301051c051605030613080f0901140f090112060f090c0c0203060115271208040b03042009132310061e080d0f03 61
    0x40c001401c0203c060f040c41190240442002000d40c400c2c10002564400340404210032400c0c8010f20036450310500044100845070361074050180156030342810a4110f0384504800d000242080116040034065103a009400400803000720f48907680d0300c0b072280522540b010f1052408921403406c0e90044d1a21240740f040380c0e1000b5214901511001c11580c01100b041d40042c8182c3c550f10003184040c01450b080c0d4046103c0e0410450070541d0034001411100e420400304050788200c4000758405000d401d0284c00f40c1200c5107280ca85203170020341001508002414031000c2c4403403640d07005212080c880196441da400e24000883c0718181005113004540104140a8000040c002000025046900b128141c0c80744001d02e613050001b0001020012648840c64001305940f00e000034100c904400008640981c02803020280560131902e082c2012150620071555844117101c440641d05100803100480505d01280302c0c140010b09403034003000540002400241c001d034202a07030003900708201e0301c2400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 652193273 1250 652192023 652192027
    0x120203040503060108060601020127030e15030f0f0c0a080613020f0f070c14010c1401180b101203020a030c030e0607061401060201110412020d05030c0a030e09040213021806 76
    0x80c011003501d1b00c2003507070341c940558038000d003940ea410715088078022800d40385035510268440ea600c1c1a105042c4034040994400d40c420720348140a60310b90043c42c00346c94044541d003014940110034134500e80020b099440c480400f0f1041d40c07803c9a110380f0250703004270156008104501c0003100c1c40007a0142c100f4610180401051081241c400f060240011500800503260103540d114460303080480c10139040c50004a41c03034011070100313202c000700044401124000085400450740000c681803452241151740164020501480c0928a8500e00150406c001490481d1060342d6019565034403032030b001401e200902c403032001418080c0078011600d02c00500170031340e41d9006141c04c1008111080140c90144401d85c00460001d10503c0385148070000d00d104246001e00b008140c8640400300e1400700c0e030103185845108002203050000c2c00d4007280050060180400d10726020301590b00c1001628040e00207001003001583d2180880a50301d1880c0780010703134030b10403001c0c2000211500c0d9a0240c0180c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 652194523 1250 652193273 652193279
    0x7030c0807080a180524070f0203060907030209150f0d0303021614011b091e08030406030e0f060412050a110d120e01150e060102030d0609270f1202030405030601 71
    0x440f8840071311a203441c0c0800441d03034840c010401c2291000e2040d50400b80d0381200300030081c02400084c80402e006104900c94643c00c0e60000e1328050f01110310f082aa0420384041046092000e40c1c19001300c0300c003c0d40c5000401210100381003211224070035200340300d203415220905020f503044801107070780440100300092003170074240a07e0700c0060381a0000d62030030310041051300c24080241807803c11a5070b1808001c0c9400d180070b9060240da1f452000920140c00c0000360114100010402004542c40114400702c55003826030404c440c0e9465034000d034002108000021b00088104490602241030140c1c854550100446e0b01054802081000744110391515004640105000342c455080c03280600c00c03200f07024265801e030742c40210505007001d801c0074180107500341d102409a008006204490809800200940640c0c960741d2021004550711202c81e0b036000c0081850400b0601c000418000d051420b5a800341c10a5411001600d007500580e130410741c1610078400c8400400c4002c0860b2120350b1 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 652195773 1250 652194523 652194527
    0x1b03070806150309061902040b0d0f0b060708090402030c041706040605070f08040b18030403060603030909020412060b030c190f06020604030503180a020d0605071d0607030c0807080a 80
    0x4080d502544155102c401020158503008100e0784900d1051001d000070781c81d01700111803521320507003154080c141c007440040382510246002d4030542d00381d0480810010520a0610700300c41d161403c1c140280700070842032021800703d8048540d50305040e14016030343e0b5200c1101c0c541d01c0c0141d0b0040f80302010140880c00c40c140001600500843c01030404100684031284290340c1c50321301c40b00780000304408400180115665400499002da600030b100400002c403804003500315801600211486030361010140185544122010050103070728408520f80b90400802d215182c8075440c0c01810700c0e40390522541e207503d0034800351a58800c060400a10107002c8021414806014000d40360711032020340c80010b145100140c40c0340101c9d00742d15080e00e5a16000e0210b065211004030f00c880c0351003224600401070721001e000421103401040e0000d03043c100f00c2070090141512003480d41c40d0707907415110400d081c1d0322101101d40140e4107003454240c5054a1a10101038098014098003141000c03401d208025 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 652197023 1250 652195773 652195787
    0x10906090501091a1005060306030a12020609160f230a0b25030c02100221180123090102070302040203010305060108061e01090e031c0f0f0e0606091b0307 68
    0x41d2107400100c0240000b1a90080c81c0b003805c940428107017041d8142003149007000c03030007560402c40107002d640900426440c0c10385411640c06407000143e00030707800c100d540d48045c03028844420b400241c04441a20b814440504a070040c003030b8500c4400d45c141544600d0003810242d92803c2d1001c0d002440c116a00c1d64498140d810545a205240b0b40d40e182b4412401d80c24003d460042c2e5064a83d03100400d1307036409000d4048618009641507201d041c3c81d840580c100085d0290020705102d0540d950351715107220382000d80140c2103030306051002c2a011020a80902c01c4c0c1d00710300a00b6400740540750002c540040b40707000c42551010350080e01c0000080144880469000c0c1a15a80000c44445031102c070710200303464040701c0d0240031005850f4018010a40250010304d000c06240c01124108800d4140c1c40b600e421140c3ea0302507005540d42c420070464140e90044003100d103407426080041110411000380c5480008003610301c01c0d085000000c0381c0fa20241c0e800400710190131011512032a03d204054006 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 652198273 1250 652197023 652197041
    0x9010912080109230705031f030609020a060f0c080f04120f1406070c080901031103070801031b1d0601140d060815060d110609030109053a0e03010906090501 69
    0x41c1341000c4001030000034080103200401103003c40c0d0a01070b5910700080f2055080a0040b022076802d030b001c2110500360300d80686000c2c600410001480303480d00d204024152507540c1c442010f10426121911181f40c012800c1028640c100c0c42c41642c2c0c170441b03402008140f007240c0106585044400c04001804080521090043d20601d9020100c48036040d406940c0c80c822034000000a521500e100c00064580002d80a40d090604001c1111420803201c405103401c1102c010380012021801001030140d80981e01e4a6214000c116030305007800c0c62001217042c0c040070300c0800d0202019000c00e40991080c41100300700002d40700740540b40c166038810031000d04583d1043c0541c0344905190507001c6c1c6080c10f49a0b00030a00184401c440e000d1560b1001d58500040f080e6951050041c00010f40d81c0d1400e003d6480500c0c03064010b888054140f540000000c091a42070380d181d403031680d079400030000a2502030001ca00712424000d00000300c03280081e02400e40303401d004264a04012072a802c024054108650b2 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 652199523 1250 652198273 652198289
    0x1a1206010f0f051e0310061d100501050f1809010605190503070e010810050a080d0206090f2d01090b060405090c0306010603150b0408030415030203041a090109120801 73
    0x15560300000500051500640d5130108290b4201088001c1c1100314501d00340340542650840f041590001044840c941e0042c00d104008440728000d00c0304e0428900d60214400c1144419a424140000c100303001d4105903901c207820009603500d000ba80702c003144168050003007800d00c00b580c580b80020100c0e0041d444482c1d038100180d00f01c80d800e50040094910640c081e51394100c150344a40c0044403a024054860070104103210008940d5441d0018034070003a008600080010a0040c00024604407005180102c25001000b5143c00c81002040c1c4142c02c807624405080060300269401c100c602903844c41412a619290715034041000800340544968001c840822560380c3c1c40940586940d00d08640c070760705811000044c40400c1c001d6000d03201d04500864078020f599102c0d03004001c254001d8100c0d800e29400440c04000d40d0050000e941c907038022901d020740c2036040c96502c0c10034002903c9403205994043c00c0005002442c07d602c000309440d08882c072041d0b161000040a052481d00b070080c41304c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 652200773 1250 652199523 652199549
    0xd0c110601083c0f0309010207080105010f0306020c07080610031a1e100f1d1308040603020f0d020703030506010806030a0b13020103020715061e03080703031a120601 73
    0x242865000c940030300215200d003810b0100f56040c0d40307400e00800000c840000c03a4454108000007500003001000f0720412070400840d59040e5210004e031816586512218031a818080140140d4a081440303400301e1744d0000002d601e4007425010681030040d0f80d00a0b10081c424041045a4910354581181c1207074000c481e00c0e05107070a1044820700340201100c0c1052044504001140660f80b490314040c1e20911007000d0346181c9445189100c20104983d0200e28503190104035244007001c40252683c201e0703044045091916426030395101035003d18482c1d003083c140c0c080741d02c689038040d20007144c000c024a00303030855588149140141c0200310075102240003d6401d000658141030010b000d2010641000c29501150754003071100d04a00c020300822410907400307000d40d00010320003541d114100c4440c148040b640c21b0070b00d03140f039041103a0f20b0076040382e0168001042022031022403c8403a616050b1602180c07100b40c901c1c040c16071410f01c0c6a016005140d40101c071a0003003000c03602c18166041a41241 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 652202023 1250 652200773 652200779
    0x617030d110741061303021e0601090b240a02191a07181703040b0307020607021903080115090302060a090617060f060706140705040504180507050409080d0c110601 72
    0x20f8000c40d41c00e010503002d43c4001d0218052410f46021000110310910403030301d00b9107850001701c1d05c901c10010242600d83c8024014005891640208680f14506480d189101911900e16001030302541007034064414000070b2000c0c00c41d109102c180c002141768031111113007281c1458000310050448418044004c501c2c0082040c1d01d00c51104c0c5040c00e02202080c4801c58107200800759000007807404e14009200400001440d5134402d0048d510442c000e801401d806d14080001a00740310006030080340c40401501d5003030020b50803c0d03019042d200140400714000d480e00f8819584002203400181d84880d001c5114074a071940609030368159601035465202c0080c20480c0e880c1050001d40b0029808404009158450b080c034078080c0070858050300003c9a60703040c00003c21403c00d41a11031000081c0009018025130400380900e002c14082032012180c2d12401c1e88841d6201c0c801402360300c1c42562121400780034400e0640c243d40642070708510030401e49600d0040030b464a1706e03860520421f4007603c0000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 652203273 1250 652202023 652202123
    0x20609131b270e0105060c030415020105011d0402030a320d17040803010e0c13080109140a03020c1002160e041b0b0901030209040207051c030617030d1107 68
    0x300003150190f01000344281d08200c00c00c01030340c2000325900f00c0c41c8020300c0700142da000c0d00c070000f11400c43e031038000140035410f06401184030001c8525040b9001081c0c024040140c40010307824040035048200e2071061043c5456483c4950721500640d0b18011503130791101c25187c000300d010a0084580e8581180da0a0001880911110121809840c2d440300f03200400c542142c2c200065408501013070001c0c64160206001c00746000660007850352070390b5814801c4108201c0400030804070000b00010300070100b142c0e4009580311660f824081c041c14040c1002071216000300031502c1e003002440c62040ca40d91b00c1da400300130141e0342142e042d201b00c000083d081c5108911304401900765601080c1d020324000301c400055000e588134051071a04580d08200040104a0902a0b102c1006051103e0b41402c03105d160014251011380c0c1042d059210085c43c2886c1e00361000003103484080000001043e6882d295608080d03a000f440800341030003000f92500004031201c03051000d0004900800b424508a0351005 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 652204523 1250 652203273 652203347
    0xf0f0601150c0609020103151818150e03270301060b0705120703090e01030807050d0305061e0a1e06030e011118150c16050409020609131b 61
    0x45040802c0001081c00041900c90304080740c03490040c140401c0308158070407492904000f40d4005c0841a284903c0001150b0841c06001c45141019050046803002525001c81f03420400341c1c0760340d20680d02c040b812124002441a03c0c16400407184202d861000d082002c1c048103098450603200b135203403280114201c4075510503640381c1500000209a207035054440300d825684590300550902c10803100003d051245103001c54040c501c83c0240e1794465001c1e02c0c1a62034148096100c100307050611f010000e043c0c6884601c01180c00320b88040a580740c08032004a03100808680069020021280c81904041c120060105c01c413969550300300300e0096116811822143d21000d00c0303221200400003001c000c050904444032500700103100350030002c500020701c9900d5100203e14411900091201210704800945140040009441c140200d0b0010b078005403480c40b03078000d514420076807400c922800c440e003540814800782005054100e094000c101c045d000076501c90180f821203204522a1401c1044960 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 652205773 1250 652204523 652204559
    0x60c1206030610061d0406060c1203140610030f090524010b0f070311060403020d11010605060406082205100507110d11010f020f03090105010b0c120901110f0f0601 72
    0x143c026807400c0440c2194001d000d0152080e194800d0010302c1d0080e9614440d010041c895500e070041401010301d0400d0601031507030b00318414149030104800b1035141c00018190f0090007140e000c0520440601d0507002000c084802e0480c95240c010100f0410000180351442400012040840b001692404c0c03581200700340281000b0a4061080b0031103940030902920301c00d40302c2c1c00c01204010380c0030886894a5001c860950040e80550800240c464020805012801130b03800244019820600490102d00c620302c00c40d802c0207280000103a415494104400c0040c1008602009000c03403800c0c090f540f401c0384482088403500c2c0202150482d40100b441100b4442c00d40013900d0502054441940c000504040d500e02554a6000810a00e001803009001082494a4183d00ca06103d0b43c11403c680050300b0650b81d0038801c10440050001c001015450300d660344001d19503403020300004035889040e070440d01840c0c1c0306100383c24108920205c0c803020b107403440f40d0071151142e076141c0002003400d0282c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 652207023 1250 652205773 652205791
    0x60501082b020309220e16050d020a12020103150608010e162f07171005010b16020d0b010e09150613020c010b060a09030b091506060c0f060c12060306 66
    0x3a8410307078100f80074170140100e80c0c40f05205d283e202202e03a00040d00c1120084c018203800c451450785201150b009201c000c0d082c152180c804003d0281c0c04646681c460340210045261080b6403035007160b1007500008000c00849090341c0e545655040007801e0700c5420f0141d405060031200000d070300b95541250904203200c0c0c03a030311119003141000603d2100004840d400d82c01580483e00c1812480c404c10030a002010010082c90b41c41c0040c0c440503040c600c08190080301d0a041800400500a40c101038429902c020800755000040a200084e00e2024505008144000200001a41500005440d441104008140c070b00010510041c2d000f00345c401c40f5116400b21842001d0800041541d0181c903000e00c682c8000110b511010340060390760b82008456400244921805108001c820b0081c80d8002c1110802400113141c055a46e482c0a00e000780014003400e004104411141c004000480c2e13550700000c1502c68600f040b0720000c41642c4a039010360101704081c0d010942c0da00700000d1151107400a0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 652208273 1250 652207023 652207027
    0x30207120305060f1c0b010f0608180f0d050702130b1c020a0306090c1503060b04030609030210050411040c021506010309051e030d05161713060501082b0203 69
    0x4240d0080201030f00007a040510502041c019072036903464641900707031240705000f80d030803145005074560405030000174642903800e40800109805c9080c454000d000c00003d0144511030303904803803424168007126a104e101301030140e210b80e0342000c01000403900036110b1014444529140f40b0a0350300b00440580c000c00c490700b1801428040c00d80400d03506100912980c6469680c0d1074031401e0750540030081d10f840d503a60f4806c110b40102e207800324141041a007004d004d150b02d0070003001103600a921003e8141c686402180003054400c0c440000e6056250004001a0034281003250014031152015405540b400d011111201c1c00010b1556a003281d0540003090340c0d075280011400f501004608850354410104c407852221040103101c00300e5200c1070020f5440c0c0c9044031645090787e1024000c0c6c4c8503850f140241090b61580210020b0044140780c1c2103480399140c0d5550310002d03031011708014144034603200000c0352000c008100c0b5140c2041200501200c0081400300c050419503003a082c0d030140e031003 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 652209523 1250 652208273 652208303
    0x2090f060d0b030a150e070305061b1c0c0e03160512010b0d1a06010914010c0503040b2107020106120f06110d050f07050a0903060209040905070308041401030207 71
    0x10000c02071614074101e81001c100c01e940500070a1624600100486616046071007030680054548509250140c80d000280301052171515180e4440c40003400ca08841c50400240e004410036001c12250102241c4500f000c0c96030035440328038014402000c9a100081c40290540c00c03502e0000b4064405100040c918900b50345000200540c42043d0042c0603895502c4110340105030b942c1c0c2044024403402280c035500ca50403007602031005004001d140d0341c14483c419200340650714080091240120782828020810041da0030054514016075100700d150030390000d0780a40c60421900100a400416110b03418030391250300d0140c0c01e031481c50145900141201ca03600c0b002c81c035443e42c1301d17100e5406160001440c8082d1012070610ba070014540000040e02c40081c00503031a03003900724650118040c82c009044c19444800141107040c00d100140070a03070041030108441c2e50360341c0180806640101201e1550fa503902d0001190341084c0f0506800003002076030200107500a008443c221a4000303411524001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 652210773 1250 652209523 652209529
    0x3030a0e01030509010e07080703110d03090308130e0709030203011d19030c05030406050c1501150c0318090507020616140d150f05040e0109120305090a0f0b01060f0302090f 76
    0x310090801300c070f030740d2a400b040c41d101005002d00805080c80c0c2015290150441c00c0202e050004002030714007803c0c80e59150b0011907800f01ca1203058035407110040d90741d46084040079041051941180c80070180d010203005180342c2000c02001100c0c800e400900502904040d203628101561030410740c0c86c0c1014100b9a81c440c400c504407881d403032003030604e04030792095902c0d0145503400503000400440c81c00035580d00094010481003084600b8098400c15035030501c201c2902405225402a080c0000c070684542014000e5021080318441924146d2026655400724805464162410f002500500010882004040c00304050901032a150403061001c8000340c12001d90020b2030b101000c1d0313078400c42d207000042c9400100300100b242410827004182088200802c440c1e205290110702e230300d000d800e40c1c00540f03100340841d4529014240022180e5072154010b0912410000040070441036121490421031041c50450681c0e0983e03850924010740b0010941c01c0703104010149610070040103044c04e03580b23 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 652212023 1250 652210773 652210781
    0x6240d0f030212030a0207060b0906010f141612090e070f0815040f090201030f06061b0203030910021c361a0919030807030c060912030e0c03030a0e0103 67
    0x511a1044943e0b0244000d05000190030580740e00794146c0d00090040d060003464010410241e00c21608041e0300d003004c01c00a40840c00900d0a039007446008a0f00d2070000360000141e0381c03811030540e294030a6414528040c00245a00b00e65100454200a0086504240202d0051080c003940e103418600b40c0c0080804c1e50105801040348811444c01c07556151740391228000c0540d0101e0100020071440703001d20014040e510101d0506c0da071a46051002c202c0f0a60014414102000b40a00c860101c50203002182c01d43c424180c51542050b43d154403200e109500060b012100010404401081e045d00201200d041d500c00d0f02d44032994002902400450103081746280e0100104003807114000c4e500c42806000320b051808200c118000880c24042a043c0045d000d0003000f201608195414207507650700c1a1805030340700160070402c0802400301004015485407022903000144c40700c10248180300100503215055030410f5502800100d0035040c01c0010a0b10071640294541c07181d4a80c201c0b00443c020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 652213273 1250 652212023 652212053
    0xf1103040b0a050919050a0606140f0f1215040b07080402010c081612122724021902011d07140a0b030c0c210403060c170906240d 57
    0x19000384101c401c108550003a0120085d44140c0243c452203405041200803900190302c02d01c00611500100c00d4195a03c3e0800781d0301c41005c4902c20841034180c0301242c01485002642c9889100782c9542042a1943c0510781d0310481c86980c003890140d8a40c01d0489040a094a00034082450b07d0116000144060302a114824903400d125401c0c0065446001c5a50012404107002c80c0b8422244c0c0e800503d14006e04071000040840d40581c0c041811490410480040000d00317007106134010702010000d400b00440540a11302401e5466034010044840b080b0740c40a026000341d881c086011480c240c1002104407864405c10103082c456103000340040c6440c00c0380041941c484601500032a22038141c1000d540035a1080e40001d03240d10095005502d491034207001100d0484c580d81901d150b132000c2d03800312420749500440c08030303000d40580019682514895174802115040c441080031442c4002100c0b84214180761031070310081d40440c40702c0703603c0f601c2c03044d85600a00c0c8a8545000b00e806c9841060103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 652214523 1250 652213273 652213291
    0x90512031608181e150d06270b130c030f020313020a06140f090d02030a05010f1d0a0809010c0203100c02060609151302040f090f1103040b0a05 63
    0x5441400c1c1d58681900241c000219024007001c110800c0c16a030740142d050b1990010355840f8190022440301d05820101c6122a501c10041c0c0024800405e04900035181c4c800d080a006100f22a11400d55070761a00c41004000d458040d0386010001e240c201e07010381607114001801d4004256040c0300e0340380c0503180d040d10342d0040c582c440148003000e000300c1c03004601c203040d200c5903844400f10070701c104000465a0752101003007001e440641810080c83d2411138041400e100d4555540758004004140c3d420a481c40196060203121004014040190004c00f00f46840003c01c001021490910685040d20a540080180d001c80c1208001483c02d100070030b02c80005041100b482d5410b40c0c00246030101e02d81d26000d541e42c03128010302c1c0d2141c0410543d074001a0490b1002c84a02d00403030a0750081c600007651500c0360380e6018074509400e4160b81114050000c0f0007211490680b101000360107040810a250041440c1c011020941a1140b0549001d00d42c011110301a64960700c4240020308400703084146 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 652215773 1250 652214523 652214527
    0x80403060f0b221e1e0c050a050304020d0f0605040302100e0304090e0304050406081b01050a08071b0206040b040e060604050603190615090810060305062e0b1c02040609051203 77
    0x2900380c807054012042040140408078074200c0411700c407080980d994442e185803a05001440c15101d4100c01590700d10781c3c0768509640c4036030300c90000403800404c41c040a0003604105219074140143d94101a21a078025000c6401140c501d000880c00c8030307800600005543c20900c000c9c00340030803581007174124050b0309089034282a203070340009080b031300264425502c2d640b04400f80205c142c41c83d00501d4007240c0900b4142c3c1071030001000a448910000c101c88200320820240c9040c44054826035000b071500542203170707203c07503d80003140029071050003140320180c40000000c02615000c002c40c1c1c155030000e840300342140c0f03881c0034041480302e10308040c00c0940c3d151540441ea501c16491801d40313000c030300c2d900c030300740c041c9444001820080e00c0c148000c0c0c05410b01805101003100000d446400c016510003d4207041080807441e00e1640d80b1810580d4088a5070900003a21402180030744070760034a000b00034000c2e0590702071a100300e1040388038a001050b01541c017009a07180900640ba44690a02c043c0e074 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 652217023 1250 652215773 652215791
    0xb150306211207051c050306090403030207050d02030426030d1e020d0f0c0c05071a1c090c0f06021506060403020405071218050a080d0b0d080403060f0b22 68
    0xe040000c28116403000ba000480d07031400744001000300c004200c040c40400c12444c0d040120042440c0710042c004c9024038801c50101e01090302c40c0c0c4c122502d494012096412410750710300001d40340e034020b1080b045c0701400c01904a00b9101d0110081c01045100e80c0118a402c500c0340718203004d1b1009007d0445651072050043e201300c0c900313000600c0d890749050f0300001e40031418210a011a03524044100c01c005100764004000349000424030309a8070024003c0c0d10702401c060380620780d88101410302032005043c0c4041e900c1080b90303402c98800320b807065081040d03e588800224810507044d220340001640020780707100004001060064000f003001d07203024030f07090b22900031805640091b01d41000082000c81c481e11600d0051040950003024003407108840c002a456282c1c3d0380f60f440001800340342000030f40d900c0c91540c0d50300122000401800c04800008203003030481d82e980291105481d020304088541c645203505100d943c41c0014001c1219240b0000c01c10314060107071001d100c1121095580e2061 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 652218273 1250 652217023 652217089
    0xf0a11031e01050919020d030809011d010609050702240c0d1109030c0f0609011409030106080715050909040b100b0c010606090b031b1c09030302030603010b150306 72
    0x80c55075503012000101e600d0401503015031802d0703000c00303410800c6100103102d5401603480000044003581c040c500780100c0e40b901a040d90041c9a0040c4090303030311820703810744544810113401440031a000010200010341c0c50410a81c1c8900d404a54404c2103a110002002d080074002688e54102c0d0400c4082f0b802d0011105090342200d504840d000c1040c2e04c04100340c40c2c68075080105440f00b0409607040d2003400c0c08400824883e02a600050341403020000409110402001c1a1555880014005c2c0300c100d550380d100c161903120902600303c4000102003d00e841d40d000d1070485203000d4000d00411801c1d40c550b101c0c0600f1500c098403119101c022020001100c56090000d0301ca14403c080000522030b150160181440384181c0c004142000140f040041c6207a400004242c0e00f000c100d12142e40b801100d005104002c00c59080c00c08c15490080140141036155018512858007900200640c03d81c0d0020030100c00c1b13100e0303904860700000700009011420311242c9030900c54016014055405008121 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 652219523 1250 652218273 652218313
    0x9120403122309090601090e01170115090e101a01050c010e010501060801060e031f0b13020a05180f0a030311030706090b040c0e0f01090228120506030f0a1103 70
    0x3441c0700c01007003c5502080c0740b40c640c100580041302402c00e10082440d09414003d0150148100760b114080c0b6900c00e195081d01390030180041e541303540442c885984030441ca000900d20482112061b214201c0c07403191107030306481039440341c44110f0b2042a445286000440381340d84a64411401355403140c44c03141115400340665400b0b45490340b510f88596042031401400ca0b0b8851100d03602c07039408245810f014455426001c20150a901408a80450610041a5000d0a00c40001300e55480001c1c81d2030350382da1210107401d41e0304564002050341150b09040120001c100103c65601c0951502c082001038007940200450403880e0b0184e9003480740c652618000c07aa00d180040d500c0c1c8a0800420042105030855680501281c1c0d00160080c140f0226032800b0003c14050824295030004400980c201040303e005498020140b0301070b451481071000a040c22800020748407260f040c400815114079000c50100756508414004018110f110f442c2c1c0041c1d0300c00c4084c040d42501460308020030010100207 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 652220773 1250 652219523 652219577
    0x3110304051f0908040e060a080313060e0a08060a1508010614041404030212030c1c020901030608070b0930031c09080703032c0c0301050912040312 65
    0x54903907402c0903407a00807020540c181c0c01c1d0516190040950020383c0003029141034592403441540315a60785401319a0420311500328040038480840d04203041c1c0811803003202600c69556405203034011100c14000d0300400c0d4080c60300c05410600000b000b284240c0d02491031283c4412510b0402c0780c2d250540c908507031103a0441c00701201c140402205034106070003980c51030404030241c0c0348985090f4400075124642c0d900c030700d002e80d1000008a00c1c1d9248410a50341c0354000346420380c050b208031a840c00000d621840341d01d40424100307400000e02080110302002155005440f007031900c0854010840c1e11900220144005490800f00840300b07940d24191031219124a001166180d581142c5032485500c07000c20714400509094405000074004426030301d07400c1e40350502068488488030408100c0b0840e020382000802c02d0380040019000000d100003d501c410390080202e0f07269070f00c07020f07100c20404d041b00d28100c004000400000300d51a07a0010303003c81c140f5140729403001c40d510b070b0b03012011919 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 652222023 1250 652220773 652220783
    0xe04060306020f070b10120b1f0e061011101104030b04060902210d0e180924010f1a04120b01050f010e090606031b031602070b03042103110304 63
    0xc68010100000c21030001d40207109918813141080c42c02841e0860f072100284001c0c00c0100101c08501145029149900c6512029200f27045942e103905503410307500011107045200790b440f0b203607543c0d141d4011000205031400c601c0c050080304907000c0300800a000c413002e861420180c100000008203220811146c0a5403107036101060f0350016004000700040d1071031070141c08408503010101c0001000862000150603810012402000c600000e00744071010000403200100c2c60040022032603001ca030544501c00807101c010210512080b54194040090052080c10301210f00d0072b000c0c16400c5000d80300107801402c00e05290070340328101c0c201c0440700c5042c00c40395080c4420050000389400c6c42ca060510b4828070340000181c80030b20014a03100e8002d02054000d900000114006402303400f03400340300107a5080000d90f40d040c4090588038000002000c0070040c0507a613008901d42c80a8000c583c0902d0b0481c3c10203403600700c1d002007400b00b1800085042d05150ba2101001c00c3c00c807401d006507216030701503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 652223273 1250 652222023 652222027
    0x50a050607022104050f0a0506190f020d230f0a030e0705010f02030702090a0f230703060501120507021608010b010809061905041119090b0d0b070e04060306020f 71
    0x8000041c1c901869002c2403194240303508503848400340d80c1c60591307044600032a40c502a028a071404541e041c90950010368000c580041c2c00824845107900c200140c01403a510b5008041318000126107803559881094001800b80e00182106c00310340c40848040c0001c980480d20b454090310140f88203502c10003c0030301003910340c181c41a0f42d0009001020040c5002e00f4081c80442900c20020f441e071244040007440780204001158001034554444421240d00f40800c014084107003a14a000d5000c2c8103000902c2100040003509003480f074001c3c5003c0740c00c10b850b01410843c4c49003800f000342030300801c0d0800f14072500c1c80081101d402080510010118400002886804440010240301f002811001035600c50024440400c01d400c92050300c80001900000312070700c03140b81c4012107400c401e10003580300c50744c0c140c0080711007103c403c407008071401c06400b00301c003e120006000c040c01107132202501400090f4001040e0700d004984c0322480b05002003001038529100c2c0d40e020200e80205d0a002414100 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 652224523 1250 652223273 652223281
    0x10b03011508120435010c030b0a0b160b04110904141c05160804080d051209010506100509180924040507051203040e010b03040b180d1b050a0506 64
    0x828422040a405500743d41441e00d42006560580a8a00591400d101e44410610401815224517200c48008210000d00185921707000080182c85540c0d09032b803043e17078424800640c802600e1308655642410007952880140d0a031030308219a04000c0080c0e86d4807869250a043c2c40e41c45d035250501c680d124000c6072000840700d048040c40c222038521200f40940041201f051a1908807007500c0302e081140c0102c203000c9005150440e240d02807a489081944a01440b080301541c10070080c003103a0b000703102007a00710b40d100600c8500740c403400d8440d65000307150007440320000e500c100010554080007410440c4c140c040e10390345003c03042080b101411240c00c500b0f60304039a0006c50f07100c80d0044100d622952524102078444070b80341e0a061103001e2003641c4e10703540700c0f100d09002c1c02940c000709240110358081d50307075400c4e001d516580100c3c4c0444a1010800001e1080040300004442c4081020000d002036039030080c050381c4022600d40301e22480002008050b00280d4108041b02100d8482e201401c40f9080c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 652225773 1250 652224523 652224539
    0x6070606090914060424021c1b02060c0702061b061e10030203061f0b07050304151b2d0606030b0105090123011e0c0b0a020f0403020f03010b030115 65
    0x141e010101a0000030034003006c030740b1442207100340105d4495010801710820343d11200074800c1070300301070548000000c114010065603000282e600c48074881000a5071944204a84130001111483c40d5450140000c07009418458080c1c00503100341159a1101f21a04c0c0303481c5c1c640801220302d0b040700248000b080e009120003245042c0c20800100c03000e8001e07400d682c006500c07404001c10100d0741034802c400d410902c0e61004500c1004215a0310002d66a030154203045450342d000740640e5030a07a040a505102c09403080c1e01021209202624003045804195aa6448400c80f01162070417100d2840520098501d2402c04010300c1d0700c15600050302600c1c514021000c00d00590195115000c2a401000380d1400a0801d001ca030700c0305c40328130300010104401680d11407101d8450b00c030f4881040a414203000c5c0c120070000901e40c010902006240d0f00d500340b110503407040c400c2e03101007488140300c2040107040c081050100000014004107840d03e1b03000c0801d00b1103201c00170f0340c500e000f9044410040b0308 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 652227023 1250 652225773 652225793
    0x9050406090c0e0303090a3003020d09060e0d061a0913021e280b1308010b030c060412170d06150f0c021219080307021e0a11060706060909 61
    0x42084d005182009a100001012601980b29552203e0480c10349402142441000c240d80002e03001c4014030303440301c5030400a68480118540c080401c1900101241140c01500d40c690001c0300108200c0080c0899614100600401c8403215540f03080300d0324810301580c400c0003180c45000642d05120b0002c8141c010000d0701841070303050724100c4000c0c0c2c4600c4440d80b00c000400b40c0e41034030310126420895907a03000ca12054200d9001c4070440c0004241c07520705001c45040801280c208800921560300d05104041c1c0302c154012515a1050041104001c4045200c01c2484580c0c000c0680c0200c0c990f0b001d02c0940d090b4005405414200e544135402c0c060703000b565000340000a0140ba000070742a00c40c01018003003003d4000007030300c03a503100c0741d40d00c5125004100e546004c003e4040683c045000c6480d00048681060b1092000760050b1005070003200c54520301113000c501030380010000710310701d612000440b4501c4a805900002c007044010045840c1d409408018480c0503000180d0144c1810105042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 652228273 1250 652227023 652227047
    0x3191511032409070305100306020301030602030a0f05270f070b0d0c02031c09060905010f050604061502030d020a14071406100e07080928141609090309050406090c 72
    0x30501e4490704080503100c0150003640010135040000e2252914101c039112107810b640700815040c00000040300b009001e40107140190400d0780107001044038aa071010a4500441d0f4401102420040950380c61034442c41041040c0045000c1d24441e1003071a140505000d4144c110644ea04170000b05c01e68141441d20581c440c1c00350500c00f840c03c050381c2040e40d01d98400307110b003485142da450f011458240f04681c1c0c0484440c1d0f0344400204400c0c003500b40c0301c4015280c01c82d00c6901c102e2825400180c3e0704450000010680043d5000d035181ca600880490000e403c052422401c2040c030b01c9104140e84024002403450600616991408001d54150395191080081c88150320b100b820400b082416240b104998111305141810230450b9199070034645000c0c46106c6004400c440800003181d605481641c0e040210301800d0008134050051004d42d039100c030803080d540300720040504104901c41d0075a000d8a02e440c407a240c041340e156aa10300040555034650080e4061a0b6030b0801d070050150451052120 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 652229523 1250 652228273 652228321
    0x120f0b06040f090506011a04081c0e0604030f061401060f1b02060a08011e0f0902070f06050a0f050f041208361903230705010603050f0f0703020319151103 68
    0x151500303149c0503540310a090102d81c5202c200c0412416261801180d4022001c0f00141c145510f8035981e0900d103107203003107001040d102907180400841849045103e181d040c0c0b1101d0329840c020301c10080d01164000c9014022510301c14881400e0001680c4000052440000e96950800f65506000150040d10b50f00e11101c000c4591740718080228071000e40b0000d04455042c5001a1602c003a800c001ca481d0902401c01000140b4080400c001410641c1c0710f40c0e9001c52003070b000c200c0b41d40d03403401c0c1074090b00381641d0103071421039000000650640b040c170031a40d01c81001200107140450b4103e8014420074520345281c6044d80440079001038800c2040715a5500500d0000c01501c42416107010b8010504070b80d000595200c18109800012000c104981e11650300c5802003010950300d0600540300c014030b80c1c035090580201c200110803140300040780d0050340d80043c06070200312030030705034204d40108148040b10a409081c2c5004908102c0e84911046d2a070007110703103980c038a0301c0c40a08201304407501950750 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 652230773 1250 652229523 652229527
    0xd0f050f0c0601330f0f0509040516030b0d0b040b07090e07030f0506061204030503060f1207030201260a0b0d2009060105070b0f06040e03070f0b01120f0b06040f090506011a 76
    0x15025441a00c60000417464100458840c031000000c552511542021503080f509110038402204010790140c0c080140d80e07035040045c950a001004844181c1070b0b0094268001c240206010800b02400c01d5080341d807604110082690360032582401220498502c00400d46d182c4503144645100c0c043d541d070000089a150749440d40c04203035180032100241c409000c02034084005406a01d680324804a4481d00520b030700d0010001c41855aa1a00c040c0401c900107140e0300340b4840c80045560300300100580d41211200c041e91390340d4071140140b42c170b03800710f0350b0000901d0408000320314103541d1000d0b4600408075241031070110405104449802400300ca041000400000d00030443c2552b220b03800003042c0660322401c3c0c42e0240010080e000564241c016408006000303003c00c2600300003144074502c40d103000c4407142c0c0e80f044803c01100b56210041d03c6100b80d200f41d0000509210b0495601000c0140700046103061403210008440c0300c0c41045416078070110051041440210f546000803012190440c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 652232023 1250 652230773 652230869
    0x5061005030a060b030f03040b07050c15160303020702090f0609071b0b04051011030703050c1314041d010c140a1b0303140f07110d0f050f0c0601 64
    0x1e60369a41c07022015111aa8800124440d980c0034002d1301007a084038412681c0b01c5446403a03000349075201050448441c4222000d050a0342000c413901c5003100c45421840f41018041c0001c941e14005206049003059402c20600b401aa91403100500400740c140c1080351918014041c400110307070141080083c460050640e10504400605110000780e2000c4001c0c0c4c0c0da180c038901140f6100000e9881c0c801681040380c1e210b43c8030340c04000366201c1d14480d9010b11080e11042c0a030700304c1d032044038511401400d41e0a41441010000c0c1003c004018010304001880a003e6a005408180e25206503c103651076404024680b6400046544c2c0c05180185603482c190748648040d01c0e4402000d03102e100c19241d0495181498081c0d030105001032074259010102c1c1c5015810407040701e40c1181e1039404102d500c1e200d0040303040c0c002500d10069956864071402207250750010368482c0c00c0401c1c00000071504004100050405024060007040601e4558900c0c1c20015007200d5828581c64128003607181c1c0302240 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 652233273 1250 652232023 652232029
    0x4080409020a020102040504050901090302070b0405090109020306030a050f0129060d050402011e020c0a0815060609030307020301060b300103020d0602041518090b130b060c10020705061005 83
    0x220112030203108016510051600180d01a01070703940610b52052030001040407491040d00500f4000b407096007914800e50310b0700061850342c007c0d8052103070031881c94030042c0081800c540c021500004010111101d1403c00d03900e29107801010320b4603112a94450120b40f65658003031b684e41003402c446c0c200101100d50741c04e010411030b02845104045860300c40700424190390107045844d00a03868131060301c01f88500b9440c040c1d5941990440140503110000001440082c0460400800c0040101c01d002c142c803460304018490304021819a4103000c20018640145c0d0244910402000c030308030402c0c0c5424035440c0078104110f406260411105480840c0c21a005100000a05480d4103d48007540207001c0d0031308400034012900b00328402c10110380c102c0d2101c1d420901000d00740b03160003101210310ba264600a01035170244503800383c02c01081c01034941c0882c400d0f00047e12204020705130030b0609401010451510b12070503aa01800c0da40060a981408014892030740d2107841c2880e10040c0300d142c4004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 652234523 1250 652233273 652233277
    0x10207030f2d05010516050319090206040b0d050f0604060308071203200306041104150e04092a0e01050d0b06180a0c02011b09060c050102160804030302150408 70
    0x10309480c18640b507500340a00c19004007020000324111000c035800c103803030403500074001a241d8155604012041c00a024402c41c01c482c8a01d00380f40c4403c6031903813130019050203041c080808980c810024080440d4025003031b000b4150a4032a5078000c80c042c107000290350003510016000c68004c604080d0b040c404158140101c511103a4462800d050180588001710020b22546141d290740103100c401e040c10402d403003005940101c0c411503040110006451100015100358030440d00107862160300b604419010702400040c41601501c003050840e15607a031500c03894149141da802806403c284200440282c0007244082c00d12911640c2040d41014009540000c140e03000401d21082e410000e00a92620700301924556000c072500c3e2143c0c07c02e041d04001501c01924490300640ca02568141c040c050100c490084400c079898180e0054140035040340c41d628400e0040c8c60340d6400b04001003194122110842d2440c2c000c80c051030b111821480c0080c10003580348071f00300a0001e500288001321751000700f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 652235773 1250 652234523 652234553
    0xa150503010e0711030711010f0c0b16051b0106030c0b0a0504050907110106080d170105090f100f06022b080105040b041104091d060c031306090f0c06080601020703 72
    0x10b105041c40c0e480d2032084a4449241030b015480b07010210b0100108514500b044490b400300342c035000c0385410020000c9070603240c5040302410355181c0c1c002040700c0c442c0411070040c1c802800d141c0249091020b41c241004440201e0f0240c403c0d079512042001841750b4403101102621556030170f28541000c088000b80b45000324010030788200f004402141d141c0380100110030780c00c80c8000091007641d54648080c1d88400030a2100320114088050181c440300c505030b8801e05070740e002005041c03140c542d50140340c0c4a90005027008400c103800e100106403100c400507030500800e4650b0083c080d0003113400d9840d41b80d40301c0d1400c5d0300e1401440813524100300d0304110020b041d1501524005003004a00000130050f2000c2e84c14200c90b40c20024000c18291050740080c11403122404a220350100005021035803504106c4030410949000c0c0040340c030611012408000090103607401094101c0182c441442d5403850700c004840000101508020040e00609402d51000c001d00103411198a15101d43c034843c82c0511b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 652237023 1250 652235773 652235789
    0x1201091118040c0c0f0c050406060309080723121809060130020a02030417030319090602091e030d210923031804060b04030809031002180a15050301 65
    0x8940f00144130301c00e84100000c1908000c410f44e1070043ca0500002940640c0102030242d0704040c80429154064002c0e8806a60b00107045440c0c041e0703e0b10344020b0580503543c0c0c84291030082c030b46854504c0c020880070444150240c40030355503c0000307400c044441c0e002c0651501414000c170410100380c1e049040466410041d9004070b01c450740c200c6000380103520b510001c14032a84003042c0381030600e60000142041c2c6a101280c10b00303140300c86000c29039038002110052142d00c03d0b165411107140340c6802440d90140b04d00400350800744040c000804074106040100404080f1042c070040f0303440d040120b010881e030039051090b0003500d4420261b0303035034403007103141e402c0e440e11440c3c1001041680040380d2201503004001d25451902280100d44076401070311340c0c00146042481d00300c458503147c0300e4034044034203400c20549041d1171943d030b08406070009440c40e58503010380d211066805031140010030341d1180019550900c50b00310320400c448501c25810800c102501c1c44a1402038a40010446e81034440d40 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 652238273 1250 652237023 652237031
    0x8010f062105011113061b08090d030201090b01030f0308060a0b18030c090c1b07080a0204111911010e0708031204050f07060203070b010506130b0a090b120109111804 73
    0x28180750303004d00218a2028168400051304e5901100080b09034429140c80d5a1a5410050004502a90300c4e215400c050b0800c5c80801041d8218900f0f010014601d0f4400e000200e01003081e512082c80000099105075160040340480000b0907030302000c0c2a500410440c0c1e8104a1820444240c8050060f09900e1000186102d0030f6082a50100f0504010f080003e0100c28240b1b801086c40d003c50b0004082e000c00341616120025002d100898100c095403171030b0005000702d8145808000241c8406124080c0c4400208000b010f030803100440881103140a8030740c080000d89185d2800e0031180501491661a041448207000c1410b010040f1185280d051003c00d95545403400e205040c03207044420301540b8440c1c0800000c09540110240c00c500340214644a42a80d84000f03100640c41046440c07140d40000c41810701141074406c025008a41c030b2803820010702c940740c50010000341d2180c0c0c1500c041c4a061001041b40007454055600d2880403402100e0800114075000842401040b800078841c44e15 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 652239523 1250 652238273 652238339
    0xc040f091722090608010b060712050307030f1404030905100e06180a08150610020a021e03030a0e1c03051803190f0b010b030108030403080f1608030108010f06 70
    0x1605102aa100d2104180000c1c003d6a622410000780381c01d00c0703250910b50a0074044e00652411809030780085400007100000c0034030b18a02201c2c5944010316100a040e510390b118401107010b0b129001000c5154038105116003810308003d00a1046035011238030036041031810721440e65000381026030450065945549842300c0d8114a00400c41c2c0d070140541054480f2400203070030800140305030070012200328200c0551203440c10b11001d13220720b1400c0409a800001640014140302d11070b541d903440c4100004042488040000342140d00c05048800010459090540b00d407a0202e034421000000054410381307141da9075000b5206014200d00064080b40d40d15070448541c400340070003c940000d110104040107081c0ca0700360312111104409450325405140042000c0d81c1d42402c403416201c4c1d45005504051655943d1003003039101703005850000c1410301100c260000032003070008c0c4003441016102d440e981420700a83c03c440120012042c0d060400c24208110000c0c40c0f40f106080c2c500801c00c101480d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 652240773 1250 652239523 652239547
    0x213060804050a0f05071a0918150406180e0105070e010507080408010c09030501390e060307050a02060c1e0901020102091e0a0501020318040506180103050c040f0917 73
    0x940044050200f1001c03081c00020851701103250f400382c0d021000e411303804104140b00c02c0980e00a45484541008903a440c414408803000d10a580c1b119660070458614400c00e4045001e0303c0d119406190305100f400d80320100a21240a429410384018000700540d142c0004000e1002058a2130903040c03200004e544001d0007103102c1210050590321000b80114409013070010100c1c45503100544640d40380001c0c5410200121514241010082c00c0440c100c19101950180003120b51840c182404241140b01086403250343c040d521801c260f4803400d0300d038000c080010b41800300050030b007040700408000015001074000d81019200070b140c10920f03140c04105005031f0081c401c00c880d540d80580c07040e009500400d50072240c120044070039180d01c2400c035910401681e42c0c0c010110645210380c940c50301003100b402c05900059000000500d000d0003d45404a042680f41084c6c1040c0c5180d00840800003d6080038015a071040c400d120081180003800c1c0c485102c420000300ca0b0340e202034400034030108040 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 652242023 1250 652240773 652240783
    0x40206070b0c040302100201050702120c0102121503061012121110061415031603060509101409010302090f0a0b0319050106090e0a060b030a120e01080a021306080405 73
    0x166201807030440c182031981282c0e80c0c41c0c00c80d102c2240300314030514141c0c00f80361040c000c0c54050210343c1c0003048011303140c2386a0404c1d5004218402d0483d03600707005041c283c0900340d403054016060780849010540d049400c1c541880c400030000c6840510034981000350b00e40b11200130009a8000d404610108000340e42140d4800c41103c0c01381c82c1c0c2c416500c651483d50100d9000d0740440f008402c01d5403601280c2c1c0c00b80480031102801c1d48024800601c00200c0c00c01030301c10020351a000d03c3c40c00040e5280c4503400205c0c03510003502e81d070111008408050020039440711300880821401ca42c6100e603903142d64002041e0001c01007441e654140407101040210343c0f550806203c00038014181c0702d508503803c41456642c4040c01c0c060351036600704040000c034161070f4411a05156005000380006280980f1198050017100342c92a4044c8a000c1e280c20100e507048942401c002803d03078a000c1d008a4181c001000708801510305000300d4410009583e09860540f0003c1c2103d46038200314540341d403a8104076080c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 652243273 1250 652242023 652242037
    0x405240307030e101406090703060609120206040e0c071101030b06030a0216050f0d080112030e120c150306090703052a0f04080c12030c060105130b03070e090f01090f0b040206 77
    0x140c181844078017089016500c4e14030480c010395106070b44d41d45072039085080c0e030b000d407144a001c142210300512000348003074400300c241400940010325143d6140089280340001320781d000d805513070100ea00010012020005c060011003480d06104140d45d14000600354403024100d03607132007540000c1702c40e0b980c002000f5608046402200340c44070b170200c00d185651558140000c0c440052030617070010508a82d107614000e1203641581c2e038254a02842c070140026244e503200315225500c503240c00340c100d69a03001d0303800e904080701c4c940c15a200d0401c0740600a40d60340c060101c8003032504180800c041e22742d070503101d54894684141415052038849500c00310328400c0f03042480d498500018085000400000e20300e44112050314801a071821143ca400c1e12401000c8000c00d03190001001046286170021b00681d6107002020000b8014000c0f000082c500081a0f10a2521103902010040c900c034090124050a2071048001e024005403641d81580c00032070f44c0c40c01400075882030082400d54591100b600d42c070f = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 652244523 1250 652243273 652243303
    0x603010e130c0803130e0118020703020f1903030f0203060d06110f1801081f1404020f0c0109031d15030a11030907081204030308060d1e080405240307030e 68
    0x486621040f8407030702d95001424204011880700c1000504100754210300b41201c1c60136000c02c680034941c0b0a580f003e5800114298214800c1e4130089190308030a0044e801c50411580c407003402c84005280181c1a40c1661040d00c695a206104000494454107a60120b4030351003400080c021801e00303a046100d00689084184010002c280380380410111006c00708036000907210b040840e5688010815a1a0140210400044c05880c100044268200011090301000f4405070414201580c0242203411080814115079100c02c48038041c0740d044039544211180c8030304040d8030841136030045008480b40740010304404034004000388052205500104698210241c015038034104076800c40e503100000d01840f440c3d40a8560b03a68450b0802c1c4040300c0c00c80340e2549540c403076580d90a0402060700014001900c80c0c034000c01c03903001803c034800f40c0200010302c1001540d449608040c1884482c0010f0b041041201d5400ca2034605541490320503203500c54410f00c0d010909100000d6030b03900345540192076040c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 652245773 1250 652244523 652244543
    0x1150c03030f09111206072a151a0301230c071e0302070803030708040b071101050c180f0a0506070609150e062415040e1003140304050603010e13 64
    0x10020341d4036104c03807240b00440c3d0440c00075880c04045500c074001a65450b0120f80750f5030001a0f082d00c25400c650761017009070724002826005441d1013008079448185441015640e0884040c0000c0348e03810b01012440540c002c10620211145509240c00450038550b524042d04001030080801d5508039480c065025020302d5200f50091941e40c20b0324000d030801c40240c01601000b090100300002501c0c41140148d407222407544842e10340102c1c00c240a4007200400c844580114010403090003407a0280982d00300e155074031103401070440e582c41d080d0b0810f18401c010000f12601156a18200d600580341c0450700d640e0364244034034104008103120385009000402c00e02488501144940c0003044170b1030000181c0b20341d40c0c1c903994405d4041151200c2401c0d00070040050369041d0503c035000802800ca0090007614054070741204219404040703480c04d2407045c5915040c410040d40c4101d8400b03844d1424021800c160030b100005140b404140200f09022100030700086010a100d101e050403103410418880d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 652247023 1250 652245773 652245791
    0x7060f0606020a03020f030a23072f0102070308070308090a0609060f0b06120a11070b1f05090903040b0f040b0a17131505060406031a0109060e01150c03030f 69
    0x107500c422807003c0c103a0240c000c1c52602c3c0d00514011003140c0000038541c0e0365036030503a207460354040c00b844400f1070a580e41c513080c0030f45000501d41c00c401402e0090340c070050802008080e81c00f1101d2100c0c00340560b045401003403080002404080641c0c075441e5050911100950700c141000d4a80060008050515410603690105101c0c1c1036000007500c0a0483c0288610b680c40c4051005900ca4040304400c845c11510024070942c2c0c1d20713401408650500d050f040e00d081415241c01000c600150740c4007001200fa2042e05003010810390302007004000680d107141c100d01d024818a42c0380d0183d4440d02c1d800c0480085c1050407260781c0011140a00708500010361a80c1803108020841d02c0384841a2164004600108000c034107225403440b51264050090301810b0441c00d043c4000d006d024005a400030380b01c800100c00118950301040b40301000a10a12030342d8945a604812341c0c1b841d0340010794120581d00103001c8010500b145204001280c103180c0310a840310302e81100101145c01c000f50020f4504182c04e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 652248273 1250 652247023 652247027
    0x1090b0f09010b06070308070806010509100f02070504060b0d0509010b01020604030c1e05010e010f110904023f0c0403030c0807051e0706030e03130528261506040207060f0606 77
    0xd034082d0143e49c1d141095517881030011b641c00c0c0b080941c0310b680b0210304500c1c0c3e030246d8401d0400c102920410700c1500c0b4031275550307808241590342d19045114184170100d4280700c0001c2505c96240d10072005002840305003180c00020b074903280050001b904114400c01120140b084030000c41c10b10f074600c40709951151102d0b0a0180c02410340701c2071013a4039400d0161020700060140500d04540c16429078892400c4a00001c200c002e41c00f03101031000110a800b64030310028402c03ca880040c860603503410301440e01d04d41441c3c8503038400404035170180406000038400309901503810001a0b074400d6190340ea070b00c151304055150095803101d010180340000381c0b038400e070940890148100d800d940c4007400500c2e100c20009481e4000c019030845000101841008a0329000c000b90251b0181c500d02d0410004061070500e2201c80703242c012064802c480031843c0140b202c00e0141d9500c0300b14120282c030210013440403000c20204040c0406200740e0f00410320606011007940080340b1440d85003010803550b0754600d80 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 652249523 1250 652248273 652248287
    0x9010e0d031407080912090f030a030206040c0609140409080d052505210714070f031407030e0118080601081c051234120e01090b0f09010b060703 64
    0x25442c0c001c03403001d001c103181e5400f0b1216a8040c1d0250009800050f00c1403040000e00e403c100d0145078044581d801c164640c3e04c0c1482040002d9000354054010b034903207800c19a209100341d9007c40d0030001791407420021809180222800a14100d0b4081540d1780c140c00c000079180100010100358528140c1481010014041c2031401307a0030079024055046212801030701e01c0c1c0202003140c14030180071500701c0520356249104035800a650700f440c114103000d20130340e000b054100100849851601c1c0005000380f6402c1003a00807070b006140041460121280e030020481d0384030108186c1440717501c0a103a21159102c03c007480c040c01a80d02195030b41d42c0c3d50020155185220444668000340b4040c1140380700b88118102c2c0d00c0c1f0401ea184201040d180c8940700c06405c0c6002005141c80c125045400504440c5041c4a0303401da10a0b81c2c03606e00b2a440500300e10111410101c0a08050380340161000005600d400d655074021402148200b02da40c1d40e251036805000d8260000e80d0202000414100301071300004 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 652250773 1250 652249523 652249541
    0x308070f06020318010e0d172502060f06060406020309010305180d03090b0a05040210120f060b070507051e01180f121202010c090b0705010b0324060a061709010e0d03 73
    0x100900c00034020b00b200391f440e000318024580c00141520103080c03900011a0045800c00000c80b5001114002100214400c3d0903241543e00160800c00c14814651000c80d44103400031400c40c2c01d00c0c9010315200004e9900d10510b00881e06058850000400350008069003107034003080c800585003242003d0300000c004041e100c804903041c0f1510310214074800020301c9410b214a5000d0309052007140120000d0f0381002024200402c0b85460707480e00540c000c424040d1100800170034070450740f01c029518000c5e04200b03241d00b0560294103120801d4ae4000031b40c50120505041c01e0918030040c096002c00203441d6101604180155406110001805d03500c2c4090307420742e82d004d0102440701010b5203c0403404d0b1640700ba640c10024107511400d1016014180060840d1841600002250622400403070b050101e0111500c030072038000e030301141e00310040030b0105601c51002c54a031020315040c99000f6041400d5440d401e4000402400010b25481c400d40c0a01d004200725021915110103e1b0001005400380c00 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 652252023 1250 652250773 652250821
    0x7080f030403030921021e0612090d0c080a050904060905090730060f0209090f0a0e0f1c09030b010b031005030a030f08090c060c0114090a05070308070f060203 70
    0x44c82c0021214000b80c980f104c000d0340c0207140141d16a064003004500d110a8194940075038441680c80071640c0c4820003010401070101030060302e881e08219813800c14030045510010b002d01d0700412000513180d0f1040b14020219414034641310b818440202d8020960f50b04070201580c501400c0c440c108000140702c200301c501008002442070340300e4240352503210b401c140a41103d0900c5c004040011080d41120b03500c8070b00c8c0000107041884007000100510015140e11041101040901500703103114010303a5580e2050301c0c0200f1412b03661100c510b42d40c0c3c00c5404c08120610358224109030661050300d60000071600070341500364558442d0b1981e01c0c5603109803103007141c045484800040505020407049490b0b40c16898486042c28050400d030740700705000b0130452050142d40c43d20b1481d692810090410782c1080b800000d03450f03403d0010504110400f0780641c80e20b6000c14611f50000d41c0001ea20000e899004c0015034071540030340313041701440e01c10540040c1894000720410440c00c912a4000050b02210 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 652253273 1250 652252023 652252037
    0x30906030414060c0423040b180a11040f17010912030c09140105031504060f06020c030706180b070c170c0307140d14030d1b030b01020c0904110307080f03040303 71
    0x500340244e0a48500e1055503c00000e0030500c0d017407207000031000c1c80140d00140c8081081a841400280444013403490342c1c240d02500024850509001d11030304036007480300c80580c6e140608020061b00d82c15054800c1402d2004000855020b1417001e40108045681c010401071187c100603102401605205603100000f4407103a6001a43d036a50b4415a000318006031507003495034036074506d41890781d810310b6116500242c4401c400a4183d000104c20401000e0f90703400703000c4960300141050b003400c5443c2c0c40007040110510070202003061007005002101c9001c60499501e600c2841d001d40071440c030f41c0c030644050840c20524844145c000c1078600c80c20104800ba0b4800540382c80c40c1c0030759a08126a140e40010b2040c42e0080069017001e002040c1d400064100e9041626058000050350b440c0c41c0000300500003c84108d5100b50103005005090f03400340050500ca01c00740011800c0140004e00103044059030381000c002e1510248002406040300c40183c0c2c9000d40d0040c1000d0342d90740a440103c00180c18 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 652254523 1250 652253273 652253281
    0x415030c140a0f06110f1629030105060a030f110901110d12090c0f0603020712020102070308040f020f2805030c030307080c07090501080a03110c10030c0203090603041406 75
    0x1100305002c050b1120a00807000440c14a40300315415031800d00090054480e95004c0c0701d500104014046051055100361170180341085500e10030102030540c82d2501c412071414800626110200303981c10b4800c2913898640340c27004d13a58128086c091400c0e07942082440e01c542d504401c0c401c10b005000c00c94082c3c0341c0003070001a0340100c656840a0440f20030000c0c4412840311002c5900c1e42104580744e00032048400f541c2d03207800b174440000c0010b601c843c011030350010b001c400700304041e01003424000341400218100000d5840107409540000c000814440e43d005454085640310020743c040381c0405402600405017264541074110070704c42a410013055820703800a0b15140000c2c18250002d0090003440c2001d10554641c0050703041841c0c44402801100da001c100c001311480340b00e00800183d0001e00c001000c03802d0181c17000d00130b6200d030142c60b000b10413034181a0721216402c0c0d160300200c1c503000907481d074014012410742c040c0b05026503115400106000a01001403071484207405008d00b65a090b40b5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 652255773 1250 652254523 652254529
    0xf040e0f180c030c0f011101050c030108011b1d04111602190503100f020c0a05160e24220617060906190209040207032304080a110415030c14 62
    0x801d140b03029819441411024143d05006000c0341c1d104206061920301407101a81d0a82074440445d0100c680c0f020110040003651002d00030340e020b107540c070704d07a48000080b4090002d003003580c051aa0843c504240540000c00d442c0c3d507009200011200e44a59207400c000f102903490010b4000c400c3c1d10070041d0000f48415400b011003c0002c131070006004102070072803d4143d40180121003041c0010030307400c3c80b5019010905101514205104001400350b200481c446400400c00d16008405910b030b08a007084409045002d516030343e5922102c1d0484044100e00002d507040c401c0401e40034604018944002000b0038542000c0d045d254084c950b6074401c4444100c40e540d070a42200c8021059100701d001c50181001c64122184e462190b10001d89810b0a07000800e0503a880780004400240c00304083e5040e200c0304140442c42c1c008680d4007035207814601151255900c03000c00000d00810104150310300c01e55251f500c22911070400388100c40c48166070742405070358911a07100c0c800c042800250003503c42d00e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 652257023 1250 652255773 652255783
    0xb0310122a0605160f050109150507080c041202240409140705030c2512030f091511070209040f1e0203060109180f05030d06050607020906060f040e0f18 67
    0xa44550750f01824107003203084580c05402d08500950b03e030502110315030003150080c05043c18260041c0400c03400150280180c50803103c00070844070070008004213016034080503208a404940c1e90f03e9403400404a940006845084101d002050044851601c0400f08004002070801c546111030b00300034683e11095254008602110440002142000000e03644190320026041100c1482e100002d007210807088022004406182600d2455200030f0040c00142c0c58002c250204080b000280301031940c543e01c104e0684105010300810175180d0a4801001c002d05040c0d480c07468008140310581c2c14a0b080008950804240c143e42da444100000b1500320441151020101e40c06401000705a10300103041d001415281409030400030a1070000000c1003040ca208012039001b50081c55689070390726049001c41e4840d038402c6008880600824000d40c0d50540c400380c1c0480140c3d2059540c0e010884001720764403890700494520001a414444d01c150548906c2c0e120798610010b8105a1101c243c40c1e954030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 652258273 1250 652257023 652257029
    0x2090f1f06090f0e1e04050f061510110607050c030f0310030611130b090d0f060b090603071d15030d02061905040203033f1b130b0310122a 61
    0x480c0700e00c040d084d80003c1280c545d64001d0141068883ea000c07200140c9041071800e481e400400c1071400c101200b145011002e51301d841c9114240f480c5040000c00f030300c40d2580070080510040c0a0086003468422005004071101a40751003000b690703a00e0004c0300c1c4200201c03e0700040c3c0b583c130b10303008240d0139003520501103c04a5202c0e00c44207088074900740f404031080c0d02c01c85949801204d01c41040002840008941c09078501c1100040b84900340c61090040c00e0f03100900e0184698442f0b04100b00342584103031440c0e4410b0380c101c956003950780e90b100484110f1181c00c0840b0382500c100c00151007866800f090741c074010841d40320801c1d440c58138000e510701a1f40c01030b01c0c080c2d4190400c22010201560004a00d042d0614a1140f80c0c200e03611130112041c04811803000e07840f0380416400704a40f0000c10031314865501d5065000380e040030104000841044501d02a40c031000400001007000030101c1e81c2064020300380700d044080000442e15040c42d400640d620141c0101c00080304000d5a84c07020f8031000d040d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 652259523 1250 652258273 652258291
    0x1f060807061d180109020d0b040c1d030a021002030706060801090804120f0b0a1512080a08130204051e15101d120a02090f0402090f1f06090f0e 63
    0x180d0810b912084031104600307400700358030005841c600b07000030340c003008114001d00540000588481120781ca1406441c0b1618981d44a9450100402071a940000c00101100040141a0101c0190201280c50401c1e09000a94032484251121a00740d070300100418040f4800da01c10b2141c281e4942c80a0b00740c80c600b12005141d0f1400b40400d00000b6555040d10745d00070700680124500c411141c451b902d103900e050310703421b18132600c800c060340b48801e004207884014001d642540c039940d0016213030380c0024002c0e01910130030040382c00027103030a941106121196450f0000e00070411802c1195083c40c014488008040b1110803120004400010000088040c410040d0200c070569550040c00c59429011440960150b0b200d10515000b40e101e0400c01c070201034400c001402116050b0042010121f402480c0030f0342c6d5401c080800006845800074117410500c1d8521010b116215642014038488500704503940c80303c18080001091980700b50030804640000d01030741d64183e180e03035544c1c0d000c8604494800c5 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 652260773 1250 652259523 652259537
    0x2d0a0f1412011d030901091d010e04022205010518060a090b0105040b13050312040b04030f020f030118031101020a140703051c05100b0c06271f06080706 67
    0x103240c141440e0322120060103900008480c184180c01100001c03502a001100d80d2020540e51441d58210b4801d50160140a90301024280540c80c02c01c0721080c1401400f1550014201040454481042ca03281c15034401c0035074402c20640d020880000c000c248541840b9551110000c40d50062000b4600c2c0154005081001c001c0d040541c404040d01d0740307564050401200300000100d104140c0007402d45100c0688a40309880c0c5030208143c500303442c1c1800303009502d60810081043c01d00a1041702c045070b07804030104120141900018126000700c004054041d401d040985545428510b604e40f000c0d0320030748407040388000b1a2142130803030013580054800f0402000e980711803e0442d01c080c007210340c400d1500a1a02d028960f01500651480b064a84140c2d142c0c010320440e21401c3d40d8240281c1502d00080d0b04100b00800038594410024000c00120f0303032800d0750041414080f801c041591034510040303641484201501100c6003894010004201e0f10780034000c00c4000000c1110011070710140e0707481e4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 652262023 1250 652260773 652260809
    0x21060f0d0f0609051603081b0303071709010605060403060e0106080f0c042004060f0318030903020d061104150e060304030215070903060f0614010e010206152d0a0f 72
    0x900a00070400242d4003485110381780000492a801d0950266100d000c0321f58a900c0490800443c245845405601c40d41051041019641e8000d0f10342c03c07c00e4410040d00115140e01184d02e005046c1500440d8004100007004420b00025422108040340d0b01d4000700b190580d10412281c980d0001c80308524550000c1c04c51544a1034940c0001520115110f15000d030752600424002055005902c0000402c0010349401c06654061248010a820f11000b6141420480d90010078896207404006d03c9181482058400e0020707030361000c00c9814000002035a20354650b5500b480000e4244688000110840c40c144120b080071010b50b40201d5260b001425440d106401c8040321410080000d810000c0208002001c01c940d4020001c1c0210128000500d5500b8518184904140158881c1c18070015204807503090340e0020705a680005400700611101c5e00800c000388070301e1130844030289009028050348240140010a134030403500111101007a045e500c2603c0e81c0b4141c950300c5002c0c1074082945801e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 652263273 1250 652262023 652262033
    0x80a1209082b0e2b08040303020f1309061505070c05060f0c06130b06010201021201270f020d050f10050d030c050607120e01111c0221060f0d0f 63
    0x4110a1024881d4008440e02c403000c03004803042a4008500399001c03016411202c40c2ca00c080c80703034682210b1030aa07100b039050100608402c40141c801001c02d90b000a119801084a8040e1608500c21b16194080143d5030819030b0054002c0b40515100d0903020a190034845025a0868840c958080c08040a00c1e26060400040d9004104404610401001051000002401070138450441c0209503c0056040d040407081e40310000c1910303066a104020901c0a4187c0b0180c00e8116a8144010044c0102110200be010b40070750100b124000d05103c0b410240e10843d8002e010b00742000c41080080e5502c110700044400419580c1c0c1c80e2254080e00c040c055410b112184100b224040e05003114448000d6603028500401180c1c40310004c5c07001040b060500c2180e000c1e003080b01c00e018000b402200442040d590a60bc91815a20801d80d004003401b043c102003a010b44100b40010300b502ca44440900b400e0300c41315401207404501c101d80300c0c001c44881e450215458010203421070140092005540c1d16 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 652264523 1250 652263273 652263307
    0x6090f0c0d060917040b13092309210910021204060503060a0e04060915020c0706051c1104060f18050108100b0a02030a020708070311090406060b07080a120908 70
    0x1510050000341344941c08404210062000b007400140d1765a441c804060b40e8508401c5035000408001d05040300e8407004000081901912200030007001000c0e110542c00b1031400300c80c0004013007150841d001001124502c400a0001601e064038118502c958a05e400c90701e5003211005140401c2d001d20042c0501842036014650201018000e009820b4544200340301c2d11104541c01c98600751504925420040020880d005440d50603c0550804106180040d12040140100f5080010124540d403e010101c45800c5201c03007a12010481054484028082c980c02401500c000c43e0001846010309481101c807500c040c84500751001805042000440b0342940151030350400b081c9052010440030755440c02040140340079002983c1d65030f08800b0181c24a4006d9001c1a070a401c40d10040001c81d0b13103085050400350302110401c2c1140e031280340020080100350441e00000760085444810000c041006004007c074680b0b4804143c462a504013060700e02c09100200b83c0003040c40602c1c4a03c503802a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 652265773 1250 652264523 652264541
    0xa1701080604141216060c0809070510030f050106080609070503100e040510050705130503060103020a030215070c15120b0d030e010c1509020f0108040b070e1c0506090f0c0d06 77
    0x40da801c004407004150f80d00d030052045034162011a505c0803040103c03a208050070301409003090350180c070302560b04580f161481e1003518040c1c64a40c03140d0292910980c0002064680c600d0100b055507140c0200a01104080714964011400b8101064589015005581c410900f80781600043c9040080503114004050400c8800c0d00c0362541012014040c0e0186910031952603031082d44504c4107001c059440052948954001d4216500500260712002c98078000d481d015600701000c000e404100b112144141d640140c0b410803404c10105030720480d5a80e03022100d140780d45050513003d90000b0041181c0c45a0400d542c003000d42500c10300041e000d1012500000014102101442c83c940c8454000c0e00340403220781c0c0465900c402550840c5051004400805000c2c40c102207145400c1d520004070035406403c00c1c060040507480207059a4810746410702d079a409815802c03102d803080c40c1280e503c41d0161451040ca0081c0c94802c4042080003841015164004042892410141d1618001001141 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 652267023 1250 652265773 652265813
    0x610140d050a030e031c27270b0a0501080610140d021e030c04090905010b0a080a03080f1306050a020c0618010506030604021806040f0e01020a1701080604 68
    0x5441100415010b00805184501075210711940c07189602c10103007410407103580108511100800fa07143c0a40c09400c00009481c0e01e0600907441203c0200540c910074030341c2c407810000080c21105400f0280300c012840c03500040d100188000d1040318200560f8075031a000b200d00051a440010380a41350080c0d141080c03c40c1ba083c00b1518890010307003854103038042050141440d8000540c004408003d00841030b0000c000390100e819820400c1581c1c0980c8694486c04c40e1050700c03042b0500900c4400e500502044074000c201c0741071075a0392051240c80b00c010380780c01d4003c01c400b900012011084450281e07c2181c981c0241c4000c903915a5508009000c0900003140c0d00d54240001001400200308541c0542c118190400712055004104c034251100144418020740083e002d000040e120001200c090b090031241c803101c01e54940300030500a00110391142000f82c140204c9070f40d000c10640c0144910403036955900f5090440a00d0301001071003e108210160b403200c000900403c840a801d001c01280c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 652268273 1250 652267023 652267039
    0x1409061807031d01140f09030d021314030705030c0103020a03060807120b0106030c02100c050c0106090e12090d02190e010e1014010905060a030b0901030f0b09061014 73
    0x1404100c0c03545800c80e52040401d03502e62191a01c40d42001c104401044010000d00c9a1500c1500550601a02406000e040f88125000ca084440c0134800c4d24645081003030b086480303100203158155940058403d040070445020021038403410042080c00a03503101800820720b070f050b907400450081d804022550200b5544500c00b04070981e042c07000d10001c1841540503da52000d40c14058940c100603170068080c945060100c110f10758006c590045013111842c40007605011400007030b55a44a1000655142d5107460701c0030810014580c030a10188844004489005000c4025084a441486091a84265401c40c2100145131003980c2e4604d11103000300410110303039a1000b001e0541c000380c10100a440c40b2808010080d500c80210b0801007058a480d901c480910707800182c000d4160303001c2c0a014801c00120070868500030b03042000c0000001d4500e12441da5203040c417040402a140c800c0b203291401101089a1440010f0140e000f2814210003041c140c1c6802e000c0d10b6441e003042c40b030f650040d0030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 652269523 1250 652268273 652268299
    0x5040606051e0f120103060b04111201030f0f0b0a0507020d020c0112090203030c03030f1f12121b11040b220b040f09050d0201051b0714010207050a05030a020105060109140906 77
    0x1301c0c42e501d0095204000c0810100040010402600c032407468a0315242c0c001d00040c0554004000c1c1c0a0440c0e80101e0400b80006280c140300303cad040304081000d4032004c0d01c0028020032002d154441c62156005600f620204101008201e0301d401602944500140140b588841000c10390343c8000081813004003101e00d4010b034650124119001111411641401130302000b100001103040c0c107004007850507103505081d0801e03100702c8840307000e604080d00e03440000f141c0500303190195180d4480b04a6019040c6000e0585160100fa07100c20149034501a42c1824644819418030014140e1340d905041056004007400e00c48003c01000203e030845d900586850b600440c56609106030541c0c140600b0203001d07551010348001c0c0c29107802a00c40c02100100d91505490301c002c0b0700650304007940c005540701130140f00c101d565029000303040000d0700e9400307011994020000000024102c2034003c2c1c00920855803164010f4424203054410039120702c070428840c040340e02d0014021a44403500504035412108 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 652270773 1250 652269523 652269547
    0x1314040f06060c0b060a030804180b041e0f020c06011a160c08150402060d020a09080f010c0801060903030203090f030a0b0a150b07050c21010e060105040606051e0f 72
    0x3090340c000301c00700b1612443c10742032280f5403180710b0740902d080d2030f802201d5103181c1d6501c07113030b12440c4a11238900107040e82e12298000701c0c1d00499007002e4010000c0c04003082441300d483c50b008442004501d554074110200d8064003480c02070310342400e82c040142030300ba8a460014041350702070004030211481c08100025a1858401c2e22a038070030702036911002c115040c01407071490001c0501d2401c9020580000b007100580d110780444040c0600414050307200e0b0141c82c415600c1100310f0700134160394000c0ca803161083c180c055000303404006080d0390b4141d441c0d9950100341c0d2110f51600015005800c200509107541c20000c0c081c85550398041d04480c4104c40b59100c040f00e004041d02e00502d5035440c0e0100003001030382e80503120094410410103e1802980f1b1b5038241c0d4401e090034401c3e0080d1841c0701c2e4118130802c2d00700d0035451005110001c1c042c01c41c201e03424a450380d00034000c20344607d03e05074010811501c60b8003501d90043c0f031030058056017096410355000300d4006403038095203100200214a4140 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 652272023 1250 652270773 652270781
    0xe060310020c100f150303181701090317040807080f092806140d05271c1715030f0d0c02040c0e100305090307060504050d141314040f 59
    0x34081d031000d030040e08001a0700d8002d5406021128010300d0501c1641400680c0c0801c100084a50500300b40189000c0c40c0023140c16400d465008441031442c0c4802c66034034950640060030a640310f40e4620079105a9880c60303940c0100c090360b01a00307441c400c1c0480c0d03001079010780c02800d40c141e00004071400c00008500182c030a800702d03150702d0149040410903a040c6810b0400f094003500050429941c500b041030041012806018112844252600c1c0032802c1c0341c920482caa0764000c11040108107030030100400c2a13440884c00310059002c0340304106242554450b00d8455502001520032038115100c0c2002103207009103440500350b05004421251101040821214100b8085a1540d01c92042140100800c03030344015050401d11400c10040e0709140c0e1586d840840c801c403c3e0400040070388480007118514064030800402d40d0346024184010701c0300014460443c07002c240d03554a50f6084d841030141041c091520f4803410140032200500c0001921204042203d00103040020300e000c900c42e00e9410b40e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 652273273 1250 652272023 652272037
    0x20405040f05011a22020c03031305070e010b120601090803030702070602070b03280216080403050d020a1e0821010501180305060a09110d030503090c040b0a0e06031002 74
    0x1400c074034020080040c02c3c042d0001c1d8a4104100703c01d05540c200c081050f07010070b0f241203c00c0f582c501d459039030243d515038161a4a00c1d07005045a0700c924105500c0b5408404007103094078284220701c40095803801c00f24209041c4c44400900c1400e061514000c51003e0300003038501c9052140c124408246104104080c52151001c0d6004220480c58000003904006040d0418881080100100728a0413484006000041b00c01d048841c102e03007007601c00c100240240e003801c10040245e50071242c1404861005002500d011314103992500c907a48074166502d900f5240001c20203440e9420308403004540c0ca802d1262980200901c5141c14106003142c484594403180c039140d0502414014041940c2c030191038514000d516034180b00207411911240c0e59503d00514080c01c41d51a0043c40c8100070304008030b61003004000d48400e599160920780500181c004844903040c5120b071a01e092000d1170240289825100301812030b140701414030a0400b0b03d01c030010400c0390103101e08140362190900b1440200a6 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 652274523 1250 652273273 652273283
    0x110409030527060901052b1d06060d021509041404051606050f03221a1b19110303010806100504020a021c0201060506040608040b060a150c08040302040504 68
    0x7444403142d00103900d100d409105840407a8660b000d10010340c5800c011665410400d09040ea1202e1400740304025502d1401c4500c00100001170440d007a003005500b01a0700396076500911449080425030003959054120364095001e0148003c40c4054104945541c110207101d07001c82d86404004004601542e5281e40348080d280c50000801c01404404d0040c0d15a403429000740340007492903c2d10040c40d600036200c801008000c00801f040c0c10808181c05030f041d601007209038080c4000241040d042014803240c1030005400d10700d000802c0303e0401c03544003801d8000b410030300d810520250600b00c3d26030f8107580d800007803050098207504440c5d410800f8500a084000040010f403800c40011084d4903226440b481c000c50051000000c10340d00415000f2030904524a0100c1e50000c08030200d0250501e41e20683c1c00c8940041c010130182d40c0421280e2289009600c0d03461103071550001d2101350b035058420481c5012404869041d01440f0756a800c50050007644614182500d94001804942c0c055038100e403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 652275773 1250 652274523 652274527
    0x15131a0607080d050c0a050307050904060f09020712030e15190501030b01060e1009090513021005090102010501211502120703090b062409210a051902030c0d1104090305 74
    0x440c3c402d8500445030701102c0000d01e41d04018910f6005042404054289001c0c028046210102a02c5a81c80403008003410880001d03c0b5640e03a09400095200200c10303100380c03408681400c411070090040c54000c0004c1401810304900c0e0300344810071114081d02c00d004044100c1c8910385800c50a016083c06940500c8907603800d945800000b07000301040d0800c29009a203000c2d15680c0040d00148038100312209001d01156030f80d00c0c0d2451011416044078002c0d4803403070038086454001c1d805400340040c0b60342a002008542d880c6c5529240d00006000400041c1030900c42c4040040c080d0341c444801c920030301d200981480401e50030740510407803c80d212030019613a00284402e02084000b00d98209009492032142600320454101040326051600d030022400024203100d0394a546050301e000c42e004060300d88074000c41010440d20703900c02410a0740d1900c1003c3c003180d02222a0106c800c2c07100d0b0f00070000c0200c149001c0600403440303100d510a480c00c01603840740c40007075100c40c01740c0b148e00c0e0b209a88040d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 652277023 1250 652275773 652275787
    0x1803110105071b062105070905040c12050c220b030106140d02190e1c08250c050f06030f01050906040b10080a0f02040501020703110a050a14030615131a060708 70
    0x400500e0003001001d1742d904000c11710010b20b8125600100750385040da0b0200c0c0c916075004065542c410a120715002580ca40303010802d0051103a030103000b0800418625803029403080c2055140c80505000345880c44078200f004100c43c9024808042c000c162403d10b09007040c00030f1002c00c0883c1c0003460604520311010449a5080d0351240308040403000c1124041420302000d8101f00d200c890310f010003000c1207400180f51900b810515080400031080c8191a220a805440e00341c03040d40301842002c2c06078225200100c10341c41d01a059034400e41350b002d590f04c000d0b0300e4181000032003200600710030f030841c0d965048200b00781c603107006001380e4000303645441c2c5450600000c3d10085401c00c0307525648081c410300003805680c0e03000c9141070850360028040c552900090340003c88420343c981c02a0391000c98403e0000e4078100b0400740b400da8090440a940d41603440e060784114061405450503031256000c0000b10002c006035000d501140c5110411b10402000040810b81c40e500840096030f980202040703035 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 652278273 1250 652277023 652277057
    0xe071d010302160303050603030d2c01090302030307080402210303070e10020c0607060b09101a0a200a05061008160e071b0206030c0a1803110105071b06 67
    0x15a01810286421454090719034072038040400210001001c041d100d101150180d03608000b582d030610340ba10750801c0501002c0c41c015444103820306040318260340722032241c0440c1b101071142d183c00e0f82c1c01d03801940c40d507541d1000440d4501c01c0200100c2e803020103414422052600c0d4a45c1c0c02401c91fa0000444d528242100068a220aa901418401c1800e040f188050b1580070a90090420050b02c4083d10380d400d503e080350151080040d0745400644420811082441c0e41c044581292500c04842503907082c0501d4084003442003068403008102c4551600c00c0400c0f55001d50070200b1b240d50182c60320f03540341d942c0c5c1c2420501d0641d001030b40301c04c03101c0003881a00c0c014800c040c06516124000201107250500d4a4031445000f4840c0c3c00744034090240841094041c5068181698010a682c0c1d4074948220105810303006400304400040201c0500403000e4000c010540540c1d400425130304140e4104001100d1941c031a290458810401440d1203202c0c5841c0ca0646e40500410f880b42901903040f4910 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 652279523 1250 652278273 652278317
    0xd0503090105100807090b030a080c160f0b0406080a090203012a02150f040311060a0218060a0206010306051e041202060705120109111c0b0a09061d0403090e07 70
    0x35041c402000f0108101440c00050010f040f80c441060100d410288200043d0411100d020040c003544000150500424804582c41c400c40d034000e00340d03901c1c450703c50403180304078841400b0380c6035418803c06c400d005040c00348070401d6000e8010071011620b200554046401c1d03854008092919000800180b0340280075200d21180000e011700c02403100787c0c0e000c0c010380607070035000d440c0408004180011500307041c8566100244040c4020849040b420f242080030001d52100848a04148420746085510301c4e08004179040c038a150346c02894180d0950704c1d8100148800707007200017100b182100b443d40d140c0582128a110364015a4903006c1c1703040128000e424400700801031000c00c101000343c84c04e1711492146240c1950003086000801ca0121580d00059204841010450361750100340491000c860f03822054103035100303452040d44a542c43c149c501c140c030028043c00180160648503030102c0940007081c40d501c0790291074003642c0241c0d140c410900140051324404005104a580b0741c030761070b80c3c4100d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 652280773 1250 652279523 652279531
    0x3302161505011415070f05070305031306030f0605030a06111603020601051207030203151b04140a05030f0d08060d0c0303080403090518270607050711030115030206030a0e0d0503090105 81
    0x2007143c080094403290880710b05c5103680040a0340c540d14503020500000b00b003040043e55020080b0780c0d503541c2212114150b910184605800a070412410b1381d0500c1107805080704403100038009201002a40d0f46460180000441207002900148403090100c80c000c51118500c0e8081d401409040d410281809240102280700c00c205912450042006890005120150f108003844071203031a198224070400300c4404001611800c0f00104010030302030034141914802c4017046880710440ea40c1e5000345622940c26080b2601207400100058a0180c00f1300d11701d03584000018520151880160b682c241d814049400c15000250880104002c26070007111900c00f529084800c0c8c00143d0303440111423b2008001d06040031952050900d41004800e1107803c82204224001e466107843c0c2131400078000e4100d1141a0344126465074003600d0fa04041c4910110301c5a03d50366812003a0858080c0500c580c0040d088030350480c0e030b9404205ca20041407044200107580743e40c416542e03050074a116400e4480180c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 652282023 1250 652280773 652280779
    0xf07050c0a0302180403031b080f060a0b0313050109020301060b0310090612020f0d05150a200f0a110102070c09060b09090a0c140c0a33021615050114 66
    0x301d0306001503502c1000c0b405020280c400300009035a520324044005e40b41d4001514040380c2c08845407042c0e1500b2050040c450a280c5002004030b907908400c00911010354401c604007a0400c01c041180b0b0000e0194410036180120000300700b0451550100f800c50b201640680310b2000080244900c07031844c0100e42e0002e101a1005200d9141404c03403080d0b141c042d40200900c07420300d000006060b80c603000180401075420405071260b10006030100722125000f140c04208040c90a594209659028044511110822070505003800140826903503968800500c8030305002200d603600d904010240010060703180729a2200c0700203841c006260066440e03c2e0064100e0000070700401070140c0b140340181c3e90110a1004c0403400031a460000d4850b940c09088105002d20f0003e1800303940740002501c41e04091040811540312000f142d2103c81d01c10842c907030f02d103074051041110203002400340c0203040007400b2404182c0700346a4603507809030b000421070811440d06840d00010403d2064503d0708808072a01a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 652283273 1250 652282023 652282039
    0x94a09030403050c010c1e1101020c030706141b070b04081504020618060f21090601080604140309090a09061103070912050304150804050606010509100516080f07050c 73
    0x560f02c2035120709414a025040159420645051001401042e000c42c14907019040c504c1c070b81c2e0b090030070100784000490b170701500c00e00034100d0603401c0000d410320407a0000c0e650080880d108009110040e805260344207840c030211080c1441882080c0700c204014a401b10070180d580346000b00c00c5081c5072107510501e0391100d00d04204000b60f1145012071361444074040200a40c1040d80000500c01c0c01103150440051401240b160a15851481c42e241281181071504040e0741c0c41d44903031643d030107090062010680248010400041501d0341c0142c6907000b040c00d0b03e040c0103d490104840710000c550200001b6220500001841094841c9010000d0440000c170714614090f14081c0074200e46115514074000e1582c0d6003028058207000b40d40103000007a910b07070091071040c18000c00d106401d90b0240d805016100101e403007980100119103c0c1200a400d4030344100701144180d42c150403504c2c050280c62990300b50100000c03480c00046c070315103000500d040c5c1c403120982081450202070340691030041f004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 652284523 1250 652283273 652283279
    0x301170601080615040207060f0e10140421020a02150304030305090f0304060c050a0204140603060112050d0e03010b0a06180602012007033509030307094a090304 71
    0x107150305944014600f0b50300035948005910b8961300070089d062034510758a103042e0040c5da00c228046119860740d0101d000502c00750045082c554449281554014076009100c88800804025044904c02010160041e01e650540039004202003041c1c1c035401c69100000001080308054140c07092941003803a03a0f000b480040b030200d44c89a5640700354028141800f21010100040103002c008c544070895003c2c009000620010306040200301c01a1002d031f11070f018032800410601400740f00c850f85590040700411035400384100568800c400c00850765059500c0320403404443d100c0c2600400141125600e00202c03a008620103041110590001400c690510828041000c55028806044810981c10603a10300c4a45010749111454032243e011403041280c0d1241114420403491b002c030000078685d6031444d968100c0c4540c82c1c2c8011076407503000c18640602444a03110003030780080500c80703140490000d032000c0008508428100104410508501c030301c42d120030541020155000791503000154103040c1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 652285773 1250 652284523 652284541
    0x20f0604020603060415140f19061b230c040b010503061207050a09020d140408030f101706100509010b0d0c120e0d090506041a160803011706010806 65
    0x100180010740300b0070020000c00d0b456a01c80c3d00c012004d000d002c1c29260050307650284031854004260a86100b400381001801050501e0100d4002e080601911400c6a0342070003070030788441c0c0d62030100841c1c101c100c1450382c2c00188410060081e030f501e82c00032100015211090b681c5043d1080300701601a505040c41e4103020390300082a290000d030200c41400402c061050003900c5c2000952203076030320015001c00055000a1a0b000b0f0059200d42c00c41844040000400d001680300c6c10396000784903034403c0001446c0b564a51101076003010494016612460351402400d0000c4500140c03440150000c130301b0700c070740304100c1c2141c10000d1074251540340880d0b24007d0070b161107015000a05884c6a180c924180d24a40305071410740780002c000034200b1001442c0051039a4554680140300040303880181e010685160085c02d4074200e81c074074008103982c85401408110180c1040c00156074012580740c0d60400034160001075800f800461314407114008049002510306801a401108590400d40c1030100c244 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 652287023 1250 652285773 652285783
    0x1b04030c083405130f0501060816050307050703050c01061e090615020c091e01034b051f0e120f030114130609020d0b1e010e1302070807060507020f 65
    0x30f02c0c101d4a0b0f1404642640194018001c66003000440038640320000c81c945800c800c03031a0041340300b4035404207030320b002003401d55103484183c1d90344000c038506000040000b0f200700e000f000306005e200c0000c01c5055598203402d0045203400756000b86020030340070503c680007982c03040c41d0062040c0344003041034a540c101c0181d11001380208950084011400244d00704200d040d000d6405446419049a41e680d00e0400c071101e04100680c8048045d40340000071b0401030301c106d548030610701041c08003003103428440380c0a40024004c00100c0d154000d86042c001050031090700c556000c20110004110143d107030a00340e0a100e1700b441c902101c400280700400401c8420380c242c9040d81d030701e040781d81d502860b0f142c0003810051400d03000044046c20f1980200c0e202a0903000f80c10148142c2206125604e5820200801c2c18883d00021040200100001c0100d40c0f0450001d664040041d20320b075a00d0f980c1c1700600040c4c0c0d100320410343e0058400260001003085a214050380400c1c4c1e071016050500035034071455110 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 652288273 1250 652287023 652287029
    0x117060d050a0f0f0605070c151a030105010b041415030109020d1b200f1c0504080d0c020141090d0f1203060e1b04030c0834 55
    0x5910302400300380800104020504429400052407500f02c14686030403285480241800c0362039504010100704210b00a1070315002c00d0703501c00c2070030f0020107100074404010920101d05803410280354003c0c0c60303540c800307200e817501812480b280c05503034a040010000c640801c14131a1801166003208548501038500c0030f90b810348100c03103c05a0384452580720000940702c1081045400c1601100c8101016040b40d600c24842c0104954480300a21004020384c607880342030107441d000c1e08405c401d0b0004003081c254840554510341041d500702a04c8141c0e0500d081100c82d0960040b0344402c02d0031041d0341c0c00a440f007508100c100300d0409064454600082c6480e14580b0729401007607010a9081038207080c4003601c151401c058011110808c440c207000d00f021942c8401075840c00740c0501e401d00b01a100703001d0b50301030741c0d070000c0111915141c503c651020b0001e010707409030610005110210010f140d0024100080c003441001b45444030f425130021a0150200783c0f100725849440c45254205428040740f1812 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 652289523 1250 652288273 652288279
    0x120708010b040311040f05241e01120e07080601080f0c0a030b070c0b190b06030601092102040f0f0c0f0806010509010309050105280603020901050f06190801080c011706 74
    0x3130800c1180225000c2c0509400d4400380e18200300400000d044004540c50076405240300f00440c10a1200074440281d0340c0c4a00c1c1c0c0c094103c007220002c0c140d401a9603210044206020001e114045c601c881e17400e0055a400c01500d40e0000801009401c40030481c50010040060140a417450f4140c0041c5512003140f00041c40106030700c001a01c4140a000b039000400d0704502403100c9403505c884400808204800e4800c860392510180c0390843c10807005032072103004180c449562441c00d04080800000d4085e207059200c0e08000f0114005071294004c14a486a800001003001104c02c40101c0c01c0c0c030342105c40c3d80c040041b0301c4420346a490340421381f070390030540a090290741c480852004038050644000054615800e000c14400c03a403441007028024500c007a1340d904050754550b2000803d0b12074521010b54440006401408245829507903020f1643c1e0080a1074a081c0c0404074400c5410b100c0d00084010039030328001000f4901c801d10032450f401d102464214000c4c2040e4070322008008026000700c3c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 652290773 1250 652289523 652289543
    0x9180b04051911010201060b090901050d0816030305041e0f080a030204051207150c0506010b0306130e0105010303090f23011b05010b13020f0909040203160605120708010b0403 77
    0x1040c000144504070b28020b4640481210040500300001040701c5241140d00541c0703080700015500c8103000075074025240c001e144000c181d283c481082102100c0ba0ba040e1007952040200780c82002c00d10600321201c51280e20003080b02d00d4141000303c0b080c24079162010a107418040301d030002800901607084210390000089464070600c1c00124024040c0307411027500022482280d8070300c103000240700c0d42200e0190b010041c4507910080c0880b03280c20741010052040c3d00080050100e61603c2c4040c40d480200038040d0700024012001c94010384110140010079039554000500605602c840c2d01000307000110b0035500280d2415040d03580600088040e94003440f0040000301803a80b00e02050842e102c00352142c900454241c0c03e281c0c7c020594800382d035100d100b5400500001e20120700954003081c41440003142881151000c0c403c1c1520010070403a4140525100120080c840040c0c4d40c019200c04d54500c0c0d1541807144104515203c00b414490612125000422a494020046906590b44111048 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 652292023 1250 652290773 652290781
    0x6060a08040f110a0906170a030f0309080906121e0910110906040f06081b0d0b010306030206030a020a0318020f190e07080a0c0903020f01030b031f020702010909180b 73
    0x14070030003d005030316a8010007042000800000e150805026a40e0924440d180d02c0e4401c0b40103030750355409400080104440c400140a034030700a074042240280075400c0945480c050300005a1107030300c116083c0f000ba581000c1440041d0310b40c03400314088240c64030011402030a01403c61913440720700c1140880c08a8480e1241c071903900161090340c1c450320010b401207444070340300c61104151420300e00400c000a5034040025045489080d401420f258880402c58505000c0111100107840c040038040e06054445000100685520000718490480000c005881e6950f240d8000c00740c1e0494011040302c8020000d0800c0507035295110040f4100c022149510b60828105004c4c0e1382100941c40164118001010051001d803c410400c2c0b00740c4144000b0042c1444003c015100840140406500202e8481440c80103501a61140b8a106001000c440411620f44520800566044240142950003042c1c4004558010502802801c004c00c0f00380807160b80707d004001669600e060181490b0451004a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 652293273 1250 652292023 652292033
    0x2e12140d08070926120a0807080601142505060a0b01180e19090b0601080112050c0415030b01030507050405060d171821060a0204051c0302070e0114030606060a08040f 73
    0x72a549200c03015031756150003003400c482c2c4582240700040b0100e00100c0000b10850b03c40d040a07480f80304161900000204032480e0380186401c9405441e140174030260801c0c8500d0b070200c060211046c4600000c0c12a0b1810015a4040e50020071a05060241e0249010407909074000501c0580301d4602080c00c0035603400e0303240320100b40d40000f0f2154162504d60018240204040c006100c3c0e4021303250550141d9913540002520b100010300540742c0d030825081d1040501d0250440c85007105409140e610b403035100c0d00c9003140d1a1080e8012104c030351001c48204081d0426010740c59000a003102c2c00c10701032646845d0214401d142d02441182c6840c0002c01d01981002c02d90303400c03950840906084641035814690040144101c0c2e550380b040c0c0308a2000540300f040c0d42c0211070a4031700c06002c011900000e80c60342520450389030011003c0d4010303480c0104419060342d140074024168014041c000017544024581840009086540a4042048084603054010280e1a0410f80c0500055074554140c144 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 652294523 1250 652293273 652293329
    0x5090a050d020d081303021e010807111f0b03010e010908030f0c0706050a0902010e03010e0d0806060d290612131403040b0c0f01052e12140d080709 65
    0xc001400201e01d48003da1020f00c0f041040d1b82c425186080740d080d61090078480d00c0c16200b00640061103400014103041c0c8a4014400009402003c03159200d007120001d1346c1c28046101e104503800d65889883c0c3c8540f40901500f49182d0003200200450480c82d1220321091000900b0101d5500c243c0000c150308104c014201c82c00c0c241c0042040100b0b0908c032025201501003900c041e40007d0f19030500e02c03818541072190380c400c480031310020310000109031025540440018020f0b98400008c5c00400c0108a803802021080c64030341485015080601c85003a9121402c12841707806401d0920a07810a05d00b451161500f25a01d0f101130202e0710301616000009210505003001540002b050010300c96842102801342415444255134004100d8001c42d4201c0e60b08881e0095903c1c207480c0c6052441d4040b811940040f241d583c2401c86150b1034113251050b103401200112155a00050000c44520043c01400e8242181d881c14460038140a58000e00c1c07040d041c0214042c1103007699002c2445044644 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 652295773 1250 652294523 652294549
    0xf060c031d100804051b090a090f0206071b061d090406020d06032f03030d02030c040f0308130b16030e0414010b1209070b030708040c12050a03030c05090a050d02 71
    0xc10b034076404901c00c000a050a90950781201c140c803580303102448040039201503801010000d885d548840c0d584d10803440181411100070f0301d00c18080d4040c0300143e240c4d0700040010342c0c05a100c0b20a070b54604161031190129950040e020001900e801030a5a900450404952001242c24540503112800c042c80240700c3c015004852504c0c11000108010080010342c42140f40c0141c94034084003140203003020303d900104400d40c150810407051002d030000d87e000c1c60300101c03180c0205040c191142c3c0d0140c2c0391803494200703070b42c5c0304c10110302d250a8a4442c02c0a102a012a0308020308201c000751142070400340b000c0c0d000b0103001c2c207482d0302c006c1c43d100d503844659040d1900c0905040c559480a0700c1c10180d000107558010f00c074a08000524001000441108948016954030b1541e60744201c11501d13510040d04c204c900402e0303840000f6001005e03040099403c7e0042000d0450741142c0c1c078010b0128dc046416810038040140800342042e0303200e0300400122441980d110020b5035041c1300042200c031a0756 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 652297023 1250 652295773 652295779
    0x207150c020904020f030d03050709050a0e040b070c0f050708100e0d3219140706020c010207060c05091206010609030615080d091e12080711031b09010f060c031d 71
    0xc4007d5001d0344e242c0c01a034001d086980300d00d00c4558803181401000082d038018403200c0044013010074006040c103c86107620245a1a10461150040d911441d16040d111000e9a960740030817001e014108050200f0718425201e807100b0001d4201d08501e5035168201440c43d081030007000c00415904d01a600b01005915600080340100844d4250060003590007400342840e070300c003054010810703280c010040c3c03c2070712202248650a0404941d1070703030301070740c020b62022200c0d540074441e4100080d038074021504401c000743c80d41c58442d03c8070428000c0c1034110002088995000400401c511600310000505581e0401170210f14994000900d002169441d030040e1007a201e4007005140c6190b10288040907264000354614000d4800c0c6501082d80c85503008218551a22440b41c1002030102001040c6d614460203000c2100518280000e0500320541000110403040100c021103d150094526001d030001c01000c03040f40b401d0a00081c40e02181000c01024050700c12003003c01600c080c000035031455801 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 652298273 1250 652297023 652297033
    0x1008071103032404110f0f0f1602130606140f07021f091e060c03180b030108101b110717011b02030313080a0c0803090303070207150c020904020f03 65
    0x3c240000442401e1804094904800f4800d00c1140b6090080940500c170140e6054100705a83c10b80c0285640840c001a1145000300403155441041c3e001a00d06c10244c0803000d14030460710300611600242801040800d2454054103221189d0040741c001884460300e18441d4490030440c542c0790552141030400780d0300c00d90b000c10000408412207500f0009220594502d84141d5440c61074108005001c441489540d040200600c1010300c01e83d2a91201c902a260141042a117407880d2415400c242e005a480e141000005110400040007640c816043c20380041003191000600072805422042d500000c0204103490f80c4074014040201c2d00c0a01000d043d8070f08a410600003c0380241000c01008030001c41d581034101e00140040240d0344600151030b1003805c1c0b4485907139907012a40c408400f00051180759601200402e0b40c1c1000786110748080801181e89041410002e481c00403107900041d803c0004401340305040fa480241010b05030780c15180c41001d40c9840c0300240c200b10801050f5a010302c07807 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 652299523 1250 652298273 652298281
    0x409030207090b0a0b040f081504051f09061a040b06040e0a050c040819020315010605090d14010e03040e010503010501051309080708030c0d0e0303010503030414060c0f07060305070e100807110303 86
    0x7c400da42c021924207a04a036060700f9150b500c075640703100403200a441034200301803030a6203030078400044030440d45603400003680441036035520040340c1650380210382040c010004001103041c01d210304426280f04503071407070800c0e00c0c08803012000f250003080318056070703241c1d004200440348a405640183c01600d0a9480000071412030790b90703a00b860342e405d9210340320b10311080c01940c0d10340c12064182c4425030f40c1e8620748151036040c09040821144121043e500c04400703007034001428410b580013054010044e43d40c1da4545004204a03880c1030b001680705c4e074902001084241d44101d070324440981c0d4103001080c94001c50500500c2d46c010a00007800141c000010818070b451600d0043c249401d491508008a024201d00b807660ba010074000d803038241e0f104100901003400d11100c0643c22010082015241802d10b40d11b00d1704081d0807024440c000d9001050501c00c00d40c05000b25a07001401d490728040145a030b100080e5120040ea42050610129030702099056100d0014060f80e41c502c00304803503403424 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 652300773 1250 652299523 652299539
    0xf021b0f030c0607290601080103081c06080d03051b161e0308011d090606040e1c03021c0b060d050613050c03090c12073501060e060409030207090b0a0b04 68
    0x2061703401c0311410000045e4044201c405075800759010f408180c6d9840400d80c01d56549482c00d40c04203c1c100f824061600c010314030400d050180b00c000c2d00104000d0b110000c0380a0340641940d0300a009080340c000d030340350410898070084055a402078605100d0702c030710859034200f08080d81d42d040302605e100c1d03c1d08601700e404d054000810604903a40d440d4400d0402c44110440d07070340386005564141c1c0a40040c0d004c80c3c11450f1903081482105c1441c029111840e15a801030001c3c80d0654128102107034021840405004440d1a00c4030400304281c0d00303000c0c0d10910340018001d0b00c1800d080120841e650300c04142c40340c40f904c00c000c51040103271a04026500300910380358155081192407044520609001c82407600780300d01411070b10a1510003c01d0624100140d0100b0b689100d01c840c02481d00d002c0b0303010400f01c2e80504640d5440c58103030000070f6650410044a011540003420396000354140403031840060390015a00d4215a079040000584054140c000756012156510000c1820030204020402c00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 652302023 1250 652300773 652300793
    0x12070213060f03210804140111030f06010201050906041e060f090f02100504050a0b090f10080411180406150f0e090c09010302030a1217040b06010f021b0f030c0607 72
    0xa4003901102071681c130f5410f41c00d4500710303001c14400000703091000070600103500341d40c070b4403d110754590002ca684004641c03895403c1d0812141c03c08403400c234400b0700445503020711403030303070805c8a00c03002d44a00c1c81d0507114162859020407040607290704030100c4100703000180d8031211162612610a01141c945d500307041c001002019000d0340b00d00381c20b812050700c240c0a8402c132000c440b40030702000302c03d514002401c1d01c0e076080f54034126040f182e00c08040e02c05641c2c0d0726074100c2101765504c6c0d09041d81400e04011400c00075282b140e90042c40c60b005085005d0b144203d80300da0169003c10041040300c8119226a01c22449501c1812204080803011134098010610340d441021610f0480b20807110210410400b40c40a10001e90103800101561010412036048030b600c80e45142449403600c40004660025200211001d403a4001072005210344c031341c4d0020304036a068a45100030030380c01d503002900e69a082002c6c4c02d1244a81402d810075050b50310207008840b0307842c1c00149116160849824007480722 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 652303273 1250 652302023 652302029
    0x1a0702190b09100b010e01030f06080105010b1c02031b0a020c120a1e0314250f021305070503060d1103030403030f1b0b06060d1d0d0e01090812070213060f 68
    0x103000e00d60320304400581d24400c4c1c0c612401c05075565989030309818015001001100c0f02102002d85410010035186000d000e424000c28405000070ba640704075148581c41d185081000b1140c280c01042401071800702c00b0b0a031002c0c0d0110f01295550f540c400c0505038581440c013a4119040301c031141c1c04200c101804103070240c5d201e0040c2411485003145940c0c4003040d460b0382500801050049014200341c032824806031041d556902c01801d07100c410079407031500707000c26010100c5403160518030703900841c104440f20b031031030340d00c010014041400c201c0000740c02ea0200034502401b420f01320707811000b0b00c030710003440c1c00380942c010341030782e9941e40c4909008044c3c2c02500500c0d800300303960702c002408a20100480c40a11604452505041c0e2181001c01c1000d500250f40610070343e840d0000c415000c481100003d0750454030070300800406a00d40b8003c5c161000301c85a076414000120303410088050b000c1003c1d131650100900c0603650701180d200156009034144506510a417520b40f012802d00ca000724001c060b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 652304523 1250 652303273 652303291
    0xe0c0c06011e0806010315020307140d02090a0518040206090a030f0615050d050a060b0109090e06010639020301180c03031418090601091701051806041a0702190b 71
    0x500360b01c60710100d44d182d90a210003844c00041c2032050181000d0f0b50301440d002169441c240071400c080030071081c0fa5400c44015005a513900140100043c60a07100040003400d05481143e03440c50a0843c0882010700144060b00407280040c5e01d0720581e568203074501c0a10b510940240d00ca507541d0425000412034070308110b1030821024408141d5140c00502560401d900400402810b000399440c0c10240c41c040103454144030041101040c01549409514101c00b2140d00608003580760050060400c0c10240700030394006405103c0e40040111450042c10700d829115101600940a201003801030010f40810004c1da1038045042041020b091109002c07240030b45d4510443c1c0c4c034146801c0c082489001404514a90001c003010100e00b40700e40f08942c070080c14101010700c00e40e15a2014000f404445141c42c143c0d41d20410450b01580302c01888032925100740040101d450282d0310362500d042d400751000d645420402c0041c0c4414802c014800c100f83c0c1075200c16000100c1481e0650301c04c0c00560304441 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 652305773 1250 652304523 652304579
    0x303040902120a0509070b07030f02070e010e1b130509091914010b09220201020c040507030f110901020304030b0a060f0311030c0306101511250614040e0c0c0601 71
    0x42d003405c001500c0426034010300c2c1ca0341c2c90b149aa56040c2d40042c00c00741e029041d402410800900c4941d0740d203541d4000c104414041c141c1d8902104080840b004c005400e250750070060010b0401c104030b4032008416614190f075500c10a4691000c0c19180c101580e98401408240031180c03000c119291308200c1c01c03442a0b4000b03100003443d00c81000766203001100c0a821003401000518410349424108080380f50060060f1034102d0045000304081c0c8000311019070206c0c0d100d000d08440070846210340d0000c110400766240c20500c00000007500c902c01c0744400392850002c580030490702001c03684164003c0855070f03000c0034055603900d03000c0c5d9045030700d10045100b8000d0750a03611032800c0100700c4510403140840b60405803070500c0740d80d4542001c1a4520701c108100828540190700b0300300302c260702195a0544200382d4030300c00300c021901ca00c0c40703400407001c10080089081188640c842034a056800849004001d60b840b40104101d40c080d4005103801c0344902130000502904020070703d185600b0401d9018 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 652307023 1250 652305773 652305781
    0x9230708011a01092711070f0c150806240c0307060f05150d02011b06090501051008030f0d02030c070803040f0303061d13110a15121b0e0303040902120a05 68
    0x1e1410f100005d0b8201010340300f00340d28403450321990181c04003031181100306003800b0b40d0342c0700e0300d0910441500496060f4840340003401000c0207020f00038880d014030319140c1c60a292a8020a0024604131040e210000010044400724103114099459000d00042140d1722503403607003400c80c06400311080d140ea00b14680300105003205810a0948a2040003800c03c01145031680c0c0111502a2280140640c07103030400b1903480014030f18000c0c0062603005074004500c3d804d1444020415204940c801501680700308001210316844500742c80f40344034040f1005031640d60316000c15482e4819400001e0040e18000200401c201802d078416461078029036040088940f80c0804421070800c00309800294040840065200c000d882c2d2003901c403e200c2d00440100300041000300b2044601504009415494004030b50f144540c440c410003484c5400c600c0c00d000700781c5001c00b07281a020b190130440c82045584892050107403000c1048030014880c0308811035440c2d511854981c12002c055486465190611000c2 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 652308273 1250 652307023 652307039
    0x10050105033702181005190305150604060206070e0301063602160605091606270605040302040f020316080a090204110309060a09230708011a0109 64
    0x500e10400c03103905110440104240b90000391081e41c2c60806040340d0302c00010ba51a06180041d28800081002c207a052000b000c041003291110700ea812800c002e400c4c4082c480380045200c087c7c00d10285410002095115802000740c0c0c50b4a001019400600004000400960015026225180039524a070041610200b01030036528944100b00614207610b07481d040782020800e4400052029903804920a410a00114260b800149201c12106401041c0320148207031401215030192092000d0f00b01e48905903800d82030a8581c0c000c0300100b000c4008602a88001c03000380140c40b40e10800e80340d00071079840400402ca907006001c00c9008904080348504081c0040c004c0e640214400c00f401240030b20700307040464401c0c100400f000c03040740d00d4002400140e1581c0c03181215803110807100c0340d5a454215012481c000c00505409101440d01d1501000300c0c520221820390301941d44850b111550402d6400703481d19000303801070107095280024038a21480003107280c0d06500401c0e211030759026030b0340c540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 652309523 1250 652308273 652308277
    0x3130501150825050301181709130b0f0a29040b041406070f050102040306110306030a020f2107090c05030118020d092003010b030c06070210020a020d06020310050105 73
    0x290880503803220380c4008840307407107100d540c0f51006542070845445940d00c0c00a42500d55500d1000310840c82c0003181c40c00d2000030800031440c6200850070070b10700100318010401d020000000101d4081d0f454101c0c4e0b149984050203040052002046000443e4a806c0341d6031030036040c112014a8140d0b025100c03030801940000340c40461312030320030a905062400020034104440d0005a41c0d01c40020046040000c0c00b412008105501400c00142c90340d00707514254044420b000c41c0f0010900c414020850580d50010f8813010180c4c4c142d4851805071200e20105401c1c0140d070b8114541864281d813244c1a400c4002003604c100c5224030428010404900c07419141480280943c021440da0a031108810480d00d070000d1105401150000460b40150b480e100c3ca241d0134a4402c80c82d144102c03280d15000d145c24010b41940030422009890300302c004034002061842469002801041c2c1d801d002e9200500074800064050303000b03054850014554a0711100070340c002c698604500c0a03e0300d001ca0694400c2003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 652310773 1250 652309523 652309529
    0x6070c050f041107020f060c030301080124030b190209100c060f020a140a140318101a010804020f060c0a0b010f03030509091018020424080c03100b0313050115 70
    0x809140c00764503000d2000031240d81161b9034000404001c28520040200b000318001c01c00000001020b510710402e9590307080c4507403000e1590fa01b00308001d20216180c403104513040940081e00710744000b800e00441003c5e0146d0301c0e61982c00400410380d10040b0f034101c0a502c191500c0344404205402040321030324100e02890b0408400500380c0c1050340003003241c4200030100c002050500c0c20b401c0d03449030341e07000b42c40d4400c03280065a482d0303c0e42c0500c5018420045000c05031900f42c0140301a0a13146c9480803280068412541000b00c070801140542d1246d42ca032005542d0040c050075501d919074040700c0e030f6440036210200c034038000b030301d0000511480c044081000d9075419910945043e600c481040450b0901911000e10007010900019801c1d1500c2e01011180300341403000740c0c681f0b140c00c20b1903400003841400d4465181360030010b0001c1c590b0000d085079224442c48050354407525020b0802400103a940c0015070078480000c1400002c501c80501121428841c2009014002d4103108091002d04948 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 652312023 1250 652310773 652310801
    0xc05122205030d1a060f12040f0c030c030b1015032a09030c080a030e0d03050c070f090f0b0904080c030d1a15070314160c090203070e1009060305041106070c050f04 72
    0xb01020054020847c1c105070400e0081d002d144000900c0e480e100020303005603200b101c1000007502c2c20001c0008160455912805110410f0b40e068688a0f00b15030351325419a11000300350341c0c0c500311518000c8140141240207100c042300114a0302048024100465a01058980020440002902e481d002401c1115a60b2558407000c44003848020b10140080c1418110240034041c0029100c02c40700700700c040c008000c4000400d8165107050240821035000c408641c2c5668185901c030019a101c5141954100f640100000e548101c1000f00500350f005412100303c4160510a48403110241d042c0b4054644c030084a280058880552244541c0d20610200a0200341c003100e00b054840c41103406403844030701280000c0401c0545a450309640c240c40d0300b15480c03095001c02032090041d8818413080360300c034080d5129102508002c0e00502182c10a10410080540394000901007100b641d0308440841805405952540340782d1401b041500000d02400b409849400000c1c4540d2038640688050300140c0c03 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 652313273 1250 652312023 652312027
    0x31101021c0909050c0c0a0c0611070302010c170708180103060608061309050106080f10232a03090a060f0b0d0f0804080a12030c05122205030d1a060f 66
    0x141c0f251001d000700070032004180d401400302004a060030311046606500c41c14a02111301c0c1862406803080d40c900760700d440b1940c01140c0a10050340c0001d10035205a17000300b0f0030018102211a241181d00c0b808a00074000c040204030404412620100040d01c1c0e0000d880038000542c84032021107100504941c0d075988102055800806154141d2040c1502c0c0d000300c0010030320940311000149090000c032091100da5002c5c9100c0211803d861040201d41034030141411040d40c455000001a1a809048018030318107980c10041200f044800303080301c0d4008428000e48900d01403c00300e8a44443c0c0070706841c0c5d103080008042c40304855201c0c1c3e0442603801016000503140c2038641025984901500b01c0e4415030400020401000c200b0120b44882d118004d034018807104c040c1c1c01001c1d92040240c0505106003032049816107210508481d6000c3d6241841c4202e80303401d00c00001100c800050040c00324000040c5081055003513030030000800c6040c42c15000d04041d4101404614400c0b607800800007181 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 652314523 1250 652313273 652313279
    0x10c050a0c02041401060e12070308070311010207051617390307090504120801050102030f0a0c0b07020106170a230a060e010207060518070905100e01031101021c09 72
    0x90600c810419002070000548595040a4500142421b8201c200030810007100c1c11032500e05110003640302e12014000c2c014040c03640d03544030103900540c00000d081c850106d1403840d020009506680c2507541200480320300135441d011004010b00c0502880c186074568003003c5040c0f94000484400b085001c880d40702036502280044056143e010340380b1042190151803040c41641e080250b040581100340c800039407401c141c584400342c2c4504003200c809000c281001041f00742e1f00841510051a406030201d56034624020301118000414040184895020814042c0302a07056100d0400d64000c0048418924501e95040e40d580f0421034000309040e0042540340740070030044000c120001ca00000f00d810f0b021040e9524415142d0003001e400f49694085a52418004640141034200d241c0150000d074100c07030980c1260301c4154902500c0c21450712003010410344483e064880008110200008a80d96140d2800c5409422038003a000d0040c1320b002181c1c1d84c1012281d0402000f40015104c2c0004245 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 652315773 1250 652314523 652314527
    0x12071a270f120a1106090607090611030904110f0a0e01030510050a03021003111603020c3f0a0503130e0c040311032a010909112b0603031e02010c050a 66
    0x200003c03114007044100c00700010148400c0100a014a80501c00f03401c81d840c01403001010b4450329404442049002c00d041035a1050120442d81500c105032030204140304d85484885251041081020450034000703a48509940e21039002450b00001740e0b4244070307548400d481c07a07140a002d40212684a0301c254010001881c100b4180c0201c1c940a003408502080c41e402c0b44061500040c1d0034815001c2c203a1082e83c101741d4144503940303c810040324076488000c40d054560700e04020340c2c40030074958021810040002c11400816185250004003110ba4055041c90815160303004696030a40c0c4003480d8401064800c06d80ca05a4810501d491496003818a180c55010b030181120740300e141c040c01208000c2c0d0765603640c6011150405034010043c0403041540000402c0f004e559401010102d00d460820f070007007074036202103a1004180d0f920500000180c1803044001c159155114144180303407501c00410140c00070f000901c0642030f03403c491000d99841c0420b909842a040e0b0b24000030b1010003004000f81c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 652317023 1250 652315773 652315777
    0x9071704020a0e0702070f06170c1810090504060b09090f070c050613140109150f02092701060e0109061b061d0118020312071a270f12 59
    0x1038002424808565543d00b80014070307000a960003001a0440c2205200391900d003044100100301174a401060580d501141c89410640030702520b0a40703d00140e414008058040c1818441c00010108401c80c24030743d0f005000005244075584c01030f0b0401000007408004842070318803001000d400540e0700c0e9a03610a10b00d4503140140080300b8080d180e260a40031920401038603104003540c0d040c0c00d03014049401c01040009206060341141d0381022035490000301a0090403a022140c8080803819600400c0030401030300a114207139400100303e0b8030018090400550900ba500305525131800c0e584d80315607003200c40400c1c00c454980481c21003103041040e1440340503108804903d00300394001d0825aa50703800c0c1642c0b04000e580400395800c944403001440300f885104412540b864030340004501550101e0703140c0641c03000c400307404e0001250450910446a0030402c480c201408500424503240940c0400058444a05000c42c034440810740000940003a40c000c00e083c0f544010400004664102403241e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 652318273 1250 652317023 652317031
    0x20409050304031707020111210c010204090e030409051003030e0603060109243506010309050304080106090f11120a15030c080f061e060d0c031b05090717 68
    0x58401003100101140c0f10400d00090381340031081165840100b8000100050600c1c1207040d21500003070050b000348070b0070680840700d04401d041c02648950900c00c035203009000780c0d40210552801c01d0020318004101000400a07070f036a1040c10450394480141040403000540001400304c0c04848012555240000103560710400500d0201111911109002c41c0b07041d40110110000e0000e0b8641c616080e00110550000c141144a0004030b00d4005a812a56481ba1002e051400d9068000c1540d0381d21941149140395000001c0b00d55440c0d890703034510300034032503441410040d9240c010761004416036800303110002c08c2480411410000c000345608607840019200d2009150340fa5140c1040208015900005500460445170078600d08205603041c554480c144110075000380040101103184200700c03d00f42d00e801051200c481e81d403140401d03008110960090000e0011180c00402c00c10b00b014010035040f4504406541c0079a60001d100882e8401d80744100400c511019007000c004440c00700a81c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 652319523 1250 652318273 652318283
    0x6110313060f090606031a2508040606080a12020705010519030b0a03200a080d1e111005180a0308070e130f0204030b1311010c080705010f05150402030903030103020409 74
    0x3143e516603510003260300c0c607401201d90241c600d9034000b91417a8074a5450340482c00c420388200d1a05590308240086143c401458144070320300001c6020700841d9444007010300540c508072450b102103410100300300314410000000510900b030000c40c0f5544144150744046100200c00c00030b001c0010800d1700038008110030700350089a100b100102107036038090f02c0001100b0210810200024450030300082c002c1682181005502040c1845145684420f0b1610003171801005595500780c0450200d400d54035292007102d4a1191884240e5a83c4070365221a0141c2182c00110a000e1610900a0b8a56003e0000940807903503a10004440390301911105c010395400500c0112040c0c0e8000c0d0150440b01506680c060f86170307001c582802009142240c840d080501140311000c2c250380e9a80d031900702c808880129040000d0702c40c81c0b104101c0c2d0081542d040c80da00000078020208142d1100008040407551740b000c092503003d401115060034422a800b03140403c010354910f0782035400f0f210190420b4001265 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 652320773 1250 652319523 652319531
    0x90f07061e030b040f020903070b09130b010c0f080307090e09060f0a021e040503240c0a260f010906030c09020a140d0f140105010503150301020405120a06110313060f 73
    0x3e40d6158820700c100100d4a0800507121f4480074145450908250400d920070401041662110341d1101d81c450002044000b0101e2011807410040f1100201c49100404110200c0525410400c0007005140301c0c1420341c2c0d500e481c0c15a50070043c0c4400000366a945039582081003c62400010030300003950040f003848026140c14038003d044201d0070181182c1c245101c90215051006107000e10003520402e000c0c8a41e4149418a0401400d20f8140540300c1d00c540040014601006030181440030800038151850101d0311040007621000d0100c04c84600b20740211510000c5000781851050100b501c0d0842c841040003030410350b030381009501102c0ca010a200802800300c4458120b40001c090314444500c011800e40320760802501580c40380700507500411410001071150380d03071007020789921485007505440f00c1182040406e00a218a03006581c0107030400c7c051200d01d200000313400b840c81e4810f2800b08510000120081c442e4003040e01c0c0041d40619a01c90f030030102d056500111000000107900003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 652322023 1250 652320773 652320791
    0x20d2306090a050103080739091503031418130c0201050f15011103040e0403020f06090109020d02091905010602010605010206090706080106050309150a09060c09050a050424030803090f07061e03 85
    0x2e0008483c00c100b48508800b4110910154161b07000c0e0112b407a8080c1c124009080c11590080c2c00108040440c0c010802d0119000903c980c04000300c0c04408400741403801340040383d040a202a000109900025608000c0440c1002400040d405d00c1940c40d241101015038038400110361800015610203000c2c031082c400130940c80c40c1c6c903c1840c091442500100150704409400e81e0403c0d40007400301c0303140d9140ca40405c0242e2030b4400c2d0f8240d0141c0c1110748500311703961076a414101c407046001070031801d45088000304010b034055100c0819140b0136000c030313145640e89481040d5200924003a60f8002448440100003140c0900b02850300b004800003034800440b032000301c240e10140111920610a84c83d102404244541c0d4418090b02c2d92645c540381c9442c2c1e0411001c00d440b0f41c40c1d031152034051562400c00304d400704070b040444036080900242d5081d5150b078a042010060308169560007050244404482c910240080e4450840d5504d8650741c3c0b80d104003680e0810390a101100c2c0505144d1a22402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 652323273 1250 652322023 652322093
    0x121407050618060d18030224070f030e10021e0f1b2b110f0d050c010b040f0906050c0309100b01120c081b090102070306020d2306090a0501030807 64
    0x1107022104840d4179070b0b0780e0422030500030f20f00351001c00141c400b003c5903178407800d8812080e12101c0d485610340c10642842c0c00d036190204c00401e5a0510b944040c02012000010004603400030300c451012401c000810860700404244075115113036108c002c4078000c02088251805205806c0e58403202e420a07608100d00c00c1318142d006944e0f10000750300c06960004041003240c2c0101a48650282d03020041404e400800f00c0035070fa03490102030042c14082d000ca21503a03601001d40040181c0400900309001c00c042c560f441801800014000300d5030039060000113191100314009603032042407080001c2c64041c01c1015824001c22200003500c1c100300e05130f194000b8003052401550007080c81c95480e071000d460811034001c0d030007480c682c8605120400b04007041140c0e1b800505102520b412200042e514440c0901d010000c200f102400c410015044a620213860b14038028144949000d5850b034074541c0e61010050111030302404014011541440700e100460381076010300c00350340b90300f00400c103c0f4100c1d0380603 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 652324523 1250 652323273 652323281
    0x721120b12100e01090b090d021209010512090f120c010c020c01080c0a0e041109010f030e0706051b01050f01091406210f030f0d0f0b01020a02010f09090204121407050618060d 77
    0x601d01f419400000c81364038040e410080c001440418881c55030410000c1c90000b0200d2084000701c0c154801f0003004100d070074405029000500f03020070111303241d00c01001d442d801d058101c0d440c9807080c1d52a16400754012070001c50100c1107181d05a6805c81681d80d108240d00b00c540100038650200006400001c0d465111480740841c0060209040c40d128120b0710001000d200c8038000b040c04241c01c1050402001e400003420200b030f40c8650a0407901e442000c09085d08180001403160025800d00c814446070507000510745059400196051206600d10313200301132006400d60714a41c100b00a000c071548510401c83c40308000c074090707105a8182104202c0d01c1c6155400005c141d0581007000120040d600d4014400c100c411907030110b0510480341d00c240081c0d03c0d80800c1c0400781c1440844945880c1c254800c50340600074101c405c108540700d5480d008103107010080361004507074072000c82507070b8114041d0000c0e1250841c0c80080c94240342002510440c841f04203480102604050144000c040003d05805 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 652325773 1250 652324523 652324531
    0x9190b010801050604060f051e030706030905100204060f030e03130e060103180507030201030e0a0b0f070f050c070513020f390d050721120b12100e01090b 68
    0x40119055040c07503046801c54001401480c0300341d2600c0d070704019149000d00b0745000c43d082101c4228402e05956039070b900001207402c40300d501d401007503004641550141d00c6800404d0003502100c507580c1c114820f00049215074014040800c3d0b42e10342100940c0d10070342280d80d500d0560004e50707060007003240301e8007050005c42c0c01a02c4551021000c0020700d5903d840398440958003d0901d000c00f080907220184c90340c140740000380c10540c50340a80b2029030030400a01e881c1c50792045604003245001094180044415a40e00000400101c0001c940c11300c12006e44006042c1d000c040c11a541ca0f00003013240307240d88400c400c03003026000d1000c911391805150182c644d02006d034118505000041d2000455101410080c10140c1e20348051080c03107580004441e000500c0724241030382d44006a0070b11100c032801458a065052407400c1001031515488200c2039004901203d042c041146110f00b040400c500070f68940d05507501604848564219940003103090005441c00000c05650f0380d1607007412040c00711 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 652327023 1250 652325773 652325783
    0x110450060c011d010b040c0e09060a05060f0346060b0a0306030204060e130f080f28110a02040f020408071d0c03061c141006091d12030919 61
    0x31421519200081c09017a140b42d0301145c040018510154001e0003440409580c280603040e602d00144903521141700d5000a000020042a100c1c18002c407045000d42c000c0b285c411807041d881605002c04c903183c0c00c072100d81703a50800342024000c010402d01d143c1c0d51030b00145d5242c0e03161213420004000c14084d00401d09400d00d540c01003121415030041c082600d6142e406440312800100030401e80201e26008a0310b0164090f07041d000c0090241081e813620b0150840460402e100040c04180080e103600100301d141c54011440c8804160b4000c041d105840307820b00d04080703504460420380c01840c050380044c100e0040c501c001801e2544884c13815280c4000303604418036a0591021040c1c540303030440302443d8403441c50300e103041c59440c060b40420089860382c50950403d01705101c40300c04002c0d0b2010400003184901d02101d0060524044250190a4900c8be8580b030340c0c5090100d008869103201d8040110110030010f00c1e404080b5540705a0651000b4810940350165401160300d1001120211128602030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 652328273 1250 652327023 652327061
    0xf052d0618031903020c010c0f080f0a03140f010605090a030b01030b04051209130f14070305060f0405040b160c0506040b0412080717060301110450060c01 68
    0x795041c0743c5058032000c000800e10b094a070740840029800130705404060000e20746150105203038a03040003140180d140050150001080076005803600c5000781c186065550f40070b119010f1550502074581c3d2050711910658004080140441c034040c0000300109a40500f12203240e41c1d413500c074113424038002e0b007040b10918504400d11003405400c02070196607100024a04e8a09a82c00d400100c40580c4480c0a04249440c2d100d0701d0301e0036009501140580742060300d0700c905403802200007002840c00301c0300315115100e02051105c80742014420984103da1242c070b001d103182c4a90b003c84210780588201d850410134407080c0c400000b802030102d940503601c41c9200400c03c0c1400e20b130a2a025010001180c01c10611508025045600652010541840c1407404980303490f04000309014014a540200c1c0b5440700103400640d8000180e000001c002d0706144192111405582550030724030b007141c01c2040720400031044400b054500b84045100701006000c3d81c40d00c806000d1550030b646c0c00d69500c101460903 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 652329523 1250 652328273 652328317
    0x2030405010605210c011b0614180106050a0b1810020d03050105090c09010309230307060e01020a1418040f050a0506060a0909021606020712090f052d06 67
    0x1081360700c440c100c2051081e55500d03000b074814440d034810b82c40560504000c02d40304000b9401c450481c4142140341c100c50140a4404d0f0500715401481e0140e0349924004603200512060490610841c403e03120b006041c1c0404910f0300078699040d4100303605c000701c0b00151108402903541c030715800758145455038002e04042c0c080058003170100c41050388480d019005500400003500305203030842e42111030909000903110f44030b042c4084221880f008104600c0220005803000744000006451131502c00d4209000c4c060940410900381e009580b04000440e0790384c1140d04c40008000d010b400140f010442c4035220015140014060718401e03140d154030140c2da070003802600c2c050340c080e1a81c002016201285001c41c5000000e15485c094814209101c6c0d0200380d903152410014100d103502c503008907056450300392604054142610103200b02c2c0114a2071080020604c80c1c0c007040d00e089480050251100e0748400f505804030b1910040d655403600f0120980045940d9400c4c00b80048042ca10300510002c84 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 652330773 1250 652329523 652329529
    0x12010f06120b06150301050618100207030b16200109060c080a0c030b060a051e0703030222080703080f0909150a09091104151d0a0605061e03070e030102030405010605 73
    0x2c000d84900e003d44081800c00032081120801c03a411204295241030b9a440f81401d6400084120500e0940c0149041d031060380c42680011001e0a6a010b203e6001c4240c945003e011044084c101028001c80c0103841c0854054481582160300c1d40a00c600101d82e4801540c0c40d807045510440070000818905001e01c45103000c580306105e692805400c007000703443c01c40400200c050141074241e10400c20005500240200b8107022208240c0460040940b210110324010303001e900300b690200105007404241009203914160903d0031a800000a04031700341c19074980400ca5440420400b46191081000351881e89900303a800d41300d0b000c00d010741314500c500c00041208040b056407001e680d0f1400c041d03064011480703482428020001c210380004d8101c20003d0800c5951301c4aa11041a01501d040130132130f48228100f60b14800c100401c07040017a5622141082503900ae1002200f1080c0b0140308030b0700000d03c6500003143c1104460a083c040007030304100107400c0ea1300859013108c0594580b60100a182 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 652332023 1250 652330773 652330793
    0x102030c0607050a110606090a1104030f050604020f1503010510051605071701090201080f04030e0d06023004060b04020c0307060603023a0f0b0123100e12010f0612 72
    0xd40d0300005840e4504207c80012008507000d443d00340e100d6914404452808110000c480042d030303000f861a111100e942c14a1a1152003ca50a0340034075201403440702549040ba440f0341259080b03000c05400e43e400c100500c0243c2c1148184841805030810078100320445610301100001c0c8140b004102450400085080c40e1039900e003202032a0781020f0b151030060380c00045981e4003560280c451710103a91541030490b440c071007518034650008441540b42d01809181d400903c48055000d200221840c4000c00c2032203c200c604040744401262400420009102a0400890740c01c00a2015050900d207891040c110781c4550011a02c8079510001042140cd00226050250319203c2c09140030000034100020410ba4810060117440d200404100c2084003416240301c040350400c2c807984256855a200c000312800c0b00401a0320b43d1054186d0384010720b031000540750020200c0d664460340000103420301010704040d601c2d041640d525103506071001c002c54841d060003400c032500180007140107414001801 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 652333273 1250 652332023 652332047
    0x302042103032007111c030503040c0f0509070507050a0203030406021e030f070b0714070602030601034a01052e0303080c0d1508060a0b0a0305070308090102030c0607050a 75
    0x14280e414403d00100c4030030000d40d00c2c800c0c2c0264201e0b029a940d5800104440c5107001c10780b0007054107040039424985e21202540c4620310444940c01d00d540c650200c040b412480c0e1244643c800c100000080c02c0328842c00180c801035204004071461607280c0d900007415901b0607000000164020345a00010400303d074800b03c1e5400d0140301551409015006d118803500c581c103800751003520b407000803031450340c0301d004000500042e100903261244510700e8014065841a503216000a041c0000e5440c510311243c41251108000e071101c1d400d150000b00700d601080c5c041250318029040f405d8003840143d400303005007071054088196103880c0e0307551820900e801d803658200c07965114800410030700009800c007141a801c121010b00580e21821320703c01e03000c09080302014103000300c15110800565000b001a20307a0040440410a200e80c440d124203011424060344000ba006a001e101c0c10000f00701c008006001000062040c3e81c07400320b40002c0d15181207010b41d0b1410000300001044051160700241c0740400e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 652334523 1250 652333273 652333301
    0x60e04180b131403030c090a061b021009080f0106080d02070b07031d040c090303080112020618030a14160f151d0d0501090b0f04030c03050901030204210303 69
    0x21405151a640c101460040c14030032280e140e41210b00070f2009103295103024010100440f0341d41d241c0b043c280000340d0480010789004042400e40450114060b4842e091800d0320040ca200764034580340c00308485c8a5021024400b4410b64250204581c0b8060100d61600041100013107a620b1404410600e0545103040030700c11074000b1103040c000494020201d6864603014079001c0b03d5080304e14001004039a04041c240da210b4a04544010841c2c0c211030003604580c020340b2400321681e0380e1003102c0305001500d40000d503c0b030000c000c00c404400c188115000030300e40c040d0854401003560764500c11805a03000840003aa884001c18006400381c1c00800409800321682040c00103242601c00e05002d5060310226090018030342c1010840c0420107070702d000222004207111652100390620074020181444240c802d120340800040e442c03640e50203054082d907455035035032013007140585084501c6c1d0020113413507040503003c01001034170300e8840044c20100c2e03c010040b401c64000f603140c09000c03148071101c3d40d22 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 652335773 1250 652334523 652334561
    0xb03040512160305090a21110411090409170f030f0106030c050304020d03020c060f0405090912090d1b090b100801030201081f08070e0915060603010603020706090507060e04 76
    0x1503002e428480d00c4240c0341d050501a84034880030300021422222500305a101d2016400302400110b0f003480d41c4290b0718020201d0780034a07200c00080c0000d0301c0604610304110030040088070600d040c968072400304ad43c054012004486640318154507290700940c200d8210040100612159101104c0d0550042c10942000c015010440030701030440c1c00003d00207441030890a14030020725000b403040c1d40451030000e280d16a920040b00c50880030303400c00e00440b8000c00d4210001880301c040082c0d0450201114100117040000540401c460f0a15000c01218201c28003091614498200c500c0c0402070900c0d4080481e4203100d2900703001501c2c0f10b144525080103a20f100401c0540d8000c04040c2d0800f000920100f9250240306150103850b0956104076070a22600800040000388844940e02842102c03040c1c42d404101541940d07100070007a03d000ea0700c08020001009128083da0080c00110711420010031104d086e6181d442c10542140c1c4001e0100706108130510141c50310344074104000c41d6940202e4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 652337023 1250 652335773 652335787
    0x31c0906020d08011401360501080c0403080c1e1c08041214160b10050a031703061201020d0f0b04150915210209102117040b03040512 59
    0x2080601d0602c150042025017a0080543d44d1146480c51240e41c0c15800c40484650443c0c5191003400c2c004100d40602180b8002c0402d1941c03180111500608100b58114101400c1d515180200c1d40005500c900e54803448411540c525a11100c4000c1e181c1c41380e01408034a0030000d0042d400d030248011420401000b1000c11001441c5c440d000703150440d5502e00b500321500140c01e00d40140c8200e50103000884441821001000400c0348028460300103c0400c4041a40e00c1d0140528036036240402045409443c0d901115070102001035948004e0040019110b000440c0c00c542c02c80c1e00c81800009481c1c0c5440000e607440000c3d001700c0888100c1514200141c0c2e052014001407100705001d40c1c5850798580f4404618040c51034074510151000c12400381c0c00031112a81d482c50525008422401a0115800a482c450070002c1800c111a040440100750700502c1003154003c400b8400101c03404e80d04d50000d80780c1c40110401900241c2a60040c0903601d00f840d0803c070303150081501c071004091408114007 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 652338129 1106 652337023 652337027
    0x1e010b060723011e111e0a080114061804090803010b0a030e03160308101518090608120309010609050a0f150b0318010b031c0906020d 59
    0x28502500d0046441e509a95101d200d034011001c402c000304401c503032903030403d401503171082c1490f510b024061010041d0780050400c00c85084000450174110290304401428090030915440c40004000301c400540d07036224151405850f2500c03610715607610f45454110b6080a83d10a0307a0075200e6860701105145500401c0c69030b03000a04111b01d01100040c08000c4480070079411208501c500e031562010380300100050000f1460803210940080e03409a4003800701c0b000101070b69416080040142914200303141d5403c54044035243c64010001458001500c0303200908403003c3c02c4d240e0780c4103000180181483d80c0901e0040d0304003810071840c1c0d02d943c0c0c803980f026000741c2000c1281c5104440c40401140c51402220b12000d02040884c80300c002c480d60800000d40c600d4004505c100135a8040707400d01c03000b031541d894400401c2c00300241040c1c00c49410000b500c2288010081800321f1680 = true := by decide +kernel

theorem cover : BRFrame.Cov 652158273 652338129 := by
  have h0 := BRFrame.cov_init 652158273
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 652158273 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 652158273 ≤ n) (h2 : n < 652338129) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
