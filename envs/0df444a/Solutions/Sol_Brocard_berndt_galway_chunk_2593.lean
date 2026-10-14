-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2593
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:10:00.181345+00:00
-- url     : https://prove2.me/submissions/079b6276-d456-49b6-95f3-3f858cd829b4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 466187050 ≤ n < 466366906 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 466188300 1250 466187050 466187077
    0x3080c13060917012702040603060504140d030227040b030706020d2d050a18080d0e03061512100515040b0a060206010302010f0306180509060a060f1406 67
    0x340001c010750300c00d03000030940341c802c440c000704101d01c1d10f003c2d404da030b10315401010001c0c03003c154088402100428100e400740000d00104120395a610b803034003181c0081d42d00741c0303000ba152101c80200200411841d180c541c0203280452606801d1000030001100c0d60300900000800c070103200f4001e680f19005010a81e0004003680d403000d907507400107950703401d02c0f10310301012558203200d2503505402c00031340b040c0c00b40c0e03980109444e0b02d242e00c03811607240e030004103c0018420401040c5111244404030140034144c5803000f8098441940740140c007143c0c4500810388241d00a2003000134940064000a00450081d101c0a016800340b40c202428200d034810540d145615100070490019803100b850104041c081c1c404110308910b6100f40310600001d03005000160348441c004000551040641d0384440001d480c0c0018140d864a148242002140d00341100d03698450f414050004414042d85420482026081104c00c0c0703042590032003010350b44104a00035208900c440c0c0191240c50442d040401d4104 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 466189550 1250 466188300 466188337
    0xc07020d060c111009080d0f060b0c01060305070e070c11060d090c090b060702060418270b010603020c12030a1103010602060f072d030908031302090a110703080c 71
    0x1103005043e071040e040c40c0c140c5031203400c034a0840680c00388949260b02d40c00c800002d24021075140c603000500b00180c0030a6555030344407800600b409814000d45400c02114001181d01407440c10007034070b0b1004036000800b012130b20109005109801c014820461503008070036104418094002034924001c455001c00314504020982c4100b1400340c0c20107003565042441007024041c540300b4044140200c0c4002500020200428800d4504240c00751002004030341010800400150781c1030150103500c0f4180c0100405800c0c800100035040003042c0c0580b0043c50114240244180d000380d9072145020942003040300000807071011b803030580004841082d031090f0a5542d5039649002507031800115500b42c90703041401c0103c2d02d01e40c41209126802c099941c400095000d4200070400c80035102c0c3d400782c043c1035484402c807000074240030103544120304d0181282d01c0707150140140b20710b0080c0280007201e50352a00c0d034204503503045c0c0c40543c0d441e9901840c00d4611562540c501c804540304400300b180c80f140c2d110 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 466190800 1250 466189550 466189571
    0x40f150e030d05130b0a1b300f030e0318030a080304050c01170c071101020c10080a06080c0603040b0c0f1216020102090d0210050d02041e080d080c07020d06 69
    0x1500901180e40212404881e503a178440038a00140207600049000460102c030780e502e0001c55000c6284038038001c0056445110580100c420381c0390417614200d103480141102c54054030380020400160407140e041c10300c80222252030b45500e80c4100075410810042ea01800141c9442c05c000c0543d00030750000c0084d41d2805d00b820a682da031811200c0c401d00044050304248407035035800700010b000308126001c0c4d50404419a455407450801c44c18054110300c505540006140c1e9100820301486032292144d801ca804e020740c508007905c095800642031075105031040741b250346521007200e9116410908416050f15003c03a604814440c0381e9000b0016607000ca5810041c25504d4011409207149070860090001120b400f60309038011000b075103501c80074403446900503003810840d007000000e103480c20030301d40308050705521704036005500507000c1d140e400d6079001851041d185241000c2d01c003102c001e080b0524080c2008020102c000c1070341c95402c1c0040741c2d410464075020b075050300890780f212081c0105241c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 466192050 1250 466190800 466190807
    0xf0705040810061a0f070605150301050a0501090e0705210c21010b0904150c030b040c18090e100e010914100501050a060e01200703050304061103040f150e030d 70
    0xa005050340000307041804000100204202c0d102d0114010005007009250340b90b0800a24000b0005890782050168051704d92b82c00f8800d01c1e1040c0340c034440000b000e50414581e1005c0380c4103003900611680c81143c00f44903e41d9004102000c148030985003200d881140c851503424008032036a1103810030002220200c1d40380c45519041c06504a200c000c102c1000c1041c00c11048080540e40a00780c07190103050366852905907003111034402d4243c10080355110190002c1002c54140b9100e40c0c1c001486140e20000c0040044043c1c0000c014142c02807018400601410341c440000c000386030300e1075645000103c1e1442c02900b024001c15000b080f0f034102190200150f6031101070000c0b0400e4414940700000c6258074040060a06948180e41d8004400b14000010f41c4c840c4800d41c148886109840c0080c0341510080010001840c03060015549403860010302611741c08035410f0402e41d070b800600042c000c45e80030821003012214812030f41446209a140140c6164000e92080c80e014000d0f0000c90740708d16003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 466193300 1250 466192050 466192061
    0x204060e011d07090f0509092505090610050909131704050909011e0903090f0602150a05040f080702180f072a1713121103010e060f0705040810 63
    0x10440c180b14040e51560802c480f00c1120f03000d00101d0f50010b0401340918140644441e50040541c01154091040000445840c8a0903400a802d44d0304804d018807013410002e4196801c628107640b80112102116006807043c0903444605010b0302141000403000c1109141c640c90f029000f07110011503000e0740c103c0303403c00d0344680100390188400c00040366241c0300520680c60b0f200b10f0960081c00c124500036200000e011b25100507000c12149190200e54000e40d1180c1d10001c1540c0d8004040071036201a241054400007000c0c40040d40c503200412020500036400c0720103496020b03400c5a515041440010b000e01c2124000c0c10743e000901c3e04200c0c141844100c0e82e4000c602c5525440e01d411085042c041d11400c2c4c070300380111072011030ba80700400a8440030a5040c0b940ba0aa140350802080480e944043e4082d42e00500072020311070890418010003880700091560158000d0224400d824640f6a45140180542c115080d80000140003113104006a03000b9002a1055500007454141303000b01509 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 466194550 1250 466193300 466193339
    0x504080706090c060801050108060901060e010504050a08032203050604020d080f0c0a0b091605060901050f07030306090f020a0203070f0201020102041d060301050703140a020f0405040513060b040203150d0204060e01 94
    0xc100c0345c0049903d6009a4580d48982c1008141c00e08981c200780040b04c0300b400104c0742c10b0600c0342c140404522543d50f506007a003c0c0c101c0100440d100e24034401005001103501a401d0000b040f046402c6c00442c002181d115031098045e103189116020358a030101da1449101a5846803100110310382401140c08030398000281d01850449117103440e56501c90ba205c4882d200190b89203110741504015608021000d00707072444050415900b0075040d81e400c1c01c100d5109220440020340cae11031050061802501c1036122544860404600745008604082d40c5ea1051074400703040c841c00c01c0c3d9880110382c400d404490142005400b070040131841c4007000700140c4c0c010b951162080d4244070004602ca4441e2040c801c7c8041d12031b0300034100382c50707030b40601c40250700400c0342c001614230800000c201511a03014040c020215003001041900190402c0000c80c6c03030702419948103a004100b4031019000040d922035401a003225600826206840054000d00650703101d10030346408440001000b00c3c583d510040200b = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 466195800 1250 466194550 466194557
    0xd050309070e09060403021b031023011805010b040f1206090212031e12060907020703050303070c051b060f0d02070614190605010207090f0e0a0c050102011512060504080706090c06 79
    0x209405d0407131001e12258030249c06030300c00a403a003c40d58594103c000e080483c00d84001c100040c3d000105020b4409804c40103071490303c2199515401403c1c481c0900414003910340d54240b50400c0d010306d0340310078940b1403056070034413521042d01848950f40c4055606540241985103060b403440910385ca039040f04249601510741e402c5000d014040a000b20342401304040800c4549a50f800e04000000340044c10043c2113114008001c40020030410040d0300405680e01c60490b003001e1454410714041ca0f854038280310341c003105000071454a5010556000c03070f01680320b0719103654608030306000034001c224002d003000d41000002c01d1350703180301c0403624058407606134041080c07040e10341e052041d41d01611519005034031030441001040c50300e500560078100146008502a00f9000645241c0850020309a80c1c079042e45108103c10340c0c0900c210003500e8a19064840708526001ca2103500025006008c0d1443d078407200000c007040b200c17804885486a00c180304201e0482c440c200b21440902c24003641011 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 466197050 1250 466195800 466195813
    0x11190e0a05060f09010c170c010506150c0d11010207021302090f2205040f060e1e0d05090d08160606080c12191b060c05010c0306080d050309070e0906040302 69
    0x382c0c1401011940d01c00300c2d040c6041c0c43d00300000011034000645110944004401c110000f4144546030000d099a40c00203001003411304281c410030981c441039216200302c0060400c40d80004401c0411400c0d40e030089400d02404421038060164064410303503c1c001d51045640c800c02d00c504090ba405007222000a0340d40041202c85002071003406482007004150042c190f11a2500d0040c6c0c5801441e4040d10a11342d201901090b036039014195540080070000a0700440b03081d841c8001c030302c10201c29200f4040018802c050307040c203002e4003034030a5034101402030300081c62080c01d10500804444001c0f210b060200c902c25414140440240441e02814086020344102030300c04d884c101e12108500140c640c0a014640d03403040c1d11000241a0120840da5940d10111201d2507400b180d0207000141415100c505840c1054a0180d085495183e915001d00d45402e0051110000c00284042007203a2402c21607920b4441c4840d07145072601581c000300f44a281300080103101140402c00c207000d03c0c829003c40c0c28 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 466198300 1250 466197050 466197059
    0x10e0606040501020a0807080f16060b01030507140702040e060c070302210d1a040f0e0705040e150c132c0c030a09020d05030307030c14070506040611190e0a 69
    0x80d907100703a00c100c03401030707010404c98004100c0c41001001c0d00340c0716038296807034400c0d4030002d410190041040826001c0380c20410005120860144400b040c0c0d0900e402c02051400075809802e215100306c102c210f1080c0800d0300c108645455204152940710340080b031314140381c884000000c2d0b80c4140821401800b881c00646071001042d414000e07035000c6684d016003004d544183c0c040052108070003052141044501002d01a1038620848885d1080c5840209251703410003d40c0e450b211556001c40d0040c3d281c003510003140c040101d2841101007010107400440d84851742107043d140641e091802c1d080540c01400192803048942c0100443c840100040c5a43d0802d0b001424501080b1000b00030051b0400000d9004000b42d8000e510303032440144003a10521160b1a0f07146141c00403980c010200c0ea86040003130f11950042960400039103012042803404045964954a0741c1b005031000b05a1038a5048041e4801521802d413a01042c050390400c00f52041c4140042807884070500d45409140c06400224 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 466199550 1250 466198300 466198309
    0x21206040318030b0c03070309060606080711060f01090203061809060a0501170c011202160c0906080703110f120a030f141806030601050f07060b10030209011b1104020403050303010e06 81
    0x2c0459821070060301242d0b03a1040060f04940c0300420b260704041e074902111001460358031500e0007501c0300303599007500c503d405034019080100014840398158040c0b005c001c221444044054196843c1031030168607510340401043c000060300c885045110422020000c945d41c000072144e1040c2c03042002800180d84e42c201c035003600000c240708034a250700500307042c4e1001d50140d182100e00c0c0441e5140103140c80c50b0410000c02d0b004001500302c0d55090040c1040203840030314065034000d02030b01806090340c20315541d1900c2c0f0760f829440b80c0c04c0c0a0300e42094044200d80d10703c0443c0d100b40c40d200041c0c41030803032185001400c0d41003030405140850703e0b03c00000c2007000148180c5404004920f0100c0030210540c04221251300700130501410844108000162601c245002d00141303032080b00c000c41d02d882e901040001c149844400042094414003600105a0b44040c465100140b60310452081c40c8d640e043c615494643d07a90711f55085400050000100000000214100d41840341c000400b07884000811 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 466200800 1250 466199550 466199597
    0x8160b060904050d0f0203130603060305100e0a0f0c1a070201090f06140f0f0714010b03060403050301120309080d020c0a05060a02030a0f022802040f051b0906070212060403 76
    0x30340302d41c0c40600c4c041071440c05501184030000311401140d0812104c0f9402070003c920036088400065143c01c0200b00b008810880b03d21940200c902c01c5c801000032803112691504842c501515001200b000c94050050300080300018004005601200740500389050681d648040012030004594460004a00a0301c010311400d946503030f500d058401980711014001074008030305095400e1410001c145106404030000d1043c18424180503015204545041d801c40b021004202c0c040d412610810000940c030504507810340d0854012680c04401c241401c46d05804075800c084035030310030031100071070130394001074000c14105003140e98a4945443d4070621665009460705040503070f10502440c1d00c0a8000d24603100b54000707c1c8100c454500240b06d250000701d0a1041d10400216006460700660500b0700414600e117030011030510039420803503204540500742e88071001003244c0125101a8a070b84041c1207807030b0f80780c008082484103030000b8201a21603200742d5045001c03074a11150030b907410410781c464 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 466202050 1250 466200800 466200803
    0x14150d020307120303060e0403020a03080f01080a0201030e0120091002280302150a090c05040b130c1202030f2703090405060a030807110405100503031603050708160b060904 76
    0x141804a1610003004100701e21143c04805041d01c030f2502080541c4900222031240380640d0051074614000d0801500291002e0700c44543c203803d5000610210304001024100c0390b9080c44c00040c880000206035005020a554656410326030260040007800d100c0701600360710104540c1c800c2c9000700100244da030b03640e82c038110348036402d0084848680c0038203269071140035600900507154050aa500e000b002c040f42168107c011564400c1c0307180c103000200c1101d40142005036030800401d03c445001500a55041e0485403c09445c0e4256085080c0b090300c0c2600e20b2160060195264285400c4040e400d24044a411443c00b289491440c001c04042c0c0c3c4032090a511603002c0c6240c00c000c8428800904801444d690300103650041c00800a06208028003160380644115050000040108000d464001d00560f0800f21413010501095401000301c404004a201407500c1c0c0140c0e070718081e203440c000c080015100714004540d620007207203d01c500e0f02c09544180711000d610303640c4000300007081405550 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 466203300 1250 466202050 466202053
    0x10c0509030615270708150105032a0714060a0c08010e0405070b0a02060a0507091805150402071b06090e13020d02090a09021201060819060f14150d0203 67
    0x820883d03044402030b010b4069018000418010f411401c400b20101c07111103003980349401004000107241d0040c2c1d415001504102c859400148280c00207069000c05030045500c1003008150311903000501400031004a405240d60344c60300801e0070100000d840f012200d0409001d04000540b00341418820b0812840194550840036401c100f020100c42c0c1008004540c54841c0b5100815207102c2d00020f004c5101c2e150b40180321034600510501c0a8410140c401014001c003408141305819021100540740c40560070001a0740c1e4944401120303050501c5461608281300140510a1050304501494600d0101101e03800300c603550f810468100c900391107a1419260314001042c10184d14200114655000400c00900840c90f5000152140c1b0300796803240050342da810159085080000d9500141c3c4020f4000300b001d5440c10304041c1e29201c1d040198240d8030076490100c7c003046050740c81400b81d0360720001d0410411686101b03800b8046000e4800c1c03154140940d210540515243c0e50718911241d0180 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 466204550 1250 466203300 466203313
    0x90e03091005072d0210020c0303030a0c030908190f05180105090301150b0c011a0a060f0c0605070936020f0705010f020d050601090e010521011805010c050903 70
    0x110454080e04030820884d101010903e240789202a05100705590303504c48001d0700404446841081060601604ca003401d642012000c03640c5940c0c0401603d601103442c44011800340c403d00c50440040010900042035004041010303044103801c0c0702d42420300e8000c0d440e01c503482c8160501c180d4081c002c13102c106000710200c8003c4015544124090000203a0240000c01c6080c2c0d10801c42c031009940e03070848030100d00045070840d0340319401d0140303140b40d04031150408003820707440000c511851000e014010501112550b00d000c2181300390740a420140d04000200f1040c185410300800098440c8145e90080c1500e022560890301d824100d8840c0381c0e03450100080d00528404003001039040b410806004007000d100b41008a01c0a00030f0882c20b80213a070005980c2e800390384000c4110ad00290445040000c80241072142c002903408150644204640c001c0001c0c00118a407035182480442c40d011650030000314014442c191440340703a901c0d104400a04c203450340300b030044130140134521100d0707419400038 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 466205800 1250 466204550 466204579
    0x61404050616090509090c1f08010509040305090315070e0117041209050a030506010e0705070213090f15140109020a0509010c0f0203010221010801090b071101150b04090e0309 77
    0x407100c0100c80b081400d200821075a90400940550300880b14020641c001000c2c41885103004c3c40b030394840402441c101c0d603c2d041d0740e02c0c0080910303005015490284a181d4003040500d402079060f40c001c058002c0880f5080003200c158070720142d10554030074010490385a128038464bc02401c64a9030701c500941010380c1030303503552074003810020114401e03410700044000114064070760188450140d17000300001e1110707500d020320700010041e008164104001080c08a48016030342c01d80c803400c000d03414140100e20580746041000c03502c0e1010400510b0041d480303076074803070030b240981200a00030710b0028107040780ea036200c01140c26441002000c2c000180c041150894542c05030510420181c003a080d2910f901e941603002c00e089901c507605600040d003144440c1c1c1949100d1030a0786001d07080080092059141e50b03610211103031000f5003403006000303035180c00011800e401d40c08001060a01404810752a6550841228690050244060b08e60619143c1c00c900c0d03c1c000203d520304500546001c1005960 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 466207050 1250 466205800 466205821
    0x70c0311180606161e15090206040308031b0403060501080d03091520070c171207110f03150a0b0405150111030f030108030a030c08060127120501090614040506 70
    0x242103c1680c4c009860054021031169803485d0820728500440d40010074103400c00702d06410441c1c8a0304402410000c0c807500584501d010b03103084070780c00401c484e101c0c0c0701c0f152090059040205a0b0741c0300c0801040000038082c00e6000241242c114600307807040c455030008110140d51070010003800271501d00601c2c04a0b01082e07030001050308420226107880400d0040803007100c0d03010103004d4480342d1121030140500401050007040221051000f02103003230401104a401d4080d00d40003a003404a40e010701400303502d581c1c0100952041c01401e48001c41d8011074000105007064440310345144c074280ca803407524109845000c5c001d81c445d90304541c40c480001c004507080303500d2030014082800180b00c018030303441a10029601900c0e4041c0510703107031b0300700300d5005085800240c00b5008000300981402010b076004880741e120001604004ca1121095620f016150364003540b1030081c4040b20b9881c1c00900006500051420344218401d00c000180c000091401c004142c0b406401a00000c0204185511 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 466208300 1250 466207050 466207057
    0x50f04080a0e1306030606080610260d0801090c0513090507030221330108100b0a0309060b0603100e06011b1212020f07080717070c0311180606 63
    0x2103840d294410680110205914041800704041c40540701c21041c81040044d00070340c0042c05d80c60000706428603040050003070b0040c070303407198600b180c0e8904e5805508a5011b50011015094001133403800000307418010f0210070240314000400e4034000d06070b944070b84140101c903020104801c1c1500718509080726a0018100602910249542008083c2e051000503150b90000d501140801446203000f105407098203c0c0110b01491180300d1000c0030044c40200d82c2c11169000080c030780f040d85540c4078101038012034440d0308034040c45400460200142645900004c00e450711541c8140000d9054401703121440c0000c0d6030b5081d685811060a03c1401c0310310030324690140c01490304480715042c038006100280c1580070300740da81d02da1000ca1507041581080080e403035480c180904500e05004900440c000340240d00c030082868000095481c248200461040491046140e019648200038600004105a030b0b1100300d0305413508040000c01c40c03506c3e409403039100d0100c52000700d0382d50312038042201c4e907403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 466209550 1250 466208300 466208317
    0xa050a0e090145020405270309130b011709070f090902030c01080a02040306060303111903021c020a1506060908010c020604021c052a0d260d0c0918050f0408 69
    0xf444004400035039100d008083c00b5101e50325201284110324122120840b5403801030904641c0208030b44480ba8131424441450a417100c500043d80006000c0100d0b6180280013524030401c040300e05108132100041366450840308010300280e0400c1d0f9500c485000d030f40c0754110180d410303084502ca01c0c000c1e5009858003684440100c0307006260640f80d17900d81c021121550002e030002003071040f4801d2010b504201c1c0b122112640d030b2a0b00340c000c0855034000e40d501105041941a5556034042c003115900801050031140e92041b1108040940740803c0401801144140000202002d130000303440007040c46040345501e200e074090f080d20790301d82d02440000e0344104014182e0700b490841b83c0b07020030000e00c002c10070401d15181c082080402c0140420308070000c05c6213103202d100302d6000d01c000070b035010300d0301844200c0341301200c0e81c4000b01a8000b20240901211901400d007000e07403211388c0c86c1d40200850252517450202c0f03c4201800c1d000102101d204a40121107480100c0c08940812459005400c015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 466210800 1250 466209550 466209671
    0x708070921110a03050a0b0a290f12060115020606010504030b010b030c0d0219030b030d08150307150f020d0e0d060906060503010603080c0105010b031605090a050a0e0901 75
    0x4660380d503170f042e20b0004c1011007a95101203903820702008503054050054407103d9103081030046100080c134400c180d118078000c0340c452086030142030099180c03047c8100442c0b40312030a070344072580d45580c02c1140b00b600500100c01801036a0000e44258010402e0390141c0c0e41064154400740c0c03c000e40368440b54005003422905a50034400714540050600040c200c0294413040041c40da08901c20180035100f00c0b03211680309410622909115030741c8005182d80c0041159050080c240e12240800e062000c1500034145007500800c22111aa410140d8900c1c0303907130280d08403059080001d9003194158900c00c92103500152142c0d40c007011901640280740d065002d8000014138650300c10020b400c40b0a991310442e59107d000c90040d20700882032080705d005003220203a1503e0b6141c43c0c04400141c42c06190b105092100220300d890b0207850f4222458043e10300580400c110980307400c40c00f1407011048482548640c01c16149004a444030400c490840c00c890464003030203c917039007100380406407200e00103422 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 466212050 1250 466210800 466210819
    0x61605040b0315040e071d180d0f17390a090602070e0402060f0d0b031e010e011e0921030212010e010509061215070807092111 56
    0x100500303000118001d8140b4501040d4031043d900c01d100a803003094409100640141408000c4842d001741004070782c40d6502d1000120381c0e5041c002298214039000105442e00c20030500400d2150021030841c010b1100d52100d0308405503422051000900880701c240c0440001201d2658a5102901e41d108103981014006010a900c081c181840e8104d02440000610901c6003013003a0b0360140041405042113a00701c0705689059000310f07409101d03907440016005130000e40807107a03070340c103a0080d1000c2d00010182c0741c00080700c4143c03101e000601e4a60394010b5180c1210000b400e801449a134843c0b00d03014040200011402c0d0b202d1f0000c01c05850191451000816075581c0010070400040c1010030079180103032a000080300c041803c400503041002504140001403180f6524480c11641c0100110b0780c1b08150304e4180500d50400c0000c2c003642d081c4000c01403d00c101190040d403100d10890701a42c3d04008030b0f554030010f85503000000082400b60030890700a5005c102600c8001a6520700502340250303 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 466213300 1250 466212050 466212059
    0x90a27140d0e0a0608010b090108040c0b0a0c02180618060d020909061602071406251104180b1f1802040306050106030c0e040b01023301080f06160504 66
    0x600651409070000260350140368640c0f4500441588007820407450410031940c144075501c2403d00c40d8680c145d051003012000201084040c1e01400c016105144180d038860f1041c803805443c41540040c00c80c896882010840e021505c2440290311500000f00040d88040c69000112030440c0050100b41c1c0014403002210003503226542014064147c030402000145001c2d114848803d810301107407001c6402c440001c2151040e100400c1030300c103c0403540308e41c0d0380c81c54900860310b40c110858880c04048900344250180a02880029803250003030b5811321690441081480d000e1400c200001c0c5400d061f58081072403400007400900280307180300c480e08003a5032074035009400a00001210208242c0000d41802002020302503a40144000d04081c081001030382000b4054000981c281401a0354072040503065a1080100e04001801c28080700c280b07032144046240c01000494400841110700c000018a8510004040f940c031a01b440c0506100c2d2520008802c3c402d99050301c10081103000c1c4070205 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 466214550 1250 466213300 466213303
    0xa031d06130204410402090c0901090906080307030210020301080304120c080a051b010e090c1e0406050706050c070c030b1e0a021206012d1206060806090a2714 70
    0x602c01c1c10152440000134100903c460141c0501d000da404541c07185401c3c480140c460f034800640203450a0340040e140d084650041310709070010b5101c0c101c0141070480000d1400d13800300c020701c8018003960980d001801034901442c2688002e01c184022680100401c1203a00c2d034010342107803030380d1141c80b00007c495a075840b540c1c513010381e4081c2074420b50407076140304204918011601485d08000e083c40d0070341d4200000051103020004080300c6480c0d9001030546030220113a06145055019000724a4541c1d481e403000034640d030489001142c1980c6007901180003d04c0340300c00c3c0c509140e80701025903201c90941d47d500c00558030190000c032030368030001c01101912054181403881500e145100684600140d810341a8601c800303001c0605224400b044603100c0c82c25080c0e00d1400d2460480381400007180e0300e004031000a141d820a11120789015400302c0c04681c4111500d006090843e10107480e138030340c0c514101c00c81c2c462807021142608a6481c4240c030052500080300410300800024150104205840c2d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 466215800 1250 466214550 466214591
    0x30314130503160608160e0108090109060e070f0b09030a0809030312070507060b090618060a03050f0604300c0804030b0f01170c0102030403060e070503030a050a031d06130204 77
    0x100f111403d10070140945940030031030650200304000c4951601d01052800303410b00d059695a181001803403400543d615000b5000550303100d901071010480b10303429501d4961100d056000d010014540e04400041a440300b600340d4442c0c50700100071300032000c01c5e85e81d00c8035180d0080b84015010300040c4541c04003c648040300c0b0744a002c10b40c0300c0d940ea4001519204046440300c50802c4d00c00d1220b9001d021482d240d82c4500141141c5800c10010644c85074000140b00900d90340c00203015214081030255040c0000ca940c50040348621092885030580c800004000c0070060401d0000448a039040781c0301c140300d2204c1400c503901a010031440c241d102c1e00c8030703100b40b0011a64246030a003082e0040250114000d00103070003104071006400c1c00866600000e4486c07190b40701c081d1800b03891340d0700e038401c0c034900748a0740c0001d00e00101200d5071030400c03145c0607000303412034024400420302d08000e24ac1241d03140441061400001c0c4090001036490402c0c0360941060214282d8215907a0030b8101c60250500101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 466217050 1250 466215800 466215823
    0x1120f0c082104030b060103410708060904121707020c0901080106050a0b03040606090e06040c050f01050a050c0703201c0807260d0b120106030314130503 68
    0x25002d0003401ca00401c4620310b40e11040c40c0031603001c000c20400b0035281d500b030ba07070030040034600420707186140a09a001c0100509160021600301380050219031800d050504082910380002c0701203665440d010f541000d01102c2140d0080d0f034100021740010004003403d004c54005080244084500720500d803020f20040b00c400015900101207a0000c2c075100e1030560062802100a008007401c04c1d0120f00d0380c140903c80c141e821200403021408103c030640000b00544135205041007144200c0040c25074510341910151000c0400e03003004182828240006020800182c45031880c1034841c5204481c0f0f58081c0c0da81200c41d000e00c241c003000041c612a200c1b04101ea0780440c61444004450030030000140283e83c011100e01040205000030302c0e144280c0d0034817500705103080d10b1140b80e500301440d0075041e4080d89810b6440003a40421401582d44603603a0300c602900c404444090000030301d0300b00c564900005d004142948041c119041d550001030618041c28601c0da0302c019554000304e4684045c4282 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 466218300 1250 466217050 466217053
    0x70609060206090c0f010309060b040c050306090f0f0f0a15030803161d0402030403090e010902030103030806040c2a0b0109021801021207032607020601050913030801120f0c08 77
    0x1810044141d0402ca10390300000800090040c00d0201d10008580344203052a4505040c0c81d52035040510919a2100501b485c4c054810b10521160000040456000300e590900c10034982d008a10700c00d00385a074541c4680f40b9440c01003d81d4441118094002c00700900c60040ca6860303142c1300a04c01d0812940c00020b6200380a5a610390402d10300198020305540d0b01c2d8070410407102c9105041804d429905030403800113681c0142c5d0303070300e40e03080c200c401400075000f2181e000104800014070148643c02903040724001d0341d4881e02a11654204015102c0f142420800620000c140800403240c4a10500780a0060b010701d170000c02c0559940780e9150800da108410b501e0b40803c104084000314007900a100200348054103600e0940301c091801d0340145940542000321954011002040c4107003040202c81609103101950328080300c1c0295122003d00886000e89603402c0410300d17a0401803500a241c5a054840c2a950381c02d046c0c460304030484008080c0c40c1e8000b8602a00080f81d0745a0801001d020240d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 466219550 1250 466218300 466218317
    0x30d021606180c060c081b0304080304080a03090501050f090f13090f17030c040303050a0302071709010f03050606040e062106071e0e0108090a02100e010810060207260706 75
    0x1003d0b21004290303401601400010703003030000011013520485088100303c200e110318100391303141c406285000c1e940002225200c000703400b050f000400901c600102c0e1081d03807440c1c03001da103070401191903014900d0811030f40b41013805040c0484c5865124184116005020103404084208402060391a401000e0383c0e41d1017640c06a10602440703a0303140d0809442e60240615500305031102805d41e116074480581000300120300b00220700e1080d0129661545c001c808000c1800716002904020340c04440c6140c0450000252808064000d000d0140f041a0080200741050b00d850008800c0400003000c559200303034140149900c1f140041b08500140303218100506d246e01e4a1007010340191142c0c070382c50401c000c41a071580303074865000c00d94641520003842c219a250300c4480c0d100d031a0555005009520501560507115115401414900c20003030903a111030a90b22344540c005d490303450301d01030140107070416070003401118801841c80040d441301401c030002407036041e40098240502e42d007107080040c0040 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 466220800 1250 466219550 466219553
    0x311150a05040302180c070f0c15110d09030c12080f031017013c0c0f020c0d0b0f0403110f0102190e10080a0e160510020d02030d02160618 61
    0x501c400c5c26628171040111418a00003204082c0550b030001001d840045e03200c007080181d017074581e43c0200a1407002c1910000350020242019044100615891180d916004000c900c54a141e500b2690001c40f00350300c16050040300004856111802e170382c51041040901c4e04104030000075840341c60001c1d50b0800107801d07c0c81d40441c007051403412008582c1032900100351403003008a00c0075201d100035600141c00e01e030307130b0051400c03081d2105042402c5860841d070720704510340240b80303416080c001d030f82a00d91030201a020081d03021401440903216044142c00200c2003030040d420b0030b4005000c0c2c108141428202c0302420301e0154a00b45001c066500400c008544544840140c2c41d40034507401d000036500480c0303011800301030b100e0302c0341401c012030381c008141c452038694003041c0032540d5602510400410440324000a201030b2188a006452442200e80e8481c40800c071124a0a042c1c0e0203549002c0c50b00000d84007a410169a1501b036003407640b00100020344030311810841c0d200684500c00c800045 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 466222050 1250 466220800 466220809
    0xb070212030a2c040e01050106020706050a0903140f0304030c050102060112240f0e0105060306070203070308010e10090903081b03270319200312010311150a05040302 73
    0x10000c940380640c01800741c0415243c00c0180340940059105040c200089407407030391581005070780f10315500a4a484131883c2000d5064005a045c0c0b00360303400302d840c400e039502d500f2242403103142c0741300c00000d40440d000d00002e8410101e01071000b4809003255807002c40505d4040c00c5a01ca0350084400c100c002008001c1542c041c0309490041442c1204080300503a60b40b5070130311100110705078007640441c5c00e0100400100039803100f085601a19410050300d501c40042c00d0007041c0c1520007a100e0301c10781000410382c51000007200c00281c0e0655502d540d1364a0110b01c282c20181c054035a88401c0001e01000c640030b05144a000c1c00030b400790380c941102c1d0070454812482012070700c045c01c0403500704008008483c4103d00c0070410402c5240815400c100b1800790b01c900b980103030440c948000a00948075140d050380700080c407407207007600d240307003003a280210420031360302d1003550103e1a410b4954001000422801c00200e500380b03001800301484a2a2105c490700c580d8001010100450350104052055080 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 466223300 1250 466222050 466222069
    0x313090b0102030307050d151e0e0606090604060f14031608090106030b13020609060c010b011106100e04020619050d11030f010909020a03081c1815020a1103040b0702 73
    0x60030b001441c51400c0c2070100801d1032141c1c503031001c00252940201d44030300004203d210018001c10700f000d0002c00403a4030000d08408603200d888004400d4401044417813a280040b07451216000b0000b603e003a15014090303c544800319800c800b40404203c1050b542505030006500c1521035802083e4040100100a0400d10700038048205d02d80c9080020310000f5100710f45030381c101f88240d10f1210541400d200280e1948100003000da0042c0300400e440c884020b054200441c01072007600d0340071441800d80c0c000e40e6140d0040390910703410070082c8010441070044e4000160041d001a0050749442c0340d018489181500d41c828003400a1400aa02241c0400601c83c80d01d0300303001102c1c00b07032a40c100050815007650060241c04032040d0307984200f40856640340c1400d002141e214a500351150010342940100b401202c00045215040416104007001188011000d065100707d912051030510300d182c1c0000d40080703180304144845608150104a4104003a10040001640d9950b81307403640c0c8103224200a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 466224550 1250 466223300 466223321
    0xd020901030606260a06180c0f080c030705090418050c09070c21090302310c0f0e010e03070314100c23040e0403030f0b010801080c04021b031309 64
    0x4800951544200031000f56920b444a5040c0c0c061080d00c0e1000080003d010507441f001805c0071160035510420115001210400801d84a5545008659401f6264040129040c034540700c4c08100003200e0b40d02407070152032041e00185c0b0010310200540324031410208070000946066000c05018409403414a01043d4000c0701890061030314245980e41b4014642100da1040141d24100c2030007090394440c0c11032400035500144540550107c42d00e6104c0007085550403108460951803031002c1e041241e000f1014800075a0399081c20070404c403403081740c041400240e051b041000070650181c1c030340d030304001c0c0c00d002d1030044c0b01e460150244500010b2600d810811018006805c09006041d2503030812074045a4000741c42d241c100032105610020704610564001c2490201d400e07050100340350f4507510032056010701d402c082003145050801954080824840c041c1c89502c000f004244a040c25009030281403105401100070b00312b060341d01030960300080c0c0103001400c0001820040220710380220801d04 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 466225800 1250 466224550 466224557
    0xa0b0c0709050408070c17010c0c0c09020d151814150d05030705100902010e0306010b090f030a150e0d0906120c0e0307091b030b090a09170d020901030606 68
    0x6261941a40d11011244200e031191503603580060140002c0a0856820079402902c02480c0f54460082c0c40000c103501160440030b610b04440e030707883c2c3d5008113110a41c4030380103004210304038502041800a548001c01d070384c02c20707522449026880880503800b80050200c400008407a507008200900c100c23051841840200150701081c0025445021000e5000070f00a07130b64103603101a6401c00e58910300c0780000080c6544078040c0d14500010320381e0b020f418070300d100766151120072051000301950391500307004030303000390384104036501c1d5621340803031810186400074040da6001141901e8640440308012440b81c000c94984800207905d0341f01b80140302402e003242c10720304041070610384014500d580303440120319502c2d83d0b440da01c0e019501030074a55a01001c01812640401d07110008100544034040785100300100780740300141c502d400380c000c201980c0340160600045980e15640f4402820303a44d07500b55500b03110441840d8013485104d00904035240c4075400542d41e50180300005040b60856400324042 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 466227050 1250 466225800 466225807
    0x90609030228080f07080f160c09020c0606061c0207110f09070206190626100605063004030503010302030c090105060304121812060b04230a060b0c06060a0b 69
    0xb5003c9820fa13102c0c15148500241c88034114030340280c0c584689004210100390101d0b801c1221000380c0040c1d45140e02c81c1458038003040d43c540000b401e902a00c407544c081d5800a400162040c200032000d40030040d41c0c02c00d4004000d0342110a00c0807640324900aa07640b0b401c082080c0c200d800d021070040810301c1e041e94116468602000025140c03c0003903e440743d8021001080c0006c40c44540000c8043c110882d801c218004c80c4098607079050b1149014480c85008021110400e10901d1080c1c8085490107081541f400e00c060044480401510b4680c0f442d1841c5108147c3c00040704c1551188140d21a844e01a96075056004041c40e216035036031802d10a1080c0b030010301550f16043c00b0b5a81069022a40110f0850034030380c15104107019001502c0500b51081c030015507000010000c41c3e0841c001c0303004011114000050005440810340307003812109006d07107003034040f403d140b866561201e4803a80004405840b50807045d07143c0d0001d540400b07640d01220500c90f051401e071010303c00800410322180d19 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 466228300 1250 466227050 466227053
    0xa0c09050d060f09021c14210306040212130c080a020a0605090f030d210506030304060c0c050d0303020a080f060f0f0411030a092a0b0d090609030228 66
    0x480300409500510060b203d810300c0b01e0009160308121412a40100710b41b4100000007904003920b840b0190aa4081408500c40311311a140490000b2480302d00500c2c40002c408405c210794255800a803140b81c105500700108481c04503c011020300072014860117106250441c100103429030160782001c0c0381504810346110050741da00001c8400c40350ba90070402c0d1907800c1c40c000201081c2c24621800d403d406043da2a82d040365100c956618205609100820101407001201c0c00726901120038030342682c01080140406400380d901204418401d6503030440054582e000304040b4444100220003103500031a803440c20682065800381c5c407810100141d00d030b52030410005020030440005a900074030203001c1004c070b5500c40c1d40140200f141101e5840750b8034100300030b106c0b00400130b25030103a95695140c49410078a00301480c440c3d01d00c0c800144607802c40da080003800c420a80c0079000150415964032103031000600c6c54025908501e0080d00500015100d0386485029045900c80308001001080035030b00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 466229550 1250 466228300 466228309
    0x8010b1504061b110904060b0406080c0f09040c0f0b040609140109090e10021605010606080f060405061807090303031802010917070b0c030a030b04090b0a0b130606080a0c0905 77
    0x4900c030015021600044450421851380d550241c506900528031804100074008150428080103509507010010344d0742d1001901e84030142d4000241e400326171000005a58a03041a440c0c0d0000e019407207424002d82d031000c040411030500c3e404002c40b0300c400700d1304001498129000d00010a44081c030000301600301400200b070742c03540e80900d07401555281d5642600400c2003000b142c986861400441d610b5140654104408800180403a00c80d801c00c030b07001c5030a42c03007184c0e403d02418200b00000510707240d0b002003001078440104031a03046800850844c003041001c038080c902984094803482d01503030039400c006040d110940141c800700384039025020300503640b1035441021101c800420351000000d440040e42028115845a05058000304500d8030006003c402480340b841245c4080096036400000d1106903114100f000e070040020500060055205810640004400a0107030b0f1004228100141c21907071107400c201c000512450801c01c03140c9851240384210b15850400314006441c050015 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 466230800 1250 466229550 466229567
    0x6060906010c030e1302190503150a03170319050f090c0f01051611030304180e1f0209030f12071a13200d0308041b08030301150e04050108010b150406 66
    0x16400b03130700c219500c0c480c0011680c6c1078030881c1c00134004078007805401c9000200b56400940b002c1c418468000d510b241031389007038681c02046070381c0500c41c0410030175003d02c08045600020200040350b00010442d807044170b100c0c03203031900c910300307034030109060781042340810740b4040401c02814003504041c61081c1d04c0340c5e04107041d90b070a900409080c015480c4517140210851051508a907010f20000c180410404181d041170710808014006c02c006c2c008004243c2d0303940b014000c400b50050311440100e00580c41054009001d5014094110382c046140c0b00c0c0c12620b41240300140b484400c1c0b0200300107041003101a076400100850b10702080310b07070a0544c180c01d5003c80b218001000c42c0c0b021010b555020a0b405c140400308840184074001d50181800c0142450b0002c503411903d0503d8074180707500a4440e4001f000a0f10300c80c4005604680c02c1c0040d201006819042c0801132000c044240800ca550700c2c010346019110400001c0354078030401080c0003100200c2d07011403c4040050005009255100000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 466232050 1250 466230800 466230827
    0x12110301150203070f08040503060705030c071e02090f06040c03060e0a15030f0b01062a1203060f0f03020f0603130b130605040302070807060f023c06060906010c03 72
    0x1071000401018800b42e1031482400702c01446605140043c0c404e020701c02d80a00704813075080d0706440441d90b8a01080300c2d184412910038080369014495072010802d11101e41c0c030108519000c1c0c0300d240c901c540004031040c2044503000d20340c07000d410800200b401c0034002d1140000113420180581c508094044c91501c5004140e0180203590f2584d039114580318080500c000c40d0004480407039522141040314001c00e0901410001c03d501d5001d11a2003c01c2c80c0380139074041c03113900304e2400d0005195074181d1245200ca422104158481c60040348081c0550301c4000140302c4203000441e69451841804014042c078604d582c40340700b007032081001c0b40c62004043c040840d40449207107031903901d05883c5160180c00345005450780e4609010030003050340004a140c01c0c0d4210402300ca200d10342e220f070308440816401d48004016041140b0140c050030050290f07201c0c0190741d640304640d407200a0134041401c80a5030503107419a22520034070000b4282440540d40100007880e102c40c8501158602504058034000c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 466233300 1250 466232050 466232069
    0x30705191e0b040b09010905010807051c020c031303050f030702090f0c0706090303050f0105060a0f18120b01090b09010f060c140304061115010311010507050109061b12110301 77
    0x96410755080840500e03001d080c40400c501e440c2e0792111401503c58000052082c04501c0e500c201141940c010385529100e0003080c0da4003460312070401300c000e5290754118030000505409011400c00d00000b4005000d10796800307545241e01038514103040745409000303001940c1d10b800030800f0401503120a1410795101e1104207600240f511812070060030352060500140c40c15140c82c03000c02c05c243c3d0540000e80140d0260841002698a07130302045820b2080031003081c0440c940388083c00205026800310480c0071032101c0303660000d980d52001024a801a03910403540104018014012882140708500d45100265010710311981440101038401d1060700850042c002d02403041e500b00940709100170100c85001055a4039590381742406402d49105000354011030280c0002424603a680321040382c12a42c2100c0b0104400b100032005650035401840c00750303115500e510540000c52054003d007005c81101d041d43d00040c103241600107080000e6200b00042a604241c0003080001c001d00030349054588801 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 466234550 1250 466233300 466233329
    0x90306040f0f02060a0c1b06020303150f1002070f080615060c2d0705011d04050414010e0d080c0c060a11040302040e070303030545010e0c03070519 65
    0x414034480032281200a41c813032000180301d0811036120b8801c1e402e00307114507180c280001060070b180c5c10a84090095100690080c000103078000c0f0a1140403030001406042520710352504404141c0d00d2404a000c60007682c40790104000d452920f0220340014a1000068055400c0142e0310100d0002c04443c21880b58102182c94800d9103018083c001c1204040c0d01d88151091404082c0015604500031810880c002c800d07002550354011903003110002103000701d51000c070701d041040000504001c2c1c403d440c080110129203841c01d400b480780c03100a810940c000d060340020f0007801800c103080109905510030013408801134200d800500075810006690020402c5200b41a4a08a40c043d036480a0b500c28213081e1800d031920360100c0d0080a5038000d90302403180c0e1303985201d03a0303051680c00e240304c0c04903c1d02840c00c424a0410040c2d11950340c03054004000e0000c002034181c1d429109110402c00a0340c001c1d40d003030340040ca800c1040030b0003040c0695080c489060020550300e07007a00180700b0b05100c02c5020 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 466235800 1250 466234550 466234553
    0x6010605040b031b0a0e040c0f0c0605090c2106100b030a0b0f1315050f0904060519050f091c02100902030102161505060402040e0402040c0c2312090306040f 69
    0x200c4c0203110410b124045407540090040201004800034000d40150b1a040002c5504c45c4610603000b0404410340701c0812141d590340d00d08000f004010200b0240303002d038041e0a000f0f55207e18070514020300c0062061070b10301142039840e0902c00050300c0c0716082d1552603000c1000c8854082542d07808445480c5c0022800c80f03800c040b410ba80c1254125591110304404892580e14240d40300181c6c41d000c02c680700001944034414003403000100c003030301c130b0380b019070480060300040c000d410003540940c4280102e5061201c00052409584040d00c508082594140c2045011402040441e0b9a801c00d000c601c0581c46000c0d42c040c2d00e8030348005034a030390706131100d51520a40d102501120641d0b05048200704030301c109400d1041146014042c0e03020002d04000c0443c1041c64940281c406458000e07881d02c0e0ba0b91110b5007004010494442003405208195460801240009015485144414186010101d12030001b0b90800e0742490000f480000c0038800381c403450b200065201c0e8841c4d4002c0981c081c2d11110b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 466237050 1250 466235800 466235821
    0x2010804050a0b1906050604030c1211060d02070b0703110a0311040f170d02010e070b16170d0b0a12030f0513061806080702150604020f070501020304110306010605040b03 75
    0x10b010010301100f04070014000c48a892a80e200c1c50b150b07504070100040c0303460ba0200940c620030f9200141006503d484140421640c00c0140c00c510b900c05d143c7d00004840040110710160014000c107e00241e0200c1c000d8103002c0a1104c090f070280a03840c0400c00d440c85860904150b000740700003034003056640c0000d2000001c190089401912a001c0000c070b41f81e5603009107050721080c1035038035040c0e8040d50b103100c5400c50050240054100711030020300445410909005000d404c07111643c4002c00c1c841c00a1004109100c0d903060307030316009032035403640c0d80402084002540c0000c4d0084e8002c14142c0c4040205590980742c2142c1c4590520b8200c44141410400f100c80b405240c0e100f401800c01d030b8900203586a04420700c4600001c40d10f510000040d40d40109803100c00084541e00c0168200941e682030610364000d660741d0041c070061005007411600e01620103613800420f0110b43c03581d400030070320043c80680c070b601102c1980114001c14030ba40c1411802030840c0a6032003020083c4001102040c55101c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 466238300 1250 466237050 466237063
    0x20702180c070209190608030a0804150b10030c0206010605070f06020304020105090604060905190303081803040f0e010e010b0901050a0804050a060e0a0210030c0e06070203010e060c03150406120201080405 90
    0x80040020200381000b52203120350005c1580440199407500c0800124210080705407181000c940c0c0b501020313a03a4030b868108400d00311041031b040c0c0c0703540e4042c404411383d6409075001040d18980d80019207246582006880c0110607040301050100500c51030001034034a81c107020301190b222602507201d4a85200503581c41c055003504980c440804070b40480d0341c940c0b0682e01c0f401c54070203c5190340c03030488212030402405040c3c040580011100c20004510340d142420f00483c0500040403a86000c1e964140e02c18403105a0300403040e00855a801004050056483c541c00b40801007490f030720308101900080c01074820500b0030020f0210010008043c850180007031460550011400d00c140c0490000003074980750b010a04a00c2416086104599144a8032170074501440c0c5c1c1c0c0780d60345440081c1c01040f03840d40000030102e0740366480b039040301d680b520280403480c010011051140d80302d0070003242038003d20801800050280d0300d04034003000040000603640d01c3d0182c0a0038540d41d9034030340303050540c103044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 466239550 1250 466238300 466238303
    0xe09090c060d0b060309030705120f120402030f070801020d0b1801060c0c12080406020d03050f061201020f04060e010906020d0509060306061306020c030d0314010306023f0a020702180c07 82
    0x31004000c00010f074402100070682c05105006031003d8441002b0b840c01140143d401003100414240180301140e0442401c0c5a040340c001000c07607003041c0d0311805140c604141c58000000a94011459004100300c07802190f0318000c0840d060180000320030241080b00030148903200800103031800d84c0041c00403059540d0064124981c0a0019045500b404109584640f0501005225402c40044064070910400b8015040c0340179240c203688030b0b00c040042d124a0b140441402d55820400301100c000190300410041009071a8000c100411100250030146190b001d01c2c155041101e4100071168080d00b1030390305100c200d803284d03101e44844011801c02d009055108021040d09003001c240726130000b485a108800480c2101e4055403000d0f0704405a5590040e0540c04800100040c030004005802a0030189002003400f403069101040d1071820003000c0c4020481300102500251000c80c000c4010359011550407415883d00c415507000c154001c144c0c2c3c2d21078400001000100d50440d00c0c203030440710f099 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 466240800 1250 466239550 466239559
    0x3030a0b01211e05100501031a0306090d11070b0d0906141504060914180109020a1401120203150f03012c060a050103030507080a02010b0a090c0e09090c060d0b 70
    0xc1a02c031103510010069109500145408a504101c18500500807144100090b81107550928074010055000c2c2c201e030245000b00e209042c10052450f01e04100c02c0d40b040d4028001441000552000601140c2081084500b40d4100078000c0c804500740c141200e1320076000100000b10780006003800001040207000b60603902100100303104190f8445500c072460b02c04120341c00c01c101071741c4a6003101140c0e200041182c69504840016418000ca0798101856003241800841c150340c481e0b001480d91151508002c00c550554215500c003564800c42d03110504d441040b0851071814410b003041d80164000308030a10600320310700e8400d03090f03e080d040203511480c44100c413240503520b0030f814400b08018000942c4948101d400165030345145000b00c1d03040f1b0303406403545032034414940c0b81d0950a6026059040030356480ba003001500b84ca4103032409006181900e800110880176140c020f040e00c0d00c0b07449143c851310545041c0941030002151655210b40103d403110703038070080680e1442c00340019031480c6070720 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 466242050 1250 466240800 466240847
    0x415060f0504180f0605010333050402032d01030b27060c0a0e0a06080f0a0b10050a020f0d050a120e030c030405012a020f060d050a0b010e0f0303030a0b01 68
    0x1400305a030408491490340004c148081d644500c011803c8410740354820800500c286000301e00450282000c00034401100c2491506584800115090740c1c02501c1004c0c1c014500000d009007000401d542001702c1103515030003c083c0d4510b8131240c0c100d03040640b4a00700c0d18501a00c80c800815050880201c00602d40180c400b14036155032203401d903400240580d404240c5100d82c20345d0707030702e000741c0c581050724002d4540710401c0e00c52003003e107481c8030020001c2002e40d03620103105030607541d0180460419411541e41503550f81c00105c0c000d040c80c2142000fa02c071a0b1090710101400d5070844141c6104038030368507200501c4803050f88003c0c05071803a8619081103000000309c610101801200a00944601303896003100000b0391f05803030014183c080c1000b020303101c0f20712000c030040c503064403520a01c1000030315890501c0c04100c1c510307044030070944000d04e060703503a6540f41c0d040f0758110b140d207219084100e484451031924030001ca501d070301c4028180036007a5034800c20040580e002b000c6007048a07203c2c500a48a = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 466243300 1250 466242050 466242089
    0xa0b0307060216061e05030711030309010207061a0904020f0d1b03120f09090209010504090f06090c0e090c0c01090804061d1c0605061315050f0415060f0504 69
    0x1110083c80d40b43c1011140c40e80d90101e842400ba14400d040503402c00030302400490390090407503840d0000b500c902c04225220741100d208007400c002840c007545441000580d00c1d540b500c0c07c10200d076a00c0a290303400d10241e07145480c8958500c0342c038075841034050740e1281d6207084020000d80d088000a50042c20b2405546001010035084500c0b0300980780304a858450800180d01f0590300d8240c2c0182c08030020f4040300040c0081d00b0300341c000c1d008601c018103000e410140c035100703000300340c84001d422101c0c61503071440c04100d500d44e40d01403444c00b80b8250401084580800700800c1b43c4403402454440407440020380b03002d903a00254880400d660704900441d44554a5400c003c114200001902c0c02c880980d20301e070b8419203007035030300044185204031501d03565122907515030015020041280e68000420700369402441c10a01440560700004d26229640d1030a110030800d000018801143c041e0346407800c0e90624491001c18401a1303502c5041100110143c0d84040325144581d030010310141941088204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 466244550 1250 466243300 466243303
    0x19060e1605041503020d030c02150d050a0b100c02010305061f11010509070e0621010612020901090209061e0c0d091d0702100c030612120f0c0f020105030a0b03070602 73
    0x40035207904403814031211a0001e42d030300f5041403901020394850480e2242800183c02001142042807010b00a03486210892000f80c807150818610990440c0d1948100b01c20001d0703502c12802c00e00c0048940340d0841c88200402000202c12110083c14151350f180070074102c0e80d0302c0c0261707000708031030740b0300c56a011011074001014013403c0f8001e05036941c20200441c610010200e2174000359101120315040d0b950326202000408001c0d589440400d0034400c406984449083c003e41c0040e241d15011401d0903100b0f8410701c4028941640071101c41c502c1400300283d9640e601084610308011a54069820240c0301c4010030b8900ca0500e0080340c0f8426144000030464011010300100e4560a20200350004104020b00c50355004840c00401030f00550700442120b0a00c1e401918402c0840c600000c2c0f854480304406200408044241d420300b0384050000d00300b82d84030044008000840c548400d8000190b81e0351020906c2200d0000d041c80b50200009070303140e0450b4010440c203480107040303800c01a542c1d140170303 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 466245800 1250 466244550 466244593
    0x103030e0a08060106080a0506010c050a0c180b090a0c1e030f0513110603071b0605090c03030f040320060d06060306060315150e090103051b0a0819060e 67
    0x4500070041114002100030703022903200e04844143c3c0b103045155544501c48401040010400303414001c01e0600480422002c11041e54181c0c45407132492000e500b00460728410228840c0b40316245810b1118811047c2c0b2450515a080480003801140c0c0c41609042601e03c10085e140799031035a0198801c0240300c5505400c0038683d840700003401c10590b16203044c80071041091020140580c0720300c4c0700070034842c1859001541d000307a0b42c1c17414140000040068603124001c1c50001e44507141c44005000c001c2800b0700038510001011001185001c000180b2542035005922001d400c1d0071036951034403030350348804c0881103d40c000204055910407a20610b24028402c40c09036100003441c0840108299004e4880d02c4c00140b9011200ca080f41c1c544058682c04484202c4050100b01007150950b41c1d5032504042113018501c543c01a16281d1182d00c2051903514031440c4140c070a8803004402c0082e1440030030644800301400108110045250030100c005d414a9641c5650a10441d00781d046440b4400320349 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 466247050 1250 466245800 466245827
    0x4060b040b060a08040c170312060102060f0a050910020d0e06010b091c05070312050712170103060507020f1207060b0607122a0c0302030c0103290a0905010303 70
    0x41090a41910a01003241e0450406980029041042d140c20900030502c10394440d10441000a2440d2a0006040620700c09507043d003140e88007040d1452880c040080740c41e4040f5081c4006e0000d841c1131501e804680001a240000e09640ca4000c0b07520f41c9000e000f680f0421012003c290b64030700c0760350501d030010710319100b1422940c0281800464501240f808075405020007c0150002520b511480d080038202c2400880b411311400d000040054032440440c190500c2513100c03141c1340d551504100c003c0344982c0702d645003000b000e0b21211014606c01d88541c0d0561b03420820010385075032050001d92420b64100d81c00c02591140c411219404580f800040c500c01d4402c240512801242c0002c3c03061500071110024116100c00b4850307c010342c4103100e004a0468280f02007440440c0d04c1d03c1c900c518410443c001c1e42c0ca0480c121050003542000c02081104040c2843c00308445420341c003041d118040c20b03081d05840c003000401c1c21120380d580c0700199030151580c0c4604110075603691030080e1900506185 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 466248300 1250 466247050 466247063
    0xd08010905150609010315030204150f06050301083f030a1103130b1b18041805250302060309010219090b03010303050306041805010f1116110102070b1204 68
    0x3034007030102d8100030000000203041c0c241044600c2c0015400303850844403500400409034000009692a4000d180c96246034a40c00c041290620084010174901500004180b2100b080108058080040c000c111141028002d074200ca0070340b02c021610f640400c10404517a900e8210340c036600c4ca04100114096550325208021010212080c0e85a600044840340460181c0d4481c0001040c00b01e071015500051581800c940810718414000d00341c0c1060041a041c030b0f81c01d8641e40f0040c00c081c8074a81d4009082205100015101d07a555940c88001683d80c1343c1c2c00341c549142142d80003800e640c000c040c40d40141100e480c0e11b0220032040c002c6d0002c1c64031203100c8005003d6240c90318010060030099503101c0c4000d03451a07095480540d003e030b00140001d60020766034000c10341040300e40300989240a00c030340e0001c60300c00354030040f0400352000b107241c5610b0b411040081d0b0051130210102e04070a02d070701400c40c0404002810050703007081810b0b803103007000500004811000400444d40144031b40d01c95807 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 466249550 1250 466248300 466248311
    0x6010e3619020310022b0b010207050a030206090f0f031213060503040c0603050603070909050f070e01140f0f03190b0a0203192406021b030102120105060f0c0d080109 73
    0x40c000004508a04020303403da009580340010404c283c1d0000c0c03034180d075003035000d02d60302c485224940900c8600c1d207415a102c80e91500048500e6034140070a00003040200c515944d20b904607000030340f4a101e0050010303c91034040490745003075203c0c0140c407840b5007402000d440d402c84013104050141da0098111848a500d040000724245000314240c0340070342e40190380c0b65000f50405a00350020a40540200d030306208100c800a2a44d13942c0c01260200d51185020b0100420350080b080d240c400a80c200c5030115440c10014400c0100f000c424000f28002200d0302c0a0041116001c1541c030740d0b80442007074140c080c000c40d07102c0000d2000c1d812402e062041c2080b01282d51070f10040f108031702065441c28a26207241010504841d060b41040100844089c04501007045414100c80c44640300e90003000540c01070700241805040d10030700c010054806400961030100704068002d8031040c14044d440c030030940414107008003c400c00c183c86c540c00a440449081e0310317050501405ca10024401c0343c03112401e06 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 466250800 1250 466249550 466249573
    0x4111614060c0304080c0c2d0907020d031a09130c080c100804020117010315240306152c1303080c09011101050c040617010806010e36 59
    0x801c54403450000c926603003551596070b1516078540c400b20740307050b00380309124040045650b108904801881108403039410003848540484d40309503203118161241200c03004100c0060313000324081c4402d81c2c161a00140e0503000c001541c410806400c04681c01191001c1040a549580f07901140c0081c011104a100c1c0c9a40d056003e50303030b07000841000d410480c8142040d102c00d000e08000e80e0401d1050401c100e600c0c090000043c03c02400340d0060b184100c0070703010620b04804600c19005480c101101d501e450070541d0111a81908580c40000c204039a211080543c245841d101070700138142a50f28804500c151b4030646c50510700d8490100c00341210240401c0441c40031403d51005194540c0325032040303589001512000d50080303a4410b050200c0c84480c41d425000a101e40c62055113999025030f150f41c2000001807010031080b4120a503e040480144041c01c80051a64115207080f500942680d8400006810310344002ca400e03031203801d0300c40c0140e030100c44401c0c1600415840c1003c0b2240000319 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 466252050 1250 466250800 466250803
    0xf0f1104030212070609260f0615121209010e03100507080c040503100f0b040c030e070807030c090902010203120702060402180112020603090f0604030c05010f050601050a050904111614 81
    0x940c0b144401140b83d40c06d003006401c034402040d100d00454014025828120180418100343c82c003400c12603030b03410040800034019045070088843c440c007038451000c8001010354003580c2d040c202d40e0b8500c04c0b4601080200c440da00c20314200440c42b40c05400c1d90481492046600040e000945111010540260000d03a0701c104860130340d0b040f074100500405401000042400040280b152000b070915200c40071080703130362200d0003820608040c036503001412000d4000c0050411203d82c1040486401040d01040030580c1c551110041d41d80321080020b0b025003d10060345148a09582c00207a000d24004204281d40c0216103948101e00944050b50902075100c1c007030700005801d01840000380e12004c0c3c41405801e0003070255910800718021100b0740d20200c207503a45480e82c115821800281082a4034003041420b003e10342507807203040c0c0140042d00305100040c0c0140540d400d4501081000f20340d08030f0a55a035000354029100329040c8a031744184010401400300b130411000d841e0103403400521050780a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 466253300 1250 466252050 466252063
    0x60a0f09080403060b040b0603090307020126010303180f0603020a232704020403050724091716060207080706110d081b0412060507020c130f0f1104030212 68
    0xa0000d803882c641030850790b8440042c0441a0300603000359130b4284002c503a807500002140642424002151900554400100304103865159110001c07a40c4410845001401d2002810b43c0d40c90306040010340c515011802d80036030180e1140c1c0702455801000504d140d0150700804408078180d07a480402e03507910352907628035015043c00005180c0204042040c88000c840c0c403051032904000c0d4601c1c810502e00c0085d041e40c2054000b942c440c0c00846007008800d5840e01c0c0d090044160894443c02d40000000c007501c0102d85210380b00c0049003c204202070020140051140c00d40415036002c07100b521200e0095803185240140c0d12180700d074141c0411a640600e20305011204040000c0454409001e01120380010107040d81e0307440c02c0803403024482516490090005054656090101d84501e400c00f84166040503000301c0541d004007650700304d82e0301d41814424440b0418440400c0c0f8003110482040204290174200c0c080300d2410070900e01e904070b0a0001c0003201d000321680310140040100161312900c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 466254550 1250 466253300 466253303
    0x4230d05190806010f14070503041d01061e050313020301020d0e060604020c0705062505030901090e13030e12010c050301230d11032103040c08011b111e060a0f09 71
    0x480d41710303512245621500951080300e0142420302e0502d0807940c1d0300343c81c41d0455000459440c0028440c1d100549002240c10f0041c1950326103407407842011a0403a50030402c0d0324a24003003000001c002800301500c26a40c1c0c04040d8042c000b1503988103081c019800a25404c4400c103142c0c0220f001054040c5001d0007642c0c1810b541002034443c892510040162551141004032082241c603c214041d2840c0600d81215a17405007001d155a944d951000411418042c6c10003c500b0601d00c0600c4801e005842080c410158541003040c071320340501d00000c0114201500044040d03003030403987c1c540c0c503502202030760403203401d00e5440c00000300541c090760b00a030f00c2e5029103400c00b40c400402408185c1e40d0203401c1d6085c1c40070381030710380c40c1c000d854000e08104c01102030054180e2001081c8020021000d0782c103001441c940008001d4400e80004004031400c401e50f1803c1080318203509030003410700c00d11808186a003000001c05031000c695400e141ca90804071001c0400c1c82c60b0244c0c1c207a400400d80604d4441c613 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 466255800 1250 466254550 466254557
    0xf1e0f0d0606360503011b02010e03130e07090b1c0e070509131a0c07021206090613050c130504120804020a060c23100e0a020904230d0519080601 64
    0x205030f0a4140b00702d2110000c0200c40140da42480094a61001c2c459100703118a00340c01d110792410700c15006420b403810303070318041c0282c2c0c82003000005443d50041400c058078200881d80e00b00741c441c550121076500031600322090102c3d000070030305522000d40c254800182c140311028000010010910b40d01c48245200f1550030110840010349902030498951208a10502c41c904805144071a0501001002c648010ac4070800041c448107500d010282c8000c031070000b0008100070314001a000ba121040605a0381c41e00069030b0001c010444144004200c9020150902d4a40c09001850714064a0155020303035800c503034109a000380310b01c11404144110b8020301a1004030b880e043c811220710300c40300c0040e14801e411002c07100f88084108040c40c560403000c00102003424110b0150012a03144d0030f12242e8030f90000002c1c000503207826201c154044d1300700c0d500c0c0e40741e10748400300b98000f07400034200c92016010310b080030481a50800040e11045e040c00d80c04a0740104011400e42d03a113001a40c9440c040b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 466257050 1250 466255800 466255847
    0x1061403071208250c09142d1e0c0405010306050604142119020907020114130206070218040b0a140a320a050a05010b0f1e0f0d0606 58
    0x1c2ea02600010418044c01504a90640e0094803003400102558010301c0e07085450340e80100c04c001081840542003518620031290030b035400b00f000340007000e552441c01c00d4a90920005191810440d9500044103841040004985130003401003a20780d0243c000c19021a280030008142c40c103000c0140d0702500e07445002e01340307284249000c001482d0340c9484210245184003024102d103040038880481001d480b1401489181100c0c0304108015070001c0202c03046a14100005115014603107403690001c1c2d10104400805000f400420b00c01d00c030300140a9007040d09070103000c000f40a59540c40303201e0b5006846100194854540f80c41c1500d05005220414000110200300981d00139800364400c40310f40c0f00b841508285060158400c400e0481090802240c048200030300300800c0e000703180c0d002101a00412640d03040c0641110310340640c22a000340144080340c01c0c07242442c01000d800b10b042540b001c107030315890fa850361001c46902c9000350050003810800c000904600815003041d0541c01104038854 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 466258300 1250 466257050 466257067
    0x60b0705030d1113150311161103031b1006140a0320030709020d06080609030a080403140304060b190e01230432040807060c02030c01061403071208 65
    0x1410f03002081c1c404254041151600c1380300741c9100b0758002d046280d900321000d0420399000e0304031042c80461301e50ba4241005002061410510b4206080d036000003000103a0045801003442c0d80505001c1c2400c04030408008101014002800350100107619000d11025445145001d255140c510302c1c2500840d841d141170000a410620700c3d04200e21580700054000a5200028900340e510f5000c1c0c40201d900080c2c902c5d02c0340c841d00849011305801c5004000c0c0382020310b83d02d5039910644081c1c8013080070350400718041601c1070492070034403c0c50003003070b036100d0074181010001400c0079414680f03d0101c1000f19040340c00820710710411034284c416840350310fa207801040556011514a410b003415041c20840481d81d82c0ea104d04020303280d41c130843e240c00c022320281c240845407551048044948002c404c00c00040c402030229103809500050203d807080015006a195000d0070740317015000e5007409070104100707490b109014901c070400c40c122181c40d940d440c140070500d0102803000c0c0030b48400308031121 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 466259550 1250 466258300 466258327
    0x9060f0c041a03070c0f06020d0e06010b0409091b140a080d140a09080115030215030421090815100b0906040320181b0a080f0403050913050a060b070503 67
    0x140d0002490808078410217080d514a45081003401c41250007039804210301303543d4100c5106407006900644001d08540d410400c001d02c850080748120700c0c01944446000c800c0041c0ca4203c50301d011408140591240e840f02c482c3c40b102100b510b02c3c0f500540105000180703a080004a4143c7c00d141516403485103503001c0040c20f5503a01c01c60125040c41751545000400400903c103514054031040702e40c5820508610400003403519120021030808414000c1c04082206070280449905c0ba0040c070f0f141403102c030362003501c0701101d961008400340100f258003000707a4084080e49105103100c00c10000400d031104410b20203405050b942c1c5802c100d0030f200034000100419402091160300981d15203004108100191000040380d201e081e40d0b8120800703202c02c00041040d451040e14005c0c4105090030b8a00c1c17001404450020700450b10ba40782c0b8004034041c5400b400840d0202c50024040c000d91500d00c5010601812080d50345062262901c90300061990a0409868020358032001a6151400c1080b158 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 466260800 1250 466259550 466259557
    0x14031512120406091d0f010603092f0f0111070605031e070f03060909080316140c010b0307120b0f1503030a0c05010c0915032309060f0c041a 62
    0x540305441101031081c26001c1d81005000101402e40c1e0700300019040818500d1400c000050490040202405002e0b84072404681503040d42e841c0c1c940062809814140901c3c0303041ea00c059200641c0703514502d1241503d151554031654001542d445000c2c845c040c0044920182d142c0c0c84240c19002143e051042c6440760000b10742000c1003a02000c0120313041c20f03c508007860240d440c0800b040c002d80c0180300854040c01160000d0007018001c20800c203d9440e4a581448000d081c80d81c1d8400031042c44421500079041030310404c030380d82c0703c094032006280b01240c002c0c42c541240e00d01c248540440000c512504190b140c01d0268407104800d803d4590f501c0380421742d00041d1900e03104001310482c9007080e8a0410207008100d0744d070703502c1b07603400d990600f025400c440002c915032040000c1c280051000303e601c2240040303030191503e00099000c400c280210381d01c8408a103d030804003849401d003d41080d001503a01d011300384d156040d08581c0c0350361001c0c40b5603101e0b6220b4460380032044000080308070301e90b9028 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 466262050 1250 466260800 466260829
    0x20c040b01030204240807020f0601030f03030905100b180108153706060e0f090603031c0522030c0b19050403020105070e0109030302122101090c140315 67
    0xd42821784841c800c2c001c040411001c4504280d240100c44040356000a00300c0c3c00000c0c1d40007030024000a8912a9125941404050200d070a000f00c0d00c02090700c0707540841c4c241604a026200050326050848000c1c01e42d01503028825084c1d1101d00c050760341942c80840c100c03540e020040010b2084418040b013106401018030070614081c540800040003e140003403440140750103401e400e24401c082000841c0c400740c001008011080c2d5404400340c4660100303403028182128a000c2c02c0d560803000920b544181c0c0d4034001d04030303482405000c5800f2150416406032422841400001c19602d600104240034504043c000403030b03c04109000ca00d00b004c2650708010758105800e920501010040c081e00c10940d021401070399542c04001265500c4042411440001d1808940803031458070700950f55a030b580304d01d0703102c2100043c0340800100300e0301d1074608040e05048896015039443c4032040c014064900c118007c039100034034040040b0007803021244203442032200154000781950030700035004802140c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 466263300 1250 466262050 466262057
    0x10503041b05030a110a0f080a02010c150e0a050607032d09120503070e01020c0a17010e070e100506091c020112020310170303040803160203360f01020c040b01 70
    0x7000c00d96480610840d914103018540750003061810b41d080c000e80c103441c4d6000b121907002d09001481041d034041a428016902407070b001c01d02e0000750070040207042a104014414a2078988000c031781010100300c28003410301840070f540c1250f451520035000d845507010046040782d04665200032002c00c00842860a400003070b070000d0030400c2c90b52401c0030038270001140d80101d107003c000c2003035031030b40400301c7e0280e60f1080c030141640180b90000b05c1d20410440c080e580c1c4c00c070b80240c083ca21001095010495807000c1c0c00886800640e107882c03000400c98250340c45001d407425400d000c44d050500004540c3c03040e0300585003007505245c08587c0f40b24075800d02812410025982784003601300c00c00340007550181100c00e21000301c01d840e00084042021074490b0010b4103070000d00401000c10030000950b944140c3c2000d046d100303242c0d401c5080b402c610820819000850213048054884850461400c0461205240d507030980407861040140748100f9480040c01a0320602003840d0074100b41d000203100ea0410306 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 466264550 1250 466263300 466263353
    0x19151209050601090f0e0106050916030b060a090611060c0d0c0c0c090b0f040e0a0215040b0c011d01090507090b040207050307050c19080c15040b0c070801150501050304 74
    0xc1c0c8035400c00000b0381c0542411a140c051103500e0001c9841050f21002030a0000c116403417910010030340b5000b00a0207111004120050011854000c2e001481d105500030542c0760784000468014007079000900607500010854120360510b040006440c90003101200c1415003001d1100c4014006491890340c020304011070701a4201c0041d1810348210041e18007290003095840c0b0560030302140c44103a1401a01c201d0604400d000103140106e00002c03d543c0595228002007141c40010010380b18541c482c00b0a41c0000460011554065200300520a0040313642450078208902560030707111168005001600f00c450104610300071580107100c00388000e0405420101651200390a40c1c216103c251003075041070714020814980803203c82141262901001c5e1502d04040e02c0f00d91700c41d004030100d80604051181810800c8070842a40e000340f810071070403603450b100c91031280d8440900d8455030f0701035820300c60f0742c81034581030240340c0d0140e03030040e580d41d411039940740c0b18207803015243c011035010405600c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 466265800 1250 466264550 466264553
    0x60105040f0b040c020706020d0c020105041502031c1506051c0c0201330504200d0209120c0307062a020406090c1713030507030305042a030219151209 66
    0x240141d044c408400c0e00608507103807038401c0103410170f4075100c1000104058010950f0050380c006091f2415a00a003120003061168001d06902e18420445a48a8440e10b840e2900c00300300c2d03d40042c50354880400d06d84000c50f42d255000c1d00c05009a82c030f89912509590000d1582d01c141e07a01c402c0400e006440041070307081c00c0030b00e420515507410035140c00f60034400e2100403501e945070501400a203000e032000c2168446109071100340740041ca120325036002000401301c11182050701034400e1900b00401a42c15a04121420fa54030588008003078000c0c000c1100005080b80554490800d052010380548900e40a00315044d059a1581c04103d074031564a1001207000012072140c1c001d12003c82d07c513030b8802c1c056043c1c2c0040e060001001c960481c1101c2040c100001d5005c0159860240c0c1410081080c1d00d441c544100c041420b0991508500c07027541801041d69036091074402200e00a8490b0104648010001d80c034140160140d0051014045d960191040c41103941541c0482032510008030303001c46 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 466267050 1250 466265800 466265809
    0xf0810030b0a0204030c0b0309030403020607172107022b120c230c0c21060a06060f05031006051303050106120201120b0f01140903010e030a0306080f060105040f0b 72
    0xb0390391440302e2540072034140304000c0c1c2d2103c18000740c2a00e058044c290b1425404e41d554a100e5400000d00808000c11a1401c201007c102c0180f4a01103012813034454072140503aa4022200746040f100f030700c0710340010521950011420b2044d0103490000c20019084950340c8414422805401c901000758038052071000240d940f00c0c0386e0800e24250380b000c6444020304040c04035444409020200214104000d0116850000d00020196015120852489100fa510001201c1410352440075030003848108034500348140d1014080d101c0f103450700d0b001c1c8581001c080710640400c40385041c810916500610455000310040c058078650071040110407900ca6541a003503401d158415240ba1079142160021981c00840c0602d40c00300b03c10041114040103c000392400781c0398080301c0e051188040340254103400d00c808850820f44054000e02a00444000c0f56940741d01c00c082180000745060343c04244158045407200c0d1400329840105100d900740000c110081c05502c85100d60f1568840130746210351079 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 466268300 1250 466267050 466267073
    0x706050c281205100504050105490606060305310203160e0103120f0e010807110106181808030a0b0a05180f07020706020a06020f04080a0b100905070f081003 69
    0x120010340d413101c0c6064184000c0d04d406800291040c848288142c0080e03a251140024070145d002209075010401880608d000d900d024070100c14030210901c0f1400d1101640145040300c0c190b940c20801a51220301d03d400340c0d003007071070084e044014aa1103c40c1c0c65040c2d072407650649000070305480944003400350640328514075501010702403111000400512484078600c40a82d07040d81001c4a00c602d40c18802060140c41881a40c140700443c00460006445240c0c11080480749200030030030f05494400c000f442c940c0c03288814143c9030900e450701690011115000c01043d5100d52142d007192900c510700c4e809025888409034014032100320020703050762203504041d0f500030881c1500c00581001c4801107c1d8a4000700322805541c4140b0003080550781c000340c1208520b402043c016100c3c441c40014043d04e1041e0b034030404c0380d88198940003051004258189005494545440c50000d6480038048143c60089a8003070119002441c4540314031f000f41c40065110180085070341070103840e507540300c01d41c55 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 466269550 1250 466268300 466268311
    0x15090a0e09061006030c050a1d031e0c0a1d13080316020607030504020307050607050304030c090b1e0d150212040b180c06040306151a0706050c281205 66
    0x10b02280a0001d5141103400c41d5000d461039144c02d00550070f242c074019040748034000c0302100b04840398000c40c090014040064150a000070240c5903034402d03100d40462a1900c002c1c0d080031501480c2d40036005442c1450308030f0700311102c0d40340803480c80300f0703620b100d449045004107400c065201040b42e00000600110055110b92494021140080024280245000f9009101405040c80c0409100141c0c1d0001401d108a850841d10310303980302c95600c1d00310700714003903903000500c0740c44102000700707204015400051801781d0940e50446000c61609240969642541001d0303040700c40542c000004c00c0c8081c0e1a02600d070b901460251802c03201c0201c000c8081c0e403c4400341c413072a8400741800380d10011451342c00c4a00e12090001c0844141c2000080c10511030342c070004221603500e08056080f07650a198800042503071001e801a0b17000e1002c04d41e802a8010f10003151050318000000b1b0a007444242503800040d650070b0040c40b40c00000901c158003020750302d0f1070001d0002d007040c0520850154060346100380d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 466270800 1250 466269550 466269553
    0xc030903071415010501081509060f0a0905063a08070503130e0a090503040b07020a030b04030e01031401080a021009050402040306091109090d12140718090b15090a0e09 74
    0x1a142003043c90b500c040c1c02884c100300d29030041c040a8555900d490141c20400c451035580b9484810000310010740d0101c0e01e80c0c000e403000c4000541d03c1c0c0658016407041209480401d040d002c1c01c0b15804882c41401c02030000c100b01c118280c04581c945104901605100d181e000d441c01505882c4d0030303d950031140c550a551a244c02d4240800082055416000b19501c10244906101c0d50394194690149002e040d070003007404105002550740e41c414100040d600115481d00d5810a420700031300441e015512180071070f0034500c1203801c8240c6c4082d000d040b22071100140102217032540c00c101900e403103030b0004001c00c890404082120343c4c2d54802400103622030400051984c0c071618191080680c0b41c0400707481194a03608222250001103a0003440760740a2400b8490f400007a07a040d4010400861301d28a40c0340d00c0000c000c06507401000c11a001c2c60401d604400140d55112010700f603d00e0a088103400180d09154550a802c0da5006018401802407402c0318842e03ca0030096014402140c280d0810b = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 466272050 1250 466270800 466270813
    0x21804031b0b0907051005071104020f0c0303240117061503130213021615020d060308070605060d03021009110d080a230f030a1e020a0f05120c0309030714 68
    0x43d0400b00708030300003424190750102140d0080c040c0038041d0f0280800241072103001d0070002d550b44e611581142c11f895a25452070b6128110b40f26107503075030342044034034024001c0403030000d03900d03042440c0f102d81801c00140d4460381480340c0ca80034107021134030190449400c908450090781c110f5113803401861142024543d03000c501d083d5801000f1140c00040c2e8540f903214410403000e4072602d42103d400e0815a006024201e816415613440e40082c4900c06a091080341307441c001000b00880b000050071190b014400600070307606c0e00c00400503503001e01b140003000350f44000e581d5615030105400c1003041d107025100301840c4241d54000f20b0324a820306001201d0b45600015824800c54005d1141856240d40129901015249142d0728419110f03080440840c4400480050f03c03041554200c448100020521025003680340342854003c1c0d0008040341e400f0500b1182001301046c407550583d03600714a04030048109854a070361500d81030340040c0c102e001d9404200500e0000c00c8092707410b64440c06000008011 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 466273300 1250 466272050 466272061
    0x1031812081012080306060901020304031b050a1d15040f1d060f0108100b0d0204090c0311011106060607060b03061003050c061c0e0106170106170a021804031b0b 71
    0x40b14415410503280400b01442a0f00418820703400e03643d00400940315995168840700050703196000d5640024030100b00d202c00d051840030070000c40b4084440030b44c5c040a060703881d9104601e1004124105960202c41840040d240122002d61400030130f80180c0005051402a00c140702540c0349103103000381c800d0780c2d2814808602c60400c85c5660104407150004110350400034220b841d80c1440700742940c0380c0d407507000e1100caa54170960a160b540760f00400030003000d4003c0c0750001d00c0c03980d43d200980e00000480012906d950103400510354102801e070181c0741c1c0340c1c1d0700c40c00c10002d50460394050700c04507910b40054445460030041c650292080c241940c60551440c544507150500b05410107024180503c4140c14680c00c094101a036030721a484045101840c0248050060010f50300240c00c3c0690051050300703001040d0711043c1981c07020324100000360072610416030b5405c0304680c025040742c13031041401003500801c421250040e12130310f0031000e014048062160715611420007030b40c0a110010500c034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 466274550 1250 466273300 466273321
    0xf060b0c0606031c05090604090501090b0a080106051302130306020304031d0f060304022107060e0405450307060b090f01030209010915030c0e0103120507020a050103181208 76
    0x20350040c2c04400506882e0361102a26540041003100c0d04244100455080b2203551040140c80180543c4031040205683d82c84030140a404040e032105d00500001d00c01103420081800fa610680d14060070048100040055501c000c0d4002501041017807114140400091b00c2800110302460107551004038034403001c2c800d4812101c041c1480c501c5200c14555207a455103070581501da109030102d07132220302c0e00704282ca40e68120202e00511101c6000340342c0040340284d08000c20800140080d901002140c0d1500d503042c08200b41403000e81c90300303210702010000340e04070901002358944a0f084810581800e01c03602601d13503000b45804440c2185c0382d41c0d120003a402d0101c0d0a507401415052840d059525603000b266103210103000f03000095858107580c10108009110b0140290303030145494000c075070303940c000c500005030a00040352500c40c9121142100d5219406039500180c004008a0f91146010010742c01050018410810351418641c0c0d00c002c2604e1040007841d03410039460b070115500c0c0a0a050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 466275800 1250 466274550 466274563
    0x4030c0f080a20010302090405040b1603020c0a12050d05010f030618030804031214040c0906050603010b0406120f020c010b010905060f18120d05091009031e02040f060b0c 75
    0x503807122000101050400b840140300c18603c09400c0e0902c41a040101c002e44607032219241c102d420030061000300820303005050701c80c1800318203050210503105412001e07031058181420705948118010008a00da02d016000c082e111401c2c42c0307140c044e02042040981c4e000341e104102c402112401002407180c6030089000c601c1e40745292341c040751402d0358043e040719005000030302000071125203085e100e210b680c85070300050428030400c0101c4c509032910401035015030041c900d5003801c08070b00013024140a41528142d943e0380340454189420018116036840601e1800b1f010031307440c0c10f12260184128402407205158807800459400060000034140a0a40d0701250041604000a00b000400e080070b450748884c1c1048100c09050490340001c0220312148241c0040b80295200303a04070f590040c0081c240c214040d12a034002d416108002d803401d001c2d510000d0104804005032082050041885074010780c0b00820000d00c1460907a0800210365554000223208500090445081c140402c000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 466277050 1250 466275800 466275809
    0x60f06150705060f04060e011802040e0f030a031a0a0902191b080c0a05190b01080703200a17011e0501031a0703020f0d0923030a050c03090604030c0f 66
    0xd1910400b0b03515541d0380d080003411101d07524661800716042085541000110030a036400902c00404400c00710074806a02c81d801300c0c459440c00d075200c100008003240750000c600e8080e01442c103103c403881c0700b03401a20140303100308182c0410280f40c00e82666080e030600c0180004801c0183c841c070240034512036034000c0440400030302007100307080169045008141d814030340e4407425050303c0721604040305290402c0c90500412034090010340303650b0078080c4400604824000d51030b03407013a641c0e00c03000191541100d000180031140106060800340d01040c921400020020f0460360780c1d81d951340304000030900400420511079449055814201e0030003000505070b2400c072842002554559501c0b00e0400659280400d501030072000001c110314020740c1581c12031882da1362615030344c005000c841b03001000c00e000100c900140c594010b0202e04400e001801c20042030300d005501e0010b8080e025201c5ea08899001400d91204104529541c0c5540014100440c450030171080b03410b040105000004815400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 466278300 1250 466277050 466277089
    0x50306100b0d020f0d020429040509161110020c070503010510030b04020d0b010305161e03020f0310140a0c0c0302120a031d0a021002011a1908060f06 66
    0x41840200e00d1142103a894502ea50ba005039181c10000741800c03240650b211104000380b02160005881e01a080c60603a006480800c104d10454503504001043c002c80c051103400102c540d001403489407049000d882000981d040c0b01c00010208042280b42c100c210401c0302007a6000f0407049154082008020b020b0031046000f8402d5140046c40001c1411540c40050950344a0001040030354464003010401150480498030181d80c480c108203031f68424401000c01052003046000030b80c0d05552078585043e60314611078403845881d503020440b0200c0c18015260741342c0549240f03d0040b0304c0d544034002d88100d600500005624000709800c049500001e150000e0100100318040040d0340440e02c003200c3c1c05803038560b60b1a801c6440d0300300d008105d044c07402d0140b40722204202c0841007000600f012014403c0354141c81d4080c038120202c2c00d03038080c50440f00c900590154220240e04d0300c50b190b43c01c601c0345401840d00d80da943d800e030149442e40c240d5201d4110109101400100e040002c00201b100c0e12100 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 466279550 1250 466278300 466278331
    0x60903030c09051c080c0303130b010e270f01020d09170a050f0a0306050d080306030c0f0a0501030b040905031306020c191e090204090c18060c08030c0d0507050301050306 75
    0x481c21360640780c503c03010020f640d06000c100300400e4809a44a1000d20000c076a200d00c0c1c5503142008a0f444d1580c242c4980807680700011342c0500c3c1d114054480c51080341e0310181d016802c2c2180513207841e5224591030500075040300d0b01c0310f6102440074062101c10381c04042003c0800342443d14614481140245480784208100390840e40c00c001102c404000c2000100d0381d841a0190490081030745400250348900b0b000f01400600003607001a5000c0e100171003d07203008401c04403c03c49012103c1d0f180c250425980002000783d9802a4882a50710070040c10100e25804540e80e2107085a2050407640b4400d5a000320521189604021403001e119054484024828514036141c0c0d1b452041c0c41448405a1a031019103104004c42d041480201403028055407200d49501c0d144025204074131110303000030030080849084001c3d41010104480803038880b5010b02c4907545a81b0403d500082000c85c10000070040801002620310a061082c0d503c0d50302d8544950510b02094203040020b08a05c00020059 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 466280800 1250 466279550 466279559
    0x2070c08070e390d450209010e040308010614120408120c0307121e0c0513060207030b0a020c0d0e04140c070c0501080903090105090409050307060903030c09 69
    0x250991500f00155007001000c541814401041503a42c011124070224920b20f050320b00c600503940905030b00041d1410512002252081031407014626003080100342640b58220003811409142c1c91a0705a110000c038080d84c0d10940104820100a900c804548403511003040305041e404520180074201ea442c10a4080314190756940050054441c0d10110590000c0030404201031001200c00f115003a03421079003186017084049145400c12643c0c18046400701c01d0807004214588203502080c200d580d00c902600d4140550580245481707030956050000400074520003010480d40480102042e40c000c0c2441400c41c90000403420010b1b1020281c2801486010580c10000c52140d4200e582840d0805130b0700041c0e40081c000d0201c2c00e40388101ca10135102444800c407030100041010ac0c0c0100e80b10141c180e038542c01103503075030421205c2000c40d42043c030504a82c1c1d0b200702c0003414400b0f00200003168000e0251550360841d8060740c412030b02c90340d851095070304241c0c06014144980c1e41c00c0c1004080140f41 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 466282050 1250 466280800 466280819
    0x150c0c030303010b300f01050102011a01080a020d0917070201030f1e050604020f0403050f060615040e09070e01061d0402031b0c01150b040f080106060929030a02070c0807 75
    0x5c40545241c0030012040f1041c00803035074842e050710810888003401590400070107043d64120b0a015480c015424244444e03a80d24004184112070b4070181d40c0c0803040e41d00e050400000350808800030348041d80b03c0700f0b0003000c81c60780d040901101c0346c0d41040581c0ca0301c0c0c0d4800501103a18106401e09214200ac60b0a69650f82004d500ea850420121010513075507512000100203120382e00d05880c420300049008401e000c800078005418405130030032155184c651030104041c0004819040041c184d042000380301c540078078054141c00c507540c602100c00a07611007a1312800200260410b2002408030000ea002c6840341298021440c4001d8500310300e1341c10901c02501e06602c480108031000b00000a010b018040c00754000f4400742615a03640b0502034943c030740c440c01030340240b15283e041c031955980842c4200b01881480c045580ca5140c902c0c00342e25003981c3e109004521244081c00c03d0000312015100020311700110704c11500c082c0f0040c0e5a16061410000c0c01d005a08544170941c4004c0e1b061100044 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 466283300 1250 466282050 466282057
    0x20151b120a030e011113060e060c0307140a0b04210f020705010e0a0803040b09011e02190201020f010e10060b070c060507080d09060c0305010909030906051305150c0c030303010b 78
    0x3410300e0049103c684004140307002d131241c5085002580000100110365141b00b401440a94a40c0d0761f8420012800400b085064040c046484120303420802c440c20024000b80b62241c1d1032844101621800605a100c00d5804441200c090701d80090f0400c2c100030341d1085aa414009640a041409140410b461b0081d82d03460b8902409040c0510b50003000404c0d5101f450280c000c02a601c101c0e6542c82d1200107041031a048500340d1808140e075150201c00b180001c0130041000509a40140501c82450440c0c045002e03d2001c10f90540c001e134038034801e000c3c100380201804102d219004000415948203100215507140d84550300f401001d1104400081050743c10004495aa250060320b0709a54200400203214a0f550f9201b190325284c185000c20040d60007a05c1040f0464404110980c2ea65510b03800b6680a642c0c001c001507411401440118040c9010b40781c0c6201903454441d94540710004240344190300c000080c610200407441042c3d590302001a0a024107003a40a5410355260105000d144e00 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 466284550 1250 466283300 466283317
    0x5071d040b042a0305010e0c0d15020a0c0501050f010519081c050f120609010f030b040b0a0e01060e010f080c060a03020901030b092511030720151b12 66
    0x200140001911251202d01e4900191a8101030403c4d80ca24081c3e0007000135a071421181d010300c0c1c400e81900d29107032902c0c110184d000aa11180805054076250003903200550700028800701b8000b45001c41c00174803602c0e1081590307502c0308105505001c10804840860004410b001006440500c0707584c0010480414013040c0d084403a16200744000140c0d00350049900742e45116001040721144400155810381c003410040e24140107503602d50701e030018090190300002d450602004041800101003a000319844182040c00017a0004130407002400e48005520802d00340e210400103000c40710b880741880d40100a50001001c0c014000000301e0105d00420350400d0626901017a0010315034001d400050b030042d8000d05501c40c920b40020520f18002d50030119040f0b4080d0007581c2600b09000307040401c020210240210b00300300c0d081d550400030328241108180c0c2000c040c240c00060740c841e1002c0181c5000c81c00d80d4035071500c481c0c280e0175040c520340408210141d4409106000f1031400c01d0704036584030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 466285800 1250 466284550 466284563
    0x5030607050409090212030a050301062304120c0302130c180e060111100c0c210e280e0609090619020c1e0c03010c0309110904020111010905071d040b04 67
    0x141d0309800010f181b2030300100901c489000002d500148254400000d40c1a5405501e910145940f0222030070a8001404140807205104000911582144500c440c0c000782c0b25049500d03555450798041000135825440005000d038841322000c21464224050a10002d0030725401e1011500d84002040c405d140a007490f418048140b65903030503044280864001002d01900c1071000c000307500310041120102c0340003690158040c51071171080300c07402407022080200c180d07200e1426880d000c0410004440c140207401c101e500b12140391031840b01550b410001002d5426102d9440c1c40c0040605c0b5100e5402080d40816401c400d080000070300001e440f210100c0941e03e00141c54009110f0000d2070701542060021000d034600c800900840c1001a00c04202c900580c000d01c140707510248250243e45d0352840013840c250803440340010904049071840ea00500524058401c8056590640c0c04c560030083c00356040d0300b10010502201e035002490f6004030380441460031107841c040e11803a11207203005d440144030 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 466287050 1250 466285800 466285811
    0x518040203190914011a090c18090a02040807080d080105030d14090a030f12200c040222030f021e010c06150b0d0f0509070303020a11220f0605030607050409 69
    0x14000411800c60610313000c440200103e050742c5d44081c2406601e81d080c5c40c070a10061000481aa502400381e5600705248400c08200103010340070030180b41070040004940c56400e0100162400c0d040010b64010400c1c000500888a11050014101c03101600320500980c4100342580820382e01200d80c0c4d54400c0344a41c22515a1034500000c0c40914990340b0207854894012002002e11004c01c002c0382c2c40002c0c5455054600f001d1403145160001c020300884a03541082100e055182001c0d00241040464a8040c201c140103280002e00c0c0e00d03480742c2041d01c2c0e00c000c40076040c0450400d550404140c98030708001c20301640c000d0300002c040d2158100028a010784601900c10b01e07090760028107001d03141c0321820075220744c50854280002d022140c9400c080030309110108031400004a071920580e070700359010341100078440e01d5000007420300e034a9807a049215a0690704400001c100382215560031290045802c3d00148503600c2503030300d02e4203d1031194100d4402e109100b43c1010844045a02805000c01d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 466288300 1250 466287050 466287053
    0xb190c02060a12060504051504050901181e060203011502070501051204020f0d05010509030d0b040e120a0905090403200105070e1203160c15020c0607150b040c05180402031909 77
    0x10705038a40c1704640003030406091088100c201d5856450314501518100415a20705040302c0c01d07a414041c03561012a00d0381d0180c0041006464209604c1c110b42081c0c90300784580740e444c0c0040380c1c0241d10010362140c1204405e0020795041c030640c0d0040200b40b900714101541c2240b04010010003400003072240c21445040c0c506a21602c215001e000d0700240204a2490003440060312603002803a0f00b040b03580f40458040c110300e441d04c50300c00801550001009501c00006d01102e42d507008101100600c403070014005a540d54040c40da9114511a5691000e030072603c8040c041d982152502001550b41800100008203511940d24041c03110100c50b112010381c1c104281c0383c00e5220303255401c111900700791000744c18418070f90305003800c8460040024185419000d000c070307141c03502e0385184c03580104100700e175801181c25420031005400d01c89078001902941440054200e035030481210011038004034004503a142c82d00811954080b003514150720314031780004d107006009040c951482c4c840781e4942e070800 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 466289550 1250 466288300 466288337
    0xc06010504050a09171309110421050d0203070b0106170a020a170a060e070507030807030207020a0e070c06060602070302010207091116050312220f14070b190c02060a 73
    0x1400d080d0005d6010300c064244501803000d0b81e12014616003000001c481c0007607250401d110310803410340d28502c040d003460b04165600f2881e4400701000006029628245004200280700d0104488030917001580d5904145c90408040c0380c0c16800202808041001e11002c0010703500705647c0406550780050344e4080c220020741d4400c0204006550601c7c84070304000710380b1683e61000068421039081028aaa101041100c0c5841a00c4000300010032500c0890100c6002c0c1c0c01a02c00c842c401050356028940724030b59420428000c0b00c15400003803c88403d4818444c4038410b00740a01664400707030103030f68150340010f9035605e81445505070f0155590b0403d021071031000305956900c080d8005040c102d01442c02d1142d038a030003043c01c0c0060f218445e00400c8408104001c044205281c9140202010b04551a2950741c03410414042e605104c0d00c0c0001c0c0702d00e81d07003808100302504624488a40301c11b51360840900f120260a420000e002194a401000d6580c540989562010602c0c003510201880c3c0c1035030 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 466290800 1250 466289550 466289561
    0x10e040e01060b0705010605030604020d1b030222320405070905010f1e050901090507021e0d020f0604081c02040503010615230409021b1c0f050c06010504050a 70
    0x20940340d4030740344010030328888020080c00282d000c0c0c0c00038800280c0f1407007055102c103400d5400a500c0b104495034135002a10480080c480b4030086611040d54a9498004c01c155400c1c001605024003c40e0050001d510017601c00c08640d001c00052503099403031545050070700030100e40001c50740c0c00055130007d03041110801c00c000107440c4d106028001560b60f0240d5500420076800344040705031071380e008000c0d981002d01003442240d01c01000c030301e60f0340d1801d01c0c100002d00000e481c1d20300f14050704180c20f082071403504d07050080c044210018001761030181d200904001c0c082038a45039a800c200c062001061341e650030713186c43c03020362001c0158000420300010000c2c451640043c0e0103500b403080008000e0011210301d142c40ba05512203d00400144442c5c6514581509c00190f501400740000d00c0005030070390161030440c9100d505d1b0000d46240716800c0d450003d00b080340c4100c1e81c0b10543c9070315600c0c3d404440c0e0f40c0c5200780d40c201a401c01910041e140e40380c200500500d4010740d41c42000410401070398012 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 466292050 1250 466290800 466290821
    0x4050309013204050a09050f010303050901020c0910051002060c0a11150906041502070c0905070c170c010b030303071215120309050102120c0c09060120030304030e010306050f010e04 80
    0x10900d40300d07402d1031942142c0c10503c5203510a40c005240055011114005d46200c2c03403610070365040581c2582c0e010b03100c94205e00c20160451040d80d1803194684ca5015040d4040c80b4000452120145003808000131400043c03610303004c5400107810b010307581518400b96410f0722030504001111000b40b2820f9171500d000400400172204040046c42010340000c01e600d401103004514015565407403030b480c41309074420b044c0c0040c0007402e1850200003d04c610340c0403903002403ca2528040b0743c4c542d621a0980103201040c401c040b003400040030a8444000d22800205620070b6018504602c2c1520b0090000d105e0102d41c94031013519940e802d44540c84407052803010302100e2003401c001c0c43300781c2001840443d03140a014094400c0039003404110280c03c06a48000180c000108103545a00d001e00c00c0030b22000c2d0150b0f05010800c5403201da840e11103400d07030200f40b4045004540740d01c0c2c2810000c00c2d040803905010f05043c64072605200c50388810801d240e00b1282800c1c07414422000802060092001c5041c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 466293300 1250 466292050 466292117
    0xc140315041b031a100608041203020910050c0708010c0507080304020f120d030c02062a19053402040207051f0b03120f0406110106090f0618050405030901 68
    0x310802c4040c1840440c442040320004965544005c02d0070300203030082c0200400320f0946400a07000595282460910980a16000d400c0088640202d200fa1088044e102c001c2400414101d42c00340040212000038040076001b407211a0700504050003500c0740309005007030a6070010002e010740d1038a4100b5820303080060000c107001c58a4558243c0c682d810b032200340c4002030030188410f074020701c000741803809410383d2ba0654202406049080314418a041005513180034140620010014040c0c9865042181c0b91500f50360b40780201c40d90403072010f200c101404240d0f006600107681050801101e010030303905130340050340c401e0107080103460003082417103448002d18900e00c003080c0c00342140c1000e400c010095048882d0741e50340f80d002c950a4001c501a00f00c0b8560180010406244120400b0403078200c03c0000141040d15070308640305803801d01f400c0e0703000709031560800c000c0101c06c5260039110964403041007096040c1a0344030b0b92280301c1c6890050421001d60520301d4a40f0218200c1d007424000c0c1007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 466294550 1250 466293300 466293353
    0x60d0b03100f0f0b090a090215040f06140408030703080c07150204050a0503010b060d0c1704120e031507081503030408070302030f030304050604150609050a06030c14031504 76
    0x1d0200740900700201081d9160360030410703c048104804d0045100d0210004c0c003514159695151000c01000c618201340d038002c2a061010b4012110710005201600754000580325681c2400805406403500c1c0080b002c0325182004100708003400442030f00c1c106580b61402d00190303107945c54000075a010b08074000c4e00c0c542640d11010008440340c0c2c01402154000d840350441d1990b00c40c00c1608886001810940240040010100400c0a5806000d08100350700380420150b44280480001c8101103908440d05180c4420704d042c4282c111141c1d40d4075402c102c008085000801d2442580303890b002e4180e9007400300040105181344214120140d40c08009402c03a903c50365628134107981c3e044144003d078021f02070303840b540d1803a000c00303c1108c1c41140c02000412540d00c0e1903a0b10042703000c40818450a4135505c10003c90035640c1e901985000760301080c0c0c0450401d05604003010000c08070791000b49001e500c00360300003190b10b0120f031400000003c011aa044e55455040208181c8040c1010b4070511300580d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 466295800 1250 466294550 466294573
    0xc01021218150a06151722060b0d080c0114060d0515072105010f06090305030301120f080301030318062a0f1703150d021507030c06180203010e120702060d0b03 70
    0xc5203a011070009111a031141c0d444107d502009080120b030040000d0f039103510038101107100d80d0840c070a140d001825103924a1107d0321050a0ba4002d40060680390751120035001c024501d0040781c913000030080321015610101c540e641b680d1410a40f5640600403030100002d59440e0080400540b0a580040012078840c014000c5400810f0b00b401230440e02c0b144c5080104005126040d0b040689501a0081d8a56400c1034441250700100b100101da1580c40300303841100103583d0001943c029480b986490400d60200800e00740459481d0700002c0400802c01070300c15440c440340c440c12a0b850030400015000442604000384413904111001c0c01c03462030020502841c0c89010020341c401c406904000743e000a1020803c05055104100690300c9441c10440e02c402195050050142500c40d04005018800300d59807032042e50301d048052005886200c03455425403c0078000c6049000c04a0050002d02c07081400b107500c64018041c0280c007407a0041450760b000081031348904e4103000c0c01821140900040c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 466297050 1250 466295800 466295807
    0xf030f06080712170306060403020607050c04060f090515032808180a083009030a050717150115020709150612180204150b0c01021218150a0615 63
    0x550700b1504c6001d0b00140e08104229502070700d004000c010f0509103030a1460b001c00400360481c0000780c580b4000d4400c410955a80c0e4442c0a008203070341401c000742c0914190700c8404903140280409101c2044c038844100039540854040c0c1e21004a00b0b8508a0780754401c24008800580c540c01481540000340c2030b01d100040e40c00c0c1d1030402c8404c4031400002502c4501d03690310344020b450040c0b0000740912000c210314620b402c0c02a651407006200780e0078a21003100003071030320a2515042c0c80c2c175007007040c003404041001080030440e83c3d600b00040070030b0403a0004c4284a14414070850110300701004582c049540309020b00d40c02401003402c14000da07c0b00c280301c691145001d21030000403031550410004178810500403010492006100b21071442c82c507409200c0688030420880d1440c00c855400415000c130200082c0422074001000142ca801092900f0b0801401c00303004003021b616558107410045800141d480343ca0500030009455a84071080e906000c5c0c0f040707410544410300f0f803003c02250035a1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 466298300 1250 466297050 466297079
    0x60a151101050c1b0307080f0a111005100504060807090e0f0d093308060406050d08030103060f02040312030e030409060308070605070519030911030a15050114010f030f060807 77
    0x51030200301413242d4041c40d005550303102c1d148006124a40c00d105000360030800c02c000d1314040c10903041482040080400700c605101c2951003201c16255110240045001c1211140d000390106480c10880c4605020070145d4542c400d214146000751503c014503031031401800038041d20008a030440380f1071140240e000c1c180380c50701e004500c00c04030201d800e0480041d0345540c0c03615844900c02000c0001008000803500110010b103c0c45d0042e4441038009080d0300c5070008000c405004880c2181c8035411843c1560669540c00e001466481c010f203c02e201246c9a003040b042e4260342c0b410f0001340340d60800b1040b41140a240d100240705c0e0301d403480020030f21444a008068003807061804100d180e49444d000d0701e09004e05401c1c110b1100a02d0a812031650196119420702406001c500040780e0340c107000285080f070380c150100d824806a1203844144203490244601411107400040c40100108000034150101c0c8003011007050744640005005503840d0380044068803801e0141c505180d00c2da03207441d00019 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 466299550 1250 466298300 466298317
    0x120f070c080f191a1305070b0c0715020d1803020319150606020607050912030307032003040b0f040212371e1407060207050a0509060a151101050c 64
    0x3c4004506001c04a00c07503448405a01c401d0300151442ca01004d0071019200a24103114140c20103042000710b40700b040302400138003107034024550320108543e019003442c806e07921204451042c50000d0081c1e9401281c0000100f02078034042c0081990303180e1030300300c014065001035014080c107444204450602c545003002c0f0703030142e040000c1260703c0300801c0d03046400d039208a100681080e40818180c5228000a16078500002d280903104100407400f90b0031540207451000c0400d03130790303400001c41101d118000480c94a10004190030340c98240c40d020300b039080c001c00645250465000080c02c640e2100110415655491b0840d58900c1300d030b85100e5850304d100c60004132103448000c13811500c81c0300c210f0b00d80703441644900c0745088140c1500c4415090b0990343c03002c594101050700460210341c010000c0b06c004081c03650090100f1840c010a1220102d05030300514040c28002e42000b20584501070008110340303418030101399140f080c0108480c80000e00f0405846ea50030141400380c828a281d01070003089 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 466300800 1250 466299550 466299553
    0x80a09030309050d02130b01050d05130308010501210203040804080d20071a0702010507201914100302090d03211b050c0c0d03020f010509010509120f070c080f 70
    0x16242d40404c034200100643c0254085500040b591010256410240400b4030604181c0c1c01d01440d6002c940580d901121201c15001c0c88056000a140d07015205030300400003030800407001114174000214100858130031046441c3c00001180c10402c0203411203006002c41000e641142200c10070060803a209601031414500304568002010603000c9403030400c480e28400c03601c40340042c660380c41d28240c02a500c1a41031000503c0700f8804590120300e0042280307030746400081c041c01101c00308801c00081c00484200780c8800034003442440307611200b45000032000c450004208001e20070482c06071207503007c4607030080303800c880c5401015001010520b29230403090401452030300028503d402c943c034090900501b103110100a0300c1090051008000901c010307010346460f4119600440d58101c055403007100140e011058000100b03200b80700302900201d1a400920160034880c031156a903d02011070028550310018514001b2403803001100c01c0d06034000400c28480b5500c6411303603141c849016009803603 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 466302050 1250 466300800 466300817
    0x1080102032a041e05030a0804060206070c17070c0b0d020403230a0f1115271f11060705091005030f0412020a05100c0e010809060f060d080a090303 65
    0x29280070030b507001e28209034990000c1c103261038000340d020312103c03180c020308040c015820041005d880a00c120342c260783c0160400ba690750714041c030085ca014030040c10403041201207802d00740050000c02c0c00300e8400c49004072454882c1c200d411b01d610303102d91036841000310045c0050a02c0c046d03405500a030084174016581080202020740400b00c01e030001d1109100b0b1500303c200c5040000d000035a0f4100313400d006103070307020302c00b0500d1010034446284036651182c0c0b01c074080b0b038807810807564070210142c9200c090082012004404003040042e22000404030500e1814118240700a200e68020f010310350080085881c21300b80301c0b00150450f4401ca408500405524000d680054011400c50340035202c10701c0c0c11140f5666588481d84242c0d003e03018501180607442c07042011880800c00c440c00c8404008000234030828514002c0e00e550a440e907058140126881080895080030a41c181c0c80b040e40c2d102125150b0300e80d07000410310301180740d008102030390208140c0c030281d51164611040c0c80c070945401d1503 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 466303300 1250 466302050 466302091
    0x50c031027050606062107230a0c02120109050a0c0305150f040201050a031b0e0406050411091201090213060f06030506030d121104030f0203070504050f041113050108010203 76
    0x140324482030042d00780c1d070183c0085804c3d418028002e1030852024000701422400d40840e42c584e080c000d03210140020300746c50a040b107086058280b1401451101013651800100c48000760010365002000791040d00c000424516540c020340140d007031290f101c0265245402c0038640340e01407904601080d0f40034818100192907071710445a403640202e034028030041d0385a4a90740111041c0e4060881901099114140340040034482820680c80651710344581882c00e5800703085c001102c606070300451165052440003003880c000e080072a0390440003035a9041c044a0302001c80c0e40034002860000350450401528100010100c0c0d11202c2074620f01c0381070303042040c0d8130390381241a29415500c1d55072580100b1380b44020302d40100034090884421100200701e500c500081d14600340c00c035500c02e07901006903020840442c6014486140034001c2101c01b00700905014500f0b41d001940188010803d0241608104507580c8455034440305840c40c51080c0010b6841d40e0309503000c0c1d041540c14150410300031b4008175 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 466304550 1250 466303300 466303361
    0x60f0b01090503120c03130603290a1404020c0601060c0303060806150112061e0e010509100e1305030706020d0b031f0209040f020a020601060215130807050c0310 71
    0x42215002801004c0a1684102401441e400726900c0461131008000d00b008688110299500030007864030006059108222400070a0085074401e02c540b414090341009035540f02881b0b001564040810702c290141c00c080420000e00c6460481d50043c4140c3d0000140c1d00d5001c07141184c9a4400d13a81032004c0340d40c0c1d10746981e60b54002d5400490030300d1194001c00003540714003031703000307441410071008140c00da9688400ca00d0b03c54481040e6440d0745042000b801302d0020b0168081c01000c05072541d202610308821600d03540310b101e000703108600102502203035040e403005414460715034000c82903a60711509854200000d510a091001c401401c0c42000c0d410740c80c011030191030031800c03080240341e10401d0410700b43c02980000e1480b03600c250340c3c0700c0100070542130388060101009290020001541481c0700a860401c058140079201d82581d0100807011b20f41e25201c4003582d5000200f05d0700e6207104d240c5036003000030aa158070340510480c009031040702007030307041020002c2019207581004102e000740309 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 466305800 1250 466304550 466304567
    0xc0c130510050d0227092a060a020322090501051e06030a140405030304030305060a0b040506090402040302180403110a050604020d050c03060403052502030a0b0c16060f0b01 76
    0xc141108140010050b0742082280180100d100a00700507000040182108180504003500c98843c0c004208001000804104951621050701c800328810440024800d0142c454101164007030240402d500d11183c2c003c009445191882c441c0f01c800702d861101558000d54a03a00c40e0300000f509080000500e82400c428032400d07100e9540c0c448030806503510900c0742d29440641394007400d594a0049916420f0b8844080d4010761040000d5950307070405041c01416100090a4144101c1c003d11080050180000485048a60585220303071250b20510000c0d009025551020350403841444598100e0b0541840c00e5108510079100c565415241403c503640c0c4198255000b8601d030b0103040840d0142c81c0441a03641074a05c24030465003941100004039050030000e84048001c20700100d2103080302c000c010102c9580b50b40b0340e04aa00d040d00ca50b000aa60342d813009001500150500000c204288440411200751031a040e0048500d800b007032070010010490b403141407000c0341c5403044440c601d61098039030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 466307050 1250 466305800 466305811
    0x82b051509041e110310060605030a0f02160f0c09021804110c01020f12090c0a0306050a0f020f09030709020c0721060c0e011e02071710020c0c1305 65
    0x4445503808100510280507005081070302c5941d10b1144000035903040310740b40079080740f003000c910a00c0c01c281c0c820f05180800c8200c1c011001030800c8014010a540304055030f074003407281140410024020b40f070110007031150103411403001c4100182c180038041400345111f4014030480d591189039650300203020490107140f4500702400701440344050f5a18154000348a00c1000701c1c562403520710012911822a4002241042000804140d0301025090b4054080d031100c824030107040da0245010000fa402c40311408014242a91400414a050b885030701070300000350107240c119a50044c50085513807907040542c05500c80d2081c0b00c004502c02c0558004d4500e0f10b400383c00141882410004145140722201d140c083d281142c0c111514003060090042c9001c804003600d81031101c05090780010144e284210002d00b603070002c0c09a004815a0004a03482103845503144c0342504400b0b0311059040c018944901c500e040c0c00400e09024030f50011130000c112000031100c81b407084000f021460162801100d8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 466308300 1250 466307050 466307071
    0x8090c0906010c110a1707060305010506030a09060b090106030516020a051b01051303060501031a06010903061d0604200a0e0403030b060705060702100b030313030f0f082b05 76
    0x30984030750155056a01c07151080420311400035032030012505c9540b481e40f180304641541c4601900801090021030040c25481c60309015640c1800041145484054041540f041d03030b56143c1000c0c490103a001e2603071481c00602542d141e52751458010040e00c003c2d02d0a1048a4420700310201a600000d400c0800d513030700c0303806003d00710510703201590314400d20158541440403c1111103040c1c1000410b0002561144200080a5045051216030410404c02c2c0d428080100018040e450ba0041152011244e000c0c0000c030358805008414585c0608a600c1d034601d52140724140020411004071012035500c0c80c0e210617605021500810210070002d219110040e550480404c3c0800e100350000c4d40c4405010340760a00c1c2c840c5d10f075203203460300c001100c0d40310041c0c0101c0303000d0030354440758040c00350360300802ca00860802401c0c03004c2d01170749255844000c1c801c140e1588124100854424000707043e54120112548842c40f2424040c1703c0c805480c01c4813400480b420403680e1031503d51181d0343c0540380049 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 466309550 1250 466308300 466308319
    0xc0102100e0c1318050307060c0c0209060d02061626030c0d0f0209061908060405010b0a050c0c0603010f030b060604140f15030109060e010504020702090402100908060408040608090c 80
    0x40c140080d8601c0c0c081c2d440e9010f5250354450f541441c0131085500240d10601c01141e449050b41483d800f110301c0b40c1706130400c12040003210001341e80e03401c031a00e0b007000c03044442c82441502480020901e2181c0340e030080c000010801800144107204082641003c4448401c80400d030003004036111500c001c0315100c1003030400348041200d1220701e50001d0b00c590440c030001450140b02c036001402c40e8001e08000d0301c03183c0700304117200700c1198040440380c0c0140043e00c040c041541032031a04000c6000f032407d85800c000c00818050b0388004100503046103084050700039656175864000840417150640402d54180d6142c001048807400e04404807000c40c7c052408429915881c40c08120415044120742d681c490041c010b640c0c8004034900045000f094448030015900385030402601c03680005a12107442144140711580150b00d440201c20791056045a40e007154200d01035080e03a101e0880c1e00320348440c0c03103100204000c00001c94001d1064500d16126000c940e56010405a581c0c020400e00540050214 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 466310800 1250 466309550 466309573
    0x2062412011802131119030e0a0b0124120b0f130209011116090e0a02090c0306011b02090c1312030207031e03020c2202030a06050f060a0813080705010e0c0102100e 72
    0x2091100c001c103c1d140204d1030803004800c0074030b000c1c1caa275815030301040d0300d10040100c0c80e211101689501e46844100e031001c00b00400c050800741103021000c0285890380e054448959070300c403084080320350040c0f10380040701c1c02540800081d04090012808100800c1d00c1100e259070010700401c80e08034503540e09a1060910303a41801801020900ba81c00e4401c0e080c50304016540c0c444810300c80d105214100d92289080d6000411201d1544883ca008a0406040001607100c0c0e201d203c1c0e100395580c01259559542156400d03c1e1649540f10019400030450f0380402c040d03000c11144103c0380144610b0100d950500c0d4054007507000313400000c0159210358142622400e010a48100901e52100794060014982c018a0240e03402161007840007547c0c0d02041c00640b600341e4010030340710400e5a07958142a0b007410040d028200243c020300d050104161807104001c602e0040b5010349074414028040b05030b114042030fa81c1c82311b483d05503015004003161040034060074400c000020308a60010210749196 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 466312050 1250 466310800 466310827
    0x10b15160303060b030702010504020907230313080703030207050c0913120509210d020f06190915200a0203071502090a080a12020624120118021311 65
    0x440e58110300b030540b030b8040041d010b5030000103544210040e8001142e079213040cbc030400c58144801003041d8288031028100200d40b4079001180f00c0380030045d05140740d981e110050620241800039a006020034000101c107800c040c0c1c5500a880158420003c50388960080002c2200b40d20084480c0e1003510442e15030358012030361a0000c4080c841791424600d15025154000c104c0901c04007002c0811000281d58062628408002d131012400e501c1c4042c00d414015007404585692014203184d00c001e04015040c0107103c3c580d404000b03815840b402d0301076482d41d01c3c0d072020064014140b8200c4c8007a003c810b441408141d1200f00c85103544240d014501d007003030307542c1e800d050a00c00c4596000c060b40c0c01e000012940c0c60352030b00c020151944c80c0061803049441e2138090303004841d2110300070454010000344006141d100300d90542003821007003c4088074018030042411004083c64607a660b41c02c0001c8403222212004d4140403050081d00e84003042e0750000600800d030b031100c8403100310b000e01c10459454400321 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 466313300 1250 466312050 466312087
    0xc0a112706010306090516230a0c03021006150206090706050915090a0306020403020310090b060d031806180806010315021b070308030a06170d1409090a060305010b15 73
    0x4050500140880e15012503001b1500c08881080700c007881c4240a080e540d410803420211402000c220a42141c8058066925409070701d5030301d0709004a00c070408040500910200480021011003007140695541c083c40e8900d003001c2000c00035001d020007140e51a0404039440d0180c42c125224149845405024000320721106074040e0b81010303051080c0c0d000c5555142001c4021030003010007607256400d500405042c400c030002d0382c40201c0e1608120b03600095400072300d140c0c4040d0031243c00d140c0c01c81ea0305040c1c5080c000035203006940c040458012a00c20b400c507618000d5a096049104072081d180d0a19595400b82800052700b4502d805100200310fa001c0d400508540c00c0c20041b0039407000240c460030345001919002215a8030010081020406061091000a00c1100c1080840140c0318a0307060321241c0e1908260700708a80e04503400094150902201c42402024181200c01d1030719465220081040e0f01044a0035428284158a2490108000300c150005044400d01d030105480d0002e40c002c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 466314550 1250 466313300 466313311
    0x30d110918090102070f0822030f02010c020409062c030708120c0c060106050703031118150415020a02040c0e060406030b0a0932191503080c0a1127 65
    0x6408001800000d222403940c038040714807d50a403610b44503244200d4400d60300000c210402d005511804001144403100542c07240354080c00d000808400714004500544101c0c94080c04560400300011228841e0201d522048840c0e400105081c000034508203131640308154000c0c00840050040b21668490840c0c4250800300804800b0325000c1c00c90b081c541840d81c04d81c40800810408140f020615400d400b80c42806c2480e003036464504140d19a800c2c0301c0c1e411518486011f80d00e001d42c2d101c404d5485e40c0403a000b0304018040d00c0a241c0902200035620720104c030040340110300b84103440810f5405403d21203104007008003128140b6003440011002001c0d0200794039809038440707400140e0b196440c2304810500105510845510900703042c1030240c0c41d41c142d148241301540c9000c2140c00340c0c11030302c801c1010340e00c08800302c1d50001c00310f43c910010007175400160440134001030b001103c3c44009110f920341403080310303000380c044081c078200701861403a11910940b5202d0302426201403010262081c0e81305 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 466315800 1250 466314550 466314553
    0xe03030f0418291203070b0705030109202505061618030b0c0a140a050d2d0207050a1e03120b0d2405040c080c0a180504020102030408010905030d11091809 68
    0x3091a1110024014151239100101c0d000000610400a01d03000d07804102210fa600300382159400c002c010264130440ca0000303503003a5240608240031a14402e14a00f01c1d030484101c42d2142020712087e824054007541c403030003160307040416035481013000c9121411283c01c02105800e0340e0301c0f90384115942d03001c2003402041250040c4081d01040c0c01001a001e40086507031115210940d81c0c050800721245282c9030b01c2007848440503d0010844004109050100c0c0307000980c82d9641868254503000703a2a00c02000320f44100020030300b0340d528030220320307000c4d000385d4a031032442c00311100b0002200d802140c2150402200c1000070003044100080140703005d6490003030600b294050382c04e4401c4071000d513000c40c2c02e54910182004815010402802401d00440e80c1a0307a407890b1800c510385800700002203c0c2101e4480000600390b80c02030043d10001c0840b04c0c0240016a101d150994984e44080003010714075107012003c5620380c01383c1059a800440250590904030030502081600d503a0041050016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 466317050 1250 466315800 466315807
    0x20a05010906090c0e190209120a060f291c02220c050a02071208040308070c0513111204060e030c0703060509010b100e03030f0418291203 61
    0x1a424490911014050400020140203601c1c05410804490b07000948030240d101c01d201006c1d00308a007010070540304040041e592120040403403444413500058941d40e00403c441c060034010550461162174211640030840d41c9840700842a01c24070010000110303042466003000141080c00001c00001402d01c501003800482d940011007403040200d0710740c071110300101e80001500d0300e40241d805225050600360f0810340000c00003551080684a82242e04200501080c140214003049401654000c8082651105035007000413034241d803842000c0c000c00e81c1c200d0900503802c1c140700d01c1c8130324407101106901e480404c411140b9006405401625031a5036001000102001040241a0709413180c0203814042d1440c2014000c42d20010b024071603507418200c010b945507403480500381c0c0311a06401d14150700d40401e0042895805102404004640300042c0421400081000c00e01c070440000b005201407000c0c08040844100c1004900000c10801e0f59540c60360b103400100d2024418901c02120b05 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 466318300 1250 466317050 466317053
    0x106030f0303020918040f020102151303052a0a1a040c030311070906060201090201020708150103020127060509030610060819143108030a050a1506020c0f1f080601020a 74
    0x4009000e4508958003207c840103031045580510007640550b001904414040c0340c02c00ea004400142c0007001001c12a00150000d09000480110000000c00202c0603010b14528810302c0d070f544502c0d20054414070038206032200c0c82e1203a4400c2c544580c4c0c2c05540f03911154515078040e28a15200b09150840d0300410001285a038100d208030801081e8590021903408028000681007071860b803c80412900240703100070700912840301440c11254280790210035080c00c10305d610301da10103420000d64030b43c492140024107590b00102070500d1007801c030142d4600d07440f02c2c0060401f100c03091080c4000f240a0200203903584403034940003003500000f02d0021403035050307082001c22046c00480d010320000c814a0354002502c0c042c1041ca20284415540d44d0306114207603150b800c00c0d4000141084221521032001403074031083c0f508010410203200001c01c08490f1900c070065122000300c0c01e003901894240620305440c0c40c0c000c40c403260f06000462015140031450340c003241c9030500200039034194807a5960420 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 466319550 1250 466318300 466318339
    0x11401050d0207020d0507051315030305070206131e14031b030a0b0a06080c0108090303040204020a170a0e12130b091809060106020c0909060f07141201080601080106030f03030209 79
    0x5d940c5407081c0c015102c050704103010420400382c510850307120b25141030070a07072a544444240000b80c03030301424a19281c000758400584c0d18072402d246201030503040b42c000624010710920b8500c030119141142d5030400d844503801800300031168050b50385540400075107404104502140c1c1ca0024000c1c0a41e6050310b25920380221403032040d00d65000d02951784c107040080035002c1c0070104080800b440c001e2014281120b40707607078a00001d44007a1096500050205103280503811050801034100c44141e40c5160046896009107074402d280c598901604401c40704a024640460305d1018200c0c0754240c01c603090500c0b50343d1981200001c42c0c2c01c00b0b6403494003400c0b9800fa0807403900c55662100117040c41d60400350020700780000080340d81c2c00703282e000342800755140000c1841036100c442003200e0390040e036504004907405006c2c9004030081d46000155070f1050554000c00d507050341d14407400c5414a981e5070170014201e4541b80b20150a602d481e0384034034000b92098004200d2144020110f01489940f1082c0c034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 466320800 1250 466319550 466319569
    0xd23011503020a0503150a0f0b10030207200a06080408090a08031b0a0b190605060d02070b0906010e04170405040c0807020d0306030b0c0d0f0504030c021503011401050d020702 77
    0x811206100420411843d1040404028000580c003500ca4004040c2c1c160500040142c96413540e00c0e11800749601c0014242e20945146400030400808040b400c00b0190083d0b004a400ba200b43c040050690348455050490880003000070b01040902480c0000440d04c01c007010708112040d45d41044000b401b940c0310320b5464041c1010304040c60b84c480c8190310f0609104040f520b403003030940050342c18070082820914803641c4403d5050941480d0040100c60300e0090010742c0150345c0c05400450040e80300b038010350103044040c0c4140c400308a1a166800c81136500c0c0700911682c02c149440400080020311000c240511000c400c0c0c0c01d03142031a4484000400780c0b00041d141d50f00203055242004417640e810440244545254202081018216100c690305400c00130b01000003480c0000b503001010205a201b03400c01c01d81804200100d0410346002400c044082200341e1207540707000700700344803501000101c038100c41d804924419440ca43c40b0041da0250070055903004030781e90a01c078040140e200d82451303 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 466322050 1250 466320800 466320821
    0x207060c050a17040f080c0609060901021603080301090b0904201503010806071e0c1103030f040308040f151725031b03090c09050a02040302150304050c0607020d2301 73
    0x215a00e0300d00309829482d42c00c480d80d005420647c001c0c0c107001825112031003151280d540655895030f480c035405005074a05026400c002c0700303242c5081c4000051006a03000746050b10079400c818080614040200b00304c03110300760340203820500c48802941c01d05881c51040c544c0810301400300560b40107400110000c0c0c6e0026400301c41581c01400800031100e9110787c140d41408442c0c65403140002407104010028004488018041c10400ba824400769504105032240c030490011220f43e90ba0b00c0e0b1030720680d2030304140328421001030001e1000ca80107031005c03010904c25a455489032104900b58100301190b1802401810328001c1500c034510076070012485414203021113440c041032a03442d1a0148030040d4129070000c04140c0741501c00710002d1a00e900102c201c402e00d20300403410780c4494003010024451903000030f5100070b5013510b031070800450101843c4034500135426200d80e00008003e01401d4440c005000b9484181c420307030f80c070000710450a5280003c09002c0601071a005881ca2a0b084a5050b880c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 466323300 1250 466322050 466322093
    0x705030a030605090103231006031b080c060304080703090e07170105060306060a110f0a0b0403020105150609060313060c170921070302030c0607030f0b0409030207060c050a 76
    0x100200c00c80d4050150300d005082c1607401121541c59626005101c0e20b908516000d985074a9030750700d031b17883d00401001e0703c40381a42c4010070010b0384d60310f40800e0500203600750050300c044108002440740c0010a4071950420301900d420718641e5581c0d2001c041d0307400740780c0403000e00c007982101080101e01002d00500c03c000b507403111040303001942e41500c41e00d6816440248204402c008000301da4550320140c810008250034604d61489045081d03d003095281620b0811038031a903103103801400130f000c40b242d004500903002044180c442a000c000d0881c00c541200390006010090030032079061000c021540886004500618078007580e9031882a201c102c603e08002929120040703849042543d11640c114900c0e9004090f60401d10500201ca0703c2d5245241607100c10102d00c4030140b43c003d000315202d900703400c000e9610354581000054010910606180b01013485c100c400609400c4c14414501400e0f01074000304203180c90302e80300719101d000c00503086a10780292504100022942401c00d03544681d03014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 466324550 1250 466323300 466323307
    0x1005070305061f02100c020106030b0a090c0602010506030309010f03090c080106141e0d0201021002030703021207020f06061c0203011e18030c1506031a0402011404050612090111070503 81
    0x4042003208400f02081107680400c1e1852014007071340000c2c0c9800c243c1c2c9413403000b017000ea110b2803003a40148125413000c0e02800044040004966040c3d210410301441600d4200300f07143c8400e0b0882c02c0301c1e005c5581641551041101003184c0d03000d102d4a402d803005500c3d01080041a603902c24003012801c1d8400c114a0391610030500c84e006480305040700104d0300fa00c411410321140780b4070300c904e4090881401d00900000c9151000d59100303111007104510810710641d44c908009034010002e43c415140001c40c0080000031441c83c42c4003040007104a1132800c000c0855031079110410114000d0f6160200d0603102d4000010010b8600f801210b117065114004014020142050b100c1541c0360382004801c100000c50040c0b00207a0498200c03003440b80c006011100140c002c8000304010641038002078203a00001025502500d81c02508503c02c52007030ba6485015540705144e4400ca0050f80030f5654445402d02a01c0451469042d0161344003075283c001040b0003124070a1a07605600c440d1041d2503a40002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 466325800 1250 466324550 466324561
    0x70618050706020c0f090a05070e060a050705070e0c120702010608011112070905090c0c01090b130201020c0303040b0a030b19030302150903041a031009150302041104261005070305 79
    0x520102201e8202030300d00640020785d01c40060001c401c01815145482c0e50f410104005c14130030ba2480f0381039407024042a59401c0240c1c0d0241943e005420112014810010003252140720081181c1c0104400f5540c613041040400000b40b03068030060560003150750360304002940030000d002d42820703114403040c05a501c2c0380f04481c034044010002d05c16418006141020042d40d00c4148019a000700b00c404041d8a070201150200d015183c0b41d0400742074282c51609102164900360700010340f16100340c00701d481399190f940a140e10782c060b42c4281405100d0134070031840903034002d402c50324444400a02032068101094400c64006145400980043c0d2200000b076001c01c01c6503006a4000800ca00218100703403a102c03900d0800700140d1800c541840c07020001c50a00d0340848550340c06010014014080c1c01003003a01c9030344082183c4403c1c0d12480c200f10301c42e2080e841180c00ca40507aa8403440c8034102160404100d802c42912040c856128401e02480c2d203024038040c07040b2030080807590740118803403c04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 466327050 1250 466325800 466325803
    0xc03100f03080d0f142802090f0d0501090614010801050601082406040f0f050114040e010308072310140108071202010207081f14270c12010903081b0f07061805070602 73
    0x840d00f0400031544100031000076991859289e8121171003c480c5070000c080c6030324200e409880b51032802071440e420840d044a40225090400d0f0590f9038080013003106503501c100440302c00e03400b660b0301c0c82280760341180088190803420f88800c1e01d2501505245c03078590fa510001c4021421303940204800c0001d140705020030340c0d000b4004403450105180c82810241041c007442c0c0d1840c0184001000c084001642404004200c1d0f004190712580d036a4400d11a02501c9845031100b881814444607145880910402099510b4009041e40d41c0000142201410700311490038807451820264158410038000054016040200700c443c4020f400781c02c04001d40d42400078007510100210365a0180074002040020140e4450040c14980612410300c184600c841c0143c1c1841294403503a900301c0c6081002c809403402c15000350314150b1081e03454140c56541d1800d603c0940341d511012484400c010425540c1d81a8608054a4014010f80e00081e410b00020026103002c0d00307015003242d4075084030300c00708040c540 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 466328300 1250 466327050 466327111
    0x70c15060617040515061f090303120603080306040e1906060311011e0e0f0604120c05060306031506060415170c04050105040b1309050c03100f03080d0f14 68
    0x5400241020781c01c05566160b01d8401a02c06445d00c42d10300d00c00104103665000200e086050301101080400f0031700200203250302501d0205a010600e102c9001c80810510b110b1441100d4205144a01355118941044041c0a090480064500c181e0500781110030650940e0302010748982c1c000031318076140d0328007070f180c40e2105400c41c0e040c0400b581c0303000c1010190300048403c4005500c6c0c4102e1001801000030458140e01138816004040801c0200e2a004001e950850b5540078003010000e4581d560100710b494030049070701c16055007003a920607880f402100f513100c0e00003000074400d50429480f140e907800c1810325250a54000f6811110501e001b641c400c06083d084030006c14968a000e08042c000780903031080c0e228828102d070b000101000034000700c41c1c1450107030042e56418003050030000e50440d0203400036166407004100c01000068510403c0303400ca0101c1e540300400e14101400480c1ca071004001d00b04403070f404151150f110b00742c01d071000460944100d121051101c5213400d441c00004025a = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 466329550 1250 466328300 466328327
    0xb06040f2c0d0801030b0714030a0c03050a2f190806040e0d1b03020709020f220501080106050c0c031027110909030f040b040504141b03070c150606 65
    0x104454002051290f2010390a0f055039000306000b002501d031010102c2d000048003081004000000c001e100e10000140c0040d0801d41d03169505004544030004090100d80c050410800c0200c007001c2100c2c008880900342c040c009180f81081e03070501c0e580920042c42c0105070020040020003003800c01007640350501c00e9600d03600740d174002000f1060445c64082e0580d800460308101103503c40031a201058401c010700800f03400c90039001d6440700b40e022807c110f650040c9000620fa04c0d1000b0104014850b03101104044500580d21802c050b4a000c0050b502948100c850341540d0207074800740040c1d41c07020080511000c2d501c1c140050500c245800345481088101c40702075411301c0141c1030001040c0c1c0c641d800c1e002a5421518607420f600c4404401d49107202d0700c5013071000400042030016800301104c02402c110ba00035a0244840c3d01e070100f6941c2201400c56285d8814000301e0008000c1c0540305000c2d55002cbc4150803e0700c01d0030007507260082d001084514000166417120403c0c072006512411698115 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 466330800 1250 466329550 466329553
    0x120c0201200a060203130501090c06090608041121011410080c0f0f040e0a0c050415450204081905031603141b0606030f03070b06040f2c 60
    0x850101d8100c580307411581c10064060380d000b1012402d00c10960300880344943d4440c1c001c02c1452050710f8034000103010383c440c1e040031403000080054803a016061541c8604d80c1b100a1058243c516000c109046030715542c010301c001a20180d144560800b40b040300c00100c0b0315180c02d186894400380c41c4806032000e0700030003240c4d0860f100d2190240c0f07802102d24140d1200b100e410640c894140c000c180140215408001e440c45600300c80c0050000580c8010255041600c09004034240c070b07845034446c3c4400d0b00c01c0c54034148801c2d000218041c400c20785500205001d900c0700d102e024421f0800251250a1003904003a103034000303010007411004003e5140886101551343c80d104c0c0407030b222035840340a03042d81c0303c502071404030504081621885624120344400340450781c50b002120360040144032a0640e4400502c142c2d40852030341e203030010360010210f801900940c5050220350f0b400301c80007006441d068100d502c0350880441000b01c0c2c0182c0440c010081c05e00010010007280c00c900900d01480300002c0d6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 466332050 1250 466330800 466330847
    0x80606090714090418020d030809010b030a03080601050c070b0c072105120c01020d02030708090c01090803090d0611040605070506100302010c32030301090c0809030304120c120c0201 80
    0x190701c2e81e600f690079602c8215000911600402c410803000e041205009600078183ca040c0c0e0101a085000b560048060b00001c2101b61b50810a040e6540d4110b003000e40856500000202c03d5840785008001c000466010307100b50039942c5880302130343d8020345980c5045400c1035000340282031002e4015078480a2030204032440f910075071501c644401c15440d0607841140300003030052a411094046600f035850084d011540ea18041c90001c205660035030342441d641c0200c0101400f2507110707046400070754040034003451414402c14100030b140003d00004940c4075448003041c1c54408140c0014100800036a2100c65440d04640307017a030b0400030000c1444902107103800090000d40d0384150062a01503110100030b9005410094155903942d400303403030f40140011528038810200012020754103c88180c1020f1020a07030101c004e80362450300f161848030310f500030320005010510311440c0045010700b43c28105c54054250700c4804c01e00040d0169030340032401c07445c020780841d60b1000b0803021780b803018501e0b5904d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 466333300 1250 466332050 466332077
    0x90d0e060f030c09010915050a1403061e0120071d07050304060b040b060310140312070b06190801090308010b03070f030e1e0a05060a11040614040504060806060907 72
    0x20324007000e0102c10f10a54040350f102a0b590089907142c2c00381090001007404030310300020040032070703020301c3ca50400519003c0001c40501046810b6030700610004195009058800800700c1c40a11100016410050110f484241caa10004034251260101501038020103080c5050504c0550800b500800108011000c000d80d11f6800001d903030f001f5501c46004254074500344001703406841401d001ca40c0c4038000006114000507552000340c01c4800750030802142d8006501015222403442d0700040c0b050200704840f0001449403451582d00410007001a0030000300802e2040c0700c05407a81080c00030340c0d941c170800c0d001d054100201c14010300003140c41620710315080400400f0502e01203998024103480f40702e00f0401980a04c4000d6a0101681031910340409c40380e240ca6949005d04009c1c0d401d03001d207501140140c4030034001d40012001203940b1a242c1450030300200d44003010002d682620718414000401d0310760760760080800920481c802840e0905000b410003450b4036024180c9410f003c02882100d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 466334550 1250 466333300 466333327
    0x10c0c051b0102011d0c0a080102030603100915020729190c0e1504090b0607020d0807060b0d08030a0b22020f070c0b1c0509030d180209090d0e06 64
    0x98107150909006503180d62041e00503030240c003243c054909171040c402081d034000100042e0390542c41d60201c84440115968041541c02c0340300660307450350503801000c01608c0b51221500100b40b2684900c850714140b0510319044412a08103080445800c0c05000c1c0d2420501c2441003000800b07140e1015400395402d080c4568580c00045480c1c4038152612400b0014446000b0200c0e400203000207000c40d4401c00700c211002c0b202d80c0c4103000e00d24225290200380c20303990801d90141d940326030b8090080d0010031150380f030750a890341005904503280c0303031548689140c940365400f01400740e03480341070959182c0c01c040103c4019580c1c226041800380904201c03040319040a000d50400410780003000698032102200221035510a09001a000702141c840018031400643e0003041a1100f000c004440f0f000100303e00d000b40c40742907a6003141075105020010b05810700b03a01c20900c2c44000034100466080d5503010641c03500c4100e0b0041072580040341c54084d0310350000b852410040044403135624020000c5e9046 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 466335800 1250 466334550 466334563
    0x7080f0406020a1514010317070f0b160504141203131d07030203040b07051303020604170c0102030c03070b070c06050405010b0112140a090203070e041401110a0e01030b060d0e0c03010c0c05 83
    0x15100141041201551224420889c0e0031540c01c528140440c1415040907c4c08034002c2d111807004030602580003000c40d00c600c05a0341038030a8045000300c00d812150410010000c0d0740c2a4400c1800100300c218a407103a0f1680c16001401c0710320480030040300c444200003091800030300800600d401002004006440040126840b8901d400c0041c0c460746d800d40303482144901600004d4002c81d002801103500810700c0c10808840c5070100c21107103205100d000480e00e034052440e00300c905920500c402c0b40002c000c00301c5070758040d80c54603103044107071940d4039900e007910800c0d5400d5440380d41da08104c0c0300b1940e000c242c159182007000e00920141d0785600386144000300051620301d81c40d5688643e00210342d0103204100043c0a096211522400c00c1d003071034013104200c80c00d0004175618007880e80d07514664100a8585043c09601c9204c26a140b580042d00500b014860729079007d0400c00540003185e40324410920001741d0240201161110881451300f1241e92100201c01d1185195000d400200c000810 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 466337050 1250 466335800 466335803
    0x6060504091109041e14070f03020306010e0a020d020a17070f120905010219121a0a0603050a0902030313031b0f1503150e09151b07080f0406020a15140103 68
    0x58800d03644e6040032084141c50000602c500303490245d8010900c00000038114200001e030701510841d6a030340010200401507440000e4140d04020010400030150115680c0d01c01c140c0704c8007614008504000300c049070300448945004c11032001c0d940411039032008890f0340c000400c0c06d2002e44140520303400342c003140c03070b10294842d01ca860f021030008000080d01652480070850046090300e18a01802070007501074490704020251900c0c189401c41c4684072070552503198060424004035082c000100c3c0980001405001c1d42d42e11030030008016102000105a000c1099040c40c01175415440c01502e40c040e85d5040b401504a25082800b034050079850800480710410040301c4182e1413034200f64050031113071840c00d80345003003c080020340c0f458082807544140c08550943d0114601d810564080d12002e4940a81100828400300c000d980c020000f009041c0c0221002da04044e024400544294440d0b0060801070300a041d24104100c4030380407108170301031110000e001880e0b9a203100114071405100 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 466338300 1250 466337050 466337059
    0x108010b071104020a03050921072a08062734080105010306180c060815211204060f0302070602360d0b1902130909060605040911 57
    0xe600d410440402c40301c2942c000050300540d200c2d44044400340082c10210743c080c0d02800741c0303820f44082c0907100c400010ba41c50907101c080e0400380942c855500400c0c804180000e9070713245542100e120901c01051100802d22440203110601d000310241807964401c05a144804554191000040d2000300301004800d40e80d4805c0e00d0281a801e4041c420031002a44c075001102150f00e0101d080307101900114103880c054030007032066600c00c51f80c070441020755072405800081403000610a0320f11404426410840002941203040c441e100041c1001136091a038088420400d05542c24084040c421035020391030707245070142000d14018000d4400601751040b00201940010b02c4401c07c401541030341d501343e803d01c802110a0703015040d1000ca81c20003000324003c4d801100c070348010903d44000840156039100c4451417041c1c4482e24142c1002c801155581d901c0b0341c00740320988020060130040c40090028070800300700240c0c14101801200c0454109a0155040807882e0011039070403541d6680401c0240c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 466339550 1250 466338300 466338307
    0x41b12020d0b090c0909071d0105010816030b03101a0924060d09030302030a1a1003090204110a17010510081906090509030417150f04050712140d09050108010b 70
    0x1000503003812070b800c07201503014110034244805114009040019182c842c0c1230b210311401684400849080244945400180c800b070019410354020070002e4241344c0d40381408204544480300080c10b007400300214a2105540300c141079060000c01c00c290280d640300703541402075410030600801401c82c41460222125110b103403503500031384988040f10b002c5480d14000b006112502c0ca8018044d503c2507410400880c10042e0b40f000c00c441310b10f44100100701c02840000b80b4010000282c0c0600402d03101139900c039560300341542c0d0b40c400340d01c0213069414090391400410762a120401e80f41e804c0c180c001c14002c581908041c0c0c007030343e0410349864000201681d0400740f080c5904048000d40310320340008032150b051000b48104603a0000107001030721002c19003c2115907030f2006407039507180d106018080440e1400007140f0004216189a0b8005006905407560386440b4180001d2641841804492802440c410003d05810502c04002c0010039440c00c80ca000e03144c03500080403100103001c2c0720380f400c1000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 466340800 1250 466339550 466339561
    0x12060f15070f050732130b01021212220c030609050c0a030c0521030316090b1224030a1401060e24010503010f140f030105041b12020d0b 60
    0x214641400340e03449811141c1c400e85907601152124840c0250241c5d40d0030220000700003010003042001500c40107058091124003402c0e110b0081c2005842c0c103030544c0580e0410742e0103551480018841d4216075043c58046080080d032401542250204198803941102d0445000442c800031030012a50818400f2404641e00d080103814a0310134039030182e001600007000420405500c0c908011601c089401d1058504040740c5840c0050980c040207106800810003d19403c3c80050700403804120380c03801e42e500c3e54407080310700241d42c0102d10204900e0315038800c1100810700501c0e80b01502400c456540120031610340032903520a01c040700200600546c40004031913000c00d51090006006141181c0c6ca10306001c904180c00586050801d4080c01c01d170000c4094950145044038102d9a80b8030302c005c00103240c01003040404803094007951f8001d403d49810499a0f030309008450081d40a01c40c014281e908c8400350340d02e046410b601082c0c02218643c03004c00584d49100c10ba000040d00108044001c1d07880 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 466342050 1250 466340800 466340813
    0x3020306070813060c0e0303070303090b0c0a0816030e0d0203030a0c030b0609361e07080c07080f07081803010608070e041b030506040b0106020111070609020a091112060f1507 77
    0x1b0102c182c0c1500c40407403460145a0b154200100d024050340c0e03903500584400403003043e9480f498400c00701140e81c0714003059000740055489842c484051034000b40c6035000170407490906400b82111401644040140100c9417500d12460b11102600c3c2800c02824282501040c442d00880980c0e82c40341071111106000c00c0111000308402030240c0200351800182c0e1200103481d4001030b9400b400d110745041d0303070000c03940c01151040d000d00000e031942a15a0b0300c800c00e81c1d52541c00b0f410215008402030240036a4a07580e0409420110f02c904440ba8640a109868109040d10748407200d110313a05140c01001032450120b41c000907030f07010003001d501e641e465003466204182c05884043d020713022010f0000c2840808207100740114810208014943d990308000c038241d601840c00542510400c11201d800150150f00c032848252004e44110301d510b699440c5a011542c0e031404011549000040c14604011145216640316904442c003485481c0380c4004141c03200d10311002c03480141d40005410050003903 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 466343300 1250 466342050 466342067
    0x41106130e090a0512070308061509040603030306080f0d0906050706110c060f070c03080c0313060e0d110106080a0f02030307080c011406010c05060f1e01090603020306070813060c 79
    0x400c2803456401c1c0c10b00e4400199204840107040d80e15000d00c9842c1c04a201c210000c680d0700710f030180d84121254942d03a0400c000b56007032020448012004001da0080740d03c81e805103600841c06900e00017400381c5406905070400344141854401341d0007000e016003400c1d800030101c5050b2800b501d019500c68011749040c2c00205500c145110f03050a001c5941c0788201c00c00a0820302c218680240ca0b4450f4035200e80586034080259002000f245d0054005840c90300342e00003465000c0300c0c440301c0804805180d10703610101c0b608003a200c03d454100d0354001c00c03841e400081d1003c041107c0b2008015051500d142036480da41030000060a650038202c8107801e5540404c01d48402c40c2e04400a15070329168034401c60300070040c55800740d80507554000010f865601540020104540100141c50580c3d100c0440a500701030051151909000343e02505980c0ca01e8200d0050207041540c200040311420360042601c2c1020003000d440400004a0800419030078074503056150fa07078043c41c0460100d01e4040150350550 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 466344550 1250 466343300 466343309
    0xd030f020c0715031503050309010c2102010c02060106090b031303030e06090c0405100506030a0b010201062601060b0a0221190314221112030a0914040504110613 71
    0x8108a004140c60b080300c03440c0c0d4080d800381c1c0c4040251600e1460179036043c24541c130000d4400e0308140007030002035020765500d2003803510030400100d180310024400c19000e4112510b8a0040c1c0d9204811807105404010300f5001d0b00f01c0303041c240c484514000b10850b00b8400240066031a100c0751100d9404c05005c1c0c1c108018081040b02a0ad06d5468400680d940d140e04064400d440b41d800d220100781c5503076075580c0c500c003501c00140c482031455440c081500040d12144001034110340d80d9800014000b401102801c841000203001d54041424203120070f401d50f41290041004408204220414140c0026002d1204c8400b03404100118012040d0004140502108480980002c0040c0521380364142c1c460b52141184020290403920780c01140241c990a460704481c085501e06105030100e810f1040388071701401c0051019044249088072241035030440002076000ca04440c2050100740b080c248088040b540c250b4041046140c85e460b8003d00c5444409498018000040c00b400403040248520001c1c0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 466345800 1250 466344550 466344553
    0xa03031e050c13050f06071e0c060201061d07080121080d0b01020f0a11010e030c18040201110c010909050717090f07080c0a0515070f05032502030d030f020c 69
    0xb490310307040e9504903511420b03020400803241e00d004140c614004064201c400c50190465003403007400d640300135038460b0710500c41407000f45481d0a000000d10160680d00070b40800d0380041002450103030400b01c0011282107621415503050700700200c02d07501902c051b0440e2200d01c0310341e41200705c0b2002d00042550b4075001a0a0a000180500725041103401091050500380d00320303003242e11803015445d262600000001c10006c60070126050540c8206050710280400a064804d00d403255400500407480c01680c801c081700c400820002550381240c1c1803414040f82401628900340c0030380008103884058040d1540603a41da801240d603c0d03100e41c805e0030030311840550804160400c90002550352402d42200c18031803044c0000424150804683d401e403c0710080c0285001d641050300b0024500e80310903074905a580188992404580d100c0e4001c0c90311070140740607503503d504000c10104c5580c40b081c40c2c1c081c1e6149010000c0e0040c0c400040054801c421490005921850054060086d114085498078107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 466347050 1250 466345800 466345811
    0x601050c03040f140118050f0a080105041505010f060903020603041a04150e150103061802150d0506010507150914150a0506100f11030708070b0709080f0a03031e 71
    0x4508804070390700103440c03010b0361400d10981d40c00011188034070b0f480480c51840c02c6e030241c10402414400d500e0152500c2c024000c6540d5526444800d08540b001c580a50712480302d075044925580b80e5110340da0141040e4000e000a40d824064050580c4c4d944d03101c001c0c01207900000003420300c200d4650202c440055030043c148070341090b0605404100540b183c0707100980c90100c101c3c00403400021001e83c81c407901500c80c5a1a8a1526014024090070070303001c0e111f500080ea40c400582d01e00d842d40c0700b800d607540c0c3d020b6100c41ea01e0900800301d4030024003850501000300031080100e40c04010129055029020200300e14001c0d10f828a50f141c001c000000c2c1e144182000e4201080b0b0711550740784109080740e8108400d070b54001c20418204204801c13a00814180e80c0910500c80c4100d41281a440100040701d1500c9201d507951103156219000c180c4500d10040c09020352030382c0c011500001400c0c0c02c002807440503001001280c0f11114510005d00b419690059685d40c50086040706c2e880d443ea81408100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 466348300 1250 466347050 466347059
    0x60703020f010e0303130201050309010e01110a170105130f0603080a1106060d500f12040506090a03080703030902090c0307140309031605070603200a05030601050c0304 74
    0x180c501c549031100000d5424101481000c2400100b035a02c202101002880e400d08aa00155010751018003e04015500c900000c0071318602401900104199280069582e09616000070074020042c0e00b03030a150000c030320040001d9650030042c1c83c0680310b000380001741c0600d100700200061129030b00003842c541000c00c444880d00d4028142e06c0780b4544880030ba07074542d070b140820002d420358203800c0200362007440c0d200303d40c04100c1400c000034a4000342400e01d1115240c0301200f0f02c4413030300582010054200d40d070f180180c920284602c605514240004100c4101c20701806051400b4070300500703003c1d100c0810104002c1c1d03140c3c2a424010358000701159500c944038140140a0101420142c0c021000e080200321401d00a40461380700d90215929090100603140c02c18000340c3c07024061080c548030501c28100c059080e500c0301892984290004c1c0307407080c80c014001c1d05a4480300c03000118003248043e1005007000c83d5040320000110b23450310658030303691080143d429001c2e0103085603003440085000f05 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 466349550 1250 466348300 466348303
    0x2d090d052104080706081812040510030b030606281202090c030103151a03062802160f020307030b041514091902130c020705130c02120307090506070302 67
    0x240c1030720811100d03610700c006451001d0400e100d01d1051455a0303001101c01c2000c02c4c80384400c1c58009040c03c404450003000b42c01c8141c07030030b80c0b4011040d40d4040006020000d92604080c501381e000014101886150452000a43c40c2c0c000144030764001c24444042c1c1c4415a0034815007612110800740c08034200b511201c1c0000140d10201049000782e02040101d03807004800d0b030075030b4100c0703500c8100320030a000c1c07980711032020340103103103602c4c1e02c0007034050140c049075801340011823040b140401e100011135155a00c860941103040715014415104103d820034054003a80001e2600790030805040f40c282851003c20b05c0d2920075440a0800d41c002c109000401130f03041c5012000160380b00f0b05100f40b010f007104402c441e03070701682d2207211a40000d414100303810b80a1035541c035031800107203100d5180107007084280583da046002940140c020000900c00d91074101c480c0701403490100700c00c010185c1c80d0000030350345110322160803d4070080480002c102c588501a034002030800505210707280c2541e8a40039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 466350800 1250 466349550 466349563
    0x10141305010e030d09050d080c0f090a0905010e04020102060601210905030f0403030f080601020d0c020d051011070506090d050f13080d080402040b0d05060604020703050d060611060a022d090d05 85
    0x8031040d0080c0786a40712624448c0384500d0141c8070070300505103489140074800310030382d00160445803ca001d40c00d0025a8031900d1080500911204203c00740b04e240a00c00242080c20080032681030208402c0a01a45110800c40e500414004500000c004040307081c0b0519500507200c04840000740020040205a4002140c1070003100544a1310001d071680001640c0f03401c488800d600c0080d00c4071050b034000d46400c1d04240001409102a200070341100c0c4034103005e6070103184ca103410603000000e0510402004024465010f01c80b0740140c0204403408000610314401e507101c00000460105c2d140503000402500d02004050300000c5801c080d918440c041d120180844080c0d200d2450002d0440c03039070500c81907400960390b110000e8007151b076a4408000003504215010780401100707100742c0380b8009291090f8070160005c3c2d101c0302e8001c00c92480c0c031482c083c0d0007806d95103428014030070071149013035258403440900c00ca070380050071001c11100e0685081c0100c0d45441d5000b06032145000510a0100d2813 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 466352050 1250 466350800 466350803
    0x3090102070602060f060622060503060f0901080d080402180a0510090c020a0201050d0b040510090e0a050627031b0610120609060b0a0807050310141305010e030d09 72
    0x26211000d956440c03d03600c4810449500c58511a400c00250b0649002c1c00100b024030b01c490400c142d201e1540051480725421030304480d004c958000700780030a43ca81340c014401c2c004000c0740c14000395070420026030344a88085406a0074001c50350080313821076a4449464050140d0b50800402a02c1d00c07010220103003e041e52620700b0340f024044042181c455600400354950100e400920703196a480d40111100c2c0d00c1005407c05855507111340800591381c5000b60f50041d29003014128a80e0300f00550681282d440c1c140e0241c059000020140c0020b0011900c1580181c035413170990500d5032004e10707190320b600300080b090030507020008032404d04004406982c0102505481150415912160a045030310400c3c0140008480050a03080c0000c400c0c0d0440d0700818400c0e90007040f00b50304a40421111a0310303400180c4943c01507041845141020030008140c00040b603014460207100c00c0010914800140c101d582c030440200c1041305212007500950701c0038409504881d552440f40c0d029000400d1810750 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 466353300 1250 466352050 466352053
    0xb0c04181e0c020d11010f060815070207060c171e0c16050112020d1826040e0601030506190f05180903030f0a09050601030807030e03010e0303060d032003090102 71
    0x5600d401e41c0014070884011011075001028101c19801d0241e4848400c00d500c12110740d02c07000c003074501c40d4442c0102e01c0100060f0005164400d110b40d41e4550b076580080c0039000310341c0594001c010446d40f0070411522240c0000e40c002d100000d840350b0180da44075070f040d542031040e82280755280300084000140a0300000c0d00650303180300021170a003c640000e0388107060004540c009000d40212480e802001036051100000407540c8100d0b00c16105140020001e03110320107508002042d045101891001004506044a1401d070034000300135400c200c050003090401d9a5100000c0c0103469284500d2005104038082e024915a240601d01c9418001d010b5580190380c19010851088400c00584d4001d440250155055540c2d40284101c036000042070301a8158842800c04082401441018041c1d130041d490b04e540e624050401030280f94000e50f600b8000d0f80b410b22405c0081d2400700c1600e4000f4802c071a82007210b0094101200c140c40c440d0b0464004076083c1c101c80d62001070000040400b61000c0c2c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 466354550 1250 466353300 466353341
    0xc13030605040c1d060919150e01150305091e01090209040803070e0103020c0a061e0203010602010b01080606091518031005011716030f080f120106030e030a020304030b0c0418 77
    0x4c00d01c1004070010350f4115002503d0768042062040e004c403001c100c206440100252039044100281d414007000d5200703a000c14440f90040c81700e141c0f00c1c0c0f00610440124141880f160421010311503a43e00da405400d802417581082180b0102400c0d0890790b00aa001814050755007464104a20305d80c2c410ba8041d0040340101c11000032030750007030080d201c1200021001d0040b800d00d48d143c0102401c80b038100d594083c0c852500105070390219202450103040541e00004e400107002c000541900340c0034048038415401441100800d680b18803040b1100e00261a205445100c0500c040703807450704080c2c0d526818060000b02c20001201684682d04035019803c0e40002140e2041c030301b40e100c007502c84010455410f40b410501c081044054a030000900c108080c07407401008803400103058000c0c0e0308045040c1241c1c0010403400d42c0c903004100c01924144c01440c54180847d001a649219511000b03140d19000c0c4001002c132895102610000e1840780c410501c1910801c0c0c01e000200450311511010038000c4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 466355800 1250 466354550 466354589
    0xa0801060b041517090c041d1015120f0b070806031b0609060d1406191e050a0b0307030e07121e05120409140c030c13030605040c 57
    0x50061008a03040390307140c649490709000740702c4900c21036403519105120b4580480001d08842059a502c240964009004800758590420080d01c82c11703400c6c2044ca86240710031203411400415518080c200110000800b4030884101c3d28482646602c2190100c1d8070b0b65846040c0660390381405d2a01d4400d41e400070140d52140c00a4070051800d54640e601a884050220301031900e4040700d42c5101c0c0018046410a000c05000a40320340c0f02c1507424500c1502c0d16190303100c903100c0e0303c3c441343c12240072070b80301c042c699000080e81c000c81d203a80300d0361800440c0404441264400f04480360090880a05181009174494800185660054a42e040000c1c80c1116030803c0f00004a060f0041d620303081d0f089500c0504588450040b0624204a00076443d01800100b00003442000000c107000c20501c07030b1a0b26141b5121140d002c5800c07031a200d2641d21091406c000c04110604110381d40080e20304100c6444186d6003004404e41001d035003004013880d1902d000e020901414801301805c8542c8030ac03810800c0b00302d0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 466357050 1250 466355800 466355803
    0x6300309080d03270807023a050d0309110114040f03050d0807020109030e01210e0717010504170304030c05070b03010f050105131403150c090913030527040e010b0a08 73
    0x42c0e070f00180845c0e5040c400c2c41c0061804d80040c0c100c2d4450704e83c1c0c2e17103656045e00c02144454003606940c10340301c0c020701e080030081000074880900300000c03504081041151544684501c02c4806521074100440c05030101401c0041100343c802801c80b086031495040d40300c0ca481e03950ba2180d102440080303170748800000d11092050040c103074010b5166980b11a81d036411401565504141c0114041c0904a0700488070a14114424403481d41010001045218500007410303124203200325907810b269060208000102d00b000d501442c015002900c40c03030f6655190b050494410801000c002d085000c0c109000800e00e0030701001c1c0d41690580d104242072103035030f900155000e114105246000049580d420805450014000714815001a0596001c1c5000d0940d003880d05200300c40d80210742402103040c00050801c03190700e40c4d100d801020f19100000d05620060301c640105210074054013068100f10328242201c0400302d0700d00300090310a1105524815003240130305a843c1c00f030b5004281070351000541000 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 466358300 1250 466357050 466357121
    0x100c0806091003060b0a0306020d090c1403070b0c120a020601030209060409030f0309020111010c1709010b0d06050a0b04050112021207060e0f0409050304031506300309080d03 77
    0x1095011402e41500e107603a00400b501000b0552944001380e00c100201050749030006141400213580c0c001441440303031421100800450300030340041d002288a19440303444c001964001c2e500311001403511a040714640d28540410503820342e5032440e010031403484158002524034182d80c401ca810041c17560700d48050208a589140c0003500150001006c1c0246900a9100c07041c41d50042c5080d0400da88140d0500e4295001d0f0064040020384004030584410a032180081d000458100203000c0f80d0180000251040824040500602d0340c2d0710120303a001209601c1f18003000d1f40174000344541e681d20189841503100c299410b9000c1c0e600041040c100a1001c640d003010b49030350b600d03101b8600484000380044c813072000380035540150f5542c1d420b201061041000d04000d40c403e10001d035585019600c0c1e08250303041d0781d00443c1102904035890a0421007d0703950740b030324000310103540f81e901900d080c200da0b91201a8805105405480550841d0b10750541042a244864403480700040340820b000da01d5000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 466359550 1250 466358300 466358311
    0x2d090106060513140117070e01031b050304080a091206090501150f150203040f08070303300b042a0905090610030908040902031e0a15140103060305100c080609 70
    0xa248410b010200013500407660501c01850840141034104811019020007550210701140004040315469a07140c003403a41c3c0d80d03617200d007402c502c0540c010740034045010281005198040204641440500c10300f011401054210410030089031141001d2000b40300c0301c2c4080d1440e500b4170306200c552a031050700d068116a070540c203154680c1d1802c074180030080b503011003c100314042000001908540d418000000e01181000340036201c1c41c41c540a84003440d00b51280950400c02d6130b0007100242402440d0f904850040004150811880001b400230320f88442c68850701001500401c100a030440c0d60502090380545681000035110020803090000c04c84043c0e6221076080c1a2590487c0b0035044020b03041d1061a8450a2030703220144e010a03a0000c440a03100d400d0021214405600003041031034014103a01000c001c2e03200c0b44455032281010900840314441428024821503034402d50181c8021608003007a10400ca8801002d0703000f41401d0200040000d4084001c50b07a245401154140180f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 466360800 1250 466359550 466359577
    0x30e0d0f02060903030c0304170f0d051603050702090a05071b020f0d060603020a031410110901181d04051e03190903020d03081905010602070e2d0901060605 69
    0x425403582004800c0d0f0101841c980c041c081031103044010202000604050001e5020158828108441040c588582d0145807440c990010325131001c1d01e0340013422a81c0d254010300e0f0750310f180302c40c40c28180e64501c20207100a4102c01d42c84100031001160b40d0246024080b184e4031415207150031a6101c1080b001d003807010758840c0b1002000c0c007840c58040200520b07a4403440012540a5894001450410040e80240c541443c4081c04051145050000c85e82c1005454001c010600030894401001e004034007402d414480044405020342e0340c0201e03000020800d40c0c080081c1c2000c41c121800d200b600903601210b880c410100c071465017100f00512524032920340c1000310300707000d61310441c03000786a440f0400e5000d01c00c0c00400030001d40c03103011140c8484c0d80280c80e10601810800760003207000c55000f5904081518000c0140041540411a0422600881c0e406032080c0c0b1012118100a2901c42a178034114000d0000c20100c030110b088654418400480204501030780c2d0740c8140c60030301c610b8030000c442 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 466362050 1250 466360800 466360823
    0x2270721051302090f0103030e0922150501120201020106050f0105031909290a0c1b03030212040c08160302060409020a020f0105040501020903010b1903060c020a080d09030e0d 77
    0x150a10361007150700c1051403540056041c855000300b0305010003510181c4c410705041d40107200341038002d01114254502a030301c0354040c0c584500c10001c141d1420080001d8804d0b00e0241105106031959001074040041108104a59481d02281025450380400300e02650802030001036601d04202c1e1152340100603103034a803031070781c841c3d071500c080c60308042c4a10071084e030700d0352048086262003c1c05e024644010324150740c2120410440c028040c002041a58400c0c10a0301c007045280e448202c407180d641c96036280e0302c01c02c06e9602e0164080c0c001e02805500308034250041005101c0c00031644401c0b9006101514103490810008110414441c00040e4000c0000c000c10030841d40281c0c020205490240b054924070013810b481c09003501c200355070503201030b0f4012407040282c1c40d0a200300e8402d4032003104d0100d000b120f50841014a04042e1001030040783c0e9814440348807a000740050700d101a07004c0000d941c1c56100c0c070705074130040c6034094051340041c20411555a40d8104131310070411b40c1d508101c007407a0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 466363300 1250 466362050 466362107
    0x6030408160309030501090302160b0306010c140a052d0d0c020d0c050d0318090c1722030207150305010506090f010e13021b03030601120b0d022707 65
    0x40c40030540c00b102008214400040031400c00e12500384600c3c400d43c0900440040044075079801407203a000703079982c094104140102c5a0f0000400c03010b65900c00401303407200807414882030034101c1002d0040c0403809070403215101c7c10980b00d5203c4004503250104641c80d911101242d03030b41c041c4400010041800e0482c0e00c00546044400c0741e06107031103a200407500036100c0011502c11142c44104030080f4080b207035020225a401c003200d0010300032010080140089003400242214450303038034030034546a01c2000c07030b560b501410340d60f03041c1900030401c07081500d07594078000b513076503005200701404020310781e405442140c46405110f040766002051181002480000c01c03043d02c0004e0201418040001c0d42d030207458aa039903109040f01c03062030780140c43e10b070342c5030806240c03c000409103480b6803c20010007041d603800103410520790600a800103401c4410001240290b20b510030040d6000074602180902c80f9815102c8800c500c034004507040366500d8420095841050a424040006461218624 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 466364550 1250 466363300 466363327
    0x1309090b09070305070608280f0f05060d020103090c1518050910090507020f01330e042004021306030c0f05040b0f2208062202061c05010f1406030408 66
    0xc2c2c002d1184210b00c1c248500e10b4030b4040c510000381c0e0000c24803949034042c9c826080e00342d104400c000310101505024501c4e0400c001048408900d400030f0526907124000c0341441542c141110240c0801c4102814080b50090043e1180303001120317405030b1448200300894141000e000a90103400303003a43c0000c24608001035003020b414001d028108503c2184400d07840184240906e02ea0122075100b012411044000e812112569820302c9440403250005e040200301c422511540c0e109822403c0c9205001c4228281403811120140150f4428004108034107040301c0030310038400b01c6885480c100840414003109032a6008004200804180280400c11890010b00020a0441c1b40d03803010341d02c2c0c840002d01150f555100840401010400745105020034101000740a802015a0220b07011140c0c414100b100c040c0c0c41164000d014003404100c0e1442d41000640c030034007071941c01d82c0520a541c0c40d03c1c0000c5c0950907500c612078858079100713500300b19030800008903800b4680054025203400c1c02400081d = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 466365800 1250 466364550 466364567
    0x9060304080c0f06070807121107020d02120d03060e0106030513080c250303030b03030f0f0702060909150901090b0a030f020a030f0308150604050609040b061309090b090703050706 79
    0x140290041c204601910b40f81442040d10039081074450701b4a42c107100708000d0045000141000000d4a8108440301855004046d9005a07504a99203440c81d01d843c4042028001e9801031030b4094422504101340c280e4064000307000b40c54080310a10005c0ea41c1e00320440aa0b44107844c0e10a95200030041e003000f04040b44000c125a450200071240c43c0b00624182d82d21040c400034010703401c03d407034800600c01c0580c503014032180200b04400440c1400488912034105128080b1b0303488260034005402d03000c54444606440414100420b81d106519003900d4620b206802995101e03c618072010000c5508002441880242c0300c0180a9600e400c1c21a99800b60110f0b01520599025450207000400690301042c4840458882e54500b003160034004111a44200285807a0344112000d01c405d104e2610740100391400c0180403900402c210950f0070214003a44180c03040601d20b00301c000350200702040345802a0321014441d07813200d90181d580c05891501c2d03100a000007042d9410a050400c4040c0c41036009 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 466366906 1106 466365800 466365817
    0x30d0b0f041506050309120a031b0302040b04030f02030a0f1b060903170313050f030c1509070e04050313170c01171311060d020417030906030408 64
    0x41c01c0408819000d50f608104c8080006071990b102003101a482c42c080518465032810894001400f0341602100070341e6100045414050740c40c0f00344200c6003201d8030400c0c1c040c14681075580e01000c040030070b0b10130f0341d16204220503e804a10b02145d644022407203031800407040c0c0e0050101c0080310206174858028440300c0b0b0300400101c4d0380840c1280c2d150221400c0c8035980c0da1058203002e00071200e010003400074403030201800041440000200103001c01c40045800b810344510314001e8207107040394000c0c41904460070401c071541e4003c20007500300b0702c00c2c2c003603034207200c51155118041145588500c45101101824003081c044c00e12580e00400d8080c0780c0080740049420300118100710103000d0302d6440d02c0f03c188010600210301e0b00000300440041400d07540b1403102d42c90748013039000750160031040080c400541c40204400001c40d44860000b0740802e04554881d00c8a0307003240c010118 = true := by decide +kernel

theorem cover : BRFrame.Cov 466187050 466366906 := by
  have h0 := BRFrame.cov_init 466187050
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 466187050 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 466187050 ≤ n) (h2 : n < 466366906) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
