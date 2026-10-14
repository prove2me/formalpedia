-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3666
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:19:43.349553+00:00
-- url     : https://prove2.me/submissions/ba821f53-ab9a-4345-b094-4cde8165dfc1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 659172661 ≤ n < 659352517 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 659173911 1250 659172661 659172673
    0x324060c0809130e060105010512150f030601030c030b060609012003040b0a050d0f110706050919080703031b020a060f0e06040302030a1209170a02070305011d06060a0b1b 75
    0x10300056034078100541228001c43e00d600d5001e5800b135050010602404003424024104917140048a04125000702801d02c1a038103088601190f40d900f004a0745451401822200250307164070301011800c2541c402282c403030f0140b8000c101140b411106031800d0034410380d03030541513280110324140c9114001d20056018001007002103010003000b07004100482007611803d580707401c88030048003110209400450050304d0042403810340090b0381c04a0303001c140c00142c00302d126141c1101c06810040402148890301c0c407035003071040c104030b0204007a146250081d20100014100c00c0449407900c1d01c0725039200c005070031840710140090320700d51100401002d10341000031000d00c084405440d0503400e03542500580d20200d204031100b81d024004101c0f4900f11082402040903582d10001007000104143c58014804101d003d1014820010800155000340003400120b407020a840340001d200d250558007030042000142942c24184500070840e2903100c040341c0f8150303150003400d400d003803262201c1034940130702 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 659175161 1250 659173911 659173927
    0x61c0206181201021e03331f0504090e030417030304050f0118080901120906020d0b0117070302160b0906180a021305061809010b010324060c08 63
    0x200080d00a40510408103854200c500c020020039070481c0790002c07181e81c010800d003412119420742d441c44d43e042c040d4181d0745079100d6517503070450400f8101c040b10742e1009202d200b400c0c401c20b1802c8440000002e84011200c0c00307202c111281c007144441ba4003800f290040104028000403035104103c40700801c1d065900381501c55000c040030a0081c0980102c81d0300102c1400240881404181e05c1c3c806000020001c22a9044403902c411504a0004d0001d45000c558400a070340078104080064140d1b481c00c000c103c0541c541000207400c00c0255014103071a000f048104c1354007a2082007803110ba540c20203c0c050783c0c1d041040700a0340c0104105107e40e010711026000080d0012100341c0203c01800c050142840c00d089604103a03104100082030f90b07841030b4016405a02d420b03020021451a07880b000c00c1540c0c5a20204100c030403480d480400038081001003008a02c010f500c035100b0800260f0301407242100944540c40c1d805604d91103002c0521818078200030840c02a10340102c51881003034124100f4080b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 659176411 1250 659175161 659175169
    0x50313060906020d15060e061614070915032406051012051b0702091f0909110312040905191a091620030f07051501060c0b061c02 57
    0x1070100221501d540201e142850041e142c00303041070694044540d00700741441c1c030344000c0c813440c00e2031022800f0300400a151142d03140d0013040000303071395040103108800080000340760707030b07071300e1980c42a0b0000794a044080d070150216280c0e03c5041340d400c4180c00d200da6102d00c82ca01c0074907221042440d0300c56960a000640e9440b4034840c0c03150030181780c861035031160010769000d0a03a0b03002004001440e071008400a0002119000e681c1c8113501603031414641d580d022040716401c030400542840303000c0b43ca00d000590000d00d81000c0ca00d6881a44d00c3d8900720040c40902d80d65048142e41a2102c0f00c05100a000000240d407160707034052040c40c03110b00614600100c00044405a0644000980000404600c2c506240c11015000300144403404e034280a250801441c00b605082c9002c0c4680c601700d148c0c04044810800d0303503012500125850b9a8007181d2500c1c540c2d030a003902000074070065040000403414080c6610302803603504035210ba840ca40d10601089125200c1c40040c2003c0e00300d2400d4200981c075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 659177661 1250 659176411 659176421
    0x3016391a1503010203010f120c05041508070f050a03150b0a090614090720070317030106090b071226090303420102031603050a08090d08040305031306 66
    0x300d451280c902410680408504030107008500ca002c0d030f004000400c000040081200110742e1b0102c00100002461301e4060412005a400540e00c50b0030100b039072035140d140010590403250020101c0f0783c066a03688400064882d01d110342039100c40c50701010000b00303e940d40c050840d030350010400245088200006040082c60f5044180c0e2955540c500b880b980c200340b145130200e01002c03a080c03c5989450f41c0010f000b20354029041c580e1600d0b40381c90f1018404100b0069003d96403140c1100506a15425611034a0b0130900c9001d000514070180050400e8081003216410ba4020780801e04440c844142580c0150721407044d250325102c4030040c0140207941e4580301c3e0081040744051a42c034200265120040b610340744040240301d1103c084041e02c0013488d0580310350f2000060740c00101c52001300c0140c0c1580140f582021a189802d8800c108040d031040041801c209940c850050540724482c0703580d5200d844400060100d501040450302080c042c0026507801000444200b01844580e2fa03014142c070707 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 659178911 1250 659177661 659177693
    0xa0605010b09041103132301050a0c1b03080406020a2c011d060904090c05090411010201060e0f07120209060705030405040b040209090c301639 63
    0x1200c081055980c0e440c1a02030b0000344a5940545402d60610305580700c41d00b03840c0d00008142c42e001c044180317111083c0a082000c6111387c40003c019a260074250748020305101401c40000400200d8105020070307103c02c61001c0c443e010340d98a611036689584000080d4011000394042c460450300c04021901605241c0c045415230681e0031025612403000500002985407d008011080e031282070015120001540c0f043c43c8100c80108044030b447c00d06684200740c0303411141d003045121040000b40400402030f0100000700707a00030002d00f03aa41c401010041001d980c2040d0045101c400706040a1203502c00b0100302e40000707001803405a242d00001c026034419041181d484e000840c0810041c0b41600c901e44580d07000f91400d51900500400140030440020a5003103000d00c049044a01042032560034540c403d510002c100034540080354150802e1340c21644002c241d14101d035240001c0380b1400316820b00d011484210083c00e42c00300080740d0040710501c1d42c108600241e40c5e40c9008140c40b00314000402c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 659180161 1250 659178911 659178929
    0x1203090102160515150f0103090f05150103140a0803060f0a081f0e0303060a050d0f020d08040302030615030615120303010b120109090308010302091305012d050906070503090a060501 80
    0x1098504030130251651000b819000c0e11103a010100c0015210700c4c8074094000c809190014404940d031601ca00120160000035086205801c42e10118034201c00d045070503070b0302402a9023000182d03400960350f15a0481c1c0d008056000600100f90281000030303100f0f840040090804030a940c0f5220520710703015008600c1400d054400e051022008203d21503030801c050f9030b101a52462074043c0108880c042184107240c09820110601340034001c00c68031482889a00420b0300e6544225070905070078581003400141e100e03014400c00309504441c8a0380c420700042010300034250720b03552209250302022a141e46036070445980792100d41058420b100940c040d00c80c1c0204541c4891400f40300c040d902c10142c0103052014580252900413a030000c80b22811680e04540e1040d065075036400801003c3e0440340e008003c2d600341001c060201c800110032040420501320180c0003180b00b050400207079801640c000c0307001d801c070b9400314032168071802c01540c0c40a035540454030300c210705e9611002100c009903c04212 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 659181411 1250 659180161 659180173
    0x7090b03030903100c0f020609030403030f0519030603030e0319150930230f250b06010309020d14010207080301060309150603030e0d03030608030414150c12030901021605 75
    0x3d0b1a00300303504461741e106c079100400c103e1a00100199413032265000140c10321181f00c07a00c80365103100f03100700d0f6215018050301c030450449030040600648002e00040b408a00c0c07001140b400d6003400903421151403245001c04c0010030560700e8800d032081860101c051910f40b22410040811000c41c0f00103d00c0c0f207d40e200310749400fa82030700c1d0f103e40700c5140f4001c401c11940c03042003501408150007940e00e1020440c4450341e81c142a942655691180000f40c0c50740b400c003042e49a400318064034051500700d010300f20303516141d61032200440450700b800c88001d50010707141501c0c2011485c080102c003800102c00000519194443e240c50354503030402d070b010300700094444081c40c041010400c01d0b583c0441800e00c041c45580d08640d070150810742c0c01121140100c6821218409140c0b00350418002000c2e03280c03d0307907a51070311003000d0b0707000703456180d02103028604420321480340c1c0d6842011030301145142e41c06001d87c0c5400e0300d42c40c801940003801b04540b5640074045026503c2d007180101500910400007404 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 659182661 1250 659181411 659181431
    0xa030809060a0504050d0e04060e0906071229040f060e09070e0c2d030c090a12080a12020904110c0d08240102030f030c03040c0f060207090b0303090310 67
    0x4540007009200e205490708140c20b01001400005000258a0a904110b003908894102150040c1201e40c030102044122000340540b072140800c001d40560700559401c0442c0c02e542d006070064580351210000c69a51042d070000300301042e01154200c86900400115019042c5000c400c25035006800a1207035070b1884007071015289042000030700801788011103242604d0f08200641c1140501c818114030314440c900500009041e95061200360102c0c0070382151203050921940c40d242e00007d040324060380d8040c0f000b00b80500300301c0000d2107181e4040107031440d2040001c022504c01c4510244008421303000d0141581c1076031203004214011540c2c08010351622082c100142c90940b400c4403c2c0144500c002c140032003454a0302c01c082d070300311790719482500c006e41c4000102c0c614840d90050241c0c1010100c1400b940c0b00a40004500890068030500c000d1900c909400c495809203105581c0540c0c00144100012903003134000b034210744c0c001410b50381814000808a400c24114042d03c00c0c2d11592034001070 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 659183911 1250 659182661 659182663
    0x9020a0915090e090606150d0b04050405070f050612010303031e0c030b1825050d1b021510051e0d05100608030a0815121b1807080a0b0604080a030809 66
    0x3d540a10300c080100100e00348100400c2404500121449443e20001041d0b0302c8061107400022250340c3c064800c000f140780a082c816201c001c0d07801080102c4c00c4442c000203082ca0305d41c0075100d200c403902c0d007100f040d646160b50960050400403c01441040113000381082056a441518001c1d86c0b15140490342410100c100a4a0708074072511030602000c031410310101031100c9401030028900502c8901403100d000b02c0541e4035010300c0955111003818104824140609842d2078100089660222084002041110640c8060071038003648401c2843d60208070614211044c0075154203980444003840355014080713a10300d80401c00c1900d40f6440203d1600300307411103200300c0d8000c0c04002e010b5828141050001445500060083d452280c59032158440960b40c01c940c01400d200204100d0714200305a500e8140380b6001c140340184154001d28003006508030168005c0c1c0304802e155580007103a50707240f500740c00070181c04a4094115209010116140701c08014001400b806902e401361180ba00180007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 659185161 1250 659183911 659183939
    0x51e090303150a0605090111120d06170105040f0b070c02090f090601080715180b0301080d141e0307020115140a091503080d09060204030b0603160b0409020a091509 72
    0x6030b0f0281c8010901000042c0e8400250b40c0c50b00000d103043d409007500b102615180c000c02408032180701c440080e04500107500c952104086034000311840d890300880d01b401c68204d0314200c0c1c0c042c0030701018103070a00026154944582e840901ca00700340301803c030a90045001c2100c00c8900704150350700d28003444442001004a00e00400341e01c001020b8036410501c007120042e40c3c6000d0002401400c248844030104400280006011405002d941b41d40c2d45500c10f82d5510524020f00b400308050340207035400580b01a04a83d6115000800035000080c0c401000816500007459101103550307a9841965507089900340d00001e01c50f003e60300ba154600c00c410401106250740c030040ca0320703140400030514020301003166802c5070b804c00806605d800b04c801000700a0010300380d00400c41403002a011003045074a0451301d004140507000c81d031507412014041900445c0c5070040701c520701001d010400c141102500142901d004038076010007466990241c444490f00c0ca045990042890b81206126900315a508 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 659186411 1250 659185161 659185201
    0xa111b07120b010320060a0315051512010605090901060e03150411030d0c1e0f050a0317060405100905060109170705010215192003070903051002040302090604051e090303 75
    0x705e04c0b13105800340001455480f981d04900107054a0713005441c80580740202e101c008000151098214103801a4850801e80c000b10344500280c1007400042812441071064645514000d40950456400c141054a8022007001c40036030500c50300903040c919644400c80140102c0c4644000001c80301044201401c001038650268200079001003050701040c0f840098261611006903524540ea94070704004112904410028065201d03000381c290030143e000038003080f00451803001803141c1e01d0304001c00c002e071117098a00304200343d080c0e02c0c2889030745180e46c846600a10141000c14032144e4421f181041300030b40c450350212a4004d98000c00ca81e50f010b226503405100349256244861a060858840380b14100c02c0d04020240d5a04c081c501c040c94a03107900c0b45200500d03c52075224680100c00820240d40341c04100d42c00e000b203189540b0f414406000f903c3c01d603036009182034800e603184810302008041c010030300c400700301e400b48495500020050000303000750700800c0616501d2600801c002500305400301 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 659187661 1250 659186411 659186453
    0x1207020d1e11030c0f12120307080a0506010c0201020c0108221505060303040302090f090109140313050103061401182c0601090513020310050402040603020d050a111b07120b0103 78
    0x7400b07040715941e185d00c400c41104200e5002c20b4404011204501c0c100f80c503e10049801400000d2007a180d8121514500c40c00703010384207000c1e0740d641c6001100c0e00b0950070b10081c00342c0c0c004032480038250b0140718803a80c4510708003034815144002900140e12107071704002c15600904100000105143d03d8010745500202c160000c5140a14590126012100061070745d0707101508207011070207000c420b42003c01550f40203c0d082000b46481c4601540721340c441541c0fa034094080d41c4001920394000d01600b41128424a80981034010160054840c6003182c84902d101c034400f0500030804d220700311115a00112071440c00c40c540c00c03140001101c6020040c00031ba040c0081c1c510104890743c1c8017075020b01d851004030405a2a92201d10103e40e001069400c80c0c0c2e80b007400807a0206400768190301030301c5c8010b1015402c0c0166221504c1c0c0350122442181c1e00c2441020400440200f07140000e100c121001078201191030256541c0c9110740303c0655410100d41881c1010700410600181d440c4c40900350b09000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 659188911 1250 659187661 659187673
    0x20a12021504081c020307020a2309040330022b05041112030903010e1606110309120a0605010609030614190e010e0703060c0f0c03021207020d1e1103 66
    0x84502551030740083c8458540007001d00121001030b101b44280c603503207640980440707941900c40e00e05c2e51407508030b004611108800d03044100da00e03140c6400e40c1d90155400d512151821400f04000034000d81100c21040c0c0e0701d404465204c5c0300510988010102140200ccc250045080394428131900700c0b0007119807040703a906203804c1c071012030a601d040c080c01c47c1c800c4451883c00f00309886564110302444245961651920044011031f52011034032241000f10074403590140c5031101c80540f108070850401a91507442170200d6140c0c1e0030500347c09480247d903842158184051559520705484098004c2d10004e903168508004000d0b150151420084109440b64018a880c480c010030312507003c80c0160300e50b6210b00d4448111807007980003200303401d20841601c5000d5140e0030403001508900181d50009624a404500c0b075604c5242c044042d5030385503000c0c140c1c2d1b085c7c074001e4800c1600541d03400c0c0d9104034001018000181d40600f017220464005024200800c40341c00c2a0382c14801a1f103500703029030480 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 659190161 1250 659188911 659188919
    0x106020706050307030f06030b0a0e160e010b030403050c070803090a0e0411012001060602012703020d080901110703180608061804140105040b0a1b1e0c020a12021504 73
    0x100066130740c040102d04d40064101b02000ca040d01625050384003a0000109905000d250324003500b28a4581504000f01c81c130701001e01c424410042e205105803100e5101040c018001401004002c54201d806450103604213400c0c51401800c24210303502c1900c041d4000900c855242c00d05044880080031880d91011403450075480d0340310050f0300100054100924180c45415900c0c51003070504000034014001c109042e100c5001a0082a12148003000d0b4a4005590000f0b800040510709002e80e15030301918112039101800d0359002406046812b165407070300320300100ca0b40030700040c2c001c4500954907848494440d9240328a50340007038210408000f054020401162541241c8a0f160244042401c0c403540c1e85080050200d07102265000c45542400180814041c0d9940c245010b80b407654000c000810502924580c0102c1520070880843d0907640c1030400f240384030744140544401130500b48106520303680040d03848030154005440c480c0d800d4040006605140c03402010880652502d1840c190030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 659191411 1250 659190161 659190167
    0x70305030a050901111c0501080d0509060706180b010603150608161e0504030b10180c1b0c08010f02040f1205030d05101a030426210604050106020706 66
    0x402416500800d4540c2c002c107190302401d500111000c605180700c2c0b038844e9000180c603903036110995030201d03045003002c00108081402040c04201d12409456003450404180d0034001c480d000108180c404c81d0b41c845c407040e10710110486208181e84210301200c201d6041050141c00c4518001d81d982044114080c180401c41e005070358150490b410301034050b941c407140340c0b085404411010844010010f1b41c003000d08050381081c0684252441060f1302005556000c15200d00340c02ca511801004050303544641d00350081c107a0008070400a940307404042d800b44500140d440101c0c00408403040c40400d5410800e09800f0710800403454100030b4150301c1c0c01c0c94070310365102c00c860900580d510840a80800d2040107010002c40d44060603000c402c0c0118580400007041440003446681c1003062600f00d1146c0c000c240a048a00c126401160001071041808102c0c5010940228104001008014101a01c140c494208020f01207219030380700c00740b03400e8081c481607545c113904c04000c3d9400b0407824812650 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 659192661 1250 659191411 659191417
    0x121614031c0e0a241d2803050a0e15030f0a0b030a020619020708070609030506060103180f060b060c010219080f04030e0105090a031104140105031f0e030a090614070305 74
    0x11040b4242c4404c01c02800d980c034010508511204c2c0c2c16240341500007040c0801007201e1610503505800f034024991404002071018406600080006c0d10400c40f4902c0c090154a205507a003202800341103000b49108445e0510b680705541c0d148494072100f00300a0314001500071a150300c40141e014013038002c0300d80c3c0411644e000d414904100c1a0003030070f840070428401c1100380300415611084580b156590040030345000c07141d0005a9050188100240ea69400707802500a85064840400200d5030162110000904144011a031407030716803040080603960078002e8036800300d51500060360b401a810285c500310120800b1481404009000c00183d810aa5004e56105801d802d00403c0da0707003410700403a2244101c81d01c0680c0460340c800301205001c440b0020341000d40c4155810841c1c0f86110b5058010000248502941580490046801c0c20403484280c0384101d0401004248a425a601c490030b40d04112051400078141d40b904108003644440c9140300c0308241201c0a1078060640c4005141d44 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 659193911 1250 659192661 659192693
    0x308120c0c0c09130611030a050106050a0c1217010f0810060311120c09011d060f0604090c03090c0902090108010b09030606010f0e120102030a0e121614031c0e0a 71
    0x100d01500140840c1c4001d104003100c1d81d1700c48400c200021b48041012410741003540c80c040403c0c40c01001140c0c190140c001c840e0711101035280c0d0f42c4041d445079610030076407101902d45030410843c110500c0d0090858085035002e07121021107054105e09100c0007619240d01c284407000c6581c203110b070800105128800c0188800c0041d80c901d1a00c0300b000c3e40042c5040d00e81c079000764000310307107600001380d2a18a0301140f00c070002c00e070082c6800b41c0fa400200b1240280131b1513107039441030b41004108920301c0c0680c0700c01080692418042400509512102e903807044a51103003060640003d000e034240c4d81d0041d19036015104014240c0d0416003020302195540f00300078103144c18040035441c14035102d4051f43e0120b00428001f4074004044c280400c0c240d020f0740045c4c0e5642d2115040908564208401254a11004001c80342c1c0b1f5080c0701a10098001c0043c06e401c007030b1800c0394941b903d00d01c1140140001d10151007600110380321042d4404416044070020100c510198100417180c00010b00c0902c0b03501862 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 659195161 1250 659193911 659193919
    0x10150e04080708070302100b0f0907030203090705030106090c03060b040b040e0411040504051e150c090111030a090807050d08090f04020d0204090b03210307050703020307020a0308120c0c0c 83
    0x1980d2245090601d511842a0203450144003048110070103134005074181707075580c0c061002d210881e046024003802c04185c0201c0e913804406000000c2c10148039901a650082c2580100c48466580f00003207270840300c0ca07800c00c0740095141c0343e07244c5402e80c150048030010204258102e181514040c182110b1740035a000b58805a40c0400100701030091090564022140081040085090607c0c016903030f000d4000c6400d11405d402800e07400c0d9000081208900152001c0070f1044540d00e410445807907512504115040c42406030a1030641c0310200044d0203502c206880e101600e0307040200d200c0c54a00298000d030302c100138400740500003c0185013030700d000c01c0c8144c40094811103440000343c00383c05004e03140c9415510205002a500100d03400040c0b40c800c041e816140c42e10034101c2900e055050f80108000301090070030110300708511135001404003500038810f0b0390601d030f4581e0010b5a82502c6500540b10b0401c0440c02030030fa04c501a80d0683c000f0a400007242c5044031941d030700354942d201010b840d071007 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 659196411 1250 659195161 659195189
    0x309060316200a0b04061d0c0301050c03132015030a060f15050c010612030207240c0204020d11030903070b0c0310063509010e010b0102060601030902240c0d0e0a050d0503071209081015 81
    0x2c0080e3f0209050900c00010201c14001c100790301e0390250350300120740c03a0180c1414100d00081f0701005005e56410b403100009400c51100c01c1010542d9154010b83e40c1d40e00c190740c0c9420000d01a146071074882d25061299016109040c9040301030505210f6511501c8200007100e110580c481c0d81005030b5010255041c2c0d000750b01c0d1040c02450700014204826036075040c080010402100e01004401003000b144503818a40c450f440e08008441d0710b0008603003011207080312010520409002d1640d0504045050200d8210000000c00d40100440721841c00604001e0310010302042000030f008000c5514030990003000b1135100c05000079a96040540640c3c140360351220321509548a504001156640c0300c50403010140380300304201032542c44900403012600464045500841c030940c00740a006000401d02c400003805e1400300012002000e03c1202c0c640700c10080a00001d943c1d07080200007491079112141743c41d103004015402c2c40c581d24116503c031840d00000b0112800d90040b40c0043d02d005c5654481c1c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 659197661 1250 659196411 659196443
    0x8071701050d05150405010c0210060b04030209220303020a0f051c0b13091a2203030c030212090a0512120f0403020309060316200a0b04061d0c0301050c0313 69
    0x2003401c04400b038101342ca0400108004c284030054000100501c032550032a81d820b036803800354400310b60076030240700d0084108220800140c6004042150041110140e480c0300c000c02c01e020f1484c8078155032007100400e0f00415240c90a0f50400d8900603680100d040191070100d03140c9013552200451000300c945250784140d8451562511002c40d002c20102c810b00b004002080e0800004049000400210074017980d0300203400344254a013034604002805034103450380920750f90142c0290214030351000405070b080c0045006500030710186030040243e40040c0101c041d090610a0400b140143c0840500c3c80821440b507207581c5425070b044d0700603419044240c003034880c0d00d0101d05510550200c594045008410711110220328000300c82c001c0340d10348542c2c1c40f454041a40311001c4101d04a40b10701c9030081d403e060040340c01c0008060740a03102c1c2c60001280030a65401c0c02d40c1010004411591b1352100500c0c1500d401c003449495081100304d0112400e42c80e0510340ca00c41034500e00d030010414005101518 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 659198911 1250 659197661 659197663
    0x60f1e04050a0605060f130501020d020a0803041a0a0906050109051317130605040810150902070314030a020a020f0c0906010c0302010915020a020c0409020108070513050406030b040308071701050d05 87
    0x440036000003410b03070f0740c0d0306c0c4006900301098000a405010010307000d4800186c642c00020113010340f05c40c540203010a84025200c0c82040d80004100b0b8407000b141c5408800e01c0694803402c01d20498101d00b0000c0e400105003000801ca40b0141c014965036440c110a0004007482c0c0070950841030f41c0141d4007032003203070030b48a404920302a815810003040c17400350380070400d150050080c00a1f610b039102155441400410070360705884552942e00500f0080403001d1003519219001030100b41c1c000d0801c0010880d401c140700d41d03682d004580880d107d6038049003d203000b950501c46141d000d41030300c004202e00b01c541c0c40010001c000141c60b19051141d03038140070341094001e4100c40c03101d54116040c19907000803d26400065071000d0341c400014098012a108a440d29104400c5803c0d0180d58041443e40e50382000d41c0e440d1301903441d100d480c41103240000b855580314041c050145100e554580942c0c1044d14000e003031210090006014443c4551214101114613a0350030304441c02143c003502c0c1c4600c2803c0607 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 659200161 1250 659198911 659198921
    0xa03060302030f012924070510020309070f0b0427020a020a020f101d031015030c0e0108030702040b0d052d070e0105150405030d0305060f1e04050a 65
    0x29010b018008404000c640198070103100010580311750881410311004402000009250507079100c41c481001d010000c0d00344c8001410808200e031039524103445915100d1400c9041c0316002e84041d00002000684c0c2400e0000c00001c041d0440d100c1c1c201420560a80464051760003407240303e1140c01510306c4500000003401c0b0003202d0100342190384921101d0000c0d00c031990014142e02404c9454004551130138020000e401c408890756840481c1414041d07480052403000c2d03a026414450001741c0070500c5594451040081a8080e0b820403035803840c50b280100b024035612011443c2d03200c134010010441e01004071912280d040303400050300e0340810001a25144005005000f83c130514240d24640c4040341c0444016860f0000b02190034074113084096503609160152a840c031100000400090070900100d0300e140c0c004107001420305486034046031078803410526400001b91038506228184c208041c8034021030605458600b10400032103074039502030200240b4940561f0307456000601d0007900340c4c00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 659201411 1250 659200161 659200163
    0x180606120e1f020a03050f0405060a09111302091306050105030408070c0b120901050919110406172515050702040b0901094a0309090109230105060f0a030603 69
    0x104141c1a042c24080b00007500701d0310744000428a001c001c1100d5414160005e84103e41c000010300382e80e615144203c1c00760011100403943c2d40100c0c1c66492030b40e51043c05d02000d01c1d50480005880d44541c1042210501d502d01021000c240f43c03050512140c0d0f44102181d42c40b903040343e202940c1e200d82c0d14003c48154015400b400340500046082d0460402c10340c1c0090054454100900c11501e5051070282c07110400b1039618102e503882e40d000800101c40e1800c101d401c200041001840c2c40c1e4550300c0282d021001002c0c0035064000056250354400510304210a800790b12901c00001c0b4246000307404516489100300081c00300210340d4404550b92500101100b68000e808101d0a5950700b01d8040035000404034000015100392240510a5030000d80741625400e407000c545030b444030801000403ca0b00c8402d00c0410340410070080c2103d4440d840103500a02d002c00000a400c0c518a082d08c01c2d580c0e44117148984034850100402160ba24401034075101004410035540e660403c08080c2c0052100b0380c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 659202661 1250 659201411 659201443
    0x11070f030f021c030c120506060306040f0e0703060605150c070e061c0b060a1403150c1e0d050a0e070603110405041107060c052514030c0106180606120e 67
    0x2540714a10307030313050304203510820003034a41a4540790f00304a4001035070b10889080f40c01500a05c0042c0c91803034150052100600b00d0b510009240321441b04103800c105c1305401c1501c41c0ea1325400e0400441c10034074100c00018085205c200d0802c05010680794582c41030380b19441d201c2d00d50380c01290322540d40124151800d0100d112881c0e80b480315103051101c0c0d60040315403600c5211112400514105800c200300608a8000c0103400041c000d10800102080701070300c1d060002c01c09100c5101c0c2c450728000d250021504601c04a83c82d10712109201702610b100808042055040c14210459600c00103441c0b0190340c400e050120310020400b00001103405a50301c15980a41401e8030080d80094010044c40103501582c418881070180700b1b0f05841d03a01c111a08940c220000840c00480305900721240030f0340034450102c4064070342c0340d442518510740180c04000d8169540c3c0c0e808000c0c44489010700c1000340c0c413180e030a01149103010005854641c110a012902a854604104800304241300d80a00401026 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 659203911 1250 659202661 659202703
    0x71401120905061f030c03080a0c0f03120b10020a11130c0519031e20031503060106090b07020909030c01091a010b03040c03120306052211070f030f02 66
    0x2040c416030750328080e115020724a00001c04031031210220010201565041030a0f10146c91070b5a49480b00c543c4201511400c0203a400314160008081d04140d281040c001d6a44030040031200710904110b594543c03409100c1c9940381d484400454000c990b850400390007802d1042c54038045030114041108009000041c00d1504102c1d003850341c0c102c80a4003010a00641075001d580b60a0303000e500711140032908940d2880729040d8209100031641020700c0341070b80002880c580c1d40702d003168811b50b9001034404500d00c8605000303400c52401c040040c40c0c0141036038604402028641b80240c501c030b10950308068001c540d1034001a0300c0c9403041003184e401c021124000c00c90010079003070200c3c00c07151840c04455010303000e0000242c00351f80321054070300480c1c00c4804050030030310715030310107040f46040c1da044410f00d621f0b1f500002c2da540c1d4007400d0041d00040980c130310a0200c1090900f10807602100b400c0c4403941c00034000e16020440345060000d1640d03250805580c0c02c005040c080c2e18241050001e0b0624103489 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 659205161 1250 659203911 659203913
    0xe040f11092a03100e04050705030d0305150d120509010504030506100501080711030901110a02090f100503032107021501030818010e0d030e040b0a032607050714011209 74
    0x98100401c007580b01804000180260507030300c900c24401511042040d120400062046075001102e080d00241b0030310440740c94a0341c400119060144845107800030a54800412250410402c021100008100c0d2812000f849070f82d41c000e0243d00d0000c01808000307020a0091899005404440245070030404030780321403070603041000354500f150140e50b0003c1c03180720225403a54011a007036403d08070740d080510b0405000c80c4c0112520071482c03295540ca0712135040c142e0096112620300c60300402c01048403800620b0700c007400f28085581340c2c1c8854060b0f40100141c4526490314014489504c88402d4480c0054030342d480102d203800180f80a20324150301c3c7c1e80001082040381d1005182d81c1155000c1d860f07585004800548005c4407205540d504191040d4080000902c80c041d0703240d54440090000444030014000b060018103a900200c03410121036440089030440707001400d49001032041d0052508001c3d0f941c6540b94507062107018065416a046807025070f000d1414107020140d400001c00c218426 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 659206411 1250 659205161 659205181
    0x7050d02120108030a2a0312060e070e010201150503060118470907030e03040f060c02120604020d110a030204090b07080106050a090e100b0703020f06100e040f1109 72
    0x111311006008502100d585440748101c1c03403008203a0304020402e5010601241c0ca01f2360303403409001140620340c0da44900101d01e5510141d840350040c0460355500c0c3ca0340304000b001a00316503022090003090a02c0d543d08000c00e82e40080c07800c0c1034071700c0b40c0c94141d00c4001022204018260760030f10f203802c44a02c00314080c100c1e00c0ba1000d409902c02601d100c10500c1c6c4100044250554409425540040802002400507806608480414400c40d01100e02e06a5114031410342c10b42c40f134118000103825003d90b141036181c80700300f850814044c00d0140c24a824150b00103106600c00032002007a01450340101e0144c6c0d595122140c000310b4004c0c1041c441c01c01d01e45840c2c064480120742c80b002040250b40082015403140d800d4030301d10441500c0b01001203017402d0021001100003002c0c0a21280414400302d04150303030601601c10300d8800d8004000e0000100c0311203090050040c0110214031110004200341b010f554801d41c0c0168004950481000e114102003860100d01803960790841030003414001e080c40 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 659207661 1250 659206411 659206417
    0x1090501050721061508040201020a14150c040b0a1b060606080a05090a02150706061212020d020c0f011b0605040b0106030c020f101508070e010e060d020907050d0212010803 76
    0x203003c069070401540e04043c003812220940212202c44400c400d807030800d076001e80c004540141c01401113440c03500d443d0365030207603c1280c1020303098580c024001141c214602c01218581052040640c203050a007032100c0c09081d4080c2405203000c000c1c0000d110103800554400f03800c05903422210a0203240d0b140d46025003020300988502c0c3c00185410001507008002140340d1404035070050003040c10103008946401c1b150070110003a22141d940d0200007c40100600c070700d40040b40724068401e030710a03240c9030103400c1c6004181101e0544d00311083e2005540e5890181c441c801d1000d0810703603000c01d06c001c0607294500c080c0100030301e0a8648424401070180545503d4102c84659809011481c02c0290490b00d42c00b0842000301a648080008464910150008c030b098640c0791100107002c0b0340c0d0340c681e01c0c9009020790002500c0302c09000144540d500c41c0010320f5110750f00342d441800182840d40480c4802000410200c00c101c00800d11b5005500300d90120b480903850703070117900241d58540d808952654 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 659208911 1250 659207661 659207687
    0xf0d02071a040507030305030c0c03040905061206190203070302040510020705090108030403080301050f2409040b060316031e060f080c011106010905070c0c080d02070806090304050d05010905010507 87
    0x20005041c4808644080c031001c1d84159030000c041c00b8058510383c2e00340d81039003000e407201c00400c6051101940100f4200701410092184d00c5010406052500510403030455080320207a16800c030300f0800144400e500301d083d01e000c02d240e0b00140d0300e0313071000c900300d0090089400c426481201c400c01c00c0c2f0044d070b000610300140d0342c045410008690b070380d400c444d50700c2c0324a1100400c0c06009000411007440c24402500a0305c801500d0701030030070300e084100c5541c1805015509080c401c04140e00100e81010b119558054409682c814914141102d00c4141e110b016500002095140c4125001c4012252030348102c40d142c1d2803051004036251112071303507105442e0003039000340d00c1501da41d12115840784047c0072104040a01501060b401c100d05040580790003890038051020740c60200380091144a41e21009042c004090403006414220007400d05c2c481c0d41c00066542c0c08602407203900c0002104940864900b1a540e22800e40546082d9016101c4801d0203480c651030305040114540d000700e821305a00e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 659210161 1250 659208911 659208923
    0x6040809010c0606030f0219140112020906031306060b1809070e131e050408070201050c0309090a020a0e10022503290108030a0512040303201c021801140f0d0207 71
    0x2582202e8034561000071500c1742e9001c1d0707030343e09c548903141b5401154014050340c007035003015140038100c1b00892002d920585600081038002040c201c20b2181510460f0050080802d0710307841c0c8038020700710311060b1901c400194800c030300d05800708084a008417103c10400350042d0880030f440c00c41d02c0440d0000c00c86036800c10030031a00c0072001400031841b48505440342e50f101c50081d0a004940e001111301c1c0d00044180070f09484200120b903e607581d00e0348500d01c0f4031303600980581d6842800300014504100614064024502c010b46a00c071650041600c44c803404203091414800010701020406d0302426070300240c410102207041080301094075000400002e190b02d88a48140d80e2282032907542d2003203198003800944103101048102c540c8049082c1c12500034640071074603003081c006500780c0c840c4000201c81c01c807000141000088520040200e0781d1501c4010031410032079800d540328080200004514104031610082d4402d80d10307414207940c1d1400c031b507002c0fa5458603629030b5808000d510054095444c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 659211411 1250 659210161 659210179
    0x109050f0c01230304080a09120c05100f17060301091401060503012a050a090b1810030b030303010b0306061620060301030519030504090e06040b090d0206040809010c0606030f02 78
    0x21480d0094000000200c0d20703600031302d50345d66070300c41c400550001c865040400880d01c40029403e500b40502400003805200501300c00307490103003002101c1902c14202401c0c05040c02904255a41085240a10b014501c9240c0d0241c0c0d110000039004145d6120f001f06100071105203001d0080c0b05500400070348506070000c003c0d00c8500c144490365403070503012040000244840551030b4621482c05080042600d041031200d01e40c0707403a120041500290528540340d00c030709807240820b2070140403610901000e03050400c01a006000801e44a01c014001e4413203110002000c2600b0740c844000b02c0390500c05e0b62102401203940c5203441c10402d85e841e40c120390f03400c0c0115200204d0740b0340343c021a4101d9030300000415030610018104001d00c1d600140036420b00005104c00900c1d1001406803150490a6074080c090a1801c0d103443d030150f69001e40404080d0780100e92081405400103450b0760440d0704880501d4480506c840102d56400401100500340d0f4240040041009500850010840c1c07084a0700d443c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 659212661 1250 659211411 659211437
    0x10060608010e09061b0706150315050c0301262104081c09030b060a080714040e01020a02030313080405041107060e0c21070e07050405031606050d05090109050f0c01 72
    0x1a07a1001038400c1c00c0c110000c9a20070240c2c1719090001c01240344551000714001116218000a0100303650054ac4c8040030b42070400c0c001c6c01d851083e682d1108010410301e0855041c408400100c00c1c444040c00550307581940c0900c41e0300c0003002144100480320a5880401d2070a94100e0065080751140d11410322420003c2440070107003c070f050264560503030320030200314651b465200281d140603185980180c0241130100d006001800090003038400100845c0d80b200c0031200f072008940c1c241c4115441640706200010380309901200700d03604000c3c00d5990449071103407414201c0940c41145c2c880d9138080d140c4200d0307003502e005030340181ca410341c000d0804002110b075581940380c861290134041503014130b02981007a1030750b0405000001e50311884045031540354541409050340c060070740c0d01c1d402080000c03030200460314080195420000107141303400307081c500e44480607029025a80800e41c0c3c1d661a0340c001804000c09504c43d1075a1a000000c036000400103001d001e440e08800707000140062a4050105 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 659213911 1250 659212661 659212663
    0x801060b030c03070c02030109050c0114030c0703031104080f0d0e0405060d03031d0303131e08030703180506072c0a0306020706020c063909011110060608010e09 71
    0x4084034500305460785542d65202d00440c555000514403800d0003000c40210001d83c400f48120481a481a001002c00120b6640094100c2c48070618044183c0810000c11014840d400155210305506080102c0d03142068100314906001f2900094a1803042c1502e2034008800011804060003054580801c4000300c10305010940300112003580d00100241e10240000c1d03c03030b5224085d240d282003610141d402a1b074006034155030007600c1c010003000c101e6424000b8440d404810803205510b8202110903040c482d503d2440a010060222003415a44c00a807515002c003500c0c041e95413540403040d1152031901c0040504180c23041d1000d000c040a8104055903074980780000e000700c1350703030052031000e04034590f98880c4041e6020210440d20b0303680a0050000880d01002020701404144881400e4115030f12181c0e03048500210003403c858210310203401b6540a014200e60581c2d00030702e00585040b212410f03c51802c0d203820f07240d04526150840004609505c00d40c5941646c50080200c1c00380d44030040302c2 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 659215161 1250 659213911 659213921
    0x14040204030206121b0f0306090a0504020a09111c0f15061409120304080d18050d151401080a021e0306130c0504050f0a1407020c010f17090708070801 66
    0x203400601c1000010704e103190008840c0d034031091101484049400780004008160819098000e64180102c140b24261900d5820542d0000c02c2c540b0802030351402d0740006c0e00000c00c078482e4461095071800c140c041760212104076070f84099102007071301c1c228840103e59001840e08200c04200c00e860090019004070008003168102c510a59170142d10480680054526900c1009070303644c006040d64a4035440030040c00500020004903002c1c0001d07990f03c81d80039010050590044000082c411400d000700d50780c01000f40b0005402c40100b4140034201030b1030000a0240101d4003c7c3c0554010001425910004241156510a50750042078803d12002c0c00c2962010300f9840e41d2642000000801c9070600510300c100c400d0013200c0080b845582d034004035084500980740030082c880b940d800c02071280c00345d0042c5210007040c402080014604000025268012200d0032410440c0a0404900d802d100703038022081e0404150462015040c0800d079180d07145540d2281055a00604400054811040c0701d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 659216411 1250 659215161 659215163
    0x61e0602150f193201090513080d0e01090506010635040813030303060911030f0a0506030a021207050123160312090c031b210501091a011404020403 65
    0x1060340d66210704110840036030640c0d2904615580c0c0321130904160b140c01c1501c20501d0f0140c910082415041c8441c0076003104140c0080803018100001e0203940414107080b004020303000030409843d440401c2582000d0070140d12180c43c25800c200300d10043c06004035070ba0f41251070613107442030b40090182c80d0300101c880009600b000213008001c4141200281581c60358482d00c51000d09151a41400a885903040c1503081580003d0b6201400c0c811741980f03100f00d140698003c0c000a0442c540f403001c41110b0303040182469555070301c0c0c101081e0f0548003081003000c42d075030040800d0341c4000401c06c444d1380c03170019218481c0040c1a084009460108052280e01c19080380c4044034a003843c00c00d0381c10701041801e14200d0170088100700d45030a8200302e1249002c040d10a00342904e0341e524500300074a5014591401d1442d080d9590340800c0030341030000d50300c0c01e050344a82e04000c003007034241052030040c41001000313088051001e03407a4484030140c90290f4142c94414002c0c40e440c45111040c4001ca00035400 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 659217661 1250 659216411 659216431
    0x618041104060602010c1e1112130506120703150504020705010b10030204051e03031306030507111c0c08120903030403090e06101d1002010c020606040506150a03061e060215 76
    0x700c01f0600c1926013004031115400c030304000260400c04105d840c60042c01d80b02d018803c0c200490850020300280c800b440c0200011281d0034184041800000a10703400600300c0810b040c4e444030685000703c0300320b050000400d0010000c545900540c1070150280064000b028420324031089032446d568000d00c00d60702940d8015201c0b690f0012444a1901d070811740d0a640350b45031000f804000f1151009003d0203015044036900410700b41080d1a000d08050709050000304550401c004803500721050044401d1690458513100300503100b603042051413031064a40c203a81e020700c20020000c1c5a0350000056000ba40b1940c3ca0040b02d9664140305107000740c05851036903100c09075032650b034600c51069506c1d04c00680c0b010a246080860b0760001022540103600c183c0240c0d440c1c040f6170140c1c0d5010300030140c1c05042035134280001e18210000a044410307001040e007882c0e00100301000c0c000d1013980014050110f2020300300c401802e010040d4144c4005118400040c81a13002d201801a40c240e00e460041d1400c0c5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 659218911 1250 659217661 659217677
    0xd11040e0f0a0f1503021c170a23040f1205030304030c1a01080c031506090c16080301090510080d0f08060d02030a1407050a031106030618041104060602010c 69
    0x3484440d801c110160003104510703202e14407000482c04031311404e00f0104400780c0355521285184180805102400703510300da4442a00041e8000c5011560420044440c03400c3d2540c2c2c8108144041d00c0701c10b600d81120b0300c0a00c07a912507202c202d51075801881614981012045407950780d10a070a03403500f0500004129070401c2c4082400640903922a01e00140314250610340c1c444005410005402c09a000ea0308950150640c82802d0900307000070700f801d01ca480d580400b40e15046002c6001c010010307003080c2c250580003035900381411204501510040d4003021660383d83d40e51f07200c80d8010f4001610080e11520312140300090f11500022820201d4486480c1c50344d41c7c2c07a03845016150403400800907030300104001400070041e5801d101c0000c04a11419400b1846100342a14902e000225007200f40916070003041800801e041030b6000d4100142180d42965a68994000c58850003455203100c5d00d801000080c08100b061f604401407041000707413810444250b40300c0c0c0c12826101c01041540104a10b4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 659220161 1250 659218911 659218921
    0xc170d0203180609180601030e0109030c020d1403130f050609030a02010c021908010f0c081009020a1704080705010b100c08030402040e03131401090605040e06010c14030d11040e 78
    0x14440382500c40c0b4000c021500305804500400e59080c0d54000e0380044d1141d034810042c103980c140c4038144200801e85c00800804107280d4024040d04404000680f11b007403801601020404040d00307505040901e80d060381d444042c0304a2105160103e80111000f600200c40040303042e007083c10540f0911180100204a00c1c60203400540e02008803117004d0303801c0050305214000c04001c0c5da10342001004c1c0400001071a207200c400d000704403800e0380d00710802c20401c84248006141040c407060162a8014001a0796400c42081520000c00042010300d00f01c000c00100002d000c2c0d0780020b40305d054040d0001340644d242d102e080055003880c403040040868941e181d402d020683d00c40c00741d44d000e403000d000000d5403e0030250207859078003c050305038180100c0890a100d6003000404040007001c0a0130501e07006414440090000e000b140035200f0040b9800d80000d41d01c0c0c1c4200241c0c40c1582e0000c101e0000d501d021a0100d80f240c0c490019408880d003030070307421002003100380704a4040f1100e184000a1903214 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 659221411 1250 659220161 659220187
    0x1506220e19020a1d0d02032d0106030c230405010308030a051b1e0405060706061502060402090610031509050a0b09040503090d02010c06020d050a050f0f040b06010207120c170d0203 79
    0x2d0b0032540e04607100c26041720040e01c0400c5140b4608140320a20000c0a24020101c51404a14461000680d0605004100007141e4103101c505481c403200c40300c42010b41040c29042c0240e04108a0740e402801c1800010520001c0e400a5000f90384e503030703414000ca0ba100d802070b84035100303407d0303900701c24900030440c145044078042f0000004c40074016101d4545541d13600002d41a400a00c81641c0099440c0f800b0801c0b40c04800c94140e2001c100c0c00a4881d0380740980001d07a1080c4024121800703101e0b881d15180d60f40b4800c1d88100e040c81c800c00c41341142e071a164851040244012030307080300e002c0c0c03401c10100b4092400821079071080d540a002540340440807420322905551454089040c0a81841031a00041c6a03001804412103a200001340b546414030070f03841514406809103100034205424000c210350414421070740590805400c48042c1c03104d81c0101d00d401d0855000a124460040540e0104809110741c0f5040700c0400820344100f0899821058a07041c001d50100f015a00070820b403504085 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 659222661 1250 659221411 659221457
    0x906010e060d05011e0b09070504140f040203090105040201022a060f0c0616020601090504030c11010203041701050a050105010f02100f060f03060219081506220e19020a 74
    0x201c0544211009400c9a48542c29500d68a040d500c0e248801c04015511440a1080088610045a0383e4006051050010780079201c0c50107034003442c5040302079142051b1201c600303101d807003440544210754038035001c00541e000b00f4007900e080740180220703034403006c1c0c80c0662003c0b01c1400c5c4103010343c929000840b60408c000b80e848030f100c11010761010700500320346500c1404814423600e00710758148601400210002c1c14080d05070080d81c58546000d05100200380d0200340440100d600a10028010340d055005138070310301031580401d00072555036050004100d8103401807409110606418080b03640c8500064641d84480410300c1d00503030213424003008c01c00403038001c104015060324002800d1515003013800b01140b6140c00c16102c4580020710001d284015200c0d406a07a2410b144c024900c1c20300c6011400c0900341120b42620580011806a110484c0c00400050300302e440c10000786d08031345e5104400b401c40b10482e0074441950081221040015441c02117403090010340e602c03105200768141140103202 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 659223911 1250 659222661 659222671
    0x1030209240a0305010608010e0c0d15060905041b02030306090406090b10080607090609050d051e0604020315060f0d050a0f0804180912140c010c090e0a050906010e 72
    0x144441020201424080c05801c4440740c4030041c0d96440b1400200030703094442c1a84814101b08202004000c10f8241c1c09085410241500c041940c0d814429191005404500e01003c1d03400c0e604078000600e140c201c0b4401d002c8403030544081c4841d103030350341714a0880980d031510000541c2041001901c20701e0110510382e802071140c040018241211789803806804011220b480c800b0000e4501800010010040c89502960f1494804007281c1080c00090121010384a92401451003c2424040010601c080003009441d5490126560070200e500742e030300c00080d6000d80c02809840346000703c4500c0004094803900c03001d054000f0140033901480150b5450035810360f218006c011000300080c0b9101d040c07503030480c0200080c0380c86905000d2028910031504000b80712181c2350082e030b800007400d002c0b0307000074070750341e40c10b18414141d400c5e24140403a2040e540c0000e141d502c7c0040b5010001c0c1c0050501040d00c1e1b51440c185002d985220004080791030540b8961041c0d070000c80100704201c3c10401855001d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 659225161 1250 659223911 659223919
    0x315090717100c050a120c021005180a0f061103011d04030306050612040203012f030a2301030606120803040f05030f0423010c03050d15030b0702010b010e04050108030901030209 78
    0x1000c1405002d504460781101c8800000300000383c8400b0860b0312410015201c0704000e820058003580c4240030f560f409001848020707054540f00082d001c401818400c2c8450307100c810607940404054500310300080315110088640601e0041c0007000400d100741968141c0d4075041040708415941250b014650300010811000c05495500106142c0c9588015100c0205e8141c0240f800382001d00c101420348404810325620880002417818a5800007608202c40701100c0111955989490030100090000c501c4550342080b41c01d180d03510701110441401d4100c0b809014100039071600c0c1c10440c850011180e0000e0f0621000340b01042c003207401c80300c0c007081a030b11502c00c491500da00c041319801146c2050340008103c0400764000c50341d401c4001076800d0042400d10b8890840d0b2890364028041f80603102207926219034614411002c00e03074001198002c4d64101029018902d040a0028041d0030750868007400100700c0056108142000d00400c0c2c103070307080e42e409107003440c2c0f07450011130082d045501c00d07a0348 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 659226411 1250 659225161 659225173
    0x1120207060f021b0d05031b090d24050a0209130e010915140a0b010f1107030501093813020613060302030108061005030d110a0c060306050315090717 66
    0x2e042c1d0700c002c0c15010310303485141c480a40c81084d203a04101c204204041400740800c00c101036a514a803154110100d030120182c0c5070040500443d0354a2a2480d0081000c8000c0380c40380c282c0f0460120600f50b499910f5000e0100d0350b681040da60580c01000f94840d008040a10840310800380d0307801401d807031401140006820300c035079200c0701400c03100003c00d015521780c3c42e2040c0020440d1648241e40c07100c1241401c0c000c0c034200c800028a00d035540d501c074004101d0304032501907030403400b13105940c015a0460028040f03aa00c900b8441007085002582901a106560040a0201c0010721602c01000800c94202131a62043c6030003011040d0b40504991000040110444210820401c440070b4040c40e40c00585035814007848500d04200542114180344140c101004503540000d07000c41d07041441d15041c0e014289100256203444000a0010b0050f414100c001c03840c4e5925610500840c1d00480880d2900ca0070039182c1d41d42080b080d03c401c0d0113908000fa003400b940d80c0342629000d40d04250022144 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 659227661 1250 659226411 659226431
    0x20c13141006020c030111041e030602031e0f100b09010c050a35030c070305160b0609010501030606020c0906011b0b1e1e090c0406080f16050112020706 67
    0x4001404036140c0c0a81d00034040e092180c542c1c1001107141055081d0020030140100002c0103980d40518031071801d904c0580084d0001c0c01041d0f0301990000e6921030006c4d5140d040a00350191901c0c40500c052030300d002150006440c00305c6120f02d10340102c441083d4201c0d16070510060102c0c540c00b04064905118000c540980090010003100720b80c21300500c0c240060101800710000d802c21041c6100c41704170b0701c41c00039020180c3c5080850fa000b40f0040b000c82d0340d50307001d494103075185d00494000d01101c4222b2000e24040c8280c100c07110780b00d01c0c0308032200c1c036490380c8480066044070000d00841c00164003560420742a1708040605503000f58050410110140313450700d030701612808001080f500410074405010f200e10100c6003400d40307181c508410800d1440c01400c154440703103072017101044003400342c40441e003d4a0188404681104040c3c814001c4681b208c518a03503038448000e02580c0380c4150304d14201c00070640c45800054a01c140e403810080c414194285000e074002e150305440e15503072003000103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 659228911 1250 659227661 659227691
    0x90103120815210706020102030c04120309050405130606050330090402030907060e041a1c0618020310090f0305030c0f03010e01090b010804080d2a020f07080706020c13 74
    0x181d0b9841c495500841c08503003401e81079084c030445601401c2568014820310034030711000030980c2e05a8240500b09100e982c80c6003412111198035921454001d440d00062040748a40b441c0b8070682203000f500244480c50b0346000781942e944980c0c190120807140c0c551b103072690b0030566602a1406d80d0101440342415400710004007264004e0380e4101807980700d00420000990001300008240704115170070810043c00f4402c01c3c290000700403005114080d0501400390185180c1a2065400d421100030450394138810a4000384c000056000ea01c01d218843c440101c0f0803090007814131041e40b1040e000d07543c0e070040e40c040d00c15400142241d8034510040c80441f00040c55080558000d00c000154140154900f0820200320b40d201000181000699403c0002065900303003150690030360b03402c000610103c01911204800b101d51040e03031079101c203000c61b240003d500040b0040e0b2080310f90240c1d443e41707645c0e045c10340d600d45940c4110000f5130400a0343c41e0440c9001c00c14000706408035100480d11074400c07940c003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 659230161 1250 659228911 659228929
    0xa150509090f04031137171e04031109040510090b0609061f05090301020403081201032a09150816032109031e02130603060506090103120815 62
    0x441d401010350820041450b40c0900d017045001c0040026100740012036024140c100030420005185d08031544c0d02d040c6e4100003010342203032650850b2102500c1600d110341140c0e80d030300c80180f0680340441c2843c005203a5010208031382c00c0b60b921040307680c0034891300c1c42402041e4400070015501030054101d116940141c5c4d000707143e026441088010202d2a0030801c02500d002e01900c03e0307004466041060003000204120814004540c0c1000d9071111078030400a07019100e02c0d00300070190480070a4040b4089040c41c0c540d816280b05a086850107504070009a07544400885028800d01700c03000c0810090103241c0c46007500030001d0800085980d00c405640d8502180c030b00c2192043d45ca040010014000c00d00807000f00c0440307515a0724541b04649000a107c0c03c40e600010f890704020417581c0c14504680410b01c480302d9800381c0000c10b560003111580006010314030050301c07100e007004005489031400481a5040c0c90303000401103515000000100c60008004140c5101030003a2200c14185654038061 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 659231411 1250 659230161 659230171
    0x18120601091125030905131b051227030a0206150607080315040207080c0c0909011b050f0403120903030e010c2a05031903021b1f170c0702010f0e0a15050909 69
    0x2088c001020380d6011024000113481c802001024401c0c2e00c03c040030f409040360001c1401c402c0c0070209041c80050040c1594170b0180c1c91242c0720000e9081030081c0c010588500c66546203a00b41c280348404030902c40030344112030307005164a0303007000015040090544800108900600014204003440c2d0310700310542e02022906200d580041421a02c2d842d2084819074000500300081c07140c1642c840f036828000c106d6201e510b0030303c80003240080b07400c0c0003c02502e000f95002a20101aa191010090038112040c0402c0c2e001914078802c80072194011b40c5003d030700c280e21050541403c5e0310343c020419000c0c08100c544c9000c003120440011141d50810888141d2031090703e4100b0304a040c0d150103803601442c0712507640103004030203144450780e13030340780c981141820b00c0c0c80c0500420302c441a00721802d031096110000780c46041c0302030100850015018103030091003a00d40021a09410300c06a0344440441506c41d800400c2d50002e004030741c510540c8280105031421f10504120b400720005110443c1262 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 659232661 1250 659231411 659231449
    0x70b0a0c060b0a03120e04020d020d060806010f030b0106080910050a0213170c1c14210c070504150302032a01050f0f18120601091125030905 62
    0x40280500c0203034401c041440d9401c40d920803240d413540e603c004d8100103104821050207000000c041d0384d6200ca804032031754006041d4046503075001105119008000c180101a801e2041e01c0001c200744144121250569411040c482c5403686003841c103c031621001451900e0502030991420040080340c02054041d10755910302685800e1340401c140840c2900358801a0701d200054600030700ea03400801e005202d101c06454014500052446a10b23071103030f5002d401050681900340e0840c905502041c0603002c0900e08068104070b40d145580c0d09103500480300d01400d103410502040150349895441500340e03c0080c0c5080d003042d0358980000c0c2c00c040156104400c4055000307074850002000181462080e00309003040303428038116201d030380d075140100810148401000541d0280c41c503209900c41c1801c50006058280341202c585000e600c5070004c1c41019504c60620948603032000f0040c060760b01c101d031990700a08246116154101d2001c040c0c02e0190700344030304a000802c2c0c60325040c0b054044084940 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 659233911 1250 659232661 659232677
    0x16050106091a1302220b0a3902030f0f07080c0102030406080106140904110901020d090602030a2a051c0e1809071e05030618060414070b0a 61
    0x490000ba18a070039100c424825207000d440150707075a201c40d8481c0f109444840141c466880707040300b038064000c0080d4011410000722002400040705001003107000401d41d900550400000640c914020100c122585224070344040301c0300751111090b100f5009030000f000c86040d129241e4083e41400344815260115420075001402035003002c0001c0021014284001e40c45c040c94080020f044903070600405d0b0801c1110000403107c0800300c000d4400216008008000355404603c403900180d2140704c000b409070080c0d15140420502603500c840c00ca503e41c0e0059440c205c03075000110350b02d481c0e001c10b50b0011040d10540921002044131f2942c1d0141c0710b1001403802e51100240c0f0504028002802c800700480d10801c10301395112416003014443c14041c10583d9500c0e0904440e0801e4210f40104000b10608069014800500d104d940d04881058060720b81d145c42d4800040c440c000d8070010503101e0b5121001240001300079103000c5500c1c0d200070080e40d04107520717185802003e40c400614800080d00003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 659235161 1250 659233911 659233919
    0xb0409081603110f0601290a030f0f05040210030e0307060510030b010b090a0b09013f05010806040f231011090d0803060409020a0e0a1d0307021516050106 68
    0x1000c03da00701c01e15804000c0c51484010800b195550405000c0c6071015590b56005400c0907450700545040040d21031605500e400c43c0010080040c00892043d160090502e00040608038140c42100c0c0240d4014243d61240028000213802600c805402404c40d88020002c0c00003003542841200e01650381100002065861414803688144040c0c00c1203141c1c050405c5648002d61f69002c540044074100e6080a41b40c01c28900140d0b50079000d0141e290251089180d501c2140805900d510102429404028550b0000110840403190b00b4012510769510400110700802d151071440955540b0482c03440300398010300001e224240d080c111408c0100d03484400064400c0d0854003d01c984000782650060500314940002041c00c500050081c044000000102c2c8054841d90000d0310301d0340e00680200c4025944103180400d6903012035030403101030310b03021134511400c40c44289000f101c94454002c5003070140703e400304181000102e03049018610100070b0342e0301398541c1401410305140181c0c00018201e01d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 659236411 1250 659235161 659235167
    0x60f0d0b0a02181f0f1e0c021504060e0402090a031203050610142a070b19052b0f0c0201090201031104060504180906020c03030121020f040b0409081603 67
    0x640f145a4481d00010074481c40f03044000380d45281d01c1c2d506140803903030005100c6007030710003110500106205108070342204001035004110340788154820754110342c5500c1400e5141c10540070368054800000d5204c0700e41c070042e00d0309170040c22804000400341d040c00d0790340b9038a4038007841c3c4a602e140d000c00c0d00c8604100c10391910f1700280b07501c400d443c241111500300e020ba2200c001d11401d03401c0030740d05492400c48103821040b000c1d644c004414110854802a81750384040040b40c008003055503030f04e88480d08525034284100290b540d584a10420620600443d030355920001101004650075141e4a924840030b290403030044000c0244a500000358440399800014246c0302c0e031455220b2a413070100400c02a041d031000440e0100d5104550701d0540410102481014105020b006040c05002260410400c100407000390f0413603821035510903d12124408040420340310070006540a203a504e0010210305080d0001d640f411002080040c00806030355800c000354200e1902e44510807940c500c25000c040e0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 659237661 1250 659236411 659236447
    0x1504090c0c0b1f0603020a1112130803160311031603090302030f070605091e0a030507170a03050901050f1201030503030105010e030105090a14070e01090b010e1206060f0d0b0a02 78
    0x200a0950a100c1c07120000c003090f08414034420341c2c1c109940050361103c07103440b980c0c02c00c070b440d0800130a6403003154180c180c0c010140c0005001496a81802a0006240000104aa8040c4080a031704560f400581c0c0b000e07101035440980c1d03c182c82c0001c101484044040c83c030600b8410307210384c840760819800c1d4014035217032080242503072103140c0c071191090101940000940c1c0103078070101c1e079021b001101400c0340a2840513903d92039402c440c07403800c0402000342c003180e18420385440044502880801461f1140d45142e1003c019020176003c002500c80c0e03500c00c0005007090380c0551080c4c5c0c40c08824000d00400d1003001d83c410798541e0030100c014030580d03034000402d41401000300c1c000d02681c107120480c44d403602001c0c1c40c02005406011050f90321580d0910120000345900c0c501044250707502c4251002402c245480315001940244854119241075040544c448641500a0040d0f95490f001e01c0162041c000c04568000039141c81800054176203e5518882c01c5020030250303c5102001c968a07540c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 659238911 1250 659237661 659237671
    0x1602010b010215090c0301050c0a0e01181203050f1b12070803190b21120f0711060913060305060c0c0a030c020d14011505010311091504090c0c0b 64
    0x6414100380d0603250380c0c0050403900c190036126101c03010340c49014085217086580c200c03941c0c240d402c14040121641030500035043c0007000303441c1d80c00d540000f000115460b0024650f1070401501103d0180541c2030a00898180315102c2d0502c03610702134440d680384070345070030500718094403420140c10a117141005004a245183c162042e1504043d001c0d51117508501004040849440d0040c0c0210003885207030f01700490440002c1d0582c012541521060310001e1381c5044410407a2080409140b0100c01410450f000c2c404a01d100c141000c40640e2000c1d105055446010782c8150144002c081c3c9a441135444880000000d100252240ca903140c0507051078001000e0501481060020301d0340e079080851605002079040c90848129801880010280d4601c0c40000c0c1400c1919107031000c4502d41584814002c0b03003808409143c05955200450598001d0514410407240501002205040c40c06000700700411004c3c20b641041c4e214140300303003140c202c903001d040040e0340750801400384814801c0c059001 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 659240161 1250 659238911 659238913
    0x1214030901020a0222060e160801050607080304050c030d05040e06090903090d03050d110a1e050a0f020a0b041b1505040b0703030213060f0314040c0b03190608061602 73
    0x580c00c20010751940000c40e0064054220034081d03500c195182c21101148074010403080141d1030f211040301c41110011200704404042c07445859038078500400000381200d1008103820b25050781940c41d000b15404c0504211190310030f0a5820903036541c00e001034a02120140d55032034907a4604001407078000d41c013030003482c01250f5807028401030711000300844014840070380307d82034100410b1608492034405c40e034411405502d02141ea42050203603100030608440c4660b1596001985042d5440607031071a0141040412410484c003002d2502030b040f400c2c204031090040d14910112515000960038040381c1c119440c0016030320000e0b0700d101a62682010f4002070208884060400102401910450203400b241550125071001058407a4040724009081e0544440665039074060160008646501c0d040c0800d0030007001c9154120194021441a6045841007458601e4403c0c0101aa80060800461000c2401900300000c805024450003030180030300804140c581028110003154440507a5011 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 659241411 1250 659240161 659240167
    0x9040203070603090507080604030915030b0f0906040e1506120d080730141506040902090d080c06061306080c090c21041a07270f121403 60
    0x540c80c0000c11005403403480c10005400082030034801c0c50f00e4900ea200400074801c020402080651203c00041102e00409200c20301000e40e14080d010303541c20280d020742000035100c07490b01c00e2514000c402e03004440504000b5010f160f00b0203003070826503082c402d040008207000030300c861428022400b0703040c4264000907114800c2c1d01e0030000c0c00d5000c060b1941080100c11001e51035902400c6d801c241c210001080d1746c8420f1842c0303040060150007442409100c02031210000703a01e11052007511296008020245407900741000f000070000d4000901054200e00b0710450340340010511402040e19000300002060369151200030000e03d900003682d07002d0910b0500200308020000050003840741401200c080d80666601c3c81c4104060090305d00862410494201c3c0c071a05011382804a401070340130381000300760b043c0e401c000c01d00c41c60002d440640000710131304110b0b14500315440320b119030170301d0884c982801c2d81d50f64880f40d100403c464200340c000ca00e2281d5002c04010b008164503644408900245007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 659242661 1250 659241411 659241413
    0x504050c030f060a02250b0907050301021914220e0109020a08070309141204060201180b060d0602040306020f040e1e061009090515010f050f070602070501020702030f06070207050904 80
    0x929038001600264640740c001c1b03071584215030b05c845050346100040b42088203a081c0c41c10005082c807030a8522401502400360041401d04060084541c155980300701d611150103c1c82084a020000c41c0404c5192a0244001d08504105045001400b40007e400c1114903042400d07a40503a50181e00140801d40f041068080e0f15400940e4254130081500300040e984200d401d21401c10500e0f03450280c418003c0e030204080001d84000500700f40c850a5000f00600c0e6100c10340c034214a414150003078103044440e80002c586150480f480c03a4880d01c00d210140c10b0075600d50304c51050340c200e24440120094003003001d1205045005059030700101801801c00c0b403105c0020030701040d11014040c18083e44144504690582c0542c0c2c0e0072008080f41c45007009a4500350303450540d102140702400e80000c00da51901c0c8841072203a4182c0d01411914040b0740d00c0d00d8082e07583c134802940a10400c9402e55028041c03c000750740c06200c08542801144090710700f916002030000c0c20030365a608600d1041c0d0210003804 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 659243911 1250 659242661 659242663
    0xc02060a0c0c0609020d1a0108012304060b120a050319170f07030905030c0c0a05011701050603060a0312020c010908070308070f0219141009050f040c0e030102040303030504050c030f 80
    0x14441600210001044600390021a002c40380041c805880e6220030300b40c24110a0081f600d85040b00e0b400002004081000e422014085000d02d0310089420717202c01c041400700d6226440b0401460f801060302c155070070740701c41e01c0e030a080a490056810f608007094485403800c03400200c466100852514084680c2000180285000050080c01d61100c814001540c9940030fa489050f0442d0840c007120f854250400249654402415400d03008042081000860354010341012a16500c02c0d80000280d0703090000740310311070308010001e550101c400c82000001c078841c1d8107550017140041d409403079060135007400541107008075400100164070242c0c080000c03607131000640302280ea0010302035a05e0b4626000003070084c0240d101c000c1d0140c3c440100000c03240c0d0603240c91080400d0503139521280007480003041d0391608091041c41d4201400300310840840c03910303a006010350f42c10b030309040002d40f800002107030032a001a0001c0b00440c3c0d4a106000a0003c10060380d800e80000310014079281016180305 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 659245161 1250 659243911 659243927
    0x3403030525080702011d01091a130b570703031d010608061e01030b0402060901031b23030112020d080c01230702010908040b0a0210050a0c02060a0c 65
    0x190410990b01c011a414074800c1d0080800220700409664000c1000c0300305038000d06940108480051007400092051410055643d03c11000400d484820b0b01e0ba648620340303980e030010018650702c4503100011010783e01d80c00d1440b800b020426046a6417104000c03204070715000c1d8071a10303582140302040e04444003407404111400203a0614000c0b854080c3c0c1e03ca019514100b09208000d503500f08100814030040000d6298824640007250049114100044801185080c000984035900c560005400b40c10948010701c3d03804010b2400060410001c110381940b85000380c0c0d2702c00060f800310410110151740c6581c92030b078400c02407440751a5500d401405440c51804000c02800389100d03480c07040512550205451031214440001d02c140d121070443c0140b8070100c65610000c030040540402d0840e0320500c10500001c2d801070241d40750608090029146070000d1180e04114030459084020206442c000c10380103c0d4085404603d0080181c006400c1410040456884a182c80c9910030314a41c00380781 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 659246411 1250 659245161 659245231
    0x2070b30062d0d050102071a040b16050904060f0609080715080408040807030f02010311070309051201062606010b0a09140406120b04020a0b1e34030305 67
    0x400c20a00c056040c031400c0c1c0b040709020b00d5a10042010000c41403180640080211070b2142c0030403014002c551080c2480e102084e0f0b0060003507000000011082c8001c91200c8420f08100d0074150301341001c060000b030690b085030f0403400301e170001200100811340d0440d81c3d10b005454003a010b402d14600344001c2900101d40401c03030000b04003802011400303015036001102d003c0c180c18030035200704603260300b0130030b4655204010817800207207400210400080e01206440c10182d0690750400303268500000c00c07950403000c9040840c9556240000110141050b003600c402011140200a03a984d072a1807003410300405a018540c0c4130740c104103020456a200d14460183d640602d00c40e01182d00700300105004100d2078122010500701d4070541070078008844d200da0f21039032003200e808441a44030180742c500d5010701e10400590242c2d1b400c0c1003542401840c040c0038120020701000242140000040819a02c014a042c10b092100005074040c1a80750040d1a8030811070007040c1c0d1001103c03401005081e0f54071203 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 659247661 1250 659246411 659246449
    0x60e07050a17070905030604050615010905010c060b0f060a0804061503020a06140f030c0c1006050f06030a0902061c14040b0408070606050310020405120604031e02070b3006 76
    0x100140f02c00b401000c848001d840045d0813180e144c5464541165540300c142d134050030421420001001c0e0b580705010100550380107a650084d0346000d40d990380d02500d583d08465034028020084841e083c0c4500c8007a0100f94000d55494402c1e04090030004115031016048001041c0455410b101503102d401c07a01c81100e806180c483c20164001015246502a0398103010641c00000b050244000520000e0300454035600d056900001030100d80c9002c41c5d03c0c500c1010340101c00507000d82005e10f400000f5641c08a200c240c00309030040301b640007410355405400c940c00c0b1292241c5011045840a115070a00010704a118139460b003003030340300c01a104070000c100800d500c00004106040203080d400c1000113202c05811074540d01e03200100f55010350464086d0340e00034815010140402d0741c000031a04d008507090784840817640201c284085041540c80b245030150f208900000480003544001069015051901c5658082c00411941c4002204446484038001004103010f110307070764085500c51a10040f0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 659248911 1250 659247661 659247707
    0xe0610120f0e2415120f0a0c030201020c0a0e1801090203030d0c091a09090403030906060611161217040806041a010806041a060d0b09100e0601060903060c0918060e07050a 75
    0x400310790301e04139050410761b4081c0a4192410304201c2d410038000c042c0d074800d800f81d0f03544070012801d110381b001c450b2003080d513074070300020101c7e04039560300b41e100c40360001c40b00000c0782099840d0082840c65000401d250f480c0d59079102c04003a040c2d4083e03070000140550350b5900c2c0c4034400c9030303080c10040d02404284501c02c00120002c9400c25011303500c00c1d011107502680034003100c0c5c3d0b6800054070780b89103040c0400346c0f03000f0040c40703c034007801e00307514902680c0340c44280d2074040030750340c036039005401c545682103851020400020801c1c15040260a1085100305034641000c2c41081d0703446550f64041c1d104070540d9011909000015000c03003034030441801750400d014900d03a079401c0000d155031400b100140a650b4003000323000c0f45040c04901c40c1e500b0300300ea200c01d101900c0300c403840c1582c45100740300f240c0005100c0d510620010720650003041c610200d500d8a0103a580e201c127090722400000e110586483c0380d80c5c1c0420028802007600700c5610445500708142840b42c102c40280040d040c1074103c1c0e108071181c1c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 659250161 1250 659248911 659248939
    0xf050a09080d0804050f0d021203060a08070b134b030b10080c01051b03040e09010207020a050a0b041e080303130605010e0610120f0e2415 61
    0x11401100200000401c680480400201c0070f040c07008156419103003030094500da01003615000030012651489a8000c142414441035465503940018266030b510002c1c44600045082041000c14040c014980c407440c1e645903021244c92000181398410358031700d19403c40d51100715404c003a15120380d0701400c003240407403034001400c00819017901d003409000d600074038004024021f40219080c41822840c400b0311b201512541c540396249007007004180081c6040000118608254807072030028420b050449042580701d600003071001d00201c481009603980030901400f90710741500c6900040c507096950504031824210404418400d60091468001580300100380b82e1701148400c10007401e048040d261241851f80c003104024405e0340d019601c0d80d04190012071203141c480c402500401c0010078400c06000096429105d801e45407181c0c10009584490b1070310b43e1142401000e08001900c00036051031001c00c590342e80f10100e021641c0000c2842c1d1802c01070750414502441003140002c551700d51070300507a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 659251411 1250 659250161 659250167
    0x8070b16060605060a0909060b25150c0c060507110c2803110907020304080607030b1f260103050304120804031e1104020a0e121218040c020a030f050a 66
    0x100e80d10854100c13000003061018070354010010001c0d90000b040a00c41c2c607070b5030011040139024841c1c66118240003100b6a03401c10580d5189a02824800d5248480701d0052032103d60854510805c0040071800c000c442c00e041080c2407140380da1104160a00c0f50400110550707055480c5440200303240034000320043c554035450800040090042084030011f01c940d12454a5030182501035006800750076400049400760380003000b510159007165000700a55a202c800c21000f0300058003000f500452014031600d2848400c0143d4251140030391594600031070b8103050310300080c10304485034142d08080b0300103100103030010044030116540780d440345944100d14140b00070184120360000785051907580e080f0400d045603054030322006000e40f0a41d065111181709001c2a0b114442e40c07000014038009c0312b034885140c142550402c0602080469070700304001d01300c0c04c69581c004800d091030b00780c07006900051890300d40100903d016482c80507080c01622a9806030811042d80040018048046031040410744 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 659252661 1250 659251411 659251421
    0x14100e090a08030c0405030106061110050a0207060e2d0a080d0e030c010608070e070e041e0f0501090e0a0305040905071e0f0f0e0a09050402040b04050906010f08070b1606 75
    0x40c02c440c0071581c0307040c0641d00b05801e901c07520809000307500b4508005181400b81d0784603d424151407001e81a00c2c0c40da40c08440c0100801081101e110f80d0a101c80404140140303d11078041c11081d00510824120001080043c15445103600e106840d04915990319100851a0007485a100c8102500e5400745900342014184581040149120100380c0407401241508420101e600c0ea0080d03c103925140c04a204d0710b400c3c212903100108a404110039400d040c9640800344108c203228400214600326040c40b42510707401e03000f8003009134036507006001483c441c0c816034a202140301c00601804031039580c090503c0c02680302d540c459541c0c8000140059015142040d10030450040859604010071030140090300310b50744400000d140704a40c070000d20b01a040d510b81d001c038018004184180303422a18006031200520480c1c10548500304842a03846601510f170060b410100501020f6050107903181d40307031a0641c0901082e0340007036000c1003d500f103035040300c034074400810302a100c42041e810a100580 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 659253911 1250 659252661 659252663
    0x3070204090c03020414251d04090c06120b09040201171b030a061514041208160c18110306010804020105160c05010e01020c060a0c0f080f0d14100e090a 67
    0xd06001d138000c140078200b5101c034480c11819400041c08480042c0e080e003071f43c1010f1802e0003c1a03098622188c00400e00246100d02c100080000c5440d002c1c0782c0d0341380340c04005903202601013140e008074420610102e002d2440c2c000b4043e2110465490030360002010340700da1101c43c400388052403001c00d0780380c0e006000050b290b26011034982d98034180080400c0080559118454084042c0b54107031001522400c4c21481c0c0030742441d6428200342c00d00740b440c0801d4144401c111040d010810454002c01c002801f40b480003809100441441e51520710100f0350b82060008541ca141d14002c80042190130078419070360050020b290002c6035079902d01c01610f00d8868001c081a02c41c520000440400449001c1c076402e5aa083c0d0391520010200401039948580803040140d01c010309018500c5510311541c4101d440e03500a60101c40c004d001030f151420b1503484118102032a800000e82045041824060300950003148038a92400c3e01d006140810f00715864061002d40c0d0741035002240302c03207408210241000e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 659255161 1250 659253911 659253919
    0x2060f0307050a080f0411120304180e01050603060106121d1b0111030a090e1003080c03030f01170606040c02120406031b020a051207030309080724060803070204090c0302 75
    0x40d04100704054119042040b0190006107994006220001155419806240c1c0410a40083d244003030070070070440e20384101c40d0a82c2c4005e010020b503058040c00c440714412460140000c011620418503420f6502c0100001d002e5440103004120490f402040640700c080c2c02100000c205080380c0a030898030146291b05445441035401c3c00564406420304228869026210361140f071b80c1701072480742c8a000b01c0000d40046401d0003000c0200d03442080002ea1300c02e803a030040c40c8a55440b940c81d03000340d401018492025501c088104050010002e0032a80074042040b015864038140800082d5988002003c6601550f12414410a418004c00480628200500d201601d03203444840090041c5621100e5550f840711000d040d6a23400c3c00810000710042d0004064105a80201d9140d9680e92269004504040e600e001d5000850540c20190040a00c102184140003c1407003601010345480c210002c109454118100b06508001003200c007801d41c10f03140072484000c141041c80c0e640402b54070180d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 659256411 1250 659255161 659255167
    0x90604060315150c1518080c010b06070f0201030b041103011502100213031b0f060801082a0114160f14030306011706031c0201060620120702060f 64
    0x806505078000000c82000961480340483e40c41d859201d0b0028207904180c003180328882c440c40803c681c40500b1542e2094480c010941c810124a031000717070400c420040e50034034008501034800c85820301030381c11201c0044440703608104203601c0c0e207030544140c0000241899941c0c08402c009446035040815800b1407462855120f680d2028583e8110684003030241c0140518024036142c1c0086100b580c56040c0021311000d4104e0031607641030042145c2d00c2130084490190000000c819041da1040c03005030010340d481a20651500518601c0c040344644400e1603500c01720588001c001100c4209800c4c180300346019503c2c00030700c420100c03441c81441004441050307080507a00911080c2500e003445207106500e0003050317544411810342c80340001e946140c00148014400301080080c0400c05030407440007025504000200c1d250004001003117607040003d40d458020400c0703841d4000c202d52041c02400350b510880b4501041c50140c4803581024091003800010605109545039541a9640c0d94219000155 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 659257661 1250 659256411 659256419
    0x13090302011d031e07110910080607050901080c0705151302060c010b011412010e1504020c0a030f0f1e09030803010815061e0405041514100f0b03070c0206090604 71
    0x10f00c90748104900181201901100500440314070100c595460304010345200d50700b140780400c90410005403440c420f80050301c40200e008030b014403180d400b4200035110581d0302ca0710400003400300e41d001880d14100d1030040c407451001c203401040080f4804005a40c0e202c242e914520041280e850440c406500010040350000b04000158403102444000341c0703811914441c0084058020710800584c410350013080401044008081c000040d008940c0d4000c01110180c4c0c2c001190032a003160700201a90341c00b078402a410f16411000d0341c40c02c81603505d0080c7ea030030200d040c0a04081c013480b1602d46010404d6a330074900c0d91203400804082c60b4014060b547c0c07541c1d80c84170380d41d45170070b114440751400080d0000310b181131804040c841c0b441d061615002407900c80c2503003044010040100180c458100380d20a902c1d01600034400d044654103810a564a1030506008030000c1f22940d1300046c0040c0c2d81c2c07a006000c0070050074152940013444c1d1410801c0007100d480442c40074000c2003c00b98120601190203d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 659258911 1250 659257661 659257663
    0x603050c0d0f241e1a0703050f071b0e1e100801420902180307060908010509060702060f0a0603080a050307020d02010b060405011206180207051b13090302011d 70
    0x9048130041c0180d001e54044500c07a04403c90460703c02d1481c01c03c03100040d01005a18070b005082041c3c0242807050803c0e12104030440141c0c0086800c684094a04088106030b148150300f58015100c0001200b1245ca85210ba1448060403440031389500310018000840c2500e83c02d00c29005841068001d000c007040700500e00b41443c02d4029222060122552980030a988410644000c0b580712072440c0c041501d03240c072013030080d170081501c1452011003014010250301d04000580040a060341c41d41c08007481c012400d42100d0300546195625000102842a11503000900366000001362400a0147d290500d410300204a550703c0205100c0700806c81d01e40264000000d184160059000e440300000e00010490880e0f0b030620005a02120910091045510131050b000c070000802000003105500c0342080305100c50031050446000390005018400c03ca001d01070031040341f5000c683c4203032180d480d2000a820864507000003150654540301082418803d410500c00084c610620107109940b4600c11 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 659260161 1250 659258911 659258981
    0x12d0905030f0310141e010e19080118020d0b0603030c06070306031101180e060303070f0c090b120304030813052101051608160201060b03010b040f0603050c0d0f 71
    0x1000c1c009071500c1c000032229625591240044801840d4030141b1400017495100c0324044002c1c1810040031845052560310780c41c040d003103050212a401c1c90105e20b8100580d017507d61200d0f603c4064215002c501c030040e200e5035450559940d01c0f0001c484c4c0c41d070360700c7d01091440c061948006990320a40701070001e0f4507003603801403050364040d5903001d007200b03c60380064030301c41102d03d40c40740b41142140040000300440d83d54180c020380010103407403414140740c60f0800c0c0760030146425079504490300c104201c1c0c002c5500c5911010481500c04042518498030581e480c1c2c021131001a0031041e001036144c1000c1d809144001c081c020080004628080c4400403401d99500c1d9151072209601c1c017400f041c10604000d207540f465036800e5440703d41c1f07913540101164014010b543c0103802c0d03640710140440c01c0800800514081d0045552032925a0300e03203140402c1c03008041d8840010700d1328000034403409005010848540d154003400206900b02141c0c400c41c001c1072448200541868004c3e8a10304925a600f05 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 659261411 1250 659260161 659260171
    0x3020d143901080919080405061c061703030f0403030902060304030e01030c08060d081308030f031b0906090402071a01080c03010f05010b1902100501120b09012d0905030f03 76
    0x41d820000c1090300054034880801c0d03680c1503d50380a20401440c076102c00d0400c42d0003622512030b850030325a4500115a46e50044550114020511810380d608070040d4071410004220184030076a60844451700c0c69240d210150035441d0b0901c0c1c0f40c00050a05000e508150115a40036115540da0320f000e0400a080030000781e070050000e4181507480000030322038030f181802820020b000c48070b4032400d55a055412b43c0401e400d1080001c5441000440f4841400038151102601c20403c3d83c0e89071104184850b412a50b401c82010319040c490241d003a00c4542c01c4d211003072001e13200140d94500030304040d0070901004810460680d02c220002ca0040d00100e010304942c81c0640c024000c4840075406030080c0ca109004049031040c00384044150350205158401486c00d60b8015101040882c4030010107441d02604100c202c01ca010b55103104120b49004880da00c41c250000802c4850f14980068060201c42260316460840120300400525141e50040300416401800c0765a01c02d5000118000b6410880b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 659262661 1250 659261411 659261503
    0x915051309060810110a030c0215040606030203070806070206070c02181006140906160311010c020303042102070303030c12050f061002071505030a0b181f03020d14 72
    0x800c5000c2030454082c588411904601e070307a050218000045005085032039086045105100d0420711f100d02102b44103014501403480440c00703130b0950060500d48070096008100660011b002c0110745940031400580040c1c0b0b81c68241fa056000740005490320503d2401e9400e03544820003448070340805a1101c07801c941407034480800307105a80e00c4055240c01090301030764110702c2c10480940d80c034001c11151b00c0b481e032007410102c02242e444012282191101021000540e1001041c0001d01281e11010030410107a804240399400010000035291b100c144030081c01c0c103850b5000780c3d1402c1d010340403400d403070b401d218020009460000100c010b990410748040d401011040c0c480c5550a20201d90201a1004200600c0506002000480d01a0710007000c012000396a52b402356500e6883c141000d20404262201c4215410500e60703111700d81a00406140d01003510030001c00040e1580302140e400d6581100c065840c0d201e0220b031032401c040d2914041c80c1182d85524201180c0d82082d90146410444c2c10 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 659263911 1250 659262661 659262673
    0xd0806030d030605090a0209060f131e061d0109090e0105180705010807110c1e0a0509090d031515021b2b030e12010e0f060709150513090608 62
    0x714050301141e406000c0c4035045448000014800709158004215041020300405e152560a10120540350040010822026103000301000407407000c0c40c1e01820748805000d0071414525240c1e014201c40724811358804010551001c03002641c1c02483c10030009c0201e00000d00a80040c444c50354000c0408403840c14460761000d140e607821220001c1c04605489041e1030300c0039a52a10441603414813484070490782a4400d000c250309860700c5500c2c443c647c0c1c8090180d02011020404100a5103000c00e402c454014215902000346410700001c0310070902c0d1442c00c00180880100700f40070301088294100622290380003000b0082142d000640c01e010030800919282c410b1040000c00c030b441c40405131400c034100c40d040c5e07919615440100e00d00d098a840780c00c00021620303412020605c2091012665012039560f510740100c0c2440074866490001c2030700c2c02070119440c000303a010304190440d000b100d0003a20200e942c1d142150140049506c08030810034020001c50b580c0210703402410460040d290140694 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 659265161 1250 659263911 659263933
    0x60c1403070507051309060204030c0501120b150a0302071e05160f14030a05120d06320109030c09020316110a150b040e0303040512031e0c0405030d080603 68
    0x8000c0c1d50240e6803100281482500d41030401c00c900f0341c45210104401da4441603000080d04920040c0f000b14811f400008042c0e152a00151500c5481e02c51540304a052000410190b95a141c0100c441180b2101894076a02c80001c00c400038000c009004103c0e0011004000300308040b0200b00c00141d2041c021107040682d07403010020044401c0c0f0680094580403038080c400303840e65038034103001c0380c5e80034040703406100150700d641d4a82541000308210440c0300060703c030001d01150082d800588140c03c800280c02c20401d411200c01c40c0c1c50501101d8080f040c110024450303114135001c500440d0010001118207464808460080d031080d5020f118100c10214061641801590848000e4422001a040c148483c1d15a039408195401034941c1c85907440d0348060050780e0704d00c01d011134400008025910b0340b80528041e031404400c9272054401b15020300c02c120044040f8104000d0381c0c0c00c640c1e0301c85166200d80ca8994094040c903040543c0c140035400601d00b1190b03000309614407804007142100c3e250148 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 659266411 1250 659265161 659265163
    0x30c0504180f1212051311010e150327010f1404050c010807050c01020c07090e010b0a14030304050d052b0c06151205030a140301180b0316060c14 64
    0x400c401010b0780480c02c0101c020804040101c55216881c4c141909441561300c0c43e4070031202c0407642480040041c0c0d40e400c050000d0154020781020080c20801c10100394500000c00c1d102100190200c841000000209500680c1008030b522174a04500d01d403000d40440900c9000c0e14035129454400b9140c10ba25044c3e00d440342040a0203190020b015003816072110004480e079043c01003802060080030450050710910901c0101020560080a018858140750010301915000074845d82241e0405e4200c020a5943d200e46104450110320a60072000d150008241140225031006511440f002c0600e018824040b40f043e11300e00c0d0000d40c0507100050300104010403035201e85034600107900d8180200010b50144d000d00400740c000020440340c1965111200d614900d2548211090f400200d8000003240e08050310114000281011508560520719642d40c144001c0c0c40c0303407400a4985242e6149031310144a130701c15100d94003a41000701515800d0180469201000c100c408000c010301c445d607031401c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 659267661 1250 659266411 659266451
    0x40c0f11030f0906130302030706110f1209060c0a06020f07060506010c080d020a180602031c050702030d050601050702041410120507090e121318140c03070905030601030c0504 77
    0x600b82242070a24a015080c0032403504480a00f80303038035006800101c0503030340c04c002c141c0c01031501b41ea46c12000740c00410440d09200c1c080b0451005a80200c280c81c0c00081c0c07000603995a0082618155280d10041181c5843c2c000071001c0501514070006209202c482c2c8a4014000d00340100c01c00d0149440d03041c01101c05200d0450050328908043c031041c8807000c03140c0c000f0000b41c0f4041c904080a901c101001d003072410341503484100136074000030f50004411003050342420300710b04444082200b4901200040d480e4072801050f102c00590307490000d9800e0707019009489186402400070000e134582036017284e14041c001e03508141c1c4011144400070b4000d140340a060983ca0703211000d841c06524101644000d00304540701101180141401e0761850b007442d40c042c000024299003ca480185000b200641840b1700d030040205440c1042060b80f0f214040150303032500a0b40003159140d03295a02d0000700d604e0340da69008a681805580300000901648001c084265101204c04000c0c1c1902da9070b264a100c0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 659268911 1250 659267661 659267677
    0x70c1415120705030a060f080f1e0c15121f1a070209040201170a06031110021f0605100e0a0902130e0601031e05070e030f030906030a0209040c0f1103 66
    0x40d0400001c80722803183c1d000d19000040c2c520040785440d03e4100319145075080e0303084010786030b000441d2250920400c005c102101280303054910002d40090072219124035092189600648450480002c0c030503540307041b02d400b940205410840d81c07d01c0c50070100a4401c2114001c120f402204c40400d06504912000c0d10940078044030310f140a0f46603080c4811020001d00a030f05000b0a29294520562100e0900e803050140380310000740107045144c10740c0001100c0d11414040c0070810b810039a140d80000c1c0315810310f4884808281c81c003803090800b0001d00b0058029903000400170913908081c030340150a140000c00e08603810786c0e140c0d0b1215541e00407070103404203103001034400000c200080d0b80c40c000055040401854003080300c078000a103502d00025148201d8800503580d00401031090b511640a0308140022805056040c81550740e4665a0140c0d40384180700d01d200002044829031f080d41210481d481c054410300c00f08000f0003000d020581e1300d01603d40801c0c03a0307080c2e9072095003020040710062 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 659270161 1250 659268911 659268937
    0x90c0109060c0f05070f0e0106030902010804080310050a0b0a1b0c150e04140601021b130e031603090f090b01140d18080a0212120403080606070c1415 66
    0x1251902900b00ca5405010a0a464080c6549291000724070144011005040202030031301815182081d0f03825080b505034040b10030146810f22890060782c0c0480c1244c1c11a8124124644a403101d455884504200f42c1c0015440710340460f00060b15544d07000944001881519031402c900c0451200345481e201d2158001c01d144074407a4217024a120568807031b48100c03414500110000c040002040c00c607409030f4200e00b1f20004000c104180c541c1d040040612240000381c4100400034403c0c0410130250300326007031034041a290310296034090010003c0d52155080e40030b02c54030303c0000e400d01814461490241d040196001310012411094900448200d04410303980c05010200c1400f0346e039032540100070452140f58032000c200c2c04034803245542a00041c0034030540c80d03481d20780302006858011404c0c0d038040c02d00018489800020905d0000c0b5030302513007605109038690b6a0200041ca0b902c0b48580041100c3c81e15072021544107201c1e00003012985003580c54030301e17042c001d915802ca180100501c0e0064 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 659271411 1250 659270161 659270177
    0x6021c020f0303010e0403090803030705040f050105070233210915150607020607150b010c02130207020d02090f01080607050403050d030c020c030102120f0c0301080d0c050c15090405090c01 83
    0xc42c05c914005258803d02910308880a540c554126074103541c003c3d9076480002c1c001180a108241100a111009000901b0441c3c0340c44902c0e4041032008000c2c001e102c0340682c0f8155101c40341e00c0204a40082480c40c0b83e0f505a40b4a150400600301e01c1c0c41c068070440b000da1000c0050b0024400080305550307030082c6040f42000e640c0d0583c0d800c1083e01d00250b1960070038000d21800b00140c640c08081c1c51100d101d00c003074526071042e09603c48110350b541946181000a1300d140b00d005615107102201403000d1402000da600d8070380b4000302e0424460008000c4d001021f0204000b62480400051410394210384284c4141c0d03261280d0440701e5000f83d000c043d100e42c000c0d45501c1031240c040c1d448003454103202d00548103007034000c80c002802c9810044c241600c1c14a800200141740858910003039000d0b03102100d150070b43d4100130003240c2d105142c20b180c200703124041c0b00d86001d1007400c1201421a0f0002400e00708000407400030f8222a0b0480d00505001d03600b0000440d00222020030011004101a940d00c21 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 659272661 1250 659271411 659271419
    0x2010504050318010c020a060c0303050603010606140c0123040b061e21010e1509010c02072736171e0307180b040305070303120e010606021c020f030301 67
    0x300d58103a44080c3e50601426080084c0141c48007902ca100403c2c05440e96041c1010324240a425544010040303440780c0d1400c44140071242c0c000240e80803040504c0e2549458a543c00760681c0100883e100b840d4a00000100b0b0036041081501910310076480b07890340c24a50b40b58401070000b074040142d0422001c0700c1d600c403506450309191100c011246808078a41154004424100d0700312011f48070aa0312a42014401c80c286507001120150080002e5000700485040710b0402905d81c010303805400014849600d812070104440588000481c000d240300300440a0170175200000403460000443d2014020344015a00002d21368248103e035801c080c02507440340e02c403407071507605500500d91080359204204401042d001001c1c0614803070345076030310b640d641105004030f2a07980ba04181c5c032803001c450b8108410b00010300045017407021a540350910fa40e40c001240c0b2000050086180b2285d80b40d860b0660000d4a5540003c01480700c4590348105c04d410050180d08980700c04081d0700b503656a034800c01c0100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 659273911 1250 659272661 659272687
    0x102070b04050a140607060906020d0b060f0a030b0604150210050f0f0403080705070605040f03090b040807180b19050a0b0c0616020c031c0305310c0f030c0f06020105040503 76
    0x15519034001030400d4075041b11952110100c1e00310140c107580301d60b40820244540c8e0020f100d03119071001e0407141d490170705c04044007065641c4200b54a44007055142c48002c17485865000c240c4026040c4200070a41c507142445d4025a80d8a1500342c0308065810300022643d07003061004441d00404580280040f10380c0ca0b134030155826035025192500b080070803c001c01c0400e600303114070380c010391050809030852019410010020411900050010402000100300030308002941ca411220210402b0f07031003209041c0341c000200b40d54035056410500c940000c1c9040d00c070021001d4291142150041c500387d449111003100c0c1d0141c4030506c109607000b4070206000e101a100101002e800d01e2040fa40216900004241040f20700c181e00784840c41d00200401c040c9030140120750313000d14cc07021022000c0702600c0d00203451049030303250344e0307102034001800c4414083c8410b46d8030007801c0b050002c44d0060b80e6919043d41d031340440c0d100f0303841c8400102d1404524144103000f00d602464000d0001e60403c11142070107 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 659275161 1250 659273911 659273939
    0x90501051602150c06040605010602011e110423011e0f0c0f0813081b0d0b04050a0b130c14030607050f120c0a030e060405030409110405030102030a0b0102070b04050a 73
    0x703030390041070401c1490002100760f0003002c2c10f440403800b41c100c2e070800c0c1c41c1c48420380c0c0042e0441006d59040c10590314000318524500750240001c914041010b844004075401c49100d550004103440c83c070903002d10605c40c20300000444100082c2d840040031460b500b0741e101620f211060800c0062569036045002c10b1080d031401c010340740280d030348080300030103940c0701c1d90194415030481e0f00748601007404100100041c410141e104c041a901ca0729822214400076015030041c0390010b007130100400100e0148a8200b00b541c1c84136074060f00090050900d0041170f80d50507441c2030111404400002d010505034403c0603441420b640260003030030552a0504141c50381d4200601c0d00a04040601101c40d079a401080020b00904030545c08594401d4031103002000d0390011407402c81c290344131405010008000000307c60444a505000160100d0500e40c03041d20b62040ea403101380d1540c0040f080c49000d03d10f50748041c840035026021200d00d42d0762000084210300842c0b241c15844094601c08200510f1000d0711 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 659276411 1250 659275161 659275163
    0x10f050f0f0a0804020a060801030503071e02040e01050613061802160c0f0e0c0910030f06120b07020f070608061003060308070b060a060e06030408090a12060212070905010516 77
    0x298100141c1c00c40d40851034001040754030003e50400203000640c00d101c2080c40142226103000000d40d8110313224180e485c032a003600103041c5404414440c0d02c0326242c0079020071040e8004c0090100100b650955406084252681d0348104e454144401856141c3c1c458082102c001585ca501400d0610310340330001d400c18400c0400c403020180300b00000840d80001d031405494200d401e1600d40342003e040c4844040c0080c0409401319003084000026a20300f1107203404030006140c00310b84010f0105014024100c2d0381c0c003901d00710300500701c007500f001907800701c4a218801030b070b00312005c031980e880403140d1344c102612070f00d00400c840d500882e18505000c840442c0282c914100414401d0f40c9a84401060b8480d0724141e890900c048103001551500e207001c00000c0c0101d1404114010a41c40014510f00c00584001d080b50070010300341480703449840c140001882219849240b803407450030180003943c845108244605d007090700203000c11b8069042042902c1e0706940b228200b00e50050300c5038100714400e0f4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 659277661 1250 659276411 659276437
    0x117060112020604080f0f100603150c140a0306080c010503070801060509040618090507080c0f010c021318060f1506200601060f030608061b0a030207170403020108090606010f05 78
    0x4c04150307030008000103404030f42884014820324040d040168101458280c1100d406401c1604c2000822141c95030450700041409000070940341202d4162101a20020420071004000c5021051542c05074003a00072070350000c0c01e4402217966000115154407003281c40c02d0109150f50018001c1c82e1054020300401c4038054000526603441d48482100000e10311a80700409407030742107113001c018080c010f4000808160004250303041c109400603101040c0c081c40d071410006004812010341d0b031380c1808034544000e482010084c68034429002c020400d640c04054480034208500100f001c60b091040c0b042c01d01b00041c81da07144509004080b142910804a6000714480980c00039a40b88424003525000702803580301d40110000c01d040c080c0c01c0d00c4295104210a40120080101c100d2001c0045c1d41d50001c840b40c0b00e0340d07070890420282c1c001d02504101074420350114181a90307003070f040d1000b030003501d000b62502e101c1c82c0e42c0d400c0102d9890a0449015002034000390f0031051950140e0050302aa040c121 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 659278911 1250 659277661 659277667
    0xd0f0503090a2408040302060112110d230d0c12050706050906191a01050a0212130302040b0409020d2003060408041e0308090d1a09100501170601120206 67
    0x20351001080c0c02a0812021190000c091140106403c011003501400e00c0070052a01e610302945a000508c20035420f4a1502031003030400210402d40380d450f00b0000c100700c000300002e043c03900045201e81e03523144481e0301d80001d4220001c0c00103402c011041c1c0558903a9101d82c520f0b956240181d490780020010301c0028000c45c4006006030103458410304521008062030b02c3c0035046909168180544884154a0701c00000e45290b410b020201407800700f1300708a9560000d0341c6080385405181c000b006203888020840380198030f003004240c81244e008a6061194501342802c01c0112554044003d611805030001072002a41100d011030101c003821703088854a900590119040c2102110211040800050180f005540a1408485200c0118517900d80700e811903031803044910418101c00c1c4116070144103601088405044183d40708400c461400702400c10303590059941c00142d11214000b800d0a0000ca040480c44cd41c0402400c03444004251a074a00b400e0800c481043c5201a60441010 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 659280161 1250 659278911 659278927
    0xa170915070506061f09050f0607050312010602010c1b021e0a17211b03090d03030c02010f0218040e0109080a08100f030b010330020a0b060d020d0f0503 67
    0x4580035150190190b00500b5440c9811000c20602c61000407100c06004054011082c20b01c0d44202c0c200160b510a9425402d240004c7c0c00040890081c002c0c0140b55200004d46c5d00001808452594100e0791aa0001e00840703031900e4040c1d40c0441c180841c502d05540d407140f20b002501c0d1429069465080d0102c46e1035070085518042102803509030460701c2480140c00c02d0702e04541040120006408039080c100200c03d410500380219445891120260100d021480400221b401e08c2201c2407044001d005031506007213480c0242c090705410482c1000b551909074403800070304c2ca600807101555003000d150b40303480c4211803c11005051505c3c148211350340c0c440503103000803000b40c0180720900d01034451410a103840ea4184065513982d030404001d00424002c1000001c1602a80c1415a684180005e110981072031102c4290045058054408801120306218440e0041400420706005441a803113603078858040c08009001400001c4d00a440f0100d8500441c2840e40311004140c440c4d01a6442c144030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 659281411 1250 659280161 659280199
    0x6060d0e0102030a060f08030705060402011d0d03091d0f06120c040f14090705060f0c0c030d12061a0f070302070905010902130503060910150b0304060e0106080a1709 73
    0x41100d0400c00c190f520001802030464121b00d4000070034042c0021807500d14182d4071191650405840241403041310410039602c400e88660f010400c0741d0203000d1305100c0d40d482c10b00412182d501e05c9480d41c0d000000b00d02021f9000da1742d4000780b18114041c502d20958450609102c03e0316900f0880890500030181c010203a903840e8051620038448030a03002c181d112144100d24110340c0c3c0545040c00c5a80610010001c0d515501e06407030fa0082c4030300d8140d403206c554100d694288441d0344111507242c0100c002d4100865004450041c20700340130b9500308146602c503981e00725200005110108400800c2c000c070446019944000c05a035842481a80d100341d80d10310312a400d986003a000040a1600801c44900d8200c02122100040404030300402c0e603030402540d201d40b150f15400c60a42d0a85e03d81c1d00520b203640c8041a1031005084184901c0e80d6482c0c207045c03041c01031142d027480815035402c214001800085c0001c1c6070402d036810002c0002e515007c0c446106041d0700c0003040c6a004240601a508a048 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 659282661 1250 659281411 659281417
    0xa1212060b090f18070e0d060c080a0f0b0a03150b03100905150408070b060114070f05070602030c100c0e0402070b04150e0d03020906092709070e06060d0e0102 70
    0x1103000c0040b07441d001440c0030000d035240070741c0c8500d0140d4011824503601d0040e06064a8101c1d180e802c0054400c5014008218804008a80070f000740d410140910405540003031100c0c4a441040800c02c900c0c2c181440d19402d80e45100c03400c0b5842500f100007840855036642d90000b208043e0840011a02c0750400480d040990113800c265601d5501d18048003404000c1c44204004400101c41d801e0306d15050f030340e281e03860003408006006131007010300194040c2d001c4d805061040704881852031301d509192402600000c02200211110301600400081c07041c00001a5141c5a044801a2112070308a598650040035074052206c200300d0000030700700207911a4401410180d02804d545840d900d014148080700f4050501140c40d0249000a0740754415030108802030640c0d003a15000d0380d5000c6d403000042603405081002039110190342000900502c810500c551000303040141e000541e550015580d41b80c072058070542c036803c0d00d50000581540f41c071000600c0c1d5406840b000190310091640102e089030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 659283911 1250 659282661 659282669
    0xb09070c030311040f1205150a061e0308030c0705120403080d0e2b0c061107021018060e06070c03050606130b0d06050711010c09180b01020a121206 65
    0xc0c40150300c000034950715005440c040c205002c1d44526051030450f04581001203440341c8241040c0310080f01c410800240145107402001128130701e001d08080000344c004200034442c516103408081301c041c0d004c0314410002001c607508100c00d40d08641d10a0030f0fa4070b559014280495150040f544c261600b034800002030400b03940a060b219403034000702c0320010100d0b100f104000001354000100c88806000c42034041c00e000359a80c01480d0301405801058036012110030f80141002d00b0300300d41d1b0107000300d4800a005054022901003915031140c21056038400c0303c40c41e00d5081a0b4298905005d0306004489408480700090696880c0c6480e54444019144594000301c4142d04200140708913890043c0202c0c1d404400300c01d04228109d5148000741460f0880c0e440181115260700006a05031f000e0340010400e01c1c4403030004c0c001c2c0305c3d25940040048049025000c00d4400c40400302c0e4a5444600c43c90a20000c186c0007000d07004071a407500d843d40ad910f88000c0c41000700100c03101607012040c4c0a114014 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 659285161 1250 659283911 659283917
    0x60d020108281409160302040e030c011e051617220605010806060102070503100e120d0b03011d0a03030504021c0c031e12050307020c06040308030a060807050f06030a0b0907 76
    0x11600340140f0b50607041000e440182190300c11003030228040c4612032817100312541101c0024840c0c940400050550060b81da076400c5030f510301290082da00c4485030640500c400f02800412050790f8400581400c1d4440b5a0f880380040e000c00d1030b20744012000d448030381c1c100c0c80d0601c800710016240d45500c890107205020484140e605c902c010048520108072058201c2c3e400d002604903103081c000425a600fa201440d03110700c0343c4aa101c001001028020310501000c0d464610340d88102c2c864600001c0d02250440700d020358645405001b0480c1d9480c2144142000c10380031300642e85098404501801c000390060368044200b04d0f12568101c18810007140c0148615543c0c1c100700d1860629901d180c1c100481d003224100f43c0d2a201c0c0014809a4a0002c062006c0c03d00039200d4558203801c0b032034503104000480c0c00c150b000501105024ac0e40c8091446020307038076400c0c844107031203604454442101c1c0c811503410424481c00c90782685404070140d075102103510f03400681b110469000401d80c18003543c1c40004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 659286411 1250 659285161 659285171
    0x12170412200a0530030a09080d03020a0c12031409100e010b0603240603190f090302030f070f300305060a0b0f07051e0c010206060d02010828 62
    0x7152206011680d0765078411111040c038989041d0102d496551124a5107844a4440d0103103610315a921100f00c1c0300a44100071652268000c42024018860300c0c002c3e800b01e0f00c140c1d0741805941c3c0c817074001c0f0b54580b82c60b80d8500b1003000203a034a0318050558001c0c14820f05481d01c0b626109170340b0f0040514851000c500c0108190300d807804242c0c04890200c0820200c503410115480001c9d29180e0480341c10881040c0ca03040445c2d042860020003002c08068140d000100005106620070300803281d03c0c10720461001084901035000c0d10408461810318000c0c00758109000030300d903005824001d003070054001c410380002d4001c181c3c2c441381e10f111540362003101c440c12003041611410080c80404004441410308101c2802c00c580001c0805134688030b48a0060000103641119189100658482580c007804071810072002990f0184907106182a850301c521414a1407890f81d031000600c1401a040a0240c461807580e6400460305030f04001e00b400402c000400c0303000c851000303110100007013401143c00051 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 659287661 1250 659286411 659286443
    0x2407270501031e1104090b0108010f050f180702030702100806010906030c02011d0a05061e060409210f0e03120301050405180d02010f0b0a0e06041e110301080d0201020412170412 78
    0x221100d4400701f0741001188401482144582860901500c904449150500f560080040d1401f02043d10103e035481e408020b104410f41c001018124183c422030782d00b104050425021504064112106400520740020412806001e039102c03801002451001003410a0000045035002565030071810f12a440303024000300707000341808010780092005590640c81480100d01c08503014000d00300c50311440d0343d1010071080004400390107207a2072030340c40f8010820705075450180030307404000300543c04500c40c846404810310f400b2801c50b890040c0000c2c0582107900380b0303040c03100030700d0b00400c00d03000f5446038101001820007c005c10000c01030194004101142510310341e0003a9810400200d00440ba00601406112243c108840d80980c00360303000201c00da983c850710071141000c0c07640d00d6511864098214148100600158142e44030001290f441c0100781000b00c0c00c0303110320304c1150340c00d513010064900083c4055028107050420340064a00b400d4403000e200c0b940207078505040f0341c03c5069201800d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 659288911 1250 659287661 659287679
    0xc0618030c1b051503091603050102030420030307061e0213081b1e0409081305010e0a1202010f0309062c1614032407270501031e1104 59
    0x4201480001e41040e02d03a02d003802003240303000c0894050940e0749000c40059125201040308513000800d04840d451840e42d40c0c2407090003980192400e80ba00c0700a4444203004040080750140d00c4003000e4019848c060040d12a60000c040f507030000d10719030741582c43d011607584083c000390000100200e002c01070709240004451170302008501405c0302d480c1e00301154000d0f07615000034081508d41e0841540a007038940002a0003059030040003041420b011400cfd040030320b0303074a0300003007a40c6c001c0c2c07902420801003904215601d84107214040c1800c8d40202ca10340154401e0960a000140c141800302d5100056520001560801c0410020a8026101c9440f0058031100d0ba51441c0640c400544001041c80c0000309621a9038042e8030800001041c51101680303040140c030010040a0250b03100901072102c11387c02454080d180c50000400041d054003092055900000f40e1504051a80d130f9198600b000660140c00c0150f040340c21060120510482c64505000b130400c3c4d051090040395940b428008a0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 659290161 1250 659288911 659288933
    0x120501020318160e0c0c071401090e01080304060c02060c061e06041b1d09042603070507030e0d020d0b090601090e060408070204020c1e0d050702060a0c0618030c 71
    0xb020158000e400e160003d11003101d01100341d4034100f070740802c0781e40e803a583ca0105120303034502180d2600c20340100040d071250b11508144a18426a42d07031162543d5000c40c031004803020301074500c1e150410802007240343c0c005d04240c404188080c00c45401d16030300603420f42c00c1030411203c034a0f204084040900245048026442c1d00c42d404550420401020511010782511f4000b6560103121070602402c1415021581007010000000c00d94010303440c08c0d00c1d12480c00c480c1003c000052a080c10a40d403100030600080d2480b076000e0303907255400e014a0752421a11010071003895034000d00c040d00703000c02503100d1200510f940c50003108078510700d0800740907141c0340140c164890003150345000071b050002d41000c207000340c005e5041584103855102c4c9000040080c8100d100c225618403607100c81c036460f55a4004405420348800d003ea80000d07411080c01e440c0c510540000075803000c001c00000110a000380c0320603508502078140007581c2074490008001e0070015040a401186010300c2850411401504d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 659291411 1250 659290161 659290201
    0x31e040c05150c061326180d05151009050c030403020606060a0219080c07060f1e17130606180501050a080a080a0e090103030302040303020c0f150c01061205010203 72
    0x4220f14040b4541c03805a00c402d406007181030440f07540385815061208403d02100c24404940340071010010212569020b54800110038040d4601c440500b081c0e4504030303002c1a03506400501a0200c06120381020b00f03202c0d401001c003805d05890301004140f04c0103070702c00d207840707807003900160340c1e8034109030034081e10b0715030300401541c402d0600700500b814071a8003003050700311088a0040c1038007102d01480d02c007175240114412195588030300d00c0001800303580116640e08860700c64070341e161010580c0c0c40c00c501402005c1e1864000c04c0740100181846100702c3c800b00d5111096184d282d107003040941d15403090b588140d00c0150a503000d0180311a00b184a44a154010a4101c94540c1403070700d00740c0020307154120410007420310400407031108102e0740030355489400303090000c0c0b003c0499038507481c0141c0250007600060700107126180010700541401c00798058040002020888400745150000e00c0710b40c403d034143c903415501e503100010a0040301d940350300c0742c900c180c0003da107a24180780342058006c0d40e140c03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 659292661 1250 659291411 659291449
    0x90103020a05011b0209090a031205010b31140111010513030507020a03050607200610140a051815011d0f150705100b012102031e040c05 60
    0x10001070741d4071a0058200c1c1d0003800e2030038440105a041c0381c414881070308080e4101c4105010000e10361380c00304030301003070310b21903281c030a484042c8040e0300e0108d590034051040f100d40c040281d0001100002a400781d40107030589904070141300c4070b015600500080d0300808003c1c034102070001c00d0390703000202c8240b02ca503c1c0000700082d10300402c1245980100f2075000c0e061210000c1e492043d5200d40e44500c028603007250886000c0d003003000e4014501443c28408001d420385460700003400708070104100d070103005212000e05105062901d507403d00c12141e0f000940c8602e4a040015840e250444005c04132400f00c29125501d01d400616800c400c4c0000d0505410021035031410140b200018480c85010700041d01d0540b0b81013030000200f050305c0107e18035210800b0001c6404820418001440940b501840f6002d1150720916001540c1c100e20440c90401c0060100e91b40310000b1200e40d016507409071607615110740c000300800180310000001ea60070f449401d02940c0134401410407407005084255050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 659293911 1250 659292661 659292679
    0xc0d0905011b0203030304150207170a1e082707081e1603062d0b0f041506030203190219020d020307020108062211090f0307030203031c090c090515 65
    0x2500085d02d911004000604103902c40c888400181038503070507900010740c44101c0e100804010164060b00b030300100200380000703e2041090342c564035420360f00c0801e83c401d5292051907031641902e040d00000050700d102440c10310061141e003820010050030004101100140140340403c0000c000e44502c10f01e02300d1040c0d445140020500280c00761000d04803500020300250000360a50118030300e444035102040e407014955844c0d420003c490340030300081d102c21039140c8601d500c20b0040c41700761f4510180035282d904103071604019450094008540c07005c859079083c85541c00a2052101320b070041d204410440344501032801420307804114001100c01103000135420501182d00007020030000812450140e1943e015402010403803040c9d0074580e5850341014044802c00c0003001000d031300031400c090702c1010031000c5407400d400e001c5110001d0300d03000307409540752415159440748000115010004225a10350905021400902400019207016180401da5041110824910550005400348100648 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 659295161 1250 659293911 659293913
    0x1104020a05041203021203161101110405040209132a09080d050c011b05031b030124140403120e041a0411130b03090d0f0518060c0d0905011b 62
    0x1c001a9022100003a422030840c006078641207060203500728007403210321030120074050000c04401d0300c81180780c0d00c1c2d520312542c030003888125400e85000c40c0302c01400d290100000d10040c10103400500d0101030241c403010f50650400070340821100b02e0f02c1d68004e00b803690420b1469006081a1013403214015180c070426441c24002c1075602c8454202518061100004031508035079820b4101015084c0401c00b9001686600d0801400c550300891b400204101550100e0310f121500c5070a80303050307507004420845000301d45104602102d442008000034032600d5a071030304804042000910196114481700f00402d403513500d019152451500c0701601c500c1c00c004500d402d5007112040440194022100403901c85c9c04200711324000c3c85000c4030144404802040031030074101405c000c42c00b407032100044610001800901700c55258403c43d0410000790104110408500e1840207690348007030052002e450b2044c0b8045117445c00d040d5210110210741d4510081005680100358003100c0c1d0001a2684420116 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 659296411 1250 659295161 659295167
    0xf031d0606040b01020724091d01050a0911120405150103081207080105060a031104050a120b06090601050f0d02040e0f0a0b010509031e01060503012d0204050907050c1213031104020a 80
    0x2490b01014500d82820340c07e20465441100703040c000b000c2e4003401d1014441d260000c803804510900509000d410803540002301120030340b0400390701d00c1c0150034107400d04100711000001200d01500588981c4908900c8540c942c1c28082580c1c02140700b4040702e0f60f1031080a8040060540042420741842131240041015841d03190440e4000303510361900080480005060b040e440c02642c0045400010304600031850a407014880051103000c2c140c00c01d0380c0e80da86c030104409200d0484d805030001c0d43c10300001c1d90080c1807402a00c02c3d90003c45026040c2500d0341305036211104c04840d0120350303c13280300a06c004201d103441000c80d012428a0302c07600d41841d034400710f580e0746094a07500d440715650710200c511403c020b5110310060132000b00203101a0409400c203132001c01c00c48501c03013000d44d0702203d100304103800744c422601100c81c0070304022115900d810064480d40c02181004a5900541c0a500443c10b00040282079092001c1d692044050440c00c104600780a8580403c0c001d0b48100900800190 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 659297661 1250 659296411 659296439
    0x12060a05060303310f0b090306100b0702060d020d02071a10030b0c130b04120c080a110d02011209080d11030402060403020405070c0b190c1803030f031d0606040b010207 74
    0x2074030805100c0003d4022a4180704003a294080310006144aa0218401b20042e004180e030f40d0040741103a0840d00c1d102001152074407540300c1e8030400d0808110204c01804d028010706034011252070014100102071080300181d82c0044c5044034100279282c1e40701003228007030424a401842c034402e0748040c80d04550392100c0c00d03403014203a824a414045a104441107074011400301410655240c691116a40d11110500d0065485c00b00e03000a41c240300422004000074135182d0081c0c20516440f0a00000401e010304081780000a90400134031000c1d000c0c0d0550b040c000c180341c0760311503000c003651019417860440450b00b20700030071030304810200188000f42e5070340820f50f810f59030111000540b07521062800d590034038201400615402c002030030000d00600d03c415040101074903040030b000348000002c2c1242e40115132045410f021007643d90a002003885404050043c80a504000540c5a1054030311106209401000700042e070049042240a0400380589168400203000409070141026074001c0880 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 659298911 1250 659297661 659297707
    0x38030a0809060927091501030b04080f07030e0103110708030c0a0e0d060c0818030714030c0109060506100e090106030203041104020d2315010e030102040512060a05060303 75
    0xc0106001c10203a0710b041c00c4402c40f8000400c01140d03004004000300540300415040500300b119080003442110000c9043c0701e05102d000903c611503803d5a40c0d4500c0c4200140054038194001c1c4110b00d00141210001c200380c6000707031103504d0322080d48800101030703078a1050800b6190b20240007250025240701c00703594002d2841d40c482904c2c0c5010000403200745c0d000028040d0b000c610344284105004181c1d10055142c074503a035900b8100d40c1d449a107042c03040c008005200241e4810441130000c5603080c00f4002034019001706480c03600c8184080d542c00d407941c1000c01d4070307c0fa59a005008091130b007141004111390190408403040003251001030a480340c144104424181c00200107030130410ba03030300702162819000303004640724803146085400420540a0044a131011001102c0221000340c265a200d0580440100542841c2d2001191120701240d5000e030159001d0101180f10340d02d4a096511000727130100180410700c2c040d1880b106507040a03200501a070800c028204040a49401c40f403009 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 659300161 1250 659298911 659298923
    0x9030a0507020f03010f05010e0a06050103110d02091f02011e0b0a0e1b13140d08161b03082d070609030c02120303090d030608060f0702030c0138030a 66
    0x40c01c003000209006d8040b039800b40700f07801d160800100f080c44e000c040c014003036000307100100400c9450390010342c120340000424042c1c3d00014041c000240d1001c0d0001d01b0304901c00b8004006481d42c03425201a1141d402c450b50340540d450b40c05203005e0b10441813078030246207071031761b000c3c425040d00c50f001c1103220205010ba030040442c5d0314005214403034581199a4000004100c190391041b5800415201141c94020002e24001c07040c03850110303150114030508000d070880c8a0615041020700d5020b060480b80034110703402c059100090510721074085054000758019112550303540c4107265081c4d5800d00d14000c0022244912456841d601910425204203d03440140010400704c1d60409441c1180844802075000a0444d40c4203020311010000c0e501524010302198101e01c00e00b501a0305558007401502040c0e4403010000d00a50030341340009811114600540c0d24014400406e242580d50f0110700031041042803628519510005204815600710403500c520441c01d1500003c2d1551140d401c06014 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 659301411 1250 659300161 659300179
    0x30b180714060a140a091d04170c0a0212030a02160b07111f02250e040213022101080606010314070c05030d0c030902180103030c0f03020c041d0609030a050702 70
    0x2900e0188014925a0156200c00307030702c880017008001c1401c0000c4c0642c00802c203000190404803a042c00c0c280c3c2c003c541c02190558240c00500c3c88a54940090016100e148210311940c00984c8038a40c901180e030740d2000103181c1d83c0000c40e2001e40b41c006550b80f0f000c1642c4000000b005080110400d031080344c1d901c58542c00b040c46219000a5000c005040c4007145040540c00701c4000f150001101003161400c071400b810b00c103009442d921200e070b98a2080ea80c80b00c2400c0001001171601094048010300502001400d003d09a460b40305858000062020903405900051001c24810000141e00ca0024a4284071007441d4003441a0703004400340c1001d050151182f08038040003000c1c000d407005080740c2d40081050881a40f4024060003406205030f0189600b003d81c8010004402c0c03201f03060381d805460b0f2112034034095448070001c1d0f8903200141c046000b140303d0310391140d40314022080c060b94079105000c008038000101c41c0c102a40500380034800d074010040182d0f40e41d004001d580e5801d8048503442c80c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 659302661 1250 659301411 659301427
    0x90c0a052b1205070308060604210c0e09030a0201061e09200c1b03240a110307030203160206091e031c0c02070b07020a05060706090606030b18071406 66
    0x21050080c400003040c2c82040c1c914903030a5039000c406003141d10302941d180c0e0700c0e40e1505020301c8420b201e103005212501c05040c0d4288400790489400d050070610400317010840741c2e41c4807003104030b4070700c00c0c3d4040d40150000140c0e044501c1e03090044a0142c4100c58007550078140c0400d0024406400348642c2c08201e403280c0151220748441021072007420305c2030b00317501e40e0365888074019500c5880d0040c0020510550304a00d20701e60400080c0f5400124006a00380c6050824064020304c18400625102c0c0c500e854030048441000840044c500404117500c006d43c4a06000250202401d03101030303401d0465108100300144d41d080082c0755040100d01c42c58403840100c1d00c040316821840740740b011804800da01030081c4001845030f44030081a000c242e00307a81543c1d440740d0300500b00d4072038080046c0d4040130306c1806103c18030b000c8006006c0c4620a07440003c01240d1540c42c0001e0f038026600a8941c1c525150400c4a44120304500049400b042c070050000d082c1056624681c0e880d0070410b07580240c40106402e1 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 659303911 1250 659302661 659302729
    0x209010504032910080f03030402030607111603050607030c0819020906090904110102120c06010605251101030f09021f1701140103060608010b03040204090503130e090c0a05 76
    0x1442a00b0603070184803d850f15102c0d000074403155104600b0700c4e118400b03810b1400312000c800d813400366a008020708019149c000b8126040e049014070188a401042140c3c0c2400207410080d0004502c1803016101600d4500000f03800c45107070140b0582404050010001e60f03200310341c03100054180741c00d0700684880ba90b034003060f660302500d0141508028400c05000034040410002c6400072000d038225030040f030210200c031440380640140b6184682c03068006201d0140110003070305101060507804040558074202484403807148000503070303101c600c06203024502c4d40d01d0b001d5039006038140390042c480c2d085241d01180b001002000015620a0340a03025500a48103952819258203443c003280183e50b19020301c0164400d0800030640841d2078014001140e0380194811070403900410341170fa080d60340315001d000c041c00285c0402c941c140010041c0d47e01f0004004800703030140200b5412122103245c01e11031180f0f031034543c0d40540c0c400c090b0200100816170f80c03000300854400341e0310000980d03a9801740d408 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 659305161 1250 659303911 659303963
    0x8090a060533030709090b150105160305090f0604080a02090c0408070303051b060609040b09071707170a08090111011808310605130b040914010603020901050403 71
    0x101c20025000340040c03030034440802c8040b405040440a6400781c0ea0344580320341c01c950740d0090040c110380c207120008040d605040e171540c8090206050407841c044124906612221500801718045280810003400b00d080c54170300808941401d40c3e4882c589410702c03402c982da4440c40c401c001d1180d004000020048803500d4181c400900010b000c80740c04503102c1c5070190580c1c001002c08680608480420301c200c481c0002c6540c01410094031024950b02e41e0b880c1c0e002000030003845604244510400040c00c4040856264000880d5001408506090080d101d030100c47c2c072030010003503130310840042c1c3c0400da07403004440480e142402d0108104040c142d1142c0136040300d0303160084c03c0440707001c0c90f42440041da00a000214040c4000361207461510502c4100101800e03c50b440140b61600c280505800b4000505400424403805c40780039070340d6003090f100c6030300c00e402540703e041c2c489588804072401c10a46a01410250600358144603c002c0024040e0040e8480509127501000d43c80c031041d908221a = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 659306411 1250 659305161 659305201
    0x6010906080c090d061103011806050a050409060e06040c0f0504151203092301030501090203071e031d07030302060106050a0203030a0b010c02030607180f06050f070318060206040b060108090a0605 86
    0x20506c10b07101040f4400c20150024455410180021680304080d2051740c0f2801c820303583d001f00500d020604040c2480002d12003031031300325255565045030400350703241000b042d40709034403d222002840c0d041a03e09865410300d6070006008504103042c6141d5804012108010351364100710f050520916400c04035009a41c03907000c00030f403a29400c0107050850f00f040440101000a803424001c507682c440d1440c0403407204407002e0001601a90001d088145080307505c0224103014540807840c84844000f038050107684440c1c001260303024044c01c10406405001c110700401840c200142030084141020703449102c010b0403940e00503566120402036a00840d50560507a1b006002c440305071801c1d030009131000441c6100b644038101c400382c0010b440242110707100e05541c070381e03a21942483c0c2c036007940015580220b00124180008220100aa44065aa0740009202e90790040c132aa040c103040402c41b058001e404030741000306480c208001140002100c00a10381e000c80001039968403122009a03965100030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 659307661 1250 659306411 659306423
    0x3101e0c140309010204090b1e04110918062b03080402130f1a09060a0509060409080f1b0106031a0a0b060f04090612030c0b1e041a06010906080c090d 66
    0x780481c0240545c0a00282d030079090003080010828400c0240c8403004000204103051505910990f42c10185c10450000700c110b0000c90501d0140000241c804004904401c0d6039043e40040008030700e464510170f0011a4000c01080008080311010f00c1400340e1068003400b400200070104085441e20144940d00b8017511b04108034071242e16040c8409030104881d0082680e8a120400d1580c0c034040582c9806500300401c07a13080c3e07510b03103814030030740200051059a216541d064058003040c01c500050800917401e4031a40e40d11310340b060032041c200075855142c3c0d0b00c070703071400c1c0d001c0c40080c0840e02c0c001b0f9480b488812126055a50560000180154885017500704a0125000d0403003000349014000303a4548043c244200340e120960300540c0706104030042c1c0040c0704604407001103031603139055a802881880301d00119244000e140202c3c2c01c0282c40490b8080408540c00c603550301008145608402c003481c0004d010303850038100402d100400341002900d40c1740041c00c001075548940c1c424402a034003072 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 659308911 1250 659307661 659307667
    0x20d14010c03050f07091401030906020f070302030304150911060d0b0414090f060c09010513120803150409050606060c0c0901080703051603170d060b0c0c03101e0c14 73
    0x400c00401616050707464030b003410410004174024502410140e0141d03501034540c0e161400001d8011030240a5201c4c054a20760760070002501005030860082c00300901940007950349040c5482e10f56010200c03068944181ca142c1081400050380304030303000204110444000ba10307400a1040d0394002e0040d8030000d0f900524003403010303041600300c075082489104001d055035a11503082d074079140c60b40f008544103031041e001044444100d40c0124054003100c403100c01d03941051902c600c2110f143d6000702400303607000c080100c00c102c103501840d00482c00d055001e940c203006505c11aa500340d9126005001d81d449044003007010b042003903082005044c0a0300081c00501c00d941c6d13418903a620740b4841c0c042510240a8148440d454000940000c01100da00854038543e83c80c4900c1c0b11502034004071030707800c50706848440001e580c0c0201005441c80e04100c01c00380c492000d50340d0405140500e4000400000e13410440700482c00c050601c594101000c10940c04110313444006c004603100590010340b500521008 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 659310161 1250 659308911 659308931
    0x11060706060e0606091c03031104120c0f05030303060d240504050705180c03090106051302091002010605060f0c0f1c020c0105030f0403030e120f0d0f05040f020d1401 73
    0x103030840e00450b00c0011065055850301c105000c400c0c402e88084607004071381c5a42285003194030843ea42d034000c0c000d1130001083d40b4407416900480e0f01c164421540384000c0c54810f824400e40710321010040181120602000d4a05030100382c0b00d00004054610900d40d00410906119601e061170002000d0900d89100d005007035440c44d8000c1038183c50950f0144280e180104060030f1030f494184125207031961074000b0380ea074020b10460070351005207881000d5403180c400050703d0b21802115030501843d1035015845280200500104c0042e04140c40c0031a81403000c10007103904c414003100c44202000e2007460343c411000500614250810400c10320078401c0300b40302e40e6507112806525560204a03400d88030aa400e107401100d130b42c00292210741c1201c2c1d207030b008200043e000c0d61208922074410800e03030728094a40d2526500d660089081000d080c000001d0f501114030082c4503d504050038a00300b003105040a031225543c0c0721210900034020070a142882d801d20609070042e107010030344c0400a010030103034 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 659311411 1250 659310161 659310173
    0xa11120a0e090105090f0a0b0d0809190b0409020705030408070e06030f010608060f0601031b0f030f020c1c0c0b010b09010311071505150d050607091a090d110607 71
    0x519200d0300048000c1e5004003103150604503a4102c034002002003200e51181e800e000291000a0241490982c3d91540c115140d00c2e218012500b841c02030204a88800140d8288040f485509402030008100c00f202030004503010016501503407001e0100607140c1841d0714081d461481150040c0c0881c1c8101c01c40029000c3c01c088200b8410031041d8143c40c0c1c00d1100c00300890031f807034040c001e486054100c400080e219410030348109612101c14900407d09079400241380c03504064a0601c90001401010b810f00d0031901401214a8804d107198214502038941452648440e0151041c5100500210319052043e1040c1e4800e0f030001e8100f2040d40350b650391004186143e500c8000384601003030070b20941d008584409401e0342c10458012003c40c0c003000510381e20320002d0500074481d045084140b1a000320580307540400b14200c0d40703c3d0004118a04180d81c0c05801c2c000542d010310b1441d1440400407103c162070350140e40e80d0702e2080d070709201d004000d0318000800c0100d5050107604401c001c18841c080c400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 659312661 1250 659311411 659311417
    0xc0c0e040221070e0c3106140d09021809010b0109080a030e04020d021b010b0a0e13020906040e0f01020301030b0903030108030f090d062901140a0507020609040221010b040e0601050a1112 82
    0x280084e50b042247c3e038003400d9407a001c0302d040200c1110ba041c48090074121103600810308580c8004c1509552032180349242151840654621510ba903407191480610758210340600054035040c0000e2005400f1a6801040501ea0110260003a5000b042031051000b90340c05a42803800c0380d00c0f101e00303a0140c0c5004170b17008000413529144100d02c46140028810081148180500c064110b40c468450241c0c0030702c880890042d10302c43e0419550240004410b80c20b11401c091020030a002503525451800d01008444014168015982041004200245000044070402c130089191180c0b1120002c002585070b1400032805000b80341001540542e520700700c26414082448100d480386007101e02c0300112501c42401951000c15079080082d4004140110058094240700800051609481e030010a0998114804405603095100000d5040c400440c010038003505011984504013807401c001c08685100240210741800700004010840501c28a06d01c580c0c110490222042d03007038250b0016503994 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 659313911 1250 659312661 659312737
    0x608060702060f0c070303021303050102160c1409070c05071d1e0c09130f02160b07020619051504060b1306020c031005070c0c0e040221070e0c 63
    0x2006410000d0002d115515030780c0e010390404c01d440350800840760380641c02944003103901c0020a040010000008009000030401c0b84101048240603518518103061701600e1504810050f054844504000b500c071122190390104091500141802082c1426400c1007001d4000309000074546450b10305110454001d10300820810403282d41c1c484400c0c03900b010184c1c0035103291400e48000c010b40d90141c500750440c010b00f107400d90f10004034148480c1c6218200da008080040221130324421503414804c02a410a03403008180c0058006443c0028007408503000006000c100030784e0f04d06c0401c40d045501c14103079000c102d01900c00c1041c0b68450f41c1303020286d000980a084144c01d24180400c0107031002c1031610320b80d50040d0040c10580685c4881c1800307000d00410100070858070701001000b01d00045020070003011842802201410710380140400140b0b0300c0310304c200c40041d034451740013000d0001540c4001c881210a00407115250800302c88034070b1007103848119410305444456000d00030703c408008010 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 659315161 1250 659313911 659313913
    0x1206240304020f1804141005090c2404030206030406020c030c2104030201020703151b0f120902032d030739091505040c0302070c081606030f0f0608060702 68
    0x60310182040340f002d544030404d560241c070764030110300000d456a41c07400c000380c40c0100fa10352502604034414200c80c01258003c11551041440c0409030030a005004901b9068600c414a81c1640d03e07071840080c412844024019080000007a042c0030301541510100000310040e00d07503400300707004407035070350b410903034900900a500c0500d10449a001c1c2d011079048030b50680180401c185591a091240c55010b8000c50100e03031150071072031411071240d94090742041591614241c0c070030301e044024030011144d10000d82541c031b48000350015950001d907410050a404080041b41120901259607204581c40001800d2001194010800000c00120f29242d400320b91075100015405419100032502c014180d076044070490001d104160701504015507010681c0241c0e0a0070742d4403c042001c4a242c2e985a500095010559100300001d00c800d441c01041c00c40c1c003d2405060b914034900c400f4041d40300340401d06940f80c180030082d9980784c2044031210310690b010881143da82d00c0c03260700d40004903100001 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 659316411 1250 659315161 659315179
    0x1509020f010e030c01030504050a0c0f08010f060308070809012309030c0303091f020f06070e011107030b07230c060f1f03080c03070606060306090e010e03120624030402 74
    0x8294401c1e1070a0318400c40c000e000384501c04c00200150014100a001524640076101540021841c2a203507031008160500240d00d0043c9031184071070840e002200d510000c02d040c9101080812504c9099481050f041a4039640e9582038a00523202e009800007a420051341014216090809605c050802d18030260141c030a0407800c6810103480b842151100390740002000c40020744498201c15003003048242d40111001108607416071480c1000480d82c00000401481a081031542d010503d410303501200c00080c662681180e480220302a030082001c0e042002a0002c0c180782000440d12407008031280c0c4180d079407201788000440d00c80701c0844071041d0300001c00d408525180d0f00084007900c0300c110034460020319402c5a0b226201c0da4040c00e2030040790304c000d000380320105500f88034900003402140c0700014031501c0d240340d00307050742d21310780a020340d0303034034180301c482645102100b200d04119103144503040319505c28000079010800319a185021503c00c0310000c00c2030a451b0700540c0211700031175003020 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 659317661 1250 659316411 659316439
    0xc0d0b0a0e0112030536090712050c1b0c19081002090d05010f06080d090b12041406090105010906050d05150709121b06090f060507030c150902 63
    0x345030324840e4800d05a03070039004110051041c114000d926200b071600794904038401d01c008140e24120560780003240c4032420454011000d02c000200d0300380e0151940038052402e01c03c040c021402041201002c15150700008003226090021600d004082000c03141d030f0590165415aa00d048000030103004003c2442032200813007500b8030860854800800508980d01d51107000030103900500c1806802188503221240019001c0c0501a49001071543c002400c0f441d03c0b0003280b411401011600c00d2005418003030101d8007402044803440c589070140080305131600d00d8089078501c482c0400f4100360003000144048600d041d0001c038104c4050290070300c91152100f082003000503003060300a011740d1110080d01594829005000e40c0626281010880990b540115504800390f10070200c510f10200d680ca0184200d1100d04074001d071006150010030142080c4140d00d442016022f0b8000f80600441c03d841014401c1d0303026403400e68007001e490320f241c0728081800042e103290f0f5022845001280c035400 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 659318911 1250 659317661 659317669
    0x6040611090a12050a060908090a0929060f07081201060e0105070f0c0b18090c0a020c060d020c03040e01090e01050408030601121116050f0d080c031504050c0d0b 71
    0x6106a00014900800c2c00e150262100110b030b1406400c4549008404018022031050b109410070140200c40e02c2d80c1d80c255900c03c01c0b031100d4264001400d4146001d940d0358400808848802010700450b54001a00d0031080000d4013600400000c1405104005014000c00c5205030203002122189860030180740d80ba0390065441b55403280900380064001e02c02c500201341c04184610403603004180f81e030000c070340304d00d501c01a030752200784452210303299070010b800d003410701c0400b60344d1001884002c03506048141c04000e440d06081c0416070700c540c4000c0340140b01c41e86030b98110351030300520b2001c8a596540c0c81c0045800c4031024840d0380001450003021107481c1c0c1d010300030b0510483c1e1000703140303165903550340040d41c29460180c1c410b038540c0d40d100700200064800320014075820b0251118030741c44580074076000c0e103044c09020003044142c001d0f50f00e4154030740e00024480c0c0c00110003000c003074407035460800e21071202181c0c0e423007268800d0500090118603400307000241200d00090310300b809080c220000340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 659320161 1250 659318911 659318917
    0xb150408120a0c050703050705100309020f010e010203160303060518070e090703020f070830010302010f030e0618010e12040510140f031905010b070f14070806040611 73
    0x114140c0c000000d1110030071034000c02803039550a42d042c41421000c080d1245071401c1c50a40040b1040d920900051200c1d00d480700030b01034503406910781030040104550105258070550101d2605000c808019001b09a00a0040d1074402d5081c4902000e0103615040040c05400303203208450240c41e0450380141d501d500010302c24441e1030796448030f80d003d0100c1e20074041b4920b4001c0c0380c03608159017808115044500780000b00b082c1d6000b08002d82d00c4201707401645c0d400c0000c002c400d80801c1d00600031141c8034940022034904685d02401c0c011000b509100c400e50140c681240c44c18400d00681042010250030b0b05076007600c4101da00300070040316000090f01036460f0110650381d1104c0c2c3c81030108000303900d00104c0d003c000e202c181c6410101d054207500d604500b40c0201e00d00e200d41c16004410000040d400d40514070360400502010720041d490a254612180304a05001d40008415078400d000d0104a0703414141100200e01107444142d6a0041d0341d0f00c030300081e84c0031900d880c2402c2803401c0401040040e = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 659321411 1250 659320161 659320169
    0x1e03080105040b1e0f061b0705060c21040e0c0a11030a021506180c0a170403052d03070f0806030106050315070905031219140f0f070f060b1504 63
    0x442540b440d0f101a11042e512a01004c540c44155200700314010b03140c9002a00490001d55204444812194803903410724505801c55409282c3c04d1003180740c025400560410b10f00d42501d6102040c1e4010000d0b00340c24412500040c400b61400f00a02403d5143c401c01001110410f48d1403200440031800d96907282e101351101c0e0780040e4040c03802c26000d418048142c50b001500101940280c625102e050b01c04c0070412143c1c562910f40100d500c24000b034100c035042c1290010740e03d100703401e880c095502826500484901400403060b4115243d00c0500c0c103600707070406100107402940c4034501443c00a04154462030510005031260700420311500701401000b0566000401600203050410959426848018281c80411146c1400001d068800340090040c00180201c2599545003101000711200b50340d1111300100519405102801550b00c800d982043c05003845a0360358440d42000381c0882c0c043e80901400c034251804e110020400c8503440024414825690b048940040d07403e0b0765124052486 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 659322661 1250 659321411 659321419
    0x1091a091504170a0c0f032006010e070509030c0a0e07090807031722120b0106020c10030c210905150408070f032f0f0102040302010e120a1e03080105040b 68
    0x42040c0103222500c0244c0200b010b82d14108484407502c1d00c410251010f00002600460f10705413007605801a00d45a0a0f80035458000a0055501d0715400d041c180200074201010000f02003039a200035942842038400845004023442901da4461940444081c4180c0303014000c14251040002c06040c08911303201102d400242d04905c00c0244003452000c0d0f0300c0030384000d28454104091085075440e001c480e2000e0b00c184070034041144210b21b8115a04030f410b030041c0c4103551100d900da290a40d10000040529030035850007180564014a0a450703084071031400050007003c08070f0b0720310000c1040d40001081030080d4121045111010510781d40c40f0400d0b2005420102c08020000118103d0ba10b0590310f14800c0c60701d1041c00c854442d9443d00301c1442180c0002528490b003c1d0520158108114404807980b14001c6140516650010b4120540c00d401c80e801603900c600401c4512070184001010b076a00701c05445007401c0c00604a0285904006d000c0780422a078100201d0141018400c0c8048518060 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 659323911 1250 659322661 659322683
    0xa14060a0b0f030c160f05150121030908030a02100b011e0c021f030c17060609011d030f070905010b0913023f0c0304020d1401091a091504 61
    0x100b8080e5030f030320040c20360513210f20801c11036449034001c4500d8440d00c0d0140002c0c0182200707074500181410314444109a003031260b400140003034403a904c0c402c150350503402413080c0311809034601a111079000b5802980c16000100e1540036a6402040d01c14041c07055000400c10200d0303e000664410303050300240c11a442e0408240c0e000107001f4076409907070307900080c1291045014650981020085590b0304400241c40710040f0710916003207091105a5100b0702d00003100d61904002151190260181c2e0a04002c3c940d802d004400c1c10003070f42580191006070566070301d60302030107c45070390b040c91388950308001e80340400025101ca4808152082e40c100149500034100c000281c0e08082c1d0800e1034410030110400342341c842d0141f0009007641c103034014001200c2d1007100804200380000e45c010104c0e04551000c0003084010fa880c03000040350664004001044803500c07503612401455191402070a0300d00c0c0c01d4020501031400304046101e030403c0b2044403810420181e041580e241d0a81e0010640c025070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 659325161 1250 659323911 659323927
    0x708070809010902060f1c06050102101d0714010f02010b010e010507050312010f0f0e06030a0b0405070b130e07030b010c02010e040f0f02030f0c0a0e0d030e06030a14060a0b 76
    0x1600200380c10042070000851110020307000207030702d984804c0810b41c56503000100d45003031400e46032600803101000901000b841d4500300011f0740701e0421243c0002d4142d030b44c541c0000110003c6a03e00c0d403440c1031070112014651103514104901702421081e0f170110b07072141c1e03c0113991341c41409170300c150102c1a911184180d95440040d40e86d80c12100040301e441c0410300082c83c12841d191030341d6000304000c1c5200f403a030358a1b0040b5101007144980020004034440d004006040d1000504113050070f5100c051040107980d41e04205040c0300c40ca40003440c01c0d000014000e8812200900513505441c0c181307503c401c803520bc0301c80507821610000364080c040b138600040b4074050760007100310503407240d8080c001203180a540d805c40030846400724489011a0b0380030080c01030b100f59440030030f64000303101c89596291001141d00030b84200003402041d8810032203210075404051054141b40e2805070058602600c81c20908000740192010040b00719980380300c040000c1c200d240c5010120202c0700c9402c2180d141c0684 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 659326411 1250 659325161 659325167
    0x30606030b0609163603231e031303050604021e131e02040902040e0106050a120b06070f0f050d090f0915050a120501050a061401030506010309080c0d02070b03070807 73
    0x100d8000262031581c0b858445c45a0503a40e59140004100c2060188000d0308602d0001880001980780321003e1820700404904450000340808228040009040614610305c00740d80c41c6126020550440481038034000080003400143c550180c8d208603216000d000c031001650301d5000324641038030307405461004103205203e55030303200d41015101541c8590800491f888160180c0e8020b17401280b0085c0d00150810808524003030301409000729103059031420341c01a038020001120300f88141c089171f685070350b00611642c03010200c030112a84281704500861131418010780c403191514003950a800b030703801c0703c0a9442c403400000090740c800d00c45240c907443c24080c006c0020841a000c880c0112485170000c141d90766030000c4d0350020440c92400c001a40409c0c0b500509460b4060a441e1015040000501c2181c1550f050f0440d42d1a003031070300003019525580120090400b803140507141d140d0002c4c00030740c140c01c08070300503010f150603408849400b0780d030740717035002c40e520044079240002040c11000c03442441c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 659327661 1250 659326411 659326427
    0x603030a0813030903060c0c0c140901060f0c0b070509030c04140c0a141b071e060c0203150414010b010c05071a0f040b0301061b0302061b0c07030606030b060916 71
    0x3001346081d040b125100e560300c0044407405900e0001003642640340c9020085614483d40140510007034082d5107190759000710f1000d41040c042c510500407001c030200001d82c800e280750750000d9002004000642031070782021305940d00241c40b0314003e0040e040d409065051a0217010050700390100140343e0303942d0307141c0002c2d4248c002c0b0f02c145040184003a54490404a41d82c007605000c0c040410100c03543c19280d0300c040c0703814020385c04600101d5050b0a00194000c1c507201c001e003110114103003000400554800681030440c0d1960316124484200b050209006141101440c0b0512440c0200101d40405c001544c400072102d90080c05640302480c2071049400c20b1007070007040b10241d800343c2d080000641c414500c03500150444c4400800100040010680c002c0b200041c0e88030002540c8044842910002c3d200c480042441035107103040e21501c00c0c1d0007c4c05084585103121141914140d94583c41e2000240210b0301c41615415240004a552440d0140d0b60394080e140500e610b004402c000c1a060304d02034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 659328911 1250 659327661 659327663
    0x70209190209030616110613081b0615031002091513080303130203010c0c0515091c0804120305010828290117120c0703020a06020a03080603030a0813 66
    0xc0e80034410040d0039242005058003071143c1c030201a071000c0141e44000d113034540e0350104050b0350b8030050503c50140c0b41e6040e6440c1d4503401a594580c1c880c80c510b44a8210030011452a00c64800c3c101009012139204040300c603400007c400381c5400701c0c023404140703050303010b6280c0042d4007003610f134010102044120010400c2c5145280000351403036617142c02c2400c681088841510380d00c0c1564000cbc046203002e01c1007003481c0c0c0d4281440d080d1003c1e5070b00c41170340ea6800d0140da1602c00118102061740b0744400c01c04540b201a01020305400000348a030002c11071002030341c003211440000100818001d00030b002c2d89059a036440010114001c200903010800788002c11007090200b554040707840410906a00f004405c00d04020701500f0890f80d03030180c0e0107102d05a0009455221004210000e150045100da07180d034178900c2c4c9a41c60b00e850700c5045080c80c469a00c001c0d8096901100003500c0c0e900031503880031181c001c0d2640d007c15a50321043c0f6803280b1a92501d000000c0391080010881d4070794100c00801d007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 659330161 1250 659328911 659328961
    0x5090d030804061113063203220b07120608100f110a050a050a180b04061214150f040f0c0801210201030f0212010308090f180f041406070c17070209 65
    0x385800020080364615283c0c2280303141d10380001080100f09058048a0744c4000c2050980000080ac2c0c480e542d104401400800c20080901382c244040721041d080403000c1c0001d14140d0364006501450f91004040303411007a00124200900710132000030b2041a20301d140780ca03481d11031030f20407528004c40705603200082d030070144075101c021081494800d4840c60060600d03024541d47d658100107010340111014900e1600c0b2500305085290410608070906400501030b880b0134140c0c030310b0000090b003072040928402d80c0061811034042c030710b810950801c070b824036255186c07041c04c1c0c2d807035204016100c108a03980c000030764500d031510300c0103503c20792007056801d103050b60042c1080318150365008404820f03802652010000720709580545000321000c010030804907600c5000000141d16480315079401403d40701d02401c20300000d401d10480c0f814400c0741900040645e21145000d5001078100381c00904140c030001040c1c5000d00960408c4021218044d80003080c07110a0b9a649210503d02004140020b0030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 659331411 1250 659330161 659330207
    0x330e0103120225030c05040c0e0906010c060e0606150408070e0a1d0f12090a0902030a020c0a1a160e1203040801090b0618010317030705090d03080406111306 69
    0x16503452007406079000f810760101c0d200940c0ca14105009501c009400c201d00c52440e01d200810011341228401d00180d8042e1400c0b6110f907658070043c2c64411980307002925490074041014481000402c9113881400e00310f61501200c0d154400207100cd01641c050300d80c540e0310040c002d0009507544407600d0f40c085105100403800c80500c140c1c05082c02c0c09902c1e504601d07441441c95401c00030b0709120007103000104181c2942400c0040d0b00090034604240b00311411175a0020210311940c100c0d4040391400703a1400122522081149031940e80104c0e8505d0213080d21899601042d0429060000d51250150a650768000b40c800030007004881b86010388000a548002c101c00220a5028014110114010305400280d0f15000302401103e069001900b5140b4502200510004000b5907001300d4486696802c82e85940d903444040c1c580d441044001c1d640031401200c14400c25278030200e4180301b00c0c441c180a1001403082c02c890780d4039000e45415400c480003415014042c00d4800e07a030684803441500040c0306 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 659332661 1250 659331411 659331433
    0x150e0a0b21070f03080d0c1103040513090602031017010b010f0e0f040e1b0301020c0304152f0c09040201200a120206010812030106020303060103050613330e01031202 73
    0xd440d1840c1d13031040756030041c01325040801814a01c14008282c0f1103040c5007400481c103030310981d10f0344981d024040c4643e02c0868030100442841d406002d5046d4800c004550340d0404208511100f03590b4882c810804545808040d0084010b010b961690721068581c803a481300303000c0381504c02403007041665070010300d00c040f500f20907929130103602c045d5a0400080c102a0141c001d407a18103000d22801c10f8001d038010008200314404c0001110100d880d811101e1001c25050390b8100c81110001c2049143c640c05c42e078410341403500000940510060140c00c075103000352070600b4400c0d107110441d8068003040c4041603104c0e941c203592004d92400b0300751034292103941c00c0b107940e0420341c60210191000164800700050044420811401483d0070300c4601c0107003190b2403c3d000943d0b0b0b1100030a514101901d803c0401c640340c07038201c52016241d070050000d01150440801116036468103500c9084250384412420350340c02c03030305134401080e92452420340c1100da09540381c104510032036540241c1180318001c000c2c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 659333911 1250 659332661 659332679
    0x30e06070305070f050405030706110a080d14061e0f06090301061e0b13050d08041203020c010e0a0e0c0705070e0108070303021006082e150e0a0b2107 66
    0xc0c400d4405880000c0c1606207601c0003000c5807000d1504000f800010402031000b5030303001491348200d0b1041c0c40d20603980102803c046080003610714004046040108000000c06201c0c1c000c1d8400300180c1c010001c0b6a601c04080100712a0240d0300c00d60182800c1010f0022410015114a54004060440c03841d1104041c086802c59000d41e0000c854429001400314042c003100d00c06c00c00a00b0401003490402003e02d06d02650320426105580c42500102d9051007041002002d0f68014803c1403001503656500b410702944540104040d603002617610700408265103000e480c0001a12025079001413290703100ba044201c15440100182c9440c456030500149070310b20910b550380685100c20107030101915601d0064030782281c1104615556050000c00c1c821003800042441a503d04054144840800050030490691082c4d007690300e40ca003483d080013405113144540500307e5110346070030015655941034120864801c0941e01d640645480d03401b00e01c3e100e000d00c00c002ca00c084001560f5440c2c0e5180c442d5 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 659335161 1250 659333911 659333923
    0x5180f19030c05090402100c0512030702030a0201050601031505090402040f110a1d09040b041a0a090302070801051e100e13110306060f1e09011d010b0901090b0a030e 73
    0x10440036841000184100310810110b64000c2c5030903030b4000c0450606500182400c0c1c00400100c1c104003040e0410406d100c010030400c5c6010280286240d40c86c00e190100a440354011103652000d5030910740480e059510a1144044078180781c010f81d225030303080c10208035101c0000b034002c2c4d03030090710f61140030038060b030038455054841e0042024a81c2c038a000000079054001c40240410012200290106c0c0341d260300d0801c0780d20541c048041c00042e901ca01d8840d20032030703404a0031044854404104201034041c2c0d80004002e034000c1d0200c0710125a920103880c2031b82d03012280c26861840814184025030b06415116801c1a1001004908035440d072481070442d500031120300030a402c006030700c2420b110b41c1c0303004407241c2142030b40a0255490a5000301d40e444d8409a843c6016506503e2881c402c0e60070308904510b042001000003c82c1d5a44051220101000405010b4060f00501c0001529030988003100e07001e00301a101c40e60101d01d09000002ca540100845400b89900c400c1c4641d00703080c0c00e02403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 659336411 1250 659335161 659335189
    0x9150f1806050310060804050606060304032f0705060711060c070801020f0d0e0d0905121608061803041809020f101e02070e06130e0d0207091b05180f 66
    0xc2d0315242e1030148600500446942c1c800c0c0e060040002c00e000c0070803c04100315130310a2080d40c0c5a86e4a0b16a840c00300ea00d0200880440c0725141030b105030001c054010000c3e00c40d00000740c401c60301c00588035420010036100326080145800300c6a82c1c144c038036091110281006400302c03801e880c0b140307613541101800c0e40e00000401a406d40700281c1c0040500c10752003100c1458030b021005000c2c00c0d941e884083c100f031015010745072245038240c00d1040c21010410460024110030094480360b2a03845c40700e641d903004251000c4962809504034441d00300c02c004255030881c1c4000740340c026210750719004040200b001c40070503030300084901117030030054480310350003030014070660340350611001070003800b05d014a450344140d011500000307010072410020381503042d0000b004031000d1041c0424408014000c10511300c00703080c80c0c0070300c8a01c010000c0d008641e0714119000d0040c00e00224004910502c0c6c0c02c008070302c500e0041003060100071309a00120004204040000d0b00010418484100180555101480c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 659337661 1250 659336411 659336417
    0x10e10051f080a06060509040b0609040e061510140903150106020309032a130906061e060801030c030b0403021e0321040b042018040203010c09150f1806 67
    0x20001e0405940280070507444003110004106071801e010b0010141e21580c0e82891240d03455007170320100c0b9a603280c1200e240207c014402c0095500c4821059143d032070890340c0b5a0141c0540c0d0500c2c0203418407000d402825412541c1c0c8a042000c070300d880300d4564000103181600b600c00c800ca94103040c2d03980c0007a1030103004160021900e800c010401c0502d030000540840003110000741d03c41402c41e041001030340f1002c0302281c482c0c80d00c0d040031150740d000f00321500c0080e00c402c6c1440d0300043e00e00350311402c4414504428030040e8255440701c10036030f002502840014050f06102d0000c201195010204e183c000384644141c0300020324400030054520070b40c243c4682d0f51f802c00620500c0040918404410004c15008103030a82c1c607258030342d01d40780100100b0150100c8000ca0200030941079001120208603801491400b241d10a40180504060b01710b5089010f03610b4080c2100e1300c2400340c0804012150424612450004d040c40100d4104c0281c0204c0f1050100d002c120864000740c45081e0009004a40c4d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 659338911 1250 659337661 659337709
    0x102031806310303090c0308090a08030403020a050f040207020306160f02010525021515040605030c0f062104150c0f1b110607050a021017010e1005 65
    0x180300c0c68108200035011444041030500e0360103080a079080c1050103502c94820712051012603050a4020b0058284014402588004040200214980a0807555400f0385045030455122100d850362481507000103503001030401c600700800d01e001c074865041808090405400d104140e40403034507141c5e043c0c407030310b00394154a0008070203541d02810440c5040150f2009108900706446040d6102d4642c0d0b6081c04035090782d01c10b4a01d203600800114804000072180441585441549611070040c1010914411418041c00003098a400500d00640c040000c040c082403d215508110951b40107001c41d01c5034440c50b8220103121000b000c0440e100710f01403000c140564141071400c02c21940b050390448280b20411100d603011680c445001925038034044d101014079200b50070810079418120b900030f85e01c901c0000710a0204280810074134092442564006041e10307070003100781d841c2c0380c04512120000302e0300c500410040b46800480c1c0e400c558011041048280c0300d6003c1540700d41201e200400c0740b2100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 659340161 1250 659338911 659338951
    0x610140d170d0507320d0e07060e030712150e120c0609060708070915050f041706072313080d230901080109021b0f010b1908070e0403050c010203 64
    0x12040b0038545c810080e8500e03112500d40010207820004e0101904400d89000c1070210100d019507110401a801c1c100440e046c260303070307603400070300318040d501303a0500900603000006020101b86030304440c41075101384213030303084c00a100b1140c0051880d0150722401e40300703449032160801c41c800020204a19540084c11452600907a458946100646001c4c100002c007810080410303482401e181c103071030921040c592112000c410864860042d1144840300c0390001800083e214090b560410540140e18195022961000c00546200d080321038002d89154203a4569958080800020303c20000c040882d40c140c2512441500d10740200c000610011a89019400f10300601c20624014600c1003511002d10300f0302e640c80000c1920074103108055425801046240c9a04840303044c1c441c03025803100482c0d2102001c410b07028082d2100080e2603014000002040c920140665400010b48a10400604695260429044801c07030028003e504110341480f140c0d07400d15003800150b01810407030500b1140b8101e6 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 659341411 1250 659340161 659340167
    0xc050715120b100806010f09080105070504180b0310020c01020d02130e1005100e18040c06090b03010302060702090408040314010b0111010213140117010b0a020610140d170d0507 78
    0x700711030500c5245414074540c441d951050a2903803005c001e18100054118680b802d07680110580c0041c0940e50810080000d280d0b405070292040b00c901c00c00c240e07020445441148200e4200d800fa0319051f412241000140c03c055030010b024403002c0c0d1000501e444000c42106080344c1010b0a040c4030b41440500810151600c11480d0b500003802a046400075450300f00001c00c0b2404035005c440c10310040e103807401c0140c0d80c0c126405070030303444070f184800391840e05140030701c9988950300607403010401d8802d000ca244800c2e90152030603250b01034141807404045808100c00a5030040080398200d0f070410020000031054000b1032195048031002154040e020b50003d403004000e0101e0b05100c0c0e00c140174100e2208200034920341150f1003010340400d00c42070720004940c601210109449080e034907400004156990380028441200941d09032541529942c1800032880e040384102c4000340d1014007514100c1c6026902d80007218868106011b91143d039550504507600301604091040d43d82d08100481c02e0b030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 659342661 1250 659341411 659341421
    0x30c1c0c09080304150c0606210c061b0f0c050a031203051323010605030f150c032505091302070c0b04151110023106050301060c05071512 61
    0x301d45800f450a080c100a4101300c61001200c0380302c200303e510300c078002c10300007180d1200014000080901c49005042101448070700d6800004540311b4402c000c0005c3e45910455a038140c412201c984018400300300e45480044d818600010303201c0001c200c0d000582641c504034060011445000d03029810504902c0280c21540d009064240e2121086203080c000b44080d03608801c0c0c15102982e80d5180c00e90300d1046801800c02e6049103030584504e065031083d20100103030409155025000401c11035480300a030411900040d1615900d84c0ca107400d0142030a9881d10722428003500e01c0c41c2050030244d040d800142d0b14805001c4488003d03038002455020f10000144a00242c001248040d10b0b0914244403c2007031507050030b841040000d0504034250100042c40079101c8001003c50664407441a0405d1203100220790307070f45141411a05480402c0d00c40e0110901044581d00e4541c541544c0ca490001c1e240a14400000c5a25000d943c5000c40c051000740019480d17091560f450207214082c3c0240181118 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 659343911 1250 659342661 659342669
    0xb040804211505070903240203010f0801050c0405061209011e0203010608090604020f15071a190e0c09040317040305090109060c0b0408071b03080304020411030912030c1c0c09 77
    0x107820030301084110780e0801544c0d411031f684020310000c954284202074400d201041d0606040340d0000000140d0311117003440e90340640c4c000701d000308110f48440082d00528170461042030f030059014851034080c0e86000c070540380c2c080080360012604c2c040624540a14140e06ca03032a10206a000c2f0052100580c00b21500358048a0400100014102500001c18144e642124588582c8080c1800b125040a0350705070382242d9800f0a218041004159012420410850b40c1d010300c52822415440300001074059a501d4420010240a040031140207001a90000500940501006001a20800000c1020f440c0b20b07078001c0d0380303842d1150b0004000402ca4855030f480a420090051003e43c0420744c110260380d00164822810b079a10821031401300c2d0b8041a62660311424030724003400005000810004510543c401c8804110503006040101000c1c0010b03514401c01c0d41c0441c3c0c0010207841d0380c100468000c030305038110b141820388101091003542d080c0c001102e034542d116124000c206420507a401e001d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 659345161 1250 659343911 659343953
    0xd020c24070918020f1306020d2c280918050718060b0a0201050103170c0c0f01020115080114060d1515050a03050c090c0301120b04080421 61
    0x16003081c10340286490420700559840c04822407410f115580c00d07078103c812002c1d902c20090784480306484010b80400c010700c2182c015000d40744061901e240300d1071408980d80b107100b064001d004244646101500801c0305001d80050741f9217443c0366050780c8903500c000030b40a0302004082560518070f0701419070f81005021380072045249d9810000540105143c400d8500a0510001f5000c80c80031160180c090b40d40007011405000400d40b50669040d04004e050300d020f46140700c0c0ea681000c82c542454816070302c2c00e00780c2e600610000b400a1810070102c03044101c052002080244001c05e5444038010103600c070948582d0746180e00c2c400d0f00b0f1840c1b502c03980a01c00311003600805049482e18440c040214003203107101e5130b4805801d455402c810a44201a0001509c4410520344a02d07010303a648050041c1d1521070305101c40003030040c40c034460491741614481d014510004086a4a402440001070400c584262090101056030034030207020420802e040d004004201d20035051400b256180301c09840f4107 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 659346411 1250 659345161 659345233
    0x201020301121b030209071211091021240506070b061c0b04080421020f0402130315060e070c0c140420090a05030102030f010506030c0d020c 62
    0x1020500c0301090b8400d5042100b040da40100480c0d00c82c0403c0c05504000e602600c4981441020b80d031150041e0031a00000408004421020340400002d00588945582c003041e041100d8244510407407001207400c40c10000c042122003041c880b402903460018100a62505c0220701c10310500140c0c40000060400780d40306ca103003410b10340750034010f4000280464003500401030b003640007440310a001000d490700002000d4990a0501e4002c00561061141490002d00e50004101c1d680d0303800c80040ca015801085150003218203000e000c040e4004040480c020407401d0000030200c2c200d48225815070400600c001490340c01c028041c21099006444d0004200700703180c0041c006101191a2429a6402c1c00b1458180e445400001c01404000c1150000c50811400c050b48400804020b0215804111561141280c03501e00745402c03404104e58520171034898100402803800e0810045410550008100345001841204ca2041c0d070310003000801550721540c0c605005a0344100d80d210540c0c00e113489061 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 659347661 1250 659346411 659346419
    0x11d1e03121e16050109030c030e030d0c0605060a030213060303021615030f18030e0102061806060f12060405060a1103270106170f0609010c0801060f0e04020f0306100201020301 78
    0xe2041989a4282400341c0043c441c610790441c299004031090744a40280400001c03490020400401000110089024612140d05030b14003c034000203041a155a011180001500d845e0080c0101900396038000ba0b12042c0400075031a000f15090748003400c02c0003c18007a1840c60000c1c980580c1410b0460f031108604018850000c8499044204030840d14020800f0380743d02e01010300600e031680d62102e4080c5007a00c580101604880424007241098090700c3e5140e0340e045081a04090114038221190401400559140f400340c0d208107543c00040c1284404004052120703251610681d420703580d5900032000c200840e0720300e009081034101400c1e01c0750700b5030410f2034400704100100440d0f4480100703014400c10042c98250f002c540101444404100c10344481501c280d220351504800144901904001440040050181c440030198594039180c1e00d82c40d150080710318440c00c6100b14100107103070740c030b4520603079a0380064041b0540c42100581c2d2401d1a0b0104492500c403400e040d000c1da401400100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 659348911 1250 659347661 659347687
    0x1605071e0e0a021308150601050307050a030e0307051f05060102160b07020111010f020d0e0d0f0c03050d060b04141807051e0301060c0b100311011d1e0312 68
    0x40454041140107403298840040316400b038003500f0120400c441d94004000390400000607201c03210052015052502e45902004450611044604c003011480800100082c80d11a03400800319641040c152800c0c542141e49403410580100d0b0102042c04504296422110b65442060f4200500340018a843e5121040345111402c1911591007480000328501055900440c518032003610088002c215201c12030000d00000e410084840c20312a1400c80c5080300308000050140f400b00d81030304d0712044281602407c1315401c5503a8401c504003e4180f140c040e40d4039060186a02601a00c284103842e1030610314140c940d85803280c40300d442940c803240350400c1000000c40390b90300405103250044d51022030968a8405031444003410114140010002500c560304c41c210180c5d0620440d003203182600c441c800b490883c051400301612070020310f5019030256001d0906540f020301040c00441c0e00750311080001e215000c0c0d80000368001c402d080c4400610303242c00d1119020380000e408405061201504440c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 659350161 1250 659348911 659348969
    0x504110a02120a0206042a08160504020702030303010902070f0b0103290709060f02120f040608060a06050906090d210f1d0d0501020705160f050402040e0703050a0e03160507 76
    0x29110071801254002d00880d0f81300b0003e051007d9070b0003410629035813840c103561024014031040304001c91003008146da107881c1c000c030303120683c000b070045040d41d0900b9030440c029400b00b10101c1e401400148a034000034030944000c0d0086001e1101c0c6440c0030101c00c0000241c4100e2400c101980d0800c908014446402000c503c064410a26125110003141c08042c1c0c5450f19405c2e05441c14080460f169010b080601e0080c01543e44590f100c502c2600c60205021401420380500004104140040603260400c0005000d1014005107121403030143c940381d59605601146480b22a0101c8000000102c2d1b00855904000d10282c44d1019074403952080000e4001c0c0803071085441000310711901028400300b5016900c0d566040300580e02c1c0c40b00703103a043c6110180c1604c5500380c40c0c41001e0000071945054800e8800300c401c0c0e14030031416940ca010044005100c000e00b4a2805583c030b0401c400742c0a010000341c1110184420101d140403910b0900b14600300031503000c509a166452140302c08039840e0420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 659351411 1250 659350161 659350163
    0x507030c05030d06090501140301150905060a03020405040f060c09060c0807210c0303111c050604062c010e06011b05010e030a0509090f2703040504110a02120a020604 73
    0x201080c100001e15040303045200303500c2000d01c03450030101c004c10a0101c1da88803034122020041c600c078544c001e0381c0a0500384c441c04003100b0351100d0260010031a010382a0403499015030014025459580c0300d0740040c0464070103850545003c815400000100912403140240d1110141005c02041c0c0c503042e00100b4114201000a0101002061140400050004a58036061a5000a4840f10040c98004c0c19140e400109074002820107010317884011220044405104c00d2a0482000309240040740c4040c210182c404d40c1c0042d652500080c8120b19204624014090405004405019450520b08041c010380000808c040920f05021042ea00403012242007450760080d0035140609007480e0b801003001080c24566400000303220100a5401030080500d95004c4810003665120707c400d111198000b141c0444580010301d8808912074410818045105951003c60f49442e45940105054511030003109403429008030324042980e80610007000e070046001107041c00d00760400e900950394000584 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 659352517 1106 659351411 659351417
    0x190f020108010f150305090c0a08010b0109050301050f04110303070c060f0807030c0903031101020717030f0105030303090d08070e03061e0c07030e09071b06050114060a050703 77
    0xc1441c0944d4200c103c481070700080b44000350001c20010b8190380c1e031482818100015540c529100f40060121880045164204203001515298054000c54884d90620041100018101da4256841500801040a550b04140c0800e08510440601500c81041700502117011034000c20b05880841c52a030b1030039540c0d640c100c021021100000d00c90400100b4001301080800c0c4200d94400c1002144400185000e4060b5540c800001c40109242008503011003082381c44610b070314000f8014041a8040c2d4914070342018100e440d1008810940d0900c20103401150301548144804918820f02074212406820b12207180a003100800b40b1449d201030303e10000940b1f00b1144c00075501c001c0c1c0d140d03c0da00b8100c0d10b148208881494024a220704105000703030506080848100c64076010b81c000c020008165060680c2081c01011694802c1d000e58810010140c0303480e8070030200c1c0c01c4281c148ca = true := by decide +kernel

theorem cover : BRFrame.Cov 659172661 659352517 := by
  have h0 := BRFrame.cov_init 659172661
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 659172661 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 659172661 ≤ n) (h2 : n < 659352517) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
