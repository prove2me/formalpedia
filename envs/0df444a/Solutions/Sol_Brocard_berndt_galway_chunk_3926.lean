-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3926
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:04:36.221009+00:00
-- url     : https://prove2.me/submissions/b62688f2-092b-4929-9d9c-c76c36c47421

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 705935251 ≤ n < 706115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 705936501 1250 705935251 705935287
    0x230f0a110a120b0d0b100e010b0901050417010f021824030105010c1506080d081302030a030c0f12030501091a10050309030f030a0b010e030c0f0105031003152307090506 74
    0x26209101c445d080c01c00082d840d4503a4250f004110360085420008035014009005440e88040142d41e07652402d8117010309261500d52403400302c0360641d200c50302808240023600141019040e011083d4cc2581d070950100002c141b200318007889003050620b4039500708105401242c3c10f540007070800801048076880c00d09548044501e4000003180340c070b40c01080030440403070070440512050b0340e03000140d11a00d1410f0682101c06d0802581136000384038030780c0000d000701c1080ea82180103400c248122041034846800d400c442c2c100d070100181c0d0301c40050081c21600e21035403c00040341c0340b4464403181e01401040701c00b05240380d0300040c044c0200005d1003c01007001107400f140600a000707500e9007400034083d000b4205000340580410750400c0d00d10024180080c080818800c01003080708105ca50400546070740d4800b9262500221107060040f011031401101d06061104007003000a10040c260003000c00a1003081d108030f40c019001c014800403a501a040a00380c480031101d043d41e03211480085d6441b50 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 705937751 1250 705936501 705936503
    0x71e0b03041131020403140303010e011e030f1a0c09060f07111c020306180d0c02040b1c0c0801020304020a0b0d090b010e091e0d03230f0a110a120b0d 66
    0x5201078940c0500c980d0704c0e00540226481a2070920084d40f0549140e5160301090140307541c0480d042c001000b0079006c03011079561007941170901c5145c65840b40c81d52400104c410205a900c01c601a0407600004001c0710300c154001c0d201c40300d207800c0241010004625104181c00e8070120340010032480280b11441e505103202150003440c48409220490718031080c0e50040c03106a12038015140003c081c4215019501d600008010240075826880c003405d407100c400b500c0d400c2c0d8109a0b10020000c0340d495151082d50f8030155296003040d903040d0392520202c03000c0035030410303103803640180203000c0107841e05000d050030755604070a8161190142d41420b0020b020661002c0e001051603800066030310b1042e20381e50300414401080c2c03000e228500303500c1c040044214082d11910f0344120241c0d00d00c0fa1027a408200e0740c0d017061108040c0101c44205141c1203442c1aa801c6e00951050400d000c00d42c01d5910071032401d000059a590300340030032588050309002c1012502c40e280ea849004c0e00b0746543d52000ae4031186 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 705939001 1250 705937751 705937819
    0x9061c0b01030605060f09240301020a02030421050c0105070614070509041d06130c08030a03020316031505010503130c0305060702100e0309040207080c071e0b030411 73
    0x120a05050100d0411030078442581c005203043e0100d021070605594229581c40f001d0000c502c0c0307403129002c00d02c08200c29454003c90400e42406416659070a0004240c1c541055005545507410541100c07182a464129040c40c0609480508000303003001ca180140c4040900b8219240c2c829410f000010300400500741c0c0b82c015140080010321038101000d012080380aa40c01c00003100102264082110254014000b0303600210004602210382c510085803d4840d00451007035070750f04c10b0f02c01c0c6103402011140011075004810094a09080007603013401c6581e41c03030113001403407403000d05000300340d4507000b16410000004000344c0840d10803801f0021169200390840c5225503282022502e41c40c0c15034055006000304080e820300607541d801060a5220200042c501e401301c0d04003000000d500010003110341c03407802d20064442000511030140200b031544c016810542282600500083c1c00e6044500c4c1318009000344004580203001c0c6142c2b880051b40d070042e031803c100940300350f800e602400704111 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 705940251 1250 705939001 705939049
    0x26190606050a030507080423030c0604061d060c160609050d020615120c090403020a12050a02060f070c020f030102042705010b12041509140109050c0f06090906 70
    0x1455071240c001e04564450383d03810452038503500021505580e040e14080c0400c650900c1c0c0d54140c2007510894180c0c041080212458030146400003401c09408072410f40c1c4207030307031507950300700110101c802114500a0080940f01c1440d1040d0b01c0c0c2d52030301520020310001014141c00d4070030421185c1c0000496900302c405c44440c0301175070702c0c000d54802c0d045a070040c20905030311180300c0904041070300245141c4000d01514400100b001401032400000f041070301148544d010031f034007081850000700e00c08109030fa25143d40d0303594110301a00e0510043c28844800c20715800300101c25900c2000c0c00c20155045482d0801d4240341c40c0064003a000d260803520044410500c6254a0308603403444448800668070180516a41d41403022882d015080c08a411203000744002400542151034803110f07804d2a040c0003d040401c1e484072000303c5801004500a03a560301c4030f00e010700c02c00300718401d44a1401c940c2c43e83c03031308011804208140101484d42e40201e21600c04608144da03907240c0100600400040014 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 705941501 1250 705940251 705940259
    0xb0405030d0f0b1513140402040512101a0d03120906180c0f030b070c0f05011a031c021c030612111e150306040e06101401261906 57
    0x100400b11030b144a07104051400000c0038013080c0d0802c0d02e1000705200c03050341c80c8a00c1c1080911800c0c080d00ca51581c401e50800000c0b40a5907200fa82c4108a0340c2c01c002001c00700001400c104c02c40700034810345148420b02031103282e101c3d943e2103140c095096040c900000c607a0103101c00741c8003609804100a0806041c046031000e2444420b40d284d42c81c13070207040003602035075031a003c000500d4021b01000e4040050b00c80025611030051058100d00c0e0722501c1400002c3c080340d181c10b821502c2c441c0c01241e030800305c1004000399107020403541059104040f250b04d01b8841125003c0d54444c13041111000c5a80240724418245010b03070320034401409504030a000d554030078684880d8500c64006601c0c03003964600900d1a05100c407072440f070790a00c03001d07210400c0600501e9403c2c5154000412040e4000e485480030b4503161020300005010b8030420507015082c605104400303080740000341190341040711801004002c88804640c600380d4500c0f50982d080d5036200c41c400b404402d002e0b44041c2c01c10a04244d0001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 705942751 1250 705941501 705941531
    0x6030601030b030a05061f050109030506061002030705030a020601051f02070302040b010e0306040c05010f080c1c180f0b0a0e06060402030402010c0c08030408010b0603041208070210061d010504020f070b0405030d 93
    0xc07c108805040d41150305441e84010748041a650202410756400000080c200b41095041800780b600940112401d1401aa617164a10350103031070001c0040c0c00401c0100001e052600c0f940003442e039440055003d038149020029a40c0b108c03888040d102d5500da84c4109580e9015020902c0709080140c290307011840e00e400c00342002c00c030502c10540040c0128001012080c41a42e201e4000c01000d0061403034a00d94819450b00187c0c0e000d181c02c01c03540da841007088401680c0c3c0705052103034401c450510032014036040c842d022901c011700d48180b003420070981000c0c401340454419480b6008a0700141c40780c80714001240c003841c404038000e2030303442c40f11004520300c40008054800c49003424003e03ca80141c02c402d0080e0b80c00b040c0d6006140c0e046c5e90214018141c01000c3c00c41d44100c0c2441258006d10302c000c02034040c1ca086034040c10b8210081d840d9901180560300715540544002d480541c540b101c4d1036903141d100e21403120007611a917a00008036042013800d001303c0b6201c0ca88060203018922104080d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 705944001 1250 705942751 705942781
    0xc020604060f150b04140415060f140c1b030319082710060f05100c030e04020406030606170c090603071b0b06030d080403091806050d03090509070e06030601030b030a0506 75
    0x1032a06c0e15400c030814980f494030b801054030740302c8807800f2241c2e03170b070301e0003006898550608040d03400f40701c0702000d464410703c0301001130708102c80200024130143d010725104001e827410f1034072180c0c020f40007006200c50024504203052800d400703e14040d0f103907554182c40418152500745e86103011000b80c640003508078900103040030100e001d0030340811259540c0c8010340600e10840c0700745a00302803020740721003125000340c0e41030a1190090a04104a40d44900010704a07409600100d010a0303540400f840003940c082e098000101d51300900078071500f403000c0c03004445d01030003500500c039503030000005404e0b62046038180c02d61850490b11b000142030916190360780b100304441c82400f038898904035100c441d105d401c245000350b4058840603e81410700e0784000c900410303410940d21403515040002080d850344192405401d000356907080002c0e013404108092500050b059104010900da0f145049559850403aa0002c0f03003424002091152a4046410070001075006801d50180764104005e280b03040003c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 705945251 1250 705944001 705944009
    0x160e0d030f20030a200d0e0402070809090c04060336050703050105010b0403060c030903081f1a030a05070c08040501051e0316080610020703060e070e01030c06020c040c020604060f150b04 82
    0x11000d40e01505d803440c0c2c0e103014066480c8001030084201c100c140c2880d50041030054003031070302d00e440d2140d61800704003c184e042e82c403803134400c4000600308111a4141f154000401d401540034101d0107111246000c0e1107510241c130203401c0040f195040c1000802c1204600441d8058000e02c171071340c1d40340f000b40e4180d08030f44410f803582420007130a200414828880c0d902e049505440b60401510b07561111808880a40081038174103200001c007242010070203102190140d541b0500c1540d0b850300c03074000341c103442d4040d00f100d0034805c5c1070103c600012040c0055406982080c0ba0442e100e10240100c0800d005204a4210700c0070300000912004e02c8820f40c3d900704945040c3c65a44064540900b401030703110540c402e00300143c100302c00a10000c1d1698206c0440900c03500102d82aa644071624460402402c0e030048400103000c06007000316a405014051294900300ca04201c9003105140281d180c5000070002810304c2d07a00c1c0e0100d80110b4066001d5000d110b0788040300b00155446003002c8800781c0c06402 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 705946501 1250 705945251 705945287
    0x2c01061107090b030a2d0803150109030201020604080309031912051b0702060f0d140f0907060915030f06060f20072606160e0d030f20030a 61
    0x808075030b2403124020340907600400b5004207900d48450303e4204190008102d500803100c04500c4414100c0148000300c0100c0d40034800040d60703410540d0314052106040c003507150500590800401c0580e80200300c10780c2c880d80100f4883c0c1c3d240d40303e035140d500b188507001c0750710480f5280c1c0d0301c00c40b501980840c9031180321004072402c00c02900d0303026500b950301d90f80404440d0f40444c00c01c1104014101300c0040d1002003581f00382d03141000d00130084203095540c1e803000f031382c101d501c14030403c000d0805840186c1e40180c0c00701d0240c80b1217410007400412071850f600034007003d03105500600328040e101e80d000c0e50130013860400403c01141c54490080c010700400307001000060101c9586881e11600301c1c404156554502d00403c141e80c40c001009000320021403542800d84200f00400e01802d4062200070b02c900c1c00c2c0204003282160400c800b600000c100c410311030146c21003820030000240c21a5041d42c1070395050400300d0758130307420000b1424000300801031900103000100300f8400c115000201e603590345802c84 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 705947751 1250 705946501 705946513
    0x9030610150e0a060c05030906030a0504021008040203122803050106020f0321071b060b1c1101110c0301021911190602090a03050a030f02060606132c010611 69
    0x3400440d11035031481d582e0756202d00303259020810720340501d0f107100765284039500b44c03030600d2011000140280c00844d411071255444400f004110300c2d0501254400c0704660401455038101900420382c0c07682000c081c0d042d845000103d40d19490700d03144209124140d040842000042001d000901900c07082c8107920252148400360208800080f00356819903d500100c1c490190903c1c0041c0c408102c0600448240301994504161890b401c0d00c0401280c0d00a1802190140a00c0305000481204250101c08014003031426400604152504096441d09180c08202c1d90728070160715050070307428121154150320029070b180c3c22008800d07800003441402c5d121380303c0c00c03002d140b50b5036184c44d100c680208820390002031442c00100035034054410000b0207030501c641d00b07803203640d51882c00081120660119849c10048101c0769030410600764041400d44101d41041c003295640c826800035401a911070011075000b46120804041004000c40c030900c000341ea441d40e46110140440e10180841c1c42c3c0b9000c3c1d2 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 705949001 1250 705947751 705947789
    0xf0605100e1212030a151703040f050a0b03180c18180718020d0209060c01140a0e0a110d0b04210201061d040f1202030406231e09030610 60
    0x1040c0b03481c07007a800c2c8407010301c4c503684c0096080c0101824503240302c9403000303201d0105104403107911213820a01c40000965035541171404023003e6000d20b9020b10303c241c5511109200364548a030989801086a0070118020040210010304028803a009a500140039040201c0c038100c1980840d0b010b80000c80e8a0f58001d80402c5201351942014091900c454060001c28456100c1541c01070041c104804801410001c01d10001280c03a030042400c0502c40c5c0d1a44820f51054610201c0349800c203030544400c008520026015540762032407250050100b95a0385c19040e05900e810a400034415440b4907039510510b414034101c0d6151004181a0101000e5610055007040c014450a01544c554190245003407680048505c0480d200030400c651140744850140300041ca2031000c05c6002d20303d0780285442c0c07420400020404604030340b403814482203200340411801150400c0310740d504c070700c01180c091400702c80c10b261401b80308044410b03405119800821801c000c0002d12007043d5080320f49000c47c04524 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 705950251 1250 705949001 705949003
    0x50418090201020a0201110106030b0106090303030b01030603051b01180902031006030506010c120507050714040c170a0c140a03020306090a051512100609050603071a0d0f0605100e12 80
    0x4010002c0c0940c0c0415425009507004080170905604d17100000300380a900ca03901c1482540b000e034020700108001040600030144c05001c0e040d464002807a0401045241d034503500e80da01c5040210780c20300544110f440b05964412a1500c1d4041500f180035120141d0312441c00d0002d5104540c1410800010080410b006101e07008075030054030705070b40e8514042d00c06e480300c0f0021000c0508220600500f006010b00090040c04848020880a5441d116052074407041c001174841c103d0000c0c04015000100b2401003110018031500440c2160340020b10b005211419560080301801003c290f0b100410481030156260300298421841528104c82035190403108505440040c2da0010800c000c0303100e06000c50070680c084040381521201280c03020040011002c088035002d07040040307a25254020031145080400c1984001d04440d000400c1c90480c01d41c00e00c401d4002c100304070b0360098a840ca0145c103035a2540084000d454000d110081c9010040d402811003206103001c0b41c042c2c1422040940c144030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 705951501 1250 705950251 705950261
    0xc0309010e100507080f090d03020705211203131a04060f05090a02040e10062310021906092a05091509040f050703050f0111030709091d010c050418 65
    0xb2191a858184901d40c0d807820345640201800c4450810b0a2201500300c0d82d6400d90441801e0103a00900b44003401c20092000d1200c00561075150f002400c07031414a9000b000548001c0b0200d9a010341d61030784ca034621100340c0c401420b103010b41018010380c11b08018845020303c0c1d03030285125000030030802000d020140f04ae41d400711944030007608600f02c80400360030b068005109003456041a04c006e80401100502191100d811600440241404042c54081c1340207070346070542c0d000c440603410f51010341030003551409017104511100c00d00c401c0c080200b040c15041038125603440203181400d50181009040b00c41c049408070b581d60460b000000a00b0700301008e05a0060310281011b04a05181209000803820007070421034000003003c3c10303032002c81c0043c0f020784040c43c410f20261250304240145182558000004090f12600420501c01115004100c2400700d8401982c003041c640780209001d15010300a5115036425400d010b0301c030080b564400010010b0b101c1040c41036051400f04107424081ba5 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 705952751 1250 705951501 705951529
    0x6050d1410110d0f141603061a0313050a020901060e0108101a130b07060c08070201020a0f0e21010c111c03090c03470711010b060c0309010e 62
    0x40010003c1c0102c1000b160000345402a5001c00070801c560994002144400c0441c4c820300b04032503042003051802c1d4903003d0740c402021665204956002071b1440c0c0d810511001e019803404051005400040100038041d50300200d4000740810850742e550600a030264170300750540ea0004403100c00107050f1100c80d804030341c103a030a00c8141d030100b800b40b18103540e110b5218604440c50b18040200c0064a00300f808018625a84204004030716008401006000b004c4013400e15425a40180050800303594008403000000900b032504080e4802a9000314403444401580071124034098604804030b0b03201504010701c01055952840d09600740c43d54850344462140305428400d2008000ca400e55520036084051580e00408403c1c40a40c1e1341cad62149003404400c880c1c00d944015420700040303203400c03c0010403c603210300c003507190211f07201084103080000020081d2040c401c07c0414262902000d500443c0d400e10080c203200c1e40c90301080c410540d00d4020ba1491303030019440440d144028101040c038503182d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 705954001 1250 705952751 705952781
    0x1104030b28020a050904060b04140109030f020d1109180d02070815100e0703140a0b010206070c03020c040911131e0903140417010e0d0203160606050d1410 68
    0x300301e41800c110040c1d80044640c03820800c00b400182e9155486104442c020822024561354071803074001071050304001d4220b4181031240407002000484c00c2c04181c0502d943d030440d042c45000c00a844c011031501c5007001c0b02d5801c5100c280c10803c12207400d2840c20356542d485000c40300245200340b0700326070300c00090249101ca81c00082000802603006a0b1141d00002c00c4182003030302a441e1005c16600103000c4a0860000b500e03102850342c4070380785158890700074241c40c0c001e00c0460110740000c1c1d914140030780a03504004a004a410501d8824000088031079070081003840302e0b07411030034140c5030040203101040c40b4002e00010000401542c0c442c1d4801c0e882e0b20305440480b111507002b41002083c0084081e010b00032900300609a030800c6000030b0018004507441110520500140b80b800c46400a0710f0503000c1d804414031000160300002610418881110100d880c10041c1c58100c02410b407540c0241e0700b10b1010b4105001f00415070414858614503074040301c010000d010120400c2c1c44580000c02d5107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 705955251 1250 705954001 705954061
    0x1809031b010b040b030f0a1b050d080d1a1e0a0302130605030c06120402010f2708011503050331030827011403090f0a05070812040b04050918011104030b 67
    0x560044407550035056410236801e47c0b81d030f00d40210300005600c1c0360448041400080828401100e48208260640809074058900240c1d10114004c7c2c84500007046008181c1207002d101c40c0d480051540144da800740050603450491080003014043c02e000e010f1003409100c4088030b20b410007000b61202c80c0c078212011111a203a0b50015034000c0d42001d0715170704001841c0c42c04ca8882444610101da0450b5034031441d81e27520f240c00c02142c01c441c4603003c0301c0d47d11181c0710402c002042000003a520f0224241c2c0ba900310041d64030329603c0e0301480342c080c0d5041c00100c54800009105082c0040e244420300202d000e051a080100b8603003002405007a46c07400701d00e0404080b0014441c6901031603000445c841142d00200310f4542d010f01c2c08841d080200d4407036201c0c0405001c401e000307010085070310f01a08443d0342040e0a11180402030300881c00303803500443e0918001409880807114405403000264000c2008919024a0013640d0384580020359400c84014041814920308804905805414050100c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 705956501 1250 705955251 705955253
    0xa020406300c03031b0519120302070506280603060207020a120503030f0c0904090b10150e040e03120406090c0e16030f0b120f0c0a03021809031b010b040b030f0a 71
    0x103402d16046003000c190017040700454001074800c2080d4608204c0707007051076118140c00e18011900342803200d8410704040c0140001c0c400038600098a81c4c1041100d0300c40c45551000b46d40c1291301e0b50000800d8113805003489000014003525130f0003000124000d49021807410303100e50007142c0d1a10241002001c0c0d600400004035003404034004c030340c0c0000c2e10788080c42c1350002c180001001d48403891350980740319040800380507010401010000042542000d0170301ca0b01800340740075080302c0030018001e00441d15050000b554000500440e584210114440300f0541880d08004c0000c04072078804580d807407500c80021501006103611036100e46061403190b80d4400360200d08034040c2980500c240d00742030312641440c089649124103d0040c40c44000100003005842104c1454410140c40e6a40150303980b00d81880035031220a410003400c010000d0300c41d495200d040b8414a940708100c0c01103120b507010005031201e40c4c0b040d00040000b65048609001c1c20201d501003540b80c07a60300f07100100560205a1641c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 705957751 1250 705956501 705956507
    0xf060c120e1e0f040606170606070b09031e03060f041a04020313060b0f0a0b0f0408030f0408060a0605091b04051206061011060f090a020406300c0303 66
    0x100e203030038510302a5003062034000400c24070010b4280425a00c00c504400384030310300f403c0703c921400c080308071014440145043c4003d040003031840c00701864400c174580000c160b9182d21084940a80c0c0c4a4a2038a640c078041c0312007a102c3d00454164000245190740d80c3c0003c40e040303801d9074040c5030000c00c555190410a8100b00060440030210394180c54451a81d0070980d5891010358414200d0340300c541260b0545150405c1261440c4001d2803007200c0c540c041e41c410b51948480e501c251000900c2040e41d0b1711480c030113034405000e5a84542002d100000b08188041c02a40141003103c010008450070741d01ca18102c0000e6440e41c0c0034598010708900d0020346040c441b441c03000c220042c0c2d104020318194541d030101d05a41c820200d001c9840d4454030601c441030402c81d5601004d940c0b589000301c007280c610385c0c146031510b01c080e0618001501440114800354800d00c281107010380d0080c0100120b65407020200d1012400b08007504e000442d584050740720034461070190385515800190f6110550440d45e0076 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 705959001 1250 705957751 705957773
    0x1d010507050d0b12010c1d0307150c0203160303020304030c0b03090a110a034403041104061206050106020705060a050409020a02030f040b0d0c050c1e031e0c0105010f060c 75
    0x15a4458500b1400b0b0a1303151003889203010000b116039514501d4083c00760445003032000d41c40064042d80c1b000c2410019401c2c6c190b01e12070041c469142000e140041ca00009142c41c4000c1d9420040e44400c180000c20036070008014000ca0340306007100111701c0e0307031078003044aa0302080700c0502440d0400c41560380021507003000300d041c400004009424141e12600c1e1203c8032542d125040c822080245032103024440c100d03410740700951a608445485030141e18a1b0011404044c0c8020010041c02c00601050381d60b0740c00c2180580000240101108101d040c000054003003841054090f00840f080400c0ea400c100040342c02ca2111510381901e0310349001d14000082d400f05034203104501042c01488401868a8010802030040101c0725407039452501c022401c64180c0d14510042c00f1017001004170084010031802007035040400c003d054140c43d040707003d04500c0740d0021441c2804011121001030050322020740340c0710306061b000304826a206d001c014000c00260049101044019039000c00080300040d81d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 705960251 1250 705959001 705959021
    0x515070b0403080a0e01062606010302181e07020105061e150f09030a1202070501090e0a0203040309271401030203120c030405041103010302040b04110f0a0e0a06031d010507050d 78
    0x4032804285e48039400c6941c07030380190946c4010090054000703580401b0307601e0744021110143c002e5500d1130380014040042155016407607101640000c0c8600305d06554104d25080a05400d5568940074400a0007807a00300d07a000d118810001c0062890070101081d440701d003202900030300e840207105846c0709068001070720300d43e01c2c1d01d01001400c40d030f80c40c107018204002e0b1080b508404c0342d101038500681001c24136040b8034108100c010b0100324000081a007140c001e980581b0041e5a81c5840c20b045810000d103410001584074043c1d41040114030311040c1c481d003450102c2082142d662902d80e460450700080c800654564450300f411000300361650001e0811400c00400c903460581d0380d40106040e103006035901102c44001000400550415000d0110541d004032410805098901c01e0043d070350290101208051801043c01c109584c0205401c0030303564402000c000c82186c2c1d480000b00603060810030900300d2055115040b1980d40c05004440c0250900d445103030802840101000c018010201 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 705961501 1250 705960251 705960271
    0x30801060e061905070507080312010b09300106170c060a09350d0f0e060f0c0a03030606052d0712200a020f04020901030b09100515070b040308 63
    0xc0b00403c1d0380703070091516840c0c0540c840c00d40b076407010b003041400c5c00003540c0501c04541003081500c01e01010000c2d050305490740d2003c065143d034139400102e6011100c08900c81c070070740001120000d00d1007111044010040410f00284600b945800010240d0000304e40404001c3d80310ba08241c2441c500100a00b0110142d2300d05805265510192004a40c10741c41400c0a504c0e484490208028166900344440320f0781003000b801080034600e00180145140100700081150740c0f10791544c4c55555900311707520280d80d01115900d610140b40300c13903100c0322400400c030b004c28580300002414a000344251240d40d0f81e48030205100400c025401d100000d2402071980075090204181c0000800d02c52080511000e1640c90402514040228498840c903588200001d0342c4249040001640c815800c103050740c3c82034501603110b0440070011780150001850250b4443d240104010080c2548000e2000312042115030701008220010703015406e1041480103401c9203004800240031a00611a883d04081281c03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 705962751 1250 705961501 705961507
    0x903140a0507060302070303060f080604060e010209030f01060f050405012102040f1a010e120d030e07030c1d0a050606040e04030c020a2705011409100e0a141003030801060e06 77
    0x75503a80e0500d58660003400102e0340c0440e40344203050b4140300f8400170744078528409043c503050104259560100a20003083c4a403910081d07a02c00c00d00b90180d85020001030212910b043e255071009001c6c0c030240c0a035409441e4801000a41880c10b0300a140c12614560f01c144c203c00a041e2400003204440325007070360407503100c4281400341d54103441400100c094a10405010045550005103030104510500784260314005242c0400107022a00d00071050450030700040d02c0700c54602c0e440c24030080f40e0028181441100b070024408101d4420100d08800c10542d10b50a580c80d203c011040381ca0907a1501e07040801840309001080c0c0500d9226081806801c1201090445600068003041c46801803065803e07a501d408800c031100701d5545c0040290a02c013444150f0410303001d800c18560507600c403841034071260301103200d044001d00518003420820f40244000d241c0703500c1240c09484844080c05c50300305408000b82d08903c074441c0380c00580340d140e518460140d1800310121403a010b0002040d0f4424020 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 705964001 1250 705962751 705962753
    0x90a0e09070e090c0f1302090901030303024306090503070303021b01090503180415180b0405040819121b0f05070308010618080102130305010506030a1106030a020d140105130c0903140a 81
    0x116027618000c51080c1e80250341c2d5904958040041c840e08410f0400300c003e9a10306060005140c1240c40410306003241e107150782d00c001c3c1861800f5200d9260050200d000c00180c41060651680045c81a400f00b4451441c4003468030014034201d52104401410303580050000840380000b80e0300c6c0f00c144680090022031500c030300b8988050140b03516400615116075200c004100c403109801910f92541086500700311502c0d140d02e40300711512814000024000d29241e1070102180984211800051680000c000241ca141c2d428052819289409404151111074101c00e040c80341c03044801c419410341c1e60701000e92030204280d844103080d0720440c0d051008072001007001c50091010b0102e294880c1c6a9400c110703d1410111308560015055074042d400545507600841c03e0004415600007060714216943d03515008020003d00031800303803002d01c0741062103510f61541d030514540e060700c0b01105d60300c4040310050440c5046400c4010f044002c101104000c1001c901c0d40303c0901d56812015003914001034207 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 705965251 1250 705964001 705964009
    0x510050f13030201020606100c08090114070f061503021f020309030f01050411061911030d0c030c0f030c1209060609060e01030c050a0614090a0e09070e090c0f130209 73
    0x1034242000c540481d0108200307640c1d0410140342c100300160354442120138030140081c590041c4180c041c0020000184050542e4400c18140c000c0c030002d0341203180c94510600e404030401e1030b6500c2c2581c4140c02c08103001c00b040f0b80c600621048a5005103400f59000c5000e0003c07800003440714245056000901040d80ca50310240040241c8000b12400001c0c1487c003031400500e5403004502e010301500003803020461a140480060175050114104840327180014140985103116840940c5607103424020082c88168040e001110380c90061345880600314501c40c42101110080c03852080003a07009500e58128141550180100700c1c0a1480070031000e4684200400340c0e07285500095807191203900420a0051a80c1f4072405000c0c125500700d01d892a00000900020383c4100e035264119000450b05119504c0601d10001400c440d92242d100d86440c110a6486d00320520407803134812a60000101d020802107405a4801401010940c81c241ea02042c000c02c01e40c442c0d812145281e082001c08629a1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 705966501 1250 705965251 705965257
    0x6030b010906031401050c16060902190306200d09020a08060405060709080106080a060b01050d2a090510080c070c09091104151a090d080307020105060d0c0510050f 72
    0x4203075035012400d40e10754507112000c0004408000480c0c0d150009110080c6030040481c0d24020310089140810305450070700300014100c6500095001c200d044040b040c3c0400c82e101ca10449014940070000f030310003c001500c0001e4028069100110100034880b516000c42e03005d003009a00103030800130043e40b2000303d20b06e8501c040d6804d032510b40c040d5041280c034680c08400c80d401350a00800034030043e850124055a074092218008000e50f4071042c51043c0c0ea4441c0341910a4242860000c3c0a0442e2492100201c10001ca0340e0352504400c840741260900d003c0c260040883c0d031301500640d600424054100e030b82e40c81c0505130014611040202c3c0b400309400c51211405842e81e81e500183c08110f030300d00040a00429282c95000764144040f4810020496890a040750203030b16542c142800f442420003046d10811402c594071000a54001c800e211941e405544110300c1d503002004141c032060104004c0344600d0800800c121800764041c0814188400085d45084190801a040441200c8c403401260 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 705967751 1250 705966501 705966509
    0x9070207080a08090906220b12010212061011030f1e040602070e071103031302010216060503041713140103060906080a0203010c0e100c08300f0c0d0507020106030b01 73
    0x1240411070f407041d0310342031040940200044a401210620106001c411f0344900c40c03c150450365140040f19440c2c64584100d960101030500841d5154103d20b0031441c60802030318150b0045030100940c0c80310700d016103069001e804400009504009c000d40a400081d4445185450308282c054049400408000c000d07001a089035009000001e080c503903040784414004201008010305207055034010f20010045a0b040084682c040740c41c0d01190005038075000c44800e81c03901040f2400d00008901d44d000c2d020358090380c4030783da01c650ba400d0812124910ac0c016405140007032001c0100801482840304002c06422206040129400340d075001c00000b11080e035449507515800182c10402146007c0c811300500c2111800d0880002c42408041907000c6916101074040c80741c540914400d202e8964213803020540303888881601d4004841c00b1044101030a03000746600b101b80c0c0c0104400c84151211144a0307646582d4217410002d400300c0c1c050240c88003070710110665507154008808240c0c0403070258040c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 705969001 1250 705967751 705967763
    0x160818040501030f150b0a03142b08011403070e07030912030f050a0603031d01020109050d0f020708070b0a0c11090a0b100201050f040609240b04050106020c09040209070207080a 78
    0x1241180c00c0400129402e00c2c030b4807901d1460004001d4003540c91202c03180950b80c03c0090b211844610642036840c0a580380d1031296950300010ac2d080d82d0b01810013401d41900d0f4580d071020040d90762540811514114030010390382c9900032000610180711201441a400013070ba190105501009403a00550a843d4100100c002515206424001c500500950760440351540007000903034655103005003014200b60006124056020380036165a20035004009600d270400140c4560303a00c4030318080c121001c0d00320203030094051030000003000d00010075041d044a0203440380038507080e03602004448500064004a03096105083d1000c101c0d10b4150401d80300e40c890303540001c0c08850b09030421104081e00d00070b0f40110380c145000c0000500101d00e502e07411a50200001c0b610784d0503407070001c21401c081c0e8511204103001c40d14110900c0c0702c681040c07800031019130b801c000f540d899090880e228200715003504d40107030b2410702260050500400303039548024540b0541d0004d6031500c01003410301d0580d110a03100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 705970251 1250 705969001 705969023
    0x609050d03050f130201050d141003021002070b0904020a0507083907050d06090b0c09090a0605100c17070609051020130b0705010509070b16081804050103 68
    0x10440d0148505500044410b0f10b058440c5000c01d41c06140900a10000f810800d0100b80408100c40c0380c0c21416080f107001c60604054a4601e26820300f45140e40b205a00c0364520514104925001003400c6094401d01000e11345082e11038011300020307500506070f4100700102002410049a0400c1c040c0c0020f20400041a0006550a080c2a0b84000c1c4d0328025501c00c41a011140180e880060703250101d51041c2d03101c1d0264000d504080d001000303070070000f40c0507409005c00c02c207500c6441401012000d504860441098456002d04800c0b0b904034080c468100c412080507406c000d00400c08240164800c20801003803a807445101507050b006400100c6000751198410010480c0600425108000520042002000041f100003d680f000f0449050780d600000f40706d1409102044100e01818040d882141d5034211403808a009020403124007079079003d134860110701c04000f8000c0355040d160005000000750801e4555100725402035a060135007030032100341c0d0101d40d1200c0c014a402580100d5040c14 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 705971501 1250 705970251 705970273
    0x4020318060601020c06220b0c0d1107030308060105130807170106170304330807030c0c02090105190801050726040f0f240c0e01050903070e1003060905 67
    0x218090014095074199000711452035450b46410050751494450b002c0100003480c1c824200c0718042d8042d40002e51700a1000a070382741540000102d08402c402c49984040b49020414070894031075540d0b0100900040340e08020a02035803186d009002d6503030407030300d050550580e43c0d00a149001c42d107522a0a4088900344084c000d820203100d240700805401d22400080141c040240307480f131041780661680000074035170120220b410103a0096040d6000401401402c0420b840a4842c01c0200c48900c0046d05008802c002107101e031080c10f5800ba40940010100d9007080300b0491201e041071034150401042002c0000c10032b50900903207000d1032290301c80c1d504030039001c0c00400c9d4240c1000c080240004041d000e2100080b0728500120b0615006440f06141c60742d2480d0010501281c440c5200e52800c4014041550300b0403640070103885444d40d200d07074289010381801907036240142e034030040d0706400054081041e01c02e00d010700c9030300c5042c1d00d00c200c250702d4072952050112186500c0c2543c1c20303403186c0380c200 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 705972751 1250 705971501 705971503
    0x1c0e0c03120405041d06070e0406051c03030c0302121f080d02061b19120515011b06200a0e092a090a0306140c0f07030e0d0204020318 59
    0x2a05a0015005081d06141030303590611140710350f01c50b013801503030349040505440b61203c9007900c000c0342d100d003a145d040c1808600203014500303260010344200d28011000500307140c00308101c040f4042c500481007a0a5464038144e00411400ca207481c10f240d000c021031140d925004081c0c5100c0ca40364a442112030401c100c4681d41507140c2d82185140d42d1080000c188050b4000aa4aa1007940c40030a04a000f4969142c40024080c0000f41c03032034840039071141c0368800c0c0c01c2004a112240705107410040c3e684e8915200b0084440c2c90802d502146029142028440d0200c52141c0304174014000441e10307000e842028440208803500750000300d0408585802400e600048401180350210780b080ca490411114094a18080b92607400301d1407400c2d00001b1000303032003205980700800002c214008480e500d06060300a03204100144c074001250800107050502c04409855507400044038203420300031565400c0d00c4201c008440d45905c00c10602c6070400690300c41c002507120301004e0840c803130f446803500891 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 705974001 1250 705972751 705972763
    0x61b1c030204030201080f0901021b0d02010c0921050c061903140f0c07030e03010e0d08063c06030406021b0f03032404150303090f0f031101051c0e 65
    0x22000c0500400003040940e074808411a000f0955880112068440e03001d954020b2040d20781c12848480c0079140031040c03200100d0180609000c94000703000307418003084111070754001401000070010500020902c500040c075180103003248140c1c1110682880340d00002d50540001054040802d02c0b45107031407e00e075050181e8445056442070038040c1e414404251612282700410340050610042044010725106240c0c2c180340c075401a00801881452000c05601ca005400401c4046101c00340030507124185482841000100c610003006845031004c0d0a050b180380c040d580c140400e20311840b140740341d9905401036001c0d5104d030341c0040c2c0d40c0415112054070340800c03090300c45c9650802c18003110802c0020044a0f0b000f6403008a00c42003c0c010440454403400d0306d80100c1e0050710f04803102d6085400310704040b00f500d0003600d41001070743d0b403032450304500b035010b000c1c4281070b01100700308200080902c01e6005d401601410031a0821414564904201902d40340c490070303894558021103440d440c2813201c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 705975251 1250 705974001 705974053
    0x313080109021f0e010c15060f1e0803071101020307080426060910050a0905070806091207030203090f060906070b07090b0c0c0904020a03020303030a0c02100207030804060506061b 79
    0x3250494040e0a03601912011340c0521007070600c07541072404001c00002c00402c1441c00c0c0024804c014440e2502103035040d1603218000d20446201c2108445d400c0c035164081c010850b0001c00c0150310b80460355031080c90400608191605504c030612002001982c11006007010301900040c15000071524217009107400540f01c0400c3c9160410400d00c43e0701c1c1c10104034201e42c040c0b10075000c1401d48031180d0303810050040b440041c01c2da004400c4082041c00d00840d4050089001c1c0041790a91155210b08003102e10600d030001b400f5a108000044807820042d0140c1e441c90741c0200082d00303005018001c20030711341c0084011141e1580b4a010000859000302c0340d0809000000f10321410a540a062169581c10b0440014802c0c404040060210350b03440440901940c1c0c003405898403030411010002c068101e15071900c0c0940a0b0782240d0752101054400e44424035010f94944220380c0315620b4003c01014040c2c20103801410401042c001407010b012400303901c2c1011401840708160005a200e81c0d4051801 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 705976501 1250 705975251 705975289
    0xb0901031b030b1f0804032a1103061819170f071208010b0d1a1f080603030702090c0c1c050702011205100513090515060f010c0b18031308010902 64
    0x3d044c910380c0d0388010a158020b038182403400c034016074a002101c10300440e4110701c2c821601501d01d44200980c4250562140c1e505030120b42c22903c5205c1d8804011080100d8004a40c4c4420340104a12882c003e0f8658404e0180d00f444c201101e148103050129841000c400280101c0003414030200302100e0300f0304598055905c0c040d4103650400d00041454460307510f22210b5986c9407140500c42c1842e400f4040b00000000304695031203000010408840d9002d04001400310b9000e50005d00e05007008000c803030b60554000d1454051761b9441400000c6600300c0c44661440e0300c6101d00903292008414141c0d802d029603622850b4964000748001816580e1441d8410040c41c00d00d0140801002e40903071401c1920411641c0f0941d0840c41001c1100400c2c00c0b000261203807107000b0303004e403a0400c1294120300030074065418010500f01a070054641c3d01014400a06000801d0001207000320848078502c04401d6110540b407600d0307102c0d810080014602c0e00310920a0f590740000c801145080c100d55800851405 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 705977751 1250 705976501 705976549
    0x20d11011e0806060702040204230a06140f2104140106090b0609010f02030d09080904050105030a03021b060c0303270f15060604050414071b020306010b0901031b030b 73
    0x1600401c0003001800c3c0901402c008240034046503907036010b80d8041c00100c2c080104e00340c10702c80781c41c2c40b4240000190340902c4c08208082889482039450741c04a04400b040c072480c141d8000c914005560150750b50007000e20b039080d90700c200c03080c505114900803401140700000c0d58a00301009404c4607980d034001207501d03140c01d40204c03d40d244c040640e4183d803800d0030729410141c0301003000e80c214425010041c101d02d1a0038000070170400c0f4100a00101c1005075400c000c1030ba00c41c824103981d01507014001d805640101300c14103905880d4604000b101c000940028180000200c5445c03941d04140d41d03100d6002c1710100070402194074402c000f00560b6504008110080c4210310654a601c80c90f00581004d020620014249440d00f2044400400300580300b0080b03412500101c04100b001600d0840c0000c81006c5084180854600140c5200e60018040d000740e91034190f1100c59584600001d5052603181c0340050b24045202d04402c40440d515100480c84090354010480c7c22100c40c0c40c0c0a2241d0111 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 705979001 1250 705977751 705977807
    0xf050f06010f09030228090c300b03010f0903030905010b060909040611041a03090c2b05010914070f0501080f01060f020114092d0303130c03020d1101 66
    0x44560002c403501580c440454008800200303145030403541c0c0c041d102002c034071070005140f000c0368000810546a5520130727030940060400142c5003820b20b07140341241e0304403041500e445c0155a0141302010801000000c00e09a01c0046005440c080b103002e4001c240e0b01c500140503c8402e0240340301d80c1004842280ca480ba100380000d0f1101d002901c0640000d0ba102d40c0d04090290720303811100074161200d0000c0d8840720040c40c00105510031201d200c80390092000b141c21a04049030701c0c099540c180180741c0d1450140071050640c65903901b01c01c2d10150b40718075102d40031822000c00f03295140704031000b4000356030828194011080003030317100e14100200070080002d07d10b00c0c2d43c0d980d4191191468440c00070075001c0e0080340900f2650300c1740944c01804505000009100050740e840503642d030034000b8100d41c1104232006070074040380304d103001940040000075022075010382c0405605104054000c00d550716500460280010b40008413003403070454102503115038025990300e80320207a81c05400c0b61682e070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 705980251 1250 705979001 705979007
    0xc03090b0c03130f060b060d0e0114060102100902030102091c1e0302150c1918051509010309030908030406050720100807120e0a020f0604060509060304080d0f050f06010f 75
    0x511000b401004c100840d04081003440d400000071780300c001b803043e5124000f0800f410014a00c500c4104c503a50710308410b40e00001891410741d0b1207581e0503000303842c2102015202c100a8220844c040b80d040d5400c002c0742d8072039610000c55840c02c1391000003c6020f00014030f480d10480c1001441c0741103205440e442000020303800139003403040784140c41681580b0f4440320007181ca6070044103038000321070304410044200b40e6480508034140d400d0781914170700c16658a90521004400601b10800300074010041f0340504d5029130050804907100e8980a400039940d401d5003415a0043d40040001076000115030713040c06104004440c0c4558095440c11184411000042c401c116102004080c454001d00040c100d038042d128040403600005000d2003118460b000d15500c6091541d4100c0c8501c640403866909410b0280541e03050320860780740c0c5490402c0c4601082400d0300f00800460301103004004620704000139000c0e840c5030401c0300c08003003840d0818104410b20050018103490401c014184a0303a0040c0d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 705981501 1250 705980251 705980281
    0x1109150708042714090123010b0a09081e07170319051605070e0a02040e070503060613030501140108030901200a0b0702060703060605131701060305010c03090b0c03 72
    0x8003541420440440d203880765201d0f03031041038844480d24a0590001074804e0300070001031007071006200810a44d0a080c0c2c9900442d15940001280201c0080060004188000003040304083d6418241c101c15641d18100b40740c42035848480180045c60a841c8141c05070420029018100c141c0303100320174200003c1429903030300540e194104010242c0e140c9c488401d006800305c2d112031041c042c01d14003a00890603c1070741c0b8080741c17040c81c102c0e41150c000158101d10038401c0e036080d0f807511580c0e1401521146070880300760b003010f84105c1d4040d40c1002407401450031001050015480354002140b03031643c001c0113050003001680590300c0d0350030402918a2903070344007134410b14803816030700c00c42c1040000020709032426400d0080100403c01e88030900800c03d4000a5240c4180541e58060086940340c240c121018010404d4000711100241400c0c090030b5a2007e01d6641041d4100000583d55030380c0d02c500e030039102882e0b281d10201381c0c2c4407007610511440961075544015042030039407440c2449a40c41c10807074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 705982751 1250 705981501 705981509
    0xf0603050f13150f0e011508032d0c010f06150f0203040902180907080f1008070b09040e12040519080601030f0f0f050c040f05060310050a060801110915070804 70
    0x180b201c0240f203003100b980e62285025003134900d001c0225032080301d445402802450410740080032a24000079900314008110344a00000e031101c50107071114000040000c202c9130001066070103052241d40c908500920420300c1c81c0c1c0202c02d01103103241ca042602601c04810f024003c00300f000c1d030f011764901c140e0004100d0301120400100181d941c0e141040c8814a0344266101d00c0c0c0c80a44c030300074048181c2e44441924007604509004e94001c1e02d4131501b817a8901044d2055014540000b481082a900070030083c14900d10054000b08014a0031000300c1d0902411702c0481041500110b403c0c0302c58101134105d01c2c980802c0260025440d0305250009a4518051000615114032084c032002000f954410180c105a07000204030154007071407500540b0380d0402441d2500607032400c0c4503544000c00c2802441d020f160040c028019042a044647c400b51030010060b094260f00c07050002458a824803c0d4284810507c44458640d0741e0784081103140c481c0a441d16100c441305109203004504c1c4502121700312 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 705984001 1250 705982751 705982763
    0x5130b03070c0b06130f0b01200c0d030e090a0903090f0b0417070305060112030305060906090f060f0d030e0a0b1312020117130b0c0c0c0402220f0603050f13 69
    0x39950300c00000d901401741042c0c0c1586a040074449210341d04160418120f0000980710154a02044450003041c65010f04c14414560b001c10300f200d460b402e2405c1071540310350080c6400030080a01001143c2006401c5e11104446a45e0312071081c02d16034084404005020f0510080f20558038041441c40385001d54020352144038051091400b0802d010070444000f90b81c0a000e0300e81c1581d4990331804058480c40e8281d010905010000b412072600400141c0301e940003c02030300381030301e0340c00e48032908100041aa0b6000201503a94241c01e590741d8803400c101c01d1080d50303400d4440c0c1c500c40c248803e03002c00b58030148240c0024030000b44003101016001003912031000b5840301c0100e0721f000480c0c2900c54418441c06003880c14051008410a0300303007188006001c0d01308002c00ea101c2c40460300305482031a4042c80c05400041d5140c1c1d01789401d40007005c4030040680b842c104000030821400e59241142d202400a6100d584c1c100035154050145c0c80c0e001e1681049581b880c07500346d55070041001603a40007091 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 705985251 1250 705984001 705984023
    0x1103070e070f2006090303010e1533040b090316030308010b07240b030c15032805090c031501050904060c110604110a09060b0906070c1505130b03070c 66
    0x28084a4944800c00007035508075040c17410082003064680d8000c2c050a1011204513000440f002d41c204400d219020005d00414850b10b81150b004a480f08a6000f8251500304200c0210250324036001602c00703000c1c070b6240155076005a0080510380301c002607465907801c100860420102c0d0304800c0560448054000c4a03603646642c2c6400c0f200541b0031180008503001c980031404290109a01050151400740e04079181c2c40341c00c0c0c080200b55050881e445460031001c1000920b0000503120703a50303103015119000c00c4480c00303501c0000140c0300110362850707103a07003c003c8540c4280350401c4021308050980700e4480095048c1008902c0c0240c0090002c0c1c80b40b5110355400550a1141100303005100892003075600605140c540544441d20701c0c0c1065210300031500021480080e41d1282c48110f56090101d00d103080f03640024009240c002c040151307016810401c0001301c07480460313180380a00941e50b5400d41d4038042c80b42a50406807068000740c10040b81072042044c0c00360800b40050101d0341090100071 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 705986501 1250 705985251 705985277
    0x30f0224040b1e010816081b01050c070909060209012c150c010c17070201020c061902131d0109020909150a0b0a1805012307030207050d1103070e070f 66
    0x8260f007a200c00c105001c00d0308100001d0003110101e600f400c20046950303070300c8100d41c0d40c1d901c0b6036681e0048500d000c280940c039461a007a0b98050340081a449000394280c0c2c421680d51000f41c002c0310245401a280e072034000510b0000b56910450b1b400e8111f80d586a0783c48148003046080c2c8840202582d114050007035000c03194508500c981c141c40401041c00c00910102444080c01410a2000c10202c00c018a50101242405006000b5104441140001452540e503011000b8011030342040911366a50750811581e8045600002440003034003800d00401c803801e0200f00c0108000310140d0002c680c1520501c510341c07040e541c0030000d54201c0b0b4141101503142e50000d0025200845641c041c4544140000f140608103811008648001c4190410b0700c03003141c0e0b0b403401951100103180c940d84055107a01c100d00008480c510180040c03034001e01c102c54640b6101d401140c000b000000050b1041d00100240b0030342444c0800186010700140315180c030321400c1114003c3c1a00c1071180392681448003510b0b142d0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 705987751 1250 705986501 705986521
    0x1050406060f180e0c0d050a0b0d0215190c11040501120b06040f0513020301061502030f0703030e06010f03050c010f120e15130b0709050312030603010f09030f0224040b 74
    0x3101910021301d401403241070154296010b07a2180c807455030b2a505100004508035001c0c840c41c809064003401c3c0c0b0160a4442d8200604546401d0080c49607840c244002c0000d22600c41d40e1a0704580070b52143e95881c00306040c4811004e90703035100284224180700050042e0072140f00c008080560128000395a91118800200584002c00184800629003020840100b944080c82941c1500a40c020081719480b0071104640101090643c4003590040010b41d84d055040c40003004840d019143c0001d4a400388241c013820440f007030f8401d40700040420b0050040c09414803000034954000d003810300c550f00003030f080503040207582c240300030580b0b681c1d0740c94801403042481301329a135943c03000e074614441c44d10012200c0034070080e810a6a110320030303c0019401c1c1c0c3c002c00c916025100e00600030802c054614002c0415076000420280d059500c0c0c0f084942420914060543c08601c00e80b50a1410a04000000d28015103044200300f010007000c0221a05807101d4100b540158101d2070101c50740c0c1d158040f103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 705989001 1250 705987751 705987797
    0x71704030c150204050a091401030809011b050c01080a1a061318090605060319080904112b0603080d020304060207170703030b0105070210031a04140f01050406060f 72
    0x740c0001111000c0c0842d4011550013081526012950380c90480c0d1216810400c8601e08802c08600170790120042c0301060aa0018005024051400300d80359243c5400c100e600001143c01195658000d40b6455665a00078401079400b240c15901001040b0400480820303a40e0400821402030000144070f06943c410001b8082c05480c40c50800c0d14440444001c0750001c0103805415103e0b2464800403038224030b40861100e1482c1d041c6241c4420210070340d01c0d2002c0c030703a00400358141d00c50356440080000b00000d8000d0186405001500c80304c1c07410040322811620721844081041600d00384003030001407681e10503514500c040c2140161280e0300c629041c0002c0c40303000320203842107122581821620400c0001400c2092190f41d0900c0000c410704010364190140d10070003580620302010700c8d040d140c03003a030007109440319101e440f500451010300860101d03801e00b515000711524030410814000301a400d031038014001a2410880a1300d4040024480f402e41201e085c00c010111701055002c03c3d01d072b020 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 705990251 1250 705989001 705989003
    0xc190213020f0d060e042301020d0903020c030709050c0403080304082b0606050403110621270a03171005040204060c030e041a0f01030213120203070e071704030c 71
    0x21035031030035403009600c0e80350042c9009924450400f00017090f280011404580620361002c40200c4052001403141101d0030550031240043d075003803119010312161030045120841c02500540707111580d11040c9070601010b6003204c1c032400d08140c00d010566111204850450383c10412140c0c07a5295032504542a00c1503441c00285444c5a046503405554405002c20b0064004d000801c20300c3d603140c1042d43d0ba4000c038400580b41d044103d4820000b410540010b03e001010309010180c00d072517904d0043c421381d109584d803075219036110b0354080b030103005800b020765995142002801c103d407a80c0c0d03000741001c40074582c54003810f0050020800c0b403000e400d402d10240c10002c10a5403141c6d10f07a40010f140c0044071a042e000a44170760100d2070203040620510507920500300001c00c52850700c1c41840613406100c1e5003641015400c000c591540d651210010003d00402d01900da03c0031040d004041c549022600400030500284049c03150403038110707000c034030b40d03c100c0d116800702681e075407c2c1616480c0400340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 705991501 1250 705990251 705990289
    0x31c110f070806010f0f081c0e040f02130801020304110f180903120a09050703120215090c01020c1903110609060307020724020a080304061503030e010210020c1902 72
    0x1e00401d01c01c8000c98424145d07041c00c040c014030107554109003c80761b5810310881c44590020725006411050903041c0030200c0d80603080c40001d4581d0039010800301d40c034101001900d29400708a09618a08440b0600d0042c12154000d5007581010381b294002078012904c5a1310400359005108034503201d121a081c082025812290102d18000321001d07100c0d2f000b140c0611034000d29000042200d12107100c2d05525603004002440e031242555a114203492034554150150700c20b19410f912888200030b441d80c800d480040143c2001c5160b9400a031802a417a2540c511840b508003e214a21055042c1d5008807900a07119485c100814004500703070748100119940c110400204004c1c42d5034000584400300c841482944490307851068820803000e103801d08900c01a084a080c16012a40107409140c10a0080c440080d004140101072403540e01c2c16481140890040340c085c51356513805111102100000c041d05510303021f0349051007500e0307601803281d00301007040c0c42c02c0510039900c075101c1400a01c80851 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 705992751 1250 705991501 705991513
    0x225081209011b03080f04112e0c0803040b1504050a0209010206070503060a0308031005040e0d08010603060e0103150b060c0a14120a050c0a0506160e031c110f 70
    0x406409020341c02111a40c0c040b42c10203010441d00411640250121501542e40ca0b0550320f03205101c46500030050800d40c1d01131582d1300c4c0408170342e0b200b12070b004156800030810203200c0b807034840256414407080e40200a014800c490003000c501c02004032a48107a02058110983c0da6011010058030148000b0b903030050301d09402c121150181d54010500c18a0036001c071810390b03480680841c3d103131004590140c0c10a030003502c10000220710401640d0090300102602c003100703031654042411a801d100c074100c10f40d070108514800301c1d90002c91040c00f5150340c0c58144020380c00c00500900055062000034000604800c2c14415560540d00404050794010a400d0360390101d048440e40d105201c000c1a6415902071044085400700010f00e2030355118034180090410140310020784a603042040400440d0040c880c545000900510025106050307081c4914010043c60400800e2030040380201c9000307030b001512442c00482090f0040803400c14034502849080c9070320303400c3c030304007210198030540710322a81c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 705994001 1250 705992751 705992773
    0x7080f030f041e150b01020118050102040e090307170a020a02040603060501060e041b1407080c0304060306090e0c0f12060a06080d0c0b04151d0105010305120a022508 73
    0x4984240e01690082e401100c03250700d180d0124100c0b1900c5080140a11110b80c1d07000c41c0303003004d600510903560050000003603000b041d00411150540003441229603960008041c02035410811171290000ca000d0700860500344d041d99411000411050050740c10f580100d0321821315842004485021035026200340001552882c1c510080c0000f0702a8501180c8401d000c1462820548220021784454190094802c0342410081c6c0d062217044444e00f4903c2800c20103c0c0101d4490b000811410744048011070362280703030510080480f551508010030342d604080d40d0500487c400110101c1c25502154911038a01c10100010b6015482c2100e00402d03000b1403082010f5003505600c908101e03880c0200f40c07860782002010441f60f80c0b41c01d080c000d0001000d90089800700b441c11882401c0d42a03c5e003800a01c5484240c010f04a80e00b689030503002d0707230303441d0401032080101c24000d000540305141c00540c10112525030180d22482a07500c80310300756507154840d68010410244000c001c010441c1944d030b0030110 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 705995251 1250 705994001 705994021
    0x51218040e0a0303061208180d08120f07050708180a090c021507030506090708090a080c0f0d090b04050d0f02040501033504120309051230030c07080f03 67
    0x40c840d020340c00b1030b1a20400040846c00740445c404080d61082511f8502a00f11003001502d6082c0221590002c2c044100079001540f6800180240c1c0c0d8410b400c03080c6440c2150218440d590b0007084a010071030148204400150020156020741010380000c100c94440c1c080442c0741000254054800b8905014400e0b925136000700b42c80c1000c41d40300907030301125034608034180d06858080c0e9450360000c491000147c8030610610307000e50010810810368006410036101d1100640159624607202c1e0020180200b030408100403c240014150034007104861174811903a500307000c0c500c0b9444c0030307102d061050320400222002c0518003650040013003105503164140280e5040c4141c1c80f02c00260100c4000c0b808000e600c0100c82a00003c2d542c050b4600317070812a0225520301c40d201b0840c03e10900705004190341d69562403511010724a0350052070b111101c00d00c03035600c162910328100349012140c1c0740403881403034041c02c49038400402c0d030702c01e640d030b0741d16241401c0c0510585914010044000c814802c121403 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 705996501 1250 705995251 705995263
    0x1170a1b0f03050a090809060f120a0c021009080a0c080c0f1c030209030c0d030e1f0f030506100c03090e010b09010f05090a051315080109021c051218040e 68
    0x7155408001941c0d5985202045403d03804001d4540002889050031504c0d01c0401400602440c002080c01c0540000a8902d440d40940c0c041001603110080150b0170f80c1e041002d08a120300b400c00521070320306141c603420500e1198240001c00c0020303030742501d07013405070bc00107c1e10080f050f10112045610f404c80d1250700c96080e0340c880c41c0030180048001041a21078003d40703403a04c40081c00340405034962420003000350442c0b4011001c0c422190000101c613a5140301c103515000c4040501850a04414030043c1055012614036007814504003e1250b59107070303d80350140080e014107080d0340500300c9050130740c1d11000310740c0240c0c0019000c2001041030070090025161680d400e072190480760394246802e03500750150080b541e4114222404c104014680411f400e82d03078482107040002ea801054007000d007401c000382c00c010060381d11178441c003045050055800340040c14481341c080000d02c055986544542c03604500590405c00400e5034080c400d40e42c2c0c507070014104014020440294420780854130b40c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 705997751 1250 705996501 705996527
    0x60301060b0c01152702031005060d1a04091e0302031c0b090c04060e1302090307090218031504150204050406030318090c141b0118060510030201170a1b 67
    0x254424000050342003e0182071402e10020208001d64002c901700d9460003500f0050020f51401d40141b000101515002c0003451204004ca201044d210b40000c82040505408c1031107038011840c0c100500301107415042c200c0303031911300c070002014081481c0c1000c9285000d0152102d07000d40800104401c0d441c2c455005c48007081c0706032070345c1c4065500c422403e07030715004602c20701c00801c10400280d1040d01d441c0d2900014030008070001401c20201401003887c2c003420f500089816a800201d4050541400c010306a001d41c04400400e024840031744801020070b40a000205441004070800c0a29401038040c0c40203880043d00c00c20500b552401e00034404407040703040c4400c0701c860043c0070402c038981d40100540c0148503261010040f11040071b102c0154003440e50b480582c000c0d0314031200d0103603083c018204103c0d00c005140740d8101030de0400c081150f07400b0f00b02c06409604064100b0060340c102c0461038404000e2258180a82d64801c03e000252403042c408d0307a01421208140d00c00543c101c50581c0c512 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 705999001 1250 705997751 705997781
    0xc040918061407121805010221090703020609090c0409020f03040311060f07111f06150e0d02010815041103070e241b0109051b1801030605060301060b0c01 68
    0x104100b91a4100380810586100c030009005450488200b1020780160104122034402401c0f8440c3c280c542d130f17089030800611614082502da1007808a6004104545d130080e8845024110007465913000541d50711480c0250b5024042e46800078100d60400000e4900410a51a003507599044495004134a0350048408502084900c8030040605000240c1d07903102d000003030340c420119102c030082174592000780c1c05c20207001e2080c8036402000c0c00c00086500c0c8010310b5080c3c0441c0e05414540205440b40044c0700c0c80003080640301840c1099030fa0840104645902070902ca2040e88a42c0f0180c0303040400e1226054100d803c0801d440b4441311000001c3d4401c0941c2d5032001e02a107903950130092020104119407244441c0e001c1c0600440031480001c2400e0407000c01041c5281904400f0a400d4036a00c003010340305500408044000c040381c1c114000c54520301180d0715481c0c0e001582c04810352180600020b4401d82c2c3d80c01c0082c11030b4a00b54014809440080b1249498800c1441811f010b80440401e046031 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 706000251 1250 705999001 705999011
    0xa120503010608130f020609040216060614010c0c06080712021207110c0f120304030b01030b040b01170a0303090201090812030907090504050318010e060f07030e010206010803070b0c04091806 84
    0x91181305005110220340c2c05014010b101c881502080304940212060303d5110360300b00940d88401c2c1c14046400c0b0282c0c030818003c61080d2921040f0403511070704040c550706101c007104240000940074121542901c0090401c102c1c15155803d0480d0304110309240c0d811424400145088103c3c0389003806845a03060382c0e1402d0391207920420554a5844042c010703500b10040c1712280400340b5121b031074001116101d00032a400c2c980d036501d0f40c045c802020707802910004090750500051204030388402d409801c2c000c00740d40c01c0090b050f5aaa0b1b0b6481c000f40302030308060381c0d003070304104580c41412000010440203048501070914400c41c11410b600540d84244180300b0031034001100c45407030003198881c907000400786051100342d0003842035a5100c004c40314108580c04041c010a0340c0c5a0002d0710714003030001181521444c1d00e28001d801e5003151442d03241950701801c0100103450001040740c51096010242900716110b060501240c4d0103242c00007049103003064501905200d40d032421008103030190900303101c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 706001501 1250 706000251 706000261
    0x4061401080f0d082e03060b030d092d0b0903010e01230c190503071d0f131805010b03100209060d0209060c0f010e24180a120503010608 60
    0x150b02c054442100001e50040c03c60300780d4442c0070f0708a107a03010b0741006512440c00022990510207510290f55840c0c214100e007001c2c010f2000511400ba4051815002480203c0000305c011f01858501d05c5144094154014884003a940c1c0d489000c1d1100d0002105404460315800103040541000d1800d6001e9860900f0341114104140240b500440701c80d0441071681a94090700201c13014003c015016070a810843c4140b040744441151411003825a191a00d90030f155400504c0a440c2100040035000c0600a141440e03484d2014242003e804407400f85d40b03c8280d050720b5003e0141c640c1c4c41d103038029408a95406000040d0810100031a045007035070424003011424801301e0099111164200c48144644041d80f1a2079001f00007040c4014980e0741402181404075250040545030030710a43d448044120904008105511459500d800c03079071105400e1020006100f94020042c5003544403014811082500c20300043c45255000425113005082d07040b405842d0384d20a2090030000341da000f0003d4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 706002751 1250 706001501 706001503
    0x180f09040b0712140f04020d0b0703051b0a0e0108130b090d0207080613020f0a0509100302090601030209061804200408060106050414090a0222091107150c020a08030406140108 77
    0x10b2043c034861030004c0081d4540140304168558001c0040b60008103204817100401d0360140164480c4c0519540807800b0b2418139010109c1d030344e40c4c0000c024998010b0000c22149608220172200c244000e10780240e299441d40c5070840d80b940c0c55034015020f901c003070040c0242243c0100307010701e403100c06800b00c41c0801c1d0703209466035032103800300c9524120402030500d00700140303004034007040407807802401245046e440300c0000d400b000c01519130401c0034140000800442c1014030780250b11a509090460620300400007203806440b5008003844581c0ba84c107030b03405140d5125402210500d2148045140001240d103004a080d4050700030050300e4800d000000903d075125900f05c1d026103021366008110342c0318200501001c600c000c2c11081805400b4008904250307030a4501c0c0501c8200120346079996490008160304448c0e85035528010b0748030401204c4003140c000000512000110702c00024108040c000c00c0781042d0b082400104100740000a02c01800f100380c1009407040d03190000c414207a40d031000702c1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 706004001 1250 706002751 706002761
    0x3060e0c0603040c12150f0228050715230a05061c231c0806040921171302040b120d14040306150806070311180f09040b0712 55
    0xc00c2039413862414440d011082940080885c40b40070007407640410400b4504c15164410744d811130707a55002c10602c3c1c3e04506540c080c1038040c10b0415015443c0c002c018010101e21500c00301811101d680450140c803640280e004849685885280c10a0810740750007000c0070001c1030301c81070807160034907000c01e01a15101d0215101d4002454881c3c0107103849a5a0303910407000380c40c018444164802c02817003112014001807a10b5808100c5654010284480c090400c0f02c0240c0740b107015624042c280c0d40040d101c3e99410341c00d8466092507460030307040c44200302c0302000446840c0c1d014600200a2044005181c80c010000130b1085900f48005141c0da4140503401d03103440b8486030260b200c07503034542d01c09000d51560002290019226854113850351580c1060b116020810340250080c0e40d0100010482407280035000300c6076240c240040d51280c1a0101c4c42d001b4011801c00120103800d02030f10359580c00c2c02010001d000500307540924505401c150451704401c4030590041217580c0d0b4070055840c0a03100e2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 706005251 1250 706004001 706004003
    0x503010f061d0f0103021509030714040e01110708160f210305150f0111031201060906020706090b0a1b050109020102012409051b030108030c0c04110d090c0f03060e0c060304 76
    0x100382c0d56a20b503401f0450b5044401c1c803407818100c1c0030001c0000341e8a080c0058005007000e0b540c40313074107034007013200703100803103406400d448a6a450000d0920801d4283d60844490580103011261145c04400510003c44a01140240044401c105280c10462440d00008241c0e0340c2c500001141c241c040c10a0302510b0080f5414560300310203080300c1070207180c0400003406001043c03400d4282440d4540d500340c990380c0410880c2101181a50040115030b03070100416001d003886201401d032042c503244020300540700ba801031000d1964045000084244100c1e141c047c0f0440601e460a8801128107000340200754000b400d90065080c080c501c409003151156100303849400009280c50030f4034240c2980c00411011304800b514240e80305000a000c603100c80514040d102c004065951844075a00d001e240592a20b41c60340924200014501561240c4003030300c0144007460801f007031825141c60111460030041c0c00c1403030102d1080b6804018029154400c03c0b0190b140310480f0170800d895000c104045c04201e074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 706006501 1250 706005251 706005271
    0x210c02070f05060a11010e10090c0609050d080d200c01292b05030307020606030c06030a1e060b120a020702101115130b0f07120b01090503010f061d 65
    0x210b07069841500c41c1c0003616180e030300000d1981d03100350307000703050104489048d10081c1c0c0b52000b8038284000501b2080040ca11030401c0081949040c0204000f4801c00101030012140441c02e544d14104036080907602e00203540e102040c00ca41000a003449802010000e0303465841e00c41505180c42c04001c0300d14a901c82c0d00095214980040c0070050310981010760441100d00c01c03482c0b80203008000a41d54004c5108030007640d281d20381300a0080c90488000c2001d4400e5000d4003405e04a82c464404480c0c22200450000c10b1001309029101e4014045503030b048119440e1107070003d1402c0110014040c80d0840746414a0540c42c0c480b00007043c0d000c0d900002c4d600013000c9524100b024001d0342c000d5040c0038400282c484d03040c580c0382940c00c0b002003200e60400030701100007904200240902c500c0d92010010f481141d0900302640010300583c01408402c168582e10024504a0780c003406a090003040d00400a001030b1400714201c2026050300d1280c1c200c1e02c00210704400b40c1c400304a10f164440c0a80ca0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 706007751 1250 706006501 706006507
    0x605090105120304050607032703120804020f090109061508010503030a1b0b0a021818041101020a05060405010b2b08031009050703050402030c0a0501170403210c02070f0506 76
    0x400300000754090341815002ea11082000040544481018001c1c003030090726544c0c626954483d840894100130381d034412003421072400c00e100003095855105078000360342c500100c1e1551184085403505203c024496480103018000140d500c10541080003920300011901caa44d202c048400e481ca65400e0180e150326401c1400007908a501c1079100c40030011200d0442101450580c0751803030b00c4070003529695161a00021410b8607075035842016000c150040e42d00c4140300c60b07204170040d07845801400080800c4400d21280c0042d80c401c000c4803800c40c1d040000c0d64003a0620b4542a40242180c200d130500501c006015042e0382c01c0c0000714981900036442c8015400c108075611001154030007450036018901c0e400b0082203049141c880c00d031280145031000581c0e0704144c0101443c00e200070420911031100101c0901450764001010010a1080e108101080d21170b441c00380e85041045608210010030440398842150864011307440000040c0c00390341c502d586500d41031619400d203004494102e4010 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 706009001 1250 706007751 706007759
    0x6040c061d0d032007030b010e042f03030c07080d0e01020318010201270201031103150405090c0301051f1a040b09030c060a0f0e180622092406050901 66
    0x180b0010307a002d032003440c100d0101c011101c0300c000c4050608016500c103504c042e50a10401400c504043c3c0544218407569109280c41c4e901d02c2e081c00f903a524600b810510301b14040e2001c02861800d00034101c1c008040e0794503061030a10481d07031070303510b0322845004e031288004000e850790043c0040b8418100c1030f809185042000307130300000e190b461900c00904540da1550380140003d80c1c0c589108164411100da2030744240507000050a50304910390414103018100144040d0850b60001d40b8203200d0256004986c6903102130b80345090903942015560503500341401c00c1078007140c02c4160b2400c14109400f45400740c0e283e100c180340328030301c1d440d42100c507440400c000d100040204025020019000f8101c2d2401042c0070017040e80360300a9416a0301158450f44000907494115984d0050284150b030450280520328444500215000e0b000380c0c0152007605a01e00315031441c110600d50f10f0721122041c0f008880501d0980e01c031090802d031480d540144840c41c030364030407120b000f000200c5070014540c0308140d00b4 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 706010251 1250 706009001 706009009
    0xc071703071b080d08010806250e03190b060913020d021c050703060e0f0a050c150d1509110a020d05030702032701140c071a041706040c061d 62
    0x41d48011a9107a210000001e8800040000360809807040d07071905e5486d4074000140b41380400c054514250031840202c411000c0406a14210b0f1070501481c0c12441c4003140d00c0400d0070304080e954030754501800b600000c1d00344940360070301c2e0340101800e8612503500e070340b1141c0c5429065050034000f94010103500c91036000d403400c14000300002c810700071000500c00b000e50f02c881c075000e00356004440749a2120852000c108083c018000d1000481c070140519596a948283d00e8031001c2c44036510076070f40c450380031502c0070307000f070580760751480740320041255400d01c164260550549105000c101810002c1407880c0055440550b44041d486030002d10039804070000984803600018510b00c1144400c1c815100301c0202c040a00c8410300e01a1240500003440900040a1304021105e80d5040c0a0030003032105c0455002940074126008180c1108000f820b802c942861131140f60300c50300c0c2031010500310192600021880c503008910480c00c040341c0c01c1d03981c8000c0c0d80e05844e40c8281120804030040800d0a828 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 706011501 1250 706010251 706010273
    0xc062604060b0415060306050d03080c250b0115050f030403110c180108060c030c041418012d0b0a051b070b07050d17060f1201020d020c07170307 64
    0xc4111004102e4040c0100810115059600510304a9110a904100301038040c0f00320800303480b042c4e400c144410000c0d117000d00501c10107407080d291214005120007100c0d5502248800102240240700344007000d900740100300250070300030000c8035803030034540d204014018403c513a0b4078a100c1e41041c2c15030340c9948080d590b00d0b010304a988524050002520780d07982c0c420040e81d902d00c881d142c61166550406c9149403034254000e0007400500780c01c20a0000f8035840c035042c0d4003150002d07003c0010f415103071800318110301140c0000c100070040380381c004142d0039102c4a240c1c2a110017188086d003503264042048241e6030961141c625544c20800030207800c58400c9006107900c151001505c92204040400d05140070b00c035500c0882da00101050403400c01505002078800e24580d80307804040000b40c820000440ba8000d0551132054540c4a15a2038075160400c1e820038070018100219140c0417140e01c240060f600c5006144580c0c001c450002c00d50b040d580c00e4102c101201d040c002e60420000d42e0b81c030300703c6e48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 706012751 1250 706011501 706011503
    0x318010509010320070519051c0203090907050a030f110f09060c03030403030b1e10050d1401080d0e12071406130b07110d0314031e010b070c062604 65
    0x584a020007000980c138008409124030003a19000d5480d0024144541092040c15030b18921400059244000c6500016041d102a511260911035215455001d918512404003829006641c01c010030007000d40020190000c201c0c95101840f0119198150740201d070300440800311480c03028401403214500f0040a05212180581814540302c0f0a003069451908102c1c0e040700001e4580c0b0047c440350400c0c1c0c4142800020107001c10000704210307800100c02c2030032100d0300000c119001c50010041c5150350400446081c0700810440c81356103403000140c449803494100000725070720300301d200f210b07052840c00703018541d20141c05010080d041c12440e0038041c5d402020540e02c5241442100380c2c0f8200f0740d66020050022107049907481c50907141c44121003840b1150584a4200010f058012940110910344c051a4011010b640c80d034628015090b041041101007282003201e100101d10a0030810082034134a0050200a044d50ba880d58200c8050300501100d2004000455641c0b0001e0140207040c0d4100d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 706014001 1250 706012751 706012757
    0x702010906020711030c0108130609061e05100b04060e130b0603010902090103060b0c1908040801060303080103060f060b0415031b08100b0a050901050d09050601031a09031801050901 80
    0x1168079190103090b40c0121809980c07080703075000220418541040100034600302070034120401e2070824142c0c0d8800706000710180605466101390410011035501c000700350f01040c1d40c000e02c00000307900e0b000020101100c0100180f0495440400c01540e0b8000f0342c1c0c1100c80790781d51a250425001f043c00070880c612540c10651075120809030f4415590760010b18080c000c440e07801a29401c40234001015141258051040c5000400c404070302c2420101d2030041601102e161801c4200e40d40c80d03c03a0041c4945c0e0b1210440b546041d0b0080304040d0310034a4141203d01070790060018889114030300c1d0841c0c3e070f684958401c01c842008108503500d090540c1e4110030b00942400280e1020716801c82c500c3c0a0481040740c005011502000054240e0a4041d00603010241d0600e04100000b54080d01c0b070702c50948494140000428a001f401d00160010800300394803000b59012940d4070301e081c00c80d6034104024545068000f5000842e08000007042c0ea00003203416a2200c100c024940c015945540008001410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 706015251 1250 706014001 706014011
    0x1728020103150e3112050318010e0f0f010b1023040f0512010e030412080702030a0308160206090303010504020c0c091807090b3109030306031e1208070201 68
    0x4550385862003d12131000500058000b01808032004014400f40609080740c803110f21108001c03c240d50502e018108240c103201e5642d40310301c0350010035400581d0070320060f58244070786048411030100300002603102c03441c00c03204100400d50540d4281e403032114076145c019103e541c288131441d110301000744d80301104620307140a58410a201101c15800744e013100a595810743c0081005042100310040b01c162054000c004900c1803602076a1a48510712070400c00b0b02c480300c0700c4803d00244404440d20306a0090440b2000d02c003d00c0c02410000046a0f107500715a03c422075403110700c0c000302e046841a00300c400507520b140c2c00c08007000000e41110280ba0003a100d803059150803601c800c2116401403205608041442004031090303803804020380c010400c01400d00c440c030080754540850361f4081c0042c0c2101c82c02c144c0a0440b8540c00d481c1445992188a07080010b410181605540b2103415030740990f00240c1c6189a0a8041003202d850030801080e103040c50a14000c182d1107030388655000302c2984008a0303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 706016501 1250 706015251 706015259
    0x1106071406090606090f07080117010204050a0e1b03090d03090606051915170112050309090a02040e1b0a0807140a08100602010b0d0609030509040204172802010315 72
    0x1c601401141c8808090303000106108280c5851042d55a10540c5c04c24500c6003440e14000040031084180304481c0101c02d001c04041c1c2c41c56007034043da8040c04005e00381c640d80c19601c14141d16046c8054a4540c0c50741c3c04541c2103c460000301080701e21941091000b404070361032228080300240345d81d40d41a122281d0382d51010a8564642d0140754003010320b5040c44030f42c0360038500840710f221480c0ca400c1e070034002400345640c642c5402c50b1032a03046070401155042514007030300701542944904a845036005840700700f000300c038040a038054001c0d5140c141c64030300c4595a1800c80d1b1401a05000511100c010511a00780c00d188910100c552028682ca08100300300e81180701e01403a07401844005010803032080812640304402c01416005010a10084c0302e80d85464020541810203250040c0080da1107840c41c806060280048034800e4101610841d42d85a5840207503a01c914004000911400745038003c6c2c82e58411540440c5a10b01c1c2c40c00c00c280c048005600542c010701c90040032841c041e8407110005 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 706017751 1250 706016501 706016503
    0x90e041203020d06060e030c0118030809150a180b0901050414130615120b0607030f21090201020d0831020d05030705070b03100b0c0309031b0406060c11060714 70
    0xc00240300317944982d007468103440101810b040307145045504120003410010007200180304070340c044030b03000020b881d5612a4400420305500c8a845000c4030808001070300c8810b16070103042c6200d030f92040100014500d4640e0004886446401d10031400180140800c1c484550309100031200031800802d213911a100301150501960f02d181e10198210a00c460f0b00c099085e00708400301d85c00c1200d00c0c1c0c1001085582c000007030441c0218079003e030800000c1c81010a00501642550a480d01039000a2007013140d80080f04001d800c0c1003004900500401100030007071070142c61050b000389002c0b102c2d0100b1055418078005144e9002e001d05410402500b111000f43c1c80c0c090104d5042c5025502641d5240b010781445454288203170302803c0d0280c0d0400c2008480a1054051826541c28000140c2d0b2000707a29506072071406005c00d101d0b454010314840340404a20800001d6180300d06031014441c4907951007041c0c0781ea11400d01c0207840f803668401e50102918003400100a030340c0c490030380050624918151a = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 706019001 1250 706017751 706017761
    0x7050601180b061306080705040e01080c01110c0d110d0215030a0605030703150504020a08100c0f0f050d0507021e010212060f0303091516050c0a06090e041203020d 72
    0x4140d03240001038a040700549180503080614000340c88103444e142614400302d038141d24a2245004004c0b111000c99071031840354084038014805d03408030880c2075868a25080d1152026810a800306610405d952000340e40400c0040803e107008000b03244040480c1c50f07110f5640381c50007000c1e92241501101100681e1020a115000b841e030715102c40e16840c080034054111030050304801e01c2503000000030400504080240b600410400302c012500e5100c0d4808241e071060650400c0055001d034440084185980d0382c4400400e0601d681c0c0c3c2e00c08494480b2054900103142085400000c02c00c12513000041c80c2a0041604644039104070385014141a1002c15107001c809496501a5000594102002249003c01340c009004440000d00801c46c00006503403441206802c0c2d001c4c400340c0090914068466060700c04100c00b0351590701c4545c1c102c2c03401e00d8441200c003400320301c1041c0002c40400d10b14441c2c0f020300300383c40032102e104c4080d85131525217060391801c203010380040580802140c44400300e00c0c098 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 706020251 1250 706019001 706019009
    0x7050f0c03190c150207230d1e0c02011412090a06050105010513090903020c060d020a08460f0219141b191209060807020d05030c07050601 61
    0x146855103140084415001101e80100302007003d091100804200740400a00e80b4481c0e0b80b800683d030300c0c068540040001c1c4000701d59816030080f00d034078140903400440e485a0400b0180e0b02d03850b194480301c1d4000c9030b070710049610100044070031980708015402200c40030082440e4000d85410210402e00130341c40e1100c00c507100345550304403d411200304101d5014103405003009090840c1014120340b183d40781031b0000e201d010402920381c00300c002450300900481c11820000707030146d60350b61070781400c44000e0b5000000000001e0f040c0d10000f1000d0400c1c0d1748445260b600c051803504040d10342d1030b03103241601c500d141c2d6001e082000c1c1e00034291003142e0710525080210041c0d0144c0c44003c040401580ca030812807205c01401442030602c0d0600c0d150204569150040c803514090f50011040e20703e24000310386d00e91751070841d604461141800346104101d0780d030101d03540e00d0612040d207440c4112282681900d448015a10650303c080d0a14000d8002c1c651055510800c42c1c00e01440b0f813141488c00b0302c280c0c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 706021501 1250 706020251 706020253
    0x1106100501050c03481c110a060e0f01061a0912060a0618021603050f090909010506090903120403084c030201270302101d090f0f07050f0c 61
    0xc1c00b85904400300c1c5128140c0c1440c1c41c04074080c44000c0c12000c0d2104015406005070480c2ca080310061903000c0c03201d220f211f143c1081122800b0440d468444010180d0060b0104a440f03104455441c00005005030b00503580300041e00030b084090004d9400310354008503445c03a400048418001c03030911080025910401071a000450540d20781b1424640c2000c0066400b070155004105843c0245404502610115411301d8102c2c1c1e100c1c00c0088500c2c03140201082154807210314802e2201c4036905401075402644100c0e450400d41d1104240c050740d901c52901d0340302c3d00c40f01a00c00940840e024022482c1d1101080b18501e40560042080a1024007038401042101c1c21200804144000b50415101c9091001e035104c0718540c1550001b800c51041301200710381c0086145003015690010080150003181c1c0079007400c0180083c5ca00107007000038018030070f0380308030300e140760062032403810364034450007990700140480c90f0307407541d40400d0b0910000034805d50138804100110045511441c00400310541860 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 706022751 1250 706021501 706021567
    0x1911120f0421020d0b31021009051507380406110705010504050c0303040812034218010302102a050709020a0512040c180506011106100501050c03 64
    0x403030240d01402200c451b485a415072600c1b0720941130325000c5c48035440750100c420004905604a0480c2d50490503000145c001030b9a045103161494007001030180188100d40d460445452180c09040c01e24a000300b44d072640686004024400341040e03103d942040c0541c1020440000d40005d07000b6540c490346088409a40d44c1c410041801010b01c056030300c522040300a14605843c0c4403ca070f40e00d40341c07000381140c01d18001010a80c01e9104506994480d05071002011503c5184000c41980b01c0000900f80945c0260401c0e4070b10520340307a012020b1170b2000303070710501c1c1b0f42c0d00b10303024092214a60014039003400080c50326419140c1201c04503007160304e0042c111003603500342454501c0c100410340d03108604c00c2e40140456100c098002c41910000c0c2d5404204401564450511404030501e980c01403122104420311003141a4180d00310a03c9100b081e219111210950320141d03903600c1040716038000c84a6000e5081c06150710450081c040c00d240c090849040c80703021041d40100c0740000300c400c000a0000703 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 706024001 1250 706022751 706022761
    0x1c021c0501140f19090c03030503010e0a0204080312041a0a0501090f090b0105100c080f0a1e0e04051918020306070503040f0f06021911120f0421020d0b 67
    0x9004411480c1c20000481e04541449145583d2100001d00004224281118000142070703007a80001085500700078a103112564074140030707149501c01e01078103d01e188008005006012280215000c664201d0011441c03c1d0701015480344d1b4001c080c104039025075600031803c503881409001c26000d031351644400600d0394900102c2c0c41c200e503400e42a101e0010f00f0024001c0c0030038018600c05045610650f2800076651144104498205e03045100402507400400d0f03002004d100311002c0e02900c0038603281c50160f080291441003801140f4680303000011001e158051150078150859a040a100141d00440180c0191000d0030741d0419001e01141c0280d07840c0400c190302d41008019002019800c0c1070b440c50070030740c50b00c0d21100c1d8081720242250800d4040f02007040010f41c12542803400d081c0d010b100c400040e80c00200311746014040200c040c80b500b508000040401c0084500c031840e0160154549807a00400800d0200c1101070220000517540d8442d016858103011103000c64403035080d4080910705 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 706025251 1250 706024001 706024003
    0x1303050d09140609150c07020315100501031d210c0304090b030610050a03030309050a02130515100207050f030f0d0f03150e07080421052d04051c021c05 67
    0x4001c00c000701360380c4500740130f0003124800910f158200c41c1d4204a2070f65440301c0e001082c582594003000350143c1c00e03800c0c1081018030000c0322810a480c800d03a0b0a000d1084800b80498030030520500e400381d503400c01040b40c01d02d000001003449244140c4c00a00f402d0852800324581940c00c158052401d05485000082c110f15050100540c00003590180002e46420140802c504e5503d42c040101031550b43c02e00c80040c0401000a1031714a0390090003c4003d0607048402405400300362008010114140340614840c50450450340a070000d90b40108140d900d4002000076405c0211701c100c5d0180900c9500a07c071610038010041002003c0e105c0403003030310032103c00804039010504102000c0c0003411062000c100031200c015000b4102c3c1c9040115511141030040ca90146114944000c44d1050041003505d0b030884040c0000c40600042442d1400b284840804e0640c071701c884081d010700d410001070100307103042c0c403801011801003107201e041e45080d54049810f052400341c8134509a10103118160400030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 706026501 1250 706025251 706025263
    0x609030b060303040f03080307090b1602040c140a1b0501110a09060e0a121506062313030b04080705010f0b0f100903021e040f020919030b1303050d0914 67
    0x1206070003d600e054580f0700902803203580340c00000c1440c1000404180d0350713031043c0301d180044d000e481043c60307540088408000e0400c0c174001040b800ba40c100520b07038a20318003a000d08000c0d03406a440c00c0d0b1802100d90303411111400c3d010042180741824020450201e1803d204081900000d03040465941c9040480a00091070641c4000b0400101d0318040700340c2d0711a00081000c0340c00104080404840700e04c0c10091420b40c03980b034910b5003482c2c2500002c8085d40042c200401c5c60006c101c203007030038510b004e862005100e42c00e2040100b41c803e4104000090350b43e0055070340f2900038001182408081c0d038403c0d003994420411144c03e59250074001000f0700d0542d440015840c030444a25003034018004002d00a1354031440040d20600400907000c6000d0040c0107141903426000704100969180500050025003111030001c0c00b442d089640413600112100c5208103403030f00148003c00e5652460030000440d000f043e41142088030500103a28140c102d4010206424031811500800c0c00102240c00d01e082c1c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 706027751 1250 706026501 706026511
    0xa14011d0d0210020f0c0a03031509020f1e0705160513090b1302130905150906010b0f0705010f23071404061103090913050d03050f060111160609030b 66
    0x1411040d4507410490300090450000007001102603290394080f032007402035024011136515180541240c210030558150312148141441004902c2d41d280c51b410088105d004040180003400400c01100a15503804149041c0da00c5504200c0ca00e031054998a80e4104488103100307045100d0030b0b500c1070100d0310b0880c042082240a1510401811840751903c1690410140000596505d0200e0b103200359140c00c00700840301e0300d219005008401280c036040780d54034019006201000d0001c1d0201d1613150011403e00e0407a8200d110003414050080381c05040c2d40d220940c100c455640e038200d600414841c6001c0c0030045a122100502404101000b80000c40c800400f10302c104a68409078800c045500d8065500341c41661078030084c00c10104440600e14400c0c1d140c0103502102c8030003000341c80715808004881c101e01c03030800e944000320949416820b0b00c0b803c2d64048052618000014815446400d01100341e0011034221540c20355209e41c05c0343c00d40600e070000000640899010f00a009040381425004 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 706029001 1250 706027751 706027753
    0x503010510090b0d0c080706030f020c0c0108100905010f050301050601031401060f09030c0b0a11010b01080a0504060f050103112d1216090204180203041110020a14011d 74
    0x35290094884460000c9400341c0341c0d141e5603502a65203141c8a5000c040880b07a4419800c61000c0d460701003040c0e031600c0c1441900006401c00d003404031368451701e00940d400f0645150040514000c01401554004802000020b090781c0007440092500c819024032802030501c011a492254109020700d42507030001040f01d4145803c0440e94040c0c20300302100310341140d04910b002440d06582e40000c840c22805030b80058500c1d010980040792800c0e1490041c4007000c2980c0368202d03407a030100041401e0f00e41d01c450b4203000c00c204900007200e00b18150002a48584544c00000300145114546405c440c420f0f0070030f941d8150f90f00d030709200604240b10916182c6214450100107081218480441c510303404800500800d41c41e101780d407070b01b8010415020340071000ca24046400e5240c0031944025042441031482c002241608a001800e5920849000726001148485184555000c1c400c0a038008060070045124102c1b001d008520305644d40d041003c0d1400c00030a050f1900c09403100e404100083c000e4803 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 706030251 1250 706029001 706029011
    0x120207081801051602061b0f070e061002100902040912020601050a1e0311010504050d14072106110f0f09030d0e09040b0402031903020102070c0b030c0d0b040204240207050301 77
    0x2920031030301e02c0540c045a044030b486075910007001c049a400125070b010400c9600c5840808000d80d580409c010041da03c0800c00b84055030b54406c200a0028242103410015030059001d0304131040b601d800c0040c10a002800c04158007900307076505032000406080b41d10060300440c00510491230110030f07400042100200c2d107400601c01031940a071001d150310004180d0380e14680b907500785d43d0050f81518010400104240003030034150030140c0d00c01d144280c101c1c1d0b05005080011584150440540d100030300b400108443e0380d945e65a0380c0008080f020036100d0036000138088140170181080c010459098544c00003030b1120140c00030306180030490b548034030600c24079035290146916001d04403a03000760003481525007610744e0b001081c148030680100034880c84140d000170082c03540540040901c684105017140540340c2d6040b4103441760000380e4106030568810414681c562000c1d800c8000181c40007000146015507034148207841c070760520704148104d104200d480402a4051024034010042a002800b03 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 706031501 1250 706030251 706030267
    0x1b041503050903130b0d0621062f0304020a03080f04050315010819150513110f010203091201060b031005100318200405070306090b03070b180112020708180105 70
    0x20030f04e84500444064500100d0241d2003c4e100381c0085009003586816003000d80ca0340c180340c1d4081000340b41c00b40d0302c030350400c0c0301c1d049200011320380c0340b824262015042525055015400384150b01c041c2042ea0f0207103520b01c0100106807000000d1992410010185a80d1480c0501b41030a100c072703846d00c0e511442e00100041164210201d1401c010207403081007101c85e07010034a4141d45503807042e521490090325004c10004405000310002000c035000781031400d0100040410040f240155007850390042c0c009100d40807a9040982c041000c0c401d1810011038001d8807002c800c1110382048841c4d0300e140c08000c0c002c000e40d0400e90f240c002503072458a41801400038581c010500100c4e103c2000b040f25412201c0c3c0c10308400f60354841c00301200300800c2403026080241000380a09010f00540c0c407090303e0b0122403001c1c0e00d00000c0d01802c442e00204513900340b45611004800c1c40400c000101d0621516810701c1c055010244024160301e80700d1034145448101c4102c1e0303840c61240d402d02050500c041000604 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 706032751 1250 706031501 706031527
    0x101e09080405091003060e0109110301150b090d020d0503120c040b0a26180c06040e0a02030a15120c050103060503031801030f09050c040c0c1203051b041503050903 72
    0x81c00395082550140e20589440000c019031214603440036040702e182021400005c10190890311415000c1c8140855442d40201050708030f800c1c10312412a0f11442c0d150400c08484030402420304c1c0d0710010300001c4002810b4002c212103149521084440f030300005918580d030305048280e140c00c00140c4640c14101030408060001521074401e41005101d07008120030022900354031410000010700d950306005052069080207551148207060455025213010b1581d103007003410665040326080c2202c03c00c5070f250500d641009500207031008500b1901c2d02e48a054902c1c2d40001c00b8020a105602214407420f5410207040f07850068010314101070808030104450342e00081510040f100031120491040110b00040c3c00a140c00955031201600308941b11080c02401301e0740403450380080d14140017007511920301302d520010346a001070021104c004200c100a11036404280e02030120983c5c10002c3d51403941d010003035041039005020141c0c80800e403500090f81401000d411418840042d4241a1140004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 706034001 1250 706032751 706032757
    0x5181909051906020f0a0e010e06090f090405010b271e0408030702150721020915070807020306040f02120f030406050d0b12010203010617040b0601050706090203101e0908 75
    0x94520b82001c40060000d00c20940e04440c82c0c40701955031641e03036418004010700a1040c3d04603090108000c0e203e00d28083c1400303022102c0e00b03040244014103410f06034080151081005e00259000c0d9070b900344041803602c0e4015066041c070150b00c04449400c90440c600c0854480090035081c3d09654034965100d11201000040e80196224a14a880c0c3d9601c481c2240752001d10340c81c25207501d5910742031248140d04100d1685450701692113004040c43c0c242010016840798174042030b089039440c0b070400c911000282c0900b95844c4148030007441c20035190002441c2c440156419600030190f00310308411448c010b000028008a041d000d000b41c8910013201c10b8a0b80a0f500c0b0344401c1c407a001030211a4609558080105100001d00d480f1034480007240c082e00030b4009010700f40c00320300004003400b94250b4032610725100b541d02c02009542580c0e0000116920703042808102c88068942c8443c000503981440401c0080b907000500051000112440364401d081008070525120f240108182c04640f4441c11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 706035251 1250 706034001 706034023
    0x140403030c1b0b09070b040e0103110d06090b0a0c360e040b070e0a08030f1c140714070201081501090806150415051c03090518190905 59
    0x800201c4021026040d00c51401401e022001403403100c5146040100d030082c224040c410000460304540d4075140d4801c907600c03e030f000350039407683c090300100b000400110345060341d1440602001c1380c038a803a54480b020783c0d9030b0702c80449005658070100b090150082c8174080c2800700600e084d1107404206441d5010b03a10107454143e41c1961184080f0311403008401d000da000709088900c82c88240382c40e003003403425041c0540e0303150002500c9000b9501185490050501130704c8826025500c5d0042244800c4901e62145414801240a001000595034030382c0c4512114070b0b5180c143c145451514440050074011111068000039605000800150341d20841140e4130400082c4401d40a07080c41006803080320142d407010005104040400885801d4141190030a81c01920180102c0c0300f4100d0840c00c01d100e60040540100740d1003104030030021200703107034001c2c58028181082d0054480d0701040c0019801d8205c2e190f000413000c1031220711001204000d500c00c0007414204001145980d03581c0c0c0310095511 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 706036501 1250 706035251 706035257
    0xf0109050918010219080402041a01050d020d06050a03060209011103040617041112030408011802010518130e0d1d060a0f02030c0604060b030d02010e2a1c0b0a140403 73
    0x506012070b200254125000c1d000318440b240700ba0502c210008140c141d0480313040b406a402c0c519417840b000c012240d07071a14020144c581a003000b107201e100c00c000b0f402004440302d5280d111500001c0e180c8034048480040e601850b009659400c1500014114a90316400c0e8844c903072040204000403a8403c04010318160380c203a03020300a4580c1c1c1040c200398135854440d10740c0310b0283d01c18888100f10000040c012200b50703100a001d9501d05038907818420043ca00040d01044e4204100e006140ea5056450750030000100b01d4445040101280b2040301c20340740b130501c80b9a11041d4500d21241c0c2000003000950820320f05801d900c3c20b2a404110070780903400224060203480080350040d18002c0c825640544090f00440c0c80c40d2906090040140030141c010310300078010000c0d01e50700148180070b44072030060003000803d01e2101802e040b034120740d08440080c07400641c0f000c442250b40c0d1600c03c2c1c5107224000040b542d038581640d00f005e041010011704041c00c0c540c42d00524020f000507450100f0750046d0141 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 706037751 1250 706036501 706036531
    0x1104061d1e010210020406090807090504020f0907360807081207080706020705030d0b030d270b07060b0102190302060103020415030b04060606110102090f061b0f0604020f01090509 79
    0x70041c1d14284152903480350083c00445c012400035404030030345040341c034004111105259210640c02c02c64105035800781d0003071400100c0324030320f00f404181c0a410244626060929a10130040d04060307800d603440841110b000756905c0040c0070307102c0030090302a00d2000d000e402e02c40d140040c1613540e2409419000d4100c440820b919043c88030f803406482c0c4441d0002801e65440c480c91420540300d40c007113070a507041d6a15042000c0c6040c240080c0c03600d0070708801e440301045040c03000c548801c10071000803050141e803101030002c9181d015800150007a00d2203000c012407100f00803000641080b01c490040701c407600b550090000400c4d4001902c604480d0165000120304209408e035441084158001074071495103182030200b08410b5910100c2211800c0d0390390404110040c0c05a4240c2c8034001f0f016a100d9080300c1c0e00c240c5032404400906460030390890000e02c900c0030178107190801513000d00301512500648100b10550419180d07401c04102c00f444c111506600744400100754050241c0302401c0071000d6 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 706039001 1250 706037751 706037809
    0x50d030201110307050c0138030102090618041a01020a0305130f03050a11090603151305010509061504050708130f05030f0a090504060503120d0f1104061d 68
    0x390300500c00d502e0030205480d920710303140d100644554004c110030111986010f000d0114402920b80f01b02202c4a414a1640610f611441104090716410455a80f45d5400c2021801c0f41d07079144020b04c5442e08100c6203d0b00140d511041008440220b9000c045000c46240100004daa0202c1c0604401c2e6160801e540c80d5451900304039001c1c07880780c00034500c400115102200f8800002410700a942c0b003214a03c8003074005409014002c0015120306404d40e00800c0c0c9048407129610540340c0c4040800300542082440d0340f0341d2425500150344852260300720030f05101d0034480d1005510112102514148114241540d00426112004181180001113240d2680400405c0c055824429070050100d90305c0d034070200f0810f030940d841076003000c0101399900800149410b080c001c0c80c003221001005068100c4c12501005440d51004542860507036440000110015840c820800d183d641550b100c0c0d1200d040c442c01800f40c0f07600c5041c10754004018804402e183e034401d8408503009507126080340c644454 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 706040251 1250 706039001 706039003
    0x30f03050304030e21160f060e0301111b060f070f0c03050c070803130807080703120903050d02010507032901180b03090102030603070512121e0a170703060807050d0302 74
    0x1c4e1304159601000d908690358420600780401c1d0913008402003a00d262442c4004800441c51182c440c0004504940a00700400c50140b00850340700c1c003019001054076101d004030301c14160300c00d20a12241031003a001c210408901002840d130b00c840d886500c4000c608008001400c000d555191820422803440401c5c1d040601c604c00f80c03802003c080048175400c2c1e0b180d540300c0307449400c9404c01544e489594032000480c010f00003607100071545400041e1035014116121414030b600d9a903140e201f8040c080000100140c0100211850706216034000551800c00000041c2078030403640000300580042c084403140f403440820001480034003401c0548000204d1303800e1048856955100008100d0040b00f04210b85d4010b40043d13206010450680700c4c55511501007045c68140c0c070401035219030180c0449656641e482c40108802861904045401707100700700400050f90010b034488001030303542c0d031907c0204d00011500c5d54104a44d824140403860511104c169101e820780300b0180305040f0b10b0150018540 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 706041501 1250 706040251 706040267
    0x3060103020f0331081b030f0a090602061302130c1b0606081905030307030c050d09060b0103141311040b1c0b091605040b030c0306070315050a030f0305030403 70
    0x540b50200689a107441081a1039408680714000480c0c00301c0d109013914584043d24080d0510360088845081192440041201d0366031540011400d21080111020400c0304001074901542c0395960400303801d00341240241000d8000d822070a14040002044006907289061b4822101600304000b8111603510012902030821503003100600c09652030680c140080b45d004142501c554001b10340c281e00ca0f035107e5810300c00c00d000d80900150014408215002e00ca0f0f040f030b032440074140c541706081a1844518004a450080044070307640d03612440e2800303950b0540241c0040d0046130388030400c1441c081c4030200c2d9803000c401000b00b0700414244200b0160b607075a030102200c440050061942d40311191202c0191801d025030135500740003c800020220040010070494101c080b01c3c035240e500745404180320240284003102c1c0d07414000d82d60071140c6620208170b006d108008503134000c500329003030100304030010702c1d00c1d006203001f0580102d051000ca012480c008440903410f00c1e00c03035520741e0f4078101155040 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 706042751 1250 706041501 706041517
    0xf130f0e01091e051e070503011409010507110d12020c0f01051e090705090a09050f0d090b090303040515040e1303110a020f1504080a080c06100e0604020306010302 72
    0x1898850240d600c4141503005003000b9201e80f05504282e40102c85142d0a001c031160010b0490780600605207141c410000301d40e1506001d41d088440c500c1e11a80040c0c2134400c0d01020b003400e000e15504015560741d0034028a40c0240300b6050000402341590101034075156820b06140c01d20044031714000226007964111441c0c800380800340c80f680d907180600e07680a01416540c41e1506004040049140d4400d0b00d103960082c440d400013000c140f4680030901c0050701d4010004c0c41d4880c1e60310315050101d407090000c2c0b101039003920041c15602520f01e10180c80c0d1442908811001c501c10700000d2000d840c0081250150382c0c1c01c5035034040c482d141c40f100044c18072454012400300e40340f01081c0004200b0f914a803801482c86500d0390b5600d10048000c043d0b82d49503a40b8044d500030b0b03001d980e400a03130030400080c2044e00810348405140507100d01c05a45842c0c002101120040742c0010603440408080c420b03da0001c4c81e8085a00240c6d190111042440ca0060440c610940d8004040707000d51380039034121901c01e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 706044001 1250 706042751 706042781
    0x3030c030d15051c06110f0d0b0111070807090207050a08040801090c0e1504050727030b07021207110a0515030a0b100f0c1a040f0c05010207050f13 65
    0x51038580e40c000058210703444482c151040440b400f10b618503002018411141c0c001002040d003d203e52204006441401e03840d101c5050300b00002d080050b680002002e0061100710042500200c90000401140203403400701000d4011080c11312a00101141003811035600c00c501507203a40b2a404c00b5400e112106400170b00c20b040001d4001581e1030190000380100e405050300d205a04e60712091004519411185a035040b845603103002d407503240c5507105d560405128540705090140851400c500d8071101d88011403100f280c1d200810400101101085d403241d6140302406410340f08150950042c00b440f1002004d0313030410140d04205882f5100303c040140701c01482c04010450461521a50303900942d03d0315001410030070400118108051100444400c0e503032270100030f5210120454002c0004c0c1c1088600c0340b51000c400c1c0c410b100d80c090040c01540504601c9158080030310f02041100029400a81590816101040a036490071402d42c040e01080c0c83c80804901810300c00c4000f084000044079507 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 706045251 1250 706044001 706044007
    0x80a0e2b0c0f030b1807030201050307052a01020403020f060702090103020d06020f0a120f0509061801090b0a0507080a110a110102120106020c0406050301291804030e011d0d060b03030c03 82
    0xc1c00011141d139400b612401a80710035503107102481070385544640c0030181c00320340c3c00c0000c5080c00d442100100074503800403040030803a000d2030109d2000311520310301e0480d09a40106042c030a42c40c1000c6107030314105088419901e0208035a002c40c030201c0b814440a4421200c8000400500005d90120340c51510814030950f511900900003500b2004c0c40418441428504842c0300c2400b40703d0301c9418000c1c1c00da0001803000e0795485030351014005a040e20212155200c0c101c072000941d070358071014081c2d08145804603c51414901c020302801000705032400c0d0509000301e50810207010001c55200c0c0015240c00036013034501c0400303140a88203194011301c5500c540000000c0c0c50340d01203000f10794031000300c034140034140c0d0f01c004250aa84000c104861503e010980c400f0051030240e0480c1c60543c405400449580c81d189000000c20002f1030b002c1d030100f51103070386440c2d42d036030f12018000c0b03070143c001c02d01c00c0c071040d9000210704410420440200302554801114170160340800640e41045201811696 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 706046501 1250 706045251 706045253
    0x3060601081e0f150d0b0f0912030112110306100501080a090b070c022d06070314040f05031c020a0f030306082409340902030103080a0e2b0c0f03 64
    0x800070085a80c20740e03010384c420068410345030075545d180b003058108031000c00680352558100c10004025041c12074502c281008042845000f4010314005c1421808040e0200445c2c100450010b8076031146900c070f6042081040b854960404443d010b0780c9080c030b0684001d0b603412203244000d125038003002d015401e42500308203d9070391100c540d09000e40f080c0c2d207203001018282154078034941211000420810701244450719414110b003e0042d850192419140402c000303039001703a85901076080184084ca200320180302c80d050800000401c044180101c070034114940c803000391a0740c61235000400b091103656104040c10b06c02d801403400f038200d1006030380c40700c4041020480a0380c0c070368807444007000c0844002801c80b0008284e0f88503500d504040600880030810350307144100080c0c0401c1410700d40f08403010410300d00b18400340d4042d500c6650039540d80c071034170880038140100ba40c0c01313644501c0c0d60340750792080003814503200040070f41030445070004c0700e1051905446072a41c03034001040751608620004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 706047751 1250 706046501 706046521
    0x3060506151612030203090d05280504080c0904082a010e0109032604120201140a0c080a11040b07020303040504020d06240507080a0c021011010b0603040203060601081e 74
    0xa0342070f80304098100088403003c005070160b000440c0d218069070410034102c2d1aa60148000700444019403800e0242084940449000c0b26078650480b000a50046428044820b0400464810400494840c007480c0b40680c1d0311413640c4142203a000c100700114400144148409280c0409048414002e001e80d070960b0b03031401e000345a1004c0030350020344d003841c0c5c1e03a41585010000944200c070350f200b140e01c5035980e6203c0e10000a01560034504665952082e003e541100240c001d015044003c0e0214142c2e00042c40101159406400344c641c051511152200a20301001100c04851140521984030b9900b400001c0c218011644130300d81240c00054108028210b940c001800c0da0000d00140c01c2d00340c11011440d1410021140b603001183c0204000c1020460440c06444d08041ca03140503800c03a241d950102d104452034010f8000460072181803220038440070301a0310000311041d10502e00754039040c1c0000ba0784003c041d200301e051018400205680f5681040a081000481c12040300b00c0d050000c090 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 706049001 1250 706047751 706047787
    0x170d020c0a030e0a0512121308010e03030402010f0f021e03071b030204110c030f1b101b0509011e050f07051b1807080c09040908120604060608010306050615 69
    0xf96101ea00010404100c5103002001e11600f00d64640040401600d2000c1109056004540303030030301c2d00303191900010030704424011010f2000c070100286880303091510014008400700d89118050204440280c0581c3e0740c009502c1007078041203001c0c1f03a0125074117014281588140b15014000300d5a42011906108c00c00d902042100c0c03083e1380030011401d40442c51501c6014016203411142c1081200b8040c084400e40034080002a1040011100c80600e03882854042d01d00e10603c00b80752140004106c10740c1070903014403000428201540f8048602c40000c2c40300050141c40900c401147d403802c510184103205561f110b018074501c5a5581c045410602c0d0b40e8003501c0b0389100003400400c0d1000060505000c9240c20810b66003440c2c000d40c030b40100276101c1003001000360310402c3e424441039200741e40d24002e10036404e010700000c0f9912001d00b042d010241c81e001b42030354041c600b005410070860f64403652141c1101c0e0800c00001d226222440000c20251101920b014040c00109880c1c1c10001d801c0c40b0703 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 706050251 1250 706049001 706049027
    0x5010c1e0f0c320f0d02190507090e01051014030d031e021b0f010b060d050601020a05011a0f092a0d090b16231806070f021309170d020c0a03 62
    0x21100302d000354203085940c41700701c202c0030401a04901107000c2440400c40390b18010728440c0c0281c6403150348400c2d03180e00301d03491f0035803111a1780e455405021310442c07100120400703080c205030303026038640382400840d6440b0086900c1c0020140d50343c142d520320380700c055180421400719880540d9a10030704c00100075190032000d5904800e004036081e001e130a050510500c0601c200141c407a13801c041c4000c1c1080300810b001442070f070640c0650b20f0322500040003881b50034054980500c500354184e4242d000d04c248440e0815180e40200814000e2005000c07443c04610070341c840c0c0703002c000741c03140003900182d22a000f8405140c000c181404084410001a449000c1c03040180c00d00a0542e901d140c0d0307049505030094403d15001e00d90504000303821b06021801040c0940c0740d103968001004c0424041003280c0e00038a0103680c0c040c1e42602c0202140340604124a000199001c14010211540c0310403681140c4d041c0310403121070001500028248250701a42c1280d400001900c03441142409d001d49546134241c8 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 706051501 1250 706050251 706050253
    0x60603051905070e19020a0309050607031b020a080706150b030703050406240e0a14090604060605030d09050f0d060207030f020c0a0e012102060705010c1e0f0c32 71
    0xba0100d00d02034200810ba1145505e070068442c10400b46099400943c44064a4006c0548403004540880c0080107281e0081c0714560b8001100e428524910701c41207100313030381c1c0011904400c4918010500c100280c4040035040000016441206640d404092406501071400c021000c0100301c103903900340d403041d031249000d171405021031901310080c0100001002c8246c404903c140c84103010b01640381d1801e40c2c0c000c1c241c4000240490f02d120390403107905800c44050307485074040c1c4208010000d0a0007084001d0909070000d041d24044400050403c015a004090085000528060b40c40d60350070820860b9603003100c411542c1320410304000b018042105444005480380c1d5001c4401d40c18900300030011200c070601925402e0b42442d040b220250b100d20070588802d070380141e0038030141c0d892200a1400364803a1000094000025602800c0400341170300c1307403103110b41601c2c207805165000300c94500e000585103031103481c40f216464561800707449610003021180002c1a1103c4107010201d006030603140e020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 706052751 1250 706051501 706051513
    0xb2212020d0801061e0e0d20030c01090e0c0405120606102105060d05030c060403091e0b1e0301510302090315010914060f0607060603051905 62
    0x100e4260b81c00780342880303110006030343d01000104032007021041d01e4100d0300c2c910781a189262007500051014204804c20346a111540da100f5000b40f8007440401000c2009174080e1251490400c0003138880c604c0d0b84a05d10381245018001400301e813042c41214040e040050140707810b96041c50006030f5a103021a0520700840400c9801c2c0800c9001380d00030032610085c01000011034155019500c0603010141042c2d42004040440c900043d5041c00500142035694006003200d242a0030003d007440001c3d44044c1d5080c1c3c0d09006c01c002201015060815696200e8510740e94500030030200c48a88030050040201410100001c101c51040c5c003814003104c203080c503004a021644158030000008060707105c401d00b0000301ea066020451501000c031210315135003001801c00c03080c0390119007007002d42240f2014002d0542c005006100a511403091480c0d1010803070651440c000b8040342c04401c1044801b4860000450307658100074464100d0800b665202c0156064201d80b400c482844007280f11007210980620 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 706054001 1250 706052751 706052773
    0xc030b0f040b150102070e090d02160515091c0606091a0306013011090a0902090a0518030d020409110c0a03140c06090c0307080c0603040b221202 64
    0x12450080d5000011982c1c42c0d121056107241082d29a4800390641c0111580083d2400c0c00142c418415058140030301610007124030024180301910344070303542c0107a40004c24041c81d150103c0020b003034810001c4107a07450401100040028180d0044414450b2118501408000168025200701c0d4034a02d4103210014003454a06683c0c3c040000d01c54059011500401c0354100a06072080c02c0c00d441c43c0100c0304548013440f156202144000252045016522010000e04103130302010303413000c03910004209411003030340069421540030304a040c0458a45005c51803007183c00381c07202c0c100812282260750398004d5015500c040d4000d889100000c92801c640d0032800040305007151001690540070304140da40f5645c1c1035551580640d94001c4443e07081c808a0085c00701000400e0080d4030020051401204003c2014985a8203800c0030415800c041d8040e216034588005a0f50803d600640c0c10840d5a5030020341d8641c01607400e80301103014040740c00306d82800549070200010380c2c1d8941c2174a50450714 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 706055251 1250 706054001 706054021
    0x702010603110907090e0405010603020a05090c07030809011107030e0a06030902060a03050a09060c030902090a0c09050d1403070312140f0109090203012405011205400c030b 76
    0x81844090412002e02d0182242e600d00410041c0d4030003031300d060a141440d200c000e041440c8208450403207150303550300014429132070a25070501c000c2c5001c940880c038505e001e0010000038040c0c948010207000780a008501114000c0d00079901e0305905200c45c0352601d01d01e0078000c00d44082d0620141c0a4000103801068051007070003038035aa03a80140c146032400000042c00c600818008241460701c1c0e964040c48c10001c3d00c5d50003403020104d210342d070210b484402d9004028042002074a00500c8901e09080e41d090340d034002c0401011100d044a00208045107400c1500225042031000046030000003800390400d500844141100a00807a0400c20100c49010303034813000a0a0300d00c001d2129494004110f01041c503040130707040364406000850b4444204880302d01c0e8460f0f01c5a50340c0c05030301509040c00156488800c611054074a280e06000c1d0307003031150560a04e4119201980910042c589009101c4401c50381c0c021015001c0c1c4811114601860501343e04100c203502041b144106500041411011 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 706056501 1250 706055251 706055261
    0x906080a0201020c010c03020a0204060e07081e01140112050c042c0604090f0605042d110d08220f05040212190b1c050105070816120b040c0c020306070201 68
    0x241c10380080800350701d201d0055030381c1c007240c510860441c41805040320040e00d0301d024440c01408070703042940f454107108030094090341d4020850790540300450441c9008010611354141101c0d200c10075496000001c00c01256002c100704015941982000240b201c0310354644001c0c011201d0585000c030094002840380745511000c0715091680c01100004207c0c00e29040e8001c0140d10711038038114510405541d1000d00b0703100d04842c02d581c0a01d84440010070a0b001e0703810322100100e07410b503040300c001d080d94640340ca000e41809418041d040404900302013041d0308044a0f01030446961403e490302d0f641c2e2403000780124502502c825961014000070f8582468000d5800a545107034046516980e0b0009600d91011208c0c22060019281c410701c80c116220342ca191041c410036292000004002410243e0030b54002820240411503001c00300104400c5000800c0f500c245c15103000e861104942e01c00102a0400c405445e91141c1b400440789103407500701c095022141e100f074080d04c1d80c50340c41d00d03403e9003254 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 706057751 1250 706056501 706056503
    0x60403030504030b06010c050f0f010f02070b010e063012070b0a09021507030c060612051f020d0501060206060a140d24050708101a070303020a020a0b09070906080a 72
    0x981d00b400240300045449064651000b01850102c0402d01c0d2074403118640344c402c1c50f402d2402c3c1c100c0074070105c1d4500d007030168881001284109514106076650703643c4640390144610001300c48401d01040322070365082c2c002c000c0c42c400700d000e8811541e091015100d081200e04c2d42e801051081101c40d01d120784440d01590f00190708084a04010f40e6880701c82c40217070078004001c0380d11081c40143c200c0b020400101030580c1d18029a074019005849141404c00c4907030580281c0340d50b00d460191000013500014104000f060089031488648003200103240103070240c540c14400690501b0700100780558000b5007284540c0d0116031503070520f60f07100e0541003400c041a544d160070a40c61010b031008100b100742c1c5501c1c046c6503400c0c904000300841c2c128108544041d02c100d80090280c1003400324400c603000b0014080e00304000c5248050202668003413079442010b10080c11701d074008c0790040b0250f0003880340d45402601304401700780a01c1c4c200c0c00e0986401e00c4e400b8041200e032428001003412080020345445003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 706059001 1250 706057751 706057757
    0x180507020d080f15041109121b010f030f1b0831051204060c052e0b0402120c0c0d0206010510032a0903060b0613090b040e01052406040303 61
    0xc0d211030f074883c2005540101440e1070490894240c0ca8251a584100002001d01c4502591030704005400c1219104015010038290340c411241c16540001c260071a01240d002420007aa400c1c003e0b100644c00f40509600b10b94a8a1500c11601c80d01000d004034450784425669502d89150745244054614904118811111300300300d51000c040716054415182c0c000e400751045444800c0c224640700e0031b6901c20781000300055075040d04d02040000811903a5002c07001d807441585d000c0c07a080421454103040c02c02c000308107a01c0b410900515215641120b0b051710210640210503d400c5081c00710a9010080300700d5284039844412499920200d8070f50b0596000502c5000e9041c1c0010086003c1c20081c0c3e180d58441034054070441c5d0140c4848514001c200c000e403514040540b03181413480440e00c00214060150004008103400203951406a405503040c04100051070b498500100703009041381d0007c403100d503107003000748100ca41210500214001c01e01d40c11840350035001c03003070102e01c0c0110300c401808 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 706060251 1250 706059001 706059017
    0x3040b01050402030702010b04060312090602030a020c010509150307030b0f040c05031b090a03050715030608030919050307141219030807031401090207060e06071b0c0b0301180507020d 81
    0x441e24240c3c0085401034014400400c128200100203030443e121940304603a0f014074038040e10420b540041e00000104214005941008020a4043d443d8204040454100301c000200300d0904d581718a140c2400c0c10003803280c00e03142e20700203801230000c040c2000300034401e1000100184403480d0502603c9a1003a21359034040c01c6869407000208801e0031201c2a140038401800106e00c1c50f02e52588010040d8040d5000b0242c49103000d00701c0c0140070780184964209400d0020a00c0b02c00d000000b15081c81c1c0e001d440400039866180303000c41e420801c580110781e040c05540700000d031a94a070301c590006403408480c0307040355050521046998100d2501c0c1c4c180091090b002040c08607008095481d0b0100c6c080c00c0c04102c10340012800000442d01341c103c1060b05a0100d24201441003c1c0b18100c0143c0030480280181d092220300900700e0307a4041c0d843e001000142d4608010041e11050345402050742c08103842e102d5845841c614080d0000100c2e030f400851074071000510079480040d0101503119540c4034481 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 706061501 1250 706060251 706060259
    0x60616030c02060d05040c030605060901060c1b0b0406050d060f060f051c060b0a0f0c08041e05040f1e0209011e0203391c21091b0b03040b01 62
    0x281d0900a1a8141d900c2030081c003480c4583c101c2d502826105601c604400e074502419460034404403000a400c5501030840c0a0041c840706800c1040094402d0b0400c3d400c1030300c5c07840c3c464900e40ba80c5103604a424100070100e40000c05030b401c000601244400c0c1402400076a07114a9504d1415155100d800c00080d900305480264501410082c0f0300c0601e1241003490050500702250283d800c164002000f41c280013a8156001c4d0703100466240800325440c100c2444203140c0c4400c02e0341d0050b0b02810010804a510710b0a2040041c60920014071018000703110b0090043d071140006d04240c041d10200749182c691040b4034402d280300322211098141c448020402507400d2141000302c0380c0d02190194841004a0541c007081c03011a0745151019814501040e0001c100c0003062040100340d5074400c0d8403403021455410620038010780d600314145080d80e1481e2905800030b003001d00e00d900204e0368524154182090210b900e200d0362550a0185210b20001d58400303c05801c1d10003241c0242c940f91040300188 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 706062751 1250 706061501 706061507
    0x4241205070b16060203090a0611120106030e07030519060e151906050319050c040c0206040b060a0e1f0b03041a04020103020f12090f0606010507060902150a050a0806061603 76
    0x2d00f503c034a2180b1400324a80e5020b0890b84103803a199400d43c0300002d4802002642d000700c04400b0801c04040c0d0a0540d204004840100180120320030b054680c80c540e20001e8041002500035a045011503600c07840c0c44a1520070340c244d80c40281c13055820108030440200d00010403c9005a0700c1c5c40c0400b41e66181260060801c120580c0080115244e500001d0346540400051612410304000c1020301601d61604503c0c2800518400303001b503003081104c02c440364000c2034040d0b00c903401c42d42c010790f50b580d0900040c02402042d00450b03164494001800b0380f46405100e040380f0344118090151446868000064180c00100e03402068030462294003031140f82d04602041e0440c1c41810054106610360304032440541003c1e00c8489200c08140811440440c20441000c0046450015043e541407000000700180300d004409400142c4441c0f206c400c5484076131031352044206946040e600c0d0302c6000c2000381560720201c3c210300010b64880105410f4500320007200c5030140200340318070410311256015 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 706064001 1250 706062751 706062757
    0x90305060712060f14040f181719260402060a050c070b0a050d140618280921081801090f0c0609170613020301090204241205070b 57
    0x4403242e0303141c080004a0900301100d00c03024045043c00e40b603059140909002c2190107084403640c0d22810f1152909041c2e100c0003082a080341c0103c02141e5035460490510658401c05004070226141c00c14500c090540c00080080c02030420510424500421411582c900400341c501070341c8240704010940d03400d070045005081040411007912085543c8501d442403a402007207281000c108001004444250203200c2e010210a1300e014407146400c0020100340c01c02c141e44002241007991070040f51010000554110103040d8405a0802061001100720060015904102d82050030100c0e520365015840e032020362205040e50b601011907544030201807a00c0d404025200c015540c03105250042130100300c0114405011f0f12003d503100b80360440040414003180e101800d154113140e05440803600c0070a52507041400c518000441c24032900000380140b4900d1002903000b890300d1404d02924070203c60340000c80914040400559a485c10004c03400303140084000d02c03541201205002d500e03a40805 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 706065251 1250 706064001 706064027
    0x90902040f091e06060203090a0803040f0501031e02041d010803120708060a0503070b0408070e0c040905060105040914010801050c0c030409091a1e1312030b040219030603020306070903050607 84
    0xa011410080c0c40743e0303000c59200f50001c01c016000010746007007508214000b100148803001c02149001e00d01140c3c40c145000703c0c00ba942c109921a6409010000f402c100c610050765003850856807142d0303500f42e002540090382150b4040189900000445d0080481558403182100142c800c85a481ca50200c80f6070707000034443d591100c07484ad4041402e417420070920b0003415560301c4031540d4900b00010300d8030b000100c0c0d0050400d007a10f1420010a1440342c42030300d040329824100410f06440b00c00c0142d03268003641e0000f800e86403800341401b04101c0324042450403a1401e0b0020042e603151150000102e1081030300050b00740d80200000c00c600d04940c1d00400002d4000c01000c800d60000e0f0038809401d00f015505002d600020725150b0000304091280a5041a003544c405030030b0481c0c0d07a0f2440f500401d951400703c1490f668400010450301c5e190100d174010315022030200c12020118030060024080c0d804140d0080c41154002440f2900801840007940c2d04880145696541c58208403220025410703 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 706066501 1250 706065251 706065281
    0x807170603070f0e04060617070303030e030f0c0102071101020102043006020310140d02150d060b0c0f0105060909031c1b08060102060702390303030c0901090902040f09 74
    0x7400100c0001d030744601c2004e0312008a8038a4036080505028040d40c0c2035420191948411080380b6416250000d408002c895243c00c02054802c03107208500d0450103400daa000c00924001412044c6a5040d0700500c00c181c4180c10860321211502d004908034080c3e0701034006e90003261800c18105010a84010b4009802c000e40d85106200940e40e04d01039030010b0391043d01e10261900140300082020001300c5680c03000f500d412080ca001500050b880500001e01024240c4000801ca081d4002a4000101820845c040c3c540d44415115803142c0c0e0350308802c0003485952a000104005180404e111030081c00c01000442c10081c02e40d03100181c8011031100c00074801d64990021101d95000030202c042c9046544401c0e10b10715080303001a0802d10002c1c16601150010b4006185586824450000800840c0da01041070b03040b4002c140715030140440032942c18030000c010042020b09083c01480740c0c2c1c4003a40c1b0000d106035103070f6240f802d87c010b60040b0194069000000c0c40340c01000d510152514086603 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 706067751 1250 706066501 706066513
    0x10507183b0402090702010b01020307080d0902090f1017030a080709030b0108100501080606101d0d0506060406051005090f060906030405010608010c2d110f0c040c0807170603 77
    0x100740300751001c0301860864a4607008504100940c5000721a4a40c000d101e80000e108550140e00001c3d00c902c00c3c103400600c0b00d180440e20800c5011103a120599a40c1e02400060540c1450400600000401c1300e40021101c0c1a032404201c074803010000540d2419514001c0d41440280c070350542d00d800008186004010300e08800102140071202c2d03003402801108054402a02d003404207500380c1c0d0050b000b880541d40018140259030710f81419410040a00d03103019400c0646541c8012100001003071596030125440300700105000012401d98021603003103408109690781c460038440c48040301c19a250119005001407415801c00140d030a45120f40204110314250600c0000762603508152000d45a984d51203c09100d0740314244100c4401409a0804d4020704041c01c2c45104c1108020003c01e08814464880510300781c01076a0780c0c86c80300038907000e0301c981450b8203d00d5580e40074510465840369081050602a80c0c1c000e01429024455640c1c40b400c2d842d4610f011840c4d1820090100c9030144281 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 706069001 1250 706067751 706067819
    0x81303021c0302040612110931020310060f02060a0509010906020708130f0506090607050a060603050a03142107120f1e0b06070f08161401050718 64
    0x20419182207629507440050302d90f030400d07000500304150b0281d030b848002e00d00b59000306504640c600713640d170b04071007103c101c0b21041d140d48600e081c0c2080e80341d200114802c0e03148403070041101500a94030444490a400c082d8960b00d55044692110040408000d03801c26008100f1011590300000da0101c0440700100e0540c505554020072030344440f40c1603c43d00408540b8007421030074081341c0c000900419505081c4da40c10880050365a1044d182514400c0300d00155003c2080400d01844400f20342014040040d00d030349043c21525018045021030020301301c048815520f9800300c007034641190808001a0040c8021000340d209210090070071801d1101b8902d250031510024000c031070706465880d001040e1007904000041c0d161085544d2a920141004841091038a40000b5030782400e402c807910f09448480c50400b41c0c944d10811000307000d02015000390750b0034001103980b04c03a80381d4190402042103640f614801c64400c0e090011900070304d0001601002460400407103961110004502602e00e0b1280c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 706070251 1250 706069001 706069033
    0x81b03010b070302010e0105010605092b050309101704230d18050307230a170d080c07110609041425090e04030c23010906050a0c08130302 61
    0x42644181c1c00d07450009008070401d83d0a020b017080725284407000384681d5040c1000540341c1d00401a0f00f501480c080e6413040c0c050700c841c5e4a51002d541c1000c0201da4880103908005840f42e00c1050754034007400301107a16824240c410120502d2003040d0000c1d240f2280c48a555003641d848200700101d40020786070010ba2180c0e48244500ca0144283c0e03103602e014100102aa4586503001e5070109202c0d40102c0300400c004101d1500c914448454400c40035030780d82442000503c0c02406810042a2010381441042490310000f050711003d5582d480d68400d80d43c9803100ba4490b4840d0403c01006940c0349903030350729981041005461080e10083c4081064400301aa1410102c42140d4005040e204804180c880c082e50b000140700309501854102c038200d0500b481c4190b0018050001410808075080e19820b000b1142203801560021554903002c501083c41200d01820342500c090755047c0c90a00400c003000c07540e100d001d8540a0315100c08190350381e1141505912a94a241a010750060200140314141 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 706071501 1250 706070251 706070257
    0xf0f1b03130506090a02091b04080706050c06011a0a030b0f04150e060a0305070b0a020a0807050c120c0d0311010b450103060b041b050d0e070b0307081b 67
    0x3a01600340038651071030070010700d80040a0300d201d120390000300484000d0788030300c00201d03480f0408064014040600d84034084c4540b00d00d600030000c40c050808080b644903070040042c403000c01ca00b0b088034411798945125041c144550750800240000c00c1000341103e5000c0d030000f402c43d080080c4040f500404000215050701c40744034142003070055800003030040315403102c400c0d90403000668000c424941581d5400b5038944150141c110100800302c1c2e0f80c1d500e948200b001c04410399006000d0b580b40c01941c5015507550190440852180a114110280220001034015052100141250740441c2c0d16282034503641d501c0d03010150f00303540312600e50109880b44c50140703501840310408407a0060f9500b0003100000c1044c82d2840e1043d018090b051561284c103018281942d421540001e198411075000400030030b0b400a6072511041d466040032011070f08200504810034003000213102080a400d40e094940c1c4480c000c81841020500c045405540702d074030500da1241070707050a05070703a076081c10803004690 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 706072751 1250 706071501 706071511
    0x7120b010903150b01030e030a0f1808070b030f16050f0f0d11031b0301030f02060a0302070b10080c0406050d06050c040b0f0d062427030f020f06030f0f1b03 69
    0x2900c4c0d81d070103e00d03540d0600c20305d101c00f21010095410102040340c02000050034500c00e4003004000c550051910b400404014000d14900d0100d8641c03036a0f94a80e131543c0e03041222000c0d240301041c40041c18244414864401c0da00c1d00740d036a5403403c11084071804032a0024410301300d002c0c13010300c400c008050441c854841030030a88190f1549030324102d02840450420f410100703c074405c003800100700003045d07040007601041d0304440726030310b07807008c94405c074001c1c0034600c00901030000d000c3c00e2081000003820113030241d89411040d220618a0b400501065600900c145900955004000408525140d000135040401015001d107016522520020319410201c280190b600000881c19040b52492041500505600d0400180e142c840709110081d01450398810f41444a808010602c2c50807040d4440c400c3c00c20b041e0304008036030301c0742040da4192301c5c0d920049004014410848910b03241072000d0703a102d0011404613219a0780c48480390a010b50000e03249035a40d0f1020400e0781c0c400041800a5480f030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 706074001 1250 706072751 706072793
    0x8160c050111030103060b060f04120303090b041a0603031804020903010e070e07030f0b091504150f090f05130f05030909281a0409050c0d140c0102010507120b010903 73
    0x44d50450800300d003203401e6808801d200c0d075010020780f003984160001342d81c21034984501d4196168400d05007603001c0c04006600500d201515404c120411001001160b035010f02d40c1a0b0300415039440d000e26640740710310100100c3e88101041041d51a16241d0001c041512007d00046003808244034511303c0c04586402058900190b03c041001144d1701d071052039040d010019060008000d1346003c180c400360301408130300d461001404412003503203458000200e0a0040c13182490803e41e11503030020005014007500d803c4030f0800c0540310755103040380982070164008006005880b081503131070582054240008a43c43d000c1480140c0300c503078441d40703000e22403172515602101c054800389140076034140020310580e9403460440300c0040300c203076444440041c01c4250303400a10b83c1d0640c10502d00c0d1240c0745036507e610405604510082113503200914421811080031564910403410040e4241d8208036010030011303808907813910410409402c02e150105041c10682c2085442c1d0b110082402500740c0403804c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 706075251 1250 706074001 706074007
    0x907050d080c0105010e0a05090109080901081e010b07020913050c01120f0510050f04050108030d0b040908041403190506072706031b08010b0f0309121804060b03060108160c050111 79
    0x87c901d945c01015880039200000300704006450369018020300900246904008080001071400349200d484400c0780e08103601c0b00320145d030755005001c0e026400144228050361506021915001300c040402502e140d001d03005d40300000c2410011102d2026489400c0c0a01d0740310040d00b010b000342441001c1c0100d400045a4181c5401c003018014201c2104404030301035807a207030040007442c5000c4103503006201201404614100c0304c0e4001000f070421408041c01c035000019000441c0c030022084403100a0301075080d070b05080e9201003480c5495000d900081d02c10b40001d000580141c5c400c0624030070404241ca9180c01041e0291070450340344d882a0070182c0442d54410b00010301415218003a00b0f01c1c206403501c00815810180000e000d400746d4403181741c14a0000c4007058076541e0610104044080340e20131a6200e0170802840c000150017410864040d03890200042608410201200e10961041e182e0803500c0c1c4411000e00046000200c2c05004c002c0640c103000006803007030040413240a140151140c03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 706076501 1250 706075251 706075261
    0x60501091a06120c030c120108012310060c15051005120c1e061905130f0302011b1b06090f0807060c060e120d1e050907050d080c0105010e 61
    0x3801449808150b03206490900400400814540b034040e48010f400c1e950b2078907034031000e1501c10705000c1c80d400a00040c51140000c203500c003056008030340b2064848205c0740d582480d40742c20b204d03100c415502c0e0208126042410b00146024251460305036202d101c2d48c006000f02d80f882d8a04984058030803074241100c0110401135132800038041c148104840014211103084640080c0c005105521003905107000007403880f1240d0345803400d540c203c0810400c0c5055040341400e0041c000da1100c9482c885c0782034200b80100d05c4c69203003002c5106607035040e1106810410000f100020b40360528408a03101624850a4081c034040152060300504c0e03035448641605003400940036014207203401801155010140800026910843c0308243c6600241d000450f04030f07046900d07003020922509102e421000040116020007103a10917100b0700b0001908280b81c07000440c8000a0310400e03100000e171030707001030340c2403100e0b1a1003030402c003442d449100b02d18a001c0c0080d1540e400d541c002d9010801c102c0c0c0b0f00d41041 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 706077751 1250 706076501 706076531
    0x40b070f0203130311060c01110d14060a051e03030a0e0103050a0513080708040b160308090109080d0c0e18011502060606030a1a030f06091018120c06050109 69
    0x26045400740051801c05007003aa010754400345520010346249580a0b01025541343c00c82121040300300d82c0000d22040c80303c100311001c030398032034015002c902c0e15182000c8512100455294000e00740181841c09561600081100b010040c8601643c803100040502900340d400300000d10000d0216180c45000d429180c0c0058102c0300c0040100d10780174205010000c40070a1a000000001c0d400300300c1d00d440303442e24280362490f80a960070813594048002201c842c009400d02144108a01c290345180c203036517500080d00d003614000c05000340175000520071a4101d0103143c000030010203003450400c00c1d00052400140d2070b076040c1070041a02484c20401400b054494461002c0011880d000520300c0e4184600441c01c02d2000900d059005e076503c540c0e84c00c500c0901c040714821418000e00b241c10501b0307010082921354900361081c6480f0300c504040d07410100c90760300485100308590b50050150000b0340e1a41003206088105207010000c608074a0300026040b407154501030a403a80300040c208030040303404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 706079001 1250 706077751 706077767
    0x62202190f2d0b0a1101050f01030b0703022b0b0a03110405100e0402010e01030608060a0c1d010203040302060d02160506010f05060c0c0d0c080f0102030f07050f070b0402010c0605040b07 82
    0x1004042030001c000003034100b001e8054104075007040c0042c41d500c00c15541e0441e8040d0f40c500e55403600c0d500308401c5c80b2a180510050f54103030f9006402280e06070705c07211000d80403407241740340c1c80d5640120704412281d09044001054850083d00502186205801000070110200e50700b04407111800c184a04220341000d104181d8858860000b031080c0904000000084090003800203042003038005e031801c0264400d4010314010015041100c0050178001302c13071030160000a1011001945070840c0150041440d20513000e01201a0047c0d80b6250846e001d222140e0712050b13a484116401304020003401100e44201480f85010300c014000340d5041c5165401c0c07003040d1b40d225502c00c1c1410b1002a0224a010500e2500403c0c1100c081032450418a41074080c0540d650180c4001e005605200300300d10810b400643c13003284160821001d6071b50f030450544440c00766000d10a2452800e0180f070f03000480d420591a08240141082550016141e481c0c0e01034650403501251283c07161018045a90b41000318 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 706080251 1250 706079001 706079039
    0xd1e0b040501030f06020717030c07050c09011d090c030a05070602011b1704050f0d030903320d0209031c170910021b071511062202190f 60
    0x41c0019455903e4450030180002c5016048036400901c0c20100705a10400c01040c10300341d04641c2c0c4030314100d006000035810803102600c450103420032100040c5001c4111074161012a503050801d0381c3c1e00c045104c46440300030410b4103144903e02c02c0e03440300c0d9000c01184900504c508010a030650130104000d0030f44000100182080480d044140c00030398008101501d180004003c810480d552410010b107001c0d01128002154052180117a1806515401c10003095001e9220742d00800d040e0000807821225131112400d10b854200080052045c03048018015462080b00141c04c0c20326443c0003c1c240300a58500746201640c2da4004041c2e0b58204c0303600030720130a004c62100c07554500000380c2070311a404803d4088456a00259500094568680d4406540700700811a5911901c82c145256904cc0c040103090100e210b4000c40002c1a40c0010418454242c1e104a10300302800c900800e4041c91030344004981c13180c40141200388525025001900411b4441c0d4100c9505140c400d00050505e60717541 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 706081501 1250 706080251 706080259
    0x904110a1706011e0c0f2a450207060e01022d0d0e0705040e0a080703081009090516320a0b0408100c0306150804080d1e0b 54
    0x70800009a030082c5964600440070700b040b0805401030707881201d4004041038010003104811841c0c100344844d00840d0014102c2d04100b1094415910b81d2041d81f10032548174880820440c9a00d03045211100410a140210041049258a9160440c52284c6400c001c248814558013091000170301501c6d010f403e0303d1402e00c04c02140b03002600082c5c001508103440c040ba0a11020103410110401118101c17110511092001c10031401c4480e061502c4101a11820b8400d0381040c001c07490320100415150400c13940822483e181c01d0065038252035011004040c0c43c6411101c0a000501111901800c9513551107100906861040c0c41c4e003140304414950031800141c180403413062060b41c201c1401540c0aa0610740c9555550044400540c0880c241d401c0510207400108000480700b034005442c09410102c5601071100741c01c002c1c011000c03181c2e1480b40c4c2c2104102c2c54000010280581c4016812034010300c60b0915010580307054000381e402840d15002c1c0c61049098085a0603d0b500c100c819030a0f041ba = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 706082751 1250 706081501 706081547
    0x41104110d05150901241e0c0611040b0316020c10020d023018120d0914060702061b01020a0f0210050c0a051b0111090f0a180b0301020904110a 63
    0x1041c14580c83c440c1e031800650f1034510501a410300c0c0d000e0382e01484003441c1c0252241e11020000c800a104408c140070848840e420618140381c6d07104500152001d0f5540350280c14207555485031408440791009140320154000e0103858808c070380781e000f8907125510310350b0010102c000e18580000d00d000440c80c0428015a50300c2c0303401543c6049103502e10b014511902485861340c0800c5400b1640016103040c003a030001c01b041c1c3d904000d00c0082200b64081c01c40d0f03200e1400540d5158120303141c40e404801c005600032406c0080000529010010f08010b888041c05602080c1612007410f00721390040760004003045054a40a00d8141c8c1040000c14ac8a0b00b04030506c01c42c10091031081c0345000d51400c00090100202e640000c00e00105a034160311107030900280000001c1e540c10b01c2c80c0c0e074001040300b4001d20300b03113000903c2410720045240c100c682e0390420284241e51611070700020300c001481c3c5541550200050040d550300c5000320301342c40d40008801540c56404a00c007801c103000c4d6407034800743c6140c55 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 706084001 1250 706082751 706082759
    0x1003060815040b06040b0301060b03042102010b060a03091b091d0c030303070c080c0a110a090902100f0c05160e10081203060103061e0906080a0b041104110d05150901 73
    0x610f982e940141d000da03000304102400c840081d001d0420b40e00b05100114001c0100000c0c05151803414107480c6850f500c0d11750340844594102c4c01d8606107494542c02034420418004414400c0d842661a54091041d40c9500342d00003040d43c0d84113807070394090420580c4802d84140b44155800a000d80050a54010005030402401013500e0303000081044040c042c40729026030a1020080841d41500c07074000c16601303510042d141c0b00c400d061485008600410f00c2400c04503003891584502c030700903a001081924544022002280d500f21030040303043c20400404002000203a0802c540c5116820031502407d0060805416040365040182128200d581100080144207404100c1008500120310450740e81e07503840c030058014103010340c45040514482e004092218505e5090f550070750f62001c1040c04119596504107a8404180102611450703905c0d02050024901011261172010003400124100e10041c4c100c04454002d081c17031410507a1a04c0822030b04095001c0e0180303082c070088456420b0395041c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 706085251 1250 706084001 706084013
    0x316060506062701050912070e010b030403021c02010f0f092a03120c0f14070f0810051f030507060306080a080f09030106050405191a011e0e100306081504 68
    0x2103040d40710441c0c803e403040d148103912a108640c40e035007028140c280400b000c141ca103651b43c030306440340e91100c480e210001b042c0710000c001145c0c01244c040e4020010740030b11450040100c490004400150b65030b684000011400314010403140b0001c4060025954685042460441101c080203456503c22007241122400c0e5078801c48080d42e80000381c002000040b004191441d100c2d01d4405411814403010400c100203c4100a1200c1d54492040d1070381e042d40d0700c910b0050309085000b0711280303030018108814804003a43c012944088151450302610305480725100000301990001d842c1e17904036100511005405000b440000d114444c014500c014058486110601403080710580360040000d500e00c07282c0d02500080301600c00100100107909148440702e4014000d1f5140e00034481c1844091300048030b618042c0c100002040c0c40f81c030141c103002050005019007044011040c042c10800c0324050303440d90203081c0310b4842603407400980581001e8400d413030018202e03075040d4043c030072504100000d0300c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 706086501 1250 706085251 706085287
    0x10e2a0a08120f1e070521190507121e05040b0405010f12050f070f05070c050f0d0c180b032a210631030c060e031606050606 55
    0x510100c5603449011600e00400e142c404e804c48040303840300744401070303601d400048018203016109801f103d903402040c080020018040550b12920800140660307240690041142072403583d1f940b8201e4948411a0b0321302134a41045ea081c800012645032254010109840c2110105207031802c01c03600305841c04c041030180c0e205030b0203858100455802c042c051140a00700d5842e000c0c40e240300038421450204000031300d4141c100c0c1c042c0005581c0308e10341c0001300c1c064801c5481058201c0483c1e10503038113000600c5030844501500c1c94000000c480340d08041001a1220b4001e0103140207480c030200900ca01040684414850b828400d40114115035160301e40d40d007260280c00c0b80118269030f0000b0351000110900800d80011100044412101d643c100c008610203219040c15004c100c4984020940c402880900b603a108420381a0712140c01c000c0b80c05281c82c100302510a0a01190644810502905542045444050103402000f0140402c60300d402120350100b0140c030f400307007005084101035800e58 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 706087751 1250 706086501 706086523
    0x31e1207140423130f1d0a020909030910081506030c120c04090204090636050a060f060e03060a0218010e0619050c010b061c0e010e2a0a08 61
    0x1903490105000581070154420f00d24000902070802091103c04d40382c042e290101074228124036281c011281c6407008000f030002c1485000003482010303500d5084c8000c03101c020300003d00d548424030030302589036906001d1141501c4a0f45c1c900311a410f0903200342d0008500268441e100e081c040c41000701018549040c7d440142d480c400780c588940303605140b016544070320b4105544050001401042d8020160416822201d0201803403124441c220141103203000c2006803003101e40f1803014012030403001604140d8020b185034030001080f5541c5c442c03001090030141d12400204900d0110f495103858203224240c0d1145200c81d0552804400150903542d0300b0300703054694184803812502c411151200c3c02514640c1078104d20021500d054000c1c080c0064200403841c0600350f08250030701c0f0b803d081c0702c42540e100303802049140c14281c00540102010b0107040c1d1003010b20f0341d038846c40d400001208000e0407008178042a0b00b01e02e02d078034420704000c201105240c83d5004000185007005480c0c3c002607210045 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 706089001 1250 706087751 706087769
    0xc19030c030e0f0405070918020c2d07090b09070905030606010c0501140c0912030c0303060915030601030b090c0a03120c15020a090e22080c031e12071404 68
    0x12000b1000040c441d0000400100d07009440d0500b04440320b40c1040c0d90206481e40d01203030b480010303180e940c0755007039119810540c0a1038120311180c8020350b000c07544996401c803241c03000c0e025200095940700c1c0b420809601c00d0200c9900d54403172100340d0900c100059000321151900c072062500b044042a6141c1010b0015070400c03da5800100034003900b94130280102d82c05480c01101400d12512084d1607400c461030b143d00c10400c0b041005640745001003140e10030007801000c0d506690f0b40e6010072004490060075a407010741800243d0f8041c0d1340610080d806507120b0009a2214203254404a10340411894003501910500708140007041c2c0400101000d90a9032501300c201850516004881d074400c040742c0507116002003610140d4035001142d070010350740c1400880722295900c0480b0342030100d4a2091342e03030407444906c0007004030340d90a0060910f08001e1080b00c3c580b20020170440c0040340304504d420305110010400b1482003203200c0030580c10030344074900040c804252480101c5030b482948540044 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 706090251 1250 706089001 706089017
    0xf0803060f0603090d11030a080f0a0e0a0f030905040c080c0313140706030c0f0503062803030302090f010f0815040b0a090212060604060f180b0304080c19030c03 71
    0x8035903407807164149444010300b80700d4490a011400c9581d550180488038081240c0c2468a80454000001d88400184aa0304e500ca03a0702c0780304030803e01c40c42c060442501c6907141c40e1010b203c4c0301c0820141184a00c106101c2841d0001420014060820381c3c100c20b10480c14222110f1300203078000b0a0741c1c0c22000316040c0340d641e81c4940c80441a00080c024009002e0348030f8420300b20390250081112811038605031421b11a42202c10b000b1122610745190b100e01240040c408598942400602071044011500000c011024049118803100718030358400c90000f50000380c0b41c0a903041048411803043c60a08114121510550014221040040c07200711182480002242113a0710340e04111a080c1b070150601e548030703441d0414840a54050608854402d14032070200c0c0082c2810000c4900b1140159610b00350380b04205002c41d4440e80c6124800e50900c100e890100d007412503080114002d030300c610300c021750b90700d0b00c1807210341440d001d0b641607806a400a44080301194112141e10f4a00360b051402c070070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 706091501 1250 706090251 706090261
    0x7050d17041d040b06191509030503040807031a06091305010f020d0c0e19170c041a0a0b0307090e0a140405060106030e060405030f0c07120f0c0509040f0803 69
    0x3054040c036807040400380b050141011407880300a8a241c0076500131240900140c2d21031051018108202c3c0c00242e02c04510081044030f4004a640005044068540041c4090b0741e510b5040c59500282c11040541d04503280800400c4030401c00c40803404d400c5014400c051500c40c001034070206005004078006640244500c08100d801c0d0321060900320b4011085484100c900039040051035003000600c0130500c0b00000300c0c07042c5029680a1030142520815030303410380c00c1c401c1c0300001c0c120845042d5050f100398080c00d02d00356118003990502241c2880c11010b043c41031800c22488403400e0340903a103032000c10802e01503019031151180d010b07074480b8000003040303807550720402004000305540d82d50a00041400d00003082008650f240c12501c4940d010300103030100c021400c0e210b01c815a03000303095610400000281b40f940310050886910b0361429200129510b688541d900400c10004642082c611804582005804141c18014000641e410250751034195900601041000e80203002d01d100440003074 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 706092751 1250 706091501 706091543
    0x120f100b0d0f0606030308150d032001050f04020a1e21062d0239030c01020c0d03020304241e0b0a06180608070c02090c0306100207050d 60
    0x1d60242da024400306111480c6040c810000d110703901084001034140300104c1d1442c0d920f1240310300500c0d0020004405502c40c1c1d80c044c0e82e40c0ea0042007000d15180f014200302c031500400e100d00d9115080425584800b4502841082282e04007900180c1c0580b6003001c06500e48907030410300d04260f504c144280a91144140050494020015402040d803802c06404211124003ca03000c0c001070546803911142e03013806032240c0300347c6c081d003008650781061054800502c510440c42001c040010381d0003c00c42600502e00c1c1c541940d200c00003901c45070790005044140c801c0c04120312440f5000d81d1400b182076080c00d940309284480c0105001000d0381d061440080351603007507880900aa112242c65481d840b4901385160043c040c104c0780390b480344038041400241107000c2c8030680c001020740140b8030300c4181041c00556040f08060f040404021024070250b0045e22015075041c042c82c0c61b80305054031b0785800401c10102c403400500d008219042200101b201741c40360784012050302d9002e0812a0005c0d5442602 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 706094001 1250 706092751 706092769
    0x1030b130f140f0403180e070f0f0503010b1c020f070305070516140405180106080706090b25030203040317070605071107090c180f06080f0105030d032406030506120f100b 75
    0x4003113040c01850501c01d846400540f0030038810302ca82c2b80d13028402980142a90340380024800c8844050040240601e607c189811041c0001d04032903005042c07020140f40a141c1d60088541100400c0c0001203400a00c5000c00090384103231421401e801e542410510340e0790401c0001c808080c0a1078860001c652110f400c01c1c2e0096200b281c4500030403c183d903400445a80e01410711900011414261003c56843c02010403a401141c6801c00300740e800230700200d10443c66003100801d17011400107100c0800081c0300140d04403148040c0e05206e036145e0525081c00b40c00c82d04050001020711800d4510340c0e048030740128400e0304031440c68800103010560b4200c151307031104244006020303402c0b90702000308003400c00012030000d4031526515954141d8440f13401c2c02c0621400e00505a155020b0054036074218400e0f048004100b114406072003007107685601107058a540e41c1c00900100361514204103440c182442600d2909035444001d100781c24409003803540354000643c6417135200303403158420106030b20b0300212 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 706095251 1250 706094001 706094009
    0x1203020109060e06010501110606090411031906050f0901091101111e031809010f0905060f040f20070b130f0203060903220503030a0e01030b130f140f040318 69
    0x10901c20b000900d00c000380c07504424086d15000c6031180404025114000900520942002c0d050b0510750700c0d0750312040b10401c241c4089a92512510f4032254444034441401f0050070312179031012600d03051083c1640c10f001e01c01004080c49a00d40f00700500032400c101d003503d2410500303081c54025070344e0105200c1e0804040000a1401d400d0f01448400400d0f8000010003d0b0841080140c902091071400c01c486920300b031207401c0c10103490b05418028091140c4c821900103100902e60071f00b405c41c41020809440c1d244407070741045a07a5660300343c4540c1d0b0500204a8101203942e4031440d08805540c0c40110142c09003060a07048000301d081020807401d00c441041d01ca8009007240d80a1600004580d980e600034030240d03a20001a42500c1c214030002c1105006403440103001d1410034290400c200c0d01d0503c80e80140381003684940c0b0000803901d42e600172441e100c02c07070040840c440e84000000800e9600c0009040b01d41450941040308a0082005890b0069458605080420444015040c4d41065904 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 706096501 1250 706095251 706095263
    0x507140709060e16020a02281a0c0709152303010e03071b06080c0d1508030d15050307060c14070e180f03030c220b040302011403060a1203020109 64
    0x802e50300d841c45007461007091210b290411044150404a840f5807860340001e4100c0642948400541c03c6038545245948c11005003044165035014100c007499401441000885400038048a2400003405030002612014600340140c3c084041d2901c00c20440d88a60850b102300c0000901483c9551a01411802402402031069900c0c1c86541c64603070f44006422103004400c1d0016031442010742551000b00c60894a941c26150350320b029501042d070054458650344c90703540e40c10303488541355008403d001d440244011621555001703000400ca0300c1400c8200e4a10740054810015640c0001d5a00295410340c9480c90020141e0303d000101002d20220b10280c90185960210308c0501481119108201e2014000104600c81100c141c40c0c0c10044c02e4100140c20070000215042c50180062440b0342e0b003c040b080d00983c0c075040382582900385401c03002c0701e188009010015503a00803605c0c1c10240080074030710f24500300340c070004160f8030301d62040380d1950408a260105040c003c0d40034140160b0011 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 706097751 1250 706096501 706096511
    0xe030f06010e06090a110f090d02150d0b0a1a0f12040602090a050d0b15010c0f0b06030601270c0e1011010f090308010e040c080708010e120702010507140709 69
    0x1000031000b80807100c03d8001c41030200003035118000790045082c3c40503907400c1207140420100540c0c250b0342c05964119005000b4071040b400503142d0244140a1014059209031200745204030602503600103100c0d01d104410245003800810030000104602142c0741022943c1c0d1200903c9140c040d01030b000842c000e9405e05801c22080c007286400030030660718121038040780191180c0400c01c010314028400707001040d072980000c006201042c082c030700724081410031000c0301c18155610500007509540403140b00170041d0900843c1c0c1400c1029a0160000418000c000b0066140d80c07060b40401c280d800796441c2c0c94400200000340203501242c001c5c00c024016202442e00920043e103104140c844440d015072824442500106031031140c0700ba1a40d0642c1d03816026468240300000340500a007090712340c5000d0300c600258510040007840c00401da22400441c460103064100381c02c1011044000d03180b40000c00c14100142c1e44001201c0d40345901070540340b03d100e030750f040403031401103d500700100c080e01e80 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 706099001 1250 706097751 706097759
    0x51b03041212020414100210180209070825050702131e050138220b040e1909170d0b030304050f090a09020301090c0320100e030f0601 59
    0x100100401074100354035207a14a11404107048124411407040d1200c1910324401c00d5140c1c90709071894401d045252040b5507101e04031442c0c0c1c0c0122100c9915020043e04841d84200841c10201c0030142d1082050411304050301d401e210b81c0e0403d1015100a2841301391043e11540c2190064050701d4409401500b606050080c1c054400014810340035294040301d010703140040e0390301e01800350030706a400c1d00603a541c01d081a1816030390300414070410190301640d00d80000700f51060000262400448862003000c0c0f1400c04909202ca042240d08180c038407980400041c041582004a00c44e00a61000e07040002d142e00c05c01c82000501c134840d0020641000d800c1c5d526845140d03940507018295403070303500f0080680f480040544c0ea102e544141ca0b00300c01c0e81c3c0b00f07610052910307119450f40540c500c18080b0309071850750b0010742101c1c02544220784000ca1101e042c4103100c03285045031019003504401301d4458500e00000b64121301342d0504842040700d807a040343c5250320140101c80c1e6500104085813410b58403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 706100251 1250 706099001 706099013
    0xd14160b0f04050616050f0f070f05070510050921100e030c070f0f050409021302030106030911011701031202070b0301080105070f020303010e061e1807110705060d051b0304 76
    0x1d85050355030b03101380c50208000d260401c070070508020075610344034035041c840401c00260b0707001211550961b100500c0000d0209a02c1000000b410384540003401449083c44200000c01382c1c040b4404007008003e0100c0b16441c0c85194002184007101c2d15400da040c440d02d680f0510301176600c406410903604005031300c0310198000024000c4504410261104281c0b510301e414003081061040c4000720341c007e80704004a040c0745e80094030090016140c4503910001d80da5840903030380f0070307440a07002a0382c0342200030070702100d401d009042d410b09191542202c000800310061170b92041c040a88a140c002c803031102458000c1002d54000d04500d20f0040d269039603a040c09000700000c441000210b900110011540c6101000b02c0381a603511024411907601d500d010300c810041500c034040340781c20000344410120b9454010100030028500d40707003941d07490040402000e00f007102e181d07040d00750b11600c818040381c0e0700c10701581e481100350440000c00341d5503c50010141e86a058101c440044000103010500030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 706101501 1250 706100251 706100281
    0xd0c05060a02010b040b030d0914030c030706080103030806060304050607031d0a06061406040819060b0a09020915130306050c120c0408010e030f0304080a03090221010605030d14160b 80
    0x180031601001b1110148050549074605100800c0001c0e49401081c0030031040203030845e00100e006400c580d6000030100100c1d19040054104c031001c115000d00405c00c02d1307480914658805020f40d907c90950425940702541d80c400607051505240c2c55034045154507404500000c03000c114141154156140b40c1030403001050f450296060309054414035031003d013011000c982c112601c000c010020b0080e10000316082141c0300c0801c80321180c540e034020206903103600440380540181c00e40180e0b06c0c03014001b0031901e900404004203c5e10410b00c49214101044040d00044030703080480410b0705c0c2d0f1a2070420341c0a11500309501101003d144c14860003115040182040d40c4612000700300040e944084296280224011200050020030001e0b00154075100a8113003e41e1908021480300016800150003120100c030a50240b0340c0080c10070030f44842405404000c1c84264064846019211070041c03980d50032203100d00c1c00d448001114810000c0804032024903030b0300000425414200b0480e2490040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 706102751 1250 706101501 706101521
    0x3030516031817061305070e0705090307060e120c03030906130504020408030705280f080d0f051e0f0703020c0a06050f270616140310050103060e040c03020d0c05060a0201 75
    0x300c200c00005d012006000309605085400c400140004c41c5881c2850b510000c009184000b00802403284040649003040350308060106900d9854075206258103010b1040301d407141c60000c41e8403210300102c068034080b01711190f061040c1c0345280e590f1400b5654240e00c00940c0e028135000791000800003030140b0044060142d06100d00c040d0f07401214100c6012214100100c1120303200480f0314029000030720300c540103400d11403150f0b01e03517401c3c2038900105100305c800c42d864040b410394a41e01000450b50701030720147c07104040c215112200d428049100d8141e110010405428035030300141c0a003a0084c2007111028080e403004045c001c6140000f100c1910040a8510701156070440c81404910070b001d4071103901c1118030500034030499882048032280044a0f013603810600c00c2a030301541d9881c43c1c40004602c500c200340c3c20368000526190005040b07030030030b034841c0000f01c07414401d1000240040c0701d01412660100e030010546081c84c02c01ca40004003980c011039224200065103890a5019004040c81d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 706104001 1250 706102751 706102753
    0x506030f07080a1a0903121e131218050411131e090902060909072312010e0606030103080a051309050402040b010e010210050406060e0907090c0903030516031817 71
    0x49070130240b100d03503825042c1e40c114020b030030502c50303218401d00000c00ba41d44442910b180313000300840100320840c1c401003902d20010600c1c80700c1705101032003104000484e42403d50b1400e2903034005d6000e100640004240660307881142c81c0d8640c1c1c0601c82080d426a041e030400c8140b000142550381c0c2c1c1c2c0c0c0025800180d850502c244002c0300c0051a04c5082c410610710701e401410b400c0c9040b05403402c001911a0003440d1505004020a40105007805445501010500980c030f0030740c0c40e1507a402d03144c0000016444400300d0012001008019280c40c1d09803130460360320099041e00c6070190481030302c0b140a1202c0300c01080c40d64203800030350800960003842c010b50003a5020030034988810011205007514100c16805a404a034400d002990310380d005540c40340c014000018002d4403240114500030064402400b070398003050f070030700183c00c4038400d40310945c2c014141520103a140d81c0e405050b13806182d44401d90b043e003140c1c00a082c50f00403103055041480c0c00400c8007405803a128043e1403c44140298021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 706105251 1250 706104001 706104023
    0x20f21041508070e0604030b0a0518070b090306250c03050c15061e030304141207140102070e01060c140114160e2e050d0f0906050c03070f030506030f07080a 69
    0x1135420f008040345d0540350820480c0000790b032103406400c05000054841c0c00c004040c41d0300d40321561418000035020b86039400c0c80543d1100c1d590109450408007601035080c03240d10380031034042210b400e1103039180b1080b07034100003040100070b050680b89805400e010b01694003440b140845e84400d14803880e480343c8001c440c02c00035010942c04100c0b80601c0d2610700c030f4041e4000c02c0103100201101403200050300000300150240c0c41002e8815040800640c4000d400e8040c403420110175680510452000e070491f6880d0004c5503240000040001003501d4001e48901143d03414541280400e400007156100c0c0c411034000d6909100b150a545054204225000540b0004043c40240b400814602449804c100c902e056444500ba149200c494141610024444100120030071a1500c0c020a6800a111000080c0a00f01c3c0d04048094a038000c202003a540400c004011045821212443c4c45001e1841c00281c2c03996140007203880d145000d45410001d120700003002801840015002c50368a21a0001240f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 706106501 1250 706105251 706105277
    0x90307121806230c061f050a0305062205030409090303021b06010504150b190e0d03090f060804050a0f0302010e150a0f09051f0b0406081507020f2104150807 69
    0x401d4000c00f0000182500548003141203641d507000350041b41c0c1e444a0000b42010354030000646580c0c00303907200b110130b074000c3c90800c40212008410881c2c00e0902811174400e134070b0340d40e88090b2a0310540c0141d001d001d5071000b0365403e041c42603058540c12900c0fa9198201704050000030b541c0c580c42403140078451400e0860603081020034099480449406500c0d05007000c2c0340b8000c01d4a0000b20002c5c840802400d1810700080ea50344034800e00d0440e010742c68403000c5a0814045100c480c150f5040f28040c03120103005c0c007001440014200810580141e06000141c0c01e030700e0100e014020035030658181b0f12900c5d164910b003520003801540100fa00500c01c04c81540404030351819100003032000f0303143d6080f18049440c0390f000300e5080b4011603101c800005145015400040442d03402e604101842c1e804003500c80700f4076051360182a04054980010720030b414001941e2682c4003045480400c01c000340ca10302080f03c3d40d103201608d000d000252003080c48d02d10300740f40007043c01c00119011000502c503090010 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 706107751 1250 706106501 706106567
    0xf040303020f0c0a0609031113021c0606030507090b16050609010b01020c121908120109020c0d020a110f1f03050915091507120603030201061a03090307121806 70
    0xc4d0846009032100d5001c54034603103401901c110112001d03034203e4213581c8200300e0076030380d48001c050460040c0d0620740710341080321a08040715059000030342407525103404d000f4a1500000d0110445e415458666034400102c0c185201440248400030942e2040302c1c10701c5051801074020b00301c401d1081c0c0c200c071000180c0c1c10800c01e90484880102c46641c1095800707000e80d10004840259840c000c0c10401d02e041c011060418640700245e01c00c6440a9002c0744d460901d080c18010b512000c0d102c1c5c07002709071a0500e52502c0340c0500001a03894030400b100c0740910aa41c491502c42058a40c50242101801145420180180008a60f01d250a00442c481c26403150115136000e4098804400208217801c0321080c80c4044000241142c401d0000d0326000d00e6621000e4001c8501840c80ba038004a0181e1800c601c40c007401002a09130840104140100441c501c80001510542d0350444a50b13080600e071990155103071601013818180c80943c0b550b020503d0b64000b0100d03107c041c425000d6514020005005d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 706109001 1250 706107751 706107769
    0x9090b0a18021002100b1c03030b01091d01090501060305060310020a03060e1e010819060207032109030207080307022d1e01170610030902010909150503060c071e080f040303020f0c 79
    0x4847d540070150320109219a1200f21090010306000313100540b0f030405488040b110103018812026090f006001344141303801540c0c01460306041c02c1c0001d0411000003a180c400c03403888142c1c0e0550105148085c1e5200c1c1c0c1040d070080c1989403e8034928140900e145a000c4403503490061440c0651000080017034002032610315124a8040d1711030404940e070b5409020b1b610566080e010080c5020702c0c480c0c800d40c1040c107000f20315a000c000040981c881d14019051031041c1c0c0c080c50064006002541c00341c0c41d031080e5130800c00d54a25040e406c041004002151405c10304446540050702ca50404160549240c5031100d01c100903240c0c4400d600d007500b0340c00c240d84000c880392030300901d0395105014050300075009026000d205040400c100c81d00c0310307145e42c215280700d103080e52103900c4844108121704082c820740ea045a840d1641e6441c0030321580754200c0921400b1013009000c1c4003180c0800a100da41c0707040d51061904081c225940c1c0303030344c0e0400039921540c4158280c924002c00c0c00741d1449240002d08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 706110251 1250 706109001 706109029
    0x20f0f0408011401031a060406030b0c0a170606040611280c0902040b09091305061303090e0403091e0519050315040209070e0d0c0f0e0109090b0a18021002100b 70
    0x26500007204070b4801b0703680400740500314542103038a0b080040001110105050711451850507070350f403225134002d00242036040c044a521941206503041c40b00d40c0c0c41c2e200441e000d40c0d07403504040c080864441881c1d484c0010410141d0301c101c04000d031541f08205070320000c000d99806904038030155911100d2000c100e00c9184910128040108400001801c0100406070300c05050003c00841da6401d0300c4d9142040c400f140c3c5c0103441c842e40d001c80e00801d42c00080d6035001e451800020042c81c40e00780d43c054845100c0f8041c1c21000c1b160040d844c04900c400c50b009101902000c0c01141010071588044a810030705030042c107210703000d07010b60b500101c000000d800b171086400401c000a0b5448050080d0344150315102065000310050484a01152445107103500a00b22040d203031000d00d191081c503e031281e0040e080750074405d0401e440740340440d02d0710340103641001005400080024050015400c40c088100c0e00a4000500540e18280705401060032a07e03034040c40750900500c1140020001d1071240303c07403 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 706111501 1250 706110251 706110263
    0xf0e0a030515181c031e0509100207020f0d0c03080a030213230f010507140a1103120702150403020d03090509010501020a080d0b010c051005041131020f0f040801140103 74
    0x8104e01c1360a044405514200c80b0700340028070290072016081381a2969800d080c44507103c0c400e00c4510f6004000c100707600c9101f01c400b1414085c0b5170b4005000c4800b070403080d034481c801c001c00102c24032140003a080021980941c0040e556550000054081d411040396031402c4000d005000405045014808290030950302038420484181010002100c02d030004a604101d000d10641000540110f191518a00400b0040000e2181c6103440c14401001400441c0240c1010305441c814102d50000e80705007507812114504602c039000f1000c10705028981c006507021820381044c006164102060b042901c805894441e0750740e80f24401039a070703000355460040c05100e041041410444265002e10b40710700052403c03c621042c240c0b5180d181c4060f80f0b0f2181003495451041c0f20400c680300f8200b8445620075100c00d0861045a50205598100303101d4000e050100d91001d41950340303050307049071150000ba852090721031421a400c03003615081409500310641ca0448064a91006842450704a0390301070 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 706112751 1250 706111501 706111513
    0x412030f0f0c030309061e021903060f030b06060d05040602130b0c1b060d0e0d2a0f0f1401060303021905061801020705011e0b1f0f0e0a03051518 64
    0x10f0f40c110b0003000a000140c41407550b40100d842103000311240c51055494400f0096252009201c43c5180a4a020195414145052010030802c00c2a280300c0049a0300b062802409564000100301a44502081601020700d000d00700810450990301422102e01d0030003100c4c441c60389410300e604280c410000e200d10701d503000006001d40303513091503a02c2c0700320319010300010309181d000031000e011b5600050388602c494100d100b16070022940003201c81543c102040c40d4424503070506200300d491041c04c600103018003454100300c4043c0842c00324407401d41c660200001c0c41000f440030055009000b036000c1140140a21101003c01b114040c0f90142051b810130041c0209803103841c414440c4034170907400c1440d90b54003400601c011420038800c00300180300e906048000a850f890f40203040721140c4081d1845111400d03900044c9801001d03050111055074100115554428601654141481c410b41a4001a6090013004120000c0380241004500c1484404151112a2002542c131405c5030904401c0d0b11032 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 706114001 1250 706112751 706112753
    0x5012309130c12030c210507020103020304020616080901030e060c1603140418181a0604090b1503011506081b0c19021e0f0f03120412030f0f0c 63
    0x2588070004003a11590740303000c040e59180190216007407101400d6000c1a4440c40d140284111200d440024107901098051407005043d40588a4000d141010b4101a8013000107011901d5900442d0045011108210094115890071750003590098036201c2c0043c2c1032404c0c811418500141e01406001c0c106e01c07007410328000d410181c60041c84401c003541040a1500310f10486408580140b02030440c0003550301ea00d910003400c00c4150380311468610784108640190601040820002c01c0d0503840d054501c0c0320130f48072000010003900c40c01714040c00e2040c820003401a8903641228100c02e04c00300b80d009104410244400e001d880b0307114803880e004907062800040140643e107030321424050240c11014104403102c90391902e00807403d602009010811f10110f402c2d0700d03180200c8000d0348200c00c80d03040d40c0c04011000c00e526888040e0783ca070003201c1e4980780500340d80d020320980140e04a9880340a0301c1d542e5920409075803090000d401d07000b01d20703030078288270003c0e02c55010541d0820040d1503441006060f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 706115107 1106 706114001 706114021
    0x1104170a05150112060506060904020c010e0c0a122607030c0c080f030901030b03030705010c0801060e03071211031615080115080619080102030a05012309 68
    0x700400a00f045400356021085d404100428942c6502000c10024000c045141d94460700100d00081510703415845229050b6080d000c03581481020740910407050a140220a0300098403081c41000c11241258103d041d08400e42072400d01c401d15510901c181c1201400f280010704e62a0300f0b1003404045a9054054114180642006080340d0f280e19580c2c440d01c0e000038103058440500c02c202c0e41e000d00c25140780310341000090044412022009042c0c1009002d10002300b03600c95800701c010f0400251280640b81030451210348858151104d141101007481d0a070b506200304d02810921140d6422a0070040a440a010701c00b010f40b07003030240c04614140c0080000d070f02a001208082503001401507006202501c040c00c40c0910340040c60311900441d00b2a008940c0008148500704043e81c2c4094100e51031850880c1006c070ba03841c0340c0f52090204443c4030303600034030020200b1040b480d = true := by decide +kernel

theorem cover : BRFrame.Cov 705935251 706115107 := by
  have h0 := BRFrame.cov_init 705935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 705935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 705935251 ≤ n) (h2 : n < 706115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
