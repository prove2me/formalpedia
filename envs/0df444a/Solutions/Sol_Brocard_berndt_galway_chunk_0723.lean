-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0723
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:23:38.525737+00:00
-- url     : https://prove2.me/submissions/dc45e8df-23b4-4ab9-beb6-16832429c961

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 129856115 ≤ n < 130035971 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 129857365 1250 129856115 129856121
    0x90105030a0620120709050d0f080a02160b121803070f1e06050612010e03030606220f05030f01061a0c0115080f07080309090117120301030b1503011e0f 67
    0x401d8183c01000c07420b0140705202c104040d200e80429902d0140090703a650601c09420300121001c1d28a8140050f281d001c12800301c0108010301d12031048403114581d02c852032406400541149910b0703c00000c0402c500341032482c10300c0d00f1000540c2c1d040540e44401c0709103640d80c89034403001050010651402002e000c018050365000c0c0d07200211200c0000a2480c1500017071004545503849041ca141c0040c0c96914144120184800094001c0d4550380b01d01d0100901c982101090804c803644e8900d4024460b14040b844c0c000400203a032600003010305002c205401c04801254801c5260715100d803c0000341204005200c1445030b001c80995160040e110050150003400390028041c07030441800907810500155914062405005840c0800c0e200c1c01310b1900c92140c10882c607030001000e0014800c815545c284141003003042402c544090b001c285c2d4608641c2c009074020344411440008101440440002d1603494500440c02044800160343d255a803410b05110420421541c4031800075400c807070740e8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 129858615 1250 129857365 129857411
    0x30b06010c0512030a14070807081305010e0307060b061e030a1103041214070b01090e010219020604150908070f080d0e0c040f05010e0c070807061107060506090105030a06 75
    0xa60390441024285224554805d031440700d481340c1390030681251450300e4806680206041da40e5400103440d03000e400c80c5d001c00040c004054400c016008d100c005842441450060302c8420b0180d51500d2207801c20404440000352000e00410007004511142c1f01c0c000824607000d444807603215100c2c0c5030400948000e0042030204480c00074000184000d02000c224610490252541d070100f2000000c918100700307000f52240104400d07807a9005101207404c03900915821503010000500700542010003a91882000c289035001da084001840b0500104101d000b00d031940c00c2009005d442407a503150707103541c4580000030b0180c4800d02c2464003007202690480d0990f11200030240700004442120688444181c1d41c41413049151890740000d035440c6014885c102d805652100075995a141545000781d400000e045034038440401c012030018413188203040014010316070b03068640d9041d280080480b900a0003451188860310010440b9940004800d000d0701d03800704001c2800c810f040408411440b5403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 129859865 1250 129858615 129858623
    0xc1502130e060a150c02011103210708061c02090414010c0914090105010c150221041b0305060c130b040b030f070c030909020c0c0409050705040b0118030b06010c 71
    0x800000a511403070045000c1c0180400c584101440c0c3e9102c240303054061411880d440428030040c944400f643c098403122443d12400d10941f440d26094200e0840d5032120710031441001c00c0c1850502c030b261a03210240a510046c242c40c0c40c1408001d55030240103420310300900a104030700000010302080f007030f0741e140c041c0c2440b900000d10241d20142c07405440359442d809540071482c40080b1002c0c00e0701d4140221412900183c4407201d60440c1503c95100b1500014074041c0000c2d0200503440f400c0c1c4208441d001150707640c0d40000b68074109440d1103228800e20b41512100761000d2402800416070200f415a0040c0301000b01590b1030401504400070407900b41e011100c1014080b5002903010b078150003d510800703030382078448110358072503100307440e010001d8501a00143c2001021301103014146d0060001d03003001c00880742203a81d02c800050030b07104c00000885854000880c100040d04250051011242090030085006503148482c0c0648507802d00c0054003160454003c03e016034011042c1c284010b0b00 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 129861115 1250 129859865 129859897
    0xa0602220602030c010b0904080301060c031e08070f05030f06010315050a080309241204032c0a1d060f0f030307031710060c0209060301060503030c01060f0f060c1502 73
    0x207100000382d01c903001130380510102d50801c9803030703821031502c000c48034480c40d03020741c1391810b507403c00c8011907850114010480c2402451282003441c40801d012114031092191349400203480c1507140240081d80728000d50040c00000d01c107120102583c80c42055200e8420b18000030084140315450b17041401640c013203038201100c0000898410710100050201307400c00c1d01e9131010280078080b20901650448031245030b000d024044540c07290700400da80b5810502a161025045000001d800300c2107281e80021510f02607034000d400110704281e0301d00401800c100c45500c034138200b261403560031500001c08092080344c40d011111b4055403124900843d00d00054120303910b40c5070074038000e0035030312441603066801300401c4001078410949850a01c143c81083d41c410484001c19401e1000c92080a00407035815500c0710404a10340d1410006080c14500100c0040b82c59444d200c12080b080c0c443e900f040c1e03905095400c0c144407440e0049191f108003a03105021180d0003c0701c80b4800000c0c0202c90101a1400c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 129862365 1250 129861115 129861119
    0x30405040f0f0c09150e010e121c1e1803082d040b04030b04060f0c02010c1b0201020d0f02010b030615040506010c020922080c0a0b0f090a060222 64
    0x140c2d901560302e084901000704030000100d941039464041621400040114003210b95100c203210f001000780507001810a0140c00605c031b00081c00b0030901c15032840e410f92001c840d100404000d103185c20003c0095003044440a902185021010b03010580d07410103100384041048101203031207101000440e044856240c07541f24550046458110700050701300000e0417501a55a20300403502100c00700d8514420481c5028616501d00002100052003620401d9031044842d100c5030a034050190300c1802c2e58000564400384403400340c40c41540420100001c1001c0501e500144d0300055030003000200d508020b444081d42040880c090103d440350f80c1d03018000e103014407030700048504c440402c3c100108c1e014092955200b00450f600803803010060b51007490100401d052603108007081c10011900001817a42c582242c81d10346541c2c2c00881c2240c0140c1c0002c003a0401d000d9580107080c5c102003030f050300d10711a0030041b00c46686c690380d804c0d01030189076000070980e50344041c0381c42048030300300000241940d1607 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 129863615 1250 129862365 129862391
    0x9060f0f0a180806100603180506010b04050a0e010311010c0807060c020a0308010b130302010e0a030f080403050c121510050d03080f2a09210109050705010f0203070f030203040504 79
    0x1052008040340d240241c2d40340410600b0b000308084e8850301d11030546031221841d10600710090402d1090044000c0e04041d07480020038002e02200e80a8aa09500700c1c0d07442c0d281c0003d02a000140d42e100800c40c0148000600000d2442000d440d044c10007483d02c0c00d10600c15080c540700e6440b031800b0050000d0726103134000301003e4010400b00704107400b03034403800d60340c0e0ba0350a10380343c440c4542c4098801609600805000541c0231303002c0c610403440041c06d4a00660b0b1244da5920700060b80140540b041003003c901001088010459200c040c0400e464114652880a05150392404505488445183d02800154011038044034001c0100782c0102604981c055600303024101c800d081d1625861002800700003860001d5004030842000000b0a410b9040420040c20381e0980d0021000d4035402130081c4400300c0010560b5000750180b07562400009813860721460304520300360766940564140801a850a2851034011095888664006401d440030b007805203001c03811407080340c03c0a64094a0a400c0030305c90303 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 129864865 1250 129863615 129863627
    0xb0a0f03060f0516120f140103050f0a120309060b04050a0203040302060109050c0d050901020c01050103080a020606010e010c0f02040608030a0905040b030f0d200304030609060507090b09060f0f0a 86
    0x40303000d44002c206030340300e0188000545004544440140200b5040d00c1100d505c219600c1061591903440020003a0358203407110f040e20f1030035040c00c103410703940c0005009009043c00000b03a0700c16190300902c00c071a1a6a50042a85503c003070400034982d480440c00180000d60b00090910400144100840d01d020310b00a03009420a43e03083d0010310480c0004580491140701d20390040c4051100c0ba4180200c0b1880b040c040c1000804042c003d540034010101003c5007401694040d5124040031500c1d0101003038028549038004051504100780041c00c00c0850b600900601c07580317600b10b10f50003103000a90000c58043c200f65070180c10fa510001841e01d0300300d907004400758265141183c062081c05282003c165550b06a9580c8a43e5904224149a9010f0044401d003480e41e2500c070080d4540c01c4580700c46130554020340d1040d20745984810b00d030401c2100368401c00e5400380441c14044522410700142750041e020706909a8018640050000f21508050064802c2204040040c6a54011441c1d00030300d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 129866115 1250 129864865 129864869
    0x90510020319050919060f09080405180118020a03020715050108010e0321040f080a1701062d09260f0a03050901180503011a03070b0715020702040b0a0f 67
    0x1a0108519034034040a05401401d02861408008090314174400405152041a500c41121190382d100c410781103000d07543c01b9130242a400b40d041d141c1c070780345402c040c003805501680c074840d0707000058801880785180080305641042c11400340140c641d8018070059000f84038200000c0e0a05000d001071500100c002c1d00014141d5135450000e01102c501d09013095a24001d4820141c91103e00741200c414914020750020341c4603000d45452010801961036440d095440048060005204604144d4070034200b140c40da4010049417528070f0403240340c0015182040210880701074514546007540030389503c104020000780c00541541e1204414481540c201d01035106200d00940c044d4042d07020940300003285041030f150700354490524142007840110380404081d160107503003c03040706000c151a2001d00c6291201c600240341e944600800c41d041501c4c4c2209070780682d000701800c20803000091280300a020a083c840301e000768592105100003006001c40c2d80c03025400108480002581201500600301 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 129867365 1250 129866115 129866131
    0xb1b010212060a05010309030e040506030312070509030c2b03030b040204120501050109020403020105071509140d0809070b071707060903022a09240907020703020109050a0f05060a02010905100203 86
    0x520f03a030b90b50005409403400d00750b002d804a000c13820030304500c1c105604020342c803240050680385805141c900e0703204641819a003070400504041600041c03400c041101c22501007040310000c1440038032101c40308500d07140b40b03143c44042d1030b04100842018080e40104031241802082952103036110b01c0d01642c209988142075801d50b0801c0000510051184212400d494040c0d60309031800c40b240e100c891084000852041c0e800e56101450700c0464552400f030013031f5081610140411f003213140c9009150352409040c80055030008402005030715032810031070302101d60001c111300b015078507000c0c07405a60040800c054400340c181070150007015408650328917001080300f038015181c110a00030558002104109641201e000e2002c80e1000720314105001000302c040300c40b8802c03003901c80b021134141c0c0000d64240c4003580c010001803046681040303502029120540c0c020220900d0400d4601c1b2100840c03085074066000040c0d046040b034801c0d000f1121580c0c00c00210380c00030892a42c400b000b0751084654603 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 129868615 1250 129867365 129867379
    0xf09022d0a02165906101e020a050d050406090806070c020d05010b1306050103060501022d030f0c0d09080c100f03060e010e09060711070b1b01021206 66
    0x2036054075503c010340b8156480c1d05401090a40345440a15042c40c4500202a02003d940c0b50b01a1140000b46a6184050400030262401541c1d48540c503407800d01900c0c803445203008880c9111080d50058050b181d6808020480b0380140440400b45c1c1844811040034015005240751002d0b90f40c1c200c0300810484501d80e440004195a400e8420340300d80041d242c14001840302d0802c60b015140c120000ca07070303203805035000203405198a00014007040c4003c620141da20f440d07900c104910368251180c0740052500b80040c01c2500d0b884040200000b0b529594040d10300c500c4413401c209888200240c0e1034000801764440d58405842840a5036005815002c800252202e500400c1e400720204840c1580803020f0009000c8004c081001c0d074940c0c4003444c0c0401091b90f00c45000503000b265019440c000c4c00c004055201500b0542149400c10b40028001014003541c00041d1506441c0083e00c003080b12000f40509840307410303001c045041203150074407002c10740d07002141540c0150b02c00040c0070f01a031012a006 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 129869865 1250 129868615 129868633
    0x130902041e0f0b0304170f0a0908070815010e0417030a0209030705150d0b1302040306050f0a02041521020a02010506090610121805030f03100f0f09022d0a02 69
    0x24448107203003070091441d1040d091001c100054401151220746c500b12000c0b1600346401c4162078500d6401010246e0005a984801000707201802e02102c00a0f00032400507004400384030540301d07004841840740c40307004a800e600107400e00c8038a04060440d07524900590743e4904001e45d001c40a90000a400b0781700f8010781000003414a40f04011885400b00940094141004103034054028a04c1c0030245800c00b08000c05001e800320a0310051020f980f094000264605150000d17003080007000303040c108600c0c41000184016065884071401410480ca041c1c81c0c0c100304031160310241c0301c2c02420750101d02e0003c541c4135449901900014801d00040d10460851744d02d440400c01d4828440d403603075004c42e80d5451412280016a08076000946c0740900804401c0f4003542c601d45168049084003e0860002c402d021b41d40010524820040820841c842402414103007a003c800d0b000d1302c90444d816a001412102c0800300d0307007486000803d0701d0180c064851030001e004545030f00058030b0400500540e068 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 129871115 1250 129869865 129869879
    0x9030c060f08130203011e020403050f030702010221040509040605071d091b120a0e190201050a0503060f0a06020c0111061608131401020d0b011106040602130902041e 73
    0x2041900740166680c0c40281c44074940c0719080c19040806903015500e550300d2544a24500d00c8520050360301030307801030b6110b141d810038505149110f03003503a40980040000f040941c0e40044d0311144c1d140c074120181d05908007006181d4041c820303135002c0780e08112210100001d203c1d841c0e0105215414a84401d08070b1250868403021038075501e01c040c0d5004000c8000314001e209031042807141c1c0c105c1d9854031780c82c205200000e0150305408a54603200285c442c403a074400c0c0101030085076191030718034140415820b015800030380710707004280503042000070110000312566540d20080c08130802c06030200b0302403520b4100c000c0d02e4000c5602030f0341c0454031800416a0140d000540540705078441012600358031103900044503504800b404040e101d00b14030f00e4500116106290413000c0d02440c9000507034071208408650196a0f4049019040c013822407039081c040e5101207012980b1039413000006030344945070985030282030215002035194902c0800c0228220100740342e02c1c800b1020700c290740401190b85100c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 129872365 1250 129871115 129871127
    0x12080a120c090b0d060305011104080708070605030c09061b0a060c090521010b06040603090c0902120f040c1203090e090604120c02060d05070c0c080f0d1d060a09030c06 74
    0x25801c0c005450804104003a26525019003110a09100007050785a0f40f40c940e070f400c0d41c0d451550031898420004042220010400850300100f13141c6019009040c41c0203009080303400010300780b0b201101d00098002e200c2c1c0d00c4404684d00c05161210b01407038003040c4940144c0d50340c2c4400007101c2042c603000150007610b0107180346200311040240901040a00070542c146a0803891420134100c0d92141704d25031099603402e0181028107503a075030000718041141080321400040340c1c003800115104010301401c001c0d40c0c0c000e40f548040c03090028540d980340c81c0f5051922048640c4a40c140c15180c451000030164030075200c2040b180d600380702e11550b442d4198200d40301c080039603000b0403050744844268106070081e94110b1240c1c0c002090b050900c45c3c0c0c0c07400901034540807600b810020340c6000749401000711603c0001c002d001494001c10b644140c03160741c3d40d55061b40040e48000e0207010780855000c441c1c04110010b108a02415072078450004200240c0981603500080f82e80d9a072200010440ca03105407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 129873615 1250 129872365 129872381
    0x712030201200c100908070218070909020a120e070305010203010b0c0601090c050412080f070f060c03090c051306030804080f15042301090f051e07031104051012080a12 74
    0x3d01420b404061000c0800040081c64001c8a1000040c800000503a8504c0f0f511100c10614100b014298901302400415520311038000d0541284180b000c1212254440c0303c01d202803400c8031000680c0c80c8412081840e2a0b01070340001c00d103600000000c54083c03400d0002d0300321100c104044907450b903240c0003c0c030141c0b00310351548800140c0620003002900d00b11042c60514500404002d40b420138962141d483ea41c4c444041a44c8ac01440e60f00310027001030610900703084145500d810802070690783e581c41943d0a103841100d01c1401c6184000150343d4455008000840d40300c0869035499985d03074680381d201d011000e2210698051200c004859104601c044e0b0700c12580100400302c61070075028161699000302040b03188941d1396401800000d0b042c500444681d602620003803807070300500100c160685c090540001d5458101010810002d40003940c158008007088502085076039849501d0310007402294002a0804120080701c030510901c60000c200f0014280c0c1c80ca0181600300c10081c1c203580c115 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 129874865 1250 129873615 129873637
    0x31a0105031b160516050114031603020c0f0a1406070c03050a0815030a111905032d0a0305030a110a0503040f0615032102060c0d050702071203020120 66
    0x318052481d80c450200041c01400c2074040c10200e03d42098a42e10b213480104a25004141c0c64403906000541e005071102d0480f030441101d0f1444e42c84c0c490306a1b4409465045d20b14180354001c212510024020302c065040c3c40c00f000100d5581c8070440c10070015000d8186540c8202d4010003000c40c58261007581c0c1101e0f026010340f26946443c1c070082044940100003002a4000c283e81009180150f409000600b40c03d401518007108002142c820403100314400c1c240d80422480c80c2c9001c200355180450303109003110640741c03900c0c0c2422041c4e410700750311f030001c5c0c01e1042640200c0c20300e03c0c101900480910300602a900003003104240c140740d40c00c0d8601c911941d94010038400e10016000a01511b42c4501700f078450300780450a59070342031503804000500d0f0800c6806100c4044a250200c1c42c0c15510010102144000c0c185030420140f941c00c03910403509090026070b1030342e00040c2154003c01c045001484480102003000301c00d0b0400a000b0301c00441c580184c50180e442d4005140f00c544117642111903030f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 129876115 1250 129874865 129874891
    0x11b020111030f1302040204080f0c040b01020706080408071703040b0603030304020f1314090a02040b09010509010b0c1f0203071107081c020111030702010605120118020d020f030607031a010503 85
    0x81d1120000c1041c1c0040007011302640450741c4400689032400504000e11a44008000d4144241c50590900c0e101004c418011460a082c4006507a800210300003181c8807420b284d20365450703508110030907124404014100030121030390900c01c420014000d62050b401182d04c00b03800e40342c100c200f50300c03440140c501a50044c403a040b504014985000f5402d5940004200040c0c02c858105110314400c00c1100d10303540720b0304450003c60a6041038060000c88801c111902c1c8882c0d030404001400500040c042c900101300301046400c00c0071410041003551031080c542c07000c4c208400b020050043d5004440c0000080e81c0d2001e418002d2800180709015503007a80080c20520ba0220180310480c2c00c401240c800719922521102281d414650045000f040694000300d1420300709030a000481442119846442e8941180d82000616141580c10034a44c11149040401d0312400010009000010010b51600a400c00d02c804550194040d0035000070203800b000103240703101c0041d0ba9500045440c0a18910 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 129877365 1250 129876115 129876121
    0x30d03110a0806030a14061909050303011a0d02040902090103060506070203060412030f0905030a080702070e0402011b08120a0f0b060d0209010c0b0901020309070b0405010e01080603100e011b02011103 88
    0xc0548040b59200002a048030001ca81503128003010701c01014000d0290f4000405120300c481c14507001c1c44a0450b800380174001c1031055540c0030b40e80c0c8414031482d0021000c54078901b040c024040d00715190300402d01c100b5500e81c2d403100d4030030b0001c1d40f02c689640c0c082858100c0000f02c41c14150251100706400602078107481d91681c54441031010a10180710400d40e0b035400340c00c0300000c82e2040510b80303400b4000454860b0a0314a018001c0000030340108107552007001d08000300c85400d040c0c154050b40c20b10340405105207076958101c83c0d0140000050910b070010131407401c00f84104040e10312a8680400070304c9003c030300da41400c049507040308606400c101c080102c4d440c280307400e80090580b0041031400300d1848245032103001469a003601c100c2000c0c0d400109000c00714008000c200040d0206c107003c0341ca8503151100103030040501c019858144607128001586940e42403125a07000034805200b40611491482510300070700c85160300025007446c00503001d0300944148914540c3e180700310542c0745591 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 129878615 1250 129877365 129877367
    0x30f0d14060f031b1504030c0305060606040e01060e0604030b010909021e0d0803091002030c030a0b040507091e080313090509070e2404020f040806060306070f030c051e09030d03110a 80
    0x103008050151340121550100c4174005e451580100000e42c080d149069031b960a5103411030902074041c05140c07280e48240b1041c4a05000e883d01181110b103c3d05042070003201900200310b05005507440a07001e10441d40000440c500d080d0004580f00344211481c2181d4040501c00f0404c5a4034142c005402640080c080741c0000d100b5002550420fa82404503030103550482c5c81a003e9a00c1210b070b0010b00d06002c41845601e00c8240070317032480001c00b110140000c0c9000d4100900680f503600c034000c8110076003100412040300c8201800003800d914001ea0340d41d40800003440c48200303204e00ca010605490240050310215002c02c020301a01c4000c0714251850310348a00c3c182c4485074030140c9440404600103103039015501c5c0d01c01040b14274208010360362a14030f400c9050f801d22030001c006078065040b001c00c01407010b500c60714804207d03926040016a034800b200c421030345401132054280030842d82c460200f1000a0304005403201c02003c4040700c541c01201a4101c090b03030038111001e014010140300c0d6100301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 129879865 1250 129878615 129878653
    0x20331020a3803010611010f021908010e0c030408070303090507030b16050306091314011509050106081504050702070f030501090b070c03050a12141f15020c040c02030f0d14060f03 79
    0x1030881b180045404034440b041502260310003204807646a41c81600e02c12150703044151940108074505143d003035803608101174842c44c40020030061241600154140070076000c0da20100c03400d03812504541c8140c0c0c03a480d090255000c2910951000800e07081e9040e03d2a20901c100d0788101800340080c185070300d4103250459031210243d030803070700742668541d03035008210240304050000402180038034a071480c09100f1011110107800140070847c0e0780040210580b4042150400c0940135a80002c207a61982001c90903c1c41da0b4000340e81e0019a1000001404015000382c49498001c5010b01c1d03881d01c03035000c10f0701c40164048009011503800c2c0202039180b4081d00c180d182d4609101070204115518180280f01c10000312a200d0413000048c1d1240380402c0c0c008541c9000d030184403000c00c210510311074069500c01c80e60780310901c1180c035420170910642c428426148400d0442e0740c5140c039000d0a10130400a00003102403024100d030690002000740c03a10607401141d8542c00340c05015030700f030074600910032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 129881115 1250 129879865 129879887
    0xb0307050a050d02010504080d0c020f0108070815060c070602060414011506080a060b070f050d050f120604020c0607020a210801092a0e13020331020a38030106 70
    0x148002400005150682800148889e1301155543c4015108910400c100640c0c0d5464980c10044107804004502c0d8000703408a401108662107140000702c6c840010b82c00d44110402c10909010303540300040c28940004100d0f01940c403c280c88203d4800008090b4200c46441100103141101d00f101007240300d001d02041c2e9045000c601d00810060707182c03110a1041d43c458542210b031040d02e245d2030002d000040c44445080805031504528240d40c408c1060007500480400504442d400303404110155203941c121a0031907140003d4800d01d20f403e68010b520b60080c61800c0d0750150000c606c0e002c0081c41421166003180ca66112002580d017484001001040356a10a1100f84c2401c108516030b4190000d200400322559560000058004010300c40d85070015a0b030569214014024441c03929086054529024440480c0c62210350b0700c090342e0b500c1210b030fa200203508603e10200c0400d40b42c040b50854240300100551641c0005143d10ba044075034800300d04001d030444c1e0f0500051140901c202c80ca01c1c0c1c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 129882365 1250 129881115 129881117
    0x604030e0108090c040908042309220203060709150503010503030a0521101404090804090e190b180a1505190501180c0c03090e070c080307020607030b0307050a050d0201 74
    0x13100103035008a81107404004043e43c5c01e54001c102003000c446522010084104000f00f40f1240051100218031600806025a00382c00c5051201481c81c2407040305050890350002c00300c8ac1d0320300704060003800300c21040c0500f61054065003009400c040c000c2d02140d048442c094011450501103007411900ca400200c400f442024074401c03c13460906003154064040c4030300c017a80000312071400c2f2901502070000508036008605011200022544031001da42c2162640b080128082d546213808a0a290b0300c5c0320301130400d410741105c100900c0070700d4a82c0b9100cae0a80c5104850060a40c0300318503903484030580c0003404d0781c601002d25001429a80c0000340c0103210212606200b0188801281c203030344090b080a8902c41882d20300b103440401e54081e100100d08182800005983c0d651002080102c40d4090010007010301004184002e100d8800320b00303050b40040c03159489042111000b5103582044d200f1030000790901e10001a02e1030003146c904115040106042c3c43e5a1030041441144009044240c0c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 129883615 1250 129882365 129882373
    0x804030311040e090609010c0309050303010b0a02010b03061e0a180f021309031d0a08071703040906031b05040b10120213030b01170d050f070204060305010f020406030e0604030e010809 81
    0x40d01520f0b00d0b02c55000390901d40c068211031521800d1142100c60b1040d1fa141010f050107400000300b0000302c122815504040000d907607401c1000400d0b805001d4091080d9014442c04080281c104583c10407107404078014500716050391250043d26003900c00e9190840c800115440000f000209840b4414089034800b403c1d460040c910341c03054004035000d000c4250003050a20003443e030346003d920301079146183c0c200c07000700c80c035402c2c001c04541d03403c00ca01070800c0b030340c50040390080c001344104140e40007850b03083d4003884190b0304c915200c007101c0902e108412158a40d0340c0f01145914141c020307420345100c081d004003034030b01c5184030489841e0000082c01c003200303908011890b1045441d51910016500920404034035516007414100c4481c0e20324009046a04115150703d82180d0200444043c60880d94565454203c280001801020940c4c4020030a61030242419040f8550341c0141040307502d907480402401c40d8001e0b00c03a0701c44904690040c0016151400300c51958042d010345900040d45804803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 129884865 1250 129883615 129883619
    0x91012060605270d0506130203010f09080a080a0608030d141006050a05070201201509060606040e190c030507090501021204062f03090f01030b0d030806030f0106090525080403031104 80
    0x840c1402d071b0a4500c6500200b0344103140c01035017000d000f6400768807008001040050656122119180200c400c03030700400bd2814003241e007142464000384041d0002d04290307940c8a200380042c0d0300a0082c0d6016940b50b500c0d810019080a05141c81c101c1180c0164403441c0c0f030003480450444581e489420101c1c140106400d401154000c80b0000d500c2281c03144005006c8260303414800210910300a205c0ac41c2c0764828401c1001d0742d114441901c04507100720320f80d0801916005020a016044107104480051900e48212142589600030601440d9551103580b20300b526600120b0700c03a01200d007032005090040008102c847e11803511010103021809440000d450001040a0500b20303842011003660f00c00b00d80013000b4544500c03582000a02420200322404121000c1030300000c0b081e001600b0701070130600040440e00c090000d582ca0100c1c5000030003c0c01d45a5104100078442911b28041e01d0011581d4024100103815250704012b00c540c50714185540c4954080f030280c030110504003e640d40038000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 129886115 1250 129884865 129884873
    0x507020c040e10020d0606090b13050906060d090b0106031d07031e1403041d160309030201020c070e0f070f090e07170c0a080a020a090306020f091012060605270d 71
    0x45d00340c070301480b18040f80081c9003800044c816802c90700710503031100040001e02030f0384403050302e040221003050340c000303031b5590f80c200001d1224018144094010f50a02d03200e03400300020492003d05070f800c25101048402e10030401840c80c41c07a1288038107100e500060f41400414801a4200402c9101d402084203c00c983e944000c607548001d2922001e69001003000d10448400403151451003c0301d80500d40d13585080410405c1c9a40c5013403001d02410b1340c3c0c0d08a1005c1c94400c0d011101c2d006c0c0c42804880001d5980d42100d0003464045034070342c1100d946000400d044a214990150800c44980c0d600306510381020b00441d8114400f41c00e85003800380701001c04500c01e480b200501c0c8111424154251a0702d042d49014000d8a0300409885856204010070041039400090082c29070303402040068540e031210003844113a00c5414209030303010800a00520245030710158106912210100910840b641c8200940300c50140c0400c18010480c1e8a4280011103e20090400c02c400001e01310000c0010980b0707 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 129887365 1250 129886115 129886117
    0x20310030203120d050a0b0d0305090d0804140307090e06161106190b04060501091806081c0f02010605030c060f0d1407090501020601080a17210610030507020c040e1002 74
    0x100d02c9a540c60204112030302d130311980308803a44420ba0756024803050510780c0004405140c18034004092050101e01c00429840d44154804859400100700b680c8a460707000d00d840808981c04218428400c032131002c103a64101d030141c0c201e14040c80c0020241500c072001b03003440e48031031441d210080050442e4140700c1c1c0e5001300b1049005002482e50b4600c4580c2404048090760388050f1154001c6080420820090340d01c10194412149422480101e00501c208658068545640100314a00c181801c1d030704031100b0f8012040c0d00c401d098076210702c86103010348242c0c02e9841030301ca4a503054010010420b034a00b0301d54001c102c14080443d079a86084004010b2500b00c070100d112802c903a6002c03400300054590041c0e0f40b400900400d00040025600d8a07084a540b004204801402c1446c46144050b41042e440c0960b82c0600c10101c507001e101c46007118008050b030044580034030480e44c0303010b201712141c003e03c1240c0c098201c0d940544410188071b410300c40a0030101e400c7d81c5032441001d8400c8264100c0b44 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 129888615 1250 129887365 129887383
    0x209130e0f0a12090b0a080c0d0b150309010605180a38090a020c07120807171c060302100c050c0d0b060a090b0108040618080307051207020c13020310030203 69
    0x7142030004241c10b03c40007410040640c10802008008001050702c09401a0805901c501d80d4400d4a03a07820b1031307080281c09400841400c580005080c240400107101d840040e6102e200500020048242d4507020414031862a030020102001060003103080f42103542c01600d000c8010203c546102c8014080380c805d40c201c2c450000e40440ea105580008030b1038102006600b0000a800c01e500f130043c103c841e26110740c418445d0150900303060300d80d0000c210254041d0f600c81074101e40c2e4804900b0382d074a002c031015405428510900e100d0390201c003e0300409031080c5800d881d0042c1825070008150034050340c820010349810346480c4608440d40b812a034034003140d00e42651240d00d03404034600380102030110f00281a003040c140c09082a800500c0e07039078020b41560b409034021101240180400701d00d0804040c81c0d01c4041d201e4007000040190303103a0440f0041c2003140c050030512016603146c22040342c84090768505661b2202d10301c0d41400e41301586070007458021040081000c0415034030350000e481c01c0d041c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 129889865 1250 129888615 129888623
    0x2701090b01150305060102031312050709021315020a03170a111605100e0d050a0512010f0303021606050f130f0e040213050f04060903030b04150512010209130e0f0a 72
    0x3400e40c103402d0301d80c14094560000e60030300096082c05009030503094105180e000703111011000e10380400a002c01082800010200c04074119030340c8000d118400b442d40200d00600b06840c42210010181920020300f84100302e4055840c25280743d800010300d00c00d5080500300050440d11215881c501d440100d00502000c0c80d6901c00100d042180c0c03a0035401c140d030352082640c0307807480c0c18001a0109030205843c00c83e5807951424940d110921542500d1502644030920300d581400030000c03801c0040b010f07400040d17a01030703000ca81c4000d14003020500f40110781e006070f00001d102408110720524041c8040d03d4412146a01c002c80346461300c10103515014254480701c1001180014001541000707601e814010845000900107480c0031104440d4054026100600155651000c1401d0620a078840d40481030024001d021864001036091015041d40c003586103c2c0064901c2140c511005100b04e03803007560044d103c0c20800402a0244008001d401145503103401800e110700000c0c207050201358850340c45 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 129891115 1250 129889865 129889889
    0x601080c01030501081507050c0303090a1109100e1003020d121701030b040b060109090504050d020708030c0c040b060c070603090510050105181026152701090b01 71
    0x50042264500385042400c0360602d442c080040c0f01007000403403c00203051021508165036141c000e02140d00e80b0840e00d40c0c441600000c82800840140840c201054500035040c00003807512000410203c032900740c401880c3d009841c101081085420424140e0112018803d080d02d06e9994000c107101c0f00d0150b0f001c072402c0024215141007a9041014100340c0c1d03c0c1010008030660450b541c017545810040d01c00340c1014400800254168820403c05019120001c0240100d040c01d2074070707a59480c8408284009030140000c049542c660001c203440c02103c09500400141011405100003480c0314098542c00c140108890f03030440008002103c002c1c58107680c0010494102e05201c0c0c20b060100700d480d09982c0c104001080035540e04584c004481b100c010850000381c0302e004004400c03030241c4d444110001808201c0c40c80d203c8a084070319060290540c151085100304400262440e582102d55060341e008410301980d481d03070540b000e6400200c60200002d031042603511221500602644119a4640c03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 129892365 1250 129891115 129891119
    0x50d030305180a02010f03150906090b0f0102030c150c0d0524040218011b0c150e0d0b04030f0203130b04030524011a0d1103010e0112050a080c1e0601 66
    0x1e010701c00b0141c02014040580521440d5900080c0a51000d1017840c04040e01d400710407250031410b02c4008000d010452040044036a1112a00050716040c4041407180d06031758041403040d4008000c4856042c00003002e0721502449441b14505640701500450b0303002d00501c000b140c803950605c207450282c0d048005448020311211400c01c00d001c002c1c03001c6d902a42c010310102d600c88604454005100e0002d082c41742140e00240f2400c41781d5070007950080c00d8140d50000000d0b20300c3c00202c0319002d01c8182da9442100702d054100b031001c4280d02c0a401041044118001808203200e009054040050b603c1070b2840c0c41001443c04400040340d4200c1070300c0c440c000408100f0041d0402c2551500c40c611442100750044018428201e420b05115034000d1303440d4414840c04405140084400050540030104904440c92122310b0603900240510300130503880100100300c03c0d10303c3d4130f403040e4264090010f0002030308964803d103450f01700c1456a0014401c1d4880703030850300c4102c01c605220180f440001c0c0003641c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 129893615 1250 129892365 129892381
    0xe060610020102041503020901030e123714210a05090c0a05040c03110304080714060c030604020d09050609010c2a1b0b070b25020d0305070504050d030305 68
    0x280c4010098056a1040100b088122021011100d60401038100182c4441e00600141d0240200782c007202800e02410445e1032100c8005c4020384200e80030301708000407094403100300a208085409426006401803681d00181c94441c3d2003600f4050780e4151000c1c18100c07060021210042036200400b42e1200e0f41e001c0101c900194414603034401031160081c10000b40c500c0100782070322114041d8a01503030b1240c0303602c64a140283c005205040207400f045030390f407801d801c140c181e0f034020800807600c9070a20040d40402c501c0001e90503000e008183c000d680b03182c460800700302c002e5006030b03205807040d6100c0e0a200c02255050164601c1241c03181d0001c10310101104004260b09440f401503030900c010142c0079250b00300840c0320404140d40c407800014011031000302d807081d40c03030940c3d0246840260001d010340821031400d901c24020f201c003142064040d04642c40300503010700c041010340c0040e400310000c1c076801e5119801c442d070400414100b05241c142c4070030104800001840003640030a40b04d906000c012 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 129894865 1250 129893615 129893629
    0x7020d0c05030c040b1809010204080f071706040312090c15120b12030405060f0d06032f0f0904030903140d090506030405150c0d090b0702240c1b010e0606 68
    0xf50700803a0100600300d09480080c01e50103242c6000c1d0862400900003501c041d40c2541100c015050420071681040d05540101b0350341c84140c0500d0170b20b090b84a500c14104013001070070b58002c40d490340355040411f0a6042a800030004d1000a407540e0307442d100c00154000c139402c40302141c4076142d03840c1d009000c10b90b0400000d0b5a54420028001d030000c5c110041da00300080140c40544004460983d650038400050a886000d0700402c1030441d413401100204004121629000b007981c01000e8205900706003c1c01982c0300b5802e80c6e0ba58020000300b40800b0a031a1000040364800d109040c4a00483d4407901d540c01841c2e450352007003600340e000d480154080d6820030b40300c00040c0340407035515213986859942c440d151480c100d0140700c0000300001160702c038901002520301001c096102000598540d0820289810b401e88a501c05401070640c040e401440c00550340300c03840103024180da066101c40351030031020792000c0e0741030385c11115000501c0100c480a0040b0b50f111814400140350604224040000c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 129896115 1250 129894865 129894883
    0x16020616030e030604050c040f060f0f03120503071b03020114010e0a1515030e0f10050a050108190201120213080102090a051828050403031a10050304020f0607020d0c0503 75
    0x1c80c4c1d0141c0c08000c005032002840484501040d2000f240440c2c4000014004c0c0055400c44114141d0008020034001000340b80c2e030048900885040d05440f40d00c070029034152100381e47c40b0380004c00203000b40c58052500b105003958207100f48000a02d008141d600c0c00d2401da000c1c0c000d42c88030310011040c40352400d40c131f00130b4000b41d49585080960b214901a0040c2c20b03001c1c5901e8040070f05489001c8100ca080007401800180c41d40f1030156001c1c0035041500c64010207080307911040c9645018008103580c60000b0740520302e82040c144840710071109400558611161943c1980703081d408102e41059100d00c0001c1c0001810030300c001507100c21000e42040001200f9411090007240321210154007001c03402002600b10b00919107000f0070464031180090b1003038404411095650625040c00b041684c95484002c5d945a10b2010034203040b844001c00c0b4021400c40d260b000007490900103d000f520705600c890340f0100c03006003102c0ca80000b960105211511484068480c40c80b02481084207007014803040b00 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 129897365 1250 129896115 129896119
    0x30d050a0c0e130513050a0f02030714010f03090501020c0111090f03010209060315150309060f0c041805060f03190507120209070e010216080a0203070504051b16020616030e 76
    0x11818401c1c80225010b810744003c203100c070b1a00e82001c0740d043d41c4840340c200244c03a040000e6a03840203550515080518100000300e0103031043c2040010041c4c94089038260322107050303590180c0d0010a20048014103a0610b0945003950300708071001354110700f4410000070403d02d86159450f04c200c10100000c2c4006161402c0c0642d0042100c1401603903181c00f00da5004030700b207541c01846100040810f16a24040e000100c8180b00081448020600001c01031300c584c2c3d07103000d80280780c5e6a560f844907940c02103229401c01c481000214031124034480d0081644040050102100b02d45100d0000e40740001c8500d001d202000201c03804014440c040c4021800b802156880b6a16031307100ba4045880b00d18014551001c000039056580e1860b8400e20a5644030241000410492034940501c41e0315880c3d10301c000c034441c2c400c1c07440000711381c03d05010302441011180d542c900d01c24501443c4495a0740918200110b823500c0441d40c80044e61214054903046e4003081d840d5203c006035203000340c11040f0b8819414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 129898615 1250 129897365 129897377
    0x801061401031409060c0c070302060304033c030e0f0715110105072a140705040c0315050f03070b0301060905010306080a0f1b030503040305030306041107031403060a0305030d050a0c 80
    0x21841130300c0040d803d40c202c070000f668260740d0062603891500300b100c0e9400003540080e0020501c8180343d4040c60060000380c03c404500d00e9505041c4510714040d0485100000d00608054003109803808bc0e44030440030081c003001d5070040011050020309211715a0008400004e20b01010280140c3c418403140752510000c00800c05030414040151410304860700080ca1030783c0788a40202006159012035008590000c040c2e013200c0000900c4c81c1d12214a4040c06001d135191140310f043c014824050103c980c900303148440c982d24100414061111301c0000d44075050b00c5059000034011100000440c001e01c40e50340c030041840e06142c001801c0c0d034035645c000b007284d50018015a0100d42070800700240d02e603000203900d4204000c0e460900c0c000102e90b201415900010500000b8800044000d5119210849080000d0740c1400090303482030280500140c005402c804200d015101c000c4029034100078010000b401c216502c6d6500352450380325a0404106940b02e40a10603c07a18078018131a00d4202070900d4 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 129899865 1250 129898615 129898621
    0x310081f060806091903113f04050603150d0804050906010503010803120603071805040c0e0112060504170711191a130b0a020703151a0103020307020708010614010314 73
    0xb241d56401100c44c5403022441c45421041018041c4d91160307d000f0000f0151201c10086d80f03106400340501d1b00c1c0116000e500c5000ba81803910030300058010b240c070082840f6013130034107000038405190402860031502c140c400f0070215140e44c03008034440c04c0c980300b0000ca540e950305040900050841c040c290a0521030248014084140c0c04019184099100003551a5666a01d00041e150078041c0c1e1001e030414074030b4181500da02c3c00c16000b0703920940c01420b511242c1540e885084059110034400c001170910301800c8000040c50607000b1942243c001c11400400658403800181954080c4e4002c445401186003141ca06003083c44844036a440b0030039900101901e00741c001e07120108100c9407000b5181c80001d0403034042000d95000d20180001d80c0c80f0310384401d5104000b95a071401404265000c264801000e040301e0301c14011707010200500ba810089400940005501a4002170b01e4481540100b40d00030403400801d220308070082617441c01e4902c814400c00c001400300d900380f41c03032034800903022810 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 129901115 1250 129899865 129899881
    0xb0705011b0806240301090603050106120c0e070e1e0102011b1d0109090509011e0b03030f0d1d011a03010b10180b0309010204030210030203040c030303020310081f060806 75
    0x101d01c0c1d0000041d44d40700840141d0600380d944e04c50000750000041c2d0004800810304400ca070703000c14107991040f0020030841d0f880e01000c505040c04080c0c02400c000300d8503000d2182c003a41e501c0780c036040070450805070004444040019640001150340a86c2c08951210741586580d0900030002e11000c0e41580c0c03003107028001c0300184054490120702440c1d40840d4020511a44280d21001c0100b2018100300311605010802c98041d160080008240901c110188102d582d41031051090281c8028001d51512001c40e2812402d50401124070401c1c0f69502608940720000010002c00c44000f040000f90942c603040d042a20701003444440d6000b80e1510041641984841c1200c2c201407402d4103000c41c04180450074040d076100320360000140c400010050004054054010340300b43d910880301152010322010f411000c90108481c080c02c034044060080000c01c0c02a4000c44c2c00c820001540b07606540c65100541c504960030408804d40509094a0144d401103403145801501c461400b8001030300300450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 129902365 1250 129901115 129901127
    0x100c170f0411030f01090803070e0307060807030f1b0201050105010201060f1d09030708130e0f04110f030c03010e060f01050604061421070f0207150504170c04060b0705011b 76
    0x4001482e50031440c0502c056a0340802412440d000392100030301051290380307004281c40c1c2054501c0340104008001845d49450040740e01810b403041d9035201c030f00f16501d0400072000342c030404107503842c4681d54480e054004440036254403c1641150004121940340000090844802c1d42c403404c1480b01151042c05001c5505030400003440c4001c0040c07000d61030f261601c034214810228001c104403000940c2c2c240742022501602d044800700d6040a5031940c414606414061007290000c105010882a101035407400c030605100010303000d41280c0d03222808002081c21506103013880b9842e94000e104110320807031840b01d120b0141c84181c3d1b032681007914214000c0c150701000c0215517160400483c1e170310701580450010000a46018014000360b00700344001611000c2064507800060040180c0443e00e40300076000304004000c19500d40b40740500e42035013108400100d44c01c0d50b881e8003032403034a0046a52680201c00141503070381d19081e41d03000c10740340550848030245c14680910500c100140b20a41d0803074 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 129903615 1250 129902365 129902371
    0x61608070602040e04050a0606050f130c020a020a08010b031b0f0907030f020a03090b13240e01020331020a0501030e030c01050405010b1306050603010603020c0f100c170f 75
    0x9484252222401e00d88035000e0302981c0c00c984903520021041200340b103800100344d16018002c0c001000100d480308280071100d002c041380c05030845644450000181d0701c86e40001c0e0059a1441540c0088c14207034009040d012856001c079480fa07440c0c401c0103070140741c10300404541d03c9458841c4005114284089602a002c055107603109102100025241c039000340c001200000e1080c0086558607000380c03003e0010320804c402641c0342c400c3c51000a2004503084d503c4100990082001d00c092404441d084042244282d2458600b5883d2040740c89080400d001031406414500720205900e000d01208540035102c002180701801c030b0b20a800d001580342e81d040c64084d00c07801e03e0b01181d0f069001080d90701e03510401001114a600c1d00041100b400030640c80f0b601242011140e90f8900424010050306480c20b502035160b00007000c000400105029038000c207a81001003042c2c402e10a50901814207101c082140d50720001d85483c80f47c95159400305061b003000241c04841080f0381006015004040001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 129904865 1250 129903615 129903623
    0x3060a030813090906020d0f140a0c050f040306060302010f020304031515051c0219030b0604020d06050307080303010e0c0c0c13020c01111b0a0f110f060304200616 72
    0x390b40e04400480c001c1110141480c0b41080c415040340b850a14000c2d4420302c3d407001c20350318007400d00d100c0442d18000c0354064101e00c0d400300640c1c0c41e198803a80003041d540080d00c040c020204100d0800c69144000380c0700550142c18000b0f000f902d10700024204106440003c01150170401c010302c0042c42c00030610003001d051a0001540c01416480c8500c10102604500d40c06400f40310304061341d14441d84045807540c425220320600d0440d01d4000a918234160000410340c042000024540d03003070a03409010280903440f0082502ca6441001ca810f02c1d40341d8000ca440c1d5040080140000c03004001d4040e0086e414086040c546010004c02c00d44580c00500a01c0c0310705103240d065001d120301a0199455500014001c000301c000c0020541e045a010941604030610402002d10300000042482100c89400460a050380942030b55841c0400050b201c605502a100356006901c54442c01c3c05944103e01c05c0040581090707640000c40075403100350034803c1c86260100300400074414150f00d55021079500c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 129906115 1250 129904865 129904867
    0x40608031606090f0215030702100e071e0e04150c05040e060d0203160609052803080c101803080f040302031603050421150b01080115020c0d030503091203060a0308 72
    0x154545042004004a000780d40026000250061a0341e07010055025144032740071641c4081e02500048151444100d0314601c982001004100400296000c0114852241440e24101da200e0b000d0072074810302610241c1c0c1803034061345040b83e01402c0d481014040e415600b01182018a0003540580f03a1000812090140c049400c403c421900d040003035501c81e4209240808805407074036801071030009144101c601c1644203200d40015030301000d146400d40e12154861410140c25925042d07171341d40c0304440020003803080507540002100d40b4450b9113803410704050851101c443c0c03828014050000642040c04038544041844002038000046420340230100e44000442d004e00d09050f1101d00807648600004000c0c51018003081d1706800e82c192505101c2e524a08a0b11700700300c071920464100740c42c81400b2a10341b1005102030307080030366405a0920140304442d135074036080c40401d0109041360300c21400305502005110f203440b000e000c1030001258480007141507252101c002103045000703100c0a0701c1200 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 129907365 1250 129906115 129906131
    0x60804080720120105090c09150d0f06090804030605010503030316180f03050c03010501080d0c170d0f1e020c0c0d06060b0705060403030507080103050c0f01021905010209040608031606 81
    0x1080020b2021002c0d80100319050860390041200e02800c021600212a4040d1403a074100c03504d403040d003850040c15100001002080003400340924100b083c0d0042d0342c00720751405179100045041c0180b4000354424112a6140c915518000d01540c4040c1c00240c0320b40c0041c000c01002c2a030f00c2c0071a01d2058180d1400d0001e0031004000c819250015802c040c0080d10311050202c02d0080c0050103012462041c7c0082000d43c3c0c1c3d40032200c1c0ca801c08580000009801681c518000c2910054404100300700c1e00f1516180000c0504900c040710b010384e049280007600c890321000030751503d54019412241a0000f945000800b400d0a900c035285480010310501c0000e442c1018021130303502000160105404159580849080c041d644213411a41200080d05100c0060390603840780d04424102c070391050050520a03244000c11024807d01456a07045201d0211200c195005001d10043c030702d4000c03c00182e9800c0f081c828401175548a400403007540d4020004032040600303848021884540000300010446 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 129908615 1250 129907365 129907403
    0x703031a0a0b0903120a0f0503191407020c0102030f2209050108030c0c0307050108011205010b03030f07020a0509150909010e0115090b010207060206071209170a090608040807 77
    0x301600c5550341e0800c0721101c0100315191088018802410202c040305c0030300950b0010290b0900c00d0f80313100400520016100c520300380c0280007441d00b281800c16100d00d852103121030441141c3c0060204524100e401d0148030900b0380510030314014907001c1c40554900f445102e02001d0724400d111a92041c05a8950007880048040c50020040c040c81042489a03595800c3c103540e881d0490280b100c054000c40c904000c00b8074000802a085800607168800703503a1920001c401e041200c41c1c416076040d5291113086a9a03a0244010701342c0e02081c102c400d403180042d006105002c0c034941c002500501001e01480b806c50155880c1c1c120001040b130703444081d41e4038095000d014000903018102250700780101d40c42c1580789102860282c4d11102d0080040440c075100480c0e54205a11800d400b580244020030505803180e058050728441c14040841c5a5403540d0303a003c15611804269044080049680722680b81e214403100c0003095540f9111809040c251a82101d82c4a401e0005000c1c1d09c1140d100d207029 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 129909865 1250 129908615 129908651
    0x1208150f150307020a0b0a020403030804021309060e0601091d0709021c050109020904111c0218060304060212061005090f0a0902070b090c030a03170402010e0a0b09040606090b070303 80
    0x9640301c150103469080100029540f43d010000880b01c444c2d001000840f810520b10a4030100c941550302c4040b43c1d2129028132074155903a0000f01d0b0300e50341301c03040900812a0b03805407116140070f24009054943c9807900e07400480b0140440a00c200344135400d402c440b6000000c0c08410f03141c0f4800c0c01a0b0390350442424030400358800905041c0c0906140000400c9109640540800b0609a4042c001d04c182c1d8282000390340314040c0f50b58070b040071390789030f044d00e0240b154054000707030380d03d521011100e2146900280700c0e80c108540413a0b2054000030342540201c0e040030074a41003e0280c0e00c1ca844d00c0f010038000744c018001d00c002580a58814070080340196103554001d8001c01e0b07403200031507903141142400d40800c1d00c1254040610b2140c1d81140079241030010b9204811500b581d2400c0308001e52555042507054003400681c100301c0c81c01941c2c55142c2c1c403001b2a6005210b280d03486555400c000051009650390355004809100a0100030060202804100d0b050755030b0626000070408100c180407143c3c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 129911115 1250 129909865 129909889
    0xe1b10021f0e1203010815040809030a111002070b0a1d100e0907050a091707030209130b09060f150111100903090b0f0703050c190f1208150f 62
    0x198100d41d0380701d00180415648501d101191002c2551540d943c0e6460b440301c21300c403e12415106511001144204403201d80078290402d01ca20146d07482c0440d00d80c0002e14048260a05039501c820825031113100d4a41110034250440040c0042c15401e460400c0082e83c40c0541041c6070244012441d11014840310380b80004660303000141225041003070300c60000d20359090890014000c420035030111304c1440c05041680d030b19000d55a07450036401d0074007000c4d02d40141164801401403081900103c0160385040c00644100981d45510300d241016003005ca01e05980a2320241e90380d00400309020503002840305a03644980e01c2c00600440c220356000480d51850080c0c80741e074450041e4204001a500c16400402c0c800e0300071364070150360944a241c2c188203403280c1c84440181e00300c100159400079020340082c2c04003c8400042d144400b0000d0485201407041003422107461010003890010084150746100c0c441c0858900410745e442c0004ca001004154011410320843c1412031520310755903072240c5048 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 129912365 1250 129911115 129911143
    0x150a0c080124050d06360515040e010e030307031b09030218041a010303120e030c1005061c081b010c020d0318020d0809030c0102030f03040b070504170705040e1b1002 73
    0x1007640c86d2201c100a44000e440503d04031a50b294408005800e010300955002ea040d40d141e50507041d036150200710040000c9642e0b410a03540703800341c244030300c142403000e14031400c05034502181109a2580001c003040001003850140203005a00f800940c5402d00810506140705160710b0031500c0b0303810311050100c6000d80954464400304c00200c10107a0100c83e0030003043c00c03203209100c0c9003d9009020707100e0007a00310304203603a8040442401c100156401c1150406000b4048004804052700072440904c4030090a90b0110400500c00c1c81c40700c3c00c030b04440880c01c0500001c210304414004025150f0b00b038011814201600c0f898100c0d00b880142c00403900b241d03401800b00381c040035180390440050700500e070014480d0284191070515540044112802107150615151466549659030909410003801c0c41b8100241440049140e404d490041c040d030305c0b49070300201640c600d4030041009450080c400c040490700a03460b2408400c0e001e8001d03404800c0126006083c02e14034041c12803800600b640205 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 129913615 1250 129912365 129912389
    0x11040207031206120f02040203040809090c070b1501120c110307030206060f0616080a180e06040b060f04030f0807060212180102071101050c150a0c080124050d06 71
    0x10406030406088100d41c02020b0382449010760301c03000141108404d0001924403507561803a6001450103900440d403040c4189140b508003034400c4085070101004032000801104001405004d02c09882000c41c1e01801c00d07203041240004840c0000c2429440c0613000010a031146416030015000d0f64080080a007103c2c2185d445880702d00300203540d160250780990141d400f04103170890f01c0c101041107501d00030755034801c02c0c0b40c1542580c4419a50780305e141183c0401036031a4203032602c900003400d1080100483c01c010328040c1041010881103e10585a061254038204031040070311710310a05031030890350480c604803207603d6241800300203842891401442284001200783e80180100d0700a8000c06c100c4000e1000080c141b9412800c0b81700310030f030252007845e20700744000c095031040e4002c000b00c4000c178054510200027207080000380c840c00d0302e4115800d038031400707444901e60340304190701c0c01014400009110618014400b500200c40b82c6da003001040b200141500e0b104085400c1640104028086c007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 129914865 1250 129913615 129913627
    0x110d0603140307020607030f031b090e0a0504020f0418020402070b07020708190204090201120603050d260c09180901060e070305070206220c0e010602070b0f0d09110402 74
    0x4005121034042124818000c1c9214a1074a5000003518405580504607a24055960b1001d542c1442c0d41c80614003019200e07407803d51a8650301c0b500c000342c8000d9842d500d02041c105803900394005401401c00362441d00c1d00080101594074024021000070040d1400202c42000c03071441d03502c46203070540c041d4029000151000401102042440c498000d660940c1c04903030f182c9a1450712582c450b003540403803007404108c1d20050724182c0d00000000740b05042c4544545000c2c2100410f880c12648140d41c81c1e004511a80c0307865802055000001103202400041c0040340740034a86180801740c0405544440420f14405541324100e15042d030000011841e030f400c2c038103050b031035000e0081c5004e21142c256291001c43c2109000c0d010b02809115142c02608040d600e495000c2e50151f1038004a0411007000c0d988040413652400d490000381000880702145581042000703498007500354403400c100303202002241c41c8011800e0640e001c2c035182607008100d925203814019410300740c81a040740c0c020b10000340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 129916115 1250 129914865 129914887
    0x7090e0703030e0a230f1e2701030b070e0310020a030c14120901110d0b0a0501090810150306020a0509010e0a15080901140c040815161211 61
    0x3244003101d10907950800034640040c144103c114052060144804801c18207403440403090700a2810b2610280a03100241c81c90740001e18032107040c00e122a20841c00c02807501241c00d09090303800e20318800d0080700448515003070442c80342410511001d8041002403001c03038000c502c00d2040414840d0001c007241c200c0b0784003015890003035100b151540040303860001c2000255025211480f58042c0c1200c1c030600380911020350b120030300001003031001d41755610841d020800da01e0f2001703084540603407038000400e01119801e1040b8060b181d003220b4148072001c10b04000003007001030b502100c04880003000c903000410282d400d030700c0001500028400b0780082204d1144542c010090240100266288602c44151806002d2803403040e00440710710b0380c4145034180d142c9009103007240e08080c906c400040c0803400751804d42d064800c00e5801600c2c2c1400020208000c040800510f144500194070790807444c10580140c030310100e9104195002d1041900c3e00340d0341144654440c11070706022008860b911064408 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 129917365 1250 129916115 129916123
    0x70614010303051305150406030915020318010b030f1908120109020a02010b1e061605030406030902090907061d120f01020301080d0212090d02031e0604113007090e 72
    0x450081044c03400340005690b260074542095040360084209241038104942100940214507040d200900b25013500c83e4155154402548100705004215040e00160300c01582540d0032124024400c1d48490314901220001051490003402c1100313900e4040202d615150803035024141c41503503001c01d00d42c00020881d070160010078180c13020354007c1203030b0320b40c81081020500500007282403a081d41060070089050240003004090502c40d414800d584607550303001d2a603403203038010000180c0c40c0d00c1188210b04101e18070541004904014210480c00e01e040100400030f880d0f0103402c0e10901034041e4280c0c4d02e80c00c3c0480685044201543c41003440e141440e80030354002e05c201c48041c4140c0711082c401c03501c0852030601c0c20710000c100310300d064541340400039551501841a0390500510421108029801c10044107000d603103800340c40107203881d041403090308030503074071440c01554245654100700802c600102e031015a000d071a100c2200503c1c5000b40b81038844c1e085103d80500c3c0c041e408010040000d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 129918615 1250 129917365 129917377
    0x90902070b07080603030a020a11010302090a090c0f11212203050c03010e03030a0c0e0303220902070209060d081308030702090117031e1603030e0601050108061507061401030305 78
    0x603c0f014a03549680050650720301c1100a10360058220080440000e200200c0b01040c0a105141c0541007040d000c2c0002d4510303600d90b20119100c5d03591100d01d84120f42105c0c6614010083d801e025030413100008140744c071000c0f888005040502201d0414203002c0c0005c05071290712074102e45504010f1605480d001810506000940325486002d404800b9442c050280402c00400900032710b0854540110f0f60000d0202c4401405c00c0c00317115404080543c60400140482001070140c20582c2002a80803414102c6d41e03070003410800380100600f20242e201e00c40256000139041d1540c030410b5003142010551070043c007800014004901e540091042000006006468000c83d814002d40c0d0741c5040e40c0e09105a8003030200c2041d0414020b41e008412900c0c040c0041c052092000c0d0b1030080000c01808080b050341104401003580c0d0504e481c85800100314940c0580300a08003200c0d641050400100711012221600ca160403000404c40f040281c56004001d11180d040050342c01940c507450701901c260020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 129919865 1250 129918615 129918617
    0x6050c07060e0c060403020f0d3c17031305060c07020411040807032306010b03091e0316050a0f031e0306031a1e0a060f0f0f090c090902070b07 63
    0x100300540012030108002c050401d00a204e10328292a40d403e20456102103034041da8003e401c000b060b0003007801500314544850410070f407040244140005540c034618100400c06184528990300e00c002184ca10145258240002c0003e451795203903074488042d040843e0f030080442c0a1981407001c500c0c4604040c0190b940300f100e05001503000e4a0002c521800395105140e40c6500c0028204040341340e225103071040944c4480741c00c1081d01100c1c0303224a810307400c1e4040c5801250010800001c12401c0c4410f0020600c052540101c09100c00f410594078011100e000e100303040c0c01d0744060704004042020380401c2c0c0e44104000001590303820094610078013120a90400022540c00f8100c0030b11a102d1941a030740d0013900d0410403003264581c003030043d200801480da40e00b41070401d211520824071400f0302c21300143c140880c9150500c618821302441c55400100d05098124050015840348040c810903514905400100d10414000c211901c80306507100410b02440041c00c50184035018102c00c1c4200e0301 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 129921115 1250 129919865 129919871
    0x20106050a09090206030402060c10021216020d0f0e18090606010810060807030504020d0515011a1e0a020c0d08030603070506120412110d050717030403050a030b03010906050c0706 79
    0x681c0307035140141c83e41e1a40c000d501c0401080041c0041c43d19001428001411404564456070318524040490741721540c50400c1c0010802048020592006064080740c454409490f024100410161050340802080400d01072551001003441e1285900c0301550707000701f0388190703550400440590b1280300680d161400100b130240090056065805103800700d8042d40d40d091195960410700320b004203006041241d006000292407008214100488036414603410b52040665140c20700d802c0c0404601d1540035268401030003410260414010001c2c2c1105105e04855580c15444404905001d04020038079032044c03400b0a200f092241c00c402652242c20113500b01c4018540794001c0002901990302c1801064907c800002c00140145102640c44005410000c000d843d001a485080405541c036040000310081080414882c0c0420300c2c0d24810030245155145040c5501c0c0100648150384100c0245615002e0070310507a00c01354131032142c0c02d40210040000e41030a5104820075401840d003503c2e0242 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 129922365 1250 129921115 129921119
    0x130308030a060b120109021e0a120c0912030806030a0512031603020301050d150908031905010906060c0221030d1d06190b150a050702090903040608180a12020106050a 73
    0x40b80204139551248511001001030b840c0040d088081d60210f001046484080e80e50343c038402242c00c01800a00b80183c5031580b8181504410303000b04c030070000c8980304005552408000c030000700d140d641a82605072500b040c644c2d456070b02003480c00300105802405485640c2d842c02c112081c80c000345000e41038200746102518948181102079000a009403544000b190f0b40c12000180501092803400c001d88501065800c40ba446c2d004968104444500c1403010344480310702e080c1ba4500c07400d800740100810030004141041c0008000e0004080000e014907080801c1050070703400e140c0c034144061120300403681d0b0760099506407006056189140d038061012100d00c811000b80104003031303200d510f10084014109850a40d240045c01100d54403980044d41441c1150305c1742204c1c030051078201980d0711510ba9410051051010104009120603107541080c00240411548000500d401940c02008048064846a541c5092040000c0c2c01803007207a0340c030320b9016003c0e01034110a086820454000100703507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 129923615 1250 129922365 129922379
    0x2090f010803030a0e0a0b010f1a0f0327010501060f0f0206160e04090b0109020c0c01110d05070c17100f020a0504031401060b1204020301050a020f1e130308030a06 72
    0x19000380502aa950003c0c000590580155844007201501080c200d900109064a6a4051410a820805900312101c60a100744d4440c0200440c48441d5100543d140c400481002e002c80e010117821800c8010010b00c2d9944036030305001d00a11030480d0384001b04410350795118080d050050003c641d40200e00e25400340c2c8409800803413510302c118402c84202860000c450000c60790103000c00c565503803041c0d542c0d45460200b03514448180c06801301981c01039848842c0480c0c075103014030302d00c10641002804900c0710246507000c503032000c00f4915400e28a444050610f011440350f816500451912150807001e403a030050b000074051000e00110701c04224032403910503400203a00c220301d05003000ca682040102b00258268080c41a11600f02d000080c2c40c0d901c50070306d104140d01c044040455200c0c400300307100a500c0e081c45801d0300402d030540110300d08120095000c410780100d01c0a892032002d0003009200141c904411a0200940003508526440e00c9103420b40441d002900d6003880d0718502800410b9113 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 129924865 1250 129923615 129923641
    0x20d02100e1b040e070e040203011404030c0308040203010204051e040b011d010c1a0c0a0201050601080403090b07060902062703160e0a0b030a0c0503010f111b0c09130209 75
    0x28501410152105012110485803922821038045800940c1e0381e070130300300712541884400040c204030109000c0700e091a004060035100e140f6200203200c103111051200081d002020540c8042d4542032001040da02e82c00001c2c02070007142c1c06107401110700e0a4107481c401c48940254420b1608071004c00802e01c0ba10011911040314030710000813a803464084545c84d6000b4104081e07158862800d0044076251203030310002526098a0400c095500441c1c10301c0703400e4082c010035501034801c0c6400d110919007910018041251417058155444001420000f845034540203035682030b03009085250340c0c7c0d200509908a0524102c410084801c4400b031600c1e06260200d50050b40da11483c3d840c80d899410302c0080e48034454050312561009544440045942e1018080c02c00b1041c000d0031180000c0b840d000505007503035a981d08080001d890585103400e00701c0154265880c000d03400036200d940c4203135009480c0c6401c0f9a0407905600c0158281049441d480810350341d04400c3c0f00799200c82a03030f224030a06a00b2 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 129926115 1250 129924865 129924881
    0x30618070203030c1605010c0903032601060c06092a0602070b0f03090a170d0b040c021209040b040615090b03240f06030703140112050601140a15020d0210 68
    0x182c10410108021034926005001c0d10303004110300201c01d003a540e417490f00711060401400e001c2940101d0070000c0c0747d0000240b1540c81c41d1030500f0004031031440000401d85a05000c0c0c10b050218100d450800c1c80810744c44601403641c0304a030722034800440c251009041e101c2c007540303014061384e560b8007103001440428801c0840c0d1001d07001900b0500c1040c01003006400007424466541314404620010601c00c847d540c503455071410341c1d940d840726040003410568040003086030055080004002040c1e900181240b40c4c00c1c03240942030348030361008000070040c11541c1507050344a81000b10102c0c2056610aa9180007003440d141d44201503601d002d11040e42c0411594240200c000d40d1a0701081e031412541940000b40c020405503009003c0c3e40060800d41082d113400d000a0790322680440d141305074800342170141030622209031201d0700f240d9429940d818140503000b0602000708a6407040d8481c0241a40600f250348484c00c02c031701c40030500a40c0ca4515840c07a42c01032044550801c41c0500c54400c07020 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 129927365 1250 129926115 129926117
    0xb07080403060911030d03020901120501030b04020411131d01060c0c0e06011205090c030d02060105030304030602090a082b0507080a0807210c08090303010b040608041502030c03061807 81
    0x400d16103181c03502c100030400d800c010394202c015160b0b0440c540d42c007070106d0503041e451501c0043e226141d100c001409940c00c00d40c1d51504620b0600140f001c502c40300c15507980594100c0340400c0703204074100031580d1400b8a00d405032040742e006401182404803881c03294040310224000c880c00d03070398a80044800b00c45558000c0c280d4001c015003841034500c01408258020010304008115200070580401250000c84a40001c3e41002a901481c2e25003444241d00d08640e41c4010319041d410030340040d4a82c0300782c0c0b000074010743d070024125031a9102c228990004000290541d25042000320300300d504034405050351906146000c0f45c07100c80c18040c0c421f940e00d540c3c200140900b441040c041c01c0d13034460300140800092050031445480000c1400f0150703103002078440404684e01313419800103441004060140040e13500140014051801c0b40020303503084610602d00100c0c1c549036824070440f1320610310080010b460000082010401d41c0c0d1000b14020542034801d034180711803070015003035030460650f00c0c14 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 129928615 1250 129927365 129927367
    0xb0306010c05030412080c010b1f0309020f0d030305071103160303020c0307062d0506060a08061503010807170d0f1d0405010f03140a17070303060803130f0b0708 71
    0x90200d5114070800001c0a00c90011280707402d44407066122241c020300f40889228100241041c041c1c802806485070b02c034000d48484501d1500c0c003403210380400045407040e00301581c40c80c111040d580c0d03415a54172002e4002e0003112030a00c160a00802410040358910085007815402c101c1c1c0c51000002c43e14043c2e46070050f641c907103200e694200c0c06948640200d41c0c980c8800c0c020030012944030b119041074800c0303c40041d00c010519a003e034085402002c0c4005410386400c040141e242c8030b00f8110751000b190344c500301035181c0c4c6002c00119120326084101113041004400480c2120000031235030b080e103d030003e200c032405001e6039003c3e9039140f0f18820313600001e0700c603040c080c170440c0184440c1c14509000403256031030b001041c1c0401e045500980c851240c814600b0010020300409000590f00045649d01904036a4025154207038250aa400140401e0b1400521700052600c2030703002d100130b041310b075060381c0e0340e00001c1c0940380e8414840d004d40002c0071041c920021301c0542c00012a03901c00e80c42071000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 129929865 1250 129928615 129928621
    0xe040206070312021602090106090308070602090409050f030901090e1e0a0204080a031d0111120c0c181e0106090612021306050406120908121503060c120a060b03 71
    0x22000941040c1402c9003448000b480300408908a400a041800829a54650341c803043d8010401c0461060317018405120b0764880c14408034411104031002c0a4008030050783d00e602700e8000c03070010000c0c484041c22038010032504810f200c00200007805090000d03079034021010b85444040e124204103a654440c0e00295090344c3c0c04061500c287e242d4045c110960040c00c095640b4003590a00398429411400241c0ca0306980380c0202d080f032a40b041c2c0c1d540030301e040058595040c4003a60380c0d620401d40030007103810201d12900b5801d001c22604c0750050001d07040142004020711203000c0d5800680d0400741811800ea131401c4048074011426040704d07c5507840c401942c0c9406001d072641480041404443c0390200404d104941c2c4820420004140da951040d40d11490014004c100b010750421071010f05051802c8440800c50440685040303040004c086241c03034a403640300341000c5407000f44007905130041008001482c40b066028080c0f12140310070013a0b00f035550558100889005004107041040d0074404 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 129931115 1250 129929865 129929869
    0xf0715080601022508070803040303090e04050a020406141008060f190308040303081b0408060604180f03020d020c0f030a0f080c0105010909020406320406030605180d090e0402 77
    0x4140d04a00d041c0113955641c400c1c0302c802e41401c01a03071041034060b45010301c00c001c448401c0000170018018640654100f07070035960700500005061007144c5103402d4590210781800414000ca2030440ea001703100300900c1e03a981e030320901402c8880f100d5a104403050b08000c05494064541302d481240000c00391a0307001b0100040102c003152245444000882c00140400000c6031523008001841c001d480d001205d2074210b00010034903041080b441942241800100440000010626000003040301d01040c1c0d03001e0488900b20408001c071015001503180c4401c00241500030480c00398000c429401d5030807036440c101c1480782003071403640c4440d0154400709518010600703d00c13070b03007072001e10408840303280004010400b400c1da0402e8002060055803049030308110718040c4503001c000c1c440f1070b102161074035040c038445200c5040d075048046e280001180d508140d607101d510003070203103074030503020061420440552170001142000c3d4042c141b056036114100135000d0f8540c0803c0702c00b11250f003070340b6039180e5007 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 129932365 1250 129931115 129931127
    0x1020313210b0901090203070b0717030a0b06160b060411040e090a02030d090602060703110316120c030b04152912010e0a050c032a0705070b0301080f0715 68
    0x24165894441d0041d60000035011820070340540780c004008203d41c4000d004060400c11550f00c1000d1aa0003006020000341c0101108030b20503240781d41d450b0b202c1d51400f0400e0050a4100003480e0b008400088088000580031009a43c0c0ca01465621245a65110034081162101244911214410700c820411144400400c80d4070802c0700068800e5400d441c1c0c04613181111545144010030200003081c094158100b01059020480d4a8184040520030507a0f0015110140070250340c00d020f80c0e41e880c2903501849c4252070200044400300110a66484010011715403900e080e44642e04150b10b41d0001d1070740c2440c241c281c0700d0042c5031801410492a41000c01c040c43c643e1900c220400f807261440c00420220a54000d000c065003505003840d00c0880781c411204014560006100180140503041d04541d08003000100101040070bc01101d11046a5080c090100300a00d548110880400c5503940d210285040740c40c150221280440700d68100c6403240390710300469032041962600b402a0902ca48 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 129933615 1250 129932365 129932399
    0x10020903120f0a02060718050906010e03071502120a05030c13030b0a020406020f15010501050714010e070303020712030203031506070614100602010605060406031d0f0a030305010501020313 83
    0x301140c0c50880d40d85031a500c580c001084016040c840450f4142015405000c607550118075442e0071700c041e041d00402d1101900040c003a4a02131400344000480a900034600415040c1008084481d016541c002a00341e10003405d400034010f000701c1c17000c1c3c10009005020340344e09900c0b50322403a003581d464040d8001103410414440318006070401f00003002c00c0c0311742c400600036100d9010150ba52410060080d107004280320f8007148603440981512010444441d01c05c0c1540c3c42443c2071a43e13108141400b01490400501140c001c0d40b80c606100e0034481c0000b80103048a11036000c1d901d840340d4507075048950112801010380981c00410018200300100204642c1040006100301d0600c0300c0f6450b020101c0300041512072280d03030498180718801d48020000d00040034a48002d011aa041c080421540e01442c85280180350302e6038180140030704202a4540c42c5040d01040311035055640e2a82640c903411900c0540c042072801c800420f09501c00700c103c0da00c0301480c5004003030040c58480d038440590900 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 129934865 1250 129933615 129933619
    0xf0308091015030209062409010201020c010204090914030705120918360c0607020a050d030e010906050a0e0f0301110a050403051b030a14070b0f1c0509100209 70
    0x580541040000140320b10202180040700d4621124203520500031303000000340505210301c048000041c2c1415040020040d0900404491900c817000c800050340a0b0188050004042d40081008601c1120a501030407401e4042e02045000d41d00c10b400c683c2d2284183c07100504660080c1c5001e2180c0700e8228002c10075460043c1103210205130100071070481e20070944020940c1c150040d5042c04a035880469080da0350000308004075040002921183c0e25103411918a0181d0b1011034020305564074840010001d00001c3e06ca490031200604c0c0007000303503003c2e0360001d01041580c1c002042040c4a1400d4a80c02d40d115100e08451500c0c9804014280c244003650130350540d04d40a41c00804603509001c1c025010503602d9080e2141e003540b40030b42c00d100ea0965045228000c19030262a41d60700058505099500045071014981d5400314550603d045500f02000300a8001002c082c00c808400080060a400d0141e1442101c1030b50107417003c0c1c070020307110400aa445095840b00c1c1101c61b5000f2f00041c000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 129936115 1250 129934865 129934873
    0x1314030c090108010e070803040b0d0510031e05060a02030103020915040f020c100e0c01090303140c1b040c03050610050a0908010c05041d010b07060c03021605010203070e0108040f030809 82
    0x82200041c12001c426007140c11140d4481c001001062030422011000d070046402450900342803d40d001102c0c002e808070606e405403288040303681008404610741c051500080700100e28402d0b809501101c50000500315540d10500d0001b07410b03c0000d1003501d060320f5004045d80c4041c0c48012500490417009414031354056070350b07040102d07605920300c002e0a405010720041c000001a205598040340c085004600c81c0750081d03421401d03160307400039410b070580c2d1341350802c445403040f15580c51449014000b0019410303c5201d1112200354404070031401520700c00c41e81444045400310080341035404c19207074607800001e414440c11a060084000d419a00c2d818030b4108105503690511a00b541c5c002c00030413000c14400241400003600311107103045544a4020445000e5151400308481c41c420700002414440e80c1d41004003401d0b2103034044550340c3d8540460140ca140704c0781030240c000e40c1f040e580c0c1d50225000e0100c581c1079502502900c2c0c0b09a030003d420030280c0e01191030503500c40b14010034515040c00b07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 129937365 1250 129936115 129936133
    0x609050f011a0a0506030415090c0b030403020102030a18020306160e0301050f06030d02030f0405061c0906061502120904020d0905060c0301030b0c0405060904090302100906091106131403 82
    0x4091140c0740d9207a001c90010042100c00009108034110f1030b030042400b4010400412001c9101d00b60442100e1405420004108005007014407040081e90403c6c0c80011b0000b0601c000d1644c150051030040704502d104002c00ca48038588600e44201040d0000d40640000c0c0010708a12140000d400b0020301e982001046d954082e40000d003112001ca0f010320064519500f40003060800f004600001915400107500d4070b0869050044a40600d00c68035101e9a40011402c1c08407689801c42c540e00600c1c03400038040c0c440c1e5840d0000c003030034080c054614414005003000030082c0c40065844c00254420030384e0352400000c482408041c0d03210f004440305071030701c07a01c030070f00090400c20032944900706102c001600d9505500e85480b4480000d003010b100690300f880b050051380e0f5120103c0b134000000f118005a020041d14040e800c0483c0c84151351000c500d0301520a051010903049549180d01c0341125445100014040103002d010340241102000e030103a20500c40a400c51907403980c102001812241514 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 129938615 1250 129937365 129937393
    0x1030c030b0d051b030705092802030c030414030f040302040203090703080f030415060e0c032e030302100c050702060d02070f30140a03090606030506100e090604060905 74
    0x10351880b0211003d9108905000018044100404074044210080c0c00c10300d240600080181401071701c40910741c0345401107542d4003044002000404100560103545901e4a07490440300f40d00129070544410011a50610b04240c000c03088609000412401501700f80c10354084c0402900018a04019480380000120101d1209c0d0702070001d80b0100c0c181541d8929151400343d00401c0b90b076808140160900d80144902c00c5040c0310590700074082c1c0003e5413a996806100c0b5001c80c900d0090803040701c1460307010b200c1020071046d04d4007034a005e50200c81d00c05420980030b4088503070035094100060070520607040107141c024000d10788500d030990050708000240d114145004070400040b500400009107805000c441b8442070400d112039801c00403c0240000c40103008a810f001a0501002001500491041c041d80c44014002e4100c0d03401c0201035243e02c0c10554404041d40c004105e003019580c0040d425a1702c0315454440d07803d2101034002e87d1176994075040070b0412142c08407050300a80114201032 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 129939865 1250 129938615 129938629
    0x1a040b1b0f07050304050a1403031905070b1006030c0e0a030204090c1e03110402031504020901020a0b0924070f0c060605061201050f01020a0302030301050f120d030209030c01050c0c01030c030b 85
    0x755020300c3c061541c1e20f00d018100581581c00d80d00030a50340c41e9440c4142c01656000c016640c0403001032198410100c0401000c803050b1207203031380085c00d4000350405c0c402c11b6000e0280d0300e416210302d03440403c40d43c00c20380001e0710b0f80d044456110340e000d45800018801414207801c2030503420320400350030000c140c0f00c0266140001c5514041c25260601000170800e000c0e00c41e603000781c4400161401c520f5405c0c1394400349200a0000c10b042e010b950000307800700c002c1e44200865802283c120001700350504018188c3c54542d1031504440350f030200c0c0070304101651100d805042d07014006c1c6447e2090304c1c1205130307402c0e40c03289400c2400751621540c036500098161901c10091440805043c0d04031a198105401c10842401040c00d10707045601800145001a4000003100e0540f041110030940d0740c2402800206001d01c680740540c03440c0110303030440c014150107030094416950700302c0c1902e159280030401150140102c0c002028950b101e40071401c0254040e0b40004000d0b241d6240c0820220005000304041c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 129941115 1250 129939865 129939877
    0x406020109020f04060302010210091e05150a0e0304061211040303030f050106030213031e0816060c05130e10080d0e012619020d181a040b1b0f 63
    0x541d44079158802185015014440700d48400c41d0304100a0f0305580000f5074401c040c04642c6840c99849a0302c60900c17800400003001c2c4031941001580340011440d105444001440c40c05e201210504040fa14640c0d69000360140c03403050000031401c091400c201212044800e01c50681c0542d61800f0405414881d10300501c09140651030105410781d240441001301d910580c07001c8201441809407050035504100c1e604100c0760400480c0b081c600103480464260b0207100b400524444000a4912403514004800349540780145c40800c24410680710681d182d02c1180f40c0300d881c0003040982407007010b542449180c0c0148420550055941c1c44000103881c00c1c50312040900403424407180c0d407070710390b81c0140000b20000070040908141102d0f81030903070000704042c10210004541c2c044240c40110a94141c40094168210a200704842071040d17504c260201102580d0320080c8141a030f0002010052035405160301400007400c0d40d9401c25104a0654440f0203081c41c0103042141d128120f5844024206d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 129942365 1250 129941115 129941117
    0x804090c0804030f020c01090b070204020c07120c06050319050411030d090801181109060607080f0702040f14040209060307050409080a030e0a050c04090602040504020a110c030705030615030708030406 88
    0x1225040c41d05000d09019070140391001154420303411111b040e41e2125038001211580ea0b8090345601951000a01178040c00080107007501c078200300020b104c0c0f48000b08541a50145c60120461a1152421074103840201e03640c101002146116030160600e541c00241c0c024095021000e1041c44080004d040c450300114520018030388903001c1c041c0420a2107140c03184503a5407800c54070142c056170b07003082c206017802d030041c885d4182500241040c1c440500b1294000e5011020580d1140c005907041066040302c0c030268029898405890a9814a840760048c41c41c0704100c4040b044d6520390800c1060b02c030003014150180030340d43c40045c0c19140d9001303080c040d42c810707940d20340ca800c1000402802ca80c2e10128203100b55105841c0180491408911039803101e0041e200407800c07000c80d04101c400f07489141e020540152001440104181d0300c0807006c14803e11007410b846040c03180300101942c40e40d8a000300f0754503401c85401f09403034000d001584100b41402070305442c09680da600c10301d82960040d03480b81c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 129943615 1250 129942365 129942377
    0x290705060406060801091a0714030406020a08010b04030b0a0902030718020d0b0904120e040b06070b040c0e010b0a0509300d1e050c0a05060907090b040b0d0f0804090c 73
    0x881000b036a4007070280074008a8000b013014511a440f4461000003104085024200000c04107002500c109100f407030505100081a544c0e0600d482c01d54020340c405109030001a08117800030440803964022981104d400c81d4a82204c0d40310545100000c0c01c9051080741e040c820b0300c0f00010b50000510b1b94500000d4110001602c412a000180c000e41e01601d1100b4856103045d400c04c00020a4600034900d004032900d040c00000d06100c004c18000e010808109602041c04101c0c40100070080001c0c0d840f507031290b0f40b21100640d40e6407a03d00500c10a01645540e14020b02108110b6031145c1e006d41403101001780444540010000e00106a455886c40381001110182404180f4581082040c40540b81850030304440040f011044401008086820b0100302e0000303503d81794050100071f050211900003085c0e13110b034105220403a41e02c10962040030003290500c54040c106207860310540c5000c43c0c3c042d0171190000e6055596003048001140111403914084c480455600218410038000032000d441d00 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 129944865 1250 129943615 129943621
    0xd061509030203010e0d0c0b1003050a0b0103030f08040503090d06020904020c010509071703030105010e010e1002060916050a030209040f06061511011505090c25060c051329070506 79
    0x41825200120606600c5606c0030f00c240c554a980100042d2100c0d0700410752400390307280c40c0050703050341100741c4c8081c00c144140300c0300d1002e1010200545049a00c681c48142204d84480ca0a4034918021a00a44550814082c925403401e05440d0249504c0c8942401850040440001012070b0404500000140c1d910000c1000b50b660070001000a040e40301442e552005800784d810b070b0340e8030050003000d0400910303500100c0e0070390040181040940b0010015191060044002980da0704c0841312814584541151050f661061408000a450740602200741480c215028048411400380c011250006081101d401203130369441024054080c40e1092802d031070301c51000404441c110b141815669140c604480c10b11030010030710b903085420648510085030350700d500c80c000c035006031280c20b0082e178000b0001c00303040100521400c0205101c3d00c070800142055001c00c888a002d80360702c01c1e4801c091030000344816802030b0460680780307050481c8410030700301c0000d4281258000c58030031640c9034801400c3c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 129946115 1250 129944865 129944869
    0x903030e060c040b0d0b1003050f15060f130f03110301060e010e0402041e150e0c03070912050a0609080706110f0703030b3f0c060703050d0615090302 66
    0x440c00389408100040201e03041075110b182d020b1095200303e01900000042604480080c0c1e08402030743c6400401e094001c840c0120041c014100894107901c61003200740000d11228060049100200000f03000b590404503030041008440d84400c5a03152058007000380058070200c0c4407a83d0021350710450884100c0e803000d2042c0b500b540d201d80c105040030001000180100f00320011015070054044801180300103925001100000e907120005150504110751071804811900ea080203c9a80c00360300725a40c0d0f103404001da014001a1816000140000020000c80d0b110161501c141d500070001e540740e07a2100d9a490080303c0400a04680452011889c00d00b44212031260360b01007418081114603000383d1450103034252182120081c28555198120601034407482503404400c00343d1a6001c0c01c2c00800500c002c40103502d0882000c6414141082c94510b420100b00300c860b03044040c00160500700182d5050707410342c000c001c01d605c0c1c040c0e88110020f459803039440201040360464407019186811401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 129947365 1250 129946115 129946121
    0x30210090f050102120a0302030a0b19030311060606090d05070e0f0f090d09051e030304120b0703020c0a03120f1a18060a0e19052d1b0a14030406090303 67
    0x20280f41507401412021520400003c1224540b500310303d001a5a43d440e49044030003411540c412541100701c050000390305140aa9041007581e0103622000700714404254016560f0800303c6a26822150510090340c00b03007420744e100d50416102d4000c1e10a80398031001c1039041690102d9440c1e1801e44801d042c410369064510b039598000d40700d40c002c0c0541c0b140200001c1c180c0c01e43c911515014108a1000d04910070075030b929030307400c0c20000341a0390703980307544001043c00c0200145056485013049808621468004c0c8215428000f0107405030003800078640b4141c0324410101880300c0c4030b41e00c52220907c0c0c101c05110b0541002a0541d24058490203d8203110103900042d03400058210b501c007d020181d035034a82090200c800e00100c001095842d0b0042c842203000b04d54010500900300011300000414001041d0303030794668610303030350740303411480403115003004007510303615a0010140003214030082d00340010800c0d8441420710070001c103405039524075036900450313098801d0381d81c481c100310030594140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 129948615 1250 129947365 129947369
    0x7030605040c020309010206150402040504110a0207051e0603060d21230904090c0b040f051314040b1017030c0601090501051c021804230102041802070606030210090f 73
    0x44011410400b9040000c8e55501d809442c201840e10403040042e055559038040702d0240802500501414003014407120703668100103204400740c0035026001c1990b00f00300001d27a121114800c1c1c000c0444035460b00707000999101801041e002100c04074980c02081c403d00c5560303079015400c150782c0d0001d200b681000b4011261640380c481c0c3c807503038640d4809a0b05030050540b140b2050071580040c515800d03141100380384102d07512442521401140000d84140c0201d41c13082168404c0d00c1c07031110b1109014524080b210304003140468030010f04080382c00304a060033559840590f50301e451142545642148641d9034401180b01a51342c000a585c1074803030001d004507401010130b030a050000e94100030003e0b82c1541089074084958007020b0440c1d06556880480d5092104843e11020b000d080900f858403c84082542112129140c4050546245c0b4144200e50495a20012010b00b1100307039810380029611080701030310700d00d07114880030000d1b981e000943c0c0c4081d6215110860994a011003a0205e25025 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 129949865 1250 129948615 129948617
    0x20a03090204241a0d0b0604080703030818150c0304030c17041d060d02060703021018050f150a0b0303120a0e1606050a0c03030f060b09040e161e080607030605040c 72
    0x49034a40c003c0300314005480d082801710602044842221001c80d0090141d58440b43e20b62207034540000034150400740c807901074000101015a640070009a280e5283e5403054120b80b20105c2d85c0000e076507064003102844e04140f091908001d569540d0315100317a00c0816064442c1d05401c00601001201100701c0d12449481c0d100a40d1115403a10b900041c8040300a40006400b5090001c2d050080500c2401004240c042303001c2c1c10090740880b80d4000540c92840c1c0b00484061103400ba64450f240e000152040e03801400543e8400c0b16604c864407207010b0513041001c0794142c482800114030441d03d403c0712500c1251311242c00900210100c401030301d040c1903402ca8103081030b0145030134000e5a50145c01c580583e00e40f410084003107551403030210300820780702030600c001d00d103841c10100721061090010510010f04036410f201e407140d04240c082d200c144001407401904a00c001c01c11180340385024221600e0f079088502c611881d03941142504110302210710b8000039070f44840500c103510301441503611070750391 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 129951115 1250 129949865 129949889
    0x31f0b1903060503060610050f1303020f040905060105100201060f0b030618010b090108130b040b0f0a0c2114011e0b03070e0409140a08040f0501030203060a09020a0309020424 77
    0x43d14000c2519140081d0189005000c05902292194010030480f181d490045200782e90f01c80b0043c00049000840340000c0b4071030002c0e41c6140e8903501c2c240c02600c40d90f40d0440040d03e0103904c1c05040000008940c2960010b42d500c030b007400904420381030803410061501e02251540c5e482c051007008041454030781070b0320627012140014840506030000382e500607a42030800080c02e40b10300003055a0040d40b400c00920424400c010402089040c00307582e07005042414402411340c50709560481510700e80c0c0d18a20015190101060300401d00041c502d030311004142d000540a03408812b036100d00c070b07026004090400c050100b21260000314021000041c41c8c0c0b12038144c1503013400800180070102c1c2c90241746c8241c1d203034010031081c0503150701d0020030030991100721810440d582c0f4000c80190010b118558240c205d03c100022203500030b0080302d10a0718000c00780c000f41e5041c94a81d0b0000c0d042034040d0010959550000d000584035441740032100c210300320361009881d020305887d0103100302c2a0004155050 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 129952365 1250 129951115 129951119
    0xf010609060f09021c06031514010510050d150f0320010f030b190815090a08070f030509060301091b09050f041d100c020601080601050a0308031f0b190306 68
    0xa1034481400f560304404026035112445d80d40c64005003449110502c84034030b090170010802c4191100c40c4ea4049083c503040c019114001044600010709100349a0461554146490703818801c1c8014040c1085c04440024000302c00100e400442c285504a12003174100c1e0402030090100c1421003e8900f426a0307015030004c804000002c201ca000e07a5503941c00c0c1a00d9140b120110307564005840c1404041c05000c45050b1754644906070b9034001c2141010041c104003020490b003000c045a140ea40c982c02080310341c0b80102030b0f510100000f9500c0c005400b000401c1c4031016840c1c2d28030004600a101842c00801d800c124031021b001610400d070104814019680d10230406900c88507000f0340a41001c81e0f0000f002c0c0580c0da00496100c101ea000513405010300040d4100541c815480340910024540c2200d020b40c0c0c8400240d41c0d82c4070b0a004055000c90600020800a00080015a4410074403400800c1c6100b403c08860112070702d541041c0c07000c4c0c0d800701c0c582a440c141c075002d86501d5409440c00f84043c80c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 129953615 1250 129952365 129952379
    0x313030203250b0f160c1e0503070b130806010e0f090d0207060311070b010e04050c120c0607020a180911010f0c110d0206041e090507201e0f01060906 66
    0x62a200d10b0040050104001c0324a9984c10305032400100c031500b50a000480070310b000107a140e144e000b0036140a0404110b100c81306c0041c1c691000b0340d04003400410b9590b0030072100003280e41114807000581c01c07a410b800306004505001d120300801980c1282200b82c100300c541d0310140748004100241540c09844c621f0300307a550006484084440500b40010240d05051840c0507d1148d200060100c0c15078200000300c0031044c14440e8071681c0140140c44103101540704200804a068001004541c000a0102520318221000349803840c07008052149507980c1f420404140101c140c2540601550b40080380203004a03202d6007a140c0d042441c1c91041c1280200c2c0291010981c0b500240001350301038204403094480c0307010060096002402241c540e541e9075882036183c803401c68041400a81d100307001800603214041c03140200f8441d22990322060302e0011040019040b101d4a00d50b40c42112a5241c4800c1498854914140b03448094461014034903201420b42c2d401e139000032642490018204040 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 129954865 1250 129953615 129953683
    0xa0c0507120c0528020307140d06051017010902130b31020c030d0c0206060607060903022a18010803030103080a021f06060807030b0f040b0d050313030203 68
    0x44041d08045181c010b16040c498a010903c50001d1244c100480c0319070049807440c1c82082d0154421000c40d8032007526100c10242d010000d05540f50840d110b020f040d400030304680c0255500c43da140c00c00320405592450130071a072036604080c80035940d5442d0011020741c1446240320008445c1c3c3d00701400b00c00083c0003c40c54181c580404e104800030701344c40c52101003000002c50345028883c0701066458110990b481510381c0d016a01980005140c0311104495600105103580f0810008002034103010880d1100f9020340f40708201102103002d0140d81a00b00c8203d11042540d40c600e112111003015070140500413005001c40c0ca0800481000c1c2c010024020000120783c1980d900c003074080c1d1100000101a03113080001c0041c000c40301e500010700c811201003035000720104e41c02580c2d0300c801c0d500c07100c60a0b01180d030780c0340107990822079010403a03d40e42850f4000d59651880500080d001e250a03440c2c071030543d04001d140140390b204a090820075480e082101180c2d515007080e502011810000451000c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 129956115 1250 129954865 129954893
    0xc032304050402070f06060815070201060e0105010c020f100509040b0a080318030a0b04150507030b030a0602030c25020a05090c03040209070c0503031906060906050f070206041503050a0c0507 84
    0x2080b07400141300307010441d981040c64150342e4015000e204242d00c4910040c0c449840d0319018150050104c000f90500f0b20500030001154015490900f082c0d01744130046a01d0b24000170240d8021940750400383c216100d00c0004580d00b6170998500d5100c113a00d2040001741d515040129105003032102040c004070b42d010040b00c18000e490389465007000740f400040ba0038100f402c02c1c06080c0d00c10349401c20082c803400c2c04d202400c802243c50308100c540d0707a03809c013901290f2900d41050f40580c0090b5490f000911140d00860b000800030303104074100200305d40010018111180214030039614041e0503021402d02810140140c403040b21000307040e240cc1a49000c041c0001030019204019036404503c0b12400348807207218594005060300c2e624504005c86611100203084a82071041c40e0a100040c1944a401c41c03005881c0d003980d6843c6400140b070b061034400d40040070280c1e0700020420000070898503114004400054513140400c01c3c2c903000c050071007150601c8021500780078040080d80c00040d102c55500717817 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 129957365 1250 129956115 129956119
    0xd110c0306060f030712060c022116080d02070c050a0812030c25061a061603030b0406120b010e0c040f05010c030e03030c5a010501060c03230405 64
    0x1010f581030300c00292514003d07600c252607079481c4d001d13084c05005040e000318000100700e80886807101c5075040c1440070311015051482c1010028000b580342c00b417400c16100c40c41e90140c22824201210001c04800300e070b00102c001c440c0f007882024200041d00348094080010440700c4003910345d01c090340500300c60501c13009244450150300041c44188003045e42001c2c29040c4642d56100244403110f24100780100000a454000340011006c298043c2c98854100d460500310714051841d40103441e81c095020f071034590351903039102d40c5486c03020448120010201e10824040c034500c0d40a5458404004c11401000c0d01140c81c1400c100001e1002d44600180301080f61801c1c0703001c040400440c217084404c610000c480c1c550601001411618812000660407a0b81c3c0f120f003101500c07203e142c000c0c103c1c0c200c0030803500c0c0050030610300300030140c036180001a500c501c18510940c00c00c20000a0003421104242c00813004514021684414154010701981c07010b81c0050f130341c810004900d81140d1a50080e0f01c00d040c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 129958615 1250 129957365 129957379
    0x3100606020c01180801060f05040f09030e0d06090503030901140108030f04030206180a0305071a09030607030c1205071701090c0c020f010c06090f03081003031d150c0d110c030606 79
    0x1813500188051664001d0140074000c0080b0b54440110600100c60b0303105843c03145051480140414080b0300c1086c2d4150381c075840c4e00d146010408103114402a100809031181075950311101c002c220180021b42c03144404000014441c03161001c031078948201a00149265070051044810315002d6000b280c007925012503600b03480b14005561001c160a80010164101e02d00400000c00c0000003c0c400c81a2141500046080344c00742c2d4100c8a0740c01109032480d030507484080442d03c038601961181210712240d250000401c00300b0444c802c10f4070350540c4d026000901c01440c00e0344081044040e00d01408504005000e24803084500a00503000420040d101c0c1107586945c81c050781c000e19242c2c080d103600c00403c2c03200190504101110380c0500c0c0080d03004c40d82860000303404610544144007a2541074a5107842d1402c00700700b0401b452200742400e40c10883d0741202e107654161240140c0340040e1100000c06551a204200514844442130a440107612050354040540d07000700c0e496900050941d014 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 129959865 1250 129958615 129958637
    0x1030201050315060a09060201050a091509020d050d020322030305070b0903160302030706111303060504020f0604080c0a05040c14031b030709061106070801050d0302100e030903100606020c01 84
    0xc48401075102a40307552055002440040315900400500112101170300200143da45010319180cc0d030b44a240000e0a0550343e1905210303800d07403035000e44080343c00a42000da00c81c01a0b982d80d0f240c490008061000340c5c0c00800c0c9c44003001249014400d0488418115000a0b444e590f006401ca01030310ba4020020b4002c0300000e20310322010026200d04001013005030880710b0203418003a4807984004815601d250603c04266019131080c012135074504401c03032001c42100c3c619190300c002010050401c99019a181003d50011744e83da8001d04040c02840300601500074000041018040ea80c0d070050b40144e08100c903a10388190040306050340d00d83e5401045a40342e862034041d001d01e12081f019240b102002000b40f100070f41d400301081003541c00c95118925000c80d541119a55400d04031051300000d050307000144200d08007080ca2292291090040b50b044030040404542654142400801c8035800403507180070308e2400308000500b10b0040e034000c001d05410800d00944510090b580281403184130507903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 129961115 1250 129959865 129959881
    0x10e150703020c090106030c12020f070318050409060f0b010e03030910090801020a0e010917121623100b09010b1309050106080a060b030601300509010504030f09060206010302010503 80
    0x5003d901c090010a00549980c4071400a401402c6419521002401c84445003015841e1341c400c858070b40705814100740c10b0803003e40e4103e8810031502080f0903408106000001caa84450003001d2085101d100301095503c541580103040305d40c0d240c8614108400102200610b4038048205c1e40501c4095034502042c00140900f510300d601142d100b540e980d88001075104a0307030740c80510784541c603a00b41d84040841e80c1d00d000b10f41c54020030b035030030b21480e4104000c5800450802402040300f00170304891030780040d40710b40300d2801707541030600910420100f480c00f020a404042c07040d0b03551405050b104206504184c000308403480014080c004c030140002900031f180e403040d40001e0000386581c02c000e114560711214010004441610b100180360b0400e5400304848040c80141d074412101030391aa0001d84a804c09801e03004019009050910101c2c5ca6a500507840e5006c1c80e44141c20f40400030440d81030500d0028200a015007004041000c40311040c8081c550102d1140d04483e02480d004c0d49907298115 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 129962365 1250 129961115 129961123
    0x10e0c0723011b0206150d060e060105150c030301150c08071b0509010617040303061a0418050c1b0106051f11030a140708040f030b040c05010e15070302 67
    0x80a0048440002086090042100d107541040503100092041100183d401c40c1402520001100944c021000003510002c2540e003a102c968001030500c114014a0f485510454100340428181504a05c0c014440c0d410441500032040d010204a2403a1071650310100307440f40010700506100220031201c8041062240080c403000c0b84d000761340150b81d070a040c0b40240c003a403082c1a61846500302c280000515142840150381203a0603034a0729002408410419103600b540100200c05044e660040415072070002c40344950350041c80789d101a45e40c1d0038001291020401414011003040c20001080004d074640d50036590a8132001d620007000c164810381103030142200d0707003110f60000042443c040038010b950310f00000f00303003c0b621800000c1600252039500d80c0b045988030004a01451040c00d945180d0390002d00410b4005e2268078105600c84c0e1485c0000212075006840d80c7c820703c0700b88024002002d101c42c000307200c01d0070802590031008d070101e90082d030801000100030a01040200516000744 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 129963615 1250 129962365 129962377
    0xe1504060804260307080702060421111609181101050a09181a0306010303020613020d0b01080307051c0c0809040b10051803010624020f01050a140a0b09010e0c 70
    0x622190f820310ba00048448030780040304c0041c0003882d9400464034190001c43c1c1240169005404103128030041c102013050070780030f4007251080082c02410991003000910000310071340c03690408609810300d011070342c0003650103890074030b03c00803030054856000030050032000342036100a080480e00c0700781520042d500000580d100480001101d1080c0701440021b40c000702c030000f134103462200c1c01540001410358900c1e003400700801507031015000c603400f0039100c0191091103100411120284001c1d5852444000003a480f901841e400405d4039002c100061003e003c03404c0e8041c0086405541104008041030b180d210050030341c00000411041c00c3d112904843c40d8508003420100d443c200d80131004080342c1c030490700c001802c0840e8610405520701805903d00304c0c0c44090349000d124640c0d00011017900d40e1444501c06600c545044171000490a01a062203081d034800001210b02d041003861600081c000d1140012901d800340c0010300f503550040d1079054a419038001106036403000c2c8101480d00c985 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 129964865 1250 129963615 129963653
    0x708010207060f050a0209030d1202131712070506060f01030608010509060f010f24020118050a030306240e03070815060f0105070302030a0c0606150f0e1504060804 72
    0x69480601c00141c20038203c0c4030201400304800d9580021040807800b4002c549645504441c102c4d80380e0900c0342115030903c10403ca0010710b020401c210409500c00e8503881a45181900c281c244940070091001c0c2254420501c82d091402d00240e0700c054503000000c0142c3d20545100c04d078102035900c2030b030022020303211650007000304d8200000aa40e6504003120400701c45540180007041c0c401013150741800b202c141384d81030041006040148103031100c01900000443d983c0d0010840b20305c0840034441e09450041015020f8035280c0c6c02e0040959803603030032440309209500e07100400d00001c040c050140b500c580c940719100c0010040000d040c1442d55006081c244600c0807407150764007400d50380a0042a00b101c1c246002402d10b0015103003401800c0000e00507030404d20005a01d540515106c8242c54402e840015525441d00c03050b4072a059600c65810000e003209403c1030130183c11001c1c8500d250811114440e002d154907103184600c0c460340c00f0307a404010301e61010404104080d00030398164804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 129966115 1250 129964865 129964867
    0x1308040303020303060307140a050603061203070807060c0801050f090402030a060e0c0123070816150c0e040b0a051302040e0c070c060905090c0a050d111b0316110307080102 76
    0xaa4100255031340c1040c1c0300f0512902650358001100a800046111810303400342600600307034541010044070340c00080586820901c400d00f40075009070140002c00046d441b07100c2a940382c8000e81030000c11074008140c102c0a0050840060083e0b9443c600c2c59180384a0448101c402a0795070310102c4e040661925005080e1400c4c5040c03402040300c0071808801da08400c1c1c4c0d611004241c400c01e006030684d12484140680700c010840c15000c610b811008000d0302080b58090034050800b50b5912440403e185c48000803680c1e581c81b0790884540c041c59035186c200040f0380034400d40ba600c200003030103102c4038841c85220f0b014100042aa0840580540300100491444201c00d482e0591407061301c2da01c81d5000303d03240000b00d040811060f004048600541c0c1002c0c02d0b002c200e0340c41001750b09066010711966010321a0a02c0f100100d040b16004030601700d41060740030342d01c0ea6504c2d03480881d003d440140700d01c020342050000810741403814000d8803810f5000883c101c201c56520010900b8060b860300443e1003540 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 129967365 1250 129966115 129966119
    0x30f23030405190b06131b0c02060f04060806091311040e0a0c03050a021203030f010b091c030c0b01080111071e02210c0604031505060a050a1d1f0905130804 69
    0xc2c03d0b0000b80d10641081d00c000d05840741c00b400480440300c41d1920380f00701000f0004447d40389842807601c50034040c4050081031074031140309480b07503142d00554800d50000d000d4004000441c100201d000d9040400b041081040c585142d885d007514001c00ca0700e05001c2c40c0d9030400803445c00300801580c807000d50412260140e171626414116200d4403100f00c00d074083c06a1440100c694080081103c1c45000072500c03407001a403d060000c62140d000c815815071003150182c1034100340102070004503035240b007501d40000c0c0407207524004448480580c400031060f49841e0041110302400d01c11030703c60682c800501c40c040c000c10b000800d171141860001941148140c178820742440907100c0103200c400e00a40c11030310b140c036551341040f0b601d1259010040c02140755960740c0041c2c0d0050f0300482c3e046070006200d01c61030341e00c0d040030403690b0340c0300c0d4001c60300c0300e00c0e40100848414041c202140c00c40302220b4401d00ca408a1084440a00868860ba080130b60741e0b1400128021400045014150f45c840718203540d4175 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 129968615 1250 129967365 129967373
    0x6070309031e0903060c171602030706020c100c210213170a030e0a0b160309090507020c13090b01030b04080706110c010b030c011d04020f0a020a030f2303040519 71
    0x3c8442d0204070b81d60391620500325041030080300100f44501e008086003085a42c2c4002d08020f01038030008880540c031080c0143c40014207107002601c04004030310010001c082d55100341d001078421469024080c40f40340040c140e03440c000d00d00403001d4070700602c0015a44400780b003440d074000e55283d0b0000f0701c0d1484801c40801d10402c00728003000554003a40d62918510b14032001c001c2c80215910400440b40c80801000f000c041000c4a081d00e414042d05200c4800f41c0c1d03800014007030305c40c01c035120f00042c0c00c038a030012543c0c6800200403610b00440c401c00c100f200400da44104900c241800054203603940c40b0001780030403000034100c541c1d4681c0f000c000c2c0400b9001005c14041a0014620201d15508000d181c4069003000140940c007950143d40d141c10483c105200c285100329144230184c0c006408110400c03041c0e5a2200902014650f40d00a264042c002e0074010188213080c0320400c2003148500b00a560b42290306282c10440e02407000b0541e503502c9a18040e8a06203803481c4064000600c15941c1c003c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 129969865 1250 129968615 129968627
    0x204090b0609010f180c20070501021005010f0302041e0f0b130b0306040803060f152a07060e0112291c0f030e03070e0105030705011106070309031e 65
    0x80405490100442e40c80d80000340004c0c040c2c1c002d641200ca852444d640c009002a0000104005e20b400e004c1450b2454030240b003140708541c44020015846030404021b10b5030304000e84130381d4280040c4200815410a41c00b903039005242d00c8080d10440d141d04100c1c50b29800c3c080d41001499900c08200030441d120071200b005407480d80c4441e071141c0303003044c014640c0132043c2c010300d030f18080001c0260070946d60f82e50301d8403481d030005000144c0029060b0404481602c8210b00309100007418031109894803500c01c150450000d00400c0300825012030340c621201c00c2c40c00603c0c50181c80140c00c005d00960044801200c0582a543c645c029142c1883c2d160405580c0c1b40402c059100e803000d14000401c003030300c82488001c85496064480d8180e6800918010070700000c0d0400c50340340300745005a5007010b404002483c200ca5038200355006502c0e58010000362804100940003400c007800c04003208209255605e8031a900203100d0340506460790003105c02c041c455a014081d80000000c0f003101d2040001d002444 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 129971115 1250 129969865 129969871
    0x30201090608070c1412041202030105010909052a0627100e04020f091008090c152b020415030b2407030210050411010216260a0204090b 60
    0x8111480008a07916120341c0145205800d90345840440805591301c10700d20754074004810045010703900e402e01c01d241b11840100010328100f10610b4144609004141c01c40c0d4042c1d00c003040c1a071402c12003100203038020440318809604410122002c18070307418070002c40704119001590003800016490000a000c4520100c8001c0845105541c5003109040c810300005024603000031482800340c250203441c06800800806018400980c2001407444c0481c403042c405043d5200402e286030100403061204100200e1404c40881d4214018170b040b607111801d500c20012000c03064000d0351040c81c0f900516000c207821004a0303513421582c856580c4911040109000b1000c400241040c541c103030685443c200c2982e0b0300343d0800c06944076003c2c8203d030100d50340c4174000440c25401824a600c2607078003540305003446140102030702a8065000300c002801d0880ca00103001e24180320060030f1008011050b91140d82c01d060104080c202104050840d1501e000d004009500c07900b48091202000302078909980 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 129972365 1250 129971115 129971117
    0x40c08060f01080d03060503100c03060e0103030e12010506100c060b0307030606061409060f0c0a0b0a0212070c20060c0307050d03051308030a050c040503031b0f01150e0601140d06030201 82
    0x9294040310130100c0c1030340c9441c8983d17a455402425101768003880c44c2d011151140150400040059130b8030301c420306011090f0f0040d00400e086602e00340c03e80c14221006804c19680e80001c12103840d201c00001d60070790900314650308000001c41250200076503a4059125030f14001c00b2180305598074078021003e0106c5001e02d9000542e03288084891010000a1300c006000040c1507a08000301960500020b4000c45204811441400004004130b0b400f240c42d240500609180540d40c3c22000c070a00c0254040542600d01300140d41c000307200403421001404402600d0100c01c410556002000076900e801510390f02c0585000005450040020014001444507a00c3d2000d010303030791b03550342c5400b414a1100000b0b0300016080000074113216040e4002ca030701c000d510a03800d0a06440e031010a146801c640b010b280049031040121030b1122003000702c4503564102000a1101204c10440ba03442c42d001842040741c0c101d101c02c08258940c0c054110400c10040517024240c64100c2980070101801d454441a4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 129973615 1250 129972365 129972373
    0x1614010b0a0302010917072d0b0403020915240403050706090509010b0f040306090305030609010b04271107230d050a1803020303040801140c0301030c030b040c08060f0108 75
    0x14031942050301180d4100d0341c050b1100240c852030030800c5401c00590401003c620301a1250200710b0b400d105810345601440e440d10100c41501d40c0d40390f910f03100d140383c1140016901c03e00003000184d803403c0000b58800c40d00000412890400c81c00701f070f04c540800c0d912038078190b1400712102042e0107020242003228091411290403c0c3d40381400d441a14441c01016004030740b5100502c085c034086002040d00c88031070400c2c2413030650f0300e4445604a500c91032044000600005c140210ad10384180b041c1e0140c41149240780ca1300e8038041d02440001351000320440002840500750140101c40e40c0405a02c00d04102c0455403980e0724581600ca0382080114500b02c036055989881d500c020004135007488042c691a5540341c80308182c0240e0b103400a4000c510351030840d004011005032410f1016100a081410003c903000c41100000341441c04000c0101c03c0a090070300041011800400003c3d040765045006040180c903142012502020550170116441c416903043c04421203858440c94103c484c00c0c0103031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 129974865 1250 129973615 129973631
    0x30c07020310020301060c030810030c06030e100507051b01020d02040909050d030209010903020f030c0a0602030a030617060408030606070609120e030d0c0809010306091a0a05011110050606161401 86
    0x18004a004c02e002d00d00c00209072802c0c1c503000034003e042e669040142001030009242c0e0b030f80e60b10b0171400413039000500007988941000b1031300c540030449000c0c1900103103014021890000d800821a014a4094902d41c07000040e044014040a60480341c0052202c8400d554075900d03181e8403c050140c1d0710b400c031141d2055803403440c02188640b0035514a90016583c0d0361100340f85400b04020001c0880145034180248140c0d8062603031540840001000c02e41c0103581c8070481020041d0896000e0380c08a14000c221903501c84000700040390b0103038002e50000c0402e80300d45035907010030082d004055004200783d280a4000701403041b0030045040581450703440c130300580700ca01c09054031200c0c91140035020035158161070740018502c0b40542015841850300281e629919000340064940e0b00e151917800080000e42031840341082e566941c041c000c282045203900080b50100c40e81c54007504a80101d0716078030004038007656205811200340b544840d26540000f5050b0901d03008105a40610300501e42c46c00c000707 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 129976115 1250 129974865 129974893
    0xe0f15010b120f0a18030801080714090c0310081605030106170303060d0503090a030f110102060405100f0b1003020d060f1805040507152606090402040207020312030c070203 76
    0x1291600c40c0901204245a168030303c161900a0019002e80042034442d5041e196a80255030481c4615019540d8048254940701c0400c0c14041c1640000d503071f298090408190b2a12038842c0e203600806c07403180c0c0d242c9c2e9a64070000c2d800380f1151a001078400c0e0044484c59090404102c851200340e4404500810200c5e68400081040e00881c0c48200c0b13540e0014000256185841c00da42d519090150040d42d08e04204003001440c0d0440a0301f00311400c544031000c01d818001020203115090000380018503540c1490344420395101004040ca4003950784956686440016a400c1503002ea0f001420074040d21442280290281d04414489180e00e0b2821200240403004009a01304480511b1058940000f00c00c0c00a40a018002c3c000d0394180f08880780010442d019052117003240000760b035030782d031040703c080d01180140c24080d034407007135240011050109541da50074810390130560441c0c0c0146d4a500c1840032038207050844a00c41d4807003d01000b0070800c036201100900c0e45034400c5050b40c1c2e241c850454 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 129977365 1250 129976115 129976117
    0x60705070608101409070c170a110102030f04140304030602070c0603050a0902100302090103021e0304051b0108280507080a061706040204050907120602130909030e10030e0f15010b 79
    0xc40d00c06107201000c002001810b0038032070f080c0c06c050303540340a0040a481c0c0d102e04140300403d04140311030400018180b98820b60115510004031a41d0b4003e42c61820524030000c03002201070000390407048102c511042c03890b001c104680c01103a001000b907480d54200c0c1401d948401d5540b00b002c0c0401e05200004509428601c0381c503900940c0100f49074411000b80ea0214000d40003000c4070b50500d03034204804000b40303070001040a0311402d030a00d401e54a203403519245003800003111440c54200b480000514003680c0004000340c2c415440400d01b00d040c0141141860480c0c04002c25403410703890030080c000300660000c2414480e24605c003050026036030740d0300d81100c0b03850140415100c94000c0b4003c100107142c150040c0c2e411251034000c86821944030b0341095903590b00c11100312015075001650b640b446206c280000001e010f0008104400c445d82d840207802c50081e60f00d000c0c803070100c0300c81c400040c500070b81c82421403402403800c65071075005080015588880884c1e070b840c5450166400040d0020202c1c2c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 129978615 1250 129977365 129977369
    0x501060216060f020c0d060902100503090712020103020f0309010603050c011d040f060305071202010314070e01181a0301030c14030a030c02010201090f1a060f0d110a0506070507060810 81
    0x944019070510703040c01103076002d450240e41c5045000380b02c1c403102e050341e0711108a04041d000304400102004179204104031900345c09400024071409004010031030701c0c08102c20701100ea854000604549040c80100d0080c45114411080c0450100c1400070b00d400c1507001a05a070320800c100c0f0243e14105005560801c151041459085800d110402e081d090581281103911044140414510307204e0352641e0410003a9080703060030725000b10b0343c4025903a00d4001c0e4055107003011b1411140e4200958010800ca58030004141406000150001c0300980440300200406220b240b0442595800d840e07540d03658420302c410b40d00969000b8002c070f02da510203d26807640000c000c000300010280c03580e0a0b0b611100030303141a810740d541c40078030401007580b600f41d03000d0440c07081c2081039036a41086141c4d841c0c0e0102500d040d000708090342054005031109084843e8030764000c402c014401401c1000240001c62540100340c100902140e08002c10800044010a86005481f1400c260b0380fa02d92400003101a8 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 129979865 1250 129978615 129978643
    0xe07081506180d0807050f010c0c030504140f03030c0a1104060f18110a0903020310060b0306190302040e150f13170d1d07080102070f0209060105160507030605010602 73
    0x4001140840c1c0180040100c1e002000e003503e04407801544a00440380c10141051300d45410625404026020a100d8540350b44a030382010404c03401c05883c010460301031401140a2a504201d03c0c0c0b0940d560301e4034540700c0a00040c01c482c0d039850901102d07a1100c041d00c0048511503050030032942c19240c00d00640d82582e280d1600b592140f440c2c8051103a042e5800c691414242c0c3c0d0305e0003c170158424035402070034446400d440c0c503080307549584145460700341c0c11010b04152525011090090300c0c103c03412070ba003000d011900b114005e00c0c1a412031508607000c3e407000b980249040480b1138540c1c408104200c0c0000d000918498a03503484051040b1004215107040490340317a6910314000410f042411403448030004c040070b0801c1d03503040024048803007001e490a104a0309456803501031108001000c09441140020340c1001590f9560895a46010500030312544841e0000360050b44510199403c864101012914074402c608166071505404e010658889040030700100d0201c0c00020041000014 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 129981115 1250 129979865 129979867
    0x12d0e0d080304080a0c05100501050a1d0105040b180a05010e180d050706090605270309010c0204020d0e0601031406180d08040303150305060f0a0b0117040201030b0402040e07081506 80
    0x70756451300c0c0a82d01900882c020300818001c80408031380100002a03220645803000196541840c04100b01c1c80a1139120002d4601c0c00f1040c00d80b140d149241890440b101594040780c0d0f80c14180010f8880f201541c201c1c0001514241040f00d000c40303070f8100310704848c2e0041850703056846140c482d00c0b1801c18803410780a9a88504026011030788a41d004114160144200140d020520ba656600369002990602c0c0e41d0221040d00c00400d4a031074120249851030400114a040c4034540064010070b182d61300a0310659000c907208a01444c20340101010300e1083d03003a01c0c007960f100c0c1b5001d0400200444405200d100702e03000940f034a80d00c8011404060100001044a031000c00021500118010011000c154072490490307540109245540003862098001e05482c0c686010120680c0c1001048203032000d04288070981281d8010b0002e0000791108030030404c9550712800140c010301400b50846d40c0151001800280854030104603a0180c03403241d0321040035840f001c0029910140600d0341951180d8 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 129982365 1250 129981115 129981121
    0x6070302030a0c06060506030a0c03112a030408010509031903140a0905070308191b020603010b2d090907030b012c06070302010b1801060c030e012d0e0d0803 69
    0xc001c0d0f001100c0507104400124583d62100003040141d0019540145207984406a0704290f68260150420b4511030712482c50911202840c0c5044c8203034410480d44c200c001a2006200214050048901410f101002480641004c8030100d0343c079408581e20010300f403d00c81a070030b1002e210380140307043d00786401d42c116155260010008020450040304903928800d42c40e0000000f02050050a0402c400c00c02070b000540050794042e2440302c01405000fa603076540e180b803900594489060340d066614600c841d584884070034040c04150150040c180100ca213a20300c40480c91840c1c00c0003007003801c81c1900d8a11940d20743c808182e040e5007034900c0c001c0c0400e02003c60b1500c80715000340b84210701c4c00340d815082c1106c5007203000f0901e2036010340c174180c005035182e060481d65420030a124001603e052181582c180d8035200000302420303442030700202045030101b44421a68400c980d14400c0b200183d00c0380d101010b00e0a40e10502080207002c08002c1270600d0780d13405461400b44200f00c031490304981604d02d190f07 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 129983615 1250 129982365 129982367
    0x1503050c04170f0a0302010b040f060819030c0c03080702130506032127120604110d1112150c0a0c021014040801020304060522020f0609131a06070302030a 68
    0x208905000302d400e803107a2007080704007000c20405a003140340650000107503101c80005000c1520203d2100000d401c0c18a41e0400251000040d1121003825100d00041c030a00c0c5860101c984108403c00501490040a404010f12040130002d0103501d208035030112019080034010010b44001311a00d9900d5000f020900c00311019403404041c0214140d04034514041070b201c0914240ba0402801084214060b90b5841c4035040c440c0c14880d071110040c000744428980fa51310202440c0d0740b60703c00b5020340300c2c02c0d003e5001c00c541c0d0806c001003200d00410140c5450300303122401d640c40616601d40581d083d100e00200700c9080c42c0104a9102d01c040d5a64020b20302e5032134084c0704a00d010a070442080282000550119000746d1001d4406440b6031000548d80381000c0c20400c041d0713440130389002d00c00380151b201280b0403900008030508080d13041d1000c2c2841503d000008042d8024801c4550b000300500e030140281c1c8945a01192420322030b0004080341209180034010b00780030b002801400360b402004405001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 129984865 1250 129983615 129983639
    0xc01030b0d02030a0f150f020c100209060d151505120f010b040e040507120c0603110405010527040c02011409030405010f2a03030203160311031503120c071503050c04 73
    0x10a018800e40c00d0004131440300303403040360807c0b02d01d0300c0104c5d400300e4404903c079400c0c4075203042c1c45c90f101401e42c144039407400007940c148500c20001b229141d885500300c020704015080d03d0024001c1d400c0300c071400c0c1c101c200301030040c2d802005040c0a10348100006443d00b11000501d6050302c00008406040c24101030717044011160242080da0f951041d100c000a2410601143c1d41007144100c110a01d09441e180c1d001e402c2c2c9012407100d0040a50501080c82580d0340501600c0580310b488002d0600c81c45d0312080f244400307014840303450704641030031403941415405422181e98248040816243c0390703104040c060f1240100c1c0200c40c0013403000e034607a5960b1440b03507100d807101c080d07a4100c0e000b00d4507106031500d494403060b4000303c02007034000c0104040b00028034600741c8180d0380c42c1802e014140c1c21072601d403090300c401000701141d0180c40d40e6200844e1810816103d003082ca5070081d56892024505440c0e8842542c1300b400c1c4205d03120725031107841c10320900a6a018a404030001401c0504001c0e0044803 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 129986115 1250 129984865 129984893
    0x3090614040302040e0717010605010507060903030e12030610030204080303072d0f03060605090d080a02070b0c10050915040b071704031106090102070807061113080c01030b0d02030a 80
    0x301480501021025070342d14070962110b009054001c000030b6107010b00700114000703546a06001e80e45490170400a80c0d030000d04032040c881e4850000124014030303140a41c014005404d1101c154030454104580010b26400103500615044032034521071400342c1c44c00c5040c0d10950051210035041480800d0308103004a81070460300607400000c01080c801c0c0c10030f40000d84440c1c08140000f89056100b070121a0300340c8201000391559181252521400c0c0340465060501071070014945000040d00c40e94440c820700144c0041c242e80029180e460700369020903580e52100c039041165003450000410b07885080029140a18803480344404071950742c5842e0710240307810051000d82440700d12080c07290790601e40304030144a581300b130700c40047c50b50030600c15900c0d082c0d00810603409a8810840c00b4045000d4034140c41034542d0040000c1944511207000c8a01da00070494241c010380002800411060310100e0000380049013a130b0104084100b010401203130103400c44010350183c00110b03824002c034a000210580f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 129987365 1250 129986115 129986147
    0x72304030b0907030b0705030a062c040507050a0816080703030804140c0405190b0627120708030c012a031a1207060e03010516050a030b09010902030403081003030906 73
    0x900f503a40c2c0c2e01c840f03098260444004000440c00410480d09403c1c1e0310400300a07059406000c8610380f00041e10520810003400d090008440c5900040c08100d000c00101001c1e041c090410b40d1031aa03111000d07541d4094041c10582400003201000c40c404030b00040070402c9036003540d64180c0c152205d494402400c00d03181c1d0b414585015040e0f00d40d00750f0b01c6a005407802001e100181d0050080d05103003820403030f080341d02903900c0b414003006800c43c03040c03107180030356140d4032080c10304010b8141c00d4001a03061406003071112868041c4e003000180203c80440905802c03180040248413004050f5200c1011460b1140600002c0720404070340b60340680300390722044428040c000321500b090480c00c001640c0b4082450641c5413540101070a1003020b070b0000d51151049003c0e0000d0003075082c041504c0e000c2882040f421010001c0100354846002e10a0b04101c10125000e460501e803943c40c0c505100203544116010b0f80400d0000d80800c00000c0b0b030041402c1140e030113503140ca4866051000c210750804084c03644034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 129988615 1250 129987365 129987373
    0xf061b0a05090616050607020a050c010509010201090507090204030506090c06160201120e0c011101110915071514070e0f04050c040513020408010c021c0807120c0305072304030b09 79
    0x9400c81d102c0100410304030355844004001c8501c00c0c90017034a0508020010002c5404c8402250009040007540a4940c03809080981d1540b050800417401800500e50240680c07240440c00a4100c0240d40203109607400355023610727010b568030a42d031a5600c410206080c2c21403010880c1600c6c0054500a070800382d81305141c0700c019007007101032010075105418025480c17500704c0417000845603040140b000284030504003d015a5103004c00d40762923806070141050041201d01181c01005c2404e4086402c0180c0c04451075007403030190f80815005100304031100101d814a07402141d00107004d03680f00344111000500600b052903628041c000600f0014200750286401440042001c2d900c170300b82c1e2074024840580068407a89040403c50a444243d2050270a42d00513a4440000341e84442d0941e480c0c000c1800c0440c41516904012550398426584120045180013000065598035070003881c00740c100341c1d4900605400e4802d025501c61065122400350b800100400c0000410306203007a94020f0610050b5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 129989865 1250 129988615 129988627
    0x1209060f080a06180b0108070306030206070f1a1008070e060306160504090905010509100203040c060302070201050f0409140c0a020d030b0d0503030115031109060702010507020a2103020f061b0a05 86
    0x9900c08204d4207155651454a9590704889940c0c00b2080035400721071440c0c00d00101e031450300800e0251080800140000b18440800c8040c0151f80400406031500340108003258500000c29400705e07209401440360f1802400030028003200721840050003090010041c0c02240c8500c00e03038901d42030828180742c06026080c000068100460302c00c20f02c007a8000d60000c601d1b0310b40420300c05c1c00c028104181136901032040c810300001c1141881c0c41c0007a5041d5040c01640c2d003202d400186c40a000ea15030160003440009404200141d1503048410140050003620700c142c0c130340d1800381c002c2e4007601e0000c030010b030700002c0c110782c0a070700c280c00011802e580640002e040e11020749905080d0b9000340c02c00042c100c612001038200c0c9506101e56004041200b14460415001200190a91003131220290401001040f54415540d801c00610010300003038550381900d2840140461105500c00010b0300035004800e4041003401c404186075120740900920400420309a9205d001140c1003000324204000c801d102c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 129991115 1250 129989865 129989879
    0x6011404080a0308060d0302280204110702030c09071b0206070602030a0203010512010207032f06180d020115050907050706060e0a0b01020a0221030705030301030f1209060f080a06 79
    0x14005051844007030314040e00141005031405130058200ba0180308240b85a4012a5000c540c50541c4800050320584201c400301241d26080c1c110714020390702c14609420000800c0108000b0b060007442036040d14800007003002040340003003040f0b0b40040812104030418000c10300c0c0461614500d8801032210b818000e05031100802c0342c01c1150064085a4000300500c101e2510402000302c1a491300000c0d4900304481d540141248001d801c0340d404200508000c000c40702140c4400b0512060040840b001481c08030b0395840c03103038601184140380d40070340082ca10310248107026032030750484500e845d280001d180200f48280507500a04480800030706126004c002220341c01400010034460b94081c080b814a003c012049a40c448a440d05540c020500400140c80d4407800b0524240040c1003040401c2c41031182d14214450030303500400300e000000000c4200601b440e21140300c980240800550078601e00c0c01030f1140d8801d0701440303021034165403085245c0345c81a10000d521404d89003000c10700540d5044 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 129992365 1250 129991115 129991117
    0x7080a1e110702010201110708040b0f09040906240e061003090803100303090b120a1e1814010203040305180607060c02031b06060a1217130f0603090803070503060114 73
    0x40003030160748000601c0425581c2c2401a104401703107a119031841c00071940c0e00e2036603038815881454449807001c0b6900b4625246401074421080300540305000001c003c0c5042c1c002004850380304034892000d000000c4218031000402026921014001409500c0380d00c00c00140c0005e41d01c0110805071174400c800000381c01c3c000a50b0160418400050015082d4035001c0d11059158000301209081030010004d00707441c285145070007141080c0e000500c50440c00c540b524100311885407002480c14810201140000c101d60001e81c58046c0340c6007980548004000f60a1707100565024000410074003009003440c00142e0403a0f00c4180007450356140c03000555900c400d491a448280c000758001040c1d00441c00e18805102c02d0303a1008102030a124584400098801358960003076070049401c010640d020480a410000c8107030b0b0070f100b001030302da0031003031710724841440346010700c1e00081803500e0001078050107401284501c0f030f400010340b81550f03034044048580f604001c3c1442e04202d90b080032031070302c1c21001e0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 129993615 1250 129992365 129992381
    0x1080718060b1308010c020a020f0405150a180501050f10050d0b0301060603020c3906040b160311030c0307030e030c0d05030c0d0825090816030605090607080a1e 71
    0x70040c140c10a113801d001e10700b11140c9a003248255044140f09500585d43c2401c042a50082150300040e02c0c0c495034404c1d12000320b030300101504910000e2002c42c082005540c042d02c900200d03142031180c1da0700d600070b004480f1000c000300ca4100100300e60440e052070140010300042c10300f0000000f05003e4010000e404c0d00e5041d4824004a40c0c0050309441c000d60903c11512800500342446504e4900440b04038401d6126030110b0400e090218002e96460b0741d0503013203a00800e518403d0a44815030b03030159070851004802e08401042d082e50340c0d48104003010080d81c0186e00600003950401c501510256401202c1d48075440d418040c50700f9840385139840034000000700d03000790000e54545940a840c1403800d403485c07044809105ca034800b0131080346c1c4090803480c09840c3c0601c030088546642407080e240b210751038000f8201800303190030b03c003500340c0d100c0b103081c00f240c0c0240c8081c442ca40300c550074230751141d000707071014000a040c0740005005020181c203c11303d8200c440651000c2a031082620400300c401d04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 129994865 1250 129993615 129993637
    0x40308040f050d05060403051b070e011d0403210b090403030b09061918021e0a09060f0f0e27180c0d1115030c0a02010f0501080718060b 60
    0xc10140a60801c00150001610054508000c80381041d11480e03a60f80004000408121000400c08020046554003030003c4d181a800c942c9902c1d1607504c0000c02080c02d019004140507040c2400c1384c0c503103100603218080d03038045d1240c1d492040300c801c140c000801030014040e2200e48400b41c000075929032250740d5210750b0003581e0020340d2020217001c00180c480c029101c02c2c4100d4a1000c90103c584c0306c00840c1c001c40d80c134103441d800203031010f8051030040d0003503419465441701c020301c2c075440780440c0900518015103142e4980d540141c40304400e4031110b441000d0f501c0040c11000000201d68010000e40d00d00c60801400210060809041900e10760060b2070306001003081704007480408640041d80898048030b91014110003103200c804600300900c20103000d00b88840b543c10720040c1c2c0d00c8060040d10b00050050100791f4900c2c100780c0c00c500b140e100b06501c400544c40c0542c204582c4842c0d206807416101d40034050305100f0314004004c100428420b001503007466541d100056942203ea0060440c0c0900b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 129996115 1250 129994865 129994867
    0x5031c0b010206010501030b0604050d0f0f080a080c160206030a1b02010e0705030a02010e150d14060f031606030e0705060c1e0601030b011505070b090601140a0305030a140f040308 79
    0x1030009040640680c0003d0515041c2545866940e54070802e480548009442099104c001810030401d848000c0001412400300110400c00303001c4000d0050a9905030303611004241d03190205c10740303006d21801380d01d00c0100003800366030001481d1280007035410811103400441c0d1503060314140f1130b010350100e4015000d40e641e60459400003200380030910042030224050258108a50006805004d107880d00300d1150b1112606d05891080310400d640307a5030034030f1008000503480c054080000001c06e640c110f02c1180c20200340382c1c09240c009800380d041c03000b008240c50160300d0310744194003600d50041268070701e014114000c5103d03200e0b2405082c004070624010000b821441000c00342103501c0c408012102c2c0c00c20401031000c2803200716800d045801e030848000c1c14101d0309a0440d110f001d0780c84000c0ca840811424403035a11000180303681650360384901c11100399101c0c4104a0030311489c4c4002455038005201d10b81d2154041d111241c0f2046000341040d1410284100300da5165015800403200900 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 129997365 1250 129996115 129996131
    0xf151418010510050603130c030b04060b030a0312020f0919170318061e1303060605011b020904020d050610090c0503090312100f0f030b07050f0409050405031c 70
    0x26240d0050052640d00d28020801810440060b42d402c0503980a03003405400c0c0000402c0754035201c00c0c0294202c0783c03c5818210701301e4032441c090031494419501070343d80900340303015503881d4580410848171156164581048041900103184080d41141d140c0c0c001c030040074801100303643c80301d035203200c07440698a014544160030203440f402904522085031880d80d200b030004616501250000006500307049031115160b801e0841652100c102078402103d0070030011440407111040c0002900580e0b100d0705050203400d44501c01104c07110701c4034041145403000492210b0250800007041170b08240060403841501d0700720b4a07141e1514038140c40c44c40345540e1a5078100241d15152003a1004820b040c90041d2850510412030366482c040c2214030580d0f0306c0b00304003060380d504100e403441004140c0340c009101215a542001e880300c0031244000d44540480c4000038541a105208580d850150074144d2801c0508100c154401480014400c0700d0a20080042001c0c40440e0143e004103103a07007440210f0116 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 129998615 1250 129997365 129997381
    0x1204050315040c03030e060d0c030b040e031309020c0f0d1107060206040309030204020309010b1003020903010b06030709030b070c05010f050915162724050c03070f1514 74
    0x58800e5220a4141d081e02404009881060b03020101d80c1c0628004040c2003103900043c01c944980d40750301e4100d40c40d00900d00400e64054012081e0040101c9082100c600b0040026489103d039440b03001d00045607100030700491406902404005540c0da0449440d0031010b080d013850b048103000010b01180d00981100b8060b41c08005200151086102611550400f0303030780600400c0190000901c0341e0b40104c009a0100703000d40c450156501c0c0200b9042541c1140322000e0000e520602c00c190095082205508071400c107001102c1c0600410f0f0b4840c910185181c80d03100f0785060192800013002800c0c54840c0c0825800d001d41c5c0441510f083c00004c040c02e022491614000010000e014219003040800c85400301a00520751595064280300c180d00199802052103001440307000144001c26050101c0d19804a0030b442030040c14003440c2d0750800c0341d40d00d400c0c0c44500075241c0d440c0855004121140000d42d45180c1c203803006205182808200c0c00e03d0010300300b69011401210075511850081000785 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 129999865 1250 129998615 129998623
    0x140108070b07030804050109020d1412280c0f06020909090c0d031101110c0703050f03040f140103020f1206130b0d14030f04031b051c0b0c090312040503 67
    0x42618000404580d45041c003111490b0103078000c00307801c3c0404040004d080c0402034001003405a4000c2044a0042003031610380c0c00020800c803280c50b20302c03410200d030444650500c00c650401d00b16010300f102a41181480030038004800c0706010401c0141a444000503400d41181c0e203109200e60030258407a03c1c0c050501502003c024106c00041d441a025410b650300c900c141c12450301c2e09440d102d02c1c80a03021701800d001d0705a0076521094103400241245e40280c011441405803407150003662003400762800d1050b680d004500407054040e401900400540120501465141d90f06050150600401d407004800c42d4000c03a00300300748402841c080101b240707005031404900c00f5003c1c030304002001c00c11010070802c1c0010031340103102c005100500d000c03c0ba020815140b80403544811240d8886e01ca14220b682da0303101e4022448140e4000c0070205403403a106100c1e0242e156010015002c00d1699250207002c84009491020854400c1200702d00a4030705000403a804801d0103040366445190406051038 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 130001115 1250 129999865 129999869
    0x70e100306030201120b0a0503030d0203090c1f030c030b0a06021c030c05070b100e0c04170303010501050d1d073c1205010b03011a01020d031109010302070515010602011401 76
    0x42501e8140d080c00181c0e04203005060034212040006000350070000400c84800c015000554580b2001c40c440d5680720590300118407500b42c2d801038a5612802c502817007003880c21504008030307954030303000030400252003507010440d840da09150104500740d10707001003020100690040ca00680000303101c0c0c1761051050201411507252031030100306c000c650400090035400380310002006030115a000c1594818115416030107010400041e40d00340c10420010f01c1b03207901c035100d1010300240d88441100101400b1007924103d4106841f107030b2500c09040d2280d001001800c008880d0100d140b00d0340b884022003040644041e001440350071409021402008140c41d900c80341c40300e41e01069180c03445440c400542003c048a02c42910901c08540314903069014160203500141c01d50328080443d00c6c405035094940e4240d031000e030203503032101031040c0c1e04400380e5004409204c0c02c281c04000c0f403a1103510907401400040d000f070741540c90241e9002880203441000781c0c40038005079100c82031540c00c40c01200c60940 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 130002365 1250 130001115 130001117
    0xc0e01091407020d050702060702030601060309120903050c010c1a0903030109111c0b0d0816030e090402010f0e0102030c030c060a1d060a02090a0306021b011b08040206031806070e10 80
    0x281e0324184500a541d00310440440c000c025000c2100001c54a401040d50a0564020256203840d0785a180c020020180048103494000842c00030041c01800394400e80d00b42c07908200548280c91041005460429000c0b808503983c0403000c0003000f4081841c1d843c03a0040140d4406943e5a5150000020554420f00307901079005c681009000c808080360356021600700030240e000301c2c0340240c00000624032262240c010704407440001c1e00e01281000c0e0242510050b110f034684081041428003445030003402120000e0100d4205940110b80ca80940200c00658005204507490444040d400500b1078200c1d0003640101da11800c18003074124110301441140d943c00010500c605198100700954a05003d4409a010f6900290508803501c80700d00c8000916005401903555a440d00214450040c07203510030145c95103032081c59002d000160f421011070b55165699074500c0c0e03c89808101a5900150901c1240b45000105441651050000b544034145513114072100003d410300f40041d945000130504 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 130003615 1250 130002365 130002401
    0xe010c020d06020304121211040e150603040c0e010f0605030a0518030d09060507141803010906060e04050c01081e0910090f0512041d06040f0e0106180204260a0c0e0109 74
    0x2a02d844200c1a20300309c0d541c0c1c0150340d2b000d4075030b07554103945040230a600d43e802c0300000041206001c103090b03001c011036402c40429801a0b07aa1014030031809041e003d618001031080020a90350725090308050740003480740c1200076a0410303100a07549103500ca050840e04081d1114603000500100d031051960003040790410701d03000071801313890b0201131140c1c00c02ca0102c0c054842c8440c606450941c4040e1403181d000b001080080e443e0207050444001c01c1b0303000c54107032091030f08221141d4490000213018007010901004038121f92038512071481d400405003000c5200e040304200d00b0425601503d01894040e5444029a50b00c07401c100d03062900581d8a0541c85000f084200800b2034190f40e8403881426440203480642c0b90342c070005000e804a43e110344015820508484548001036000c4801c803a54807101103114041c02d10624203030300540c03041c1446403e003220443c0c0c103801a03035100f43e41c0c020040281c40425009645000c690b5443c0e42201319040070b070702c0060000e800c15100341c14000c540d801c006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 130004865 1250 130003615 130003631
    0x1101110909040201120b0901030311060603010b0a051507060204030b010305120903060109050903070c170d020109080f071a0411010f0503040209010302010e01053708070e010c020d060203041212 85
    0x1c2030301c0700d001510082c100a2581500c0308820394a81c04144440300040101910b540c1d030b410014582c104070001070300d01e0300680d4081089441c05105464a400c0c01820004032145032002300840340c21a0210548814010031100f00000c405100410143d482030104100c00d5042d41005481d05071009904110081d040116007599600020746d00d0440780d5548020480b0780d5000081800d50080b06030052414070148004541d03540320701011901d040568040325800c801101080b42a903140c0c010140c07151400700014a40c41c003045e00281704107401190901084140d0074030006209008942c140e451449034540c4500d5580c1c40001265000b009142c81400c40c2085e8000811410041c44000e040c020501000311059000780c0030398160281c2e01e41484501c40450002c0b60400205c07504200428040500304200d06000b20105801004913585082d1071442c80d82c0150b840025800e01a640104440c03030000008560707000a5120701d10415a49009600c501006448080c5514044844030f00304980 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 130006115 1250 130004865 130004869
    0xc0b040b0409050402060d020d0c022119020703020d080405041401181e020a08010302030606060715050705041a090f0307060219020d0b01060503100902040605070f020114030711011109 81
    0xd40c0c0942d0240e000010701501c0da440062468401c0c41088540f0500100c1c8242a5007801da10910300c404150b000c0e80c00310200e54840a00341c001800450f1116481401041c81030703504501c4020420f40c43d4011103044540f2600026400300c0c1d403010840309950006414440c0c1c3c1042e0083d08079000080f0005516541001300040039000052104600c0c0c0744d0b14050b80d00e1001c501002052400c6000342e01f103589800d10075005000c0242400264001d05c9000b02052031428030030700325100b0030340120b819800c80c8002644c404c003074200a0090410404240800310304600b1013019141d42c2c503101042242c2e246d00001c00e212501003a100482d100c3e81041200308209038010654200000790030a4110441e009407000441c40c90390b2110140150080300b00214441d508500114000c0d09102e44d4015110f507039843d603405070712940c0240c80000d0b00920040c8001012518108401481411301903180a403862603803007140c1007143e06000280290b14070090300f480a1298207141c2c1c10220300c0314604110040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 130007365 1250 130006115 130006117
    0x40309030209071709070603050f090307170c0106061e0e150a0c120207170a170906190306150201090203210c0106060305060f0306070e01031a06040b070c0b040b 71
    0x40040d010b02204800916400e105000850090004502d104000e06040303034410303610344080c020500440e1500d0040b505042d012000d0074031400c0040c009518061070ba56a50024150000301e4280000081c070a0f1040031078280a1003001c0c00c0942e90b40c0500300d085198a40314480742c0d081d5030060008640d40c0d00142d4481048030801b41c100c2c500220740d1030103407000481c2d021101c030b02d000d00040b2503007007580e62080e401b00b64041140c21880e201140d04c7d034080324007911454420401480b01c0c4000c0d06420706111740d1000b0b04498000180217030709110f10200030612010700b000c002000203039151018005002400d0f42d40386080c0742840200542071441d408203907a00604103000c550910135030b020101136001e00045030840080b03400240309140c5d4405d0080c02408040e03032010322031910f5803005e44641c240090454800d610329580c1d48145000100190001c00208103000064140258000650384a000080009045102c1d413240e0354643d90810341401d00103600020b5822008100400c50140c4040c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 130008615 1250 130007365 130007369
    0x50f130308131505010602061b09010804020f061204031b0503040b03060d0210030f0f021903050903210402100203030712021c050a150605030c0d09111203180405040309 74
    0x81030101d629211015074150382c0e040d5100c0100300080c6800d400000071140d41129040b94010340807141940ca915441c1042c441180344000190841400140c141c1c3d071084504c1500540042d040d91482018100401c2003980040c1c140c00704811030f0400e020070168400c600024485c3c1d030300b050030705000a950310b20b5281c0c810303807040c010410400310110b00070340da5034078444180030390003800d2082d00e6018101c050007508036204014440d500d0019803492030302c140c2c000c644512801040c40782c05000c001409400509010f04180c0e4035201c18018103226099100396031a178a5a040414a05480c0501c10041c805808110100840d003050041c0151143c114000c1d4902c1c11014602503110820b04c542a0400450008900540c03230804040c02824000c0d41d01840300b40000490444803261202c10a449500c415908a0f00b041c3d01002154041c8883c2d03030055451038840d89030b451000e15100f00040039016181101540c1e9000003e000680f00b02c407100c1510380180540e414400340c036040d14003401088140c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 130009865 1250 130008615 130008617
    0x13213260c030a14120a020d080112020a0b03040303093207060e090c191d030a11040b0402040306060905060307090c4d0f0a0215070c170c04050f1303 66
    0x11400104940d00905c0400740c0f81080b114a16194080700000035031799200a019500818982c0001240306106414403580c07154000d0b003110821494080b003c15241d1009005a08141d903842d440c01c000703a010351182400b00003441070680314004800c3c002c8002e01c070300c46400410b58043d440410034142c0000e031410000c101103030728183c0c6541e51001c1100611030324580300380302d29180004443d55a040102c90440c202c40c8992161a0000c640500d6914001d20030050f06801481418071620300d0250003030890420042d1025007050741e01da440340305036801a002500c0c550344900c100300242c10100080c000520940c80280b00107003821802030b0981c18400e03405001580113202d480d02004181286182042040405000c01e020b400c51141c0c284130603585038000b90082220440140d400000c000062a800500305a03045040d0742ca2402e0070f50003448211504403080c0380004400f4514902d100d003a500e01c00c003500c0450040d004210449100401c031034440310b03044060000d04100756100c1100c80d545 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 130011115 1250 130009865 130009883
    0xe0907090c020f060718080a050c040b010c0f0602030f0606031003080304030c050607021614130b010e0a030b09010b010c03051b0118060218013213260c030a 69
    0x46020203d08044844000b04998480ca40038042156071041099040007504640d0b107260648810310940c8480040e007025056070310003040d00010f45032540c0300c00c0d40510141404c101d44100e65a502000504240b41520410350100403c4010300d03600070341c41d52080007121840c0c55031804940e214510040d80c00050249900400000c0400d030051060098980d0410b04440c100c0c50400030003580d66048013140705090000c201300060b0105280c0d8072502d2448000c1103250360903000c5a0301e000410314800e06078104101403115145036241c000314070000d0740c0034a0003201c1ca8030302040c00302c2c03e40300d0048900d81000b60003501c420203e684201a14800300da14682d04a089071080e81d42405071071602e41e89031801d080d08002508012031640102252070110004410092519005640c440098404558880c595098100e8100401e0a0303191203c144018050704085090100c1e009038a2550000741c0491046914002c032168a4444041212420750080c0303010360300c1c0d0020940741c2c065500010100d00b4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 130012365 1250 130011115 130011131
    0x60605070f230303041b080d1101060e07050a02010608070501090308030402130e030909060d03020316260904140403090513020f03090a020a0608010b0319020714010f060e090709 78
    0x1c0000d82c0ba0700c120400c50119446140c0d01c0000d46a07030040d02d04035140c8001c02410700440149400480445845c007000e41014681d0341c4040d80c0030904425040c02c1556070f280080f681e0000a04000d0007080299100c030340360012541e010b402c541c3c440c0c110041a42c08000d0401c22a80d2103101e68040d40c0d03000b12410344a07140c5101007608041181e84102080e0f04042209072400c0000010304081003007102c0f2030000c0d0703c1d05001e001021035a14000340058000f081f0b15410440c4059001c008a44646e1040c01455590724030105031080c103a40d01424110001881c010610f03040c004d080900c43c0c01c80c550310b2107050565024005a0703052003294012030f550036409900720143d074152070741c1c009550301180e500d1410729101e40e2159841c5034224403910045000ac10b400d84540003044c140c0702d00b100c0700c03440c6854001046004030070b9102d0508003a90200303c1400007520320b10551100381c0450740007259003180040404140c1d15a0303080202d10b041080100301ea240800503a20702200d221a1000440c14 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 130013615 1250 130012365 130012373
    0x41202040e01091203060e040c170f0d02070e010918140c04141602060705030c0331060b060f07020607020a050904080a03180302030919090e160801060605070f 70
    0x3a00114011480d46040c4041c401d2010b4003504e8240041590f4081081130703103070703041d59201c05005da801402a40d08a00103100075041c03082c0c155182100e1b00116516000d001c4d1a00b4903144003c0614070058208000030030800203031034106400340140c6401408444c1d54503502c503403c400004000f4207201d44154008001d081e0503c008025004040c0052001980d1802e100c2075802003626502c00c00d00340071001c0071280303101140c203d000d0b800540e6580c2c5107403503048910b2580d40000d0082c0301110107400b1000f00c1445000e841c41040540184010b0001040b410400c048401501e50706028090422555030031011540c229004154112035840c3c5926050001c80d50198403070b000390303402c003c0b100c0c10f0006000156024100c440b40654052105c00c030480600d6080208034ac0d4000e01503401800004403d1820a10b09140050140304041c0060358901e0030409132140d24051602c250031001200102c000422188000340c40a07000a1104070701d014002009440b4181d4041e002e6180041d4000801c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 130014865 1250 130013615 130013621
    0x140108160c1101031e020301050a0611031e0d050f0a0e0105100e0c0408010203071d180105040f0e0d120501080303070f14091305190b10050c0c09070305010509130804120204 76
    0x40f0780b841c1205c400181c0d21440f104000e52081c0aa2442003c0c0e41c03200052003441603000c144040302c070b4000f450070224103803245080c0808002000e01404004c0c402e2149202c034a1250300d00c29130502003121014100750710300e8811101100e603c100d840e410710040140c0039441c24a81c404803420b1a41d90078007950344010a9045020700c1d045030006500000902540550291220040034000d0032030103154640b4008100001401001360420013010000400080c80c141d400000718441074000840c5002c0d202c08041d04003201c00030035602148980303402003a2688284201405085207400940c40c5080c82d800140052116221000c20059000b4485801407021400ea4410450103049809011110843ca40280c4000c990142c0201c6180203000c0340303420b80d8007403402880e40181500c0c001c0707206110100c50b01e40c40248011024860300340501d2554560321807451142d803050354001420350500080044045000e0f002c2d1200714000a00d48002c200c1e01401c603000c4900750040c41d0003507171031403004c5809 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 130016115 1250 130014865 130014881
    0xa02090712021b0a0b07080124020313271a0607050708030703030c120203060a03021014030906060906120303010e100e150f03010905070905040305040503030301140108160c110103 79
    0x30091500243ca18502c50000c0c100b4100c0780b280e24010060790b15602d00312245182413040c0603038407001c0300c19003a002e8200318443c200b4005a2050307900c0c14a43d444a030015520340d03402081507240240503494241d81d211544005204411410700c4910384908103281c501d072110318500e20682001038103000700141041000c00a292407400d0700d44403421824050002c10041e90b041010031003000014169001c1442141d200b0100140340c2d500240c1180c00b0f110108400d0751100003030003031500404040c0400350020b14898040341000f000a840c040007408940c00c0091300f55405a1129101c98210840110a0701c0c1034411a01c800d00c0070342d5400c180301756005002e0380700360700e034182700c1e001e200d2030010a01d040d070900342003035515080d083d0030102894200c070760000b0007401310f0300100e20502401000e03800480d0040e010b40742190401c4e441d20002419035000317a001c03e4482e59070b40b00320412540c01074001640140071030310401c20071811110190902e1110f0b05c1c0140a0182c000c0301ea070850f0301035801b40032 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 130017365 1250 130016115 130016137
    0x1090b0a081f060501030c0f0807230409060605090d06181505041a190f020c070e040506010509040c030308180105010807170109051f060e040c05120a0209071202 71
    0x340100c0e8403480c0d400c0349406070b2444075840c0c0c02c0070808105135002c0d005621100780c49039903900202d14040780440e41c4a80180501080103c8442c000c0810760303055903410719078112004440d40c0c4a182c428440203e80e52039002c00c0900c0310078040780e030203641d45951800c58507400c17083c003040d02407000b0014032850310540d00042105081c40c00b030030114910b651005129610800c9540c00711010700107154826907044407941d0000b4507a110a815600003504010b2295480d44030250420710728016890030104160429660811198108018000100103250040c581541c12000d1428035494401e5814000d01018007070000314004103c40c0c0d1403d03418098040043c1000f001707256129050141c42d40b0191041c22146541020a0391a03510180b1600422076882001003014104a0351030100800400c041444150360316480010340264880c0018811480340365802d04517400d00c800c008541c0403030b80c400b00e810350143c03094100503221401660f40100745410140e48030f0000c024250041c0c07140b60200b031 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 130018615 1250 130017365 130017373
    0x1d13060605040c1106060901032307170a1205040b1b0c09010e07020c19261b150c0a021309211e1b0201050c03121501030207030801090b0a08 62
    0x3501a80131081810018452040e600251220020084031240a0101070301c0c24841d02c45030804101002c41c021080340c81c0400780c5504999581e80c14200ba075a560b0140e0894015424810801c10a003001e5040e01e652424810b08042c20101001000c0c0581d0400c0f0382c08446408450004c1c40d000c2141518001d00142141c1ca5580c6804010079080c80036503a0801510803a1840c031040c1c03500310000c046c400e413928140c020280c40c1500985080300d500304030707902d800700145111801c4502441100b00c501c0c0200c16080e0041510b505020841e6908010110000340500c00c0d60322082d0003040104c06d2036011140c014900d008007000b00700a040f140c6000300410910105000c03503a51480c220484403c05032240c8142c800030041c3d1000d80c01d08014008005000381d0f180c2c0c09000c9044118a18070783c018500241488600c2404c149142d2210301d2030358041d0314213020855401d11703040070038a40ba0400c0c601541015201d41d40941000c0060060000301c0340c030b800c1e099810340c4404400a0040007150119 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 130019865 1250 130018615 130018631
    0x31204091a1c0b06010f0804081b060408040311090f07080601031b09030204061a070305030702010239030f04050f03102909060f0409020a03061b091d1306060504 71
    0x11850954a02c004850040314040040d19540c000c0c0260500f0010f9610741103038954035540c480d08654014803141c490751380a0418500e8180e001c1001c0382c81a0310807903086540c0c5055092a0240500590540d41304000040c00c0040090b101e200d0560001c0300c50400e1001c50f210311005a01802401d1401d103c1131310201c02180c4000ea2086007070044034000d5604010036034440c414105100500101101108030821202d00006d00c80c0000b154001d00b184001424450010b0790400394410b14400c1c2049011540b220345820984249911240c2c690321000f0b51600f03640c020b01c41d4084c025407003101e100715213400500b4400d450600c03450821900828003001240504003046030900140c1c24401800b43c0122061111420700420550040b50001c180e80014020041000042c00d003d0304100c1e0407010380038000001034500d004e4065540e13440e041c03211007410b01d080c0080405c81302d548415010382d110500d4400d6169a03000c4550886d03401d80305e020100f289410a10085d203c5a8803164105150000d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 130021115 1250 130019865 130019899
    0x10c120605030102043516061704051908070c0b0405030c0306160e131b0f0509150304020402070506010e0601171e04080c100207150905060705031801050a020c0606031204091a 77
    0x25000d40c3c000349c0f01c10204030440300095202c50707000c84005001c6e50142c204104490521402d00044600c0350b1030751450030200d48d0705d2800c254141e0f0700142d04c1c42c002040a200518051014004c01d00061b40100003d03d008030401440310802c001010074082551064030741a11905120560400c40303110602440f90203080c00151022180c0503000000c6403400c440d010790307100b0012a00210703001031691440d4044803160351941c2c1d10142003240d110394204280c1c000210240078042c000c0c01c041e1003810480c544040090150b040e100c0d0004070310503841c0e0403c519004034481e503048032491402001400c2e030321854014664882e01082654511a4156801051256070006c0946504c900e01a00d00d0800e0a5005d4050302c1f000c90300200360f40c0280e40040c446501c602c0284d42d2101000d4003034062440c000b80d1681c21a50256100c44c0170039000252380100003010400c082c1c03c9503040d0001c215000c01c20304107000703600850117940b103400e4490b14048010151106120b0403124020a041c0142e441901 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 130022365 1250 130021115 130021153
    0xd060b060714240106080f0a090f0b0a0b010e061c110c0105010311060301080d0f020c1507110a0e011809060c0c0302060c18040b030f010c1206050301020435 69
    0x4402c10745034a8403040b5283c202510f0f00c000d4129812916008640c2c4c884441158000c88010040007003180e4460303240000c0344080c00107802031030042060001078105448124140d560221069041c40680c0c0001340c0280c4038030003201e034141c10300c0b241d10007081600c00c0d10300d001d018012104075002d40081680c400080c010360199040300d100c0ca50505080b445507050040501092050161035001019903007002401070203544425010342c41a1030032a82e802d00010303080c8100b101c0c0750441080108801c0204800007104c0190380e0800c55050f0a13151522101035801c6905002e0700f001301d800344a1015075080c480d0800a1401c1d4032060903c051180c16100428180f40035005800500c40c06010030640c820308000c07582d081401003000c404108410742030101030800d81c41115014410301e40740d141c595038213200d5044807196681d00c402080c9100800a01a03540580120748240d10401c410000c40303600009410001e940000821420052199410007c2d94000c00c8540c40340035080041c0320241c2070305 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 130023615 1250 130022365 130022383
    0xa03060603140c04110a0c020d08030106030c0e0301020c0a03140c0307030309020306060f090106050c030c01050c07050d080c0904050411040e060613090b070c0c080d0216140d060b060714 82
    0x6088514081d0400c0804c4182c40310000d4003c800c440802413074142510501200008900280c50b40c2d020403030f596280c0519900907481280025907481c0c405003580c0d80b040d40f0291030312046000394141918068090748a40c0892002010b110b11031049601c85040d0300301b91400214840d01b070700d07242c00c160300740a009099072150481c031034080c00000804030b2820200300b810a0314090140040c0361f0a0a100366107640c4800500010f070b1106000b5001440c1c0e0900915104c1c200c900c0302c0544800052500510f4005130b045280c1c01d010b6020200060707801c80806580c0700070341c221804640c540722800c01802403503551010b25005402c04a240c0f01480c00060715602030329043d2a40104142105601412200c089078001c000e41010b001003849507200300b26800c0450b004000c6062a140d450f0b04492402d41c3d0901e0501c096007041c104080c225000c500010300601e034212140c8a0b461131000010200d4900300c5008040c2070b0740b0000c4031000e0720350000340c405681c0d2180341000d90f1900d601d042a6900044 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 130024865 1250 130023615 130023653
    0x20103060b120403200604060b0312181311130303200c04020702181f14010807030903030f0908030906060d0209130302011506051810020c01050304020a03060603 71
    0x31200003036554001046840320201d20502e910381d515641d50891361100840721440320f1100c003500c000d89030641404028001c5201d040002201e040c03d400b8141005028a0215a8204280900780504440b2104019244001c55040303517904c4204640c00c0080c050070041180e004808a850740300c1001c00403100e41030724000d4580b00d2084000f072aa210a254000d15910036a40144c1c060599030700f00f54000d000103c0c4000c0806941790000c503c0c829681100322190700c4061040e04202c400000f03842a404003401d81d404612200c81c9500001900044024211004142d6140500403d143c4a507008072a811901c04040c0b10800181c201505640c01c182c500407010301032800443c42900d40440f00c140390540c040e02d1a422507507840c90078200c404407244180c06554a4a4130482d00044040316840500803507180c40b500c0321640c02c1280e6a01008010781401110b00603a8840c17a1500003812241400d03091030281c0d0385c0d0780e8520102d074508085503c010056803d101c008020000c1c1c0040c104001021 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 130026115 1250 130024865 130024871
    0xc2a17030705031f08100f090501020a090311010e0109050d050709020a0f030b04050106020a0b040c030b0c19170c0a02070b04060527011d0d02090703050702160305062701090f020103 80
    0x100300c894031640d05180c414040d0990241c4c10654113461b45030404200d020030102d00041e1078149494907800c0e0384c07200c03d0307450011b04010014020000d05008405102e40c080c600203001c0f44030704001808045aa003e140d10070b0000d4400d0608004007040b0741800b0b8a050003065449481841001d008200c0030300880002c6070a0881c004071030b0429110701c50403180b2a07801440200d000d51035500890001a1041d22100e00a04020000c211001e44c1e06e4041e081c05440b461341c03440000001d83c0c0d58901060003400b0031400501c000e180b00c815219050304096920852a990f6094860582c5058030a6002c1c0c0070340080442e0018090303801c84080e00040904d110000451018034007100703221900509420301040180c941c03002d16580c60007030840b185801030044050481c664000500030601120103800180e21034041056185c0d05001640c0500144840310b142542180d45858481c81e00400c0014111020310b0340c13807404415030031100b03061401000200a00071032801c18580c52075001c8020307404030341 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 130027365 1250 130026115 130026151
    0x609060f060c0b07030207080415050304060506030102181c0c080307020a0611060a020a09091401080c031912020109080a0815010801031101031a060d0f0c2a1703070503 74
    0x2000d01c40032507102d5403000740521255144401a0000c3d00841d40596840800b80008034401d0182142000c0c110382d581c03035168481ca01440e14070242c401c000c0c295030003a401403084001104242d42070324140c080c2101c0b12240d0054000c0184101c1d4000d0f600a0901520800e00048042c8044000c1c40078034020769124071016246d041c1075030358215416071b00210317074800d0300050400794403540a441201c01c9440c0100301c0030b94036038000083d29040c008040d00c00b20204010040060104003150f51814241c010740050340080032600800c8030760384c00184c4500396840289900610079800480c100b44e2281c0c4d80d5842c0c00705410001c0610400b1103081d0380680408070340300e103d0360080c1c004c1c03070403030391700980c1b68004891450045002d003840914800c030f080507a84c45280d0301c0d91080042c042011007100b0010300d8122a04414066901800d0f441d414000715200c0c00f0f00c0001186031001d841108400304d106e44005d41d2404070510540c80201d652903003808424802101e42c84001140648084181801040 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 130028615 1250 130027365 130027367
    0xf010201020306030d0c0303060b031602070f060903060506060c030c060a0e0a120c0c0504060623090d020d030912030503040302060718180e0f0d08010b040b0d0b060d0609060f06 78
    0x11000b5900c459043d442000b45c861400d1241000b004403078070130701d0081451941c40c2c036405050703013003170f02c00d459281305080108070704503810414807005040304150009004c2c6028000b80c44c0d4200c4e40000340500b41c03070700001199a11450308a0748003074981c0c800c030b0395034203074200e45c007510340d002a14a05082400c1a1185d005024000b4110700903e400040503180f05e110310205076000c03110f42a0807151000c64907400603c1d9a01c5110380001840651a8400481c11180006a0640c280303103c1407588201441056000c0d01c403da042800d099068444061860242c00d040e00d101120340c4c071100c0c520989000307030010154014050750180307109800301d800f075480f1540141d400c0c042d01184501000d034013403801c101d85d401030110b122400c0b00840340095490f00c4541194188041102101065804201c4041010347d10541c042d00402d40d00c1c1200d4180b038209245801540b02d040c14044090361190000c0d05135940c1d9104503621241100d50070401c0744e6503210000e001e41400d1103960708801c204040000c1e06 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 130029865 1250 130028615 130028617
    0xf0801061e0515090409020d140d03050c091c0602030c091c03140d1d0d0908070303020d0c02010905040f09170906190903050717060a06080d12020d0c05090f01020102 73
    0x501d41c01044021588040743c1141c007075800003001c0a50150f1980358800250304c0b031901002c0c150303010300813040e07660040c00c0205141044520702c4c201054508001c00c68181040010341d0740e40c40007141c2c01c0e02500c21103901e003400c8010a07000074107601e10000c107203c10b10b5400401400b0b440d905407031610606031070701440b00350408040300142c00f0501c80700303240100c4140e1a0042c001c2c001d04910001702100141100a034070081c1c01b2540700c1c01d50158031450002d40e04601890000c254200041a8407400c1d0b0350020348401c41a081d1006112900300741c402168050100040548400351041007100b40b11821000a408824001d5420004581051000d541d5400480e552010007801c405c0c076106174104011040310203518040104200c00c01c0210010700c050041c00020036488441212080c2103259881c03c000002d003049030440e10b031200c200b100c0c00012555003208105418105016001038520780b0292103540409050985000703030000804e0741100c040c05501e1010341e00e43c42c1c2c0b1441c201c016401c0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 130031115 1250 130029865 130029869
    0x9060308090d0203010e030d0506040b09090307120207050d1208060312040b03090309060f03040615060c1101030f062d0305030301150309020a030b01080d08040b0a09030201060f0801061e 82
    0x6019042003801114100300100ba100c8038030103400010303890300036440f45081d030300190001e0703081e00c7c0c84106002c402c6c5014012010380d11000c50f076100e51814260f5003141e0fa0f100d5008014103c0074000c550721034440c000d112080c02020050f044141022980c50020302a241c50800386002c10b9111005c6651414001507203070362805800d00403032900c0c0c10002e15000782d8000034200b012900c410421102d07182c0300c03200030b0485a03500000d070715200d0910b460884c003a140c16103032136524200000310421155600c1901e900322076400c40550440e5100d9040100c002d0a4a004400040c60038620000f880b25905420f124106c0c500d0001c1c0b9610025540c1e50810750740c0c0e10b01c40506554005d10040c0030010302d400b51030381350003d60300780011800380c2940410110b00e150b0348196003401805004005001c014030807103207221040d2a01c40c4991400740d0325074900c001c0c042c161070301141d41c0c0c1441c1020503000b548040040d140340301c000107205d65070b110703058040c10543c054011405003c45a41861107001400f03841 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 130032365 1250 130031115 130031123
    0x9070f060c0c0b070605040b011a0d05040302150c1b01051303050a09030b0109090309080102090d031103040b1902010b0a03030e0409020f060a020105070318030806060c0a051203010807090603 84
    0x88145044422102604182401c1e500158034080010700d000c0d0350401803100714030900c07001c1100c0ca4642019101c0d84816808031510980d507440782528901c641003115840d26003500c0000e02030b259810200d16007202c103c0310070444c20b502d905200d040010080a00640d2511344101401004c8101d030841c01d030f850568070b2000080048044000080c0548041c0451102c1352801c0008107a407503c036240d090b00203a0120081c65070320b18800041c96808060500900b020328000e626216881d00412641420b06401908000580c60755015400c814011070f401000c04403541c0303880f442c1d2843c6241c9800556600c607405586002d01d40c1e1818101915000101ca030103850b051480c0c041d1006000240c50341580881e8840c416541c004c0c13a958403400642241e02c0c00d40e0000a081c600380801400301c80c000010414003100d140c0354040000d80c030100e1950f1249068840949421503a05568541400071200500c1030043d6089036881d03120000c040c1d0704a64000080350031160b600d2510780308480960001030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 130033615 1250 130032365 130032389
    0x6051005090d0503121603140c03181014180c010c240c120b3a02090103052404200f040e030703030f0506010206040f0311120d050907 59
    0x741d14940056094066030080040d42c1c40d186400700c00586481044502c00703141e840e1080030340d81196140c89140124110386441c002242004a0700d40c07624040100405281c8003400801c0195410a1110300a0309a1070034040c007107480d1745c1c074240740003000454624101a09025190414601c00156036034440d80c1a181c00c0c3c1a09007079101d9550780009210321000384000c014844407003000e9882009001e112980d078005000343d40c03100520554810904040c0b0900c04044058010001e4500e00c414403041121a0b429030020f00d1403603c81d83c1d01c2180081d5001c002c400c0000240400407407008403810803a0784040200409505125808a00b65405005900c2400f10070301c1442e4501c0b0120042000104884a00c1240500103003c0c4d031484d244c0d400d0640c2010403100101a0503000b1401c410120410922036481d100c3e0000f580c03401c00404c00340a640800001405050084a036020340100401c140c035501c01c900c40c0d07a0622940203410400c0101c1c074002c00111414400304049081d501c02801e51 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 130034865 1250 130033615 130033627
    0x3060c0c01052a03071404062601030c0b0a121103041202030c0c09090a0f12120207170304020612010602060103032706051e0d0b010f080702070306020d060e070206040606051005 78
    0x420000c1d00001e1008007131200406d038065070034406002410040a03241d45406540c0c0d02d840d0004800200c0410381190400c03000010b000103121030b41040c05540030803040c0741d11041e038000308072900d50b02c40404191407850000800641c002d200004c5104030301a04183d494882c051408a03074900c580040c00500e9005919024002d1800c00410b079004002c400448e6011007068441e00c2c0040d400d41003c85995501098a22020350001802100046021011030a00d80721791541110a03c0d8240c40390181c55000001404550b501011b503000da1851260402c1d6540e19460701a60392102800b043d0042103240091000c2c02c00e004e40410500c200b60400103800514192055800e5045410086603903c1e041e50b81c1ca02c1440301c0000f401c41e4101140003c19074285050016240a183c041801d0800c03540d042003210803a000140182166400507005a40e038181d80200c1c4c008200b1070b000300ca04201050188031405900180007130103580156002c0084581c1c0308100300a0039070740d08100340841c0c000c1c400 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 130035971 1106 130034865 130034941
    0x216140a0308010b0f0301090f02070f110a090e0d080604110a031e0e03041701090f050a0303240509090102040e07200c0d02040c090503060c0c0105 65
    0x8954a0081003c1c0031744082d1005016043e40030381c89440700045000c00358121442160003001c0203050001c580b90500e03030302d007115110324803031245000e02061400c40d07403041c00d00c40c4104a0080c914051618001d40d0450070040840d50322a42c1d54140000107104103006100c5005250750004007a02d080030990702c0c0203100d80d220003410b8504114040c400b04004101d60503981101d40141c0c1843d1100811805001c4076074000b0050708869146008001000503201c1c00e440c804c1d24144492280414400c400c1d00120010f10407551480c0000c01550415146580d0050544000035107001c1e160034031216088401d50b0007100041e40301c0045408402010159a0207060001c0940400006100013a01c5240c568902a105564990003048414060990b47e8020400034095802c43d1030303c0e4000b405550020710454025508241c00038560075800d0b480e41c01d01c281c91004040171900340d008 = true := by decide +kernel

theorem cover : BRFrame.Cov 129856115 130035971 := by
  have h0 := BRFrame.cov_init 129856115
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 129856115 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 129856115 ≤ n) (h2 : n < 130035971) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
