-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3026
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:26:51.122972+00:00
-- url     : https://prove2.me/submissions/cf29c8d3-a4be-4c55-a2fc-417e5d3faa76

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 544064748 ≤ n < 544244604 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 544065998 1250 544064748 544064771
    0x406080115051201060806061207120e011b0c06141024080a0e0a02030709020c0601080a020904080703030b13020702010807030c05160203032208120408060430090504110705030a03 79
    0xc084403030b07000188202109d285080c0a018045202d8142c05442251400f844070404000501c142c1106000b2500c0c40f07054000d604c40211200710b8040e500701c54658441007102c40c10802071580320301507d40d40f45048107a50402c07001088001c000001c013158601c54460801847c0e411510041c1c001d1211000030a01c8503020360400d10300058084c00030b40521460303c0024460001d503018050001400064503810790b070f2540ca45558a844a401039030104d494000705000a410707000600302588681000329100c0c47c0c82e00054685543c04031010106500010010115039210601d25802081c5040c03c001e20074410300024050b00440c0701c441c0b010103400c2c2402d01559410410384107000e0060941e105150324050011403a01200c0c411110b040c8507400744106140501801d840c1943c4440d03009084995403a25060f410701c0c4408c250401c5011803007402c00000941c41d100c0540c050051712000c0b681d074a0031084c00b04540c440780e14041c801c44244000c0380021030100c211010700c0ca19160100e808450301 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 544067248 1250 544065998 544066009
    0x120a0c08160803010614072310050903040f09022704020c06010b040305010e030a0f0309020a030f0b09070909050705101b050a170a050307080414030406080115051201060806 76
    0x28501c07698801d20816400800c070308100154142c030015502d11401040482403003215002d03008004211034a07040d080c42c6c80c0144801d0b000070045440d41105c2c00001c40209a90884806607400c000c2c50f00000790611400034a04019401080e40036021440c1050700a421040081048103446a0b0310b4204103e10440d80c860b019240320b8844442500c210796540d000e00c01a0358001e00c0120341950a1100c1c1002c0e0050100680c1c0722408035440788400300f03010f010103c00034220a501280d02241c00e14012002c2000001c6158140d4442d80703080740c0c5801c002d10214503110856004030410703030500b40410001080410600202c540a40d07614502d0110130009542c0e0802c80e160761700d1040400210711041c0b2100250b4141d08034042c00030034a80d0a4545180804c0b441000303074941c0800da0402c007044006100b0484a544a405003072810300355400680f426040d03034015402100015240e9006009018042d00100340c0102c103800e090340341c2036030044140303680300b414458801800a400002010794655 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 544068498 1250 544067248 544067257
    0x11401031a040227090d090b0a050d020f0a080709090b06040524131404020313111302130f1401022d010f0e0c010804021c031412010512120a0c08 64
    0x2200040c4403c4c071007209106400341d408071401051031117006021503549004001c643c00f50b0314100742840ca450105902510103a211645811100d5401c00c14020420b02d080c0c00740c1a248926990704166041c820030080c0000070726001380700910300d8202c005c815a80d071a01241c04aa078182c800c094550700520f41d100003044100c001d07988030300d40080d055110301c2c94108510240c0d031220380107544803020710007800100c0c041194507114580c03c0f6055540400c121700d00c1c1c4035010000a000f0070076020f10340110b030243e81022200b44000c90100c007041c030035080d503903044501031b00c1800d07021165010780c4c1d00003c0d9666820540481c2c000c1c003040319a40380a4505c40042c144420382c0000707004955008060400910744551028024000c0924078251503104201840c00703a42c0040c0159482c2418030310301403900d1440d03c1c0c1141401813280511003e882204040c00503079915020400040d85031400f030104590484901415503040341e96000c80d001c8420701562000d48040c64141d250030300c98036115205105 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 544069748 1250 544068498 544068529
    0x807030b0d0f0f150b01020a230a2328031e05030406060806041709061606050f010b0f030103030806060403080c06090f0a051011130e0603011401031a0402 68
    0x2030070001c02e0248000500d5003190f49105203808803044a02c100d60b1001c0b00c41c020040b83c0140c12144613031002c01c0140ca01c0c2d4040003e00c460140d5002d0a0700602481c0042c0f07030b00c0444a80c0403070001d00c5d100e0601483c2105a0a0400020742080d803042090044180318000c0d1951130fa00c81031100d5020701d481480304425221094000a00411051402410541086a0131203049040c000c0c0403c1445000c10140c0c003032940440340818041d0381c059a17008a410400e01141c00c40d50600410328540c42c40603d03060302d140191400030741c1b400d18190b242110b0005820103640000204421030340002c0c0b901c100c0f41103c4e05071030700d0007081d102d9000207480f901c0b4903803025000e0680444c15640c45040441c48078041c1c8003c00032540b00d003041c15490380d110051640094400c1e041103a0f42d170302e48813082c0c01103048120041d403403916191100e5060a8074040c1c82e00100300312a240e0b0104140c0781400d210b006002c103500b01c42e8115561450f035641c0c00f004950250141030700403040100e011502c0345d94014074403aa = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 544070998 1250 544069748 544069763
    0x30b0123060c010f0c0e0f1e1504050312090d08070302011409100c020d021002090a050312070507060e0604050f0103090501050711100e0c0922030e1806010807030b0d 73
    0x2414002c14078042c102012401c1680b518050031350760345a014880d400c954a4001e0000001e20401008001c5d038001e00704085c0c4140f1140c0c0c800d10035182d54074121501000035141203540c0f10b904140616182c022490300d005a500c00420080d0900e6850000045190390b003e01c2a560700c84092404078003404000f0928849180e100c01403140412010800541c00400c1400810a5840e001000c13aa1500080d00c7d02c1c0141c1c1051280c10001c08040c4c004080207a07010302103801c0307a507561002c03c2c03400b1150600203140d048041620380400c00d0a01c4204001c0416180100b201c005120010b1260320640c8100c91094044d415031000e964069040f084107036422500802c045d1400e104083c10170f401110320f90807240076414800100c10050b210b5812003250100003002104031000038056007203809003400500380100f0103182c00444400d1004c0307c82e540b180d9150711103500d0400520a0b0341d4414111189100c074604100500799070b100030301c00d50041c56843c020690b1200c00f000300d01c4032192200050000f5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 544072248 1250 544070998 544071007
    0x40323060106031b021b042c06010f0b09010210050712090b1501080f18030d0f2a0c11060c0106030809150a0801062d08071107030b012306 61
    0x3607415a00c44d0700720100990340f21340d0441c240c0c03070202e0b115200d041d003140c2c4190b003075100c0c4411414164030040c01e848c0a14220304001c1501444030403201d0401030034030700e644c0c40720005012305001030201800510b46110003030308003145400040c0d11a0000742d12480b1040c0e0351000100c00e184503400000700641c040c5000c201404283c03d1120720036501b190310a8816000b0140ca404c503500c01c0c3c000a10403035090205503000d03142c028480d074911007111903102142c40240040c041360301c8240725240c120100a0f0002a4010080201e14075412024881c001c4140481d6100d100880d0088051601c107540610480d689201003000103020f40215513030f100c050762034901d004c400c00140f174005001d41d900440361541407001d000d818098a11070300e621900000c0b442e0340100b1a01d4094a4009031480a034402200038200014188031516000801000010303110401d01131600d0b004a15401031115502c090308215045441c3e00300002d406100303054103006440d040380403104100100b400994402000547d55 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 544073498 1250 544072248 544072259
    0x2120403020a020a0f0e150604050303191d10031e060609050a050405010f06050309150906040b0f092d03070506011409010f060309060905160608010e010602030403230601 75
    0x42c0c1070380c440100d0050f2407002022075140c0c00340c1180c104680b940503000e03816645425101074805680c2d0904d5820003018480860b03903a60500240c040e81803082242c00300b010b00018000c02035103012050510b89107481e100403040b911001c0c41040a01c01038100862980111008504040c46807080240564500358000c034103d54400c60712000c0314821184224065140e00400c801c44400303124000c105078084100300111400345000c0c42c0d000c0041e01c1074030340e03954a10320b0300d0301008022107030403809401590400040089111081d13070011610801c100c031903d824030260365500244a03000d03076101c01c8840d22000045c0c0c4e40c101044150000ca080e261580d0281ca80265240428002c0103c0d1880110580e41c0c281001e400041c120303001005200101c502c0c000040c1d00070304c01640291155600d4030b000e0b81c0425002c20031202d410005500a6a10300d1500341d000300002d1060700840350151564004120a550020035102076a4100484c2c0c1d610a01c41e4004103518100070801138800e001d080000500d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 544074748 1250 544073498 544073503
    0x513030b091e010204120b040c05210d020f0304050424032102150a1109041109010e01020a020a0302061b060c0403030909020a121805031611011b030c060212040302 72
    0x618400e0904070044481c1000c520f09030b01170350085542c904180e2210901084201180a4101e4000c0401c03044864039035000c104111030303a18400510308011a40e072a10000d040100744c4070101c29202403c003501071990b08a44034416803240078400c5807581401c200441d4240079800d07a4078000100540e60681d01d26000000080402c061429640c601510340d00542c000316100421030011944041d055807540e850500900d40c1c00105003441c44240320100443c1c8039841380e5007019141e0340d090354444950000050004084c0440c041c11034000e11035620040c1c460b00c40038002c0d281d0403111151949205200400301610034051804140305400c140100c240041c001030003528000c1d520402c41548400d607503402d82c80f840410000203681640b643c0c41032845507103c1c40c240c04901d003003030081140a441e1140b0310f030084070060082c040c01c100d0740ba00b04001f100318039800010a00700000c0d08a209851034050080040e0040c080c480d04603240c5080100950442d2240800d07030140020b9030400b400c00070f5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 544075998 1250 544074748 544074763
    0xc0312180b190f0b09060909071e1511061003020604030f0203010227030c0612060415090f0213210f0201090306060e061509150906160312140f06010513030b09 70
    0x10302805c0c0c0320740414010b013000310300648a4030b003420040030034a250440c003d50000d10481c80d80200c90120001080d9054005229104902c17540c0da048001006070a080f402c015018003c0c2200d2141c0000400c0181ca8200640c1c04a90b00605105000303201760020070302a00c154150740480d00c08c42d900d04891121880c40d11030044009404807100d00c100383c0d0034002207100d00b100b201c80201c0c4c3c42e07000590500d420b8002c0c00a082d1344c9042d40040b1950f99803c40280c407000c005900f00a40c0209601c0e6070011010940e800030702c02d80d40c03405500241c44020582c1030260720000350440940d6a0102c0c10340e4003c0c4a1840290f6120760200460380d81d88607440802e50041c0c6184d440307960041411285c0c2c800c21020b441040100800ea19060b6a5020824010ba400a480640c0040007800078a800c55169000030303004500075240c20400c0200d84004400b00e40750f400d0800794810100d800d00c4050524403a446620410a0802c25a11144480d48181001d007550000b041c3d40110020041c00c02004903444 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 544077248 1250 544075998 544076021
    0x90a0501050a0b1f1806020c04050907120b0406230108010b03062806030803070306031e050307060504060f0617010b0109030f0204051e01060c0312180b190f 69
    0x200000c0c0c03110603060058450444000b9444405400c80c3ca20340e40c010381020301450030724100040110f1700c45000c44d149180390381c003160160308079180219440c02c01c0d00481d580500310b20060500b003400d1000c281020b00800390302400052a4100207820401c0d241c6c403815020390b0201c801049090032840c1d0000449090081c1d10f829404d006c0c604005040c0098080d0007420500c5c01f181e82c1d100e00c40003008032a18581e0007811041d48850380000032801c040011401005280d402064071425800e1404800c0605018980030301a192090030100c4c40c0030043c1e600d00c40d07001c071011400d40c4650420340c0183c00c40a00c02641145005400103c0c07a91200981402c500035100a125081550006403014242c074403020b8802c05e82030303050b036005150580c001c2c3d601c500b40c103016000b40c84a0782005050f1810036003061003c201581c03844424990401e00201d89098000030901455038080d912251800032940018250b00600b4007044803290100d04050840f1007a100c2045903414100910000d8031045600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 544078498 1250 544077248 544077251
    0xf0c0c030b10230906130e010504031806050d0f110a030b0a050f011403040827090a020c0a0201030c0e0d08040f08061b0a030b130c0206010602030c10150b03090a0501 73
    0x199028014031260700c1400950b0312060300c00400c1084c090350420080805038490b901d541102c01d0101940700715080a164800000360516003072601a040a805089010840c410080100242644281180c0740300003030701c0d0b0204046206510321000b40c208030100c2d0482c0c030008501100701c03545c5680300401003a81111040020765907241400860040d09c180240082e41d60283c80c8136504610004580142c80760358118030b00700d9200a040c00391811702a242e041010240c280d00c80614180005a410140d00d0000b107150030350320b0ba03c8603560000400c0c020305154682041c402c80c180540c1181410940142140760180801c1c645064030394024091195485008080810781400001c5c1140c0310f900c0c44a0141540c40d200c03401e81c50720340c00603c0e0303201c20180c403401015a251a401d091784980b903500c98001c280040b60300806410010140c100c402190310a20042030411f00005c0d240c5842035088000040a8503804040350f0720915503005a941c0078030000901403d034000017072401c82580150f00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 544079748 1250 544078498 544078531
    0x171905150a0209060f0304080403140f061e01060c1a0a1d01021e0708092218020112110d05160801060806150d020c0105070801051005030112030f0c0c030b 68
    0x1c03000100d00a001030160000414040884052407050003550028080e01a40c0d05055490380c0d444085d443ca02d40b80200e980111a044110700300402c100d5801001c040c030928001245107101118024052180c5010000c24203000c0051043e2010300c4450503250215280807482c000403100c0141c5112401780802c0e02840d58032060204040c401c1d5280b6032070700e07400011800b9200c50606600c1e00071843c02e0f241c1035010001403100da603075214107003151100d464000007400c00101520084804030411071850044404207940141c1c1d1000c80752060710025140061092654017201c201c901608958581c182e1405c0c051101601003c0c039070400c0480c0380e6941106503030703d403d0700b1130708024152a110340141b00b840016402044040180c680110548401410f100b00103000d2825030b0425104203010800c0b61005210a08010462490760400c50500500e1540343c0340d5120040e820b0400080c0c03c00c140e694500210a00c960300c104041c1d608550044000d545034101114010020b95549418805804 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 544080998 1250 544079748 544079761
    0x20f062a0f0f1504052a090a02031006050f0702032b0203040b191106070305090622080c0703020a090203100e070c021009090e060406060605030f0117190515 69
    0x38a020412030711070090507a103891070f07900e2500c07050064030840d000d000e1180460042d0803104036051002c142e1b400f806001d40024018480b5041001c0e0180c1100c500400402012030101c840c240e01719030451910070b948011100a6050500070380800070350502400304042603e107024031000c440165807041011601050480591b5280b00e40c0c4104041e00e0818800c0101d140001e420800000c0f4541c24440085195542c00030b040040440340c1134007081d03856090000111080120341d0340011128068003c1d50b0441c1e60350030122014080050041d00005040019a20b041c0100030095501078248140e0988cd070342c202029403c101d074241402c03090683d001030b41c40034003501c01e40540d00d40c3e02d8010b5048400d40911003410803d00101c0107004480f0400074210206110b040c0c10001d500003d08544d04040c90f200c010744847d940020100601070051010f0b403114202101e04444011041681c2d06001800c65810030800c01ca02c2188880000e112800b40036000c0b80291522122042c081002d0b6282c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 544082248 1250 544080998 544081003
    0xf010c022b11090f07050309010f0c2c1804020f0a0305030a020115060813170a020106050103060b030c120702070b070b16020f0618010603020406080c0a0e0c0304020f062a0f 76
    0x454481c1020039041c00841d078170b00d0040004681000141002045924101200c40d003580c0141451310f00055a150030800d07201f2a000800301052000d5001042d02c0c01c40c07100003005401d0306030840c488640000081011581e680c0d0803580540307009001280050750380d06255807290042900c01e405075080400032040c59100110000642d442500c42d10700c15207400c0e25030a02c2d07101e00c9800316440741c803030725043d0404e518400141601c50043e50012035490700f03060004095920038ae01260308280180300380541c0c90422426036500d541d0808070044a036507924802c80c904909640941030358940092608203114503142c5451107090000001518604841c4049a4510f40b000b01c0400c1d640000001c6024031070700d05044e80d2113444080c004203295450340c0000e42100c0d00c55010b00a00d81c059002c3e05402d061800c00200108031110743e5424902e0302c21050240c6200040000f4862481400c01580d580c0c0e0300000c2c3c4611003c4581c03290f0300b218282c0da01c2c1403944140c54801c00b09109046100d0700c071030b100 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 544083498 1250 544082248 544082251
    0xc0e090f0a0b06040e011b03060e010b040902090102160f030b090a0f0303020a02150112140d020a02271801060911040e0603150a02091e0f010c022b1109 67
    0x2220300410211216495900c0440b001030945076000d83c54003000a40761009001d002c05101600344000d15081440d50301404403403160344188a0071800f107004002480c1c020050f50119910301074051303070b00d00050004034140140d02d00011009a032180020601e0f280029540307040c0e0384076007814400d0b6103032001c8503961400300500040403603014406100001e0305c681c02034641c0042600454540c6801c0518422030854242c00103e01070f541c1d50703005000d10607112000344000f4590805402151200c160082d10344d0480d1501a014102008090310031011000e22a100c481c1d524114103564144248041101e0b048618102040d6082a5000c28041494802c400d184228032003c149400e2402c0301180e00e80b0380c01456164180030724081011403204c2e2200c841d00c542c00c00240181c2d070315452001c00404413000ba11a681c80c103000040313942d440d01d42c9220280c91000900f02626401517a1000480c0b21000e042d0907007049203010040c424451201501400c003a200748180c00d0204c40c0d02043c000d07000070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 544084748 1250 544083498 544083523
    0x33b1b1009081e030c03270136090c020f0607020613150605031213061b0602031003050313061d06120a02070b01330905120106080a0c0e09 61
    0x20200903a9502c168050b6400500300d0f405081c2c070700300b905400440707066400c0200030040246004400400c1c01004841c0740041c002c003400c200d10a107a60340446042354160710800003000400c01034009094065924003030003019100420700c40d640701c41e80020745030f502e03400095034544914004240181c0c00403645034030552401d41d210000c0021515041240c001c203100d46c680d041e075201c4010a80d030f18180b1111548860680c4046da98209441d03400110100c44c0e845002000840000c9410742c0810300d10000d01240c00000260305c2e030700c4e090075080d1032036000c0d8001440c5200000301892103401c40d0312506d08482564032401c441d4940600310200780090550595440301d4101b056000e030549002e805904101c0c296001420f005d07080da6281140c500a80104140f0800465007215141164110344606c2080d50700d52810003241450180012415004051040c9081c40c110203040700c00358003400c01003141d107040391409000c505100703501800501035200e920701c032200020140080060780003401c64 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 544085998 1250 544084748 544084753
    0x1003140c1005070804030602031317070206071104153533040803041101030b030709050c0913020307180e07050307090b03090706030c033b1b100908 65
    0x104070808450b95800303040f080b240410f040c030020001c5942c501c041c5120f1180b860700b822070750120307051042a05002c1480fa0170740340420085140180c489030151007000754000340011941c080c0314001800f0700204032402410403801c4400242d10201d401c015416001d82100301d448603100c03000303600c0c2c80b40070f8455010310f44d610880000da2000103600300c59071840903031a08a41020b0b413110f000c000110041e07e080c2d442131000b02c01d10062149600c08000304200c00d007420450940014082600e070300b0b86106032104640c2e60000180307503010b08421103a0b8600c0040181031501c01611001000f50400c0d030b900c13000140c011102d0300d000e40b01103103441e00756907506142c881c080ea5560801c4803a60b00050061003004901c0500082e1040c03084085c600500388000944180c5040c07000040840c1d80c8a16078008050030802c00340345a641207000c01d04400550011001c0b00c0c1000c001c1d0202100ea0750254203c01d108000920480b00d0400f1864968000201c0742d030354400964440403100b410702e60040e0042034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 544087248 1250 544085998 544086019
    0x9060503120f160303091a151e030a0b01090506030a0804090b06040b040311040f060f140609091e0601050f03060103050402030c0a09022805040515121003140c 70
    0x1481c500301510305072440c40111440c000705074092091285002c0000ca0109440d41c03260700400080c041c1c10700c80110441b0154000745000b420350203080b0b00140c041401040030000e07c218810030609503418206025084504020f440e1425081000c001d00c581000645420b010490350f20300802c1700d8001d19048001c2ca0304003800c001a0500a00f0030543d400e5220100308000902c40c6081805800158099003542c010282c9120601068500c0040011252841c1c0401480503009507105070043c0c460890b07021000c0c58101020810501c101c1002d00c2e8060081010400b44800031740b04560040c480465140807500c40500544e014043c200300302186103804e1001400d50b502c82e0340403e0b4043d000900312808102200042a6454065009540913540000710304a895040107030740c2c1400d40403012140d100f000740e0f02c0000c00747d02490040e41c0c481c56001081c500704182001c140c03100fa102c041801700c802e0070501001e1303040051610048421600070541d101d115140440c3c049010329001e000c42c1400e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 544088498 1250 544087248 544087273
    0x92d171504030519210c0f0e060a14043602091f0c2103060b0408031911030a0e040f0b030a080d0603080c010c090522050a0b030d0305070909060503 65
    0xd44c0381550420040002908003c854082d0b11544190143c80c8800c00007013004140c50011b04071280074000b542408146058165181c449800f01c9002c40e0382403030315601401c611300c206a128465544200b9041e0100c0c01043c0c0c0203103e000301501061a103c000880c800c2441151206074050b02c1c100310ba00c01d00406500405014084054143d40742501c2c060420040542d58a03032034100113952203060402400d10841d1840c1c1521074900030b0b080f80b41300381d4200341c0350190303440d5240705074861100c190b4016016183c155019181d200300e12100740c804d580d02e41e00407201c0104490141c84141c0c0c451418800303000049015480303002e168900160207000e1400d104d803140344081c0d0000c0b01f141ca0303ca659800000100340c5501c050b101c4d54002c01c0021074540c0038158000c0002c0002c0e00800c0c400c01944c03900e450207801c55042c54101d0a11420007141c1956030140d20001031404c0401142c05018030f0b12180074807941580700b640b00d11081e4481d0f02038143caa114801c22615140a06d035015801815000300 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 544089748 1250 544088498 544088527
    0x7050a06050d050a0e012406020a2a080304090203090601050607050c0108090c040e1c0207060813060b100f08010e07091a13060c050d0f092d1715040305 67
    0xd01807100e00c808a00c140340c141e0000e003140d01000c0207c58075091082429582100f07500c15800034880c520081441302e000b034890104481e072030f030340c032008189440304241400c030311381600400100f42e00c1043d44d8690f40d4400c074600195004850340c100c203025250010810b460a0400d031784440340c0050040c0003110403803005461191002e005103c8a2044d240b001240755140d002e4080604100d4000d80300d050341c03058681652401d40c0c0d48820a64024002c01e0040300d0b408003c41d54000900000f2030841103403070824200030109000c2603500108403600400815411940e0074840032210358074001c0d80d030f90b6144410b14040b819035400c0d0005468500070801000303004008056881c10303d030201d280a05225240c58030f105103070b001802042d103803604403040c040e0501c020007d034202e5041c07500a2000c041c80040c1003100328060801e015208080706184030f4040c018051030b070031224004259081c0c861154042000c0b01c0c40e091441c1c0d1180f1500d4900d80f032000d42e0700500a40e407580b030729401c08030301040070310 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 544090998 1250 544089748 544089751
    0x40c050607061e020a0809010216030c1a3102010806010c240501030314074d030c0105040e271c1e0f11010f050103060204050307050a06050d05 63
    0x890481d1543d90540c400c18141d60a52140302c4030080c010703500d42480c034001d0a88580100b0040349a44180260740300040366003641d40200b50315207444108000c807881d22024500084200004c1d8090480030807448803a901c0b4900d4400c000b544c04001003160a44810f081c003c030081009001910600c0424038235401007a2000c040d5105010112911070034000c040c0c00300d20462203003030407244c031100100141500010034080c4030050040f03003890804952210a00c518400e03e104541291005115484100b540c00c035180b0b00910724249a00c811904480d010b081d585450420f01c64003881e0043c2e00d80750b00803003c48040350030095101c00759030b40b100c1012000c104c00c200542d41940c0002041c1116000134011000e10f81b490743c400c6054881d02000080540140c5502452804564200c070fa2046800c0500003512540712710782040400354283d4400e02404030803121410581c14440080201300c61342e000f4100345d910a03001c42e21542c1da00c408102440c0218403e0501080d801c000c0c80301080000d80045 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 544092248 1250 544090998 544091003
    0x10050a0603080f090103110c0a020d0222050f06010c110f01030e031201030c050a14040510080a03080613051902130e07120606021c050310030503070506040515040c050607 75
    0x40e000d9560b8aa044040d40701c1500503d2403900043e94100b50768061142d40d102c001d001007420300b00081d0740041079460100003400391080801c1100003003190b490b21a0b0300940c50031003444500007030654500c40701401d002c0c0c0b40c03150440a8040050707101d5218581c00091280c00460941c004515141070140178640e28442c1c604050b01d1300704042081104000500070068901c100706095803450802a0b8013200c9608080d12620302c0000400868902180100c0001c00c110b0b00010251180e00d101d282188c41540882c4481c003c0c000d8841c00c0c10b81014120344034038015241c0c2d6801a00c555400011140700b200c6110b940401d281c80d85584800c940c1c0176141120005d2103841d40141c0320ed00c100c01c00d240458900c3c0c00034036140c010348403040e21805083d008042030b0005100504031022400c14925202c5080000c02102100064058200d0304c0c4210081d07410a0660383d80e071320030742010f80c6c503002d08440a582e00c0c4940201c11020712510600588a07070741161004000e103080408204260b841024103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 544093498 1250 544092248 544092251
    0x609081225091a030a06091a1e090c0d02130b07051509191505010803091c023d020c030f011a040209060706051f14010210050a 56
    0xe0140d8514020503540920701524144030035950050381c22500410007140001085500c4404000220300c911140c102914120481603c07555180d16010003407802c1c1d8407000c082410181d0300d1400340c0404084180407642034465086203002c9807220341c42039006000287d0880701d04000a015402c281c0c01401403d52171002c01b606d801104100700400d40e20070780100c20b46080c0041c81e04100a020002c1091860030b5901c840b040d85805248551169000c11001643c443c40d00e200c003080000c0038502da0361174410036008102c07a50b11600350f10350301c4e040b920040b401204900e407410105110000038820183d40101645c1c0c2c051ba422003044c40200003405046500741c481040c8015001700d5000444110440782c0c000c00785240a20105490b1054114070b602e0103902d807c080440001540400394036003042a6070250f610240300c00803408a2140b88005030810345080c0a1000c3d1049000c00301d0b078007005601035500040d032111810091144204003d90141e4014503107500260600d411450f030202c24007c0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 544094748 1250 544093498 544093507
    0x4052b0b13050706090611011e050a020c01050a240b090409020105090405090a170a1416020a0902030405060a06060c060902041509060915060c060902030a06140402010f1b060908 78
    0x2038241c64215250814000705c1d8426206102c2e85501c00d114094003000c000c000d000795540c050030106498924103180c03100a850702c2c006612007015804588c02100e421008111340c2c9031a503210002024070006410704500b4480300b4141d2142d501011109940d02c140a4a00c3e0446110411004014911089040c000c007440400d00c103030389034450584a002c411010f0244115245041444020000da01c0c2201440600c101e505181d03020341d4003164168000080c0341c1e25140102040022010200000d60040009001050b049202d401450049200d4011140e05448418490042d40c2071801200000b55505200102040d080c0e00308410090020f00002124100724681d103201e00115000010400e89946007004a03410030f204901c0002c1603044510340560078814000c00c040a882006080c039500c07007200206564090144103400fa030300400070064118481c02101042c00101e400340d01040c0e103011220b03103c078020a0500072010780088200401c48c102c2d507504004001002050b56403560910 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 544095998 1250 544094748 544094753
    0xf090602030c03090c060a14070f0b091006080a1a1f14120610031b0b13060e0103090209011203020c09100e15060d11160804052b0b13 59
    0x200550082c103054901954915001a800340303000c0b142a88103004100c10031520362055446803640c19160980e81160b940c0d0b80c17150a00c060780240c1120081c1918648106000710900e001400d991100b002d2003040c0500c95481210742d031501c2c80d00102402004140c081d0f011810940380384943e009640c003440c401031281c2e511001140c040c2c81e4021640c4003500601c1c2c5482c5141210f100b16484166000610b071a19103650224403604062100410928800c0c1c80d044c0000e02e0008541c004d800600781d526107403030075102030404041e42c0b4030500c00461242d06e410721070355100703005800760a42c02410000042c0d18000f003030141030100720415403c40c05215010718040e41e40704001801030140000c0c00000f00e0510160740300c1910054481d44404101986803e81c1b620b68000352115480c40c0354000030b45d04a5994007441d180301e4400c0c4a080d940c007004030722040020901c081c1094810a440100710650045001d4100c2140c1c02600d40004502e8039261000588c0f101c401c6901048a2402400d42c40c901d5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 544097248 1250 544095998 544096001
    0x5070c27060608070e0f030c01033201090e160501050f04120c1e120305091f0201091205070201020c190b0301030c1a0702010e0904170d0e010b04140a0f0906 69
    0xd800440c00580da032014040c2461784801a20301d40c51044420012510348440041c0d0343d0320b40c120307215041c141c440c15015a03a001908580560311451078601c0c0381a00041030403034036817a0900410001d107160100304516640b00080c150301c252500d000c02c5041c142048010360341a00504a20000510100000306081c201c0b400080c0b5503610840816140c0c41c10240b01c072000007022284030f8002c210441c0204848416800c0000e555605810001c0d55801c905000c41c4c902c500c0700264020b800c240c1c41c640030350307641c1c158032504259000312214040c0c902840340440b4070744600c00c000303401640094284000c1e80b03045e01e090080c081901c611014208c0e0303180810442d81d0401d1340240c1d0040008030b020850600134021078040750708440300c800e10304001a400030b069201c00342840d41c052204a0001003c1104501100c186031214030503642d180c43c00c0000b52409480d45400d0a07203036500300f9014901c1410507000d03445042c581ca24850010355600362101005240e108070f54041700b030303c0e01d55000c0424003d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 544098498 1250 544097248 544097261
    0xe060408121810050418021303030c0309060f0c02120c0904032001020304020616111201240305070e0903070c03030c0b0f010b0405040e0c0a2405070c27 67
    0x501c00541e8640e05110900244040c4221010f40142046040703036030036030b0340001100d00351405030340c25140000d04101803900a0007506150f00104884820220500d038201100240039072003a40c0724551036032511001c41d9410b928110781c0d00442c0a0890040052400c4000300c94000e92101c01c80d0340070740101000845016081e60158046481d0b05014140320680b55110120460440000d601c0c40c03c19601151480c4501c220000d0400e028420080030040040600b601c0c01200400188648200d8052940241038911030120144284103280a1002074111010201c036000070103480784c00c0c9041031140040e00001d0059265020412108000500c1c0601f9140514000d540e43c222060103031410f03400e01d01002d0902c062030200b00004000150399082100c0c02e894040d940843c00090400040345456043c3c0400c0e9400500c540000c41d03120305a0500800d2401c1701c012180310544900c0d0161151321070240302401c07050080e0001d00075070104510740c644030139410b45003500784000000640c089400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 544099748 1250 544098498 544098523
    0xe03011407080618010509150f041416090302100503130b010612111606020a02030f040e040c170c042a12061401081b120405030705010c0302090904030e060408 70
    0x7214000e001c3c4900f80b40304003d56482425204260550404c0c0002e50709a80003403007901d0700c00b86603000e000f55856034101c402c04a00082c00a101300c0704540d8040d800b0100c12950400b5110740c031030040c0c650503c10780502c81200d4002d0300c100b0515600c036004546aa000503d00365034406000d500200061341901810f00034201607849030500340000405009440b00f0b070050140104092000366000d08100040030451940150010303038442c45210245d0850007203540e000d414410110300011540301c2c0070921813055220f04042c546546c1c5600800f8605100e07000151580d512036008001d03641005d6102e083c8800044280e03840301420800850041072035049040b0006440645500c1e02a07083c0c0600b4015200860f070309020b1512110000344907050060101d00501c810142c038485000780312048400b013150344207a80c040c525103410aa80d684c1e02956044072a503281400f803d0b00684240b003600c14401c070082c1401c405480c0d94130b00303d03030013445880c40c1e45d403000c002c00002031860402c00040c0e8138001c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 544100998 1250 544099748 544099757
    0x190f05011d01020d060603050f280e0304031104020304170f0f072003030f0f032a041e03080901030c121a132c0c030d170a0911010e03011407 62
    0x2409904d03500191003640d030104040c1400c0200381300c645001c50b0010365201c01d068801c40742c04103d68600a01c0703244c001d908407616500d0291094000d4101000a10075680150001425005c121085c4801c81c4002c0740c001d0003505010301c0c003172030000708071000b442c41d24200b25119007800070210013450316601800048414101d0341c04044001c3c001e220450b0303440d40003240950b00301440702d00c03914183d03c41c0d403218140203c000030014881b40c0c9446a02000c3c0300c2c0d10f01740d0085103842d800050b611980940104e41d654004c0c5031031085c407100580510802d40798414111410460038000540240025050940a200740065481c141c0f0080b403180701c95004000861851480214060010484101241d0b102060500c154502f440700010052038064003d200c08141240c2440c04080c00c144514007001d0303250050300021204150310900700703880945514000e14590701c4808480303040b103c440300010140c07500840c44401d1903000d882801440100940007040384c540044074100c460130122050404903 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 544102248 1250 544100998 544101007
    0xe060703050411011d010c02040e0703060c120203010501050a080c1c060501030c02031306080603030d0c030c1202210c0f0c010207110126070c080d050117190f05011d0102 75
    0x2100c42d0f4502c2401c0007800c1184042c01050b0107100c5111107400c10324184050801844c0c21503d07507922080003c00c8482c10344180700d444e840c000780540058014100004c0e18500004403940d03092007201d0407590141c69031861320b001a8400c1c0ea25031002807407000d1501d014020380110000b00c2036050000c0c0c540b8040014600d040100140c2159181c04001c1c0440d40140181035403012103111000a0b162360303060a0300242e8500f000240b0750303c1541c81c0e40783d28030308210031701140b0380c0c1542001032101d040f40c40e40441c0c0c085070744500040380160450b14203a440d411132501d041440d00c10105070064003015406241a005402c800926801403c0345a2103039130002d00c0fa000e00014065039181c0740701c240392100445981c0a40040da50140b801e80300180340300c080120360043d000380000d220607907000b94101c5e1140a06038841d0b005107001d12030340c4026400c620100204a00100e458400640124442408a03c0c00d44400f00d125042180440f801c0d9030701d0841c00b041c203040143c00030018140000251341d4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 544103498 1250 544102248 544102253
    0x20105010801140f130213050402010806121c090503031803071e171e15060111030d1104030605010b07200f01180f0b12180d0f030e0607030504 63
    0x21100140d004200d503074036000700c1c540900904260342d6000f203005400c400b059150000322000c803528400300290700c015007510340588120281c001030720860003600e84245035503410090114420300d00c0e2420100d60042c800142d0109520703030a0000c403002c2032420071031460329800481e2440c1c1c49034100c400b141c0007200c038254840c0350070052032001d040c0c80034122504a91044a0000842c00341c0202c8039245140d0360710b0607003040101300c12006004d1080308022000b08441c11a600c1d0740f44c640c4500b28003000c010005000f9402403203c4010a508000154504503280c54048028468103041110100082100001284c407900a160107080380384140d80d0b43d00d00b00d26003085504a00403284131220a40c3c03c0c5410b1079540c500040003409000e00b440745400080c620340c80c09480080c0c0006100c0141d03000c01240e503c1400c9c000c1d00b407451603090101060307202d040486400541d4043c0c0034000380e010960701c440d41d91181c6141c80100c0044d08002c500c20a141d0405400d103101203840714002076562080106 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 544104748 1250 544103498 544103501
    0x1005100e0d171303140a030c03080c070c09061d0c0d09050715020102280c03050708120a1b050c0a02190b0d021c1503030e0303040b0f0d06050a0e040f0816050c010201 73
    0x1005420700030000d4511b03507900a0003400d00241c01400703001c110320000705400c4401c01210702141d40102030b00005922000c441d03000f005c4030301880884102842e11441200780359540913018908130110039040c160503500f0078001d02100f900449460060f040d00040194444a4010301c00d0243c1d0001342e1100071104001e0580e802c4540c8071280180303140850704805801850350b45400f505883c107196250000e00f8030705420301c1050114003c110025080040ca20070503032000004402c940341c1c4019000ac2d000c2d04481c03900841c0d0460303415800080a4000500c1d00720349101c150300c20100d482880c1ca41d201c50030012500944000d0340e0b01c50700043c2040300310080035000400160200e2041200c2d1220511aa07000c1503107000080a00071404a01c3c00c59640400580b802041a010891b96620581902c410075421214050b10085e04180700491035280811415080d1010400103a00701d65403503e45d04520400304c40241c0f440c2da000c010f0449800d8007903003100141c0340940001c0050340d5540340020b0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 544105998 1250 544104748 544104773
    0x15031f0e0d050a090603050a0b060d0c02251503110310030b0c040b1c180507031401020306100f09030b070507020a090507020d0e0301110a081005100e0d171303 70
    0xb001401c10540402641020b042c10039101c0501d4006010b541c1c0b40040d00040043d03414603540500081192480042150444045a0300e103034242c172071035102032a45140488442c4000c207420078070348006012015000d0340c10000c4000701d10300403480215484011070154001d844031080e002d0112414803e00019111484d040b0301c200110340c2c03905244c00700d01041030040c505072200c0150f105000303102e0b880c0990400308102c8001344a4014841680c9082c507a0b440982c4402c4441000c9040403603040c120600c00d0380d11039072001e09842c40e10702c0b8400d021182685041000824030402d914044042103a00030380e140300b0308940e01c0701c0f940c500c110300403c40c040350383c2d0340b00c1c0094505181c10800d005502240303500c070081d507034140646004a01c80009000d0b010400c51b41c1640c460101d0100f010950083c1c95a0248a104640c1141c080d00d80003423022000c0052115404a00710700028121410a914a44c00c128003a1009801a003000101100e041e481005503c00d0782440c1901402880351a48404 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 544107248 1250 544105998 544106023
    0x20702040902090c0d1a060a0c0f0206040902120c040602062706180c0301090203070b070f05030a03020a0f020303040b131109010b0a0210090b0a02210c070317070815031f0e 76
    0x1000c11556140007601d6031041c48c80a408109072210a0010131032881c495030303040740d40202843d84a60300c40250b10b00a4007c0e42514100c400b2820100c0d8001c14404103c074151880c56010700b055a90710b481c141c90b500b40076620008412a07a051010b00f03250144102c40c0074040c282030345000400c1e81c403003103454180b94074040c0d440ba0341750501050040c1e40000314142100c80d5484400c0d00c40d42c0c01e0824a544100141e8060102d00001501d0101c0b00d6150f030044c4070322841511486448001450103c0c1c0c2c03400201c1d401001000c610b4080b41610074518845504140706914142c040000e03180801d81e02c441c20ba202e404151800b041100b2201d4041c80703901c1060f00500f0041010803034585030150803a07070207010020581d84c00101c0a145289108000d001408402400d4403203043c11460060180d1003804140e000407541c200b0400752041c040b50650040c201c980c1d030450591a4120004044582c41504a501d880b40205d50003c1c01620480400c1c2c21142106c00500011760020044c00c00010a242 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 544108498 1250 544107248 544107281
    0xa020a02101d1002150117070807150804020f100206060111010c0e060711030f0703032d030b0402130b03060301150302010c060c0306031713090605010f03020702040902090c0d 77
    0x81546040d00480302c04142208076a8486031903a0800160b060650507030f14026030240d030000200b803600c43c500c0c11b100c01c0c40201040300c1c504c617510451203407a411107010344401000f0f03101c03001403510310a549036508640000e000c842c14111440c0041d06c03d0124100080143c0c00c00030403c101b80d0f801480c86600d00703c502c002445910045100101482c1e0701140071445920042180d030144652800b10040f0018007404a0319040903030040599507140b6440101c0002e101c0c0c0002c04a02c40943c60a44c002c0c0203241820002072400000c10b90203031544e01140c0e038106030b00780121a40102441c01c0e400091078101415035590420710189070940d0310306a03034521500d049440410060340d2002190704100d410180014048a0000d8101c0240095038400780819113810903040ca05c01c50b2100403c20080910007441d58070b96110100303002d8403010701c038803400704904d0807100800d14040c1c0c00910781248001c0c0b0008401419a00150036a041600d40a61440c0e020a4480004085104a40d10040724851 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 544109748 1250 544108498 544108517
    0x150a020c21070b070507120302040303080f07020a0b1005040b0f0603061504080d050d0c092616030c030c1208040b090102013809190c11030a020a0210 66
    0x1203841c0e0319070421020021034081d00140303007424001401528215540400803d01d0743c100210000d00c2c40c1c00c10f000130340342010354840b101d0a240c00f92080310206c1c0d500d80c40340c0200340c1e1881c0100203001001040c1d00f0540c064807905100040450003058450f400f0b12051220700c60800341400b0465600c12250380c040c500000c42c000d695034500301038035070103a03045400441030450203040901c980030325400000300d441b80d00001c0c0086500440030304441502c444007001100b0407903070300319410a028070440c0081d00110343d01c400c40e05103040d082907031039400100f19004030107903000c0090301c020f03160b01c20781e10510044014020880c024501c00c00501e0561445d8000381242e4441048521561040424400c0001401f100c40d900139081418511070342c0603051601d54002012100d02d01101d400e00411000380b8416030100c0c41c02070f1a803801501e140e00081864001c1c4c4070448024030761072030300c942401540d81000c07581d100d00704020b0810f0340c115405001c010750107206016100c0754880442c4140440da85 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 544110998 1250 544109748 544109767
    0x100f0308030c0a090b1206040f021305010509191502071706010b0a09030609061406010203040812091c08281b080f1b06010501020c0607060b0604050909150a02 70
    0x560703810141c1d105907036a445841a80075944034010740d10107150071a001c20703011201246c11403e944603031000da4090100640e04954802240306080130141c180d00c0c5840b0a0105510420181540a10150040c2e101c1e000e8075a40d074800325519841004829200c4003c018081c1d0f0520403000142010041d121422164103010b548400c1d0500401c81c10f42004503590714010311501201c801140c100b0300821126185050030009454142c070800107116407200490351951000040b01d007182c0c00c40e0040c090f19907025800a1480e442040c0c1140d21843c802c49204004103d0502d52810b84c0c800e50b03807983d07034904001803040d05101c64290406442d051000c420700b06500031403820001210202940f912510318034181801d4041d041c000c038005000810341c0e00e5030054001c188000001e200c421640f03d82c4c1c0c0d840049030749040101c1802e411250a112031700c0051401c4d041001a428014645420309803a0310100c0c2c10890b00f01c03000361481e4003099a00c1c00c40c0700e43d54072041e000035004105524042401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 544112248 1250 544110998 544111013
    0x306110316111c050a02010606110705090603011b0513050a030b010e0703061e0e0604020f07023d080601020f1e030d02070809030d03020403020d03050f21100f03 71
    0x4800c602481486491102060000e00c00c1c0c0800781015103940030040c101140c002c1140d0000002400076600c0c1c45c8c404580300b03002c2d50340100c968115800820038507080c441886402c82c8080d141580541d00c41c5003545100180d4500c040041030282d45160f150800c140940c05194290380c0000d0042c0014102030012403800e01c46241510030034007a400080c1c80d000c01c11002400c071a0700c01e80a090740307909660702a4032910711500444106100342d510a4581e00c080004902c182d08100003080c904104c1c44005044c2880c04803c400341039001032108420b01810300c03502c01100190014468224807011403278507004644503401810a100810f0ba2281e845030300c60340c9041082c0d0381c13500c07603030500307001e0700d501d0f40c00c004580300d02030210001c6d03442c1d400c28507050f0300036040340218600c01d0103013400e44c0801520138400d44003142d400800d03460b407441e039a40341983c060b40203003003202940e00c0030000014a07085464184c9409800180642110303d004960444484000c1c0c01c140ca141034608001c00c0401c0d6a03 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 544113498 1250 544112248 544112281
    0x108010f081c02340f0b0406140403080a0305010e0108010504050d0e0301061a03090105010b031b03061302070c03051002390d090501030f14040f08040f0f03061103 72
    0x301e4403000072102d8904016031a04a00c10f105a1601c3e100344681c51810700207184111144400500d00800300341c07544001c1307040303000f40c0c0a2a0034201c0203001c10000188102d400e213621035611001c16151948940350010103a01901c00f440200b91a42c00401c4480e0306140360500400c000e0000b044a81040c0e41d803030351900c10008400040101a600118140c1c5d400c0d48100010b200c607024100c41000c40c0d415480c02741c0c104442442040d4a00400064801e0700002100e1203035010310f80e0301412800e43c8210071640c3e0009840307a07800400c0640c00c13000b0762003203100400895010f0b840e10f286091441c80c1503413420341c1c220880460756005000d1100f851180b502034680c0346c0b84240c2c1055625040d1705560010030f0700d4900b0070056100c0d402c1a122960340040200040e20710a0317a05000d180c1d0491110401d40708005510042c05502000140226a04100040c9a51700c20850300c2c0ca421340d10a218070712441a60880284110701c01d608004002c428444c4800060306541010300314075043c10b104021402 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 544114748 1250 544113498 544113523
    0x8040c140112050a0f0606020a0c0602010c12050405030d020d09061514130207050d081e040b07180305030f0a0818062805070306051201090c05150f070503090108010f08 74
    0x443c3e01c081006608182c210046921080100b084159a518030095031a00305032029152010384660102d040c52040c013500c800c040c901e469010390100d110070184014200100b065174580814812850301d08868002402c030400e000e280800e603a0305c076082c030004441011382a2490100d40004c10803801b10500080c10501d9002c64600303c110100b408004080d200e400320003030a5020707140d504003000b074010f1000784c01440410004001100e803441408032810041e41d0250200805034002a00c0c00c0c400d48070044264402096054401c0c3d40c4d660f000d15541060304001603441c408180c400400d540903d200380d010362600c038036044080400f864a5280c0c1000b83c07003104131407541c1a407058000444400718448500180080000e8030740990000c00410701070041912500703503000a041942014001e42c6680313500309c0d030f465060701d10300420001800e103d0010442e070b0b0301051101807007009405014000c81030041001d95600d1103844001085032105030401c500311200f40c0c1051180581c0003c0c0400c00c82c8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 544115998 1250 544114748 544114751
    0x1602100c0e040906090506070306031209031509060e120414222708040914240a08150105010e03070305100b0105070609240b0108060d06020f0a08040c140112 69
    0x307203e400c11030050240040003518502c1000140b0012540c0740d1300c901c04881c0280001c04103c0c0890f2011146101301344005800c0c0100e044440a02000c294003c43d01c841c880c100008400348003890032810710040003007010f80028049000c00200040280d800d1f80008111140d2482c0800712416004404e031020340c1700b610690720006501060b00751010003030319003040401e040c1240c0040c50180340a034094094a4003240c145072001400180c038042e00c0317026600a21981c5103c0c0031081c0c507603000f00d8004007007d5020a000d03200080d20b550501414900c1e000192007207882d981048009003240c00d42c410260302903880b94100300040303000070580f1003e901400030003281300e803042001225103000d880030180804e46403901250801090301c0325406140c070588541a44001d08030b0003c2d00300c801c0025050b010440700703000a45503142403c3c64040712880f44100504110710290041503a8200103440404504400184401c0c030041c072007004001d00f00d10500c00192200b0b8000201710758000788200c080345 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 544117248 1250 544115998 544116011
    0x515041119030e06090c040b0103090209060d020102100e1b032d030f0f0c0d0801050f090a270b2d0907080f100e210a11061602100c0e04 60
    0x40703110f80c001441090744103048a15030b05185055030f40703ca0396a46500d00c2149004403d000700e5029002c1c03810aa80c005100c138009603200c1d82401400c110b0081c00301d0450007909070b1881c25003150302c0303074584400407030008000100e4039481d8004c03589400a4090707c00da02040c0c21801702c000c0711880012440b03a40300c00e800905c203912115440d500030016201e444401c0400d1072034103000286d000e041210000c004032044820078101c1030707601c02403c0c02420b801c656041c0009075141400d810a80d0840510b003800600c100012004c884151518014401415a401904010b12840a2103560405441080d0403984010543c44a804080a0300100c0300803003d20001203004105100340801005103800b91030320708d5034400020b51980e44030303120030401610b071081100d681c01002900142e4000410a24070840100b1410341c0d0403030300280c00c0a0308002d6900da610342400c0c0140806401541e104003500d000300e044003c041c4c1484ea40c41030b040001864242240009940a21180d10052082c1c40010b02c0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 544118498 1250 544117248 544117297
    0x150504050f040503070f0c0e010306020705060a09030f0f090e04050616030507080708060f030a030315170307020120160504050a020309070e06011812021512040215040302120105150411 81
    0x54080d0380c5d02c0400d024190100010a0007013380007490050300c51000e4800c5030f640d40c0b80b844100d03a140c0b80d0260004212070600d141180c050004011022400d0a103500e10f940d43d10f1041c040c00500b160106d545030480c8043c042007603040c88888182d0115410140490326088400500160004201004101d1000c000c1040da0301c40940c0c7c1d503201c4002505560260a076402c010b400341c000104190501c41210200144045811040440ca1143c0350042d5140403503d40045a1414070842c1940106034000b60b03001c10308801f004450046074002c7c03205100d20745000200021a02c0060850f04414010030801c40494004075251040c0c0344284203804598403404012a0001302c022a105002903501001003400080c0d94565141c2d00d00c212401d08981da82644c518000e4060201c01c0d0007100c224001140042c0342c0342c040c00424416503003c01d0704156030b9800141d110803044071070358040d9549100307000d06902600480008010706843c1400000c01e5101c3c05a0248030b416200f0040e890090140c105 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 544119748 1250 544118498 544118513
    0x4060b04020f0c0f070b09010909020c0f160501031503050a020d15020a0e0a0b0703020d0507030c02090109021206030105010b04060c0615150908010507050403030f0c06150504050f040503070f 84
    0x1800294560030540311500707015030075504ea090702c0300fa203c1481084070000c0e10340308003001c0351354036841070391407040040c90000144065048500d1140700c1d800342c14290010301108204104822031529014840c6910302800034084030000c000c40c240c4007880c40360900114400040818400f0f9040c1c40796445081681810400b048d480221400320134000118031400c0341d030000c501388210400701c4032140700704e569910503c2d6910a0300002405a000341e41122503c40c02030000c0d0201d140642490001585a13030b000a14a00098210842d15640801d03503d00c102c0c40c0e40c40e62944a070055008020b9541040c0c080f100a01480c4503000412a1100458041040e1a00103051071940720030600e100946031280c0b800d060703c0c2c08200000044121400261b07000e41405400d010720219210300b0725150070750b04e0444009680103441c2e01032280c04241c10300003400314495420f03c945c801361491400c50130001088142c82c0058500000d02032104244004183c001c400c491500303900043c1c030390a803400e901e415070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 544120998 1250 544119748 544119757
    0x607031812060f05090606101403010b0309010b0a320a0e071202090f10051911070803071e0c0b03040501020901170f0402241909061704060b0402 64
    0x34550011500c0000700c85a0094500c1201d030311580083c80011003030495002119030880c3da08405034014408107005081c00a15110182114074014a0744c0c4201282d035915688213030302c0301950041c00401c0080505083c8240402c41c0c03c03c690346000189420a018104451a6100000580a00700202140d072180780c0000f050f55001c2d210710005580d6803505014920200c0704040454800386c45005003203518400ca45c0305007401041e40c0d04207009441448624460040d510042c01401c20000d41d01080e45010b584505070166034108203007074900142d5041500c10750080c4901c1d8014800ca00014802c0b2014113011080c20030400781030356160800e411011072030781c07107140d5030070001003440144a4103400520342c801c42a215074079030420b80380c2c0c020a00d14089501600e107000d07050110317005161060b03540d0303109021290000040030a002c0d030402035501160041d90171500015000e0252350f007011101d801003440c0d04004200809005002031800b00c0100014012075440c04140400d41c0c03030364141e4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 544122248 1250 544120998 544121027
    0x10203040306142a030a02090d02090a0510080706020705060d1509060e1005010f03091104061e21060905030f18030f010605150318030f07030813020f060703 69
    0x52140c140e43c0c002512050f03a080d542078003100c82e036031040d09a01d81d401048202020880440501d550b503000c1c100310003504444101c5034000c03070481e039500142e580d40d010740d4002e1170240000602130415400030310134155154402102500009800c1006503004102c01084410540c0e84a0341c0c7c5180304540f80082072018440c00b5200e144240201d00070006600c41402c0d200c012500c0c01301a114443c1803045501e507403181d2070000d49080c50781c450151082e004800e00314414103c0e803011681c0f00c03000030241c5803580c00c281182da80c1a2481b40c00b514038030f1001d000600040011010210b58180d940f6185d16005030003800c6e00741c940d0811001c20000300202e4250340c8040f0086603c0d036590900090001c4621560503202e8400d2401040807520180300d0a804c655000300414445100700403138181507000209014110a03000c0000f4000003028070081c0035508075440c55a03a1100b0342c2c540500428006011302c2503805442c3c0d902e0340140c503840d2446500c221300f20f0711591910014503080391401c41d40202c0c0b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 544123498 1250 544122248 544122251
    0x1050903070f21171e07030c03060506030a0e1002090a060c05070f0e0103050c040b01050412020f09010b03040201020d021626010c050a020708030f12040c080a080403120f1409010203040306 83
    0x1020650f42e1168103448900044001041e60703498500780509216648140441581700c04008200d00030b0080c1c1c05107018585c14140811070655400c009a101d030000c07a80980c11076141c03541c420300b00b01c0501c507a04409410100450800024a01145000070140a000d0500c03441d808100148001000b0080007046d010a0208489031104c60006400c2420b2000f111103205541c264040313440c160245002540c1c040e9039041c105031030880c00d8042282e492700260f800428688200800344c0359000301c0307404ad14078205080e54900f01032000901c2d00109184820840d00801c100d03100408a803d2921b0440709036025020304140d584542403964404176001280943c41c190012034011b402001505043c40d40b6001e40d2409075030381c0101c5440348281501c11224100401561b1401d81800d507080f5002401021281c10460b1200c00960ad020380c184020303036600b1400b040401c05c20200c500b0401e07105e0400e241550442003101c0d00507080448030344201030229004034142400340d100f041a10000d5400010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 544124748 1250 544123498 544123553
    0xf060d05061311090421030902060403060b18010810050408190f030e0f030f0c010207051006030c09061809111c0605341b05150901050903070f 63
    0x1d0700030401c0c1514400715601d11600c02c28000300c1c41d2680540340320701d8101c0c9031109442c00d4a802941d5412058111b00d0605a0326600340015850b480003a00166204290010f9000d10690070003681c20301c0703c426021004070820040c0301d01031002c1500d480c0c00324580d601080646452901b40381c20302592010031404c0680045000d189a072103100e6210342e480d00e4800704417100d00e00358407030b40303650b00707280d46503203c2c0e00c20482c51441c00d519000410080c80004001420401e866440074148944402c0600c8001d0f00c5540030300c01d00c0001c4480000406c0009410840c40b45400015050241503401c00b030b030107540d20030a0308180b2051002d01c0c00004402420799a00d00c040100d030310511000c00d9000d80d1090710f00000100505065040c0c2e009040103141c14850810540072071104d11220300183c4820020705168103682c04050b1a019444640302d5405007407a64403800f055081048002e00352140c076070400c0280420f10a010081358221030300222102c10604032401d003002540381c0824020341044111a = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 544125998 1250 544124748 544124761
    0x1d100c050412061b050901410c010e030406030b0402070c060e0427140705060f030901020c0a11180f1b040b0307020601260d0509030a12020309100504030503030f060d0506 75
    0x5c0c011706108000362070f41c2c10090055104119424603413012a2409500c0d0f815002001409100c0c1c462044802c0319480d10304101b050761300703094540e280500300d140e510125041c024130b45c0602800c800003101740c404504020300b5440b0343c0584031442c4640c0c418441c0000403006140c071160005098200910380040d413083c80c034908195003a0280c0000d903011b010310314140d0380c0024003081a00c111800188101d0810031200c50540f0745d0340c0050202002503500b000180440642440003a0625006003a04074807942180213210b0844041007a408503015440c0403c00d05c0074a144031a82c002a1131380561200c06500503000d0400d00c12a0400f0342078103404801c1041c160703400500c59050302c80c200100d1a082c064100c100350700050660f5286c0207030300540200342215100e4805040600c4005085480307922160716001116910358941400503040001c806519040035000c140346407207a860318910b01803440d1070f0170342c4130700002c1c051120341a00040031078129591407003a4000d054000c410703280c0320304200 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 544127248 1250 544125998 544126007
    0x906030b040e120306041103010302090411120a0302030d1407021c02010209090a05010302121b010f090b070c0312020705030703060b240c0606010518010e03030c011d100c050412061b 80
    0x4450040c032503030500c40204403441f1040c0a41c0d0489074081c1c10b480180d01c0f607030342d10707400c3d5003120f1070580d08a4207104140503485810060354a00314001d40181d0360707030002d5115080546102c286101a00c156000503c01807030b81c00100c115004144080c0d0080035034000d0801c901a115030342c003040e40b01d60520180120100568441412248200c501c8260180041e0b071864903105441100d51600517908600c00b0343d94010700d06110481c11519090700010b80b0b48140480c0354101c41d4041d12020001d100038020441071168010007030400d40001c010451030b080000759101d080d8000200a541c4504071090a9100c0000000003072210240c00640c1110940c0c41400c103420007060f168071403042501044607940100c00701d60400c00720b0446040c031108201c005607800c02a030309220313070144010840b500500f9821311880340044c604c90340740d01c202088800310b0343c0f41034602c0c1d5002800a29004150901d0f0b03030404200c8040720804007029549280b42e084c02070003840c0340110700130761142c40440d074125103070f10 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 544128498 1250 544127248 544127251
    0x4080c0120030406200a02010c0807150f05040c060e03030405060d0b121605041103060d0c170304030611030c03180a050304030b0f1e130203030f1306120504030906030b040e1203 78
    0x402c00700015900701e03925175071380e41040c2d43c00a03012035070000840d0b012404480081c080d15009040c525480d541c031804240c00c4034031202842d42065a80d02c2880108088031440c0c4005182d5460a5903002802400084d101e20441c41035a125020000d4a00613109040d04044070307100c070080032a43d811320750115180e110810950000c9003059030400c041114038207403055100c003080089a103801d41e40c0d28800e10200c20751603401510840004500000c1d4040d01011181c110380154001e0754940c2e18500d04142900d00c0e032201c0440030300c02402042403000c112404d1340e510200e01105c00d4103144007207080320301701041b0700c0004c1d0003404001004000c2c4070b520001c2902031080000c24900960fa40c02403840310b00300c1404110311b50440d100124000e10708080c640e0b45074600003010343c1e140449509211425030b0100321001003082c40c0c1c200400516030011451500d0002d202c90602451030542d4004012a00364041ca0080c556100d02e5944c041d01c540e4052641450070f801180c00200c45000d071010305400 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 544129748 1250 544128498 544128527
    0x1b05070b1c0c0e0117010e01090e010e010906020d0e03070b040f031106071d01030209031002030c09120c01020c01140901030c0504150801080c0307030b06091308040303030e0105060604080c0120030406 88
    0x89400c0070003401c005c180c01e0706040700c100302d00d03204c4664284844600504000803401c3d60543d04d0740b402058040c002c2c416400385510036800141c0d64010728281006881f41510352244680040c4114808681c6043c040e03503102c4c1e03000040e001040110b207802e0f41c0960164185510f248180800c000c01c2c580c008210300103210034034600040ca41d8100d401101684152104990181c201c0d001c4648150f06030380145404c20703c0381c000a030030801410041110070106c00c40c5084c240d803000002025551f014464640c150400780303400c84410000c50313200300d594400d402141d0b040659400207103095a101c0c100380d40c00f8000d0243c4818040c0b0308084000c0900e9800e000d0f010150050141580083c03400180c02c0b01142c0c1c2c8101e0b003030040c0d600c1c8420003910440040c000310b44024030740682c0002481100051001e94401c1d24009002d150f11100b45084038002442507001d0328081005014114000482407030750b030824039041c4041500e40d0340e1004690030101244043c1d200c04100400c4091f0450b0f024500d650 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 544130998 1250 544129748 544129757
    0x3030b090405031603020c121606080f150402040509090322060207091517060a0506240307030902092a0316050f0f07030f1b05070b1c0c0e01 62
    0x1004081004500c4400355070040c2194410481e11820340600040d418103180a40152041e10360840041021200150a0510250024414000a040010b01510141c079035442c0c800c60526000c41c2803512008003030300c2c00c018030035a074044480950f61501224042c0401803e59a018105122659074903000702c4042e252842032a410500342550291a00d000c5945590042c1082442c10420100501c1da8040041024080f0b0303e0100d01400700000b1407031036100103001003283d45400c007048800c803a40078000e01d204401d050b60070154103140c541c01880b140000751510766a5159040709400400c0c95440c029081040b0900300183c241d111680d001c0c00035001c920a69040400a00103030301803100b1550140044005030071010714502c07800180044000d030310384080c07130a550503a40315100c0d0030820045000a8103a503080403d244c1c001a640036407188080b00c000c0f00200d6a03280c50310750b1154090200421004910ba0b4181e21071300000c0e07884000049030030488503810101c0181034103076050700742d80440c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 544132248 1250 544130998 544131011
    0x1110705010c08040506070c050114010312020d1404030b090a02041e0c03050f150a030512030115050a1e030213030812060603011202010e04060308030f010501091505070f020d140a0303 81
    0x40c001d400c2d0f2803189602101030240ca5070b5082c8107584007100148181c0740d5640c0e500c00030002c1c03404c520b20710340070b107000e104000c10003014103034004d2412507100074502c100070700142c440d42c0610180c000c1d617081e2a402018100d19a480b114400c3c680156510040d600c5410012551095011030240c0c516281d80f0300c00c280000b1a0952041d0141ca400341c0382d20060312404400585501000d1800d01c0741001c00404400f0584c1e500e440741450b10302002280b01e560714000004101c54040b0244e1111200c02c2420a03900700b0308004006850141c0f81c480346190f20300110000200184a035044400c405d01110200400d961a810144669008500301c05a070342250300124050345400c10550341250a140101401030440b41d0045401c03081c4070f41c0094002d0303129803000c0001180704000d58807401d000f940c110110340c54400010485a0b0551102c40300c012040900620158000100c5042c2c40d004180388000c0070310361000c01e10154038010041c10203241c0c1c1d80340011000d0003082d03400704103000e03981c1445503 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 544133498 1250 544132248 544132271
    0x3072d0f170405011e030e030a0f0e090c070b06010909060914071e0e0f0a1706100b09060c03070803040305040e090c1e04060906172505210111070501 66
    0x6920070790088901052040c110001c2c1c50b141801103d03502c84a6290218500d10b84c987c803030f413460300078050450100d03e01110240c1501d034003e00c200c503082070896a0700c076a0f0401c1c40c850710b16807198010182c614005500020380d50f900603591030000308440082084016903078000311000f03000d845010000d1010240101e10050b1040040030f0080f1060641911680352940341503400002c90300911750081c204040220301c030f43d40d500e0070b20002c0010803a0400071103c10550107050580c0104407101d42500680d090043d410184207482c50304000780c0341280c0c2c0e116014280ca00e5402011002016158008104810182c1c00b002a1044512404110b8003031744812940d0343d15080481d40c40c642201d0b180100040c8000081c0400201071405803000441c07644581440c026030318941c001403408441201d0744ac0060004210483c1a0502c04000215040d00760040e00181c0300b0314420948102c4810400c01d026118141c244051101080000c00545c01408121140b035040b40e081658254605840d8800 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 544134748 1250 544133498 544133543
    0x5010e2409060907060f09091d010f0c020c010f091a0a020714030d0516020d0302211306140424090909050c1509090a020910020a0503072d0f 62
    0x141440f103014040ca0382c00d0090840c2c01500040000701040900b500002e00501a80700700b03006210241d0342d808502034000c40d254203494000d03100710350b46440c060b61040d000d903010400075458942440d1420300a0401138040790485115001a944495107050315410030500b840184060301d015002d4412981e9200410101186800700ad00d416800c000b04505085201d100107026051122010503070f80181c03500482c1e5580b440328000c5000d68010305115860800008010000340340d030034400d614240400502ca5010030322481020140704403a951000400c428800f56000342c00c800c0c5031058250300c038001c0164500071841814001c0340c01c40b0030205020b0340a026403503c60344c2200060100700c0c484000c0c040c4502981c5038600000e030041c405841140d5a10320441e00450304e0440258844601400300818038410000708011342d0702c410b40744070006002006980000d40c009000141a40300485e055600f110701c0e904e00e0050b624641450010024801446c603409801054003007400285500c0000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 544135998 1250 544134748 544134751
    0xb030c010906020a0b06150d061a211b07050c0a0906080c0904020102011508030306040e0c09011a040e07110d08010b041a0906070c1d13080705010e240906 68
    0x300140c00c01300340d20011843c000b0100c0c0d04403001400e030714001300744c04101000641085007403528840c2c41d0030302040b03120014006192414140341107030345004403650544407150000d0700581c16030300d11304c0001040d90540700700c5070500144056640703584103070f54035005807507001060010740302e90702d0340d100030944a0081c0309520a4680e003c00034511034070000100000818010f0040381150340301e10581c104a0303003400310342000b4a8411300071a26401d00358200700030340d00d070001100c4095028074403d8000750780b00401d0b03504444c800600b250004141c0b04600c0901d01c100c0c0c10909081203201c061004069100341c8012510001e00140c0c0c0e912504600111044942803140070100482888103000d480305204018a81403a1101c003a8034009a10011074584d4208520640701d56202035402c1003040e01412603080c001c50100d030842c1242c540b002d49030310000801c44002c0d000a4001c958441000801d5006503100200382c1c003121000320407011450b4103000f070500c41000380117690010030798210001a41a = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 544137248 1250 544135998 544136009
    0x806010b160212100c03270f150f1107060e06040c051909150305100507090608090c0a230405100608040503040e24010e090408031008100b030c0109 65
    0x14030252400e03003c1102e814402d104004007401500e0307405650a13428803a4210f01c0c8199140480c0302a00400801c40d100b501c800007002d035503150901400010303800d040592000b035002045a1380c00c1e400024420040049443c0c528031140703001000c900039161103004c0c0c502d861040109000403001d140b403132600c5150a40e001050703005004401d12041c506042c7c4c540a071a12813503141c8080ea61445c0d0b21043e1007082c072080740781c3e41c08a00d0a000344103040c02400d0001d00000c2043c4054203100c803004000c80310710300c100400c01150030085803051106001030303d00e030340c5e0080c0354508064031035080780404234568007a550420b14600c0c6080c1182801d016851044c00d0001d41e0036005841c01c482640e40e520002c2c0102d0305400100400b00708488000c1902d40030300d11800310030090700c43d00c1c01c2005c143c1480d0507025052000540d4007a0843c1d9400382c0d401c2e4000c0e44480d81a4503a122600040c00b0b00f80c0da41c01030700c1b0a01800003211288030655001150200f1304404807400c8413994001565000e03070a0064 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 544138498 1250 544137248 544137277
    0xb01061d010503060325030c0b0a0219060b10080f100303200123100611030a0e040e0304060507110a0e0a0504050a0b0103030206040b060105030702030405040905160b040806010b 78
    0x900550740c040c20207507900c038001405036001103e91030300070b61b040300c60541c001004890001c028001d22944c5110310000d446d883c00514035107842c407500a580d400a00f0294104900348100342d604002041d00046034846018003076407c40620f40f40c2c082c0901c44200c1d8402040580d400c00038101c0c1014040d0001100e4064a40c80318060300500e54021038522103240144c15902e542c60321201d111041c01100c0180c0b510301800700b0904084030001d001d19240d600c01410001c024607441c00b903c0002c8102d4040450724185005450040d201080140c00903160801c028000490000307407803034100c0000c0c00c0da148a8400042c041c1000c00801c6940d5501d0701030401c0c0d02c1e803445c0c000f0b0001c41059001070303005400381c01103401c0d0781c519555140c10560700740c10031401600700b03001b44000c00151500103a0054024200a4154500f20780001d55a024521a8911968075213040741d007408001c2c400c2c0342285409000d988030075510340b4017948443d401031040e092648202000005c038119500140c0700091b086400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 544139748 1250 544138498 544138547
    0x70803190b01050a0e060f0c0318030a020108130212030a021f0501030308010b0d0f0c1e033b0102220e010b070809040f050f0108120712140d06120b0106 67
    0x1150845d00700c460003a0411400c110068000c1485009400c1011115008541e50942418280351050850595901a0788a5109500140c1e0803042c500c1e40144490140e66185030382d0b00024950400c0c18040500c1070000040c2e0108050740440c020300038000054414241b07040c0c82a403001154001d00c809400513844900511009000000070450b1400e003907000701300682a0000d0a046910000b004000b046015041c00d0a203c2c4a0060395070001c505d0400308245005195021155508000b4040140325000c0b0b1040d1b10b40d25001d00c192104800307200031902c3d40e1419072150844440f02170f0b1203482c404500400109035550a20305030695484030300f560304003400c40d034030f00400c3d0b00202d139910351003900c0b5800106200305911510303106580d084204551540350409107402e21004149500c0c00340d0007000b46002007480305c0813403e8131010720711b0841c44072040380040c04c00c18050020203000503402c010f0005809081c105028144a0054591000d182d07a1207400351804e0b940f031400808031080220 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 544140998 1250 544139748 544139767
    0xe0a170d0215220b0a060905060306100b210408070b0c13030818030d4a0301110f21151e040e0703050f0c0303030a0917070803190b0105 60
    0x18030544480041400c0c3c00701441e4642e03103460703000401311038803100c40d0b544030400c010000e09805069044031040e17015143c0d42c28451014641204240190f0b201881c3c0054100840b04140000701407905802040c140d9500703041c5065800c0e6070006409680c071090720000709a60807003220842e510041400f2034076403201d00c0d5a43c0c3c41c003035800c5207407403840c9144c03e1880310105860920144201008664a411034003070030641000c48170500524200b007506c8400c00fa2501604c01001300c291940070b03038210960341411000001d01510f1301c0464600380380f1020480c0c0c58155100780c094038009403403500d200c004c0e54405050100c040303000c642d01f40105115a40a10705400c9c45003640d0b403103070403d00c80400054034540c003007401da4441095840c00355102075000c009110b42840a44101211400a40130030f0309000d0020360350740000303048102241c4c3d44100d48001c00428401000058075044400c6484190900b080b08a94204460503901c512250350180d03c10103841c402c81082c0301e0305131107040c14000e241 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 544142248 1250 544140998 544141021
    0x1e04032117070203191e1b110f0402040b031801090b01092406090e060a032d1208040201030507090503030a050a051b0a15020c120a0e0a170d0215 64
    0x1c2c0800042d030104210321a80c0c4c001c1024000111141516946820382c96080090391917100c00e0040020840500482c684c01c0408051012102d034001c414070080702da42e540041d07082451860a02c1e801440041c000030034024680185201c0c0da80e0304540c03034002c42200380c45800e0b10440310009082d032400310010700c00c2c404c84e41d2111010482c0100740300182000d0003004d018000b0f06800c0003000c142804020018504d000d200c60754018030568031031408905c0d60303582c3c08502100c445050402c5214182c10101c541d1341d024040c001c5500301a054100b40c204007c0501200000d032000d0b80002d0500001405850260002404641d00907000b1481d040c00e20320202e40e1a0040e003880e90030010208401d450185011000591071040e407005070210401070b103000c0c000d086070284410300850040c0844401d1640210300b595480707460801c165a00e8a2000c0d0440c2c0c0d4034072882c4a658080a183c0c03000c141040a0305044030344054006c1105c05400c06c2e40703000d903a200e031f8200364504160440d07400100c907130288 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 544143498 1250 544142248 544142251
    0x714120726010920041d0c2b031706010e01020d0e193804060e040b060304060509251e051201050703050705040305211e04032117 57
    0x41e8000016140c045603201c070440502c0042d01c0e065401030340c007000325170f141901c1202021407076240c00010400240300e416441e45203c42006200c0c07144100d0590340441c280d028140c050f9100139400c10303001480d2030301501100e0000c449203002c6150000059142d40501c00c900f810b4001600204010703444010200d07240016224099003003c0c030254144801c4940240c0e11000d0301021701c000064140344681c2480c8450b00e000c031a00900840c4220741c170040202c2b001c44081c1c07400d51500b0802c0c0100440850b010f02001b00703040d900f01c000081040140103407a44428042c018540584250001482c0314280c140314200700d4000c1202e002004206c41001801c0028224101015042180b03954100040d4417041c01d000c2400c0e0750351182e04026206601d07100b40d50b4448030074201642480d00b141c07100e950b604180c0d681c0301d0310a2101c01010307143d006103106450f06400d403420f56050700d102044070025203802c20311084407011840210503003625040c80d44440300c0e203103643d034400d05c441241c407500e02c05020 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 544144748 1250 544143498 544143569
    0xa0203070b0a0605102604020a0e1b04031a0a0b060405040504060e060708041a010e150301091203060302030c06092b080a0c02090708010f06030209011107141207 71
    0x5844000042035180d44d9807001c3e10789041e407211138064406c1d040540c00299039071900800c40000e40100001070b42c4149009041e00c11706010345c031081d03031254544140c0301030580717203490802c8011400100300401002c05103820050b102e101d040d25150201c5101c00c7d10020820241c0c003910034002440ba908060f0711072540103004240c00300b4000301e0070b10b07d80e0500d002078a030440056200307000c1201303000700502030107074542130101c0c0d00c02d80b903140200400200ca00541050b10f0b00c40c40320310211031503409402904078150000b07500b000e0000c9254020b0001d0140348800c81c021b000d50f8107001c50328608241690443c0201030160080c082801240d40b50300c5e52014800b41d03403042e4004404010403440f40203003440300400c1c2c0300d09400381010f0041210000c0014400c404010803440148a901654a1544100c8000e070a0250712517120350010703222520f42201c955007500c03601000084140442c01c4021039808140c680b0301040701c500074542c1c3c48407014001d9541c402550700c1c581441d0003901200440006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 544145998 1250 544144748 544144751
    0x1801031103011e060503040510020d09050607121104150e1302070507030c1e0302040e070302090a0606180e0402091b120117071a0c010915150504020a0203070b0a 71
    0x351803803035a2809800c2a04480c0c26500d2903450b07980307403901e100011009008242080360640c50300b80d5907a0795803807046ca10030071003940100e9241c2035001c0d203410400301c0642c4042a031b0751619007481e00400f03100244054508103402c00d40e07265140455641118251081003000d07000c07c803401d80702507a0007541900c007942c102c800e444692482c6c22241c07001d041c03030714402e0024000c010718504000d18640350030b40111300c04104c0201d80004c0c0542007154401100d5050f600842d503c182020802d0030020345d64000380d0440e1100042000d0440e40e0b03401801518015103690702500e010850003407003004c40d40190440d03201c0d40303c0410701510b403032001d06502c80f81078400d0580c80700c1d0f0080c00d000c6640100c448000740600c041c0044c007007054400b100d0200c0c0086d031801440d01074502a401400d44000c400d860000650014128500c40401e402ca503094940003103146241516900000009000002c0a04a000d420881c040f4081c034140c0202c52024480398011820482d464440da50119030160001d100707036 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 544147248 1250 544145998 544146011
    0x90e061609120303020703080604060501050706051902070b090f0f030a050d0204120602030403020c12032704141009060f0e091f020d0e01090b0f09010f1a100e06180103 74
    0x2401040c003070b0a4014800c0d030f0007685581d102e1401034240c84d00600618402c5042032000e000076684001610311181d00180040f42c1901c03a010600020120b4120744011607000141d09020b129044030414090000001221202003542602e07544504403d401040303950030400c1641e0605104038007601290284007001403902c0c0e650207503450b071401240c0045480b55000320812003450b4061258100c540720903070340c4200301c3d144611501d4407071107458040e0318007a03010041c010a07610100e003003209031180a48100710700000072401002046040300c101803190011100410b0041a0b4000d1000b100c200d102c441614a051064012a18038010030f8903401d07200d880704011826455280340813070062a0000147d9640b10849018203485984001c2c00c0c09a04000d82000001c1c840c00c0416070040c059181400c0a44500d860b090140802d51a21504141001c8056540b03001d81900e020381c0100c11102d44052030300005042e00c03110007860040d030f4405c2c3c050000f4a8aa501c411010609003414580080c49 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 544148498 1250 544147248 544147259
    0x307080a110a060614040b1507050309121501082404020105160303050a06080c0a0b130905040303050708180a0308061203031801151208090609040c0305070801090e061609 75
    0x1d0042c00401a02c51640b1040200044440103982107880c400999042c00005203000110300080d000b000d0450600ca000105002441020300540752134880040c0200d4400028440721907645010001d8095014160400010380010002e040c81d040c0440c102c1041560720a24024028100010f0060b030600800308048441c2c003c1101c0c50308200d03403003620b0020b20360802004241c22140300c1d4201d400305501c410340014146e80c851a09804542c0d105248a68031208500ba1213400701065110241d0710342481309010405405800c01ca206500642e1266076590300d46c0e42006000305290b075500d480b40c02c10000440428840c101c89503106070041c183c00000301c000110713035141d60b0003281c84010700d42107520701c0c0352420f50030700480a40c00810081c010303a0314201000c0c00d812460b074140042152900040403441c94407240190b44011100403c104000e41f02c20703501801505044a04a00050488001041001e098450078003903100b038000401f8240c0c0c0b1005100d60040509044009000c0581e100040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 544149748 1250 544148498 544148503
    0x12105010c2a030203070605061908010501060e0402040b030a1a060403052808190e0406120b0f070c02060f2208070801180f0215030709080606030f0307080a11 70
    0x2001c61070350350340000c120491a04003090316080ca800d4508103400070054000700c0e6002003660315154002e17030005185e84404c40052000707200c03000b01da450354a40a0000550200640c003580c100d5800f03413075241241310b013202044100c1c401d9025200c000d203002d00100c2c09212003507124091043c46c801090341c449400000147e200d4101d42d1048600c1c0d0f10509441c203603080d10000c102c204101000f00100d8002c41603842130310a010702c80103a02c1c02c1140c410b003640c0013449040e0102061001800412038141c65641c03103d21030700b280e030060311402000740100d20044c600b582e44a10811032556036114520a03030707007008000c1c1e11001c0100c0301da8000388480042e41142c800d005588001a006041e400c1d860200c2e881c1c01c04d480c581c4068050b900d03004401481100540341310441603071080c5400d040b00f10510008940407504104040c0160012080100c003a800c00070b03080c02d40d180c03a411664160f03100382c02c040e038404a1015801c80e40d00b0602c10640000c5000018007000561400d0804400c2c006248035032 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 544150998 1250 544149748 544149761
    0x90a031502091807020a021017040b010e1302240405090a0c021002070215030712050f2a2223131802090901060f09060611030a0801210501 61
    0x300e15600107007907203441ca0241c049082019220300b1043d180c0c036046502a4440c1e0340410081d000380940054100070394070613003040404001082c0040303507508140c18040402c19003400740485042145021406095003100005804c0d540181030012445264808087c039246450030545402414440400d1555072869864850602c24900003155071000100a01e4180707421a03c06507288104101e0016840d01d04170b86003440e00c5140070542e251203100003229102e840d56461714289203040305000070300c84141c0c0308500a10441913103c240c0d4601080d40161440246000c1840b0748003000030381c03607030302c1a20720340b2b9100180e4500311032120703945031885e44d0004060300481b000004000c030588880e15103c5801c5c400f0b400004d46c1007100744a0721012058128601030082e01c1611403d00203074012209400c404043e081990b420621195920030796400b900143c0241400b00380c1e40741c0c102c400c40b00d001041daa410001a81d580005910b001401d207208240200414813501d0b0b10344444020910900030f08 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 544152248 1250 544150998 544151033
    0xb0a0e0f03210609090304060f1704050705010207052d0406030503030703090209010b0a0f080910060b03010801051b2b021c0c02030a1d030109021801060e040c05070305090a03 77
    0x9007941c0b410441d011500400203095a101d03503181414440c02c50f80002c192010342d00241400104c50b03404000644020304a00710626048031581c00b00020004049098001c1310401c0c4c0845038811b40b15000c1080c0001010812060110002c0c4010b004000462200341901d501900004900e5180c0d110b07981149d004407038040201e0303280e25076542141000049280103002e281d2142c0c1c1002950324000340802c3d03c051200c0c040003412008200001001d100e2000c4900b0004003c1110507900d0080302071a8100348038a008952801000440502000801d02420a40e148059182c070342040744e070f61a9681e00c40e03440c4981031039a03410421201c680740300410509a038600c1e0132001505c0a40700c10151400e00c1c900d40c045401c2031184481241e009007154620301500c2c0b03d03209210101d240441d004180000020b50300900b521210142400744516044c1030718980d945a00c2c1c50707502401404255500102c6c00d2000920400c40f00c00070a20860140002d9007006004050366996501c2da0607002c03a555444 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 544153498 1250 544152248 544152277
    0x2060c01092102070e040209040c08030327010212041205120703020702041a06030601030f02090604030f0b1303050a211a1305040f1e0b07030c1103070b0a0e0f03 71
    0xba0514801c018912070380d8080d4402006000e042092540c0300002c090300c000d001d56191400f02c2d00b0007200301c400304040e00311182102d480340b400c4403c0c1c148240c680000c1240038a0385800440c00b0704010300880d10514600c040c10212500c555489450106405441d80e003004410b0009110588025011500a40c600e80c2c003d80c80e440c2e00c2c0108401c5900000d002d02c0d00c181070711180985078130350409507640501d09080015a9103074551a03072000e84902230080340d000400090101c100040442402030b2103024407401c0219a031190466500d01d008640090040345050101c440020300c80c08801241e03c1000c880120000800c90320b840903101c1c90b90074003030007a01c0740c0601c080720f040c0707803040c2c00500e80003190512150409840700201300d545c0b8040901010095085500c2220187c03401000c884d40c840e10b40c5c0c40780d240c850340060040181d10403220004010030f020031500d98002060365181a0490610416a1142118035004040d1306a0040d101c0c060b00041d40000f200600207000380e54900c001 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 544154748 1250 544153498 544153523
    0xe010e010902070c0504020f0705010906090c0b0a08041209030f0b0417040b030112020402070b010b0c010c030204421107060305040305070809130509011a012a02060c0109 75
    0x156440120058000440603441404018080340024403d03070125103050700c0040e80d600540c800c1c0c08a0344900708010f0425070034540703c6020020300c1c0d40141c1795940510112207400e92603000d042030324440c209002002507901400f02e008030b04c1488207944905201d04020355415600d5175200318030b690390002030782d00f15400c900b0881840030782204454800c0118644514190078154100300501040c0207646041c0055461801152240d80c111403405400054a8045682d0713180400c0d01544803210200c501d500b066000f0081038064001d076030035990501050500b4210600c0c0720103840c0d4010340d030a000e0b100c2203c0d12089000d00c8000070070b405140d682c0d90441244002564074a4140c090744884100b600c2e00c02044082540101510784c90f9a10580d00b983e60192540044c43c001d8140f05a4141189480705001c074450b4154014450869031070210424000e840c801540d0602d0402e02d4140c1100c07039a0210010030540902c0356240a20051000b410120701c0703601a4211061500102d83d151110403 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 544155998 1250 544154748 544154759
    0x1120c0635150604061b060e01021b070509041e17041805010f0b0313050f0709060510030c091701090b0a0501080714010c060c0e0312040f120c120510060e01 69
    0x200b6151550380c2901d22500e043d10b0040028001c01d21600b044812588030345000040142c00c7d08940c6040f030411000750748a4101c400350440401148044c0300d0503200b50180010b440c20300d40700c5503104a801c0b04108500d40c2607540346442e48070b0400000c8682c20b0301d024001005003404005400070700550030030300c2c80b500c15921840d400c864068005800002559400700048007100d01100d030f00c241d402d102c188080e0038030701e0002d18006a14003540e00d0b41c000c03040081806615540004211041100d032880182d6900c20150200d903154000d001c0055191700080c01800c02c180d00504941240100001d00300b010390300e400c007099606590b00b0b90140e860300700411500400308142c41c040c0a40104011800d00c1680001c0c002c80040040103040c00d4944440b0f040441c0030b004004900311000c0c05035078001200d200400390503809030003040f05003500031b003020509901031603d10448c00c2e0710000340c0c100241041c2c0305880d4000c15007802c03249032181d04040c4140701000e0003100c000703022445128040e035042c030 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 544157248 1250 544155998 544156021
    0x5060709050a090203010e06040903090312020d03050a0c0f0e24070c3f020306090601030c0603021c050a0204050d050a11010f0c0b060604050303130e01120c0635 71
    0x20f5128110312030040c40144940c0c071302e16034150740040040b1000030700c1508030f24040c1c90402e400d44c1301400da40c2500c0625500c2c81e80200d041455040d241d54100700300c0d42d80343c1c80703541140c42104840000a07603880100c0300380303402001e03203603000c3c48004d01c0003040001c00740c90428211600210b461200c14085074082c100095150030402901030801a40070f0080844401c035807100f031540e5407840c1c80e810221000c0740c0ca1302e0004841d2610783c02030182c0d80c01d4a0312604481d928102840110b4502c21950310004420f48640b0075500781c46111107503403c00701d207410003100c040c1101400902009608000c009080e44c0c0307101da0103200d603200c1c00241c4441c1303426041050011b00000c9000341484140e03981160b6080c0c0c03003903102c40004c1e40144011115200ca40108207140200e8010300e41511000411300700910103d06450b0880303000a95282250703882e141c6240050109410003001e80340c1c041005c3c884280508142070003e05440e4800030f0b0189900488100b2040c074410784042959650b041c0406000503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 544158498 1250 544157248 544157269
    0xa060b04120c080316060b04021314010206010f0501230d1b0201050903031b0711030f010b031b0904140c100c020907030605030615011103030405011508010903140f070506070905 78
    0x99010394104140318903076110000c17004030000c0c10940d54100c501d01d5550750351b055a182c0800c900ea800d69464407100a060f40812800d1224003612800c000018202507180320782081d0f95041c3e49081422801691030103400e40522109510034400b4444c000f00c100d428800e442e00c64260708503d030b46940850001034211075006e80769007800d8204000f081040720741c23442c801c01035141500409aa0b2100303801c2c09002c030b5118410165040c0103911424001c0070b0705400c10021b8103012000c2d1380e190a4000603140141818810355600800c15400250124111072042910944a04150749800c01c9080c00144410301e40204400480c0e03e0504240550604845035580900181010402a401c10b00007a41c0d81a00a020708540c0006412900142e44075940c40d156111101c030441e502c0781000d28105010b8035042c200c1420303c00000b940050403c40500603006c03800d416407202d20544040ca0807002c03280e40700c5001840280400c02801c40055001c1188134890300d4241d0f111681d0030700b05010011785196 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 544159748 1250 544158498 544158509
    0xd050c0112020a0e0d02130c1e030506031c110d030501360f2403020114160308250e040f090309050d03030b090f040203151302090a060b04120c 63
    0x414480d0b880299000905005004c1041310b0020010080744002540c01000e480d01e000d9203810b000d6509000e6802101598544132100382a5150300c40c0218102c085440458100da0b0550107101410407514140d0345203c0015024a0a030000091400d8668039010000340b030440020b607200010408028552030380c0c0a00d0704403a180c4100600d00c0c803c074055400007040b1007808155030f00c0c0050310804007680244018820300380154240304800e180035040110f01c1c40240d011070101e030075040f40360b140f02c021242403203004042e0310100081c0d034074110307031003513000385803111415941011070100c0b01d40c01d002140c110100e9854180018564042c40151070542c142a121903040001000c0000d800c030441e982660f405681c0242ca952203400c2c02c0703000c2d0499035003040c0c01190210510649080044259200ea4000e0701101d800303943d04a00c8945440381210711184241c0c81030201c800501d030162400390009032902c0c0200c1c55689591440485910980c4030340d0018035003807501d0082002e10b8401c0c01c001c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 544160998 1250 544159748 544159751
    0x515040f0b37081023030d050406090e04080708030c0c010c0807051206030703080a081501140403080306010e0a060201090c08061b03041b03080d0e0105160e030703020d050c0112 78
    0x741c21190300151081118941820702490b10f0006809000c3d04000c07800810700d082c0c9a964800801c2050510105407040241c0a8000c1c0400c241580e409881110200c6085641340e44038186000d040d11480791010380100e0350382504009000c0400d1852008d5401080c0301c0c0b40b01983d074020749112a08444600e258103080c01702500030084d085030041c00740c8a40580500440d01d1a68802000905001c40c3c1d0b00001e01c00403001c60309004031540009500e1150200000483e00240c40800640d2403140e00804a81988800c10090001482d10b102954006006050081c503507440300000452443d855000940140c4d51030400800740002d40400800800c152000b4156504152038003000405c96400d42c00040d040020103c0d04000c0c092261060344036003e903201000b141c5074680751007594004591420b000c1d0500028440000c0188126805112440e115144911012805480080d072020702560f0600400c403001000d602e410b01d02e064250f2140010b000742120b9036002600520f445803100035410b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 544162248 1250 544160998 544161067
    0x20102041d190b030d1206050a08010e0f06010f15021e06060a050418030c020a0305030f0a0e01020f0d031d0604050a02040e03212701051006031103010515040f0b 71
    0x1381c40110356180a10711605e0654900d4644211007000b400c2c1540c042504117500c1100001e210106601403114074409074103840c1d050340da070402c3c40d030307154000e020328402d8440d0b6030800c1001d6034200c03072401c42c800800d00586900301d80580040d0100b84208000c010079411010030807040c0d15142c151580500300c222001c018840740e13402d10030450102d020b0000c05215901070070105660340d0441041c010359011080726038481380d203400e161094028005a0b008a14510f50030040c56001003020411041d07400001c101d4010307100c0d030403030140201074401005030414105081c1e1041c0180801d61195000d40f000b04001c21192050108490b5041800ca0041e08140503030591a085440c44440c114810700e66101262280315210070201c48a02d50215486a20440141e42d82c0f4107400103407091152500c801010741d660217095040e0b6501c00c400ba0280001000181710f103141015246d0140ca8070412668100f640340d5070b05c1c5901e98542e40000042d001c0100300050403110180c20581c440022007c2d80d05603 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 544163498 1250 544162248 544162271
    0x60e01030908090603060d020621010617150a05040f2702030a060c1209060b0f0301110405010513050d230d05030a020d0b0a14150a0c03050703020102041d19 69
    0x40c1d0281c0c0103c01e12406001002c1005070f66550f1040c0e005035001420784d9907442020254210703081c20f80310700b5084860f0010000488a02800a403040019101c460520075039030215014482000c80d40529405a05840049070940710b5114050041703150741000162200088080545009004100e0548a81582405005031030101c3e60880195004101091001045000381d500c220054906200f051418034038100b80312054003d07103a1602c05407001849400104141401d0710180c002d07403084550100420080d5510071070051244106038000c03007003115140d200184002c0035880044d07508040c2d0301c070705100003c003603480c005c90249402c0044c801c1c03280e080000b40590200804000324a64081a540c0030454240c0003005d00010007840000c0d407584454001250403030343d80800f401200006941c1c0740d4020700c0d40071610580d4164487c031301ea0300103c0c2d8084400d5404070b5811801c5540034000040c3e151440e4412940b01d60040c0550400c5103448910781e8050405006c00d454a40d0811003070100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 544164748 1250 544163498 544163513
    0x150f061215051003021c05041406060f0f060705010f1e1a010507060f150923061009030c12121d040b0d0f050d1b030203030f1902030907060e010309 65
    0x85940c00c0d1001d020406407a0f0f0190002c0c0161210258404180f040c5107120184590001f8850b5105407406021390039000741d8640c1c1c803c0c0c2214915044a151100c081492801202d40c0804c0c000c0240154a402e00c1551150b080d68401241182e0303064a0f0840a45204080121101d010066010030060140400e00c4d1140d5440c090800b00e052010009482d401d00c50320b80c010090101c13640c4e070180207034403070108201c6040a02e44101c203c100c1c40e03c62240e80c03110152300344e1080390b0207409410f080e50304c80804010110480081c00010700c0f10342000000003824007100780004040268480075010700364240074607000d426010315010005000b25070408115071481c07a92000d001134400040c8859080041402ca88040502400085507102a83e0401000060304240c809460b550f40e24410214a5641c0058074440d40040143c1c2007480000c40102d85c001040d035003d001c50760301c0b840300d5198000100490b0320955010200d0b4022000500110713420040280d84482d080ca010040c004542c1c48020 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 544165998 1250 544164748 544164791
    0x20901061e030c09030602070b0601020c0f03070b0d141e0601050403031b051006030f060608060f040f21050316050c0309010c0804150815100c0605040501150f0612 72
    0x81c01c0c5555107030f804226030b1041100e40003031640302504550b94260741c14032251030b140c116030b80c6005100710307540d1118504240050b14107000d4007800810200342440c03040c1801c4e82121440340d40e295540ca00005e0b0010b42c085002d4024a40e002094500c1480c109003443e200b07000030842d1341444010401000000c3e4000002032508001194690a028092074090f080001c1182081d49480c10000040180b04d03500202190b030034403074039040001c4e075a0b80000750703252002107810411550415000901040c807205800f480c86201d40402518120758000d0001595030400e105070010b6030120402c0200c4c1d00e100168403080c00141032036420400550741a9a40344181e040250411404040060030081c0000981c2c0203844c90103901405040c2980300245030600c11144444041d650f04041011400c0641b540040403010703680d03079400e000003034031010083d10000e0401c540c036650303d02140c51215598100780016001c50250418120310b400c0c0c0080900c2c1c01d8258100703255243c0400f406a040c581107004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 544167248 1250 544165998 544166057
    0xb09010e06070e1c17090a050d0b240613050103150302030d11070902030f090706080708040303110724060e160f021219030f14180304050d060902090106 67
    0x780c0540000035507800540400c0c2c4e00040c20000406107443c440085040640844181a2038000c1443d0341d550420200000002000d40032140c4030b40130030100b05010000360342d003445032001c4140d410400408161a41d0040c0001d5082e0454258184025070749801402c24208400750341c8010305083d600020340701c4003a01007001c00d02454800540b1600018800440100001d2208546070702d082d0b07003a01580a421102602140141007001c240b1500034404a4004d40090f92817449a80c0c8540c0c06500809504845002c1d5000501c605000900c8a540808490b10b9102c52510a600d01446001c15248642c21201440c50f4500400041c903001101e10303d49007204c0c2c9421120a498007174242d0605900f1000c0d00544100010300200380014510310ba0390a220941c1d00f0028060380c10800e508481c801800c0e1510382070414049007040c402c141c00c451451041c001a01c0c5416513500c0000d048201d0781c48100d4070307946ca421485080d4601441060f004007110b040c9032050303900d002e04c0c00b40401045000e1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 544168498 1250 544167248 544167259
    0x1503020310050f0d150501030b06060705060106030b1201050709032105090d0f0231020301081e250e130b040305210103031d01050c071a0904090b09010e06070e 70
    0x80300c1c15940e0900120790854005c88801c014aa400d40c41e10094902400103960050210000c1000360400104843c6c460360004007820b8140d01f80700088002d080c0300380c25641d00c11074080a00000303130020300ca1280968519201e41340300c0c0e460745c9411203842c82d01c414a043c0c01c1c0d003418004451b060300b1408aa29206045841c0c1644c50a035140010301ca0040b004040e400c890080d10074007411003600c0c039844200e00420410360300c041c41c0c01440c50607840240205001038002c2c1803103400d81c0f644901422101c0b5000070984c0c1250002c45612036008001c4400b1404100741c26200b0804129813401030354116100540700c08411025440740c840419014100408200c03000901c03c814014102003414091010b0728042c2a650b0760741801051003500528283c0180c0c2d034605500390541c000c071700720b0703443c0703020500601441c0786841201c031054059280040c118060400c0312000c42c2c2e54a00c5146160303031082e14804101e050040e0200d0031a001640745507156809070061102464028940e019807101c1200c0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 544169748 1250 544168498 544168519
    0x60506040212010f06080906061e040e010c1d03010504050a200a03150c020708060106030c030209100504031b14040209010201020d0e060610020a0807230a050601150302031005 77
    0x119000303100703095a4074142c5406000110300308800101300c0e4102c030141c0d610010b840c0c03980301075151918804d80e1003551099044e07221400610350010112104c003401440040d00900d0340402d907080da80000040000945a0310b60080c404012209112a0701010b4000700051b181c540e03501d6580f400c508001400034081110303c2c0c00807110a08680030880000b0700b90105161f528a4440403661001090051003401d0040d800155440010359030700301c0b03081600509080c3d00e0000181e0040400004601c10903408100c0c0340c55070384542d80340040d078415a5403160f5480b4070b141042100c40803190140204004903180c1004440050700da01c0f02e5813881210700503642c1908000503402072103000c1091413080d04001c03601201001c0814603d100d41410744200c042c8902823181281c6520203800010300a00080c001d85020543c2030012058140b000e8002e4035801030344d0240715280044a000844050323002000520400004440072154454a420190b0850400c00000c0043c50244e000311805101d6025 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 544170998 1250 544169748 544169761
    0x181f05040c0b0706020703030e0606010e040e0f060c091008070507060b06070b130b070c08032205070e01030303111c09020a230a080a0f0308040302031b0f060604180605 74
    0x4254900070030600d404180e0302c3c070880c6010703c042c4d0425182070340800d24001c0321000780000412107a20440e0160f4071350350540143c03420040205040103c200b1144140140c2a03d102c80802c805401510380c400d0f12510362055408200311842c2e40028882004885c9003804421900a0251036210b81d01c90740114081009601103400c3d8080c0d50703009000e0031032100901481c610f680c4120403040f80195000712248e56862810764107120094001420040108002001d10040e8140c0425060080341100f0b2000c036103480381854030003103800456a1001200c010001c164052042c1c15443e001c031268541030403420914010240f03044102c924070382d900c4240308c0c0215035139031800340041d0a0103c1c100c4900401606903050320301c00000403500032000c0e0180131840d0040010b030015483d41c4200e1590002c0d450355812260750b540600101d09602c0240309074600c036420b00074912140071006005040c01204420040e281c120043c018500030352400321015002c2c031824103400c0c460b0b9004840400c81d500d640 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 544172248 1250 544170998 544171013
    0x130519050a1203020a0212040501020304030303050a060902030711070f050112021b0102030903180d02090c0c030c0102211614131502071e0518040615030605181f0504 73
    0x75140200161484041619040c0d09640505800d20542e400c8409201c44981111280d1241d80220703030250b4014041080040d20030f82107143c2c4004800e2020801968a0344180181d070415900b00011030130981c4004800441000780c0740003000600300d180502480c042c00a043d02d0560342108e869180c00141c0806c0d44265a10200007402c1400c008540d039180164600d40c0301c0d00203101030200d50040301c50480d03552504034010b01107603800414442c0261510b0105d40225480301481c0c01071030005200e4100c50400a20141401d0108100c2c2d81124201410910703e180c58010300350702c01074204541406141f035100039551f03501e1000c030b440b030760381c80201084650f400344842d48040001d1407262403224040e83e010520304122100c50741c0e00e00d000072040071003000d145854007566401940501d0303926000c4004080d0107801c14025280010303031034280f001c41c00703680c5a99081a00c1968461061100d45000b0404036082c000711000030300607521100c000c050804000c0700d488021591103c2c045800d00208 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 544173498 1250 544172248 544172263
    0x2010b03161d010f211b0f0506191107260105070903050d0302091c060b030c100e0904020f0904060b0f0a0b121b040e04050613051905 59
    0x201120304503000586244610312140c02107141032164080c414510103012501c543c1a168a40814800c45041503580d0b081040302d00c10800800801c810608041580a2a160410b4062a0120031586e0602c124410f4900d49544018002c2c2e504002c20703c48003225060114541d07003140303001c0004986511030070380341140a401c02c07145030742c0c2142e00f03184969001070400505841c2c1c000900103542c4e044029110100c5a2001401541291741199076440c03103035008000d035003001000b207100c20011440070701654000840480341183d56000301c69a502e401c101001d074170b9400700d82c10890451559030041c001d29034092194081e80000300480c0440d596032424003e002c2e0003a010200510b418103040028101500701c943c010038110000314690b083c089213036815184110885840d091004140940d0110002c04000c02c00e5501c1c008040c0e10344943c0000c200a00c00d45039100c041d400c281c1807190030044040d1886c004003130600d00010000b00045070b0820202030006020701e9201907418801e0074547d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 544174748 1250 544173498 544173521
    0x10c05010f0e010509060105030c030727020d0902040e01021e030901060b03040f030306050607021f02010e12180d0f080703030b0310051509010605030117010b120a1e0804150201 78
    0x81011001c010b0805511291003902840119103241e60386109040d161804090502d0b01508400011306c0341e0490030324142d00c11601d103074402c203c40c0e011241000c1240c110900054140e038480701c080c025464a400380c00800049030b0021443c0c0301028030800f0080c0c6401c04035078540107001c030000300021820742c05240180080c02c140e603920300d0f0a150480c004c800d14003003200400d151010100309400c000703041c1c0314003c0d40601b0050320004010f18191002080c0c0c0901c000f10f6403a412644803540040c0720140d82841c000b10007546030301800081c59070240503072000d07501a503c003800301404507030010301d40030b200f9800002c1e20340d0310030003420110084c049242a590300b5124905500f014034040390300c00d80c481c118a02c80302c2440040101084281c0c1020b20480b400030700288014405401e1140049050051304070001803804000000700321310240e62400c99100350450359034201480071181e000285080300e021425901201c950700c20344940039a0141c05144602c2c80d420400301350003540078004186 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 544175998 1250 544174748 544174751
    0x15040b030a02060a0905130c08070309050a050a03020f0c010806030717070b04080706030b0301092001020a06060b0310050118150309060207201008011a120c0a031415010c05010f 78
    0xe1a0340c0300a030140310f146c0b181c03130700a07144140c05030766044951140c0f944022040e82c0303c118a031a041001c801400c50300405440501403401c1920000d1402c11112f21041c3c40b98003d0f085c1804240c4040e410001c81200b058180076904080200315900400c2e540240c070810500e0fa0140170f141c9a41a00e459001e40004066860010300803a40240010300c103011200c40f50380c1441700840420a050903943d10860041c01440601422180300c4011205203082c0d020600c11141d0142c0300f0f0300c410003500e205900041c02c50b940001032200b0002ca817405500130b00b1080c01c003070703008043e940c0022090060030302c1071003400e100b50181401040d200380c0001c100150000e01c1951151041e0070041e09a6090790507c0b80c40040b0600003c0e114205040c20314802c40454690088a0f803038545800407020081e012580307241d0040040442510ba440b101c0d40c010803040007a01d8a5001c0c801d000380840b00028840b02e19442c83c04100071b442400d51010600482080c03074045100c0016181031030140c0340c018201841c86 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 544177248 1250 544175998 544176007
    0xf010c1511180411071e03050f180a08070e0f061f021501060318150212181912050c0c030d02101107031e0c0f08040303080f15040b030a0206 62
    0x18a403070705000e10030082c112800c10800400484c664241c0c0b14042004201c0c40d0181c00d0041c0c0042113142d100785a1307000c0e0a0180c0b5180c10240e810045500c070348a031404011b40b141c07030b280c1c0d1030404003452405403080500602c009824180340000e11a00201201c110403484e01c00101c0a8440c8508880ca14606250014a9803059400070751220000840480c00712480000001c8161081c02550003090b50a50180700e042c10b151150121000c007511101d100366000c0140868806440090b030703201e00d0b600c513440a0040440303a85281000d1401c0c02556040701542a600007090391100404410192030034517540d40d41d1545240c0e41021101c080040d854060080c08440d5244c0101b9103205460302043d0801c104544149441070034000c5580241c001840d4008036030704c00c03040b1240c170102e248150521b043c040840e603403a03072004031400b1400c079039607100400d08004168200020b180c20a0008030a0141d52500020000d0400140c4459502c10340d1940c0c40015207407800c3c810b460926030007402107640c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 544178498 1250 544177248 544177267
    0x15090117010e010615180506031510030207020627090c0a09080a0c050411040b130303080a05071403061203040906150f02030306041d2a0f010c1511 65
    0x200d1008414a0480e542410b01d405035010040c441e400a0742c00390158043c0900a40001302d8101d13074209006004808401e201294a903199005948603041c4070414184030344a450912006040c070020b43e500b03041c01808000016035601c07042c0d441344034070200080a14210441410f21001c00045102e800003a0ba409102903096003000038008217401d03881300c008071552803d9840d510700003a20068290b000b140428003003850b2507008016006000d111050a00e51500d28200c41640241e09007211005030141c10802c064100c400a03900c140b00c031a040000d0b1820240c040d00c0c509603200035a03003008000002130030341da40e070030700d5031042d042c1007002c036900c60b621082000b000b0700c818020710096246003040b4007404da110302c0d0904d00c156115805503043d0348443c41840040d0600545050034601203101c2151034176020041107403a40414414658420790400101d1a007040319171540c0e0140343c42200c036040701d0342c01c19034141500e03074426400741805124003c608010030a1441030b10031101d000401031364 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 544179748 1250 544178498 544178519
    0x30f02070f0b0606090901140a0f0f030203010b12060f180f07140406060f050304050a0b0a1a0301151a04090507090609080705010801060302090a0905010914010905060d0803150901 79
    0x201d4440e11184403580c41c1c00e4104282400340019003988200c0c050014000d0006420030a8080d48002d040d55843c681c45420b21500007116030814849010080410001c3d85424000c8600076101600c148030b501d0000403545031100801400303c0150a0404045803191020f1166003188101c1002960850b0035015115600c41189106403201000f40f800c6084030b6241910070300381114483e0700c9554414281c030405a50b143c0009106445070b005241c01d440c0411101c140c0280700b1101c03140009115400c51701c0015248010a060500030b82c9040c00c4804003011407030b2108140c40541405820407804503041080351b2085800c2085d02d5030400e800d200d88039401c614504103803840381d2540503099864101095a400941c0b241600140c0f030480100801c40c06a030080000610141c12044c07103075107c0128200361282a0701050305281c0e105903640c40700581d07151003409400c01d030f031041c00b940c2006ea000800d19003e128025007292800804650802a10910503118480c0517200020b5982d642d0340451 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 544180998 1250 544179748 544179773
    0xc07080412111504240f08091005161101110901050708070f03050405102c190e1b070f06020c0313030f060b1f050307030b0a18060501230a030f0207 65
    0x80c5c407005980071010400c20039049080d540b0005544207042c04150560854070000c01402e45483d501900c0524450540280292407080c1e0f04554442c02040141c1002440740480c42988490b40c1d243c088114020085c234821581050802d00e04030340c541c0c1d42c2e41042c0c8098480c0e981e00802c120984034a02c0200741d000320180c804c035242165000e4100768084070680d1800048910404480300d285c810ba00e0f2420046800907a0b00344c05070070b0450982107140311410b0254180c01c81440d281d07240080080356902c80c0c3d6210700740d070b241071411801d16840d0364800400c441079031030003403078950086025031247c40108140c58404002ca039002040564074100440308241c400760075103544d4141410841c540c10a00c0c400c4410ba483d5030b4600e2035101d18910112003642010b003c8504044d00c0f80b00e14445580c0f40c031010b101a14a08000702c6076901084c41110448800351b10490500005403c3c03c110300f0b01c81c010051070b010032094029916512000304034000c04211a445408510120f4040140000102c903a03 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 544182248 1250 544180998 544181009
    0xc03060e011d0c040b0d0b01060c030e0409050c031204030c140312031f0b0405090f220813080c012307120e18090c040e0111071a0c07080412111504 65
    0x5c01405420700c080c00005c90b05004080c0400c0007482c0100440352107480185640d5019217071806900d210b10001030165000b40d00d0907100e0780d009842c40b1456140c00d1200480d022141d2030f9052400349150707214226640e0511804501c5a6012220340c0319440070f12071500828145003201e6034074944008110a4a102c404803420b00d10610321012641c00504000c03942554170052030344400303a580003956400802c0080c207142034003c040f0203442c4040c208815800344184a60b00f0a03481e07546e58101c44452140d40d9011a00342e0381311030003008250b60000c264075000c1a81608149100080b002e400b4110311490354000e04c05d003000207050100c540d004422155000044030303401881c4040e950146010001a580d481c0a030300888101102c03850b20342e011100c0400c201001095031203030f4480030040758124100940300307a41142c0c8490050181820b00643c0500540c007220308107c0b0680f0380114034003480c090031078621070040a1601780110302c1d03403103407004800502c4100c01890036065041c50b504148a003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 544183498 1250 544182248 544182251
    0x405030c0109261804020915190e0402040f0612020408151807080d031a0d0503221203121404060204060912150209130504080301050109060c0c03060e011d0c04 70
    0x20710640030f43d2008031844c6a160030b40131010300d030300182088029441000c000b03610646d0030440c60503001d400c901414560441c4125401c8003000a0f0340a82034126101c0701600c40e83c0f04100c02e000d001c580540c11801c0d10501c0c039110782810078800d9032900a00c2150081e110a210302ca02c0803a542c0704040200d4403c8a440c1405007240d60598031483d03584010740120768458114501ca03d60b910301c2030f40119050f01040390b403e07080e410480c0c040b603a0098024010785e81c0d40c0002820f40214802e106454030a4510341459a03141450003079080c00c040b03003c18004080260401407500c1251980d00402c400c1c407003a084003e40da08180c07402c54020f500c580700348008540c1c15403001640f4521004200c101d10b82000b07a0a003000000c4052000130351100101c0380d4452980305500c0100d40c0c65100d1039110350b00c86c94009680c2d50500001400384103156000c0b40810804030784030700015858070b46403000c984d030011001c100441d00c8820503000d48451785040e00038422140220000000029042e0743c1c4c1803013642e0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 544184748 1250 544183498 544183553
    0x207120e011701270e0a110303130e10090c080109050a0605030c0d02010507170d1104120f111c140613030e0a05040203040602090a0902030601020a06050405030c0109 73
    0x666032102d03031042c5000c02e4950400100300c816402c0341d403144001a1103661140030724115a043d800c075600c80c03030401c100794000c0c4080000c03c01c1c0d22a00b40a00201200114203104690024050ba003c140c010501e4400c10600030900c4882c5003803a08000c1d21090030140501442084010b220000906c01c42d05564204000306800204600c0780d10305540006d00900001d003100810711502d034500d80d408078108101000b242d400f080101146100020441c00b145560382d111852030425507410300801489284c00b000200400d2180c1c0d044000a2580201446601c0410b41811840040c05000341c40d00b04080703081c1e40031103c00f180c00603100c051050074258035650480782d215680d038000303c0f0f84100404d080d040300c4020a00803098125060402811741d0b16440d11240420705a0308160f4003100c88540205141e0183e10300400384d080a841811421821490b000000075950303507445c40050020ba0741c0d4404503050010030300480e0400800c81d002400150554503005c00c03040850390340e001d00f0760360040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 544185998 1250 544184748 544184777
    0x2160b0f1312031710120203151807050a150e030c040c03021b0601060f120f1a090f04020a18091205030711070f06050a0c230d0c080a03021c020712 65
    0x1030007940100817081100c19250300b00440d50000c01c4224000f42d074036200380100986404c611001c000d21441e9001c1075000b07415174204489141101c0c0b034010390310810345249c06211482000124440d40d100c41d207000c0700208030250200381040c0b07510f00a15042410860000621a015001494000308450519000000407103400352a0102801084000348201010721360292280c144511503850195001541d8038146456204903402a88000f054404880502203e442c01c11451a4081c0000c2d01c4401c0c41e150603400192a50007a02a03000c10042600f100310703102e9925440294034642c0040070b0102c600f0580ea01030440e4004651140009021100040201c1170100e580c3d0120f800fa810210081410070768199030703e8005100035820058a029100040f611020444480040e2203040701310f00700060b110982814180035801c820310120360001800034860304111034258415140042c0ca03543d60003002ca25800384511410306d01400400c98070248005c02d400c580e510f14540e102ca184641009 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 544187248 1250 544185998 544186037
    0x918071403011809080c0114010e0106050a020a12050c1009060e030403110607030e03030a03140c07030e040903170903030901230420040218030c0102160b0f131203 72
    0x900030711000241c8074100f0401c1107015040744440601c074a503802d0801c10b1200d402c0d401c4900c03030385095030461503140c010400e4088801c04035000d401c040c50a41d10304800d072400690740300340d0311600030095030780d00c15200c070000c0c4100284d45100149905131500086900391f0708018210b90202902c0d514602004d0800d40e007030001c11101260f911881c5070050303c0c1d040d01049400c1d0440001a014084941144603499a00340010070304894240c60005052990710210241c0c01401400e051406504002d1880829040038090510410417540854207418901d01110b80d000706011580a83c5214014850b81c0d00d00440a544a09040c00082014107a9031441941c148540e20000300180c9042000c00c02203070106d0034540d03208032545040341110080c5030100d000c03071740030041c40e00b02c0c42e40c0c045a0005a140030700821303174803000900c018681c5901100d11042c0405161103401044040011903084c10151030050301c0151911300d84075a5411341d2210141e111b201c1c0c0d2001140041c840300d1080c12115642d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 544188498 1250 544187248 544187251
    0xa0b0f0102120c01090230010b130f0b0402030c0c010b010c02010804060b0d17070c0b0c070e0901060b070807050c0109080d0e030313060905091602060f06060918071403 74
    0x581c01014a52000e05105080b030344a0403e00c00255211106480540c503071083c0071210f101e103004020b182030080d0300e552100400c2c0342d40700c039041d0741441c81500aa0361005801200380042c80000681e210124440c2801040d100d5600d50700107001004014480c0c3c0a2401b814200a042c4001e0050350910401140d03000c82040009022440d40c101080100e00d03142c0c4040c88214014081c14400c1c95180c481d4041101120b071000001400014400e0801411222040c000c00d07844004034145680340894540381c041600500410901030301c000b03074400809411620050030121a21a03890500d814045010750000400340c3d02c4c5d114180340340708071b0f510400142c000c0b03030320032005040e0b00c44020300112030340a0301c00c12041c4d040c4030600c080e000c081035121501c401040e003500c0e0039030b01c64503210034000315000040100908498081d0304510741030f00450003641c000075007070804000369591000552a4001c802c0f005802c4070b10720350505115445140640d024841d552107030002c440c0e00e0704441079144030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 544189748 1250 544188498 544188529
    0x3170703020c0604240f0b030f060c12091e2a01021c03060302060d0e0f060c07021c0803090c010e1014030a1e05070311042105070f0e0a0b 61
    0x40000007130003041109101d28010100907209003080078503071484206803000958083c1400740e07500c19508841c60100089150b411041e0068840c0b85411800881e150040300b00701c6605d10b0030680000e1020070207102c400031400b136880301c0c0b020092001c1d143c81e60b00c2214108640383d020b19040c0c00800da4502c034440500f0820143e00428034108052070480c41010f41e90350030410316841c3d00b80800180e8560000d030840d04140c0100048a500c11104c6500d13004941111404541054060244120304107007191a420b8041e01c080380d101c004c40c0d1240b1a4907104000180c004040441440751040002c0f45c00916000b00b41d0310240c010f1000810040321812800d1089c02107240c0b485500c0c00d150170340d0007075a4001ca010000040f400f2014000703441c490082084030114a690b0000c00003441e416200b04507020880e1340356142002d080510050304200d00805091141080007607400c10000e003004210050440f091840000c07540c3c5407060b2a11a40c01d503100c0d407030641490f031444914140300059406180 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 544190998 1250 544189748 544189753
    0x100909050303040615081906050112081905040506030403030c02070608090d270609060206010b030606040509062101090309050301020a0206010e132033160b010303170703020c 77
    0x1100c0b640c03144005c1c00c400c0c0281c2140c80b0000030000e0280c805010000915450385176001c0000483d141000844605070404606200080010000301d101001911000fa4201c181c1e4910900102e41c26901e50049521840c1c0c0302e0320000401c401c0507416003040c00c44078280c0d000c03914900c1d210302c0d00303585103130007225900f290f544040d010003585441201600070011321044601e658501c0804400640c08081e0490004540195420001190304000b0180140022542d1500314204100080c07a80c1c4260300c03609102e000c0b410003095040da0740540c07007030503124100da1144006000c4040c1c0c2e0b0207880c0b0850240c0120300c00d60000919403c041c02168000c1c0300790b5018210070303070074a890f402c2074140180c4414000300c101044203002a00305090b964505201d075015410301c0e900074041020303078545040f81c4224441c5802543c2c150480d49640404403e09010300d95890781a10030001c03079010305091000d04000410307400003007415040503c00441e00b111003500107042d5145441503069101e8502c407480641d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 544192248 1250 544190998 544191001
    0x5040c0f05220305030309030a09060e13020306010302130305010c03060801020c070303110703060f0203010f050d050a020405070c0605100602010b03030705190204021b0f010c020c03060109051005030a0b100909050303 95
    0x40c600d9100e00b000e80186032040b0b80031544a44480d480c1d600121807981c40d41e840015011070765034010014000500c09031900040100d001000301d40c203401d1400c0030814117a00030001c900c0301e03030290b0141c4a11f01e8014540c03100143d6603050070341c0a004940c80741c40210745000700c00b19004806008998201084900402800e0301e565030440e24000d00304204101409a8407000c030002e021070141664000e0903080168076541041c400c020302503c44d80c410f5124161240306d5600050b00861464205601100c0005055507905810b4540e0740a0000c01008240781008200e1101c0030542154181d500c40d0b1300805c0100c0d0404240340e501d205441d0050403e60080301c65000c200c0801002e00000e520103003015040034001c5000c0c0151420f9a07036000ba0f1354200200380010032070240306282e1309400d00d100603e40722061001190300c0f19418040c0b210b0282e1507100040c0b1107400c040d0b46c500245005421950300040d913081981d0070b4807040d60032501110112038001140e0821f4019900c1d805d40040185295 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 544193498 1250 544192248 544192267
    0x304330b030d0c0f230309010e100c381911070b06031005011202030607140f03041b08060a06091401060e210307060e0607140f0403150605040c0f05 65
    0x807000942002c80301050040800110500100b08400e183c485c0c1e20011522803c80034005040c0d01910700e06540120002d005080e0a10360001403c0c9405401001d0068103084401200a403c0c02464081c03014030054400f038284142c045221522400c00f090841d8000c5c1000c07170103081580c0d2204080054588240008008980703007248007500b2072001011610303d480300154040585201364000d48402110700360320410350405000c51a44980b840c5044440d03601c98000642e07441c010880f158541040110018003000642e02c0c0c2c0403a824809605010b4640d80c1d400d509517900e10482e0b440e01c66a092000009a25047d170194405804240883c100305a003004012030740d9481c46070110341d100354000d411006000b101710f40c903620000c211000d15078801d0307103007002419a0b10585003140741d0390128080203040c55100200310b090082c0506800d0f9100903100c0814014051303908050180d034100918541c0e4600140d004034100c3d88251003d1150920f588400d9400901d04071a00c00400e0082000d00c2e42c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 544194748 1250 544193498 544193513
    0x90608120c0313090501170105060616030c050703060209130b0f060d0213080601080118020906060f120f0709090219032408060709080703110103020304330b030d0c 72
    0x812000c00c82140d041403440d4840d002d011a0607071081813031658070350060101483c001e00311841525550000d00440c1001000701d08140b00319495480c08610f400c10000800d48180a035108441c2c000d421601142d03164280301c0000e50048496078869450141102d00c041c819000b08114000010202c56000410200f40085079100080e6402e443e81c0c00c00484980100b102c60500c082c0215100601241d818181501d00315810800800380110f440304040f40181d541040e8560301c0003040d00c03525207824442c990b40e2107034003c240400019040034401c1020400422040c6441240d95a61f4072100d10b0752840e40004a00c03404c40494120340c115926100094040c0e0040740700741e0040e4407004040b403501c8804d54080c1c2c2403034200b074440f074010f00180f003004c1e0341c041e841a01034907c03680a007030b01c83d18541e901c2c08008401c41085060580100000e01840910400d082c0c034003180c9a10f903040c80780d803418500c501c0759090000a408a250a8482c0a1401c0c0003c920050109540700c2c1100032910307440d0240f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 544195998 1250 544194748 544194757
    0x2a040902030c0708270a05060f0a020118050d1205071e110a200f062203060e0d02011a0a030212070b07030801031a040b0f090c121609060812 62
    0x2540c5550401200e8000344c14a0f0040000b00054002c441c50552058207150522904240c85485003030461000c0c0042d42e0b9490807140c0d5140114800d56556020b40016400746c404080442e44035a03203030a182050200110b041032101031140d4030058002142135400d0b0440d03500b03035034602c005403600c118941d40d1a4118001e001406041c2000350032010b03494032081c68231210010481d8008c2c00410074041002c503941084032000c01c02c1710760710154407100001c60120700401a45180c0c81050104200c9410325458813840515049441408000420550346940e4482941640010741ca01901c150b9107000e401c04241c1c011400524401c00c20349540c007004540b20b0400c106010700c1c011300400080000740754000b0000180720f40c80d024883d40c0340d403e2103a0603482c0501d22084610f81c2c50300300400100340314403080e40045410b00c07000041d2200f1b8412071800e800b0300c000b0360304801e00c000111003501d40081ca00019815410820f03d015031545444030070b0b204944240c10040d032000380444845640107002c1d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 544197248 1250 544195998 544196011
    0x50703080609091c0f0e030304030f0318030209070c02010f1e050903030f030f01150810051c050a050c1011070312120203012601152303030d02032a04090203 69
    0x1e4045144d0740e406202d011848929840100c0c800c01c080782c1c516900700c5512615038000b203000e107003064595144c0010310101c9040060411403200c03070310056480c441c030180c3c01a68000d8043d50680c607240d50040c0036211140b00907070201c0e20342c1140014403403040b0240c0d4401c0e010510101042407124409a5032074003e40030280c0c1c0b500003441469200052080550701c0f0b8003152031320000951401c4140f6400100303980c001d50070800e0b0790042060703140d800e4441004aa2042d030311034041d591000c0a2941e800c01e40361004016000f401c0b020024480d002403894001c0b5412550403200c1100083c09584046030041052150340160348104041140400d14076000810780c204507200f04070b0705030260101d910903005141c410071208126400148400f030144515100314000300550103101a07001c0702640c171745c4a12815214100055103c0c0c0701c400d54084084080641241e4550303504203210006900304454182c1c1807a0b9150b6039181101e000c220394114004841c0460b880c06007441c081101a50008041c2c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 544198498 1250 544197248 544197253
    0x603101418040624060203031302040b280915050f040912050706060603020a12270602070b10060f05030402190b070c050603160c38010605070308060909 67
    0x1414001240d408040c8524442c180005401c5520001c150010349204d240322040c1e000c80000b440856000000c580e080111443c07041e840d00c650b840054042c1024100854000b02d22000f07030780424980c56001035641c1860749407810700c252a02007074800c80b2820001e00c0e03000500310f0350030006403c14a09032005081e0150010540a00503100d0001d44030915122100180002552509101d018452040902414a4190b2418080b084000c000102c0444001140c65031082d600e1010b075840c0e009644c5c100d8031b0708441c0510b4070343e40c00d021703000390080e044c15541140ba82c0001185000141c060a066480c85d44458401103618602111940c10003001203070041e50594003c0a0340102c0d0007800c0040a07a507400c0303170303a03885107180c0010038888581c812801140103200340100b50107012246c40d02a521460840380b00015403e00d0010826403030f40c00368010705801c0061408000c0e0080d98001c0e4a040540445180d0341c6d090100e4180c03041c40c0c8090000b8160741d011640618240403ca508811301604 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 544199748 1250 544198498 544198519
    0x617030f070606050d151505010c020f040609050702030a02070e010509010e0a0207021e01030f09030e1203040515040617190924150e061f09080a030504030c0506031014 74
    0xb045c0144862441610004805018000d004217203005203101840401140b00a0340d10b400e001903d00caa52040083c0304210004150700075444a9010ba0002d0440c608141300034200290069100c0d801402c149005004903000403a003403580540c0c0b241210005030807508540c1c40c1400e00c42c00c06102030701ca003003001d800300880009030380d40070103a1030b00f00c2015a50f41220400c0b4000136080340c1c40482101e45d5581006d0040340030a4000000101c2e10a0a494801002c107541001d13034214802d0350805a8002d803110700e01b90081840358041c1042c2e071901e44032451038041041040840702c4007140c42070310700d071158004040c0000c241d420441030342e0b204601c2c20f1044800c00302543c0c0c440d5950b401c460500d540da80c00c00c00600d2031000f6801d00400141c60b980346981030040100c0c0341001030341c402a0a0a4400080c840780502c05e01c0342c600108000c50507110006072038a0010a41d5002e884241c4100c242d90002081910b0714408030390041d009054a250302c1450600300d000d05c1c0c6150251070303600125510703 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 544200998 1250 544199748 544199759
    0x7030506030319050d06150e150714030d0522020d06020906070f05060109060503280f0f03020c040e1e030f040314011b05180a0f090b040617030f070606 67
    0x305010b01c10034054032140d89404180041c3c000703c402035400414030101000b480007652340c002040c00c40d602410b9410a5840d0f5100740c01242d5440b582000501c56450b0491241c00c4510100c041e0980050000090185482d100307500c40b00b00c0102d180c5c00310006103101d285001458010f04512442e80f05800150408100100140d52608082da0035a070050301c1e00740321810828140b00d440e0140060310810070a250910010a40d075100300503607010b1020300c4001c01c032980040c100108260799801a2000d440f01d9441c580000361802d0400118013500c6034008040c0d940c5000d01849843c079080c03030028100803c40038241040d01c1c207204e025105c94082001a8200000c080c0001c10185014074040300c4848540b00d285401c440700503c9200700d1146000304121441c1d81f00d0100c40c4005a00b4200e0001c0004001c00200d962107944c0c4011181522032100082c0070006421000c1c507640115401c026042e500c001c01031151084c0c1950031103581040010300030022209000d400344034043c102c0001c0706a101c2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 544202248 1250 544200998 544201027
    0xc160305151308120603010f1505040504081213060b0306190c031409070e0a020a050702060310050402070f03030b0a03150e013218070b03070e09010f0617040803070305060303 77
    0x50070313550f014079007003005c201e0380341024094018184a64041004001c110001c7d1a02d060b480b401014030480d04e800101c0e0034414200300762030300c1400e00c525910325418049141c209030142a00d04503882818514911014540882c07524031032090741c2c030503804158280d50020f00500c0352480c501c050664650f00150105841c0042a10500d07607100100303a01402e060001c95654401000c00e2002801000b00c0c0102c81e0307010081d5000c865044c2c2d80b06131641c0311144010198040c50300070030740052002c14030386c0501c02400314a003903550180e101003085090394803d1140101c018000039100c0404c25101e20f010183c0e9503c5100c040f00c645c800058090303040000e042c1023420161400b2000301180c1c0c60000c1c20340c2103d640603001b482d2070221a2801c4051400e00307131244040d2040c200395103800700001c0d2050740210040076400e0001005032501e0744e1a085034107021102400b80a00240320000604501c05403210210701984c3c0200c225421952604000c40191100500c00c40d011702040c002c080030015207 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 544203498 1250 544202248 544202257
    0x8010909032d0306320102070b07110f0405040209040b071103030f04050f030a14030403090306090b010e15030a060917041805060103020f0a0c03030b0310020c160305151308 76
    0x18200080c21141e0600004041d40e20640007130f4440c014100030304400b6061031a0249828060041794080b0b401c03c400141c0c104034955014802481c000500401017100d01d40020800550443d2400191254070f02800f0454004071002034002c0c0d120350100703001c0340710301034050340c4107906151024550341c120a0140c10368005a8941110b140d219080c0010081c0600601e180001040001c5090407002d050040c0944601108400007034400004103082c10f100d807400c1e030b0242d07800200c01d10041c100c518201190480c24441d50000c40f581402088071a0742c1d455241c21901c00c0240107151801c240c0c1c44100040070300d100b0449000101c2d10070800319607000000783c0020220355100c4c1c5200300d8901001025680028801c504040c81001200880e40490080d5211804d2501c1c00101f1100503250a078000d148001005a061040d1191041144900e40052851000c41000e0b030f244400344084c0ca20b0008281c2c00014050f40010380000800e100110550754010031041c09010014503980b29402c00e07500 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 544204748 1250 544203498 544203557
    0xb060a0c0b010515070312110403081306020d0507080c0c100906030507020a020a0b0c120409060801150e0f0a090b040b091606020606010c020f040507020604021f0801090903 76
    0x11550011420300040149203030040c403082e1950340f413100040b42400c40714810700c500182401421038501d0324065141c0d0100807002000c56025a44907240c2c1006502ea0700802c10038144001c0c400d20200c1d03083d20103e89011510310f01e03118541094116650ba011030340048140f011907100e101c40e00d203519500e02d06800c0515180b0b48805030b0850902c400113042d03540080c51641075600050454005882d10203198048550021540391100d00413554242070412040011070007460200f0046002c0c41a5441401100d100400800580030b00007500c2c419014544102181020400005070100c3c2440c101c45030b02645820b40001d510340183d69540141100b91419a41701421604001a41c0c104010500105448800c030044a85c6080d1009549460040a00f41080321404181c421901d4071a10080551002042408246003d0304000d6a892084a0991082a203c907083c0d200f4030746095298441003803a540c00002da828117107403602070302011504604000403140c400c4000b00004099140248 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 544205998 1250 544204748 544204757
    0x160b0a0c05060a0519020702130b0d15020a090602011806050603030708070501060e060315180c060705100c0f020c27041212061d071418030714130f0b060a 68
    0x620144102d111709800880c514003900c10040f50300540d540070802a0310b52148040410517580140220f01c45045800700200007041c4103034400d050f0241a000b621407222166509400070360344000c124241c9000b01024007620480c505100e01142264124660000380901102d14040259035503031440d62014400742c603241d54441051203501650002030781c005108800808100601040c0b100c4461400ba28001c600c0c0c0c1000400b44e012030044c046d59030b0a0500510703035a15001c890410a441e54546000705444510b007111000c500341c015070442c441204a54000c01e009100401440040410031040341c0b00b00346903907c40b8002c82d1074188a141b095100e1421030001e4240181d002c0e007143c584000c0810080d0400906201510300102d654490f40192203048207203442e110421784003140102c90f4a00c034903c00080c450080c643d0001003080001c419022a22595078032485000d05000c0b4442c00b540c08440000241d044044940180c0800c00d070410b80003da50381e40f0b20019205900401d401000b00303 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 544207248 1250 544205998 544206001
    0x6110703050409060f1d0a0605030a0c1a2107140d092f0d02180f0709080a0b0604020304110301060807030605010b070503031605040e13060e160b0a0c05060a05 70
    0x704204c2c080c080040c94180300e07001c0c405003040c40c08800d00c400d603402c0907440d1904030b00040c032440c455000701e0300a280141c00c0d650a061203080c404c0007281540901c1042c20440715242c202a10f46100722010003a2a0040c07401ca0302c95800c044150180c00342130b010402c044a0303070310260341081302c0c01081d51000e04180010800c1c07040c6414505001c80b541880000d21090340124090f0500208540070b000b411211801d07034900354400529503140344d0300c02608840ca04000c020203180f54000d41400b031041910741c3c01d6101c2d9070301c0055a4800f040d0800501c5e02d122000400e11504190b005180c0042c4240319007030084420310b01003401c4440540c45190194000842003061110500c94a405020005401840e01c003042d1610765485c8005810b05450040d40074568000901c240b0544001d0541d07040b0103c4142480c5528030101410b09100b902d40c0e500d013080040981e0800502c5051110380010703400f100c507180031041041342d00007207508030a0000700d41c01704001030424001c503480349403505000501ca = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 544208498 1250 544207248 544207259
    0xb22080312160e030c0111010f0e0601030201080c07020a091d010c0518031b0607031205040308011d06010e0919020c0f2802040b120d0c02100e0f0607061107030504 72
    0xc600b14014035007400444488207074a0703140400c0c1e0724028842802d1124400d00203d14660040862403222109149800c1d1891203080340801c00740d0489000741d03074102e4103403118064505103101d5010003d500068a910800c1400d039103801c8003900241c006110040c141032000f6090948403000d10000c00a03030000cc1c10403100c20341c220740300d8a800040d0010081c21078091180d160004940d030503140301d60400703e190000c0501c118034540080d1580c0e0700502c2241454680030b0007580b020b0150303000629205001c0301c0c0380103e10313801c940705000581d180b04807544104180503594030090310500280c50244680700742c40100e80014081110010028400c10381c50300407081c10450304512800e8408204941b142c800c4c2c0c0c1030703000f46900c83c0e01200c0001c3d00b40c10b240001040b04440c0e6036048580c0c01050034510b80c0340e80003211211218000e491541040f140700e0011101090840c140d5540001441181842c505100f000340c640180300b4a0005102c40440f0901400c50300b00e8042200002c5001806012 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 544209748 1250 544208498 544208521
    0x702150f18010e01050f15091803131e090b0d170c010c0e0a050303040e011802190e0123040b09041d070609082d0a020603010b090301060f0b22080312 66
    0x507c200b44a002102c00310350000003c011070405004400140f41074160815581c0d424070890b602c0314074540c0c01c0542d465aa480140b032040c9800380400d0800c000000008114403c1c1c060f1b10300c40d0308000e00d07501c0104d01c41c1e940c5003d401e251510341e0580704000d01c004a0031080074400c122003230a003a101c40100442d00000c10102c03204d0754001d24003075002803000308102c101e0761081d1410f6862188c000321070b81050b000a20002d0040305d080b008188035800d040359036103812121805448100b030342e60411103011000124841000004800e220740e90402c0308003c001031242c040e24201100501c0498001c90200d05d58602250f5041004241d800030801044125000310b1400d00034003030350000d41500a00c00c080e0500003606c1d00204031344c00b04902c0b0b50344201641400924507083d40100260380ba56101d0150314811341001305124040d43c40d1517000328000940c1481d410440300005140d03441c120810302c5603560510040040490b641c0c0e00800031400c1102880074000c0325140044052580c50030090081 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 544210998 1250 544209748 544209751
    0x1e0f04050306011202060a0c030c0203100b0f0f0105041404020409050717070305040b011418070210200f0f07060203010801020a030c0e01080a0e0304080106080a05060702150f18010e01050f 83
    0x3022085036940e44c500503142d08060702d4551002d030906071603080c0281401d55105825202c0254140171780785500a0307180300c0790300007140004107940c1038100070809810300040b00b0303440c2c5244c1d011a40c01e100030840104000b0080c013902102500250030180d442c24490243c0d24152a580c000c141c3d00004100c04c00e0402e615236500072100d02d018802400d09446d16040c02c003040c042c0218103041c51158042c02c0c2c5442134200059030301007500c50342d28030384003000075142c0c0d9014014040032401c04c00300f96003080640f100012155814810380d440c2900c2d43c0e000040661040500705041102484401c0110f4501e1020b0350090511000250740c401802c00300504882d8038540da0001e00c4185c0301c51604599101c401036600c100758031800600c4101d1240c2a520b580a5035010181f01d40c02d204000c54090710208026158a102d8002c4644907114641d00341d8991101560501e00c400e12040000e07908100f850780b07a0740040d03410500745850021306041500f522141881150669140c20500100602c04910b09 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 544212248 1250 544210998 544211009
    0xb0703050609010b0409021b100507020708071d0601110a080301052b02010c050f0d050405090109020301150f090306061d0c0a0c02040f150e01080c030a0c0302061e0f0405030601 78
    0x2d2143d6042650480041c01765014040b1810387c0420703090700081940c103908c0c4c402c0607500100d403d4001c10803045400780108507001070060240d000d0005850100141001c1a070b000e018411503140a40c1295880820000344100d042204822101020040c05d2000045083c0902d0307009a40b50b0410041c40700007030610002491b40440c0c8022403100c140d5600010103281e0382480d202c48500d41604200786800460245004130340150141080c00c1c81d003000c020403c8980c00d5803441380c981c1e80d96864904030300092003904041c00c0d000722b104c03601ca0710032981281101b61500300049110b480e5110803040360119085501a843c1154001c80340d88241120036600244e042c0e03c1d240b42560b04600109001009400203000300d464900c10340441d8459001070f851204100d4040e03140d40d99a0314100c22241003071143c203520740940880e40d031141c200481c682c0c2e1031682210500704003614540c00c0c880c059021030fa070030500960641140d000c503442c0b00000c002c4107118190854131341d42840c00300750505004ac1d006 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 544213498 1250 544212248 544212259
    0x90e01050f06030a091106040801020a0e09041e1a18150103230f1b010f0c050a021e1302090a08031611010903080c06040b0601080402010c12030b0d0b07030506 70
    0x1e5200903540c0c24200d0340d0000110303c01184d844010306d030010f507a4034181c1c805030740f01c070003ca004184100154080c00c41500b040d2b49100140c0307000c0707041c8280407509035009841c107007204c1c103020202500030302a2080f81c0d1145040c048500320203040386400107004d40301e00d15100c00312031400c9a100001c05c0f0a00c40844540d04040a03949156200751401c0304070283c13003910290350640281000700c244405911002d900c006d0302c0c10700003a00482c5110341d20075101d4502040c900216810340758400d001c0345150710b40c801d000f0551a2003540070010b00100d082c1000300c0414603000348959980300c0404004100300348000160316918101304001d80030026400c015410b90050041c803036080e0502000814a5030088103081c0c03001c0c01c1c0c00049612038410341015000f01800580301081a1000440a01c503a004103100352598507114011030741c103581580d001e03000074081c075010404540741410340c0001400303600f0005442c50540010806014a107182a50703014010020446259003500606030f00082c1181c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 544214748 1250 544213498 544213519
    0x21040c0e090d022e090503090123030601050d022a0709020c10110f070b0105130b06120711100906060902130e0601091a0319270c050d03090e0105 64
    0x203651300e00350071407400940c83c4002001d044504402103408000300d289014080d50a00b424501d540713030320038040240041c1d51210400003516400c60081d405491009190346152200c03001198240c0002242503592a4200701104035400303026104c098501e06070a501c0e03816a646142035003010328075030000e0b120702c1c01000704c0e44a80304007042584500d00b2049000500030410300c1c0c842d10758000da003040000c4c080c0c00180340301480120602c0f28100c80c1e040316690b80c0d080160b180c0b070050710440008039820150500002e11024034032800180d20241528040006441c0b15100620700b01c0071a2407281101d40d10b010800521003640141006080e107444150302e000100b901c0b0441406140c8101c840d004021000320322184c0c031036078200c0300401d005403400d1480703489040451030300da0041d150b0400d0104902c0e1280001c01050190840e0305445080e00c209540c03840910949905825004407031007018041e0104242d61619074007003030680640d0b20304c90b040d030418000d09004041a001385118404028 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 544215998 1250 544214748 544214773
    0x2120f0901500c030907050402190809010e060a1a0a080c01121b050c010b030d0509061b1c08132105130b09040b01170c21040c0e09 58
    0x1402041c0c00a00c6003075450001c44442d10540400c160b05001000c0c0450a90a0000c42000500a9070040110380103603100c103603589041104034801c0280780408000a00f04042c03900c1d00404544d948010502d00204404030940d2072941030920480f094101195207205c1004115841c0d0035042c82c0c0107040d61402520307400c015400e542e0b02d003028445c0e41041021307502e06204c0d500a41100c0d03c818681c0e103070011441c032001c502070025040a203a10f5515032900075445982d10b00040c0041c0f0308a120b456803854100e60000b80030041d80603002414107400d4114020009403810400e07101c40321030000e0011080c0c089140010004100070380006c0207814010b0701007000c80c103040003c240e280300c4d2030070700c030043c01c01c412041c0e03020f02a140c002c1c581c002902c1c800080c01d4152800902401204032000c00c1020305080c010744041e000c0005411801c0f00201c00100a80900c000405046004111490755070248145001070030400312821a0381000c0c1070380400003084041c5000f5002008034028100940303218 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 544217248 1250 544215998 544216061
    0x1a0904020a0b0c2503022b03120b0901140a1211011805061209060901181709060c0c0f010c0f030e010e0415082401060c0602120f0901 59
    0x2400380c0015644009441d10610900304100f00300f4a200d50610300441c0d260544c402d6a00d8481e21090b4080e9500d18035070f032290301d21000f62400c205411251400c6180564408585035001c80042e0f001c015642d6006003502e60b03035006d100b802007280b0f00f0710030b540022000a00071009004e6100740c0c01c10101450304c200003a1004881c0b12481070a1a10506100c580780d00744074000b201d513001c180c10030b8000800b000e12402d4490350701d200b00c000e402100c002e5198618450700701c81c0e248000c01003440035072034148002411090101030383d50440071800d080c40366a5001030255440452402e045a1002c40b0429290410710041e1004280908140151180644a0024480b5482001410031000c591325200e0b1b680039641d808180000a00104008203012409044c54205130195150074400e01e10301c4c0008a080c0d000208030141e80c0c00c011004c503442c1c0b00c0195011034003004120b401c0340e001c0c448041c0026403020724500c220701d41800bc484500b001100c15007110343c0d08240702d5130707510503144240b11b4480b40b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 544218498 1250 544217248 544217269
    0x80606121312050a02070609080c1207080609030703120b0906060a11100f0b0607020a030b2802040519030209060105070f02040504060912170a0b1c05011a090402 71
    0x4000414280303603503603640e856115460350380040420440d10000d1481c0b5610402414442d03900c1c2c1c080f00c00315500c0c3c05091700d01c1c10b00b521640e00c3c107138070444210340542007044110810300d10321011038030000c0c1c03107800240c02e01000f04c525641640c0003051600515a1182d00750703182400030841000ba030001100410603843d0000c00c6e840c003660300082d40510030b61040c010441c403210030030150788804403868000170103000304022050156050090340d44a5241080869031038680c0280010165455aa180c2c607031030000030990035500754920f82c1c1c944002d00c240d01b138240c0c4920324030005030368034180810005000c0d18100c90742580c051062003400142c59201c6c181e03402034424240251240b0700e510702049080214072000790040d0400b400d200402038207800500045e2302c01c00d80c26041c4100034504465150040000c1354207136113204085954007100e40c0c0006051540034100110004400404031515441040b00b2181c07607544000005854840d01c0b620701d00341c2ca0407182a40d0074101030300000d510102 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 544219748 1250 544218498 544218517
    0xf0403060902030c180108011a130507020f1213081b060c1207050105071709060105090415022703030a0903060c0e0a06050301031703041e0206041707090b01080606 72
    0xc0c1e54040e4010755904000c03159403080300030f10031281074201d0725002a450340c0a1245020944c209501130311000b885500345103c50a015143c141152a070700d10100240002400110544c004d441c217100b2202001d01000030b822444818156480700d000c0b41c810b5081c025a44a18202e400810054505502c4404a036100700030071a001c1e601c038040c10020900f44241e89802400c141400100d0108001041d00b10f6441603006440300054228030206250202c03004461051045d0040d0005000702c8c40c0c0f503500350b90030900a5411425050f8031950391001c030780c00380024440e511603051540e01040340e000103e40300c01300c09a019504101141c00003402c05062400010b202c01d03240c5450b402c030b440c0308450006800100a003840400f0f551442c020305a54428001130714160704034090b2190348c0c510305003103a0080e540f026038040641b98409200c0c0d40712400d03000c201d81c098410400080c8a1108810403d41e48507080c001e00f400703030300d00b880803011100f10b26a0075061040c42410007011b0307900d5038107031080d800 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 544220998 1250 544219748 544219751
    0x15050405190c091a040606020a17070510020c03090f0303040b0a050f090a0b031b090d02040c020a1b1403010c0e240d02070311060c1c0204030f03021c050f040306 71
    0x300545051500d5508a810442c14280f80038540c41100b00c51300c201444c4c460042d00d040203c2038455074220b8590707904a202410002a082c14900300e104640010016540640c00380c469140002e030002003683c1c042146500c1075840407600d65128a40b0788022045d00d80c0841c0218a4075140031139900485c054050540300f0301070301240b1441200c441c130007156604800140140c210640b1a43c1c0207038260000d90313015808240e255410040b90a0300781c110b4031a05401440303035440002a40c20040a402c03622030540c00c42c02940789a5000841510303510707294203152925000d002e81071410385c211404020340320380e102c2da05000c1c0c50b284094014880400050080e110103802d101215140c030150361846846d10300c0c443c40050035801d052210b90291071002c2c400d55807094020000e03140c003607982d401a00d040d0190305042206501811408003002c0b402c0011403009400c059403030321909210211103406a000d40c00101280414443d00030b60b44140724500d0a10604083d03101d94407055600031400000d1015 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 544222248 1250 544220998 544221043
    0x40510020f1c0905030601030501060303081b0f07150603060b010311120106030b01110706020105010608071715120615181005220c03200405010203070b0a1104030305030415050405 79
    0x8034032641880f000b0300009011a4078030b503582d00d80180244550720054001610384808580810001c0e50b0680c0e40303891840116082030400d00e6144070692000200303c0b482d100708409000301c00c580307004d064015801b840e0009000140c1c48000b60a80e50322241c0c04035460350030041003070505003a00405064030040e1500098000c070010050320f905226582d0120389206a540000f061641500141d0580d00709035640040c0d5103420406075003200300100d06030721108072040001c848218000c001064118020a0b801010007201411801c190017a10071200c8520021800b02c8241071496203d0b4541240000a11007454000c90582c0f1800c400e01034540f04a404c540c01d44041851b004401e0b00f1000d44036010448541100000790050602c0c50010145414014001721030400d80d100303403012500c041c3c001d1880d1000c165a100d2542400400a400c800d03615502c2008085009016001561291316001c0d41c80c00c203030030440001c840043e08828418100010000007940215507440d040340d0100c0c1d1000704 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 544223498 1250 544222248 544222303
    0x150e0a050a06170c030c060301080312070302160308060a1205060103030806011713030f0206070912020a0e0f040606120f0201031d160302150a0804021c0602040b040510020f 76
    0x3400c0182c1c0310000b4400a20400f025902d008503880f40e84010072011104c2d00715008003406001c2c0000d104210b826002440541702121201080c60b910451520f40180342102408002d105884080742c03d400040c40e20042000c181450380c1442c026102c100182402018655100ca5440341c1c1408010100710141010400030b900540340385651400d07201d01749502d440d1550301c40c0030a10000c03005070000b8600042c0d011000f400800c245025031601d030f445d00950790402d1508403c106000e04105e812440007100040c0301c184a0310b0440c0107109961078840103042a041000954415400015100110141e403d00140014180301c14607942030801003540107009406040c0021845440303000741c021450520039040310f840383d03401270300c0c821a10140224800c641d4480305005221a0b50040f4034900c0100300903152000c020f4002890580402041120540e103440990b040395004d2040540c010034184810f20f84003420b840500200d100800f05e20035040d00ba540d9031491824010019904500741290 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 544224748 1250 544223498 544223501
    0x140d03020c0d11011709280507030602030117030c0706080a0f1b0f0e0f0108090a1a07030e1c11010b03010212042109060807030605040f0b04150e0a050a 67
    0x18000802010602209483d0030700c0e1014100031848903002503c0360a10070103d40301c03400f0480c00ba003850001420380c107640744c1d00228010440003d890345906281d24910005004120b41c030007861240a000d03840f54500800c51401c2c44d04040588826001400f0010401ca00041d44004131411854024202e44600744000000c011459844440d41d0501e0314403e0f500101e0041e410041e40d444e43c0d0741d400c0b9162044210365020380c010400d94800c003a906a0349035503100d0f500080d044032000007178590140b03403036545880b20103800490540803d102070030064420741501c100c100e0000d02101034001408141044c0b401041c10803c01c0d010f003c0041039010310540250f0100303c9504014008664070fa0401d040101400703022501159203155080f588051000601c00c810000c00d060b4442c42c0841b0b00782802a102c03c0c0700203186c2c404250303a54800150550740e078000d04a100301c54860001d840c400c110140815600500e20029020f401c4903401c00110320000700042c1c1c410358201000400b0f80300c0078004070 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 544225998 1250 544224748 544224763
    0x10302250203010b06041a090d05150f0a1a060a020313080a1b08100e01110408031c0b01050a260408031e0601050a050c03040323060a0504170711060f0c010f06140d0302 74
    0x800f9131180ba0000728000214192f00f5003e100c200c0d000c0d42c283d42d50038000b401900d8000b002c00d010703113408542420f1281002400b0f42110140303030041d20b0402c06075000300012490795a100800c0c0341d0021a80405008010140c944030100c100c00c03006d141400c0c942000e65071030b45417692400c62551002034510160082d4840c1c0c0c810310241c004a03543d19a40d06049550750400010b2100d1b10800c10703488030704010588030b401200141a102c441c00d201c00f0000503516040400d034220202e8030045a039082a00f00c40420a10a62060703802c107842c1d05103054100c1122145c50410400d10000320284100c5030381090560303607000e0080c64543c1d41c4001040500341540240c2d4001000c001d2220a07580d43c005064580202e41018a0101c41003566414000000c5d41c1d41524042c011101c140d004405406d043d0303008011003405403691064038214080820300a600c0381c0d200c5008042c01060a0034410b000b0b0103507020202c1c10110501009080107210310508403140c040301d128250b0f510303104080500038032850 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 544227248 1250 544225998 544226003
    0x70309050d151a010207050a0312080705040b07030309031101050708011e2102011d060417010209100302030907050f102001020418140f0a0b010302250203010b06041a090d 75
    0x50049151442c1c03150103d90040c51442c2c05409280d4001c242800c000c00b201c01102d410017050304014071071030300546c0c100002034003040400c0320800c00032410a03c818001c0c03850030301c80d50780010b04c071555080080100c80d401140404990519040c0540b5030361203402c0ca8192450107800281410010b00408261103459200700818400010140c800c02198180c5401060003070300c40703244001d023050000701d41e07100d0400d00940c010410f00043c0914010085403101d80f20340701000500e031025100c001141550044424170010360000200f00d00a48188029001031109960540780d61183d900041c540148101440c1d0412070303018512411310240d03041500054500100840d070743d98844100950840303407000f214101905007400591201e004105141c41402021070a080340c1e210340705041c015001d4824242c0c105902440030861419040c540706142807101051800243c0c554414103003503d00d694103091145406200030810f0401c00496207086400c5030080690b40c003102c40001d4032071840030101 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 544228498 1250 544227248 544227251
    0xd0e061303050c190b040b13080a12120b030304030209040606050d0b0103261903020f1305040e06010e0a0923011e05060303042106150614070309050d15 67
    0x2050240204005940c0300007501c00030758882044440d19601c0130300344294181c007507007007004100c050944000381819407640c13002c0340401d40c0d5902d40c20b841d025000c82e080e07401811000724603110340e42003040d050300350405500c02c0c400c13110090002a240e009601c000b82c002d025050003d400c0080640c40440582401812150302c0201030900d201e00c200240030443c0c400c015002c20401d00100088084c20807a403c034045407800c8440b0390107114482c0000b140301d0070b0580a101c1c01c03410400303010142020424400c4540c150342e03d450208800d032040b90052901e544c00000041c4160303a003075000c0070780c0710404820100d40c0c1d05562a150040b289d0707070400035042c800f07900214040d0740e07010f400c903400070444d88440302070702010304100a040302e03410380700c09525130320800082100d42003600201c56803500c0b0524400324610141c80303000580d034490142d001b8043d44031a0a00500b40c10064060b5194640b9840a04283c1a9a0003800c5403100340600ca20540078001102c08002500c0f208462a480c400350 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 544229748 1250 544228498 544228537
    0x70803090607080a090b1f08010c0e04061508241005030a150b03060415120309080f0c0901033206160c1a090307060c0513060305090d0e06 61
    0x154103858101c141d4162000030194004200044014020200841d4214141007940c4d1a021040b0300c1060754030410100c14a003040c80000c40d030400388038440d11501581c03660080a4400c03c204412104550000034806290740f000e081c4966210120991050441340e0a01e0f0665402c0058520740f60b800310007551245070002e003c0740c440d134800c02450041c0094941406281c813850101401da03405800380401d43c54040c0002041450181c2102c20060201005421030fa5102c610f01c2034801443d030b00135404181c0324082000500400c11012075404400005001035440c2200058039480062101401c1e682640b041e603108036424030702d4054800c507001700c1c40b544900c0030280e40c0c0c1c95420445910318296180300b1030260950260480c030fa1501d6018260f10b59282c212804210300090141054480f40700900c00240000e580e07100b001d02c0c12016444c6d0685420240d0286c50001c0c0c8150410800c042c14041402603415000401f4074542c0c4103810b00600612491010a01d24000c8a814058007401c060 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 544230998 1250 544229748 544229761
    0x5280504082d060f071d0d050606280603020901090801020a0309060509370209070c0b011208160521040f06020a05030a03051f08030c070f060f14070803 67
    0x5105107480080e2004000c0e80b8640c0c202c81e039844040480b0078814481c9100002030160b0701c50441c04100d0440b1a102001891104010518040c100c40c8100e89640c0001d083c00303107601d80405030022003480004c04040502e8a1705408000200620485061503004150075500d6030060550b480a403031610000c5480380c1041000902404a05070f0039074010f13241c6804034180c02800303e15810010102883e28100c90008662503c0c1c0e441c41d040218a0915010207030f000603520549101d010301103503925024586aa401e0010381c402043e8031a10042280c0c28074100020010710982d80074401d05940c03840c01e0502030501c00e00b04101c15429407010342c0b03081d00d20b008444030200604152003410ac0640b51454840c44180daa600c880c19001d80103500502c1075010362440b03900404c2c3c0c400084151140140d0502c45940c60020440d08004030f181c10104642c02e5200003002500000c0a08110102280c1d2508d00e001e00244000c0c84c0c190104109a05665114100d0f64211402107a01c0301030a5600c2c80d209 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 544232248 1250 544230998 544231033
    0xb0a020a02100503011508060a09020f030915070c030f030b030601090f0608010b09010519050d08030a0b0108010621020403120804030906031a041e060e0114010528050408 75
    0x344089100300e00909240305414850030541c0d05855076048401c840d24045401990300c0b01c0004c01d01c2ea409500b000010411500c540050015079600c146633640781e0514050540c2412400e50110003940318180812032800d51000106030300d2901810b00240e50301c0320034800c0303001d08440011a90580b10b4080002082c503001c0d0301c00d031160700c1005002c11000b5200c0c814a0300365a5000340f21548507002c42c005004500e0061448040301c107000301412072155407040860b00c441c190752800d50b0340034004010030010540e00e000300c4100c0502407900c02440c0d03040ca540030341003401d1100c00d001d00300d40e04205840402000e034102c501440e0041c040e09990202404020300c1da020442d01200003484640d80006d42034040d0040048100c0311103040b040b032500010a0000401c2c111403044000c00740c0035508189607030725110390000b82501c1c507103c101c0c0398100811190f210381d403007035454100b0101b003120140000e181c0c0c1910341104807441058040491104045855001d2034005a025008101c0010092040f0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 544233498 1250 544232248 544232263
    0x5010e160611030306030601051203120c090a080c1f0917010c0e0a03050309060901050d1b020105070c0203030d050421030c020c0109030803040b180d1106090f070e09070b0a02 77
    0x359407000c42031a00d002d06103440c0d01003510a150160300c00001808070b03184c13101000c040551010100d03401d0031244440080c400740143e0715040c44860010b2525501e0404803c00805086003900405545e050103020450282002140814800001000c01c0030144120403003002010304040c0719006980081a4034000c100e02c410580210f60011440c014a040c05446481105c0d00400078604101140701400860380c4000c0700ea0741041010400700c0c1403075000780b0402c5803a040d1480705031003038002c1c01c00103421a00c000d0259000c0c02001c90503100180c0d000011a0300000f400c0b00003203502e45643c0b41070300c041c800f049001c1c2e000c42c818901d15501240e05a021880c00b42d502e5007215241078040d030040d80c01075403a0001030300c10603040001a010070601c04406400010b03020918031510058218542041081903003040000c8881c118508240e80400034541c0003030454016026121603261840e0344c3e10218482d80044001720741c0003034001c41061200e00000c00746076424a030360b1030100d00001d464254 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 544234748 1250 544233498 544233509
    0xb0715140450070806010306020d11040603020a090503011a45010b04050603150d020307090f050c04052103070210030e15040809011101020c0a0606050114030601050a03050405010e16 80
    0x40324000350b8803024002074920403190300c00041c000030303401d548486c03020350b01420840b0b00140e143c00a0483e040d00702801000140800c1d03a0060300c4881c41c103402001c0c0c0c1119404076109070704101c1404594401400260401d00c02220083c602e40c0341020401038084000480007100e4050000714500c0c14410140d1140f0301610a00e1015240c1c0c855440d00014000e60283c07a070411424000110000c44803410300412503c010207440a0407610f500103482d02165400c90210b8545070b15440111921034042c0503004007400450a0800d8140b078081241d40608022001c003128000500c00c0015005000325001d030380d00a081c0712070306040c44d48040d02400808034201460f00c61035503603031040e015400b2194012a401109a881c2444c018011200c3d0b030b07040301c4007062a540c01c005552441d10301304108001d45124031400714500d4a84000900031078000403554030495410000c0240c183c0e808411148022001d0900041d20b07112403c0c203034010b21103e0311880c0c0e640300d40440c0d840441d1510307030716800310355 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 544235998 1250 544234748 544234883
    0x1003120216290f210708040807050109023c0f042f03010e0705030f272b0507081c061503051503070503070b0c010e070b07151404 57
    0x81c19113106030004005c40c0c0b40d1000079405c801040c00980c000005100f918001c80000c502c080090f0000350010000c10b0391604004084031300550424500c90104a40b602c60040e040130888001003c13a55041c04500000c0c81340341d68a07010102c09100e41030b4001d100038100d400030360040541e111858154401c2c05070800c034040c10800910310710700c40c000b00d074400d030b0441002030040e44031000f50032100b50700c10354501425030444c845c00011910400810100494410a80c0a1982c1d681c03900b00195415040c004c0400c881081740c14003090442c802c407290a0f810204c030100014103078840c24000d02054200c07045400e03100c1044101e0f03950641110307000356441505d02d90b00c000140304060b40c62940b44959074158200c13100400c240c41c1c0840240264403142da001007407842c55203844900f81890707604042c0901d14049074140611105202c00203074111240d00401a80402c03020503804108010001880e424007207604c0030340007031a038487d05d9080741d182088000c5c403d411407040c02080c0a12040240f00c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 544237248 1250 544235998 544236037
    0x6021306050915090105070f2402070b15030d0f020c060a020a030315140603061f0809060603010207030512150405010b0909220209090c091003120216290f 68
    0x69103000403140344400503140c861422a0680d00d11800c8c00ca03030101501e000d00c2c15901d4000c480c5d074102c250f1400302603a0a005a07954038926004144400241c640009032100590b80104c071b03140018030504d481d420703041c24050705400b104124948076102c0071050b007080000c60300c0840c41c0d40016126141610a4405014181d94244901c04210141c800c3c1c0308028500ca14920160078080d00550300079201520762146280300205034403014030307203401c0354000076402c104006082000348101d603008030342200250301d0201140c60040003070003900881c18121282001003a0311250714008000ca104000c2c00a02881d0782d103100c07a100f29002a000e503030086804500242149d0b043c0504110b8061502c506944031001580a120603003030014004409403040729145c0005a0f540c250440c41040c80002000360541503162200021860346501c0055600c083c1c41e00c60250343c0301c207511083c2c070b0740d14260b101308120317484144001d107006889522000c50300140305c0191301c000c800201440c026441e03040080 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 544238498 1250 544237248 544237279
    0x3030e1012110706020c070e010e0c03161116090f09081e0d09060209101b11010201110316110f060103110d080c010f050901150e04060213060509 64
    0x2080200c1100040c00d24501041d001d00c180e03005100c400c0072400d550781001080d0b96102c00300e900c0000f016440da80030080800c81107103051902c03409055000641c849030709080c11030103110300004d0104281d1860781884050031522449901c030040e0031705400c40d40c03000c00300b003200103083c02c0c28004e04440c035042c584080802442c41c0910110160b02c24203651801544441100d1300020516240c0d490910400140e80000118001c050b2000c1c007070300c001030b40c0d000c0c10030802c10381c0080d4800c902c05000ca0a84030641e00410580000d01041d007124080e0201208500102c1c01070001c844559001240030060054681001510310b140f60040d403541c4001000c600c2d020755480c696405088120f5200c10010710002c0c2c0c80050541081c4405840d050704026190380d444ca9617040349124081580d550035060a030b001041c000c0315080360740c1100800c01c0001c0c20740903071a400ca01d4002c204402c86008046410040d0f650b044604007521a40c1c900f00361034581c00001d00e168400110b191040c18820303000480b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 544239748 1250 544238498 544238509
    0x50103060c0e03070311030a140d080112050d0f02100204031407092a050904060e1f080d1b020d141011070f0c0e0a1e0b010203032403120403030e 64
    0x1056074003e008160313032851135035040420351141d130b585905800346002160008515500340c016141849000c1c0101c4039604800401c42081603100d900070000203031b41c00d1b020179008a00e844074414586420f4050810241c41a0310f08030b0080307014480207100050020500c1188000d901d2204542c0058610095541a1141c141e03030003001d0100c0c40210b446015048090030150701d1500000c242052030402401c100000c04560032640245200f80e456020800e00072001c80c00030b42ca5401c1c40c07201d00900d504103000241d6440000c00604148100602504008481010040100c0e580103013142050441481d2038201c0b004250241461407003100800064801c26020700c1080300c9071451014144001a105e007602c4444d4402c0075104030351500e0002c1022000b02a00ca84603426144000c65819911646c440c4444d52280f4001c522510701a0f81d44c2042e80d011085940107008001e5511030940400c0300414070819806925505100d42403d00c101c0b015602d0140040301d01039260382d10880305440c10f100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 544240998 1250 544239748 544239767
    0x7090b0412060f3608040e060913050d030c12090302010605031507080402012106090608120702151c02040306090209130c0312052b0c0f121a09040303050103060c 71
    0xd07160b0135002002d03100400c0c09011000300c440c500080352921032503202d5000e503511542101d000940b0b910100021070511a4213250010a03110b00000020b1a43d22071603100e4403401449000c25456501079002d50f0b101d400d00020403000c50900f00001d40680c41d02900030841889810f00900130044442185400f0102c1c182c41070002c3d86071080c550b5169401100c02d00301c1441e00002c43d914502d56662680f405204440c05488102c400180b1241132100082c6049103120000303222280c00c010300070043c0c071007082c104c903181e5080000f0740d1150200061400e403810301c84041d42600d44041070020600c1401c2d0086050f081c000e6071703140c141742c8481c01c108914a82403400500013940501003000000c480c950140c50007c45450706c1c50a214000000c40300409482ea0a00c070216120201030498955900c1000040301403420100030f840c034540006400200e060303407482034065a03030310303041001290300c954003485040003415001c3d10b207490b20f07002e070080030280416654245041c0d0855080d90041c80d41a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 544242248 1250 544240998 544241021
    0x4151a061c1508150a0e0604050a02090903040303050d020a050405120a0201081b03040213061e0e07050a120e0c040227060f0d0f0e0304080a3807090b0412060f 70
    0x1095840c0009168065100001e41a08045d590321486a0701e02a42401018041d500c520082c2150030382d00d00400102c980003404000c900d400810040000035040310480b0948480080e000d82c4828181c102500e4a0189600485c0c212518044c2c684002e44080b81072000baa1003600e07007000645421034201c1d00d2018249400b0a4440104003050251810401c043d020f22000c071000f003649030301c9584402a8059900c00962503141408042c0031640b06030420a601074058a48a810010780003002040b62142c90160080159250703541907101c5001c0c0890594144050800c0d96213100d02490314407104122042d1846c019280c3c881d0215610317200040317440180440a40710304000714405510000d00d80c864100030082e982d4040f0710307054501031002c3c0c001007242c500a030000c16001e0904076420260380c29a00741c0c0d10401205845048521808007140001414804d1074550b1540b00946001076035801152400c40d020a00040d900400d40780070351524071940081c021490310780d0600d01601c02d615a82e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 544243498 1250 544242248 544242253
    0x40303090b07020d06022106030102070b06060f21070e03010504030e1e04090305030f1303021c050d06030c0609140a05190b031e06010804151a061c1508 67
    0x10450080954060b00c4094001080c000b40040345036104012a801400c041000c010100c1030842d114080b01c0503160301c880140d00070740c50070701141e443c106405401010240305490110b46c80240803200c1041d10301b401c51144001c2c401080c0c541d0180000c3c241200c4100005d0030010a40030542018010140102d40c5502c601d900c0810200c1040342e01210300c00040403250b00c83b04000c95540c4d031801102100c41c020303221130390740341072000700100950001000c81c503403682c0c04000b800000c0e9001810b000343c0d2000c0d02183c406103084140403070f00d0f4401c0078061841c1c10700780b090210038004000c0c841e404554440e00ca10300c0b03880d61001c80895808040c1412035020707618074000c00881c05c0074885003200c88591000d1403295500e601701d025a540050310320080780c000014080710300f00e120301642e581011090800c0640d80c030b4039030766002201d401071010100d89a01c2d000700c50a40c06520540e40d0020000401691310390010485120550501a400b075400508000800605880d080304800a68010002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 544244604 1106 544243498 544243517
    0x10e0601030b12190c090c11010c09140f0a15030501090b010914010c020f0d050a0c050f011b0516080d0f020f0a0b040f0210020708010c0302040303 65
    0x1c0c180951034040c4090303034841e0005040404411501c130584c0481000b40b40003614084658840885070341404e01001d0800e810414481044c499200204001c9008c42012103107040c051155003c1c00c8401c1c0002501420b15080003090490090407021406644400031101400032600780d0000903941d030014014001540606480c105003446c15120300c9051901040d00804055481c9050100a40346d900864680140f0380d400800002c187e0303440e0500c18100319846000d001d004594803040c07500d001c9803e260001c3c95405003001a51a0f00b5110300703031003400109c00b5030310300c0a941e14825000d11340704c1d020303055550801a0030500d0203403a1858103135074080c1c00b0217620000c000c1550082d04416201c100d00044081c0116041003060000e91614185602490304060003e50071410103e03407510301d981c001035103808071003011008028100854108030101d01a81c040100001c03003010 = true := by decide +kernel

theorem cover : BRFrame.Cov 544064748 544244604 := by
  have h0 := BRFrame.cov_init 544064748
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 544064748 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 544064748 ≤ n) (h2 : n < 544244604) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
