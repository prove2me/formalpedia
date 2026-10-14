-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2474
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:49:26.621931+00:00
-- url     : https://prove2.me/submissions/8a3a9068-2405-4d89-bb16-7507e2768b99

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 444784172 ≤ n < 444964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 444785422 1250 444784172 444784213
    0x702030a080f06010201091704031e050709020904090210020f07081515010c020d0606032603040201030f1b2d0c08130b0414120c0a120f02031e 63
    0x19407520181c039500e40c010901a80c00080c155415552180e1028001551201030103580b4a00804003940326070450034860036201390795403c0c08428070041ca01c040800c0303000981d10308441000d0005039a444600003c5806000e036518025040541c440041051540100f00c07070301c0ba025000704441e000343d41c403a446680c414078484803080d104200d1010070900128a82d41104008043c149440b5003c01e41c0d001c507010106a40b8241c0340140c1e01c00b8144200500f014243e01445000c0b4646150180644620a403901c00904001e042c555101c4a880c090280d0b50020141c410034000200c080484560000d4115410b9107103400315403044802001000d021010120069600741d03803003001008040d82d4440841d072001c01b424005030b014031070000d80c00b4400c00080c000b8110550340114280c3c000414814542c1103001d10191980200311400c03919100c05d041c52040310b100c1c012071800303030202c0d003021020010b007480301a41501035031040c4480b415000c0c00d5107041e9440c03181100d9071712816007014070024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 444786672 1250 444785422 444785437
    0x705100b010f12090b010e041101140d180c060302210408030c070c0f240801140d02131802010206100e0408030604021b0606041104030804151124070203 67
    0x501500454401d15103c1ca034040e50b000c004020000e8400c606498103a0341d14000da01c11010300041d00c040100300080d030b02806104900030308143c0301141d002c110a000303d015181002c48591360303422600c83c4c9000304030040c412b41c0d41c000c0100160030307440d114002e020350303c200700c1406407505220b17013100394002026005209941000f4810f05540ba140c501e0071083d80310240c140d400c400e1200003c034492513041c448600514401040c012041d0703d0030014001041b580b02c2c071034203010000c00100310380800780c881482071280c101e913500a005001d10016600350352016500b01071a2604181c06100200c203503841191f00e000760200c40340c503514020030b151204c00300e0181d1050038030b1000c0400c00141503c005107400480040015041c0a400369404a010401c0c1142c021240d000109200450406201d400f8840441c041c009280c80d04588070000c00c2d00c41ca100700298403980f1500e90391445c0c412070141c482c0d000300900b030b52120380444501055080d410004001004600c40100341294000011640701e03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 444787922 1250 444786672 444786677
    0x30e03160533010b0708040e0708010306060602030a0905040b13020d0b12060910020703030b1c3f03020702150901020c010302030f06210f1c030213030803150a0801020705100b01 78
    0x3d03070070f141034451141c0090314100c0d0f10b00b0080c071021075005c08908440e0b11440c950340d01d80011307600d54201001a6050380d8800001d54100f0440c03c2e42c010351012188003990401d603030208444203414003041c20b102d074207114002c0a40c80851000307013043c01604080d4509034103c614040341403407010340c10749901c0e05a4080103030350300540380815082b000e9006040410f00a0900045000c603d902003502c2c51411140b881d070300c012a466440030010382d1203842c5025880425020411500c400c1700060171a10400f40c000d1000f1048248180144a0340407a140142d000d45000c82ca850700400c541c1068000100540c05409200914511075109200792481005045c1d5190b189442d00350034400600c1402150010440500e4824000c0301010000070882d07095000041802000d000e4114290510b0742d0811403c243c010880315401c4000740d2030410540342c01c010150307901e403a003503501c0c50030042841655070084412280000c0c039030410f502070030349076010740141ca21303074041d4012100440b040742c140d1902 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 444789172 1250 444787922 444788023
    0xb060903030a110c0604060503070201060608150d050709090c0311010516080a140c03040e0603030c03070b0c0720030d0305090d0f020102070501020d150e070f030e031605 75
    0x6490b44a0b00003d49200007280c10380b13011308600350110324164440d030840d4000c00e80000512807056824414440100b1542c40c101d08903003001c8060104a1362a8211544a0740c030030314000c41070150500408008065040e810000901c041c40c00c90070440e1030344801d85917465109100d51700f950041c02101c1442e41700b0140e0f1800c482003503591107402c0d003101c4490000c1041c0e40000f6480081040c00604030048002c0003551074518020b80e10420316002045140203410a0120000744600041510145540001f03164810b5480c45030708e007490b018101014128944094451894030700e80c4002d000410406d90a441c1e0000c016481a0281c80055890086c1e07503020a0400c009240300d542e2014403c1240c1c070001d860700e03090751505426a082002500354040e500c0c081103800c12515a440d80041444000d030011528000101910150700300080d0001e00d1784800705204180000d0080b50300940301c004403501d0700c500c9810119560b00c10f281000e1010550044008880d202c1550000e01c00e04c124151440c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 444790422 1250 444789172 444789187
    0x606071401090c0605041404021806210a091101020604050a02040e070e2410020c01081003020d03030b0a060306050a1811040303080f06010302040e04020d1704080f010b06090303 78
    0x52000016400a00e40c0d5680310020750000d41c1c00c03030300440103000d141c0c2c400342c5a60800700c80359010000c0e14500c0b803240303104000702c44034441240c241810f041c404907003683d292007846d11080105100c00502079525142c1c1003c004421210b64003440a10f0b002e45000e032a0100c240005a80c1d52205580103000c660214102d04018030307007a044140c02181030300c1902c201d290303507060780c0c00145001c0c1d44100f0354202e501c51083ca0304107802c010000507002190b5803543d40c007080780c000e034541c007210005504200312400000e012400c0ba008190096034003403c09598101d03541401402066000341c1c07284200d0f01c584000450310720a0080e40250382c0700809400f407042c540031000c51890f0a980c00c1a050a44698000e00c40440c034a000e40000c50080c0c440551620b400308540c0c440c02d0009242c035041c0341c0f0610041c41540110100d40d5841a4180e9031041002c50a04100140c2138040c0e25451514400040c081101c01c030103d61071a402071414000d1082d9840b400802249005e80c0295030b406600c1030088a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 444791672 1250 444790422 444790433
    0x30a0917030d090c0f080a060e0a030c060b01050f1b06010f0f091d01110304060b090f0705030703090804061709010c0522090903052a07091e0509060105090906060607 73
    0x20a00c8502c1340011403480d6075981d13600071140b4416485520a60030905070b071428031190740030390f0b2902d210f0140a842201c040b558090400340100c2c001a0034556142c07280207503030740540b048a003800a80380d4803c2d19105864010b80e80150b10381080001c9000303850001604400c00c844030b81c15541d1328a0844001c909180f803500040c440c00e4008c000d0b0f50808400b1450030a0280b081e041c103800f800c001c080d41c0389010706180d01a2490f404000e0301661900b0200040144a4103445402081a2804a9581cac4840000320090900390070050009900094001440b80d0400340b48041d07840340481540440d0b860007200d41c02c07038000c03085040c0071440c02c101031044040249480518048a103c40c055117070380341d19812045581440c41140459030001c0d24031040c0c01600750700b080820003045195424445802650740b41c074500d00c2020079072034540104030040300d0740051012116850200030045c07131a2400c822540c0302e03000e05c40d403800355541c1004140340403008680340f0b02c81c0c940a00354902d0480e00d41e40342c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 444792922 1250 444791672 444791681
    0x18030c0f04021303080a03020a020d050304020303090d0f0611040602010e121801090b18010e0303070c030201260a02070b0705070b040f17030708060118080c0f06041502030a0917030d 80
    0x1d80000c40f0002000c400243d04d1800381540f03001907640181c40341d50074100a03191084905804c42844014010040113a0340001241c81240013079590070508901c92502d44080340280742e00410083c2050104007000791024003800031034840d58001c0c081071600705081519206ca50043c40900c2004202c240f284510600001503042410f1400d0180180c1d80c5020740d805070040c40192251003055000800d166a001159032100d544c118040c626250056441c000f26880d984002414884e07200100780b03a2107488407180c40ea00d51a03640c81c80107494030300202d00095101c0342003201d40e05c1814011840076403042c4261161b0544c0f050111303280340c50b02e80340c1c2d41e08100b40120480e034414522107112090600b070400385020b1502d98844c1c500504100e000500030340500f1468410030a014601080301030400550040c00f410182e402181c048424004145030344102e40140301d240d08580700c7e40210f00d80c00030003001d00c02c01c640d540c101c015886440c0710040a8000ea500b0b0280d0b80240b00198500c8540d900 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 444794172 1250 444792922 444792937
    0x16031b08041a0702130c031a06070b0a020d060b1c0603170f1308010506120d141303060501030b19060e041e0203060c13170a12030f060b18030c0f0402 66
    0x2c1141011010b50000c4c40403034000d030a044503d6250800030070250b815025120031310710184901e070404103030300e004100c86010314003002d001c10300000c1c08295aa2043e5040307842e0301041d1074003480030703a4030750000c003103550300c466055680b0520b02e00d1400740f569050700c0f4403010b80782d0100d0b100c603458030701c4a40f5480750b4009803410707003514604000301c8451124031401600280b075004000311701031501d00104070344a50768603481d49441d003017000c2402610794808994145400784901d03054035908001d85411036070381c0c5600020921494000040141321014603424481c195944004503400e208404170010b0710100c3c4551124240c21102007800182c40d44141ca1014030090b041005030030031900080e19124041c0d41d110704071840003403c0d041400907407480c00e01508200071800c03410000d08090541e41d0100c3c81c0050320500200c0300c800c0c1c00605c00c1d0040d8003054005001840700b107442d40b440c03c1d015809101c0710030f112801c203030b0003031018107010a003084448002000c1d24144614138007804082e501050 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 444795422 1250 444794172 444794219
    0x30c0501140a1b0216091109121c0c020603071d09010b0405010e0d02031921030b010314070206040b060607060203010306050f0f13200616031b0804 65
    0x222040401c01000a22a02034a000030031001180401e05030f01c0791120381c8820440d000110103a941e45558004502100c04480000407030703000704260020f0714042c142c00154440c0e10003c5011f21440300042d000d9840307984941d01018100300e00020b990110943c0d400a400c14800d00001d0300b1180200300c40b0300c4880302041c200f2b0f040c1403d04001090070000b40c000d030601c00c1d030101d014441944e11115003507000750281c4003080711100507000a551114084e10344190b00310034100800030000001668410000e0110803004418008240a03020f80307a400c11150000c0c0c81d154804a18007145140d1500682064015010507262a11803402c0c0b60802042c194000c0340403c0040005210b610040d8003d500803034000a85050070304a00c8241007024000c1c0f440228103a081c80001d0141c0c0c440b0f11f2141c4d40c041a41600584201565600c030030603041101e41c01540850816524208403201900481c4030341c3e034441c5482d903a0400c25030300c40540c40014000340424002489681c40c8843c0810a50700c100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 444796672 1250 444795422 444795431
    0xc030e0103060b12040302160b0301030f02120a050d0e060a2001062715032001020c1f0809031305060717040b04030501050606030610030f0902030f0109140a0807030c0501 75
    0x2d0850f0900f6a0121601c000b003403045008000915605100c920600300e050807040d03544500c1c105810b0b8507408180400381040828121410031950354001d4294107d01103425100d44c49500d04200303803510000030000010421001d81c21020f89080811202d46516984509a00c0c00003440505240003941014800c65903075004045416003002d001d03004442c00001d04c1212816071b444290003601e04500c00c0e40039200040c08140001420308612a00c11021611008040c29100300100c1c9031000c0e0f1080680c02404034422514042044455034143c5d58407611998001e1303c8501042d5520f10850110440010034180309000e24030303041e002400014092941454504e50000daa001a41d00a92241c442c1c0c8000107002c0040050030302803158046021200c16045190038400324203d08001500042095507864111000182ca5405114015005812148440e0003da2582c5c02000091015100c0300d841d1161407813840c0300010f06d08401ca50003441d01d0301340096941e06403101c0c444500110340381c1d500c0303 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 444797922 1250 444796672 444796679
    0x7110102071e0503011d03040605070f06051003021206070f050c0307140a1b0806070e12010f1a0a08030403172502100e0a170106080f010c080c0403030c030e010306 72
    0x3226200380341e240c2c007002000816407500307007014210b402d01684600303041003c0a08030303202ca00200c05c0e41c0c201d4555040a680c0c0e8000d520348034901191181c0c0082c09246810180104000b0980d004003d891090f07030000a01c58001b500b003941d81d03074200c850000180c0810380e105c1c459482040980103800d2450708480c00d000c0960340d102032014515081c1c0009a04c005c09240070702034007801c1045050b03040c800820740181418019503c0e908000c2001040c4036030070075000c07001d80310704150110700d1a01000801c42ca035a541c2c00840038014004080d504c1006280503007a0034500480c1d440100e882400056251614603526000d814050a58085840c8814080d80044000000441c0c000c0c440320f075580d0b402001c481c410007032440e2420802a003088000381c081d1001b43c64241048081d03500f44010520310040c00b00440b40505a0303500328400600a950340c0811644054202c40c83c01901030b10795941e5561420424106406540301c00740000e00000c2070b20002c00d000300341f0440d000c0c2040c900429810346 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 444799172 1250 444797922 444797939
    0x307021215100b0d1e02180a050a08100515120f0105180309040e0c0a0e040209060f0d06050717010b03040302011410060305060f0a0e010602010b030a080711010207 72
    0x40141a019068005880840d0601074025030268000ca0000140300440e0070040480c0203406496012181569074803540490705041035060504c1084441e025503032600d601c0709100744580e070207000724001e8803821701c081171615002144000b0b840c10b242c0100490340840c94688083e08000d8000400000c40362540c007080d0300c803800411000d0040e1801054003000c80a041d9084500080264100400b41d40c65490174a4000c42110300103501100c001c984400c407d44018180103010b22043c1d44202d0b5140000341c01c440d11060f041c443c9000321610f0381290b403500207001540888600e215407215410210b10b000450a92046402c52414a05849030084900c480e5140d404281c02100d0040004410841010b40c240a6641a0503860b140601142000710b046c00e00c03451b80340034810078162070303100041141d1640da442a881003001000340c40c20390754030342c0307910707513401081c060b2100650070185620480d050005041351000c0e0310545507450007009032214008000400e0055045000f00000000c4249 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 444800422 1250 444799172 444799189
    0x100f1706060c07030819081006050306310b0402040b070f081e030402040f06030b0a020705010e030a0c0308090604020f0f040905010f0b040c023c01020c0304030c0b09030717030702 79
    0x14483c240b05a912400460f480b10038001c0d440c0c6c68000c0210304070411401ca00da407000001211203c4c100180c1725214280001c406088a8241a0070070803901000c82c055104000c500c0c4540c3d400030001c0120141d00c0b4280804d9211b503000d01e403410002007240100041d40c5a15001c00d40e409a030091742000520b10010309240003203021070001010100502c41903151030b00c1508501c8088070000c20160785580da68810f03607180180320600d056070101c0e01d40244402900200041e64960003034940d102c840301d0000d020a1005942a0001038040c4009400d21400007100b500568004040d146104505e004000d1034140f4002d00941050300d454109001031001d0181840c0280e95a0022991052010601003160080c25921003103501c88650b041014411260012402040004c10314440032090700880c50807900811400303966200140c190310404010000e8019a480f404460302015a2014548400e0041c46038090f450f4011885c01c100d0085a0f6420380c1510840c41d0989041c2002c9400148410 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 444801672 1250 444800422 444800429
    0x6010e0c0c0f0a14010c0e0108091014160504060c0204091103060f0a0e030708030612070513050106090b0a1707021e06040c090507050706090201021218100f1706060c07 74
    0x140d029150f500108004810780303059180e50240204146078402400030009402e9482c503238140540500442c50650050014207662044140140078180c01c40380c0c143c840c02d404403080704014028080200a00740710310102c4084a00640c1e944440c00c4e07858003080000c107404442120340805802d000c4285880c2407140c0c034400c41c0d00f8034800c0b09903e02001507a060b40c03002001401550030030803501c030000b8040d609882e00b10006a940d201c500c168140994a00b00040d04025440018181c0c0002c0145254000c1816103c240e52031155046c1c0d1544c0042c903e0180b00042004500781c0781c000d80702c1d0301c00030b01825800300031441250040c0d038462440307028603400485591510303000b030320402007030028201c01d64004107940308080000d81350001000f0718500507200001c3c10981c8031b68848003503a00c200949280da5040d466001d03600d544030a50402c4004000742024011540081441005402684018440c0c205030b140d40c0580f8080115585000000420403a842102403050015005080007607030080c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 444802922 1250 444801672 444801703
    0x18031c050403021c0f0815040504050f07050d021c06110d06050906030c01090e13021e030f0a150209150a260615030601120c18050303040806010e0c0c 66
    0x5030906042c001e0521a02095482d5540c001d4144442c5080d40031005015020340c9241ca00160740b109010255018520648194401c0c2408144000d0220100b003ca040703802c00c10442e0b64955a900902200c1c40306820040d501c940196002d850103070f401120002041d100f2100019000352180c0000010380000c07103040381c025500c4000340043c0c1045681160000001c5004280c03408084000800b02d003400d018540480c08000d01046a01403003550030791089600a2260300016031440e501d907000e04034022224031078400d441804841090100e812500b00790803044500c1055440094000603500c08403c95403c003581e0b082d0452140101c40c06001c4401c103c0d40d4803401040100301b80d90f604078403905c8800c80b001205080c071505584228031202e5403840700b1007040d00da41d03806d00140e40c014907160220206c141440d201383d60141d802504140d829055480b00340449480d0014140d60b400745000b840007d611800050249110300c9000b80d5020800c2544186001071903e0f81714209001d2520301c516 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 444804172 1250 444802922 444802931
    0x9061b11070f08030a05070f080708030604110a0e01050901020c030703150501080609070302131415030f030a0e091512070501140705060622091110030203070818031c 73
    0xc03609800c1c403445004001180c4001d034040d04110b4007035120b10500310300300d007403220000b96142000b60101051070043d40041c4d20356100c0e480c50503d5249540100c48092040d49851040d20a0b0b400b540c090b64000b141c00d6980d40d007074000f06001518a41d01075000305056225140402005070b0381002004099440fa400c23142d114030650124000391081a002858a03401c00810400c5030407000a0f200112601110700c00d17203540321680904010051040d2000414441f00c04107c0042e1a07842075400c410025400c507050380703880081c03587d2039008401c0942d002480a000d501e0076890403443c4181c20440b11119124118100d4000411200c410381b18105160803811082100d50303080116040c8240c0103c2c1d4062410031295511902e40c1c0c0d00030200f42c428102222405154001c01400701080c0907040030812410000c2d0404103405000b400400e403051911141d07100e07a0a120b0f000340d03070084440c0e40f030f208226242c219081c0c4a004543d00e40c4880c030301c4207110a21000d0811495401d01c040075010004 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 444805422 1250 444804172 444804197
    0xd0207031706100f050d15080109050708060105151c1b0e09010b03040b0907150504080c0a08190f08030103030c02030c01090b040b0c190b010e011707030609061b 71
    0x107407004224520900462a40c4084a600321030600e00c01122894015a2101c5411014000709528140103a0b038480388000403a010708154000e00d019801b51044400907036868400d00d954035424020190406141d8551035504000b120103050700c4601041906055811f4050080c100e9100c001a264440c46403081079035a10b0300000314031400041034410003415810a042c1418520000e417000305086c03c2140000c068601c244260300107001500d0070050040350110307008040b50000d0060102c81e000e6200401003500d481d02c10241164140f402802d039580d00a1f0740080c103855001402d0381e00241641c500000121800001c5020758825101c2d0306110301c440c0181403821405034045030500040380da0500004c41070034252802c41e05000c0c01507540381c1100703110314101400e45804020050424048400b000585103845050342c0d002c0844148982c0d0b10300e0080300704402c00050b41101d070402c2100344089200c64006c3c0f101a4011000829910614860305c2c010400c204021000a0582e10034031 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 444806672 1250 444805422 444805457
    0x1020c120913020301140d03031508160f0f030204050408120406060f050f030601030b09030f18010206060117150418030206162c01020a05061f0f150e04020d020703 72
    0x30518184042403c500310342c1030a14000101141c0e0918504c181d0001c0f00180030988a604880c4400f40c02e16003051741644d450b111383c0d96602c940090310314a144002c030040f51008200e140c402c2100c2c015175684c10010300e03580a1000404001c0d0090322055400c1184001d01b91201d0500b80c0a50721a21002452034540b500c900520407150b00000d204254601c2d0450907568005841d40c1941e8200050000b183c51340303a80a4614407e18208001c15000414041d1043c120780300c428071030480030307003d8425a64504004440400500c124070624001c1c02d004940000f06903540407204150150002450500c0340b00180502089008220b005901200c1005500302c10710300c40d920159100c1c00c007c2040c00c5040d8100c20407000d40603000034034121070071a20713840c2d80c4200400395411360003100303581690070800c01d041d110110001500350583e012403000124260000149401c07180c0d40746921080c00c544440885041b1140400c00398400e40901020060003038a1004001451280e141c021400101c01901c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 444807922 1250 444806672 444806689
    0x6010e0915070509132a110d0518090709030b07030209040905010b10030608072c0915090d05030a0b010e04052d10181b05030711010507140c01020c1209 67
    0x1071090242070843c1e21a4504600914400d000710300e060400350340c02d00d0030080f42c0121f8100c100e42c071507100311100402610b8015000344044590001400140301d202014012112000c0e100c410004038403140c1040455864207046030401c500d40f40c003514240c100381c00101501c40342a8180e45503559440c0c00d5a840c5880580f00340c2c00582402c1c2800300724075200030b168a8240340e01c548408500c001c4052544200c121000d070315a104000d102c60741e54248184d40e11b66405503580660303441b56100340840c05415002a5000070310311581d84451540d03660070021005440350600107814000303204104281d640e11401151b01ca0056000800400f14418216409030960051500a0000c51070700384252000c404019605903500070841c4043d003540017000100074403032600f142e2008071000c0903d03090750ba484401180111003650f6407100651007a1109401c80b1025215079005c00c44108050181c030650101401030403246900040c140701c0d4010710241040c3c0c80c1d10032000d2100f80010380c042a032408041 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 444809172 1250 444807922 444807949
    0x10b041b05070533100501051806160501090210020c030601050418050d030c03200307030213030f03050316030e07140102100f020d0e030a080a0f0207080a110c03010c0206010e0915070509 82
    0x401c5da4003454440082c003203108400d00801200c21b207031107030b03141034884c40c0450369100c4a00d2240e40700740c50030307003441c1d8007d240280b02288511a001d107a20300e19880040c0000c00b08a00501800c0035900c1c140070000141860040c400c9040000b00000d40402d034140041c00f02900c003a20007040400b4046802030490380407001070348400c0480300f241c03401e5070319400959038041d0140c140140d03030350050b021200e0264850b40c4024420964103000350b0416500002841c007502e032043e003e2598407010308003a002d8848800c2122841d070b00c4210100240c401030102c004204006005440300201c0700e1406c40142c50802e130307120146a40004640d918902d40d40700f0b130011512104081e40c20300c0440304004000303050103040d084046498120003c8039005c0742e41203c0425030b11107003035030380e9404200e005022211104030405044c000e054842c44035040c1805001c040c000320340c2c003410305c582c00c14050f0a4061000f07418050310f841004444003102002c800c046020f8100303034454603110b98083c0308200e000001e044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 444810422 1250 444809172 444809191
    0x9040c170910050c16060e070512030901030506042a030213091505030609060f0a0b120c01110714011101090501090f05061b0711030c06030709030203010b041b05070533 74
    0x18030317004155540701e0307101d800307a00240c0402e4000005855926207071082d04a0380e401201034803050754542c0008000c2000c203400380c80c24041d07944c42008102c2211450b14205182403502000c151425040740031a8480c14601c1c280142030410180000c0116007440e00701081c8a40e8542c1c03502d603d4080715a90200801040b8000d025a11b07007140419243d0902900b0000c03860b0101000c2031103190f903074000400021000c0c240740803000100400380e507100220303040c9501103445006c032804d80300030200d424030a0301e05880341a1035825000c4d0046500000e040d903400c4141d540c4012080c0018000c0c060400c1a60040e0458150241c80d400c2850900302c01420904d203185c00d20840403448500d001c00d0f40c1c50070f40c01003815480e4043c0840401c0c100781c401c0d54444d51003180081080030b00da400071114800e07240264000c0142620071401d1204551f048031541d183c8160344003801e820740707214100030000307103100e44103485181c202030002895641001c4403080340c29400703103010036291a44014650380015040d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 444811672 1250 444810422 444810427
    0x6050a05030d0915090b28030e060115050c12030405060a09030f141209030a0210050618061203030a02031501030b0a030215040e0a06060e011409040c170910050c 71
    0x40b04040c0c011040f9200707816010240305950942d0300c0c09080280001c144034401d0544d5084000300c580d1081409000c2070721010380160315030b2480b1b8401e01c120362800079080014007441e400c09040b00d07185020f40b0805003c0001c100603851800b0014084801e01d0022040c0082d01c0b03040a00d0030f503007425001401d008425107882c2c2e0035008207900940b01d6072404960b00b84909603403483d900004881c8125880c0e004002ca0324418010007060000003820840c0d01d42d401d49000400c6e03044c03d0340030382e281a100703954802c203580c1c00c02c6200100019401c0d00041d000304003181e0155480c042d20700f50340081385e040380101d0b4007000f04843c400640109030081c01003482e0400841d2500000162040d005001c068041c240350320401c900110380130b085801400390b401c1e5040e282e103031011355000034060501520380003508002c9904055406984244000300d840800c590406001c10300f440014803001300c0190800944407040144104800d04983c00340c00824054040584020030b540c055510142109000070b504 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 444812922 1250 444811672 444811693
    0xf0708010c050f04030803070c0b070801030b16120209240702190302180c0903070b0405041104290904231b0d02160b0f07020f030702062b050a06050a0503 68
    0x1d00f0116020f413640400140c1d229110740c181115040d0030104020700400c041028021200c1d04030100d58122071080010300e9165079008036640b050410540d80d00c000c20784207944014072841c641c0107000d182d68041c141040c44010301c0519044080d40f030490149007000081d075a010360601501c1501604819100500b03c80c1c6150301146000300c00c4850054000d880c98041800e200078801202d10041d0010304480a01d501d40700c002c4550b6001c5c4c8100c0b407160f03280040d00003030a10341c0025102140c11f000c80700c074070070005e40e03641c0c070050900c40c0e9400050000400c00003140390350300c0c0b08909808002c2c41003010042c5181040003108400500180e01880c0c040c374014200910402c120f410f050100301c00503840e603e1000181444090401000707007500c0fa01c00800100001d0690103070310602280d401c80c1e16841c01c000d2199128400e190010b5001072042254041040c0322000c9050130500d07095440640031424a178110440d00180d800450003512024100800d241c4640d061001d04821005010200e05 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 444814172 1250 444812922 444812947
    0x80702100603020604051309061d011514060c010f0609020403110a080601050d06020408010e01090c0f0501020307030f05160507060e0306011d0c0408030a0906090b0903060a0f0e0f0708010c05 84
    0x602c2c41003901c07400040414982400ea523402c00f0038201d41c000014011a01409181c80d0350714600c11030f0200725032805017448038106402c03180e1000c80d658860043e4101d400d41007801590740c040c20005401c1c0d9250518111540f0181c0b1a001c02041200c1380161514110324104d450b103007995804920a0145600c1485500004280207044a6080b241d401400000d407410802030f01403a41328100c43d51800b2000719101c481904804007881c451022521032a0f1582d010300c4a8020364052a40183d10601852300028020140c4602680aa062050401c1954045440c0540c48904101e8058004039020460540c0040c801e1508040071009009558180007002c10548100b004011f090a00b200104420702c00f900101c034094140c0e8400e90f40d81d800018006017800d00c0d58030035440010b00e9064002000110b000c25079246610041c05070403683c480c860048007500b640038410384000e9490128043d040d404100d80110a809030026000e05450403c0407805c5404018a03070003800f1003003205103420700 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 444815422 1250 444814172 444814177
    0x7080708060409020a0306020403030e0d031413030f031e02070b0d020703110312100902030f1f081e1506030307030c050c0612060f04020a05120c0f03070807021006030206 75
    0x8405181003080c0380e03224400100540388101001e90006a01c1ca008420700c4016002803040e24000d4448101a02810b0144201c02165440c003070001003084146002f0b9618040041c600303c120105e16000554a0361500c41c4521400c080c114082065803040300352180000d550020780c0d40f804e001900949150501c441c03054428413030040423655001540104050048102d100c0c41d0b030700d41013141c1d11541552409000120241d81121020044540000d0700000038002c4a01c00d41c0d5102d5048840d480d0717584d040034022003108500040031550b000119035501e04022000039a1b005a100754215a00b00380045e0900b407a4420800780d441598003008400e803800001c1725030700d170f51625280c0d00d02e04a9040c05400d02c100f0180c0c542d0710002c00980035801c6500c2000440c0544411926110303522101d80800040340301c1d40071107401084080c031203001080d907644c0481e9448001555068500170a41c0c80c1d00c0f0f16079008880366000b0500d42c000f130240316981000760841e251905003040020320b045400241190 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 444816672 1250 444815422 444815431
    0x1020a080f160e0303070c0f031a0705070803151018080703020a12050309040c052107120c110604080301030b10060819020c01060b04150c1106030c0c0609010917030708 74
    0x50491049a80d83d2010402c540741b40c0d4100c101c04080b036489501c4101e002d600c40c4415114060700b02c4e104400400449001805140c460b101c481c80d08009646103140c3d9040105071400c0044c400c490b40f00d068a54801c000c03e98030103035540b04140c15080203149004c040d40d03004001c0781d5206050620050315a003181e4410380c3c0700240040c03042c241e945001c914500ca044040c07600241000d9050f0382a54000340174200c2a100501d54985155243d6089801c070a000c0300d1000c00140e80c1010f41c40a5041c69020b91460380071450116034105010b0501840d181003070700c0449080d140040100140080c507032190750010340744c00b107a02c0b9007490050010902c10700038003904048100110450030b251020760440d54800c11100084c4130681d0b5401e408000c0e40c03c64490380b410f21080384149240b09114148400605070703c0740e44080c0c1e501500c800d000007500010b100c119100420000c80064902c04c10000e880340d0700510001ca030312000703031810600e003000350080c035400001c042c000c2c00b1800e500120110780c0b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 444817922 1250 444816672 444816677
    0x50d06080c090408131d0610050c060106050f130e010503060f04082a1501180b030703060e120c0102040317090904200607031d1c030e040f020a0201020a080f16 70
    0x240e03a4008290445d02d09907521502c2201d001920b1440103002036004a8441d1208886a01540300301820503150f40c42150002140798101e44018002a0b0140002d81b5000c07411207540c50138580e40020368881d00c0c40700d812816003207541400401141c0b904003c801da0284080324410b10a061941c1c070181c16003d00005850340740d2202840040e46184550000321380000711085801e50011482444124034007800f42d000f004c015042c407100944064019207015001c090000c00c1480d01e180c44400080c15060014111401801c4003d0302c003440d1b4401030000d00c08460001a900c40c554601401d140025060308120814140100d580381c4c6d84606405621130380000721545a00d2060454035412400192560380c0800041021024182c0c044444030b0603521a54011703c82101807001c01013000c84000384103508950300074031080007030701c281900000080054804200045031240c500c007603800072a5401c005039408100f20307540e0340e40300b81ca442d0050302503d6140f00500b403402e002e1240444180c1341005 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 444819172 1250 444817922 444817927
    0x50f0d081305150703090302011a060406050f0424120605010509061308100c090e01050307060f020a020a0311040c2a0f140c010206010905010b0a0c03020c0a06050d06080c090408 78
    0x1e02c201401460490300c0000781c411801d01d00060b000d00100388640081d00113603e0032021030a43d0070a00304c25480780ca00142000d083c6445c00c0c0085900d6400104030305031b440070503c40000c0c12103140c0a0120407035081c0c080310040140600d40100341c002e00c20020204541410030801a590300081112816101507401c0c56a906c2c0c0700c06180480b00c0c055104103150304c1000d0302c0d040401099030025800c102296909001c85958420190300d1100a02030507500d0b41166000304601c500809045c2c1421a480c010740b01c1c0d174521500082c070b0500544c0d00a0700d101701450f0340502546041e1040450307404950500c602118038201114941510f070005070502154010002014030007903203100c6031410392084d000c80d0302030f0a81102c00c1e124401041e030a03015214440020640c40050300071181a54070404802e414054044411681240c08080541c250b005400001082e900c0d821a40c201615290715a40e6460302c010003000f040700c44640c408012030b0040c10a8403034034ae4520001c143c01c82c0c0c003d8013164 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 444820422 1250 444819172 444819211
    0x21010810110414010c1b05040c030203090d05070309180606030b0108040c0e090c0415031a0c09010c11040c0f0e01020313031511030a0606080a02041212091809050f0d08 74
    0x8a001c030300c0076401b800300f400d07070080d4000004164120f9030558009903400d00110b080800305030117070300081d12001c1842d0455490741500758031900142c62040d0080ca413807040f4964425000b540803404081c040401c030b0303c541c2c0a0003025014018400c80e00020301c0c120119141545a41c3c41038105805503142741d4001d0004606540010413440036980070040c0704001c1104060303000900d598481c0300454880046440100c480d6000b148a14820032410b040300d89000c1c011001150300d4190800112103030310704035041e441c0c42d40b00c601c01c580c100301d40307a21440300c0403200c50000b808215190f02810304560040081c0001001042100b0040f264040303002c000c0c0e55010540400070b020082031807400101d005c0100b044131380c103e0304070350106d80180d200e030811501d500384401c050b8481d030300400e0804030154202100251840050a111101600d48840c9043e200c01c041c01c1840c00743d0305608051500d0788443c0041c00700922404814040c143c00038195181c0410002e042c60300010540e4010b02c01c28840706 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 444821672 1250 444820422 444820427
    0x1409060610180b0909060306040309150c060509010b030f0f10020f090d1a01060512150f03032a0303280f0f14060a0308190201022101081011041401 65
    0x741c41080c4140c031030b40c4195840d100078440a4200319452481089400085222030401080302401103405981d004401d5041c07501c1406407840016405082000094030400071403450701c54180103c2c04000003149120048d0100f40c0b42c1003c00510301001d40100c035180c0840c0700e0004000440400000300540c0b5003484010f0007419000300c1028903040300310b28045404106a011800448010304140928140d88a110172500ca008031200d80c11005454404100d01d116400080140194018144a04a9011400310b810f5400400c0041700520103510342c661405500702c101d40c1900c015030001e500710f00c0c11820101d481001c0b1110358809184001f011150307002c850700010140b826605050207002217034000301d001400400850b2032010365801c0810124a000852801100c0e0044099410221a8620400c00f04d41416842c8251365003000303040321607120300c41000004100040c041d01158540071039581020040d8948003946494910142000b0544a007a5001c3d9040c6003000c0c1c3d410070420006 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 444822922 1250 444821672 444821687
    0x6010b0a0e040612080a02060106020a0c0b070827040f09020f0f130c0207050f030f10050c0c12040e07171501120e060405011b0e19030b07121409060610 67
    0x14420b680c40d13002403e0140704162000b002404015030884455a0781c0b0001281ca6540041000300782c404c14030420400f000b100c402415440e806003030314600e0305152084040b02c048642c0c202c05040c541091f26003216241074810140b4000030038509120000c0c2c40e42c001a100d61a1031042c034403905030869101d001d61140000300a4014901c4001c1040b02d4007014080e60701d080318070034184103000011003c001c0d41070100c6d041010201c0c4d000106a5207080110040241c0001082c04004410600c0341c4248014100504040281c3e402d4046a4036401c21001030f8541600508480a0203015000c4032941e011003401c0c283d000b0140b040001302c02d5070344001200e080109440020f40783d0b003002c1403444051000700742940903612480081002e20715100c011004d410f1071080803808242c54400040319401c102149041e841d001c0f00d035201a007516a510700d0b5040c2030a0b6003520014640400d0009509864800c54610442400051104d4a040d4580e0b40e40c68200900c0d4034040c40000c4402c00a4900400300c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 444824172 1250 444822922 444822929
    0x1080f0a0e030a0503060f1804060c1b0f020a091803050915030708060109170d030b0a0305060c120c0906070201050c070512030a02011b0807111603030e0f0306010b0a0e0406 76
    0x2d0b29a07994620300020101e4106403911442202088041134a038904200031802d0198011300360f01e2642d6490302e4a500812803018501c09101111145000441a03c0c0c184468184281c109610071110380c010b0001c02e0301583c024419461a040144080200422401904552501c0c0070b683d01c00e82c800c04921941000c1d90311410416020080c0000240c00064191080c1030a03070720500401c2d503c0e101e40030000b2489400d4001c54001708030030202c452194100b068951800740c1b404420568070380e545490110b0845108106140c040b07240d00d803230f404c40544c540d007251f0781140d12401c040b0b44c103001890500c00c09800031306205000554822000e400e00403200241070090026000d08041005542c03207038880c0780154010b528180c3c035001c40c1c600000341501c4028241d524040d0743c1c0d8929905480c1503200301000c160601c80d08501c078012201c0d410a55010b948217641d1050078035600802d111003800c4160901d4801e821800c0103024602c000011b40e10b1910076071404070103004545000c2001082c03680c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 444825422 1250 444824172 444824201
    0x1415070b0f01060201050f060603011202010c0503040603050708090f0c1e15040503010c0503011d0702070e0916090507020d0302090a081207031b03080c0d06090e010c03050c0901080f0a 81
    0x40070071a1025100c101c0354102ca0309900280080e0f03460110030f200ca40003c8030410350040e801e0005200210928000448441c1706040c10105001c1a44030246103400990220700002c1d10341c030800ca02194003240031034000460000511113816182e0300c550301c900e650709050780181c11410450b2402001c1118090040001510350a11503404240865082d48503000e090302170740c00c1c03c0f08640b500e441402200e048a02424029a103207840003211800c801d000760008013180309290001c1646078131511300c24043c181090007004041c800d04d5003014882c1c0c440e4400000d0a250004110400e034000c55104601101072400694800703540001514007240d581004256104000580003590b00500040040d28001c2e194110031070710035124402024400d1034010001409400443c130b1080314000603101410618502050003900d54000c202168a0080c503460b0b1a0b442d2644040c0c07094040c401c0c260002c5140075090300d003916504c0040c01115001c0c0501103011710400008c1c0c142450356020318820003414 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 444826672 1250 444825422 444825443
    0x10519032f120705010207120c030b06030f030c0106030308070306061b1e08041d04020a0603150e0c0307120606050714190803340507020102011401060306030b010b04141507 76
    0x1150925900c2c0c3d00c600616001d40b00303003100401c60411405200d29007551200d00044085d0441e0b4903507010000151001d070b050b1140340300307140d404c003410b20107000c2c900e495a000296052540c200140400030203419002850b281940174400c040c0e100380460500204141d07120407126442c6420310310a1495140314444036210a203034000c0205a2004004031a207010078010b141421240784400848140d070300951200c80701c682004114046e420074440b19041c8071005500c1076131403200d130000c100e0899000341d80c04400820080d0581d080440e9504049403940100021410030f01c2c094818818000d010f4000181501c44400c0e10b81c4c00c0154009601408562103900800c5140c0804580c10035190807100d01d02866041000e042036001038840202c083d00c04003031600c602841a1420390210409a046540398800e4040301010011703070307034000e10b07041d503000070084c0c9941807071500400c040c0c2002007003c2c1c081000308980d0000020070040303148101c50f19451894180e502c4d40003441190001005000303903 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 444827922 1250 444826672 444826699
    0x11090c1314060a0f09090c050c010e0102040b0304230d05030708070c05340801020702010207060e06070803060609030f0d090504140a1e0504030e040e010203130602030a0b06070605010519032f 84
    0x4081c01441c0c412704c0c005c1c0003e02c07400904509034080c500805480b80780a00028010440c41c05c54a0f001642c20f2034050952040c140d4050f040c00010b11004020820010600401039403005034581e1005091812603010a0030740d0345d860302d820681c42405401c0031000c0071203a401a40340603040031641c075040c1c0d2034000782e0741d047c2640c041d4205880603400340c0101c20001500c1c1e4050814040c403104002c0c0b50502d02840c0799920700281d00054940c94100780180415012500d08000c4101041d00842c0207010b03011030b141c00204880c007541c202d20300940c200300c5000050140727001090307000507100c00c0204592610b80e60101501404022800c011400c0c00d0600003407503084030305010000b10030b45003444420f91130004a801d07032000b6146542ca0010406004010603c241d000c0c541112186070b010811000700c1c0002039a642114a00365030f03a681e42d81c0100020300d45001c0f52450344141c0801136074640d1958490001c05c0c90460250811100a800c2c2e00e120640d410421540380c003c001c0003034124620 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 444829172 1250 444827922 444827927
    0x4050106030507170709091718120d0804020d020f180403030f0515102c040629070507030804260105091911090c1314060a0f09090c 58
    0x36140320554041c000c81a000c0364401d030020249019080010050880525001c120340041c6081b00e401e41d40d030840152003040c0c03031030710780c00422103d4094808909a840024108140c0303004180b40722143d5800180c0780c61643c0d41200110b41d0094044900e056601d099001042401741d038164010703808044400780005805a0000382c2c0e014074029542082013810300c0c80caa03800c032201950201d102541010f0382e8192407515045080380729183d8a050100e100118202d802c80c2906460314082c03000300903150b03280d40d0401303208020082c6140d0400d0321549a5003070812a41c02d0200b07551050036640001c803002480702c00c00600004551120320309030f50320358800034103c040110006030701802e80034031075810344103205006450080d4913800c0500b21150300d2008490900a5103001200c1025004200400c41c0c0d680e020601c1c03049c25003500c8203a13034920505c9503800c0c1444070b8104122044c42c00301111110740f5913409961203c0340c281480f41041e220000c0941d207400856018030343c2c0e1800d18101c00030381070307 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 444830422 1250 444829172 444829181
    0x4230612160e090a0b0f04050109080316020f010203040b0c0c01020702030d050901031b0e0613090603050f1203070c0f05030909090102041707120b10090606031a010309050a111305040501 82
    0x100042d90151490319241c2d501900c2d05424074003d032400c2100d4011801e100390070300b103403500b0038401e0340001a503010070781e1400019001101c40d56800c0d0f240c1e882e614500d603010722540a0483c0c4c0d0f00021071940c50165940300e070301b1802a03c800310180300031410006640e025411556203a400070100e4900d030840040040203070b070204070424002410f140148403615003e1100e405501e50700d4462074000c401040510100780c0022100440c0003d10550008480045105480145006a01804c0b803400d0030503202d45020092002041e07584020010440c280d58030540242051394080c006020480060400354658010180840c0c0e100c50304809008440c2015030003403040b510300c01c6a0201070303c1a041d03040c1d152075183c4115070600103802440380003d03241500c480c1d40004105075505089844226400031144150400030100303a5941840c510b9034401465405501000d103400d10040116543e0a0741b41e42003103a005180d001e6000303000a26654100300740340c01c181c840e84200614901402c0c458083d0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 444831672 1250 444830422 444830429
    0x9060e040c0803030f04030f09030b10080601060f020601141314100609050315090f0f0d180612090201140d14060102010e07170a170a09050423061216 66
    0x1c0751021000401c201c0210030707030303100d40944000722180e5950341d202a03d081f90140d00c814100800c1c4600880015100c0381654051031034004040045400e1824261074194181c103c40e0501950448640500d60700081183c107480080760000c050600c0040800d107055101c000c898880c5003050039401c107104403968584d2003807402d541034440c0a44c7d581010f89040445000d480d406402008c18009518000d000b00303030700b102000007156803250320500a1800d283e0b00000c8080d0a802c254040c403020356010410b03007140c240081c54924002e00d4850060110900c44203031044158407410500305580c042d90100300c000c03044400082d17642d026001420000c0040242c4540c03160511404a101e0354414482d000700b40040b00028505035042040410380352802c20f5081d252403003540c107200009220f0394200c3e80f4103c28150b200383c441d41d05000103043c11842e500100e01491030060103044150031520040145140c80460401546502d00822070001c01c4402c5007110384507101007005001c500b02001c9044 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 444832922 1250 444831672 444831683
    0x10507060f230105010e04020705070308030702061509070c03080916080c04060b03060a18110f0306040b12060c0d060305030f070312060b1b0c0a080c030c0a03080f0703020709060e04 80
    0x210380310068038000b8a2821301a0500103045030440c4030710b03814142d00503c0e00d2405a0121001203a032a900e43c04254421107031280113070030074024060381a80300d101800e20400115211111482d0040b001440008604e0001d010020802c0c0840e5031a0414440180482040c5d0fa1400440d6150040782c0d5a41d043c00e0700c098050b42c0303400000614081c030002940e0003490018602e55561340340208407901d2400d042151408241c0d03800c1c126221070101301c0103040000080690340d4482c908442008115850000c0060007244000854500c1c8000840c001d5800300c101d81ca520344840e030495003d0020440c40d000105984000210341800905540183c00d001d48030380d9840c3c00000f00c03c103100c02030354003d10a100d8120000d0214221031085280c4004ca400043c104440c000f1021030b00107039090290340d100a01c9074022041604941c1801e1050b9008140143d03148140d09145680e0344010784600c1e40780604484000c0b80030810588203201c10300c01042103150038030065440b281346104075401030720101ca0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 444834172 1250 444832922 444832961
    0x140f06180d121d06090d080c032a241e01090203040605011e0e0a09080d1416020304090b030c0d0b0f1513090804050d0309031407080714010507060f 65
    0x40758003010030300010b00001d01400e003414540020700858681000044070100e00c03d0007c00f23410081000500756202406106075524201c0e1040340e00c40c000c62010412440d04076451100e00c1c840040500c40c8024030050020780c103591214035a280526000c6008411000c03104c000140d80c2c400c940186000d07038000c41c070410040c0d90b620b0843d08800c40c07001c5136200c003d00307000040055044058060303922903440c40d000325080e03045554001c1c0d81d038000005901d0319030761100c0e01000c102440c12000c2d8460315064490a00c1c003240a4007944d00e00840c46110003440d2500003401e0785441c280303c2c0307050015026060352240390b040d10340f0307a0840c8002c4a14080c3c2c504454002205c01d500f03045441d503034070005051500c020005a1060001e00f18024095903580c504120000e1161241c0500d20720850080d901d00c4651819032a14514100c2603a210038041d600004052021120102c1c107001118942410000300e24090b0005856a000d4000050069131030861080d50740b6889801420310400140c20054 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 444835422 1250 444834172 444834197
    0xe0a0203010c09080a0602030406020405060423012f070e0711150f01090e0109080c0a0b0a0e0606010c1b030c03020112060b1b1204060306050a140f06180d12 69
    0x441000f01e0384138000460344885240380220700245d005680040c0140d02c05894141c660f0b0202c0c9190b400369024a0b6400c0244003a4110500e0300c1c241c92035201001d2070084928a030441e403100000c21b0343d02c01042d0245100b28207910003142009104002c0a51030100000c0c1c0c58920700180009001d8000c2c610a4002c0e207038000c00c0581c420f400c05100c1d0610a200614a9003004200002080c068000507041c3d0360380c2c051100030400a002400c03030504001d00420f0b18281d146850009101c01400541c0304030b09080a10000020116145030f0191082c6080741361030b0000c0c10708600046000405c0082c0c014070780c0b004024850485050b01c01d0b00d000703880c0c60700c5400d031070000304084890b503201d0144034071410710505a4038452001c0f640180c1c405c00c0c0848054617449212a125503110358400d8001c07903560002081141454030040c2c00070107426142e1204070074041c000c2954a09800301d014852000005c01e0003452881ea05403100b140c1020f4a40d034000318440c90a01d0300c2c0340c0038110740c03c0410592000e11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 444836672 1250 444835422 444835427
    0xf1005040302100f020a0303051e01031b060e060d0203190f06260606040b01050904051f061107031b231e030705300d0f08090607080a0e010e0a0203010c 67
    0x4000204a03174000c00a140c03039a28110001c2c2409845e40080014404140e4001180b50700d055000e50f018084500700102c40807120503075925154001828031500c0c445210299581c407050721002ca00b91140581c0d81d9646804d0b00300303040290f5441d1600e0902e89542c2150320085e950140c030076201c50300602c3c121038002e00850300c9100c2540303a0307211042c9d0001c0700080a07070038643c100c4c00d4008018104927050040800c000b4040e28800c641011648403050f1000850b01e00c40c0c402440240041d0400702c0c484550b098605440e408a40800741c1012114240745183c0340846003218010100c1d08081036400118032800c8845801c1514003038481c010304030000014100651013000001070080080c00094504810320040e1041e10341d02d800c44028501258060340074007582c80c0c030400723829006400a60000c88016214000703800700c61040040c0c0c01d08020f04020002810b54100300b00d070402c003801c0e940340c00e5000c1c06010590711029481d401c040281f182400000340781c5058500c00c030000c1c0a528540b0004 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 444837922 1250 444836672 444836687
    0xf05060d08090d0c210203010c09030c1509050d0b09010b01051c240608010317030708070c060906060b070314070c06140c01050103080703120506011d0f100504030210 73
    0x502500070402801e26285405040d950ba55407244900010183d41c41c004ea10380c0031524070078028400301100354002145401c1c8179100394103271941031019005003952640c1ea4a09000d024103250b400344101c020a5050280e11100f0003080014005c0c00b0b0384482e85403c00302044d058610080641c2000b0303070000c02d580141c09856084100c1d041c00514000e402e1080c10160010014114007001d400440940d401030100c3d0000181581e80c640f84855450741c03030017415901504254008101d018000c0c0070050b41d006100ca90824050700d040300c00d990541c00c0100090214010003800c05c1c0c5401c400080f103101410207030200600940f00c03d8410020042c2d070f0f8400c2d110701000240030031300c81403007072003524091070f528030310721050340740440c100202110628210f130400e8000340c03002200401c02e035040542c082c194070b0300c1c0301c100b4000780b1a5040c1f09001a004109d0000248071307181e0041c00603a45901d504102c0a540c0d5402041245a01c00102c0054010f0f40203000590113007484d00070180070035010307442 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 444839172 1250 444837922 444837949
    0x61611011b18031a0f07030b0607060506180a05070e06090a051507050706021c0c0201020705014a0d0503030703020d090203030c010e062d0a0b060d0f0506 68
    0x1e054005480c0c0d40c2102c2c5202040301d9038110718202d403008008504144054819a2160350104446042010a038501598000c100d002018102174039100280c6030719042c5c819040c2e00440111b8151102030014143e00a210340c0f0810780c1401d4810400d061800c1d400c828020f200545810051111500900646214211071150400c03c2040104101e0400b4240e040e1044803d056140c01e010321507507640d0800f2141e601690041c1e00c003510403903c00e146013410040c0601103040c000c0d810320080c0d0010391aa640341c820903040c2f001d02c001c0d582d140c42d9403800803030300c1c68444e14044440f641071b41d51100d035021564422058280c0d0200400d4141e041c40b000f00801280c0040003581950b07500c01048001c3c2d400b81d8030340d90310f0070346510b500070060301c0400250440d81c038040004610407491131a554a00600104003032140458400c0c000c0c0c0c00f00c00d2603848802804071650104c22641c4490aa4024001010a0a03004540001c450b43c41110a500c10903c2203449503080c00b15844540810401d10001c04 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 444840422 1250 444839172 444839201
    0x130201050f09041d0601091109100f02010e0d08011707240c020a0603020d0b04020316030e01182907050f160507060c0b0c03010305030f03040303060806161101 70
    0x2002070150350060303024140b070000040010a80e80c005801c903619a41442900a416034883d400500032031140b40600c100e01d0084400b41801c00d245100080d00d4418a041104203111000b007861416034401e401c10030314a8014400c840f403610f1a400c000b010304c0f4003440350240000c0c1d807034004107410201040ca4006c541003100310300c0610580c0006510340006a088810912035040d1544006845400742d50b0001c3c255070f00e005842d1904e0a85500a403409400d0b0b49100d54030420811a400b90b10003a2210819054940050100c0d0380a601034010003103d04c44207040c0350f18080c40e4003000150380d034012800d030000c01018895810031031410001d083c152404000b00703c080c8081c2e0703644440b050103041e024401c1c0d411082c0203802525000d003001c1d1141c005100060400f2107080500070100103258201120794546403656142d602d404d510b0703000700310a0310300b803000002c0842c044c14841e40080d001340c5610707024ac0301d950624904100581c0c02d1280c0c0040032640d50f480601450070107210b40441004c900c0c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 444841672 1250 444840422 444840427
    0x5160b130b0307081b070b0103031101051b0a030f060302040207061d0613030c052103100b25020613090203181903080a18051005010b070305191b030906030513020105 73
    0x40c800005190240c49040c401c0c5d00c030500407036001c1601b411030540214000d89600820b00c8a5003111800d41c0c00c01454048200616070b00d0b0911203003001c044903a07001203468002146000704605d030000e44815400030754000c1c00445c004042c80143c0d80300c9400c00b1124040516000407034903041c0d40b030b01c0040315003150664110f48410003103405000801c01841c13055003500c100b03044030f40100120080321080e4003442c0c0070200801c0100d03003030f4520400c0504040c4d0391150400040c401880e29002c05030400440081804040c042151103800c01d03600e50443e0709840b035050381e481d0444a0001d405c111025140c1004009050781c0aa13000b0500d07040f41500741c1a10800810641c800355216540540390034802d503540c5960814001003407001c40c05036803083c1d0142c904141e56842c0c20303003a13030810b8100c107074174040c204034003000a80c001d4200c4000389281c0418030b96001c046101503440d4403d40a5814181c40f00ca8a45010554892140d00c240c2d09281c07420000d80d00d80801d00c03580c039000c204000340031a004 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 444842922 1250 444841672 444841681
    0x503071409011d190e06070f0e1e060f09090408070308060603040b0703050613090f0b01140a061b020907030504060c020303090a020d050f0316030f0305040f0f05160b130b030708 78
    0x40040d601e06000007a20040703170303035840036036010b140074401c450074000160f004018480599020005050095045806003246005645a080810304040760284140c100185004074080d0b03c40c01c3c0c03003d1510050149a19250608011103076511082040300054201c00005400b403a0140684e405181c00245514483e07461030b40641c010840581001da05c07110007031040001d441180200302d9007034800c0030410250318182c681110f241e80b0607040014900d41121040d010b50b00d402c05544210340292400b140b50300b10601540910b00241c54000e5007241030641000001030b010382100f40114030503032042144240030b600403622030000303941200c5940c00c400ea94a0140c98424400e81c500f50042041d10200d4034440c03180c91455015040c4100404840d60041c1e0503d50001d41c8401d881125040070b00440c0307483d90f2000b400d0f086108004007c110400014424040d0400000079184041d5041401c0d09403620300c0707121a600010b850100440007181c0100c1c2e22110581600d0040c6540c0d00d810301940c48 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 444844172 1250 444842922 444842941
    0x30804020120010609020a12060302090c03040c031704061b0201090b09030708030301090903090603050708010506030c16110a090605090408090312120a180317100503071409011d 78
    0x1400800c0044a03140b28640c508500028840c0030000c1040000069907541013403405002401d1040c0c030b01042d28501042040941c1f0f80040c22984041540d107010790f642e851785040c111080080e00058200d2030150380c0d01c5040e486c007800410680e2084d0320f50783c0681ea5601400f0080c80310f000c00c001d0001e90b00510401c91035100c14090300c000000101903c03c042e031150915440d680099102c00c10042d1500c01c50828503401c01c82d08030151074a494140045e20301688094103002040c41030500800b00000026201d99842c401d8908240343c1c50000000340000f81031044500641c9480d45106a00c2c041001802407242d100740d10488201800ca4030842d40c07644c44603a0b00d5080b010106401d8003414480c41603400c0340340700610480108911340b21803400e09503140c0b01107500c80150000c46140244520010035013000001c2107541e04071413042c0240d55410f129040c420078680c0116050b00c52007201148800e111107000100307040544d07036079800c0d03031380e9211031148ac01d9010104855a207014011802c00380 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 444845422 1250 444844172 444844187
    0x1050a2405160506090a060b030f0a031b05060910060b1e070201020304080607030207060c0509030c040c02013e0702150306010201021204080a030605031b0d0516030b070909090308040201 82
    0x203000354002c81101210b840b0b207418014105e81c1d4a006810116504d0100311580c0300c1d10301460313070035801845140a00c201d100c1d6101401d00000e4284504403180310b481d00349022070f101d5603d90105c03d407242c1e414101c486580e550f00d00c20554100e90f050800200311041000305032240801e0a211210440700075158020159112440c1030b0704500041202203030034441046814010000c2d9580160784010398100300007203610b11591101002010001c54000d550001602040340604a50010700205400390581c018405415801500c101c3c5503101814400100a4014160b131040521107025500d0202c10915100d04240294040603891501c18103500e1a000b440d4084010f0000614140084880160414086070122502480001c0030207580d5407500407000200010b80c01800302105070030030500c40040d940d20043c0078990b15112001480b100304014000400d80001400a0796100d003064100d110341290134002068014800068148892280d0801140c26903503890b031949441d401103440f41d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 444846672 1250 444845422 444845437
    0xc070608090f0f161202060405220c0c11151c060b04030f110312031504230103031701030b04140109020a150f0305010305060609190e0601050a2405 65
    0xc1c0710704040c05002e8841003221a003809410700050400038522002030034003c2040c0c01984800c034286141c400161148019103099910032101d2542085540c682c203030004025108405d10b2030304100c1e1155443c0d4000c4418845540652446141ca20b610414041c1280003491806241641040003201c0300d2021440590240600d401c08184c442d95418504110b403c581c000351200000e80004030100f0441100f9017004100a4020b8a0882c407180742401c01d9000042102c0d6607805d50f018074503105c0c0c3c1c0c0c940c0400010001e00c44140c803150b0100e0300c84405003100740005c80226442d9000c40b003034695581020340c102e03a4005510a02a6600d0761401540040498822465900ca03409400182c0d21024a00e000d07009240c07101c0300f161205c250092149024112a0007498508801072011030004100d0036848682940d10511039100e0025402500e04694003103540e20b858450342802116011440318101d40381141ca5030b0805844d8101b06251085102d1708418100454002c00f14941c062009020300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 444847922 1250 444846672 444846691
    0x6030c0203160c0e010905090703080a050903070e01031208130204020915220b041815030803090601051f05120c0903010f0e070603060b120c090a0602030c0f030c070608 74
    0x30401d5000d800b95180b44402402c03140c10f8442001485070500200da0140182a011000d004504210760410b40760003440c0030180640400140b02d00e0101d010700201c40e0381080c05011105880c0d40c403065035902d03035402c1c0030865011420064006c41d0b0b0f485211640d0180317145107a820304508265003000002c2d80103412003500428120061079468002002802900c4400f601e0102c0805510380002c40700304042e000720b4090318042c0820310011074103a044050100044038000b8101485400c042c400700c215900040522400200b0041700d9400410420304a51098500d40c07605060102c40008440703415828030006841806010039034822100c8003178000e68869601d600d00b40b101008642907072a0981c100c40b5071511000c209401c2001002200e004015a141c10845a0f05104502041d44a800345002600790300c48045022101c21070100e400440004128003131a590b6400081d407281c10000d800c6509020f40c02407110796500c08411525500803000151041e1420002c00351101000509a00c14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 444849172 1250 444847922 444847927
    0x403030906120f02070308072003040605071a07020a0314030f192a0e0f0102070e180106030c05010e0904050c1302091809061303090b03040219030c1a0906030106030c0203 75
    0x28441d0070f6100a04900f4081d40d240081445e100030041c003029910304041c45600e484070b120000305103011060350192502450526950030b041e04140080f1000c200c03840849850034800c1c00300407078002035031030f4100b0301ca622180600c2103400c01600040c00112480303120107016400042085602411012000a40c041e002514814858120710581d408075000114052141c00c07150407107402880300c208060b41182c0030388544030751400003900c1d14107600c504c501d40d035401380c040b99119041345417890016010200800c4856a00d0607c80fa0354131952082c00d000c03891030200900c01d418001062489550010000c1c500c400751002030103825540070710070250440d4240010125652021154501144a402429030f0b03800d03e44000d41c1800c50103042c1314104981c48146000094100301440e0490b0b040703000050b1250340702e0000c00c001d01349035400303141c0282c04c100010041040f519160020b45142c89450070000c240b0800030001882500d5009520903030600040080790f00c25048a00203800d2441540e0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 444850422 1250 444849172 444849191
    0x10110d0309140111030a060902031608100b03070512070302070f0818090c030601020f240c0702041d010f0c0c1106040806010311194407140303040303090612 69
    0x3801c41384901d016056180c0c0c000305200d4946118003030480503100414046146007010b8002042c81400e10158405100e51000000c5800d00300120700c00081441a080e070303640340340c03010000346154412900b506043c1145804143d14500c03e2095a1a440c1d00c1540b01d030745182d240e1900342168000c3d001d8485021041b140c1d280c0d140e00c86028150050769401d1115440341000c2d80060708054401044200f1580b002c106240c1900d40140c0407036942210a0b0540e10a0b160181c024083c0d2046d201d01a40082c00c0a1582c08140d12410000240f00c3e54000200094010304541d44241e5040c0510100000c06100b03880002c01c5400144001da5040202070f20314190b5904c42c11030400d80e090340141c1d0000100c2000100743c1c01c0c2403481601e522031503e140300d200f80c02d00b89035072099070034003c1e44407000c2055452044101c4003554044c52007081e007010010b4204032912206d6607803800f40659003510a100040381c0c42810000191820741c2e6068031219442170618004907a00203212030555020b0f601c685065 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 444851672 1250 444850422 444850463
    0x4020f0d1b060201060305010e12040b07020609040e030d060b0a090b03090703050109050f010f0b061c0f2f0f0a0503090a15090201081005010e1e150910110d0309 71
    0x1c000501d80b83d0000301d5461700d141007050844020003040d400a8006681301660003000038126403c0e108581c0e4842d40303c81243c008903a6601843c0c6056030000c1c580880c00c1c644071000809800128500030f01031100715140e160795299401445030910108070307181018421884841d01a581c0807041700c0c21103103d5680ca45030207003962a034120940d5640c015001f10b00e52080203000d409900e0b0780c03009013440401d104202084480c807554503445900e0101013840c15694200c1d420498040d1400e85003440410404480c0005004904a0010141c2e4201c9100507030016848203480c81961075100582c10048240000d85455100400501450040c244070030002840707034032511640804480c0001e441100c910016115a0000e84400c140380340381c82003000039070f9011400184143e0152001e2030052081181a003011908001c1c660344410031814509000170446d0107481c43e00c000301c0e1030013111310035440d056402d56a90b201c0c03c040d80c0c00041c400485030b4000c2e0400c081c89449850390218030b10124250 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 444852922 1250 444851672 444851723
    0x30d0f0b061201030c080304080a0b0423070f050409020306160903060912030b030c150a030b0607060e01050f070806010c03090305011a1003020c07090506120a15050f04020f0d 77
    0x810030001141c0c1e00604c103001208030110098007062008518140c01d0019450365042c0007203000f0070407864500010200440c1c0e5140d8044a00d02f51402e15242160b50407041d02c0381d5860040d8080d401084c040010700e0b140a000c0c00d004550094094107040e15207008250103440c0705002d100c00e2010803000000060407512079403030228082c1d0001c03070b0f00c565503001c010b058540900b017841c07080c0c0c0020801105951180c404e8507007100c40e0069142e030340c03041036015806000c1c1000880d40c0014082814818015241c008070940e44291000300002d0341c0b649100115040c050b5050400074454070700080c11940110403903603003a406410908511552aa501402e407024469003400b000e2602a040d14503040a1046521000c4a410306505001102e0b060564440551040031031040d21240400c420f91180a003044d19008200c040e114403c0f80f40c240617490301201300c007900041e45000000b40d540c4040a45903401194010010300c0801414800c100c843e0040103400c0e160800f82404c10071603071901120 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 444854172 1250 444852922 444852937
    0x9030e040f02161118091e120f120a06030f031d0405011d0105010206010b1e07050105070503010f08060114120c1905090901060e06011803080d0f05130203030d0f0b06 73
    0x2404e840c0d00060380900680c1d4801010814028402c081070008a03c80455003120385000d50014001103441072420b1403801040110300d2104150015a60910300b000d0b00c000c00200a191203c06019201c0032a404100c880f284009000032190403503600000e4803c600820382859004c440120b4022500005807c442c42179220704003032200512800d510916440b5111300514090014000540c035087c0002031510907080c02031880c55810f070b0041c4070490078030242c0d00708130741220003000246003104029015030b1082c00760802015a00d40001448000080d8143c10782d041c00d10541d00043e058014000041000c14201456000d4030a5210103519144a00e500740300c082141416a6031501052050018000d40350a001c0d03410400240001c000c1c1091080d0455001c0c40c00f03d120710001041c581a0040d41c0c0c0000b400d274040001c2c030241510321504051001000400200b1030ba8440e901320724624000000000d4054005001301020700c04c0c0e40c1c0c044010481038240208070b5010b61400200a42c0c003070300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 444855422 1250 444854172 444854183
    0x1209180212071e0f020a140f071e150528030c0306030f0b0606130609210209071110050406021911030426010f090b0601020109030e040f0216 62
    0x745814035400021049500000c00b420304100d1001c1c14080107024440d0352050509201030100e1046205208010b008007007034021b110300780d4586070441031079143c7c280300410200c148111080851034013074041c058018100289844015646000d12514480b110060400d0030700c1410701c1008400b04500c0840c0503042a10881c036042800400005004caa0784041004101842d00d40e042c80083c000c10101101b454120747e4015884d95850006601881902e13808443d0080801d400601c05030070071784400649043d550351000700400c8071810015003007942000707580811800c0110700fa180c00380302c1c1c8001c1b885000c01610308031610718002d5000d0310720560342180d074550700050360602d0705407080c003000032111113142a480305810302d4000c0f5500e02941c06a4011408054420b40d05003800490100c0700b43d40f103200030300c0101540315101000303100f420019504410741c00006100c0c0d601c1841280007040d455280d010400320b48001f800000e06d2000c0d0300c01d03041c944c00c00850840c480c1744120168001c2c07040 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 444856672 1250 444855422 444855427
    0x1095306060a090b06040308070f12080f070f0e0411090301020a21021204111f1107060201061a0c160e10081203041401062607050f0d12091802 63
    0x1e01405184001c80c0d020443c8145002c01012969480100b11002c59030420000c42e203880c200d041840410303003e05802018140c01c80d02755002c10340c0001e2420f22034030344c50f42100f001e82c0d20444140c942003446200540011031001c240d90305403411781c3c0031340712038100081d6503814a4031a070040b030308a074440b2004101003101c0b040303e4894044848481d5800c588400c10039400e09000310888010072201910041ca1400400051240c42c1c441400c02203803091089022289240400340c0608001c9114014454901400502007400c6005006100448407422980e40e20304182c0307810f42c80039821044040e10240103080c48503c5070b6034494640000f8140148050409041a2510480320780c132b03940c811002d6070009c0f500b100c00400308009407541f150b0071244030001c02c0902901c42c0c1c0100345503081415400a18004070310034200d01a00411120813007000ca0710015250000c00598009000455610042616020000800f5886241544032050901120280e2264210f01c4100c440c60540c0c0c2005030701 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 444857922 1250 444856672 444856681
    0x10f08060901060302101202160605010312090e060d031403390a200114061c020307030f0305190203270114031302180601095306 57
    0x1403000582140c1210000c2006925581c041090080484c100c4401d110088851080700031054048415203501c1c20794000340c41e4203502d0700c080100000c0c08182d4030111041c0e83c0b070180130300803042e0f80281c401c0d03039201351110350b0b9a004001450703c010b0300841c00c0112491254130844100b0001d9801109140c49007881005c0c0ca854120012884031142e2a0b048480f03103041c1c04031002101100c2d5445080c0c5010720034405d4424072003501c00c0c0d82e0225070000c0c2d8600031103148166403052a0074000c000032541d0000d509410421000800c24103c070296041e080741c1020000500c0390315289080314864101b45049c44420341c09011004151032000000d0303000001e0180e03200e90b00001400ba4942c3c10009490007240020008001211040c00a030f41001c001000c03039040c0801010b9844001e50042030110500c1d651560344440700001e4070110301180d00c50502142c3d0001c101d150f01e00d01c05503031881000b40b401d134024184240c0d0704800780748a0800710442100209004100b19001c20071664010300d064240f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 444859172 1250 444857922 444857939
    0x506040b010e0c280e120604060e070302011b031b050c03120f09040924090605070504120303180c030f110301051009090611040806070801123206010f 66
    0x400404a40f0700c20810841c42441d024440f4103c102005508410b840c420603880701519a0200c0002c40c6500680e0745021202028002652a00c15441544180144140d0000403a07442e0224000280070800800307201c0140300001c4048071440b4024913140c0c40154050401e0040d41c888030000769142d42165400c0d40c4241000c10101903a52201700c1c24500d051000030701880b4500625482910543d1a601d040381030000b0710980c5c252040d11401c40c07442c1c205403001e09400602c60788104903501e60401c400180114016030a940440b0b040d000303040544640d030b507800c90082a40605202404020100c2500440c0c600c82a15000d9441107401c1101405076040007a000e20102e805144640e041c0300c208101d070401c100100b4100c0d555003001040c41e00341864030b00301800000c2518003a1361b03000701c0c00141030440064024081c40154a07207482036601c40c140b10ba810f00709440301a0101d911240d41c107051282c0c03004203203508003400b260354600e600c1440d10141000020b901200c10004150024021660b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 444860422 1250 444859172 444859199
    0x280305100b0d02010c083a110301030c03031107150518030a02060a0f020f0102030c0a11193207090606020303061e010c050a03180b12060411070506040b01 68
    0x1c9080b140004824010790000309071210842000304901400f00b101d40456a081054503200c4030310ba041d050617900b0443c1004028115141e8108280d8188214518102d44001c1204d06898004180d1360902d070940d2016100016004401c01a0384103141d13001070842200c4000c82c401103220340d161036617401c031141400a422111003403035110b6041000c2c810016958072040b00c2100c5c0036820071180d06c8074204010f130f003003442c54680c02d100c6500010130800380741030350b0006201d40c81d041d0700c50340612041103815580c0c0e00e602140e2070001c907820401c0540465030001c024a9010064003502c0610f54500200c0b4800c0102c00d510301110741d008800c18850641c2c907019140c040c10941c8000e5045251180004c1c881c80c56451f058011580408003020031030b4450404822003076005401c64614210900d00200f60f05a0142d429002d10300b0040007040900d620411030380002d50009110b601d640b9170f00c04100c02001d0002e20090141d40400842c0009501030080c43d00c103900403c03c1e450513601d03120940c2c6951 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 444861672 1250 444860422 444860441
    0x10903090512060115200307020306090d020a02010e04110a080906060d0b0414010e070b0a090608060303120a060911070c0503010e0303150d080c011a010f050928030510 74
    0x42d40d0b004400100c581d03002030420304480015580c01c6950040090940340c2203030f580c0302c2c3e0304003c0545c071003550f103000c0c004000e10002d4401d03421200340c0d503540c42000d038490b0365030080c0c00010b170008d20341c140256115a05440c01110010000120030020200104643d844281c2c0a004a8042c00c20440c50010038001140c0c811400e942320805590140d54002c3c00d1070300100000c019501e03400b040d1400200075800b04031102050b6084a2400c0e44a00c1d03090001d41004980000003841d030240403440318499103141c3e0188402400540c1047c0c0c01000400c04490001d040b45000c40c1d541000045030829800b40c1941020550b400540da00c0300d5040c03c141410094201c540030348c2c1004040f6080400000450ba4084480b10145410710030260020f0701d008207030751001d8507460000c1007209060406500001066144580e02d400b00f054003001514800040d101440118070240a00040b50418030803403404282c2c80c1c081201c050b249003802006801c050b0b003007680c81e44e01070161648800141d04c500d4155 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 444862922 1250 444861672 444861679
    0xe0f0c2a0d020105220507030605130c091116050c030303070f03240e0a02070203030304110f030c1f020c0d06021e130302010e0f1e0f0103050405030d090203030d09050109030905 78
    0x162410a650201550040803803082c0126030fa040f4800384031b41801a98003030769000f5000c0c40300d428903045003800c0c0c145800041e2901d00c075084000480803d0380c810b180c039440181c0c000d1030400e880c415861128000d03480080d982809103050036103990750280015442206252246101c0d6940351500030111444031981200500c4405a107940c4103031410143c80c11140200c0d00c045256540510b070001074000c0400c020740500c8080280002c1010071074403040c2c1140255907844403102800c0c20541d4980e142c0710183d4101c0f5240d4100152002e501d4520b8440304034a00454200d1000080811089400c08000b55815070f80490006004003130060204d8440010501c1e89042c40041c41c00c0c0c00000394235100081c18000514002c0b001500c0303050302004a0070000340b075004052141e040440a20100706003191103941c0c0200101e030158080e2040c580956040002103050600e01c0400c0b01c020441d104050780c0c188000c0c00f2101c2820414050781d10040c0c4070340000f05000c40e2601d80604801001e4000620 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 444864172 1250 444862922 444862931
    0x8061e010e0a0e120a121b08040615050d050d0e09040c120201140d0f061509030b0c070203060a06080105070903020d030e010e04090c140105040e0f0c2a0d0201 70
    0x141215088040c0d0401e0039403200060810540d40000c0c07428150136805106200301084801038203402912591841582000600c000343c1c140002442d01d00420b09203401150021001c42d0200d0542c1c2e1045030042607d900502c840c588036000201152113200c030031281075003d40e802040041d800b103100c11a8181c1502e050705d49040c141c2e9840b8001c2d00c1c5c0d020712022515100b511200b07580c442e0304281c1c1e00c2081d03000b12550703030050307540b03000e024050100448465500384080054200110780d403111400c2c01c280d9600b0040343c110f5503401506a03028200321070002c010b210000c090ba13414402c0f18010b0701020b80010f80149006801c5080d29070042030002442410720040000d40c90300b1400d54480c95241c503140c2c0021050b94016183e0546003542160407a01c2c15507034804100140c000f8500b035074501c0040090340c8001d840111060b00c2240030310b058060340180428107c0b010b500407a50010460350340c190a100720b18159802104200e1214641d050402103080481074003400f541c448007004d84000d01 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 444865422 1250 444864172 444864179
    0xc0307060507030305090304090e10110901120f110f0c0601150503040b07020726100e15090f03032e14010e0117090a020a17060114040902040608061e01 67
    0x4081d405455805010326803224005140d204042c81190060091800100581030107840b80130b5940204005001000e441c05007441007140b14201560344101050351841401c09101c1100005030150381e82c1c500e5a962922541101078035010040c1c17442520a10105841d0007502085034035040b03041e48140088039500084d404441d51000c2241d40c440d400c0300d84007030251980d086c02ca14000a981c4403401101d45e03440d800b452200c08014546503100b240c000c0b00c090210300c400143c1241e29450001a880e806800c020b840901c041040d0f95100500b041915418541e02c081c040c1154401c48288920180c0b19580315240d192003520351903042c415051860f1658100142c1c2c0c401001130580c0f050521880c1490b000c4142c0c030820410748a210f084a0a10307150801c010301e00d5460380380040c1244a10542800440c03100700e0300c1d04507494001107034000c1605902e40360500d110b030b000c001c600fa500640c848007401c0241c0c6a038015600102600c4008000624105518480d209a1480307a035070f11058980040 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 444866672 1250 444865422 444865427
    0x20a09050c07030c020d301d10050706050103110405010605090d1b240305011e03020603060f1206061309032016090c02010c0903030c0f08160809030c030706 69
    0x2212043e615003024480c001984c0001908808424401840046407425162440580079500d0309210303887e0b0380030003c5038460700040c0c4030040e034841052407803599010940024035005d000c00c0c22070940b509040785072918644807001071710800d80003611348802c4c038480612141041d10441c5d0040481c0e1603c0c07070800303e0240018103010f5503908060402d801138070900c034000c5440065a0010618200c1007044000c0c0ea034022070b00d05280c0041240400d150000024402c0800280304d10b80c91640043c070210306080d03508000f680d03000641115000300200464070041d8882615005d500b060a0000b002107203429420040b45035203c003070f07000d01e46040ca074040d000a5044017000301161481181d001146400f0b0070624541465555080c0404c0590b050014107003400307030311003410086a0340c002d0150a6000d10300b900e110b0514440140054004e0f4141c1002c1020100107512651198410038a801101182170500c0d20003001c0c00e95104d02c00282c402058038080141c619540c40c15009001042e2410001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 444867922 1250 444866672 444866677
    0x103080c0c06071a04020a090c0815060f0a050c0316080d0b12030f1b030729041203150308040b0a03060f211e0803040501050a0605060904020706091e020a09050c 71
    0x2d90313000941c1c0c40089000c655411308010090b01c180c602c104004000e140004086540c00c0d00d0780c40d0400743c4001c895140303040c16404c440b1400c544804452030401020701c200d4140e80003000c441128002440081c0c00a0004400c00b072805000701421078944c0020071000e000c860055401522400c1c7d0043d81c4480368002105954103da408601a501d601001d084c07203403105c0107006528083e02000030901c04005441d08046a110426602002c038200000c440002030382d4141c4010b4843c0e00d0b01c041c0c0b00000341c400c1d040045038011101c265495a66070b41d0311101e0f43c0c0c200c0e03042000511350210b6170440d456030510602009080810082040511300001101c041c000031100448400ba00b49401d410302207011000001c040e410001c2c070f9004040b6051031400d42d001694125025420000400ea440e8118010708041d0303800100610f1800380c401d41000025803041404886582d00d42c00104003040c00e84410304051142030841c6e541082a61040100490700303030308020301b01031404040c048584038034402e = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 444869172 1250 444867922 444867953
    0x6080c0103180b27061302121c02030924040510141207080619050f0103090503040b030912250f0f03020c03010e1b06130503060103080c0c0607 63
    0x800081d202d44140d0304a000c0c0b90182ca0142c40f0008000600c600807040d034580b41c000e1102001540e8101c210b610003203803201c0b0203603041c44510b00c0f003142101c090f02e0149090142d00c00100704440903045007451030f05454600180350005a0000304202c14603080c19214140b640030401c00b984098111461010400c0c01380340559030046402d070f46120200b6004407041c114035001c0d41c0081c0e817600c0b1594074061072014102c41000020b100c0001080060810701e054400c0000c0100c11080c101e410310b4144001d10040e0007445c1c5c101074442d428200812800e01c010030242442680340380c2d407460540d052500c0c10011001c0e02150740e0040252450b03c03021901400d40c2d0304034812412010f40c20350b04000b803a5181c00786000c0c01d003001d0b0250900806400003020190702100750024004a0000104140c803030840382c103401400c0711001c402503400d2500380000e083c1280d0300c0c00403111180d201d0000ca450487c00741c0080b42d14440008080f07000c4031040041d003155032400c844d454a44000d0b6030b144600745607001c5 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 444870422 1250 444869172 444869177
    0x607090b0d0c03090c0f050a140916030b060a0e120f030f090118150801090c0f0c1a040c080f0613200301050a0609140402150c0106150309140106080c01 67
    0x542c001c0708944240c02194403103030414a14490161100d800010614007449014800d1000403000540300f04581f04143e0300702c0000703044036017680e180255065240030054140c0c04041c6e655284800341e50f14100508402c0c101c0f0f90715003aa403000da4081c80640581d1469029981d0321114840c40300007400000c82d0441c4480542040d240e014010043e0b0b00e0800900c4d000a4518003010040b400151a0781142042c0041d5034503032000d0390ba654000011200d08444a41c0021001a405d040c40f0380656040e050f140d200c0c42c0101141d0700e9a43c4000418042a601290281c00303003503080000c04000c020040b00b140c0108054075140c1000f45900a190200c500c00070f1128802c0600c2c0030001c800d088143c80d8680005c2c000740500c1c900035010382c0c010002d900906005500e0505440e091501408825114a6002e04030420f6000225035281094010080101c0e15648505000c1411620400700d0649d03002e0303644001c500241903180c12040721000700440c41d9581c2c585107080218000008146070020800e0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 444871672 1250 444870422 444870431
    0x8030a09120b06102c010f0f080c070305070203060f01031505010e010e0403111c090803070203190f0c08010b0112050f0601030e1005010b04060e0603010f03150b091003050607090b0d 80
    0x50f000d0710a41e41c00c80700d802944d5059600d45d90600050b0300407210a0300241e03031707001011090140aa41410304a039035800001e803190b0002c0c5500350080b0007041c00301c2c06400c01038181619a0f00191030900102c070500003401d00100100100120740d941c45200c0100e64030240420341c100a241c1c0c0240805119282c0c00d1508480410249400b807a000c46c142641c140a17143c4451000d8070a59003500540d00440019030346980014071954040141c5a00c554000c003c1d002004040c1560082011a0030050ba920400c1305480e0780000e0103040014010034007a0008100c0c00c1b04140098030400302c040e01d80140d541414200194200c03040282e66010b0790900300042c05150200c4640c1c500400080c0c409052803810001140316500c880c003034011250180d030340c0d80d40558820305121160000303114040b40d005082e48144000761001e82c5010705865110000640c0300c2c1c0034000610401c6041e035405100382c3e0726040c18014031009100040d4030102c60704000c00200e180a403402c11521421340b45541c215500c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 444872922 1250 444871672 444871699
    0x7020607021201050103051c021c090819170918101d0f010f0501021225140c030f100e0703020604030c140409080a052208030a09120b06 60
    0x10081500e0a00740c0107045580c2e0b0300e0051401a000300030070b0109803601d1007810002c11100120060103840c40840394060000720f4070403d071105200b001100e1040c2071040b662000301e040b400030850a0b611010400050501d040350b400d11804803262a81035604078003003008426203030b8903030b039070f034a4511076290380c0741069a6070700400c440021026401c00c44840e40c01410544241042c1c02c01103026108031100c14005076a02c5640c51785140d01072088502503000310510116460140010f0708510715030045c0440f02e6080f10030600c1061440030011145d4003031058080b41c07818003c00c00301003071841c00d9000f0400020441c07000743c1c0d648401c0904038600ca4850560590719103061081c2002580e014081c141c59079240e1030000001c0c0014024416562090743c0052102c0c90617010709100c039504407114a2600c0b44050040703420750b1080c100412144080819440f8103401c10201b01c0c000c0541a019503114041c4d0b0b54000c05208203548080c0448240341c80030404242100041501b05008441c0b500e219060b = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 444874172 1250 444872922 444872929
    0x90f03031210150309031b030c080d0609050603010204050906091e010b0712030507201504030305040515070c03050706021303080c0d0c020a0537090e030307020a060b0609060d020d051315020702 85
    0xb2700010041c401080480d0b612904441c68200d04155000d58900380132665409080c54201c0c0541c5c454283d04c5040d0340081116804d2002076141c0082910003140310380c2810303241c0c5450300f03a03080e4410740800000107145018030464512030380c02e01a0342e00c0d0522181c01e103100000c1c151000f03400c13a0101050002141200901c3c10030240c02c0e6082550b4850f40f0b41d00d05410081e0080c24101c40603201402000c0c03900c85140b1003580010710408017a01e036481e001100b0b031001c40707841c1c002280840d01103900f080040341041c0c07450703040001544514806a03845518205090521410411071410f0094000381d00380141e840314040e8007030383c81c10b0781e552012040004a0071410010b80000407011102e550f242e540c1115a0325048007510f03070f240001e21800201b082030950701c0c8800c60700400180c01c0700c910400040c815800290112400030805802c10b20305000046681c1e122a030750150f15a80000c02c200440a1070041661015621004150440c0d05407581d0f0f4020201140d650525a030002e148411540c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 444875422 1250 444874172 444874187
    0xf120b1206040b010f17030a08270d09061715040605090a0e010c0525230303040c06050406051804020d020d020d20090f03031210150309031b03 63
    0x10280444440d0b090a050503010500d0a010f100854680c40c080800d60140010f03043c4100301c4250021450020440e0007240d420001410b0030318803518458030356000308140108092080707460f03000f51001712220f6030041c095050a43c8100240154041070031006000500c2c4a039201c1000c0c41c0e4000020b0b0a600041d00a00b41a000070754841241d80c10f000d01c0b40c10580c485180ca076105c2000b04096050760000ba50580110346106aa04440d003503050308500344d8010284500384100700314582f072585014810403403180e072071700784000b54408010402400304a10b80d07440201a035081107480e20741400402022131264655203a002101c40c0c400850f592a243c4c102d82d0b001c2e01d41c3d4001c6481d083c00c02245030203035204038295030004e0704184644102481e502e021000b820546021189091205024040c03100704200400e41e060006001c124140d00e680c5200380c0c071a60501c1003040d801810000c81e11441c1c840c800000080501e0401038200103604181cac0c031100b003035101c12462408145481c0c2100c104 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 444876672 1250 444875422 444875449
    0x1c0c020d0b1306150308040302040902040923061003030516030e130608010c03060e130503071209030b01060e090106051b0703060e07050405040b07051e0a020c09070f120b 75
    0x307100481044665207500d00d88403042c074071442040c480f0f40d090200501d021591800041c1407014100030420062500c1c0c1d0041d00f205101900c0411005510307100c10400c005601e00e5041c0c8002d400011050200c818030003da80803d0f58164030740302c14150f0f240103000f4010103008040240181a480043c50701407149001c40000040000e9001c51003042d4882c09400144140c3e45950b0a211070501801d00900607042030360101d00306018130355149030384038450507207c203030a60303190104004000109074a40810094049a07840e07184650b403440c0350004521005034021000c01c0301c1401c0504190307450261391030440e400b9203450754684241031a0780320341c40d110148011140c4a448000010080160001c00d9032444200c255011181d0b1003090100f81e850858005140d01101030020712a0790248015140031382400c0f03849084404000b1051110790b1140c20024050b0388251b0b1007860318030300000d1040e4801ea6914100903802c8030000094141d070421741d80e061142e0b4a5541c000300980310425403c461 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 444877922 1250 444876672 444876683
    0x18151524200f030721080714040e10030203060105010914060304061103040609060614010221130807140f090f060f0a0b04090c050c030703031a040501080d0e01021c0c020d 75
    0x1500a60310000f0b076030398001c010484030040e002c41404805555171440300d00400250303c80144540c0c45c2c200c100c0702c850700000c088001d20010701010070001c41e08001c052044010b111940f800604500416140c072105030300190400c2000c41c003c0c44802210035200350b0411064401e9900e0352554901a4054011000c3d10844288040201300622203590000f066003401148100402c1c0e0715000e080b10b43c10010721016000d44d0141d840090014018042c841204240390300d05070034649103640304003151b11164024296503110000501141680041007104103504486018801c030782400407848100f402070100d031410500c000001d0950300c50820010b210f00c0700030402d49a0750b40f9040d4040680c0c0143c00741c05c03016480c2c45a141d1105009000b120100d05c4a00000c43c2030120f550390403000341c03281c175000c040075180d01212960582c03605e01a0700e0207444814040c1c04c6d5020307036100042c40d90003512081c50455010302c010b0800090080040401204140380404d1060000e0010540700d40315244000c09 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 444879172 1250 444877922 444877933
    0x10204030b1905010927140a080a1202031003020f030106080105070c231213030501020711030c0405150d060e060f070807020a0b06041815152420 64
    0x22119200703040718441a81e003000400c50380e40c88148580442d0161028014a00c81c02a00e000d17a024006d95003141072807061031040c2c428070850742c85034240800f10204890b0844c011a601590980080080001840c290f00450443ca482252060100310798400a4003e4603484560881500d081d040302c0041c1c51010000e0144e804c040c0c50051142d1030700841519240d0710802c8048406400c0c1c0d08101505031600c00070a21100d410441d85429805440c0d045400c2d600c4c0d00002001413001c2c0060151a4044c01c4154455011401450f0418102c0c8083c10320861510b000c10021070003005c3e0a450048041d24600c880d01c030103151501c0140050f91780c0700018440d60042040030002001c406107c1c4866a4406c01c294031064800d07680c5902e0510003d201000c040006101410b182e80300d600550b1840c040d6011000301d503110244a90185200c0c2e440854580203145c3c41a0b00420303501000b00014a90b20050241d2001d40310030f03000070421000100b01001406c010032041e80145402105c4d402010340e007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 444880422 1250 444879172 444879181
    0x30201050f1e040807230603280c080105090601120e21030603070b0309031e120709061b02130f0219050903010f0b010e1003021b070314011104090b03010204030b 71
    0x403083d0000e10419410344103c3e0408200d16400002e1040000d0713001c90060410b03d8001d0401401e50801811040f044c840402011036400c0308140f8451000240b241c005521012442c006040400580003113010b20341020600074581d0303201c2d5010014103154180015410381c11205603040859402c05d0092242c001107401c0c1c44800c0040045000c1c0700308408540c01c407aa104502d441600045030010456003003800320b0140d5811847c8140c0d5400c0391500300d9441d250110196400144056880b05d0000c2e03a0403030140070b140c1c0c0064901040006040d0812041c461950008007202c80000c9902e0504d03031103407032051030b400454041e80d002e4940c11342d00e00b40340140f820703004107503130020755655110f90300b4074002c400414858407941358101c0c07042e55582d2044511006014035030300c4d88981c24003059801c2110700980c01c026a9042580700c43c480241900a2039410010014511083e0800300360340f525910350018000d9400301d41c2100e00840000c0760141045c00000d00a00580d0720107001d0950420801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 444881672 1250 444880422 444880477
    0x81b0d020909010801060b0708090d02130e010b090105031b060d0e060702010c0518010c11190305120f04061209021309210206010612091e0210030c09030201050f 71
    0x410660740203541c107442e80e030382e110b0503035003a10018401d801180c00200010004195038000038010400d0113000301c442100564089060b409840c1c540041065650313900710302d602c5080c0500446035504442081a03541080c00090f11a0742d00380304c0e400e0ba0358452445840b03648580c01940e00d6410112800c100a03031042c0300141d21340004803130810041d440c00c244108031601440a4814021000408501201e9008010b446035041440140d03100714400c0e4000005558103001400e0300a0b1004001c0c0d10140795103400b07807416868000d5103065420a01081a0500030001542c4c2281c50624000b0810340c08260741030300500c001540650091801a940c403150103158120410044c4107c54118070010740d10302c0e9200040c46085041d005030003480040184c18440d40c40c1d11444100000002031440c0d030343e6524000d140000d51181100c115020082d425881c0c80740c0c0314000c603070300d40c1400d0001c5034403100014082000740c0002410b2141c0400c284459915400c140d039401664940890203480c0c2c410b440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 444882922 1250 444881672 444881677
    0x307120608060c0c250e04060b04060b041a0313021915050901080702010b030c10120501080a0303111e0703300614031203181b030105010510050a081b0d02 68
    0x880d0014801c1c4980304034440220085c10340441c0300480700c90540c0303082400013041418003500c1518115203c00260407983d6035481403030001d01c25054110f6a0720f140411071820229400c050100c0c444e014000c000130010341d038614000b2607038111050009207454610490a43c0416042040c0704902c042c600c0743d150b60844020621801e003620f172071032103a66040040382610600340d05103402d48c00184840700300e81000c60111191030254148204526105080710b01184c1b401d92000300c06a105d6080f140c01d0540501c582c07943d1801c3d4000c001d1421001a0b000d511a18154004aa41e51170000703000051501c203070189040209001c140c0600f00b402c0f0171000020100010b200040c292501c500000c044118800303026007810040c019180906000402d04101c0e00001c141c510110003001440303d1104080c031450009043c03d0b0480d014101195040c18212201600458040c0f80902800c016564004049e10b8481849240c20003040da03d0a0031040195a04407d80942050110301d590161403203801 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 444884172 1250 444882922 444882937
    0x180602090607210813150b030f01090b010509060d1208060319030201090308010806012715290304081603090f0b0703030e0606010504030f1716020306090a03050307120608060c 77
    0x1074004294075445c90b540c109000c444801040c01c0021084400508017a800003070340d10303c0c020151240108184c0e003041c01d413680c0c0c400441c2c0b24040c40700144101d00c0d0110710560405020364120500e80700c0740c1d44507010390b022490a8010300c107081c0300191059400b00003441007500c040c040316907a82c040c0e11f4003901034003108504802081e8a503002088400000411504944450b211640c4122003849101086a20308452103c02e60304c90400c1d41c072500c041c1400c4002490350580100264240d4610b03805005801c0481d46940f0400700309000101e290301082e1106090765010f600020201407409a55030300300e95110500c0d01d03c541e0400510042d443c000b0340305040c001d4600b4040d0145070044240c0b245d804075400b6001c904280020702c0070403480c4040c0340c0d407984908809000981e040d000300300682c0003242001e034045a0b081c075600440c20300b03200f2281c110368040010401d41c03009650191140c040100105c08200b01a030440641c069150080c1e0005c021038020781d01c40b0f080c01000c02185501008 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 444885422 1250 444884172 444884177
    0x7120c0f030b0109140601120b0f0d0c0e070c0312110903120c010c0507021e0d0501020d0f11031501080a06052205060a06020304060f0504080d020d020105070318060209060721 77
    0x1440c0c0c0b1141000945c00341e05c00e005c1603513141c62031407a00c82d20200921204a00715081642400031841a843d03208588010314054148a224246440b4404102400c001c05400402c440801c202d0000783c1c00581c01c6404658504002c138800c490b01c161400b99004802c00396905125540c1d601107000a0840100b065002d2400240041c4d0a40f517001c1e00c841c40303448030080d003041c5059034056601030b220310040d000c0c0400404501c0c845500340c40f80c50a80e00044480b600c616580d440c030507074079091440b4612081401e0504541145042d10100451050320520309040c070403a900000c0078001c3e0365103c1c0c009880000d00c0158090101c8030945242c40c1440b82c1041c8071890040132401030303d48031602d001103c1165001703503d40380c24280122144c1789010b080c041400800d01001c1440181440070b41500d5803150300520060b104500000c0c02e407900a0210342c00d26181040c0f01e04074030803103245240c1c040d4100c41e01694030340c6420b01040c19440762440150180564080c28408080c1100410013142400e6 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 444886672 1250 444885422 444885431
    0xa03021c0f0b0307053003070c080c0a150503240402070308060a050d0b01031502040f08100f0203060303040506090d080a1e1d090a200703110601030507120c0f030b0109 74
    0x12006d02034095060101000d0361580c840032021411307000c4c84100138070240c40054034104041641c540c0ca108225802030071440c0c21560720f840c901d082c48046440148819008820152001c1d040a401480701402c3c0da00400c0040017071010301048250303141807901c07018104554500107400c00500e6110300b40c134400e11864903207000140501d85000c51240058028064200617480d6990710364080c2424469008160740030302c0009012404a840040105030400141086d46c0b00f030080b00c001c03254504410704c406841401444503035100002510283c07801910f003da0f0b50110740000840540c900e14004010141c005400001c40d5403119141c410540081c2c240c90b0b4129003c0c1c8150382d01ca040c00000d2100039003100c2201d8440c81c05100442d0022130501d40003d0000240c101c0d1040d0f001c1268001400900000d20182007540c456075003108081c0c12070182140e541142d80305c03134440c90070b40318410000203404004024440c4d05101d401c0141001c001082d03103644e1702c1c40e040c182c103c000d00c03900050b140b82 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 444887922 1250 444886672 444886679
    0x1090b040b190b13030221190c06050904110a030207030f1e0e040207020a06210504080912030f1306030b0d2a090509010b030d050f0a03021c0f0b0307 66
    0x2c00840a40861110001c1003441c107251010071140c03c1240d2180c1000c1c00c0300b10000142c0c44074081404c106d010070348a020300d0107088116a2400c400910b030707000200b594003070110218003149145000d4514516180e0b945400500014001d0088240d68003120390001640040c11a00340c1d00800885104e600c90b0080340b850b580098130652000c02d03581181140000d46121405d10803200b0b4841074070020700041c1030030440c4c0c010442c01d0b001604030b132001ca0240e0706503a500d80cac44450310a13582c00386040140a5071509a50f0b45149010f41c0414034062002a141d80c021810b050080c2c0b00300344410190703562149003103007041c010b080241c0f0903c000300e494580b15289a00f408034002c400c0707a4100001e900800c91801000d0071000801e403500814200511010034040154007540b80119003a100105603840044101810f11990f001c0c0c00040c84010004207007070010709016101c1d029054240183c0326009203050b940d001c503038426508440d41c50042442810b0010354081c010362a002c3c5c040758141601d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 444889172 1250 444887922 444887929
    0x2e06081b0904030909050709150804030912031b020616050313060302040b07020f0f040c0903050d03050105010c260c0f0709021c1e0905070e06010e0904030c03090e01090b040b 77
    0x1042d02c01074005500d0500c207200201041d04843d8100c090391034502c1c40a0f56405451141c8444c01080320700140c0800c0070312080c1644100d0300340182c00b984d0704025401006075070140c0b07a5090110900003400310100d0040c19503071024140c0300344075030040e401e511801d00c5107030072600c030390002c0807902c0008280080420420f00c244240c40c140d0749081c503802c0c5064075035000c002c000c4464205155122001402510300d5858a000f09070b001205030300ca03481568150300c0d01d981007404184110040500e0a00108a076a907c80c6030fa0001d10f0304507898203403004800b06c0503c0094413446403004000340008400c10040c40004040400c03170316031002d8130542c079140e502100a070301c5881c03140300020320605148401c400031948040f1000d01c00004070041c0030400d421074015904d8105003540e07550049001084130001c04603190703a1240003460000351840007140010341600300a04080d0412140c12070a004041c00b4044c440e01800800c1d9407a401c640c0c0d9585440050310240c01d92502460a003003000c1000c0c20b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 444890422 1250 444889172 444889189
    0xc070605070804031727010906060503011103060105030903070503040b0306190506093703120e01051c090b0a0e0d021518070f06170609092e06081b 65
    0xa40c10b95441020020115044600c905c001d40019803160300320080301094100d4502c0203051000701d00010520000c0c0d41400c0003214905d5025900990500809006030705407001140c1d44683c0c2400c0c0180c40e51a448101032450090a80c02405413100003404500b041040c0055171156000f21000c41500b0b01d5000d5400c0445801c0c03055680101d0180100d50851600a1200e0054011132046010520000f140010040303403c3c0560040c0c401c9542d0203000303104407560b0600024a05040c0b0020403002c0400003055407090396100000d18240c000d410311102069040084007030f070050189605420700440c0c21004107194090040c0c1849114000006a40040303800d404550110420351010790b280c3e84688243d0042407140041c9008816002c42c00301110340c4114094081ea0f5111300c64200c624000c03054089024110a20911901042290450700000e0525640828201c0700c00f01c84030701c1c4031005c0c4814190707030b101908504005000c00d1070100081c0100700403100140600240098100f48100322 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 444891672 1250 444890422 444890431
    0x1703040c0e061206010312030e0a110108180c01145a0d110c060405010605060c0c04090521070519030f0309030210230a020c03070b15090c0706050708 66
    0xa81004d8010000710704d409229004142c150700307007c1200135850300b041342003490340c10044488032805822450156481095164044010f1103541c9426079111120b550b07868414201604028038140388001010103001510011380e925100c0001c150f00c210310b0070709140a4041e00c1ca81a0300241d201c08815000300c14401180c1110444021888500a03804400c50f030019985400140c0c507000105e6a40070f23400010110951000003900311401c00d498043d0a503403599001e82c2c400c00302400048840007003c10841c8580604450024041c2c03082d00c1d0040c200342480d8003803201d480420074843d005962500c01007a030340f031080c0182c41d00d40a101d11111200060b52201800048900303440d0342e5228066400102214080e00440d40e9025090f40600d0503076110002c0380401c0f20700e18003000e1600040d01c4659030040030a140950901e580122071030303942d000b4010090300f00c0c1100004151586100c49501c10091400342c1401410315147c00c84407504d902c80b92080764140d02d800009030785c0c18424884103014 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 444892922 1250 444891672 444891709
    0x503090f06010f0e040c0f0303050d20030a0903090e0c09040b09040f020d26070209090c090c09010c060e0f0622110f0405072708191703040c0e06 64
    0x100e09186a09040b070078010803c461b0407101c40008210450190f503260b00a62003541c41c103075121911400c150554001c00406da80c0b0711254441c2b01109446001940c4c3e001c5000e541c0081d080d05503060444a8018640c014031070001100184868039070940d000300010407060303500344402c1061f00c00748108100d00b120058502d880403000680189880c0303811b007861501440e42c40841800e10741035901d081300490011060500d00040b01800c5060195103160310100c58005000030450220100c5e241d440010009a4040000680c120744c41e0f004180e51042d0b03580103c1d04224680c206034410b036540001360146003041c4145000101004501c412404400d50102c000c200c0c421a40d5940501342001d07103205a50024020007900c02e00d4031280320310f91040c481d60703940326059081d25840e1859003003068908081004584424000751400281042e9900401c52450400029600300140400500c0c2031110125500000b0312040c000030640c000160b40c0000741c14000c545425040280051915040055 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 444894172 1250 444892922 444892949
    0x1002030f1e120a020301090f020c150a090c17010513030e06030606040b030f01031103010e0601050909070314070801050a0e210409020d05240904080d15060503090f0601 74
    0x1500d8503000300c0045007000c1c60141508003500200e41500100d0100c41049000c0e5010004000090150043d118140e400b40001c602e04005085051744032416507080e0f6000e0602180882e038414081da2204201c203402008120020f501c03100c3c804141c003444c8504191944c24140458144640d401c0301d001d0060703154a07000e43c0b0400c0e00701800810b030030062810354800c409100004420314180f00540c403848108002110a41c114030300504d82a1803201d0040c0240c0c506284500c58040000c1c0490544030110b407400c80c1542d41100961504083e50801070405c91407224a104c070000c00200907040d50800030003803051f40c1c0c070300321446d040f50128100360340036600c080c0749250b0340360400c03020380510b51a01c10800d2410f070311400440f05aa224904202c07420b6996804c00079140f04000d0215059404d40c000d00001e05c0403000025411130b006040600250800103c01541008541c006034083ca000d807640f03281c1a9aa00c006895a0000c4941d180035028441424000c2d03800460843d040e030359026000790 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 444895422 1250 444894172 444894187
    0x20c1606020619090c0512300d05180a0506040b1605040e101a07021c170a0201150f03020907111e10111c0203040308070c05010906090305091002030f 66
    0xc02030940418251241e40c0a41004280e0381c0300d0080b2a000ca240c2c0000405120f5031042d00c209103042800705541810025003c512180714a0303230101c4200303a40b40303000815103882e0604680e030703103215003480c5004500c200c40c0f402040102c003080c042c2c130442c05000c0c507000f29600c078182e0394010028a1400b80000f2804c100501188030044202c1d6000740e603e2a0340c54026844100020403508d403024054020700d40070070040304625140307801d0840880d00110002c0da80816940c1c180d62400414103614540001044030502d442c800d50254011880305c08031194840d41c4d40350700e0010200075000a038051029600000c0001d8081c41c04540509070000003408100d01d60b040e030303500c0718400d07000e5920039009000c0c80011005541c014071603404005600f031f5640c0c02014401c0004505504040314200d0b0060040202113038000c3d207010b030320808504014804110615100d401031140c048020082c520b40910f54040c582d0103800351440f0384055903240d801c1490350000383e0341d0303001303405900442003000c0001c0c4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 444896672 1250 444895422 444895471
    0xc06070f020a020d03050d0c0903084006090e060102300c060906220201120f140f070504030b0c07020d05100e01140f070c020a050301020c16060206 65
    0x840c9000188180e40310601168000380320505103500c01d0300001e8000c144003a8811246c41000890b001905020814501c2d6642e0282180141007030010b045260382c01960455500160076006540c614003030005c4808140d51000c3e03e92042d0113984001000380e0404640e108034440300c01c0c01284142c0051000f01d07516642036014000e0b55401640206403000401d00d44031488028200c04c600440c09000189442d0041620304500208200c0c2b08610030400309a60ba44450428540581c0a02c1c1003009820b4030764942c0b0280c54604203044c9401d1425000060004610303c29500900002d10038034415101c540c4200d0f114042c9000c003900700300c1081c010400700031801009142d403901c090500c0f4180082500c415041142d10b0441110342a2101c8450004040030f22414600c08010740350740550b410914462445106c0082682050020080100c002d5503100c07880c0e0300080c20300400075991030310108842c54480044102001c0c4070744d102200070400900100701c540c42000e519022400300309909403030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 444897922 1250 444896672 444896687
    0x402130b030709150905070f0512270105060f01180b071b0305070e070201020414040f090b100302012d050703090305060f1f0f05011d0316080709020c0607 68
    0x4066151003410000180c3e00514001c01007086098041100144d140103003890540b0070082078070782004006c5000318070080e00102030f1f4400c0407040090825641c2d600a0302240b50b148a07000d10301c0d01181c00720f150000c150541125120f81c03400d50700155040300107401902e01c0c02251000c0030130034050741401e22219514001604900c3e01a000b91010900201002000344003a44c0056801d6040b2035028042c1c008030304030007070700945144006c41c6040d1034280e41100114500c80718a100e107448003074040d551201c68020701d403a540c1010389515941000c84080380120b11382e1000321302103202880110b40081081182c04040828503600509160317410340704951030b50104408900340940c7d50808800714100300499031149208070302807030fa50705001810361502c81b0b50701e2185c0d21620764040306002d2484083d449100716a020f0801c40320504540c0d605204092400741050780501c2281401c68001c05480c0440c01114903074819130701d0f030326291415282a8442c1c14015009640600041800380307114684 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 444899172 1250 444897922 444897941
    0x3160909061404030c1214191205060307120609020d0c050a061806080c071401021306230306060c0d2001020a0e091b030c0403020a0803030c0913111903150f05060a02030f0409060303021005040213 86
    0x800947c43020198005070407008590000d95a9424843d4103111509007000000040c00250500128028420881807004811401014100044030010844450703141c0c05444095900c4221041440402c00c0301d18001d40100e9500c0002c1d17610f001c0009030890088802040303c210070841100ca050100050140701e41c4082c1c2305a0300004104040c42c4021300034810f0315641ccc891903480700500105403281c0700c8030b41040c90100c40264810451119403903005016600030142c10394044400356207502c1c4101410210248854440310700100b001880480c540041c0240c0f03100300c40d03414019840724260750b40ca00048510300704a0204115000141c508a00b00500742d40c000140803880f000d010408200c0e50304220034100506a000d06203054054041c0900c007440032140b404c0c152100e18001c05042514618481d160003450005800b401d41031092007150384002c640201c2a9540d079075102401c0c0145000c2c8015401409110030961728500240603447c043c5030000c00d2640d801d05040c4004000300135411 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 444900422 1250 444899172 444899183
    0x50c06011406041505030105010206220b04060b03100e16032604050604031217060102100203040f05010509061801021606020903160909061404030c121419120506030712 74
    0x1c4c20304030700740c10007072100850303529142c403545044000781ca0804054070009a1804014415000344900d2520f168a07540040c40c54159071203900300b10000381107000c0c50a416000b640f48800a95001d50031000f064044501218409a0a0300005481c105140802081c0011003c001d86d00224441007000e0914a4008054513166640002890f070350301c250701c01c8a050281d8115103140c250802a4008110842c42041d0450318041000179204ca503d010840d0307403298040003282c140403480588250241c0d1040080280d401c0030055103a40d030204459a40e82d403605e0983c100d50a034010b0094a64a80d411400d1804071300d41780e50b50070f000c1d4014039a070540600c580c0c0c50f41a001012480f0300002030445a8002640309681e08059003034516204000c180201e00c2d40a03c000a036100703001002d001d8010718011a03008220100f19840342c1d0041d9011f4150b07901140b030304510803424900344842025902c400c40c90b82c80120542d8203603041110f205d64160020b450070804524044a0381994074401e0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 444901672 1250 444900422 444900427
    0xc0307021c0308280609050901050a060f06120b120105010e090a03020703080c150109060512060c0a0509130608060f061818010e010203100f0f0f1202010311030405010b0405010501050c06011406 85
    0x14921941150f2055006e100000d84a03070500202043c01e1046640040c003200c0d003401b1241c101640070396211900e1240504000801030103c1a08084d507002c0840500000e0014504800740422030f8040d1200380510160507107484041800d00000240c2e012582340d0580150424030b00d036407143c28054000b007010552034000c0e0041d2000805002c01114003a099804000903440d00780710611424254001c803840c120741c00f40b4240110044003106841242c0c1041c6042c66840c0700560111b43c0b45400e2107041c0803501d062150116070444041210f0384074172071a004244082c0c0c2d441c010021000d540014503135582d8003040206150321241e031040640ea84240c000031440c1c0380840300d1282240c0c41129050580ca04c006014004100c290900c4001003036444024031040381000c0350416080c0913440b4400c0f40501c0400c6400441e4000e8100c880d9003a601c42a48c4d40300e01d060f0908501070300c0051425845140381c4000480c0640c09401600c80701e0004c0c5000701040d80c208028201a2908000070b00d41c440e50a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 444902922 1250 444901672 444901741
    0xb13020d0519110d08040e06011704030309150605090a15080d020c040f0204050310090611030720010513021c0f0c031e0f0201050d060b0c0307021c0308 67
    0x20802c01c01034000030050303868500c0c40303030514101002001c20000e1240161001d500040796442054605441c82c0003800145a100d040040c4d0302e1980f10846524240030842c200f106042e0075a100b0014a405403c1011101000310b441c1e408030b800070b000300742e8080311010120b4400601c50780007105046013080300200720303911040c0051400c000d4040040040e4000031644080e0305040c0118262450707a41001e504080c00c040002e40c0301c14100c12444401a914810802402055005982c1c220b040703400d142d599003800800240090407603408882c65002c1410542040801440703021700c192019112600902d03415403c200c503c5401041c01000b00320041c0011021512100c01414040e00c5004844241441c4d441c24a15140d410590403540e05806d07190701c408a80a9002c40100715030900e02180d880d01406902c800412480e042825680070104030840305103400401008028003c4584448000444862042010008900800094055000c02d0742850850b8480101e6111403040f40c00b010714 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 444904172 1250 444902922 444902933
    0x803070c051608280201050706060e0a23071418100806010801120203060402062104121b080405100c080c030304030822080a0c08040308030f060a030b13020d 69
    0x110001c0000049810b0020040c15004020840502501da503105802c10700d10305a0034565410003401a050080001e030100030031550b0b900801c050b080c030445045080c03e080b410031004062128a0186048003000100526094502c410388100041d9070b6100c4100e60003030300c400c4e040c0c100740369550001804030411451130b9114025020725840c0341d940c10901d442e101000601100c013ba00c20382a043c2c03c4c3c43c0307000161300c011680d2035126405441480e034400c0d600c0c00d2841e965035209449809007240b00244400c11107a458181c1d911042541d03202400e2800c00703280d103016421400020504071003000100301e503040802e070122801e892402d1080150b161500ea03c441ca501082c0040240c0c0c20000030801010380041ca400d400600ca000802c0b0281d4011001142030358020b000a010b814000c68060002c62040002d0f011060348903d4183e1159513030b182401007500150f41010038180164006010382c1000801c030411072341c104094030002d45442c41ca1446591810b1400e90308184000b0616000c00c5 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 444905422 1250 444904172 444904183
    0x1205070513110705030d0b0604080d031a100e01021b2b390e07030515030a0309140103051b1e0f0706110f07021c0f0b09160f030803070c05 61
    0x140102d0145d6526401d1440b0710048885040b5050310a08080c401801002d0000800c22001049401c0003d243d8141c040e600030120b006010342980321150702c0c1d2003075120794010030720044998280c003100c150745859000c1c0c200b08000c84ae03e86401c52040b109000b2143c054800f402480708108009000010458807443c14038200d03d42640d09011200348504d2260008038001201e98410103418600c26090521074a000e0308087c00d94020992218041000c000f0f2040f8400800030008040f100800c0140c40c0141c03000000f407080e044000262092204294000e000715441024034841010034030380d04401544103034100341c20032601030b8403050b44410416611001040e25080c48a903042e25504c0a140003c00d64021250740e0500032824404146000500c0c010b645500d9412689401c400d0400c3c030901806090821019150510161100b011700c049010250b00450802d030644114407040514068000b40c14403401d00079126031f21040000c55180005583c04c8201880c20515603680d03504d9003031805 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 444906672 1250 444905422 444905437
    0x906060b0414010804020105030c0702040e010501150801080a020d030c0812070c1509020a0b0d020c030325020303090604080307110d02070810290117040b0103020109120507051311 79
    0x10380000d0180001e2078550303030b0400490024a030041d03103450306600003010b07070002421850010340c0100307210701155110780205004070b000c04000c105540e500d49505040e0b00c1c00081c40d0001c83d90a8002048420700801c0c400c40355074001c0e05091844980b035a00301c1c0c082500c51000d5a000d80240401c0d0052519030790007601500140e83c412000402506150400b804810400422a841d0219510043e10307a40101c0040fa400720304d06c1c42c0c481054055810282c400d0541d03c81140c00000100141c1084182e024805140824070b410f5500c0095401646d0301c0c0700590f41406140d0010300041c0020320981d0095a00c0311451070f21070f0b114011030900c1468081c401d294040983c004100c14400f100c010402d10700341da82c0302c02047c008000036080c928044070841c00796200100251203035800c582d0041c000241c0034078110b000e19045280c0b078280300c4900c010070300003240018003000c000603941e44480c5000c0700c0950840060701a00d494402002180070716540f00103507080d20b404090460005e14806030050 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 444907922 1250 444906672 444906689
    0x70501060b04180c0c030f1202040b030405060f09060a020a092408160e1e0909060906070e0306150a0b040f150507030912080421110f011d04090606 65
    0x1da50602c0c80b41d000f488000906101400d141207100c1401c16801940306040e903806080c581e915018408080341c90130105094041c41e42e0001a000441082c05001144102d000700e0030707a109516082a58400340d641a01c01a450740c1c0210081401c03034541d83d0003450507010504008103403640da441c3c0001d01a842201d03052040c0004299160020b4002500e10392100103100e84041c503c400d00c4016041040d818141c9003e1401641d108032220401c0308115200400181591000d1034050030741aa0ba60040751080f200740680004140102c1c080c0030712203942400280070b46880d80d100300581c02c0c0300c5280004030741e00141c03591b80010081c5920703004101070644010034000407420880301e0321155400d458007070704021040004102295100c513850098400c00e0961510003a11420329103414011504581d8106030382d0498003280800303007001440f007180f103815103030404c080000030002d10072006041a40410403594050312244505403203c490103000400010300000704d0344440007100d0098100005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 444909172 1250 444907922 444907927
    0x1b0303040302090f061e130e0f0610060f180b0304021522080303010501053f060108060901080c0616060e071a0418090f0f030e0126060f06070501060b 66
    0x1a030400c42c000c50001005480074940800d10301c0003040f0b058520901031091035946400007452440c0034004035003031089d00070480310fa6003050590460790319040d101c1c5c00e01180490607070038079090007401c44615104012413400041841d042030b1940943c401001260f214080280100602d55050060141041c400102d08901c1d15401c102c2205004541c00100c0c030b42d4420300c0104090303030b07025044403685030f404003a003040050a45c0c814101c007035080d9000548619208000d000c00360082c02c4861144074266920850794a84070140035440500303001f03400b07607074010450003102818400014000c4001e200141c2412090b5a100c0d80c08494815501680707540107900100955074240601000c031548880d0f86510f42803038014906d240180b8443d110101540f01d50701542804000c0310f00c004c0b002c0e0095900c14030740a4070720b0014085882141418003140c1041d084071480703001000304950b81a1900101e4003a901c40b01c007001000105000c419500c0b49080204400040081c060400144240102d50380c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 444910422 1250 444909172 444909181
    0xa0804090c0e03100903020f06010929150a090b0c0703030206011a0a03090201090b0c010510090b060d020711060403030f170f0f070315180f0b031b0303040302090f 72
    0x1d561110710398008114801038100040c0e6000300702c04060700300400e800105041c003442c3c1641411040718048085000380c10000030030b05055002040101e140160480c88102c149885101c0208440051500140c201ca044424410b40a00070244400d0307070300300800a00d40e8ac0e41100c009510ad180301c0501500b10400400405404011090142032030007094014400d044016006070f0080c0f209440c10581c44503119410741e405500b0b500c01500911403d541c6d101c0c0340070811070107040241c8902d80d03504200c05000400d5030492007050750305c1200402c0e943c43c002e1141c61142c0650013840c02640d07059a41107070030000ba616000140025486921218a107900c402405480d002498020000b100707103a00c1040b414280039500c090b03121070042805003ca44881500320010440850a214441071001007c00d240850140000d6450002001400714402214070702d0700f507480e882086a0141e21503940c4031604400d10004c1f0a043c80f0182c102ca080c1a56034000806840059801040c600d00800911 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 444911672 1250 444910422 444910439
    0x70c0503012304260c0a0317060303120a110c100f05010e0103140c0324090706051b01090c0e190c05030109111e04080f0d09180e0a0804 60
    0x20344400d052412044000200b070b070311030ba450100c0200000d04490a9001000114800044074074400314041350050300c405950110903a226401c52055000c103407104100983c58000c3c8401c01e101b0340010b80030350b040c40b1035007003000d10140014209808454840440c0c0c0c481ca03160101801252112000900d070300c4d40c404000408032012041034880e0107080c440140584481034105a044a1b4420b41010400b211403001070b007000c0a0241c42541401a0098500301c03003460641113101c0f0500726046500d0382c40e100300d41d40d990750141c0b1a06000c80c0041c0035410500c130300382846400c0d01688000202e61000c080c0d64203510190140c1140e592001c159043c00188804e0340001d07081d08603c404204110040c44d5800b0703280d80014481c5040c02902d6800700c04442d095501a901100e07022001e0400c402004085001990420300441c807403480303606a10032040c900001d40703203074801c02500c50480c3c5a08107007803140340203940842c48104070384031800309005600c208101d0b807940c3c0c040c800c410b8030b03981031101c107 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 444912922 1250 444911672 444911681
    0x3160f080d090308160c08030603030702040609020406030c050c0a12091701020409050601230f0d0608030403031103120103150204080f07060e0a0305070509180a06090614040530070c050301 83
    0xc0b85d8002c01805000ca040035040013460300c9061304041042d0304c0380e40b00300010341b13140300709100250441d003000b4002840e08411340140040e21015242840441d0840500310317828040c900400380c0c15030240c0d880501090a94204402c0001a45005038215403111800c00c4612605c541c0c5040c141c2d030005040040000600c075150308218246071402e000207901c0824079100c102102c030f06140001c000b900c0301c140c8038994220394100f02818814884103584200c010f449402c540b1080d0b020405262218400380400f1080342c11008040340982d0690342191954400c4400f041d68a500340e56081001080c82801000b558030b0585001c401020b01d1b9091020040078004ca0780629130007401034840601c0001c0e80411420240c1e5800e9034403213403d0351881000d24a4019045030901c2602400c1d9130507040c80040e8216040481c09014140041d040402c0031224038641200c0c050150741081c20640c5511400045412440148100800c6203203015001c1d8000e560103950211291000c1010411080c1400c0c000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 444914172 1250 444912922 444912931
    0x20607021509150304080307030c090f030f1703040503030403030218120a260d0b03010615020703030306050a0f060e030106081603061a06190201110a210e03160f080d090308 76
    0x3c42c1400d508044e40c9a81081c003000d0020f40034141c07141d594010b00d030f02c56003100006150400c004100710f0fa403801c00c0e002c40e000030903040d01d41d8805071129030315181300c1034103c0e0701840c1c0c402d000b0340c5160b03140d4508030300139003002d00020320b810080155140742e80c0e5596103080798039201d40003401c0d0f44801482d0010340b0340e043d60b401405000104000e64403494a00c0c054500c80040c056002c40c040b88510b0000e80186001e401225042c01c012000390421540000d000302038900c603440c01c0240a4441d4200408200103110300c17018002d04a0f07040c01420703c20401c501c0d008001400106042d900d500c1c0043c100300c03150184541c0407610f100f042040c400c45004a840201c0d42103110712806c0d102c030020030600c1c07003600303030b4010000c04600c0c171040e000c7e01c00d5019450b80d00c000361100340c951005040041510141c0c15158045002d5031460b04c4007210306200322401e004001009514110503020102c030078120154064401000e0200090049041d54004014180b003444001800900d10315003d401000080c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 444915422 1250 444914172 444914209
    0xf01060206090d0f03090c0906060503090d021606050921280c0509070513060c110405130204110c01050a0c0906080106050a052a010e12071e020607021509 68
    0x2840303080c0d21341014900340040b00c40e140119000c01b0904004039601000d034003203020ba41c5880750000790558840d000e1806091180f0588281b150300314003c13640c0e00a51841040784c0031071102c04112880c0a003005085100000c0c000414010440d848ca000c80816070f0485803403034000360711034880012102c0400b042ea1140c0d02d4440422001c0da182d044e07401c407140c01098007906510001c81d50150050041d82d00c1031420000c071300c1110b0788408009014081c2c40008071030b0496107010748001841c00e0300910307120309541100716220858903000c000140003400984405c0c84e00400907074240180038000d4511a40d00301c180407400301c400040080a00606034064020024498010300c02c0940c48000c80d072075540c1b00d16209407a214606142041c0c43c3c1245d0f2003002141024929031035904040d0411260301c0f03c084141d90700000181344501c00d80c4980031005094144000b190200d000420818040d4607002500d8542040001e60101e1401c00c400003100b807008801207110006481d007407074803806198864 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 444916672 1250 444915422 444915433
    0x1b060c0f0f111018080703030b030c060a050d05180102040608150306010308180a0f0e070f2109110a0b03010906050d0209040b06031c17060901081e0309090f0106020609 74
    0x61050390f15402100743c107002e69070301c40d1070b40d50303040c0c10000d50f4910076034000c85620781e10b40d01860046c000b8481002901c0c0603008000980010f0700d0701c04140d5005800980f58580381c0700c1040c9040c0300416009241d10f0940001c4422440c010364244050300c0513145a4680ea0050b0400c090504044400b81d0320061003940300b1030045c8001000e0101341e698400c0286224070b000c400d2500064510607281d00889400c40c03241c040000c5103c4406402c901030b583c0740e1074038210300c00080c0c4100d500c0220ba0a5441c00c1004070740303100b08154059401802418000c0741d9500001001400240d000d1071581e10000c2d00c0d07040840140600c8090788113190060604992008180046034041045050000c0020b0200301149000072102d0b181880803410000010b0403012480c0380b90880a49107808101c1d06441184141c00080c0711810149091816030390190010300490603100741203003202a12010a00b858081803041484c00c1e2504400e2500440305071440301503139810300c070001b4a4410014802d04465018 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 444917922 1250 444916672 444916697
    0x2090f120f0d1d121c050c06070c03030b0405040209070f0203041d06103e010525141b0f0616080901180b06030c0d06050702010c110d1b060c0f0f 64
    0x511003500007222105ca00c040803a40500f501c143c0510071f902c00160088000700040c00c0d5000d00c60f200c181c0d211351001c02c0040f00030402d11080f54001c44009401c6031240011840c200d004840f6203503441403500c1101c0c642502d641d6514400484c0c00c2584201506c102c0500001d89060301d220401826607152040201c1d40c08500315a03200ca6544441c0641d8260215026a08200300c0140f0b555a42c3c24000b07001500f00168403c881d020103a0001e0b030022003a039140c001032441095080e11040da0405023500b80b4060400311007908000900e0b0611500ca0070003080b0045405102c614032581d50900703205004041400b002c2c0c08000f0003003100c0e00c1030749040504245d25a80450408646402061400c25a40d0741d0001c81e103081580c150303981d800555050321904128040d04410f00c9107036650700034014100088411f44a0b41101c4142848a80140c1404200288640481c005a203450303500da50500026031100d608035940710350800c001524a000815240c1d4010f628005100e083c0e213003440d0349100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 444919172 1250 444917922 444917959
    0x12020604031403062106010e0a0c090e060616051606030c0815030118081b0105010305030a0e0d12031505060405030d03051902031e010902090f120f0d1d 67
    0x4030541e10800c1000d01002050031030f10342a0300303401032107603407045ca100c0042c81000803a9208070912a00103204410000180c82c040140a040040b0215885072043e0500f00003864103010740c02000907400450900140141489458503003031014044c0001e400410001590746150518903005002451b06012032a50038070b601200e01d5a001050351503584880d410440024090315014004250702c188400f907030b03014024a0401071800c1d50340e18550a1907140c24151050a0381c800b4403024215800900001c3d030b0b0280200045c007851000100903c0c103032946992200e410005610303003100000c1d80c548100d00403410300c2003004060042269003e003440e1900000a0f81c1781c0f00140700c101050744800110b20f1035150720036107401c2580c000d00103544901d020000b48001603072200201c0044403000d000020b11100d184216903240401030f10004000042c88140140407814054100c442d01c03803070207121601d0f1411b210084041801d42d88660180040010400c15150321403813261090b410706c5030301c00400c42d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 444920422 1250 444919172 444919187
    0x6070503010f15020708030c030405130c081801060b0409050a0e01051603090c0b0414090c030c040b071401090803150f1e13110406090b12040201200106030b041202060403 75
    0x61261a03c0702010300507a204a080903607070303841712607548004101461214000700140098407415a40800124440e201c6401076412600c80d04011441c2c520200e202c4061445401100032203031400855a0790342c03889601d4035640941d01052181e075840c0288003e02009002d00d048a0007400001d10183c00c003d00000703040500d030003616060560318a64441080080700c100780003410302d100c016488594503080c03011070b00f800303a1050388144420800610102c42d07243c15280500c0c11200c02d50305050034030701603510340c0c1d0150790107580020440c2d0490159850074003485003a01d10811500c2d80320300340f40c1e0f94140c40c80722020b02c0740d201e0b0101c000405019243d4242052501c45003010170f144041440c2d011400b00b40524100d24001d0382031007074194618850a00070011686c966440c000095968000026107004550901001001d00300116000d58071403140d42c40e002c0c42602c074a00e0721007041900142110b03142d91044412113401010002480745035020f0709101d00e01d80c00075103410701e0503039001804079 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 444921672 1250 444920422 444920429
    0x7060909230f06010207030f12030606020607020c0f0f040203040606030c05030102070512030a060806040f050d05030c160203010f0e100615080a18080307081510050904050411030d1106070503010f 86
    0x2d50841e0000d01203038030800550b0011600401c01807241e1517a82071145c7c00d01305d2155401e011034201240016240d20001d035413849520759a000d400142c800404000ba043c241c2d116095200381c0d440a007107800e50712440107500452140b503000035058030703520b04012000303516800203120740d10520400300403c001140914a060802c0c688a90380d0b030300c038565000100820313001199a032240c4400c00040188607030000c942d0a02a03801c84202e142046c0c0226914801114461035052042c0440403101c9040324589400ca44000c002059404451840004690301c00e824181554483c00c0c03841406440340c0b02d400050062001500782c1c0415103c00070f0b01d00132002d00035010040c1e48200104800c880d000b00d541d025079000720040d58900385923200808610301560b402070020454489a1881e01e403040301e00d2281441038441c542040d0071b1030100401000c1c01003050324150172486c900461690103001c2840d624909072101c114080c1300f5020310b07242c034000420030380500004100501c0019151507800f07084 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 444922922 1250 444921672 444921691
    0x20721090e06060415080a0b150d2f041e0b03061507060507030b031b100e21010212010e041104020c03190305060f04091716050706090923 61
    0xe440742c00114600d0701c03c0740d006114112035001003200040d4002c45690150540140500030810301030200034078a034841035290b41149082104400384030f155007040150901e80032086038200710100980c1c42703096902d1505118450001810711840c2d45070707800004d05a41c0507100740d0300a030400290303540da03100c0500124840c1140c9003200484040072800c8841c99603020a0611440c00c0c0901d014001c1c1003c2e0043d0380c401d000b1480c0090351414042e5071070b03440c01401490150828502034060b1f8007031800ca180b40d0341003003000707241541d800058038054034125140310005070b44420340720804070042010703004002c1c4099007506201c0440c08403c02c284104004440050b540c03408019294994801c5444201a00310080c1c40d03029401d405501441c4030300e000741c482d562001650301c100300031034041504c0101108482a2030b0b9000c1001c81018090001c140c440034010003815407901494107040b0342c81752000030380b900c40500c412012401041c1040c14507a0001e400c481c503003e840d106000004124062 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 444924172 1250 444922922 444922949
    0x2802040905101406040b0103020c0a0201030b010c2102060f1b0f04050d060903120e060a1112010f050a0902090f0108060103201215030d0c02190902072109 68
    0x24030800340401d5075035458401007040712100803e60041c40f100c0c21150548628034040254402d54001d00840f10412032000c00b0b4203601d10607a005400600380b8003100d41c1044446a030940014060035540300b07001c040b582442c4408090f041d070080c0380c070000270500c042c0f42c0348080520025082070360000e0b400c00440c411a0b61640028003001d07080f40030b00d61285901030703607400c0e01c84244643c5910040e000341c025503554400303000c4843c4040a4442482c41e42001c0d40c450000203010b415a0f501c00b524040312000c0d8140f800c0342035043c1c220030b40f03002e0f00060008284040c0402682c60402841b000400b1424000d42c10b00103050000780040440c610100d0600450340006941a80307e603004100031856281526240100c00000640540011420b10081c087c0d8101007403880303204000100040754010001d2584541c15181156540303644a0200d8000c40b01921921044034440845005440010001a11054181010900780b00340007080321003080c44032540c100c155840411070080e106600036060 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 444925422 1250 444924172 444924191
    0x5180103030f1b08120106050f0909060307093303030c08280504031a010f051201090506010e0412090608060423040f15020a020a03031d061008280204 66
    0x3c6540036010906000c5403000b0503890104007a030809040ba0041018501c4116a202c042c2078460740700e2481c00c841d900a040c00003414501e03209843c03d6002c40c0c00b500f0b0325029035407581850260707004140441c202e40c002058003100d02d1510f886900012200c20303030444404e80365482c0a050908201000b5200080001c2c03000c15010b00b21082461204000740454803003201c100c0010801d0b0068002203e103130b112038400414481e40305580c00c0c145c4083c122000740c154580810003985050000000c0d03031039500c807075403500442c60504c0f05c2402002140305d40d04030361501e441c00f80d9030220045a0502803181c0c1c2103080c40701c50f80c41215690700400c195030015406503009071320340103040d000b5130903c00d0b0f00c0b080e0204010400000140c94940f07124440d50049400150030b128240d0141c005181d006074440500c4c07001180c425005000e090300d58804e1111603c0e0303030151190918030704548003004501300450400c2048070400403030121842c0403900c1c4082c8012801d80c2005030601c404c003e40720b01e88071003009 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 444926672 1250 444925422 444925427
    0x6010c080a0e090c0a090902030c090108090a06060305030a0e06130e0919060b1c1502130e040c050f032b0201020c07060306030c14010c14011e0509010605180103030f 73
    0x2410b0403200100020428900344440004940c0000b42e40d03800100800000205403246000352030003150040c4c10300c0e042480c484011103c0901c0186101c4541c86441e1044000c14403038407030754001c0c60003803004e169100c0200030090050080c8505a03402080b003000311444040c4103101c4d040540d1140d11000040f5182d03010103030b181c5155007a038060342d014940720200421005502c60002400c060700c070700803400107601e607201214404072009403002a100c285004404039544c0208011105000e541c018140c40b4a5a0003104608407404c039107101c0011003e00040ca04014201c0c5201c02c1200100101c001c00907046102c80c00380710442c054600040e6954074964005e406450703e0f4031542e011503084591b034880050150072980f0040e10a12203083c404140689904940094240d044c1c45103503407016070f903549440c004404808540ca9540c0c425803449040c001d10301c00c03d04950107540c00f144d40d0034401c078040c1c210781055112501c81d520180101c8011040c20007920304613509420180f1000b02c101505 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 444927922 1250 444926672 444926687
    0x1e010c0305010e150411041505041401020c01020616022103100504023606270301021213030314012709021005070c08160305010509013305040903230306010c080a 71
    0x5030125a0741c0a000300c60958050b0291048500c00802f081c6030100940c0160384910018106500503041000041d440c4c0030060120300030001648100e40c4480b4076000b401a07400000d540e0100007540000c14002002e80c0321200c0d1000c0d0104039011881c158103001d00c1c0e015a2001a5000c11503400c5034408840d6031082004188442c0c0090f06e0702e90344a510f200c0c180392004509000040302d02d4a160b034200207040500c02e5031500f05407034000c18516100d900000c80000c20202084041503120340014211100600300c0030b00030326100031030b00e00181c4038030803c03800700150b06110100d03e8545201c68000d03982c0d01c00036008034807107803c100d0342d521103a080100504078150008c10041c0704480000b010047c40340380600880e4001e900070080c41d00d40340c3d02c40d4240d450600100b0102e07800080214030244c0715613081045600b070550f40144807692500401c007034a00013a0160301040e89402000c5111402400707400802c0402e0320301624529207000064000c3d48004409081410085038128000340586c070f1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 444929172 1250 444927922 444927929
    0x50f0f21070b0a060317070c23030a080a02010c0203090a05061b0327010305060315190e010506010e061c0f09051903030b04060b070b091e010c0305010e15041104 71
    0xc1a452910b0312148100c00362141d1700c001c88903404071044001070f0300d40540035141c90550100f000d003112031070705000c000c511820004d1450781f103a80c0849a1515601081071b114828411410310f5216000b0110280c2125050000c0c0c40641d00108490741966a07884840402c0d82c2086880540380d07501c0c82c0e900d402045456210820f14400001d16035030110702440040448007a19584a00d80316504004401b655015198035416600403c0751000d00d80d074181c10698410342036404a410b464002c144001600c1c0c0905140b05141d6444050100035680210301f40c28050055a0844c500300390701501c1c0e04000c400b1030501d2072040d07861980500c070f0407580d004040103179004401c884645400309100f07450903030302c10021070110340751001d11f1070b250405000d000100d07054110400d0511f10681c40b202411140108005203034011a501803030000b120500c1104240300c441c0001824004004014044440681000341034908903010840c0d40d02c020074402c80e0350042030341c01182250100021440e54040d540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 444930422 1250 444929172 444929183
    0x309030c0a03050c0610030b0f04030e18150420180a090b0909190b0910060b0a020f121605070b18030601051522080a030c050f0f2107 59
    0x81c20301082c540d010002d44240034603003040e40d20341e131200200d4008040782844000d098109903c0020641da80701d91046d5445800f0b4142052300c1e2101c0000030740000009140134600c03c48807002d2103510038500c1e103034080081003640c04004440416010381410068819035038002200000c0303880540744406e4240311817000c043c00c1c07204015101c0300ca1002501070402c0040c00b8018000001c0e0100c400003440041626024105107010321807601c40042d0709400400c1c0350f54a11a444c61640040d405200c0c0500a0100e6101640c8407039103000001c2c149025442c90b82101d6000141d281d458150348401c40e00d2120150719003508483c5a480c005040c400d161388a03441c0b00e1004101280070844900522070b074031108030140d8007213a8840c400c010001d11400781d000b0305003030305003d203c0340501e8040e440040725107d8109501201d90360f0780514a00219007e080f00000c1401c08070343e0810004000c030f040c44410b80406802c18604e02002075603113600101c449030340100c96040d002d111a8a4404640c01550001d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 444931672 1250 444930422 444930433
    0x190c020604230a051003022803021e0a1e030e15011a0c03030c070f0605011d06040c140a03021c0903020708120315060f0a0c110d170309030c 62
    0x1a44594510000e22034500444102d0b08a2911545400b8000b001903910051559450003a6001d08078000d4000080c95901035110301d00d10b9240e02c00c607100405404e611a9005681d4140340c440c00a0402201d07905003030304201c00d00ca8404140d070892110020004414032015101c1022401200900341240300445035000701008080c1142206115a050301c440d04c1c1184010240c11061072078071711800b40340c21441e4201f4004500c030102d5590042070224090903400240da038564542c0011604283e004c015090401c9072a010005c00c4500f4695000801321003c110460500034040c04801e00601440f42e11500010501d215038080d50640300c4001d2005040c0404401d00940c52004101c1010300b60050b1044103c0000c10400008514824811228a0382c3c1552100308029501a06000c420740d0721160603ca0f00f0180d14a03a005803000e03004c15136890041d03186600709018141d218220450107000c3d001c901d00d0104070b198522400e40740318403600aa072642c2c2d070404c85003507005810010700a8007070b1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 444932922 1250 444931672 444931679
    0x3050c01081e13030e2407050705090702060103230c120106090c05041d1b130306090b0a0c090b090603100b0f03160c02151c02041d0603030f190c020604 67
    0xd8180f07154009103c3e465030410325a20008000048030000c1e00c501d048030440309104480d079182c3c13000d02283c81c860021a8000d5440d10005072400c01c04131403482c01644000c004000788031100d03811450081e100ca0010341e0440d4a400e0f015240e5407030418444c0100010407a01403120800d5004000610504034100002100e0620051440d8824410400700b8009800da080c0c6411542291a002d001284e4130b90340c98405500b440304258001000700b601d08021488000080740450080c048414407030800030580d450240107000480c2c144901a008100b10036900b4411680c0e00300c21201a040c040364215240d6031740c030f260502c2c600120303080300041c1072020a60001d80c2078400c0103940205100583c40d17090300038000d01258046801d80700030b58030103c02c10640d070410300400e004040c181031400080807959508a0a08260b0b8000e0b840017481c0303244035020861076040c3d541e0058100e50100c1c0654a40a00e56a0b0542240a45018400b14882080c4105c118278080c554076105e640e809030480d5180c566 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 444934172 1250 444932922 444932941
    0xc021f0e040b04020a020718020c1902190f090e12040b03060a1d07050711100f020d05032a0c0607020615010e0a03080c0111040e160903050c01081e 65
    0x84006240d4011400d240c0d600265203881e0007030307907111951603005101461510341c181c140c01e20032849100c4400c1e420800071003450004c0c0201401c2c0300401d2442d09018030507205004d0030550704a0448041c0c0e4803800207016420700c512001044843d101804561071b00c0030031405040100754401210603c40014000a00d100b002000d14411a8122032448c100d80e03541080780c000249510003c40c80d10400710001d0555070003600940301450140c41c0c46c00d800140d0340c01017440c0c94241884640487d804030000c5451076410003882054030300314503100d411801c001803070003600c0c04405618907118001c42c0340c444802020000b51501380503003200302c0c0c000d42400c5074041d440d81c13415944038820302e01011001744194010035100144007405090b240000e0701c0c1d51a43c2c405600700c1042524070f07549031415420300b800c900020344043c2804040445680c20700b80e03413030b0101001c40c81c8020140051210108007040f800701c0c50341c00c50032081c00d200c0050340d40d410307154030002e0190007003103080303940042849820340 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 444935422 1250 444934172 444934187
    0x5040c03020c0a0b100b12060105070602040509040f140f1903020a08040905040606090c0206130c12050102030f072d02160305030903061f0603090503040509013b070c021f 75
    0x6180741c5d425082ca41e100e40d04030500f03116042a52440e41c0600d00465a01d510400052140c240a11401418240c49030001905100d040c0c1c5c1c2030b00c01c0c40000100744144406030071113840443c20030300284030811510915035118940000070380000801040f00906050003032101800041e0b0213802c05603140e0700c07200c0041c01803909071000d5400514002c404542c540042c412180c5c10340c0f403500103001650307030300000e41122034501108660400404034001144011481654012071241c0300243e160b00e00081e121148a800802c25410800d007042c240004d10315043c0e0780b2800b600f8101d00c810581c05100001d030728048002c041446200131040c000014850048050b000e085011030580344152030780411400300880c4500c0120480f070b10102c0403c032050195102d80f04080c8503405aa041076034801c0000e0300b1841c01da1005003507205125020566a80c4030501e082440c4802500d001d482c0d078101881844894010280300601036038100384010741d07a03012080c10000c1003500b40c00d014282100740082c07014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 444936672 1250 444935422 444935431
    0x304030e190b13170d0e0901050d03080a02040806040804050f010c021302070c05030307140d090608070f021921030204180903050c1504030e0303070b0105040c03020c0a0b 75
    0x32204a56000c40d86840000d00340002481c0320940c6180c1d0520745901101c0e0f204602080c902c40c020358001440701c0304048031070300c0e141035140641210711032010064800007544014a216074800300050002d41e83d48203000e044140c2620781a0f0b80d9070b844110b41802881a5040f0384001d00c40c0300100410482c00c1c0006105640059070ae01c0c0d2f401d1070340401503441ca12904c4000307601585103002426200c52030740c00f40107418065564540301c95074403000700742941d0040c201968a9801c08401c22100c48081080b142880c8407803510008191030028014010500540f555040140e10040750400030700c04c101070344019280741944000c000040c40c0c0041140104900c107a034000043c1c8908034154000c2c030944040315860401840e02200d0a01040700508c40580c0c21800d125050013481505002000428078080390030054900f00d00300340c240030b40810314082080748694000c124020002e84003010142c110341068070007150b506d01d4001c0582c0a030284004410403403007a000b08005100143d02541e008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 444937922 1250 444936672 444936677
    0xa2a0f030c080c030c06161a040506090601180c03060e0703050a051311060702220f0f02070f030e030c0d05150610050f030c0d0608100507020606150706020d020f030403 74
    0x41c60340c4040e0700d43c80301c01c2c000d03145034142c000340080c0c1018103044009100709840d1400000000005944115075440c1490048110415003400c00040000c1046400d40040541c4020a819850b01195690308840c00600036140c1d51a04920303041c841c004d40003240503200445c4440d0302480c1000c0c004005240031588031010078141008a11500b80301242c503462a42c002c07006c501c101050406020255202c40d000b00d802c0310005141c030040c441c44268070000c21301d0401c0045408111603612005494469420519242c4100003440004100e07000c006491ba5141c02c00382c00c40c90941c0000780c201011302d08810340200180003e1410058041502e01700e020080c42e01c2081d9480d0b200c1400b0820240300c6500000c41e504012088814064030302440c1e0103070200b00e20a182c0754810088805440e0941d0009859030701070040640f40301c08600490380d2100d2203200800340c03807400c41e0000e03032400c503440c0da21b0300d00110001c0c6410074055250100c0f04101c1d035207182950307112a9006c00300e6080c1d0003210160300 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 444939172 1250 444937922 444937943
    0x180b18091509030d0e0304050306010f060f020d051912051914070801260106060305150130140915130b19020c010e07090e0303090a2a0f03 61
    0x80341003420441d030181c0c003640001c40c2000c024186000040c1310408400102e40710034000003d1030350742085510301a04051219803819441d143d0080c0c04845540717255820b540058a5400382e1a03405000d441100c02c00400c2c01d184142524010b44411004414180d92242040c1c200032180f803065000e00a8801e10203030400042c42c0b469a0318254000c1940c0000004041100400100341003200e41e0b9178120300c1c01002c40680f034008500e2803c440c06903211030082601c5108003c04030f643d549242c0704d010302c28200b0314042c11000078a5541038581c1e901089010700300c41307001c21801010741e11800142040b0350741a0280e05084800d141d6542104005031312018080002491902031811003a80a5030301c02c0b45c0c803140e40c0715440619518800c00c112142415030900025035210802d020b103d924107501300140400d40d00700709408043d5400848103000b0780c0d00801c02d12000000000d104040b040c0c200806000028002180f40c2c40004890b42800001d0f41904000c66000d48918040b002c5034822004183c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 444940422 1250 444939172 444939193
    0x1c0f05011e0e060906150310030c06020c011224240f0f03090f050a03080109060b0a1e18090618052710020a0e03010b0d0507180b1809 59
    0x206010720500034881040c02072404126a8200a1611508100c1c01400120548640f02e141c10050f0412101c000980701c810608105009914102070301620803403002e042140d94110020300403207094071201c112603130b0702c9070b0b507403c03254811003000c801d03c2061201000d42a034602c5079101c140c0040c12803030014100002c0110665014000ca0700c10f07143c4580325040d484801400c160006c2c12200c90a6034200b440d0303400013002610030700215080e503200e510340285a5040a14480440e0ba141d08200c040800812408100d02e401400300c11980d4400d10301c07c0c049400c030000480704a0309290200c000c02d59000804a80300440ba00080f0691382c2880e1f0095290308a00903090540703000341e450442d0001002d41d00150003890014480d00e1f00110400c0f00e100031030806204040343d105907034000015a86207100c03038480c502805a02d070003910132110505003150a440309500e0380168030500031050501c40b41c034000b0800380d402500c2d0340b140081003030481c80c0c0c1c0c02550100c1c0d80f4003110044118050b600c02039 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 444941672 1250 444940422 444940469
    0x51c020d1a0d0807020402090916030c0516080309030c0d0809010b040b100807020c0907090501110607080f07030f0519230711031e04080f0106060509061c0f0501 71
    0x10310980340081020b40d8204040e1960415035220b01ca0503a002502001100e48607240e41c081c503130003203014200c4819800000003000b400c4904202000e020480200b03d08428a400d901e0041c1c07c1c03e810001460b035984849100c5403440c0b0a000908590303014030324443e00e1098101401500c2a80c0680007400b040c40c2440c00c010407a2112650141d01100d041c8540700b4461240e90429481046401180d440f00c8046002520141d022079802c000601107100610181d42e1004058102600d0f00c0d000701481d0409140250007204001c2010b07464004140019500522980140e01c0524900c541000a820401400710760000c000c00e082c1200da060002c59a090605c1c880400005003102d41078040300d480300c032011255449139071a1000340d884180001d10320494a250302102c00500d100c500c03541c4910341100c0c18140f141890010315030fa40361940800072680c001e03088070340c049070490700c0b070b540c80201400101207549240e411042c018a4060900301209040c0c1c4020b050340c5503405400600c0109a00c603 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 444942922 1250 444941672 444941711
    0x70305060f1f0302011b0602070212060613110406030504050a0c0803090109050102030c100506040e010203240102030c06040213240303090b0403020102150a060e0702030702040b010903080316051c020d 88
    0x5e001071803130b0307110488004016a094619921a82c0007525103105c03500055400c001051031800c0e250080c005100700c6180520b501c0603c01e26101d01400369045e01c220604c0107001b10301c5400c0c14103450740d002078200001030080c1244160701480503040142c4908109035203401c00114030f400306a228a01080542c000000e03134440f0341702c41c1c0c0204140181e49064201600c2d001d03183d59009078950b200c02c00340030001e0022f1441140f07112006100e501028000b4400300d0b07540d0824a0540d04100100300d040d40c1d0124803168000d805488a034941504400944010420700e8100145004030307001c80300702e01854002e900b08890080d074942c2c00c07554444403400514412803100a0140c2d00000c2030004005031428030035813010034140c2c006407880d9901741903802d41000301c90711b00050b040000e20030308615091090f030001c4a002c0c41c2c51040701e1f0955456042520019011000c90751300200c08104051064040b20100056908903c0d011001700000310302940016800c5641242014245c000303900c0030001d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 444944172 1250 444942922 444942929
    0xf08091c020304051302030a1802090c070218070c0308010f061709072c0901050411010c050f010e0709060e0c1e070516150201050103170a02070305060f1f 68
    0x40c1515a06000024500c0c0c11044200c40c15070009010008096450714141115040c120070056030340e03e064680d5401300c07000b42d2401d080c00c3d544d0301802c50140e00e44101103a40085c8084d01d441c2d03500e00500009061000038a8800c6180c034080007080320207a80121025015446600c6284040e620b078403145901c01d142d4042d1600042c0400042c50502e800d082c2b000703400901c10030589020b141c0b03415102199450300d9a10101d80ea070382c94806d07120740b07a07a01c40c0e940d40044450003c00c8181080d44d9104294907080c60950304004414482100b0711005000e01c8080e500e006000700103031100b00507055103500c040c3c45852180e510344100000c0080d44100420f05c0341d14410b00c081e191810000c0c5000c8402404c94940c6c041600c1841260001a002c00100d916203607810340c1503500c9440e14910302c02541c0703c00403002c21a41810b004100040c41d0203080070140780300101d030365243c000c1228100e02e040905d1780090324510408040c040c04961041c140f0340a020803823207144000c0d000c0741150f000d80d41c4910 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 444945422 1250 444944172 444944191
    0x70c0204182f1509040204090e0d02010c020a0803071701060914030609190f060c120b120d0e040b04050a0b0a0e010f0b03041509060e160b030105130e0307030504060f08 74
    0x300840200e2600c02e03010101e030b10f0b890504905142090780403600701e8000c2c2e000301c43c0c01551000b032480486010400503402084130700c0240004001c0d82d0000f502c442c543c81d00240400d6003c00070400c164012603141e040c0c40c40390801c4241039a5a500300901c03040e001d103d141c45000702c0d02c00000e01380c1000716125200d114401d004102015003114130142490580301c055034403c02e0f40728a00001001c9006022580c0025500e41c289440c160a030f03030049880e19400144110664042d00051041c04038040f24003581c00e06003841090141c0011401800e00310b01800d40c891300d0042004211a52a0300000c401c0500303880341007401d83c4465443c0452082805908661009034508215803441c00000b19801880740c1c400c00200100481c408007a03c941039400c441e100d4441c044020301e0b0354204108460800818642461a0f00e06240c074a0680f2042c0545030140d8900700200800a02035007000d400e10180004882e9602020305000303000e03401600071100010003080419076540d01c21051300b401f840f1008c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 444946672 1250 444945422 444945503
    0x50d080304050a0b090c030d0c2a050d0501090c0b0a02030417010b090403050d0509070621060b130320061c140915010905010617070c020418 62
    0x292544041500000e00032205407040c45582000103601500090040042d800102070a0400400301424060740303455031410800806402400f180801188154240c1006402440c1c03d194007081d01c1502840d800098200b40c10b41c02071810004158441c00340c2c180240100200151904c0c00c0010b83d01c5141a8000168414042407140c81d008005024444814400020300c1600a502007181e40800322030a5000c0341022640d44501e010134001c00790300242c0d800240c52804c0c01c0c080098842401c1030541038100040e03015070b058040840d40500d015000c5041c186e6290f00005608102d062002d0004072010a030301d034505844002100c2080c13115610040140e402c1000f0080d10759140c1090f0025044c289407503003aa52691004041410301941103100917010045610300e242090072410b901c50321469103440c0040010a52180181060600c00084065242c9810030204c501c0b40140310065440b9140007040c040240030000340840e001d100f0b0054a4030310340c0043e003841110744003108612810503003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 444947922 1250 444946672 444946699
    0x112020a0605031306090f030807030c09060507050304091418123007050d0c02120f0a09090501060e0901090b0a0e060102100f1a1914040f0c02011e0605 67
    0x980701035a0b2080c410350130002901d1003600c0e003509403184a00c042c2c81d8119407103c80c01c14190f001c4000d035440303080c5040501a070149003000400151181c8500d41c1044004031741d03102001800d00413140200030f4400180588859448a828260b00c248d80328400c84071070944144072604041a000c0c240100b400c40c0500304502c022081541c0c00440c403542003010101c2043c00880380300b40c03015034083c9440b42d903040e860350300c007c05c0081140c40c1c3c1c80b82c402c2550300c0000c0f401840c8604a049a4015031001011602c503e5410410743d200081354010180c8641803000104405a00010850340b83c0d0f0102c039110710380c1e40e888030f0f072204403225040c180c2d030441e4803100280040c071080b40049402407010f2040314802911100500103c40c4e0301e0300018580e50f100c1c901042482c8a0200c01c1941c0c000c1205c040c0c0d4070b000400d2165400d445140316260300000350440300203c9944039031080f0141e03031400070b05116942d0302c0c0000a008013a40d00021400b034200c00ca008030f80e41c410b84508815070f00050800301c4845507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 444949172 1250 444947922 444947927
    0x10f020d08070e0d06050609061504140f0a030f0302060c03060907180506041e080f0d0f031814011d0a02220603140601080a230c040e0c090112020a06 66
    0x10718078030070300203081000202134580e20080e9080034003c890014240c1840020040001d82c05400c051003100400e640c04601c840ca041140c0848540c2c245420040c107805000c51000c40399107400503800031640d5000003d100310080d207031a030306129a003650110b9075100c1440d606030005a442a812a02640028480e140510810100c02010840e50140595030b0400075103158000d0300a4180903400c0720100045010070110341c0040e04805010b01803511085c60000da0b05c40c111210352042182055249a10728002e42c00804d0840b400000d101c2c9042c1542800400002556812501580390203c20030a8114610080403940c2211024100c83c403910340030441485032250f09078060b02080c039101c2c2680c282c548110002184299000c01c041e0f24084442410400c050f80420aa9041141030304001088a00100b0007002c2103201e03104811a0480c5292070003214045081d006403801410340c030350180c002192000f051041ba009d490341da0f00c0c1c42d09003c6011012600a4000c0200344041c0180760 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 444950422 1250 444949172 444949187
    0xc0302120708060a27030206040201120902030a0b0f13020616140703050706170f0a02030a1d0f010c0908030a0f270302010e041a13020c01051f05010f020d 68
    0x80e140c104985615485071042400c00c00c0613641c6030382c0c451782c0d9102512140141d0080360110042d91800da038081400791400f946640300100f0090411100f5058485000d480ea40300402094000c1c00b12550280149481c4811000030346801d403c806030440098030ba82c00800c1c11409555000d02141c1c1000b034040d00c50340c0307544046603040b40c0c011001a2140c1305504100042e0004500600c010800185001030181a00041d284070780c0325460404100484e0885100030944c00c0304401c240141d0ba5a10644544028086906941c0d1112303040800000f5104002604200104100b40200b00c2e4015054040d64401040c2c41000410740003442030040040c050580f804050446084c03100c854401803201d91b001c04044040b200c214400f0000610640d688550554522034040e074041048070324415110408800500c03186204c5c0d040c145444101c0d42107901904c80d041c500100a10072403c2980c01d921443c40d01c3e440007114200003103070029480d0f2156040968400094014140b0440403010440c0c800 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 444951672 1250 444950422 444950449
    0x30312050610121d01050f01030c0e010e070f0306050402160b0702011a040b01091a0c0d09030f0204050604150f17011103070e01051908060306010f0501050f090a05040e03120c070c0302 81
    0x100e00da6112840b010006e004d1244a0a049004418198194900100f052559400c210308031580d940040c0908a00d03507000a402020038100340d5040a00b00c03800320040d020342c0e00a560818000301d048800740059110b08451a4481c01f00c00e01e0642d24103100301c0c01c036024410034004440d0761400a030003509282d444440b45420626007501003a459125107043c260504541140c3c0c01c0c40011010040c0c40140100307502c4001c1c614000200a02d15224100d034108468806845a6901d901041150341e50f580301507243d2180c40111006669109550b11020483e032017804098031503065989940d40040c418040d42545080102e4250b403180395080301c061201102160500ca41009140c0d20031203020400c0200302416a6540d21074600b50042c1410050180d10280d48884001c1c4244616a0400261120501131038400c40e261510800000d6003119a9805250010f14041101c4441c15011004050150090010b80c810781c8413149607445521810300c1c0541512030300741040c001032600403c8031908 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 444952922 1250 444951672 444951701
    0x9020607020306090a0b0708012d051201090311160b070501060b1c0b010809281a060a0b0304080316030231090e1902010504080703031205061012 64
    0x2031021550100b841d0290550f802e40103544012250402c010010301c200350700540c207207890362507949844580a444088102c5c14401c880c05468210600c2c801544500c008100040c41d544031460000301d014000c1400c10001e40005441c41007001e406480012018905200c05407500074051400404011903082036404490a5480b000000b8030403e04070042d10307440c1014110f140710103145004080072202e280d0091410b00103258100109100040344285641e0800c070425a614004101204440303002da40004242030360f08152648500c1c01918214490039080d00da10b8044d0b5280e80000525000483d0000d000270350410004041c810a10949445409141805400c3c40315400d214104c101150340e040303020541c5000c407402c158078102c03c60401441d040c3e0f410000d403458074410548811007900f0111103040704640c1c0c8800c59201e101160700409505041e512060349a10700204070443c02c41403041d03828286000f040840c50040e0031200907240755214410b01c4403010f0230140144c680030b02041e40 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 444954172 1250 444952922 444952927
    0x9180b0d2409061a01230c070e010308040f08071a16080c0a06051501020303131b0303030606030b060a0e0d08091509090f011a130b1204030e040e0709090206 69
    0x1041d02140c000c9400c158455240850401040043d0303070007118005003200d04000c404424a00c1c40900001559000341316607030034076925004198064500500c9920540740413072084000000e018400c4090010f540c0703120310107051141d80324401640c82c007980c000c8021091100480d240030310b4950009090262445801206181c0307941c540200f6078005134503900103604000c02c1c1004002c40c1d40301e03d0390301000d5404400c000ca04003c00007580da01004201d2031070301e0303484c00d0200e040c41304d030680c0c40b041c60000a0320035018a0b107914000300946014880c6601180c00c144d41c9186600e050b100383d0342d8050752581c0d901112080901004451581c68000f6140041c040284140c00d40701e4900425802d401800865903032400b0b40f05000c24098000d2001c0005105000140b01d00c0381c81200d621141c1d0b0521030695121124071542c0031303000310540e0003002583c00001e018040b80c008074000901c111b00a80340c106c0c080110400740001e070744150098541c0e82e000920240000243c83e07001039002c0d400642010b0 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 444955422 1250 444954172 444954233
    0x61603120c03020c0c031b0f060705060c120c04120b070306050307150225060c080d09060c0809010504080405130617011d0a03050d11070b0709180b0d 66
    0x4807400d0018401c0001d40015012074000020464a13001e0030b0203030001c107000c03036030b0300107100f0340c030810940b5607114080c21607121040e607840c9001e0366420780e00503050f145c06086c4410300c1daa451388045103022000310708000043d10b4000920549085a00950407044800078079541c01d1001c0c0d10041c0814145030b52168007244c60b0320201312107005030071a0300f0100344103900d82d41c1c041d01d068107000707016800411040810440021800f541804c6800c2070030300c42420395140c606211a409101d07034188295140103046414004650000c110010403602c03403400e17039201e05182c4c600b40e52040300c02801d04401000300300701038180341500f1740141001800025607207450342803a070000e0050f03050414043e07440d5280c4c00d1031440b5000d1500404558000208035200030766801400c1c0340102d4081c040e100d42e40704002440e80c070781007040750300351030784500107190754900030700d000d0040240e80c021140020301003020710210101c2803103a003a15000007000030072480420385e180041c6011504140580014958820 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 444956672 1250 444955422 444955457
    0x20a1b060f0e0c030d050703090b030a051b0a0e1009091103061c24060305030c070608161403070c0503030a06051c0305030403200712020307080606061603 68
    0x25192194001003820250a95614181c40c071050340081c458011a00f041c03101c4d94002042c180240b03441c10b00301d8586c55281400e940015850f4004060030b1b100104120800c2c006512007031050314004c14070302d040c1c003078442507501500401e448038000c281d08404162491410b0f121652460b040b615082c3e0b6200e840744408000c1d2184044402c1d8121030200910940345812002000d18005550404080c610a03031a6004004100036901c08400a9009000f0311100d041c0c004502868104044a82d0b40440b440f41d80c2d0b0301e15661188800151500000c20804a03890071102804c840070b03500c4c42080582d6840c1807007607034000b60030b00043c402d6240c01d02000072000d001951186511040c0000e171240ba1805104042c9103509042d204245815000800079410805aa42081d0107240203c2da00b0926001b040d01c040144090a41038800e500c1d0000303503800201d15180055100b9815640c8169407189030070f0f076407442502ca996120206101d1411101200c194000810b400b0f8504080380c1c103040c0500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 444957922 1250 444956672 444956717
    0xf071b080f031305010806090103061a0a0e1005040b2116081507140406110a0c0b0702120c01020c060a0512040f03031a0f0d0305040305010507080f1506090103020a 72
    0xc010842e08089001545154003182050041c0020309200701146801c3c4001200a5414000185403d61f48c003100a03d0032000700346a40d007020045e000340a4191580c54004004004407510030364500d001c6800300705030519018204820001400300b1722060411404410000140f64403201a40300d00395004182e4110310f0041c42c01482c6520141803803c0e60f584100744c6501000b481041440f101410058510b5018800c8500b01c40c9186401c40404821501c4a410514003000180c0801d807201c00100742c20020340010300c0d42510844240b80701d00050107405440700038020120780540c012425100d050304140e00200305480341480c1003031602d00789034040707545068159415640714601100c20030425404d40701d8440a000a40d1081c0c40c0c400e00f0500241101d070b004021a03000350910902441098060003c2d80d0285500a00910451428100082c049101140c480340100c1015010410a045054120750700100240c5924504140c280040d800b95110343c0000301041905112000741e00c207080700 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 444959172 1250 444957922 444957943
    0x1103010e0907060201150306051e010b03150f180c0c0703050a03030e060609070f2a03090b3609090109060f11030a20040810060b0f071b08 61
    0x1140300380c500703202080c68640740c456003049040d0780c50614030850070929030503440120303070303002034003080540d10f541c185004000b50501034400e4503407a10012849003030b40005988243e100d4048007800c0443d5408101240195010154026400712100d500f503000560a00c1d50161a003604646840049414140307401d000340d1090743d40e81c1203000000c08159050040400e5018400010314550a01ca40064059000500100e0078051003860100301940107030340c41c4c2c4801d010000c650107241e06005642e80546039894041300003e01d0000040f6454a804058071a00a2655a00340c02451101c160381c40000b04500f1509250851526002079075907000c8809105142c66000428641b4451030030400360703001403090360159400c0c0300c04200a00b548105403540060415004240c070201c41034107082407141900344666180e8002804100320314002a241102000e00b0f8003000807941e501c0b075242c41ca01074800011440b8104005034008106440c0310282400e01d40c00c000c82002e039079816502e280016000 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 444960422 1250 444959172 444959189
    0x21080705070f090506100c031808070e0a0e10020d020415200601061b021314040c091401062709060306050c0c0a03230d050a0f09170706110301 63
    0x760248140b00341140a40001c0c0b02d0b02c3d209002c0703414a64009409504044680410044048248801c4c1031203200010008644042e4118030261141181740d00ca00c45030180d00200240480455809040ea103c0c040e0303105030342c5002c0c180d80360315051203001a500c600d15404240f0b4003400045034105110742054000821625030b41c0014002d001e50084005410b031025055400180041080c50340201d9443d158507409141080c044110b0301c0058070300803200043c078088500c0c02240000042d00700d080e2502031400382c0b01c03084100ba83ea050820981e4141344d21442641000380040248074001c039100880301c0c96542c640d400865400107004c4078100c081c2e012000c2107480d054204244001071054a81103000c1031402d510384140510100d5441070748140090820240542c0e081c8480308500440e641e01150040080d910100401023801400041c1d62040307440303284c009005403801007841102a2190301c4540f50840d8094403407414440d41040c0015207940da1590b41c20320600103c003004501802148 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 444961672 1250 444960422 444960433
    0x5120d0203061e010203030a111605030c060f01030f1202030d0c080a0f050c090126090d03140702120c070902030406021e0a090504020f0705060403020f010e070506030121080705 78
    0x25010407009040007080324503001480d00101503d07076404021a0751244c030028020440c01d45002c000200c2c0c0c49083c03072800f0310710305141c140c208000c1c020008003280c0182d202151810f172071301031340700e42450f20a21008090074082107004d0000340c0c01c3c40e010300a41086005490404c90111000000da40d21031340c04400144004c41009050546445085c2d40c1000e00c0304200b209180120702c0001c9803041603130080c14016191180000c1c440c10030580400c01414048040b038604100c2e0300342e41c1c0d440e400900301c40824280140490503170030958919208003a0356008003004885606002c101d0f901c03240004030030b4014180013148424080c00254000c901c01c13400181c1d5003001f03ca00c3c20310b0742c0d04c201c01c00040d01c108104031042250700c904840300791441160016038070507024a480015110b40c0324010b1403402408108014581c0100700c0c41140c080c088000d11040c41480520f03500c2d0b00c1d0900803d03521820a0005214201100d00300810003080003ea59010005980394112a600507034002c64169008 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 444962922 1250 444961672 444961681
    0xb01020d031e15031514150d060c02030c0a0302030c1507020d111f090501060506040b180301200301090612150222080f12070c050d05120d0203 63
    0x100501419440645010441d01d0030900c001515401d0740701c002c000e81c540701c2010803590001015100001c6500124542c0c80b003000205500150140f110b58005081d6034100003040d25500044581c001c0c40002c0000d40c0343c3c1c0e16580d03080f00604080058108520040c030842c96844400c019040c2ca0a009800450720b40b4131507040d05290801da14500114000c0c034005024070a5000142c504503d807807401d00c41c2c0000002d44850f032a2103001802c2a0401d00c403590b40b01a40d4805610061809014100234400961190244103480c480c6204944e1a500200030348001802c900e8a00840070000800200d843c10107030740101c00c500194415411144c4000004004080d181e104ac61300070808070801130210655900d6250341c1d0201c450400d0044c50300062044180d03600764045840d80580092880c00f8030b030b151208160b030b41c288508249440c1c0300c0e001440d80390740391203025183ca455100c06541c6e1401d01300b005028803e0303100101116540325611002402c507a0031006804541d501440040e02ca00d031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 444964028 1106 444962922 444962927
    0x1401022812060b0414040902150906040807031a0a050402090c070302030909070f030609060302060304141009050a17070b070e011b0809031623010507080c010b01 71
    0x40c0182c0414034010100c00707041a601004031a844e824001001d200407035114100217580712004840c680b03403d4a2000042c22240406001c0034145650380140614010b4590011920b50381a540c2c03005100010309001c40d40840f0410081c015400c080c1c000c01c817071030005441007189660010b504c000f414020402c683c00b001028042039030390b18201000401e00801ea095402c00641455000100160350340558415a5002015a86180c86554407231401c08401d801c61b401d1402000101025101c0500c5640e43c164041c4020340401055860207410910203100308000f14281441a940490101101107912220b2400d105908488820068400380c1011a13603a0003022165114020044480040d01140509804a0f801c42400c410204100c01803405500c03a42c040300729141d05140d070401d20410f044070040c10020328248403511041440d90000b0700560780781c2e4417500b80c01d10550b03 = true := by decide +kernel

theorem cover : BRFrame.Cov 444784172 444964028 := by
  have h0 := BRFrame.cov_init 444784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 444784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 444784172 ≤ n) (h2 : n < 444964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
