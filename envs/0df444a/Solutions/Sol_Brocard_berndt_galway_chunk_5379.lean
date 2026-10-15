-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5379
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:40:49.420807+00:00
-- url     : https://prove2.me/submissions/32dbb349-c38e-48e1-8423-e31deeaf0604

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 967266187 ≤ n < 967446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 967267437 1250 967266187 967266199
    0x40306382205040c0608010303050d1524020d020c061209210301080c0d0b0703020c0a081b07120b010e0c2208100e030a03021b030d052403060103020f 66
    0x64802040e01c0c16000380321003460350b81d000c000901ca03290592001500ba6440c01c0d500a502d140c8004003103000300101d05124650f108000c00c4094000300d00d42d00103000d00c04030007110541010b00411520241c6258402500440511000352131011481c00c01140c002807040742080c101464065000d4001403e103070080c86034407001c4040402001003030750911400381c040d0b81e0b40c0d0304041c0b0150804040c078401c0c501800d07002e03981e078000851520045510003030750700d801610f46a0807441c00b07107440d0106c600605440800035820611031884484034001c0030807042103444403945c580f0000300340818044003800c60340e501c1c40140400000d141c5a00c1c0c01800c44c00b078013030400c0d0040140b02615a040340d0b03442c1c1d08a82c000c100f00704e4134105101000040300075110400048100542c115100d00c40c882e510001c00da80022845482140c0c0c0c049004041034040440e5103641e0048034078001001c050310180c0403072240071804028208034501c00007803c4400f801414040e460359003445110341418a1040c0c3c450 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 967268687 1250 967267437 967267459
    0x1401030225020a080a050d0c0f151a090112030e0a0e151507021e0a0305030415200a060504021804030f030b0d110f120f010204030638 59
    0x420741e01d140e001c0354645058403961180d424410001d05100c6a4050a1245c000c46112000300340003240114001a0a0601640040d030707601d80022141401c000040240120710040a04800c0d02d074451522042c00000c0702942d00894010482c4130b0354244100c000810200c01d00a00292003802050300581c80a0711040140d0f80301d42c80c214170154100c840e41010440c089101d0f52a1801c50030407401c0700c1090140c2454074880f5008503221000e140035103103050144400d000403503210007882000a580000642e5100c5440c0c143d0088078250640c012000030b4025919200815000c00000034001c5000d401452880e10507135038940a008005d009a0f8405d00c03083c2070855130000d03501c405106510a954886a04181050103022546007200c1113000e002c280800c0300000d0004484510124011600e170a080b520703210004610b1300e207415101c41ea46c090142c1d8400400700540141c41076910401d07041c46400d207800c9010f8140560046100410241102e4010000f00e14504200000c1c4018102400b01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 967269937 1250 967268687 967268707
    0xa110405100e060c0d02010513230f0f060f1006090e0604060b0c0f12030907060302030a0f0603030f0e010507030f0c0f0206031905010806061f0c02031204090c030e030414010302 78
    0x350050f0144c0c6543d030300018041e17041c0c0c0780e080c421554041481030000008100d507071940d0806540b0090200c1804580c00079001c45014104100d150944000b0225001c014101c0c00342601d03150196030f10071700c5003100d84c0400c0d00f180c0d10007115420fa582965a10b4201413510414298001c009094075420507501c0b00c0108020172008000c1c03100145000c01400c41442d0200307410303d080c46100030801ca1040c18000c0c003944050208442084608529026880e034454085540003007003510707210304078286048800001c040d04180d000c0303003c1366117481d48401c180c4010f0041d1028071943c44001c0000e1614802d221116026409400d00c2d21301910386070f4200c044981c080750141d40251070356400c1ca810105c0c00960648075005d180e015008200c00303030405080000100316445c5007003070782a8548040a20805140e03100c0c00444090907001400c44440c844060940c502661290003142ca690f4101b8010340400b5000b8004c0c00715299070b00005519007407804d0007942c052004910340c9410142c08020100c80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 967271187 1250 967269937 967269949
    0xe04080a0c05070b0c0f0d09140a0b07050f06091506090903070c0e180708030322060c030501051e09041202100f020901090e071403060609040f050405060a110405100e 73
    0x15044c00e1a0103a40c0710454901035161503a0200714144d2a40800c041f020300a500880800031140481030810030700004100058240009401c80c01d203110010400c0c0c410b001c00080c5c9908065220801e81d16203417190421651640143c5247d2048100d07050041012130074148a0154440600c1d01034900f400080ea03141e0700407540e107074000b151544864090011260f0511503c100c0c8a51070381c01808002e241c440b44075100e0000621b8282c00e25100310002917525949900c40801a130300420800403003900300700c060300900d421301499010b4100112112240310041c85000c030180f500501c10f04060ba2540c0c1c42c80c028814106e0f0804c11402101e1110b07801120034000c1840c1450f004001584404040c0c000600c1d811055015046414a000c1448641e58000980038180100080041ea41e9504c0304049140c5104403000641c12504d482440c121740754141c3e2209004030300ca107060310010386030030340c0100940d44a11401d0b4040c0c0c90801003086907251040d80310728240d120b800d00007101000c0c5000184 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 967272437 1250 967271187 967271189
    0x923010c060c0816090305071e0b0c01050a0f0605060910180303090314070e0f090102070209072303060a05010c0c050405040b1608010f0603091a0c07060b06040e04080a0c0507 77
    0x442e1486040c03003000113002d9a07108036110035180c0310074a0b920759140d0342d649008912959441d644a82400c440340c034003e2603244041c02d68078805a43e05c3e03500d503001c9402400c3c1107411070345552a0491300f4803d24502e000b41811100c00810140c14080c080c4100a045541d440c0c0000c144498400b412450f5901002c40f40002c1d4040d85510b00d81e2031850600144190003442e03075142c84e400c46201400703440e00118500350815032074116a209a40c0f03100d22035009100d000d60196004030003500b0090702e0751780402e005030003484644800c001900701443c0c0c01c2c0b050105440d800d9000c4d840000a01295208075110004540070b00304000e00140d58901250448030181c82c00e40314004030000304230568201c040c50100382c21051070010501e40c50a075611112000d0340c0030f120b04040d2262100303000e201808540b500003480024040d0110700f0405c003c2912a0720500d001c80b811410040c0c075030502c0c80c004094400b160703008070302441e01d81c1d5160b4070300410b80e10030b9041100340301d469000c540100c0c2d0100041c0d4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 967273687 1250 967272437 967272461
    0xa110a200315090a020f0d0206040e09030f0d0c180f05011b0803012c0405211b07090b040209060d090c080a05060601030b0306090c10030e010203130b070923010c06 72
    0x4541958014844020595039160f4007c03214242801c0058880d20112021a940c18035040d82c26218a415141948a031801d403005403c00459408505001079206075680240e94840090340600740043c00704030900c0380300b03a52005c05185800c0210394001c1c4041c0c1207280c0050804441407080ea9a9011f50303410a8104811200c0003480da603000300c0080c0440c0305908250304000055140990b11160b50340f042440d040341c038010704200b280d00c1c500c403001a00d001c0030869450780c500a449152803940d441d45449010030240c106806801c46040030f04c221030082d00083c01c0949000c0302095110050b1130341c007c084070301407903203400000c14901c04e00c4140e070814441c3c0080c2c919030070400c000406441071805803502ca0741003081844903500c000a03841c0b010150603614900c0e411a01c810980080103400325540c91540008100030704401c0c3c040503000c807180704440d0044c65880ba6102219449200d00400c801d518401e00030b50052031801c0c1c0000e5810405142c54920b44045540d40c40940d8440c003410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 967274937 1250 967273687 967273693
    0x140a0b30010f1e0302060a051215091b160302071a0403030e220e0f1902151303110402040f030b060a09021602060309150c0a110a20031509 61
    0x1072150790545405500100541c0f00f0281101001078100700000002d444001e1140d000025112100c5010700190391400c00124040b000b41c0c505101c0303584141c00380403807240c4076070a8100040e00c85078041006803030101c82200501e0401c154000010500c24500c07a00740c043d441031400000d0714880e2800504038050029106a40307803440c601e030140214026500c510b200d00341e01d42008c4007620414002e00d001020010010603078030f01085102d4102030784030403650658020403002241d004540840c60b40e50a1080c3c5490344409400d43c01d5008a000320000e500c01c002900d071003000825a50000f04d4a40400144011303e0075684091107070030828540d0040380c0100b84a0208151071400554020041400c0d810641ca0000510700003c1444200300000b0312806000c40850010f040402100b0007000000a91180f5810a41c10440a0350003401c2040006000700004003004080030420740c00290f40034140d20200c28858580120303083d0280c904c69014030801d4149a004490715a4003402180400e0207 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 967276187 1250 967274937 967274939
    0x11180907090b030304033807200a1a04210306140108150d0501110f0c0d0306150503150907110706081b0a02070915050109140a0b3001 59
    0x12200641e6100490903201c0d030010302040001c00c1c1480e00a47c91003100d0740c8000600d40c40590421290829030620103440c1c1400710800c1300040d00b15418030841c105004502c542030140300c01441e698404240c004100440d49070902c505607108075456900701388a4141c0280c00c007420b0088000113100318002000003030f11041d0400c050501d803100e40150035020b103001909450244142c01050920b41d51484c0920841c1200d01d0601c4000c3d4800c80c078000b46c2c0e00c2006c0c0d03100d81e403240000789904a00404040380c00340d0046540124024407a080407100440034244002802140070b6a0603000204044541381d03c424107480e4a5849014052007448551208007180899901d024605447d5411101c00d00c60801c0a000700003251400048907901003c1c1d03010ba4410410310103d007804d90f10340c443d200c0316007040c0450801501c8074a102050750001e0365449a890b90312400a4420034600303c45503000400300c0000d018185910005040001c54034104020712401d1118490000a1420400c28002c00c0d20b00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 967277437 1250 967276187 967276199
    0xa03141207030e0f190e0901060906090911060a0e010c020f090405060f0c0408030319060e0403050705060a090b060d02040b06040603150f08030a110a1719021911180907 74
    0x8038144c03441c60b00340c585007a10945040613020f0301060740255504c015a810008010000941218024082e01c0d2018000603030340381c4900c4007034541c0e044110380002e00f0084508080c1021800c6d10b8020b000b80e0f4945a136481008010744100c0030a0340c069800c406510060056034039460311a6014500c240000c0c40c1501c1c180c8020000c0710800b03814035544500811003044004400003c1c0d80d002180c0c5e040140c03e40b61102c1c50343c401005a0b030301c80444214000300700820b043e00200079111846c010010b4a00c166141e1580d40122014040014002490100880c0a0381031501d25075001c14805031002482c4462900040d0654201d68009000291582e40c1c0300c00041640c100d840051807001462240d841c10007400586034080c0315502c40070028503080d0b5481c00c410402c40b06410b143c0150061300fa0b100c4805440f01c4a912616902c00c0f44075007410603140061002680b06d000720030340203d03c080001fa45d61500d00c280300900c600d81c1d00503080a00040c020b803281c440180200c2244008000340381c5800 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 967278687 1250 967277437 967277449
    0x2130312080703023a050c07060605030a020a06030f1e02070c0e060d0305130b0a0512160509041a030609010c0f0f0f08092b0306090603020a03141207030e 68
    0x9101000b0540103101c05d0858480110740a285070300003414010905040c403d8608007055440c840c003000c0d03824441440600d0000c00300424580303002c4c10003407207811f4030f50050540c0d403d2070a60003500440321a00800400b8840d5000c3e460294a103940410410400c82214010030002001007041c10344c00106101000303c55100d0100900440d10f0111307003894220006003170749841240180a1003400280144c410240b640b80e0300280c900011003613211145140c0003440c5030420750081c049114803d0100b0f902d035605a01e0404129181d603074651903e401c0e40140400350108401c085090810342590303100a680c280041d03031080000d580001061600410000d000070200d007121130a010308203803614a031580c00f4101e0030f058082030038080303601c1c0c035902036461800384401560a59015816544038140300051103a0280c030419507028000151103800240071509544002035004400315000c03c000348071060790b030030078003172190a44102003203042002055078040303c01140052040e21152f0103900e007031 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 967279937 1250 967278687 967278691
    0x210e2b030e0730050105010e180c21070308040e040c05150a0e0f030a0b0103060f0204140f03011d150a02090303030417041d2502060a0c030213031208 66
    0x900200000d0b407520382109100a001030520080b204180c510f026180001580c03607964a03030060003082550382d40c440115488900303807a041c040090a007156100250001849082c8450003800710503d5600008581101d50301d4405802c003034004c1020010129a51402030700003401e0070341c001c05140ca0245010120090260002c0e071007800c00d40017107070208030040182c03255401281420300310080c0c0d2000003101c21260b030000c81d03032620510098004018020807820304a0b88504024091142080942c5059018500400720038180400b0811182d15000c0c02d141010710740078000207100c60301c480c50741820070300781110459035610010f011488400308241a5900c40308044007142001044030000361a48000b0303101603c03c0034103106010740205081d040360010142041482c21040541510038640c00d03080381d45100701d4816108a13541c80041d201d0580d01800c075603002e007070709a591880600003010013030440d070100740e800d0200e442000c040881e01d43c083d500034802c100900c004054000c2c81c00d400 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 967281187 1250 967279937 967279961
    0x7120615050d20250c03060b1815010c1b1e060309150509120c01060801060f030308041e0c1d2a090409060606030501080d210e2b03 58
    0x500031070400e1042454240c580704000d40c020380d1030340c3e40d10301d500031100110301034040e060701c20b03801d400010801f05a022000310748007070310005829001e800810b00310b01c80440e058500101180341e40c104940c820060b0134544c0e48501e807241003111000307240300400c1009410000302031070700180c0d01c0c49455100c80050003c101500c3d06000840807981d8011058182c100480d81c1c194440780030032600c0f1400e0004d4078071503442d1101d072516410300001c0c2d00d000c1c0065100d0200306510f0300c800850151f200d484404107894268890501079102d9a80e0503106288803045052190b98403402e54000400d40c03480c01c00140718220b0080b1301540300000a03600070b0406044444900d2a507240341d0156141c0144c507040244907000780c191030316014030110f0080e1041d240024182d030700c1d00201180c010341680c040c5058a541c0c0781100e40300300305040d095031030024640c000115120310303816003014090140c00143c0383c40016001d0f00c40703005010440d401c400807900d40101108070042c43c1080304940c144521061032003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 967282437 1250 967281187 967281221
    0x5060a05100b090315100f0b0c0c0127060305010303140304050703141e28211b03020c01020c06070b01090504031b0c0509060d020907120615050d 64
    0x408426088207101c00340308241414402240c5a00c3c0c070798007401002522003111482c41800e1928040c0d4400000d858010301400d08003404000c644410203c00f642d07040060b24004200002c010030056501041ea98090701d0500200d019804020351040e18200040c4016113012a40b5415460042c0040842e8440384075401414000c010114200199010450360405030509400c44502c0566041030744001c0d0000305945150b01e022000080001c0d03510050710900864131245210204640d001c2c000000f014000103031995042ca40d10304810b09000d088605400c00c00328141d80114a61084403003d0300c290003507040f007454801a035805028070442c1c41011138401b46030640302c0d62607806680060240240c1290ba4038005800c05019489161548a19018580e4a43c40501c0d00751503120700c03401010300805030440401c0c41c600b4409400c80c5115401040b10000c1d07600e0000803130b0b036070740005403130120f80380c503840009010409600c84050802d11031340c500d59540407182114044d500030808604980f8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 967283687 1250 967282437 967282441
    0xf0b0604240c0302060a0915090f0c0e07051b0c13090201140408120d11040b03010f050f0607390e060603010f061d0910050f181b0c0a03090305060a05 66
    0x1a1340800d20703d40c0040305010004038000310341072403802200e82a1240d4070f514a0135a909003030100100403d01c20340c1c441c04110405a0b1141c1c07028145880a40d0705a010a0080c040d48881c040c4c1000140c24540d621021128481e0052000076100440d000c1e0340c86040d50340395800d00665a001009103e103400c5000e610789071510f0311005c0303980c50700104015000900041907500e0031000a400544404c00030040f400d440d1500c80302882c41c2c541c020b1107010b1146a10b10400901030626211842d039032400148403505045017038541c0c209400c400b80d00c1800c107a05481070b1540c0c0001e42e041da80700d4000710100f28400903060031100c58100c0d80151005d40300303070010300041044980706c1003210150303003040c03401d003851304105540c2550311203080c918560b00480352810007054104640b00039044a40c200d510300100350f4a035080c41192403c00c10102c107449000c100013071080115000c1e886041123002d034118944904044014282000300d101100044d84100b010018010b041003601c1c0c20041c1d0381d07030400c024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 967284937 1250 967283687 967283693
    0x605030a0c0e0f0111210406080a1509050c0d1d0f0f06150a03060618060506120f0c0c0609030d14010f03030f211e0c0509040f0b0604240c 61
    0x203d00c0320322419041040300542507400300d030300744400034000d0021071660030860321550300317450140c01c00c1c0030360700014000d1030002da848001c5007e00210301c3c0340080c1c29266181409450005010024080100c80004001440310280a80310320034001c0150070f04003c000080246442c14020045203501e62039000d2030307103552842008900c69400400f01403154030301034071045c08648000e002c0d900103094545060380c0001d20300f0301d14070941419040e40804004164541c02000114081c064880b855600000001441c4c5490440101d800c503a0307400c0c025052180c5030f100d107840d1150450389501c0c160404144d101e410741181c000c0950203006004400314941c14008540c40c3c11080313102c003904000e4108551a44070340600f40351410082e101c40001c1a208100d1860000b60a509101d01030401e00c010b00d60130b106031148a200c00304182d44e540c00340761040c03003410800a055042c03451240e440da11011003000c4d075030b418010001071420302000b508034010064030400000d02c03c1900001c0c0030401e5a04400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 967286187 1250 967284937 967284949
    0x10090e10060306050f011e27060f0c05100c05160f0b011413051e090d080115120504080d14010e0906010312031505031906051803070314070c0605030a0c0e 68
    0x403802c08128002c0f550602c208541c104015404095914801c8d11158881e43c082c1034610255002e5484d100403c2c0c402c8a400c80313854400c0c1d40d02070141d410840400619103070355045004106a1450b0071820700d609100740740420020144220303a54840075103a5020000504082401401104111490386050001051101151000d070042729542c0c0d01c00114000040c0758031000b08504040d410030300e45000005107603545540e040744070101c2d101030000074001f401030308001c0070443d41e5580d601c80002d080110340f01521003e0000c0351010f0051040000b088507900c600145249402a0b640c147e500d80344080e00344440140a01c01d20750400c80051010601502d2140380018451800291001d90008220080a0b9a4100d194035001d001c1e01d100f4507030f840c260300c6201903004940410031030301c0d6452074030302d6040351104580181d041800f180011034010b0000c4800604082c140c41c1c5404400e558001c4040916001340f00400d80c080705004000025100d50f0382d00170640d0070301c00b064881100005d04 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 967287437 1250 967286187 967286207
    0x71b050d0329360a060315050c1911011103061002011a0913060624020f19020307180507031116110f041a0117010b0910090e10060306050f01 62
    0x12020030312298001a05420411075a83c10346038252948003801d008003244041d140c40e20003a1244525524000124022441802d001d80000d4807101c1c54902c120050780030001d103480130324091001442e50000d405100f8064048001c0204510381c0da03070302d041d60400181e9501c03158010b0440e031505400654001d030311800344011319812180c102090fa100714420103103a1038144020a40c0d07040007000601084841504d180140c80e00490080c2e1078001c00c402c0744e0700c200c43e4940010982c002600d1f0011080c1c0a40d8510000e4000703000c0d6816291100920278020001200c0352050650703940421a071107516128140d614100300b0980c503d00030055041d80510410040090080c0c1c42c40c0103544e90341c1e500c0140c000610380001d0030902603980c0d0840703109210000c410b03400d400b080c482c02172140e0320941c85003154180c1d44682001410400407c0c184204c0d02ca00071905028004080e80c08102100c003030300724a10680045240d0910f81d4209800142900c9142e48402c0c0680070070843c2400d1a030300228042 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 967288687 1250 967287437 967287469
    0x151e03050312060910032d060c030903030c1103030408090d0219050a1505032e09021b010605011d0120100c050301050609040213120804082103071b050d0329 69
    0x83e5907c40b11103000e1005203c01d5900808540c60401400d1140741c154000d0702d500c0b4003945042001207804a0103071200252518804001e4204000080000d032051300074040d40300c0c019000c41264400e036404917880302101100500d0420140e401040189400f000b107502400070030403141c103055811038010b81326001c090704100b01a51300b01036900e1f1806c0e0b2801c0c0300d1400f01201c08aa824030380d8459040c4000c0d8480d9035030090110941002007800c7c841401254212841030b96035032034440c0b4241d00c10f01020301e288100b904000d5424079078814164602c00d10a40a210b20025000da0b10102440c0d10403180d40040c08000c0c88010700040120307540e5003042d100101800e0300c016a07a829000d50014000e16241c000740c41d0340d200c20101c0030502c00c10a000d007055031882002c8441c0d1840c2a0449007024409405287e07110004000088095104200c28050704031120920103414045036030b021b0410307444983c8040001d5991440e414002c038052400c90030550001e100b0300300c82400c90007160700800c00e00d5401d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 967289937 1250 967288687 967288733
    0x2d0115030b1008090c091503070902120708151815030c010e130608030d020309150103050a082a0309010f110c040e0f030703090e01050301151e0305031206091003 71
    0x44c003100018881910b03003520052840500d450500101c0c4500c4099003030311030280c4648040450780048034800c442800500300b4003850301c1d0b40d80385011140701d01c0090207810034461003050001c950315111100d03420803001a4040c102031400381100038400c80382e000e44c0c1c0d00c6548810a4919541d1f001071045020900c10340390100c86801560b00200640382d6035000442601c400118401d0a4016902940c01030003903405a50b9104502480100420f00c00e00000e0180d4008481d00c00002e043c240041031040c030f0f032221007400101103d001d03051140400c0d02c00511030b00002440b4540d0769001d85541380303100081c1031100c40f050450301d02981d0380c0da80403801c0740110390b03620701c410f00054100801843c00c1c5040d02100e56446c02441d00400d404082c0c482e066045006500101e581e241c180202c00600c1c2a464050780d105280802d02203007441c28050813010541801004800318000703100400101001c1521507803a8288003040c04580c10000f0080d450111075200c0600005140042da03200c1d40e5110307048 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 967291187 1250 967289937 967289941
    0x318080c1603050f0c0a140f1f21060807150e09190f0203160f0e041104050901090516050901020123041a06030a0201082d0115030b1008 60
    0x45880d10729a240710000a07441541e0010400c200010403c911402031026110320180031000d028618110380a80841a038070112160014203080c181c4c084022401045403080c001d80440c0100e041d040e05030300e140050b4103020308a1045d05220b2580d00304908081007040440d24001d041da485040074050420a1800081c90b55083c501c1141e00e0194800c0003403001e40c1a042507003800b05612044480030450604007401c4030b026081d5071080c0d80c070030790160014460700403e44070300300c9200d011800c889007400f002403c00c03606900e60b0700c10301d00750100540c81d0b50b540d01d04190030080c034604140d03c4070103602d0611080000c00c041081e03d1082515150510380d44072603880d80180e0141428a106e581e046a00010500300780000800d02d502540c058150725a504503029460048180103c41c4190541d001d42c1c2c408005522511043c0c0d8071060381d480501042d003030110300744a803400b500b0a041841240500510450380c4410f0950385030010381c01c2c1001100300d08008180b13407821010702e02c0e00340b005c1c00300 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 967292437 1250 967291187 967291207
    0xc0204150f06080414070e010b0c07080607050919030206041701020f03040f02090601030e062d0408041d042607050d080a20030a1d010921031808 64
    0x41014000009000e0507264603442d005000c541c08035000d03a20b501410b43e81c038076008004200b030403d0b50b6881e01c440800340e082020402c2103610550640c4850b114004c40014880c1301440300074025140b5550b4595101a940200118000c3e0142410750043e050300080006a85601c100c41c116100b43c0b120a02401c4000313401402409586160003040b40c0c000200020021001c0042d409548221383d4009641c41d0300c0c2c01102250841900065183c0c403000c00300c0d0087c001d0441c2d01c100c0d03d0034504446e001421a000707403910b03114155004c85040300040b03401d1004c80841d41c1154408035500c040310b101458551180c03460555001c6d0b40d10310b0000c4000484984052000480e40480d0300702f011075400c90700304100200301c0101260f02803401d17490310382c0030101c4d440201318414031342c10726462041c115150002c40d1001040e0300034a203141c1c0a200c030b80c480c41605003806001c00150007051060300c07613043d00040e021559962031005082501e070504005000b5510b01c000d0800b290031081d540d4607412642 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 967293687 1250 967292437 967292471
    0xb0306011412271b060c010b0411070b280207080408030a0c0203060c0909040b091c0c060c0e06190e0a080105090c060909010e0726180d0c0204 63
    0xa1044501241940030804501900d00c1d0004038044062401c50f00c80d44801140ba80f2182d00400b10002501c19402c2d2429a150180152480001c0d807000082e0703d92010002a0803540d0300d1a07800f0801201040a0301031103408410950310036802404040c00c406455401e0b40b0105416209885e0650b020500005110200003a10090f100d40b8040360f540385244070020f00005071049080b0302c01d210703850016958400c20303007d44910100c0a00140c10350b80b1150713111101d40d940203062900902c205801002e032a904015072a0480c200c0c0c0e210a03455000e035003000e009882c01100008144000c0c0e111544994880804032346016840c0310000c000c00c2713036020044a04052070b400041c2d20805981d00030501d85d40c1948580e00a8010004a60240b941e0000740440d80c040c503800141c1c402046c8004101c00c400e440d10241d8010136629010f40c01c1510114490405c803564202a0758054120082140340d070340030410b8500807180f03040104201200c0d400c004000c50358030f1030024000c0740c6510804589440d82 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 967294937 1250 967293687 967293697
    0xa1e050403060c18080c01020c010c05120403290415091505101404060326040801020310080f0f1c110304080102030f150321220812040b03060114 64
    0x90048110741c0760014800030007130100041018009000040e01c1e2000030b0000746100c81078001c1d1150000200065481030940b40080c0d4450050300c02c540300100d1030200400146200340b07100d030700f0620314a09200d00364003a070194440181c032403400d000205005000c80f0700c2000d200003010070400f88500e00401d00d860908140320502d404c000a201c9101c0034200c40e075040d0344106001443d100300703500030401038440d01c0c80060401d000840f4103900307186c844c1040707050340a0103482c50752425070350f40c80c081e007243d204480640000d0480c80e400e1000381001e1103544c12242d050b00050045004d1a81d0300c07921011200f120340040704880b50081180f50040440958641d11582a030f40c80e1941da00d4164040d5204891141004000360300041e4110054a420801420050f005100c00380c04c504441001c01410b0032404652002801031520310203140d079401c140d600d00501c11020403494495801d180811503108500c0005090000303214503075000c1c0c00c4d254405000d1070803410300010804585440c1c030035 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 967296187 1250 967294937 967294943
    0x60f020a0503101502280b010e18160915080a0c0512010911060c0c0d0501090302010507140405060702220c110d05030f0612030c07140a080316031206080601030b0c0a1e050403 77
    0x194030001031903400044000b44a0640c01444246802b220002076484080001c8021100b001c1044117104805503a0f011181170518042502840b03525251290b10780404800300b01c1d40b6400c211301c01c1c02682804036608012556101c000d020900190781c03030000340103909101c0746c06584049100f1101d504100885042c420010300b0140a012035424014040c00c80e4510175030166003000b000c0390820f1b128948100942c810800181d0a03e03042c175007008425848240c060307901013030400358581c0c00310313002590340408107d410380054070300c4e102c4901074202c3d52420b0030100c0a0708042d40c40b1004036000700407654840c8610103024010354a81c00042c000038005818002580700c003003068400b5003000942c003003e80c2c1c2022414869465060304001740100715010301d422030340091102c0030800300e801d84220b0f08140310b03003005000c1c40e10014000080700e03055480410141d02540c01002030256021135190807040c100c0055142c1951000c0244c81070720303040c020121400301240c1100031540302c0c100799800795174 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 967297437 1250 967296187 967296203
    0x9160c02060d0e03210403020618030f0c0a0302011113030b13080a020d0806150d1508191703060d0323130e060a061b060f020a050310150228 62
    0x18501074000d91340e0304180445040c2e0040001e05410484006011900c1141c0c0341d070040445654070740c0301e01180c07420f641601465210500041ca00440b400d0003401307241c107005000380b6200c64142002400d4401014504140d000200141e50b14183d0348524442941e400002c1d080c040d4850251108540c0150070014002d0341000c5100980541d001c24005040c15140c0d035081c00a441e9402000101034000c28000403250b02040032401100b1550010040c1c11000c407001860035950340c413114101034800b100c82140154480c018410003603032149000705052090320040c1103161034004514074800704c1202030240113038800006024050b10a04c03c4040c164070458a88403039243e43c82c20320012a9000b0b0b4603c1890380c400184160034911005412110b0950b41e601030303604880710060500c0a0140280d981503120800e907000f4100c3c0303000901540f0442d40d107055481c507000e0140c20a003407894101142e00d0110780c010361409a800a81c0a84640340307421041003400761310000c41240c07452902e000b46001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 967298687 1250 967297437 967297451
    0x3030705060f04120e1f11060106050c0708061b0c07090e06040303050702030702030a020f0f060f0409061d011e050316090e0d140304020d05070b0a090509160c02060d 73
    0x21091152a40918402e40c8102c690786511030055907004840300700d032038004801d1081d1500a00d020080200c6c4503001d400c002d0b002203496402c00f414041c00360018000b0501c00201844446002c01034030008000310750240001d8141220075244140080b0b0510303040140110b1040003400d0b090114074000c1840b4001040105540070019031905401c55041d001b00c1c0c82c186c002a400ba00203c12103c0700355006001c6c000d1000d40360308001c0c03100c2c0110075950704800b010b200720509071102c40003400c2503001c18203d151038610703206401050b21385c145c029018021900201e1800c00d1b40c0303450298150b40002ca00702c8134420121946a003d00c1c81a48803d505118944d0300081e000c030710304c2e500300c00c0da04001e0040c81030700a02004243d41c1d041c1030740610001030000514104121118000e55040f6100a20701000b43e031241e2145e5182c54215001500354800024011514507004400d21004000565440000f85020660b42400c104e8209820040c086081407607800c66648400704c034030499480d2820007540c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 967299937 1250 967298687 967298701
    0x51e190f0209100e1005040b010507030806130f0f0f0e0d0c080306010c02041109030c041803030218041b081605030601050c2a041107081b0313060f18180207020303070506 75
    0x100d41c0c01e02c00c56001d10b02d0110023603ea944600c0c12a1205500f54880d42030340d44405007404270725160b80c8040010030342d80b00200b4240075a580100600480c0c0e400c008628400c00e1080d200031078040d07002c1c0b10603079440b4000002d40305420800080b060ba811032002626607849a0050301e2003021110001c6d84245000e03400e400c024400030180c0701e000026011600155250003d110442c0c040308940341c155208001d0400000303101e50002d0120303406590210300502c4040780403c3c01c0d9100841c03503c000c108042c14890b2207691103184a54070501018501104042e032030340c00b6045120240ca0381d4104900000d4071440c48108101c1003090f1040c6d143c0d1800140c0700c005031011405010185d051059040c00c01c07900c0c0d0750701c0e070f101030701c001e01d030007591302072402800000c50303c140fa080054000c2e01d0b0105200c8201d444452444e10b0006161030744410340d403240072410060406040501c1d051441e01050300600044000900100c402d0b014420016030341c0d0301900000c0d00e5400341c030000801c94071480c810001c107 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 967301187 1250 967299937 967299961
    0x1120332070804030b0a060b040909020301090b010e190516030c1704110103060803190c0c180b0f03010c02120306040222081504050303070e0d051e190f0209100e 71
    0x12240280e030312070a1034030b40d03401b05000d40c4d9403072050900318001803206101c60740e556841040d41910050001a01240c0f680d254003000000b6440300e04079500700410850700002000109044034440ca108100c549021024100d03180ca50340203180030903940d281c85945040c0580c03201400c20b050000d92002a04d803038076080200305000604280024241000010034000000541e481c2c200c0700002000039085005085580d0840c95400b40e8401c08080b00003e1000d4071204409000d800d8000c000c1920300240003072090480a001640703010340c0c5000110109264041148034902845210301a625110540040c010b070180d00041c0441c504c100e030b000140120b02c2c00408013200c10039020343d4810302c42c03050448140d0301b048901601542080000610380f91054241581000e8000c1070301d2072100494482500d03045114501001c460440e22101340840340c00c00071000344c0003103103100c03c503506c1540d61020079021032014002c0c040d440403401314103100c000e21505e502602c00d1400070240da2901d00105d0703034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 967302437 1250 967301187 967301189
    0x31a13061401050a0503070501021e19030503060a060503040b0a0504080f28020706021e1501230a05031f0204080a0f060c0212030c0a0c0203070f0e01120332070804 72
    0x12050000300313000242400c01040c07400440700143c002d048054900c0c1071265595104402c181010300a070b008804030560800700d05c401150103580c450b03031a460f20400340101400c1c41c0e003020041c00300a00030000092a14140c0d240d214a0480e000704290310740e89040310007030003480420226100046040a4a04940c03074100c49000490041c41d64018910740d416a242c407501d0051038010380040000d1030a03000c107841c04940c2d00d50000c08981800c5d80e011313060316480c142a0881c0460098005074808501d414800030030200e8803c0700d482c803a080ca4400000e65642d1100031300b114200460303140014070041c0b54103450080c044601902c034070411900c0c212104010784041128118a82071001090f01e02c00211049210340d03c18a5501e1512107904801c3c0c960400084801044042146040142c03024064440281545800e001e1070700d0400400c0355150105801119203a400a010503001c2503000c8280e190444045088254400d075450645100210140680640141c00100c0500700500800284 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 967303687 1250 967302437 967302439
    0x60203010b1206100e151e040501031b0207060c02010c1709130603170706020c0f06010f05180406020903070312080a1419020f1312020108060a031a1306140105 70
    0x20784590b0700d03041005001d100e60702c14800060440170004c0f040f03052a82640a242c0342c129801401d1192009004076000003650030360203d40c1c1e02240400044d40c150003600000c0036600240740d81c201411800079502d04013480b940c402c11030180070348019a4080c28125000d650840e519411300354100c1d02c000c0903035001c1031003a030003040345e14624101511184554016a54030410564840500101140300c84c1c00200c2c050350f002c1c4d0b080110441482c420040d0240300044c00c4041d0031345624004003104034030220b0740414060700601400c084108201020f0302d034480e5004038010b1302c0d18207a00201e49003420303540005001003102b50341d21308050b40064645205241e050010300001d841c503075004134100c0301607411103002112500140f041c1f0200760064022a40348019503814145504411440ea41040c1d0080403031503070b5036032032200395641f00d0011680064140c80b9801003900d1a07441c403140c4030a104511040d80380d40070100f851413010f40b079048421500300b082802016071003148645015001e03c516 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 967304937 1250 967303687 967303717
    0x170a1a040e0a1a091504033501091401170304180501321210110702030f010537020406030209090105011e0503090a080408060f09120d020c0703060203010b 68
    0x81e09072000320f040341441408400b01800b0342200846041d4072080c0d0151040342480322090486418604070503107580038480741c8801a4400d1660f443d500070034481070304001280f5050001751080894100360b424111045c1c041801c084100400406040d401190400c0f000b400070001d2a00c480c1d005500121b050361440d000b004500543c1c200606005960602c0303a20b23980ca01103003004014a030006841c20074401380011358941c00758090b161811101400300500508102181c002c0940c04d0030402c888080c0101d5008002c10705140001c550501100c56813012450659070001040c1c0f800b001443d204054001000d5441355160140540a0740055403418003070918031000050300d41c802c401003180a007408100b041001800f440403549607000500505840c854600268000f800e1180108010b19200d0060303c01e5051290380d00c0d100043c060500750942c2e200c1b2009080c0000d80e0001c4652760403904200503500d41c507403005039040c2016a40064001c9102000020341e58124500800d00c1e4105003a02c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 967306187 1250 967304937 967304963
    0x3090601060f0215061c140d120501120f0c030c330e01110106031401020306091f05090a1401091b031a04021b01020c031801170a1a040e0a 61
    0xb04a035a020f14201214610004501242207420078400e401444103020b1102ca160002c01c0d19143d055914200c0c094500d540b00035100d2001d15400260f5850466011909018035490195030b582d10005007400505240740505440e820005000d030b00800450340300622007481035031407000655200c1c3c60f6480c007080040c20380d0882003130420340200a21420207a1102c0d01c104045d903004458a40713041100c00403640d43c1d000f0100105244900078000e4928240c0050380e2071501d00c041c8588030001034940c0c0e40442c0c4c0b080040c440081d0107a1203000b520406d03a0a10015518800729402500c69000c0c0712000d60301e070320000b00e41600340741c1040f0f025244d018083c002002902604504445420070703030280728005a009901d06141540007061048084a80eaa00d0703502c1c40d01c1c00600720380c00240d9026141d030000034100d03500c82d04a50980000d1100742840841000e00c5228000d0615000303002d2082e00743d80b100d140f403081c403241001144d03c04c5c01400400a14100a00d0a955800824829112a03845840c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 967307437 1250 967306187 967306217
    0x1050414030a0f030507091d04060617030a080717090709060803090a05130209031b03100911010e1906091703070804090b06070b0a0c11030306030d0e13020309060106 73
    0x100300e48007161a40e44800f08070944110441c020301010708084104201e449001590041c40640070b145441b42c059441d0040c20b00e483e000040301d415070b01001d46a80c40c0d400c0320609800c00300940b40c6d03843d024140221320b07985151048800000b0002c4d8001d04d01000005e11000d0030001541600392413403004200401c030380700c06000395039004504080350f101803a00410b2000d41018010900342d407816280150510107444000390601c00c0180650300210400c2404d04210308d0200090785501040704010440501c80742c50f10001d02160310342d594180030241480020a4440402c035145001034a03201c5c00741240c4601c2c0007003404070300744107038100c0200440c090816101c000c0f040300d4030180e1215040b07140615090201020349420f0041c0c1d64048070522000010554540769948162814000000d19408202000e03080010b0442501943e034814020850355440000e401010b10b40d0504001140e070403a04009101a26124a0817288a0021040c08a41c0d9070014040f4141e5649498500800d84208 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 967308687 1250 967307437 967307443
    0x2091309060b0301021e071419030909060e0402010e0d020901150909050709051207050405131203060b1e04120f0212030f12060418150b01141819060201050414 70
    0x40300400c01c12149448201606e01c0031008024551140a02ca081000030200304d5003000c50301d10b44e140500440d250342c10700b0540e010500d10050108014200221410094540d000e66801080241485a0808000190b6941201034824231b54002d11008c6550b86682d4031400e200406902d00c03002c80d0822034081440091802910b10403103030b039900c0d819641e107084200002a108112032201034010404007041d2500d5900400703200b20744401c50300c804105036140411105200d949590101860104103202d104a00004c8130b9550340305080d400404c00300032090890512560344840e034a51030910007481003000c58090111014000c581c40211540b20030000c45d200d2003a46500ca200b090200801504401c0d00d8440507000030026000140800d00c100b8001541d0054032010303620b0000e1082010b0420f03070503000d4010034000a18002c02b104a452041c2d485c1d0b0b00489101000d524140c00303109a1030b071039078003007840c1c0c102d0b5045454503159a2888064003c01064400340c4006110609100001c0000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 967309937 1250 967308687 967308697
    0x403141b06044215091103010f150807030c02070e04060b1017060402130503062815050d02030a1704060f030203040803070806131112070e010c060f02091309060b030102 74
    0x42d03100c04070520303c00c41c0c602c4001c0c902039080d50340001c1e60a001041d0300f8428454048869008000aa981d5041050b40390b0055190341c032505009100c3d58044c0b5007142c5c003504042d0090300c10300303002c40c1c0d400c00712005034140039040d0003004662490f40304006c14000306130404054403801b43d0b0744045800c01c0b04030480d900f0300d0301c500118004084902080c143d007081d0380142a200e03000704503030040380d0b1994000380c200282500d1901a901034641008244070580b00d02152103d12044100b220080d80314010305008554403506100300ca00703030b007880f00b907413024008030402b6a88064200780d8640001c400001d1a0010f024800c0000c8800741032402150180c0301b00c03405250800e50b030340e0644c1e0380c14004903004040100706070780140454000c4440605103004100c0540d01c8003007519280e8043c1c65421a010358001c00306c07030410603600c00000141c0d8118080d0032346560801008070b00e028000d10314002a1045003812a0801c0ca242d200361801c005075480800b03864400c080501031a00b001d402c0500340c2c010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 967311187 1250 967309937 967310033
    0x1e04110c101a0312030c071a090c100c0807140a080a080c0a12050a06150e0114090108010b03071806050409051b0f0c010b03030c070509010e0403141b0604 68
    0x220103140c4c605181010055603011803100390f010f15002c01c6507141034819019003c9010349038041001c0c007201d803509010380d10030000d0903940440d9089120100800c080300d00304020302603d90000e41c4038184404900407013064407400088a140f658140b603c03407d0f680c8009182d82c00111404003240d10600380c0c1c0b00b181d0000c9400e075603500114170000303d034200605001d054296030a0791340900050380180071a110804d910161241844046c1400002d8149081e07036040c3d41c6a56010019000280c1e00020700b03906407402200600e80b02c1d51011000c2c1c0741e240814002040ba4555001c000440c2c40d8010010015101d88a50034080c80d140d07003815580e0601042880000d001d0140040b0710410307810740140100a20143c00440c0105250000ca0b0650380554041200f075084a581446a4108518002e004140703811410000e4a0142c400828a00b61110301e800104000610701003000050b81d441514002c8460070b03a0303107901f45072408100150707568680701035040f820400c0b0280644240354101c11694 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 967312437 1250 967311187 967311193
    0x6100506180105090405070e04060504020f160314030f10050d0f06020f16060501060e0319020d0f060c0305010608150303040302090a0e060406020403050c0f1e04110c101a03 76
    0x10700c0d0459007445411162406042203c02c0c0480070441e60b460180ca402603643d03480c0d04070390100340300600003a90b41c00d4001038022801009240c0c003c41c42941110310140700319042007841a054a41250007040c00740103400c01c020048280450707a230300c0c048014016006410f5640980369900c041c04a440c51064016000142e261681c802140d50340c0c00500782c221314101c2203450070020b2119403008070901c400036034195690710014001c66800106c01100d6078800c90003443e803c80d14441200c400c000c0d80200078022024801c0c41c000f000114017100c0031403684030070103001d01d180b41c0380014002e120074450702c1e001801100c0031032031122590a0740681524098040d5240c02e0954080c8002400060300d0101810342c1c428030031003120800d000e168001d070710984001da500c1d861820302c989400100c510061113281d0180a05403581e403000c1c201c010720300003a550f1000c021803090000b0010b00c568008045200d2001503490010300000c00d440d0106a0401c00420090849000c9280f45500c0891802d8141e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 967313687 1250 967312437 967312447
    0x30a05030a08161e0e120c090f010b0403112d0306010b041802090a030507060f0f140301121515030b0a2705010b1305070809010504050d120608071706100506 69
    0x40740d124450981400d85051400c21740c42440b020401101281c9052040c44e00104060344440c680415a940c00c4030b1500700d042100d50602d1036040b014442c074800113041825041c0c01c842c07581c03119050102c4448807a503c90034000b08984d00303100d070100410b6015120740103144c004648030004200392415100400c2d8203035000d28608107003500030740c8038030391140d805042490000009081000424050036555440c555840454000503103c0c8140411450520603011a0b04001c1c0c0c4144041d281110351602003191080c400d810400904070203103400e02901c81c14860180d4a580800380f480c001c07a0700c60155030701250b485000210860b11128940c0c2d40a030001c5000840b99507040c040842e00302d0049000240c0038055500042c440c42c841609850754a80780d10402c04116048007141c0e40c00b00c4881c0083c00346203480e65890352626900d5900c40d080c803400b500c45405030045940000b001e810010220740410f525024040e104490641074420b0324030130b4500051804615400d003e04461020348014180 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 967314937 1250 967313687 967313717
    0x1180905030306120a050709060806010b04051516020d061a0904050a030c031103032716030204020d020f070501021b190f061b0c0501110f03061509030a05030a0816 72
    0x50102c11444c2214824490b9103008100148501d1005000c103075030010707485c0e282220300c500700701e8142d100c8103080800b40010800c3d0b850f03500304001d90100c0095a20355604144499041c0d4042540b0301a400070100642c6030108261a40280c0e04580440400040d1500803401c204c4420000c8030018856041003818900190041d804222014170a0508801c0b141c0180040c03461038008540400302d800c20f82540040403401552000d402001c41009451a010304070140256841140300c02400b480d4002491002c1c01c01940c1911000c28528000130364816450038058040d4001840d0f1070001000c200c5600000480042d00452070800c9403486250240c0d5034403204690908100151b80c0c4680f03480300107901e1401e680328040c0c40301481c1c44482201e45c0a0a00c14211000d09403100c00c1548204014041c44903130b81c09a943c400c000b100c001103c2030340400300a01038007aa031403050b0507121b4250b04c6000c102010000e050a10381c16130341c4c102250369500c42580d5030079001d01c5d4840401d908924120078 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 967316187 1250 967314937 967314949
    0xd142a1c1e0207030206031f0e060117060a090e06240a0b031e010e1e07140702031905100e06011203050714120706050f010b160c0806040b01180905030306 68
    0x34110380c01550141a601d0700412034035801141c0c81123200000c0d40c202240b1403140030140005e801c00e240c50200514000300082d001e145219000c0c6203001c44030300018441d545000014001c2c0150700024017050031445110b030340d5074a081d1100311a091034544030300c50050603404255141c0100405004d001c51401d94000703030f9640040e1403403400c0d0741710306154800031070030b800010300030084010034403800e251507185101c2140002800c0d03d0f00900d603a06100040d0340c0490aa200030080d804400e596010034030009180900300c01d80c945168962010503810311002060400038501504018030407143c00c1142c042c2ca80b0024020070103500d0b056050382004c0f80c801da0143c140d007031180303030446c0e642d00c0800961458040209c01d10300c5036040000d0b040041008500429401400394500c00e421541044180103050091401e142c0f60302e50121107141c20f00c03585640b4140105040019507000c2c0c142401c00d076800c9202400344840ea42414102206a40c4217882103000d410740090142d400c5444070130411503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 967317437 1250 967316187 967316237
    0x403090b1606090b070e1027080a11011d03030307030b06280f030b0a0b0309120406020a020a1e0b1b0609011a01110d142a1c 55
    0x40c1d110060302081000801621030749207243d004600c0c1e089035103000000140b945618000035030185c081709940f0030303610340c010640c6284003010040003003a61383d1100c07424035030008950006840d445030070544c800707028654862181d460000e0f0707950101164044a00700111011080709a0103610400c0001e818601ca50706c0703410a83e0300144024604043e03980700000e9a10200e0b082c180e10220340c100401d00c00d410002c420f05200da1403c00340141c0303605c04001010500b0505c20040342100001c00a08681000d04ca40b9004040200b01c540c1c0304c41c2c5070035000b0359803110404102e0040080c044081034180080c01600c90456124006010150404005170260f0f0005a1040c078040c20700d2140d220300e41414851030b841016401c0001034056107c620142410346101368007414041c0b4000842600d900105420071170054030b00b01003140150002811030301e48980d844100c000d1144401e20389000491100008000758258211581145040412400d1400500701c00010800d040a1700801c030480000c211 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 967318687 1250 967317437 967317457
    0x7020a0303050a18060c080a06050303070f1a010311090612060a0c020309031902040f09150b061201030b100602030c1902040605190f0b1206090405210c150403090b 72
    0x1320b081e110914090380315068000d01103400340d032541d0084c8100c0368840007081d07000c100e0080504c000352819010039260b00c82c021020f000014006034103028082101c00007100407281900300c0c01d180da56070030522107204070300446520441d070320300c0450601c1c504040d10941144040002d8038441c0ca41d002c0c80002800d20900c0c03181580824842c3d000c25607001d0000815100f040d10780704900141601c10442280c4070701c100c0240c203e1510703185202242e45402890120220700350005140e090401c00030301c07980110015111801e00359030002c410003c00000c0e0502400800e107144050581741c400507a101e004e17032100c0751119880101c1d0540944400d0240703d01d001c3c005880010300701d4554001c2005150394807501703014105422010864a008501307094000c2184000d4a0b04184050204004030a00600014070800e0b41e0000728080c4803061011040c1401c200f100070188011003002500c064100c08182c00306401030f5035800008001440e80d8904c995410744d1050b403040e003484844500368100d440c0f09 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 967319937 1250 967318687 967318691
    0x5040c021002040807081204030305030c0a110307080a020d020703170702130609020415030c02070512010f1416141b1216140109030801230411031005030607020a0303050a 75
    0x800d0007460920003080a80b15440145c01400d060003001450424121144200f100c0100010000f1a5000c016070790403004004105075566011541142c048980900d540b00314000012800f00700b1680c0402400c13419515000d48010b1078198505170303140c0c4114400502109103484c01138900c400d40300000e00760b051000700611504448280c44c00121181e940084814075030001f020700441070084602e12140440f0b00c0c0c02e101c1100704d110000e446000078441c0da40195420011454071600c2908000006040b160040042c02c12415482d1060401501c0303c1c0c0105010300c107841040341c450300c081a034042d24511107920744400342c1d03000040d81511002c0c0d04910700615280a990000c50001426002013044002c20101c40908141c0341083c00200c18044503031400e8000c00c002a00420503c0c111910003401003441c1000f5680c066081d941c2c00c440c20350041c9800fa00c000d0040b51030b006075000e1443d40d2505140c480d260030a0540c0c42c2801d0310401d0141e84124120340002c0d11a81120f94850540080 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 967321187 1250 967319937 967319953
    0x150903070501181106040f180209030a05010609050633040e0f06010810080a0609061b03060e09011812140c1509060709060e0a0e090703120305040c05040c02 69
    0x152821540e0b9050001401c0119040b200f06010444c030186200960850b0140e14091030000c04208014462048410346055040f4045210300158191010600c010b025280741c2e4206140841c0240740070b01440d01c1451404c070200d01c5500340b0035a400034036000c942c030965041c408107146580705480e03100390302e003010030400010540c01d845000c128054120240559100e081043c005080c0000090900c079280940c04010052900e001400c40b4425400c41d4000035801c6a03414007001905c110b0520303143e880c0080000c4908598503521481c1106c07480b00428226440f0841f54900b40d0f182d22843e2100403100c04201800718026001c000c04007100c40c1030100140a08245a281a401010a4034016005911900090600501d03c030f03501c09a01400f0b0f00c2c4034505200003030241502d0780651000c0146041c1e0000c42034030b03070034601c80c00b0306000d81004c44540b6040040a80d00c60840c0001c660811141401d55641406401428040e55000340e044001605010900c002405014900d60443c07040c416 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 967322437 1250 967321187 967321193
    0xa261603200604120506132301240f14030a0803220303090b0a0e060a020a02070e0a1d1f020a020c100807021501030f0b1b0a02031806090315090307 65
    0x184001c2141c14101d0003004d60301e060440c140301340200032204000359000d00b8000aa400015003400e0500818416a44158503072450b00500d400b1242e01901109440840810001030008104444400c918402195290060040c0c4882400c01054040d80074901c000d00281906000e5503100c10b4903044000c20f041c80702405014070346244e40c1900801c0e9114640814080070550701e5030b10008240b41800b8032101c080700d03280d4817640144214012580403400c0101d040c13080c010700d0700a100c1d00441c02c400e4180a500f80006140e04c64001d119110a0f880344001c406020400005c00c8042484404600c2e900400c0600030390b000e02e00c000c04601842c000d0141ca40e45003005844030440c95500c4540a241c0a00701a1404d03a00701c41c01110300b41980010030001c0c01d984582050b00760300c510f5010032034540b0038580700c12041c1480c0804600c1750208404035040d5001002e1300c410031500c4000f0f40451000007e1015030702ca0100659015005510110300e42d0103603115858206241004403490300070b040d1 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 967323687 1250 967322437 967322449
    0x31e1507021519140402010c020105090d060e0d020106061b11010309050303040f020301050601030603020f0f0d080a08090c091e04150e0f0c030102120f0c090a26160320 74
    0x100c0720a03c180b4200402416401c403032290003585502c400e00c1072068206a000603044103900c060003410028000354241664441901c01801d0a90020041c03041080150620391201c401200340c000540ca04000000d005100b41d100c565608601c1c400c2c4062440a5104d0084141078100c1c000e041c1611800d24034005503081000314410b50050b11169040500c1d481050300b901d2004d000f2a0406041100900c09030340c603807100c1072000c8803c542d019000c03285800428803406aa03100501510404201c00e00c2d8590001c585034460081402075074200055032042081c030034030503500c0b100000c079542c004941902c84450740a8009014500145241d450744480c0d400347c54640c22016059007084204034074004c0b08010030303558894220002d40c208112415600d5140e5001025403240c1d040c2640404c549040301800c4584000700901115006c40e00d5600a4610405403a0403001e040c1c0c80c0381c9003075010200030a0480000005040d40d00241b40342d5110910344410748c1d10840c0392025440c00303402180e6940 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 967324937 1250 967323687 967323691
    0x212010b09100203190309170301030506041122020307120e0102040e0609041e0c120305030103140601231504030f05061308091302070c06030605031e15070215 70
    0x300401695016144103020760307040580e0740340055500500c14581511a000c10075500d82d520f0345000111085c150424080c8a40e80020560742403000100210602001181c442e1143e405a403801103007020350303000e010030401c199880c005078242e043c107101c0369070619030001e503008000c3c0d1629400744012400030804860340d070907a10005a43c001070401c04002c80e0403009038040c1c41240c044600e45400d03107801d83c0800c00300401140c0000740341703251020070003a00d500001a08111200c0d0300d40651a1a001e8011307170003800180d61051548000800380070b40001c40074145c2e0380d150814109111507001c03483ea05402003e100b6030014544914144810308140604000d6000f40c080c46000d60140c20510b04084000e00000c00720614000c042010420100445041031800d5880c1c030005003200e5030542c001e0040b03c0d001000c0c04200040003070a50383c542c0006064510440a880b01102004082400b50302e00084407001074101e90041d00c1c2075894041c4007a0720807228019203904800419080d8411042 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 967326187 1250 967324937 967324949
    0x60c0513140a09020c06010b0a050d0c0c200d1506051206150102030c030a1218050a060b03012a090503070f06080c0f1c020c07030f05100c170901021201 67
    0x1074506803041500e0030703140c80c07001041c840c1001c6140c070112005a03a182c44050140b142d11100001e900400307144102c0403680c00080c484001c00c070805808000034025050071070141c0310341d40244600799100c0c1003121a104200320080030801c035065255204844014407401d6024480d654250001d250385485078801c000144442c040e100d03d18007212102440155805000e045510a1201940c2220008112500b88000b410b04400c4c800d104000c1e1300c090301d0641206550070341d84000c13071400c100f03000448200c5644254000e000801040f42414201c030010170010320b8100181202a01c828080d41509030701e00e840e444c1c01020700c2e843c2c134086441e0001d50ba00c056850980703250108a0039600c00c60180d000b5040342c0000346404600650985203019200c0c00c64103807183c04011038803003c5541d04035140d180616054404841c0d903400d00d200c4220302035005903000d004098803480d050405104010300d1403001d44500d25081058035070750b18441e100074140c024542d803c10400c0024a1102c28090003881 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 967327437 1250 967326187 967326209
    0x1020406110717030703080a110708180603070509060c010603080703020f06070c080f18040c170f01050901121e0b0612010504030504060c030e1e01110c0d060c0513 72
    0x180c2610924021680d44a400441c2c10349107108030401004c800c0f540c0042d058908905943c0700c11024600400c842e1620080c10000000c1c10b604101c0300c00c000d0a0042c0038610714004c0100c02200f40442440308881680000b02c04011000c3c0030b1030a0b201512103c030018000003000390302e0b50395440c569031100c0402c0e80913900c0000d8480950504029003035014100e4070709820403030000c1c1d03500c0300c050080c0340d00305507440340215200d40e880d0750701041ca40c02d6400003801845070412040000e849401e4641d520f5501070342072000200b201031002c040d40c0c102c0d0005080044203a10344a400c800c440000381d4120743d201882c5100602c00c402407103a00340c015010f00300c1c508031070409104102c03007107101e00701d5080e41c3d904250402003c40e8100e015141101d0690400800a00041c6400c4038088003040001d9407140020302050258003080b00031844410082e02d0b1540060035a01401d541d90100c004801d5000041c5c09289001490680000080c00035506007141040007a400c4180701e00e000b0780103509141 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 967328687 1250 967327437 967327457
    0x1211060f0405091012060c03150906150e130c14070804090608061608061210020306040b010c08041e030210020604020112020c0a140a08030109061e060f03110c01020406 74
    0x8904907a00940105224900300c04c414941407144440500915000d081746a40e00c01c4180000e0080c2c014281c1118401450607002d80c6940d01e01c40284198020f401c0c201d080c0081c00d92400d030180e40c40c1d6102c00c0c0700601842e070091400e9403090142075508400000c02200762143e02000c2c214401a00f100d034440d40205445a040160002c00c13150194410203640d800407091003040480d030600e10452199520f0807948964810021072003200c07010500305411300c542c400c0c82001d80859800386024280486041c4a450515401140c0640c607209028141c03800410003048185078030492025180c0c02c0c0000c940b070391030b500d4000484036040144600003680002c3c04203c110340e800000348220a041840450404132099280c1e0340e1900d101200402d000c000da11140322030201084030100316980180001e80d41c0d80c6031310700e0102078030091261280000f4244080340380007100070402400c4d1146984e4040d43e400114100310043e2401d80300c4662910800c212a049404d400e0000b030014045c143c4640c5c12003 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 967329937 1250 967328687 967328689
    0x13080a020112050c1207090b1201140d0206180a051c0c240c050a0204090524011409100b1305130c170421120e010c02071211060f0405 59
    0x4910140001d1262a00e04400c04c48031042c0312056908461003171141031241c0e607990030250b0b480400740d080b44c6580c01020849500c090665115139050340c44020a145142c0c0140d000d0110540005400a60000e0244611107444000010350004030700002e010b20001541d03040480c24100621100c84ac91522188504081c40280c0c211600206008080024100080745400f569000c03840803400401001384c4070714051140420040c040b06400500070001110240303400c030745d110382d501280003240d00708020b031089046042a203107040305c04415540054084e000e04100c06824001d110350030310302002c24041145600c4002506981c40c030f10050340b03401410442009100d0140d401e1744104a420f144071440131551106c0303d8080024500304494490b00c1d81e2400901c1c064040741c000d80c0c04c000795002600025800095084e2031450500300304009040c280710b0500ba03d0061908001590000808212801c50702c407054041c5402041951440340241d800604a50f0084140d100c1d884400704080c403507 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 967331187 1250 967329937 967329947
    0x19111c03033e12090609061518040305221e0302150702010c1514090d080c030601090305060f0604060e01121104020c01021b0d140415030213080a0201 66
    0x107880450480086040d501c000c0c1d0154641d0158440412103000280701c2510b2607618151a0f58030400c14610080303241c10500c0c15655002200e00100743e00c0784402182030003080d6669a124150081c010100d44615143c03401e94004c03000d0001ca040207400c2154203030908016032a00c080600c1c403401083c0d03481c50030f28500050b03c240e541034242c01c2010303041000180c1c0c81e1007804800d03010901c1150f8a031940e6000503654207a0b2102c001d0034480c46903102203141d143d16480500d03180840c03d020111170703c541d4030311030f90b4420081d240303004240c40d60701141d1410f0214002d10344c4408140340003181c440d200c0d510141001c00c03d0391070450164005c000e20160b49091f0040501805a440402e0310941c5841d4540c241d030001248080d14555640003040701644980c0c04540411540100942d80d038595501207000604040c1d100300d80328052094172080040c418081c2d592800000c1189508250624807481c814250003840b034400c3c1542004400c04400248090307a00608003a0041c146000d404c0c000588 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 967332437 1250 967331187 967331201
    0x50601031b05030411010302160c0302090a0e0a0b04150c02010615020d12320a11041203080a0e0f1c180306150f0f0305010b030c0319111c0303 63
    0x1d03021a0401d110a1001d61180c10303658059002140100c80302c907031a00580007841845800e5031100d18494181d810701c030000c59480d00b141d1080d11061000da0b01e2111110464100c955190942d0300425450000b00e103000740030940090058106c19151180c003500c800031106403948000141c4d4440404014034580e041c441928410030380068000c00101910082542c2d07d8618000d401c0baa560042e501c0d80c180401086a1884040aa410b0403089900c00c00d4032074881100c098240c0341c20032140c0096905506c0a40d812187c1c800d003600907500c81554181d40428000380a00f00709a0b40d030f500c000d01e0031010403c0c4544144648090300c03100001040380c0244100545001c018054005010701a80106503898400ca0b908903000040454501914006200d45940500c41d850f00f61440030450b502d00035a003c0490f48140000c0201c04032000c103158031282c00c07400b116070503005081c004124103921020040050b02c154100b4002000110000702012283c00245000f210290101000c040e09031140c2e031 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 967333687 1250 967332437 967332461
    0x15090b0f0729150319051509190803060415030b0606070318030b1609053106060f020f1209010c140a030309020907080405060105010f05040f0803070b010e190b150c0105060103 77
    0x106000c40c5c603101d0a1b40c4201000e5101000c640201c00100341c058103100c06100715131b00e000d129070161543d0405403104e0704180d4805100c1c51504e9000c0c440c203040481d001c42143d511810342e20f45a5200c808003d00c907042954150300340400b50800901111092843e000507600c40c2c501090344d0704019184000d00e80c0c483d0015014003100f64018086951400b501c10341d500d5403202c40c600d80c410f81542c2c40712810070034011807100e81e013049400705a103500403640ca1540c0300154203c4c0d142034211441c1c15560900418a1251907104000c446510f5102e41000601c8500402c41109604a00c809181c0f40041c20002071340041d40d01e10158086180015a4641001a031f2070041c02074106034603000e442e070006104603418080b1b444601c0044500070300a41c2c004200180d90740008541d191487c58503607001d0352085918024000c00411642d0040017040d0281040d0000320303408102c0250068000c010044090740c1c044600054145460800702c020401c55544e4000414130341804000581940e0f00b2003000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 967334937 1250 967333687 967333723
    0x8011103010b030118021902060f0a02131503060e040305030f0f040305161e0302030301050a38120103080c0d0203032404060f15090b0f07291503 64
    0x100040c0c2800803e8070306448400c5081c2d512482c031302a400000348102c04007021950300744130f01000103580100e0a14410b5081c2d0807000314603a502d41c255403c80c071900940c640900c4002c0014084e4a4074440c0405c500750090800140303980e19884c11000c15141160b049000400000812480c00e030704000e0340d604680c0d5984100c4440c203090741c02a169004082c01c000b0301041d0a21414240502440350f080801d000599401c0141d1b407509000391a50b0090144078003409204000041503100c0f909202161203d20034a0707440d4403030005d190100090030b0100005100c600303000d52120036030b0001c40b981c02580300d1915260754100711070502c4d040801007007088065410501c1000fa0f64054442166950390103203417505e2000348804002802030880d9041110448103480010407400c0382082d50440b000d0840c5c50b015078159072100052603601c62000305044859040c000580001c94001c00030401c01d2545071580c041e44080440d1416070070b42200c1c2045100300780e20899800d410103000c50100306e08100f0b18 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 967336187 1250 967334937 967334939
    0x14030409021b070617070503151c14160308030c1c0501060f020105010503191a040308100807050a260109111201020405090f071b030305100b03070804061d0114010801110301 76
    0x2c644c0403143e000b01850240480080007030f04500400101009602000703110381a544104080c450025007401d134215031380ea03c107552f499440640001d055141c0d50242e40c0b105442d900b1661200000d0300b000d0080440362009001082c0809143c10300e004881c200044d000640d513160000080001290700042e50669250000520071034030082036a03100c003245002c500301000f07400d207072401c06001d055410480b4585402c003400101030740901c2c007030301a1504000115445403200c0080392260f2207031081ca41d007c00307403e008210303c0101643d20b0b01c0316261210002ca040e600300d0303880e83c251080b50300200c4a40280c20300e141800e241203941c031b1826096520086050a0030000421845107000d0071003030760b060251001801d1144500d003074a0700c0c8c0e50010055040c00d407041c40d002e005024189c5003050548103811020510741040401ea070321071a016075030050944c46030748a420040030101d074003601c001100448110b000ca02400f45030310641c0d26485414079580b5000740031b400c540615091800d15202040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 967337437 1250 967336187 967336217
    0x24070909140f06010e0d060204031a090709050c07061503030f050a0815040e120301050a05060702030a141204080f010c02010b0d060e030405040e0d020c01020f0a14030409021b0706 79
    0x84070503800300421140c890b41c0d840300c00068070032840b0852050380c81201d4a03880c0301044540d4000d40101d901c903c004454a440c0200c101c1c06038201101c0c0d20700c2940c458002040503240a401898014100388401803401c01c003512400e0076034030300c4078103102144403c1d0f40030401c040e809601c40d0030131050707803070581e0030821130031002003114a002c1c20586101c021090710b9001940d40b944003140450b00c080c00c550360519100d1354811545c000740b0880348200f4441d18000307404e0a14400f110794150b8001d01034001c03401c00d903849002e03c02995850441c540300f0211441e0341314908100400260400000034802c1b02e0300040340500b500d500c0d50045086906100c4ac0400c80e89400c01030906269210b840852440d00c0740fa182c0d403860196a12040e4001c1c104200d42807003007808a500003800c2c04680c20788002407040c500680c2d40d40740c540c601c0320140d441464810b01050032134030050a4a8503c1050340d1420380d50340307070300000e90300540d6210702c0c05000f09112000e4100d0401032500180036a0528283c4800710300 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 967338687 1250 967337437 967337471
    0x161509140c04180b090f072702030606040e09100c030e0f190213150f03030e0d151505090406051006080402091801020702040906020c0d1d0f0324070909 67
    0x20740024901211940851800c02d81030169620040c1c1b48001c90300016035901c00c2d42411020302485a00c400850351280d0101c01013402113038420440680443c0c074003851301001d552961001070000250b40121181c051a5180f5401440c0c1010030380d5402107002c03d00082072504007117213500509442e50240d013114681640f040300c1011400c1e01150070b11b031112170b0045007001030503042c2001011800191130101e4103003040750258083d28040d941d8805510035400c1070056124002c103001e06180f00455035070200522613008403d20b954a00c80c241041981c030000300d070680900b03640c202c901c0d90700c550030400c400c031601010400401d05803a0820b4503041540122320b070203601500c1c500e0b429040000c01e1504c400e00750120740d6040d6000d44208016400c03400c003440207401c60f02441255016201d0b510780c00f10321881d0620351545075608003c4015140c002084080c2e4007002401360140120f490114186142c84500360310740e01080400c6e000c92620481c010440b0101d42c0201103034526000134107024030760b14 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 967339937 1250 967338687 967338731
    0x3061403011a0f0a08070f0608070219121119050606010c0f1e0503030712060510210b18252f01021c0e030f161509140c04 54
    0x141d0307040782c40c0202d2001190303c10009030050b280c58030901b000000c0072180a1644812030380d0740d684500a9885566007282c5822034091200c201c007840d60402004111426800044602c0c1c9061820b48042c07456400c3e41002c44034a0740980c00300030040c0382418401300b80020395002000740307070201003215156100341100704001d0025024007c11000441400010900ca1f05002c2d0004222600c86c03130801c07030080c0510601900302c1c0c407841c20300c1000245410305484a0803027039551b4032480302440200114240c1940c42123240d003c0140c0b0782050510f16180c0c065030841d11070080200d1a042e01d4a2100704407a00c0c03902c81e59009418001c546040240d61080c1000800c94608000a41100d8003c803040f4000780c045203025003e510004100c40900c184610000c80440881d40a004042d81010b52035101d0040045140030420100106000c002c09111080d400a1184091000705030128030f80c50200d5030500e00407504104031f0704210a851104018010801d4800c49091011429803480341d00c8051030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 967341187 1250 967339937 967339939
    0x306060708030415020418060602192d0c031703010b16050f0d0f08060901031205130b041409152407060c09060f090e070c0303180303061403011a 64
    0x3002c4041010402c07107001e0f00c800099006000d64403183c0302e642c1c48060815103005101e03030a00d44140050024004500e21000000b8000c140207802c04a85030848891000c1002c00400c0e69035441c0d0b01d244500c8a041e00400a0003006070324803c03401c2d4684014080e000311189003a015092004200c241c107080100c503210416503500b0034090f10241b0300940f85c1100381e000500d040c0141c5c0000b0311076540c4454201d07003030400f0f503071954015100d540a01c004400207000c00380c45411034507000807203640910024081920520222100d443e41e802603040c0f40c3d0010b8000340440d00c0038410301211441d0101510345c20403141c05008000d0008013000408544080c03400f14101c01400c0040c680442500c2c05940110350010010b0090314071000c0c0091003890782e030261101140c10100031603500f0303100308001c0e426030340c2590244030b003510f40001c10780301c82c0d440103802c404140d25a0403440106210301104600c140c8661000310b0001e04040f03943d4066540c000703009011b03038940440e0641155000340e142c0d0403408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 967342437 1250 967341187 967341203
    0x120626030720030c0a0e040822230910030204050a02070602040905010905010819020418200109090c0210020d060317070209070507020906010e132a02010203060607 72
    0x4504185800c50240490151a19000c500702c00885400e54070b4003086480118140c4014504000c104582d4035024010b000506400303800040004880c480144031101c041c0e0381341805c040c40802c0d40f50311940305810884100d4007681401102521013410100305580859900c2d0891034281c0e618540202507220188c071403522100882d00c0c4140300c0e4100c400454026500795622a1141003140151400303110b02ca2a05181400006030000080340c4011000044259800c860680d90200400b030458040310801d11044030004034000f03140c000c2e62a0019840390300e084000c1c00280001741022000c0d034015011141401d403910782c1e00c0e60210b8036090440506c140181c0300c5c2c2c400381c0321100400e5150002414540301100504406000c0405410711501c22511603400340e4034031104680900038684000e4000c0041c1c80031078071030b41c003840318559401d001070010f121001d0b46045050548081c041400a051403010303441224404100d040320404105000961441c1044004103241e0700c270303900002d04061 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 967343687 1250 967342437 967342499
    0x10c080712030e030d0e0d230306011e020c0307050306010503031c0605030f06150103020f03160309080301060e0f030102040819050f120405011701050915030a0219061206 75
    0x500070351043c00304502c030000b105c0c0c80340c80600c03550006010520303140c80d062007511501040303288614001d020038003041200902e488680107904000d0f0f08040d100505201540035081701500144821524400f074690040c5110b00c0c1d4074081c54203020b5250410350003070300700384014006924004115903a0201001030000221500403020004107040d4000680c0740c020300c04200321280000072414083c919403500801c5075100c03c00194100e00c50041ca00340c1800080c80060742c1e01e40c10000100b2212454100400c00c0c005076929131b070450b4402d80002c800304841002c0c1e51154100074244070302c404d50940085203000c1c1416092540c401d4140e81000c130307115180f19401308000c410321034541d910b041c2004549030300990101e145c41035009400b0300c0e80007905e4a441001c0203000e8401d0b880c104c03000548850801e40717510340c09e065581001c1c10070300c0e01486503c10300c00050303d44044903942824a81030311401d440c100f401c028100c205041e808403106042110134058000c031251140800324414038116001c17 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 967344937 1250 967343687 967343723
    0x120306060806210d050301170c0d030c03020c09090f070e0c09190b0f04060f0f080f0a06050d050607020c01050c060708040c080316140d09090b030c060324010c0807 72
    0x403d802d10244007140c010940c0200a803a003040146042e90942480075031055941d815142d6103003601303021340b580818540001c4010030b015003514032801c1e00900c1903a0300d44050001040104030261118051a07200e00606610700c4400e03c10080a00410302c15844d25042060075140180650513445c0d1013460080042c1c5031302c50500303130424000c1004245c0180c403280389003100403858203e44504400301c1c0c00d54154001d10342c424051450b5020040d114080e65443c1c08609044440000305240b001035515400030400d80d80341348070b06820612640050589250110340203050698440249061050510466070045d1022a0465000c080b07860715480680da0b07070800b5009101154040542c4e40000662041850400200f040c1034500441c0c110792035401d00621503032b603002442c03d0000050b90124040c0044a40342e000b0503c055401011514550051000103000d6482550980846a070722140b0140e0f83e20414112030310403800b428804122006603c036403000d8411541d00070440440810120a2 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 967346187 1250 967344937 967344979
    0x606101e0203091002030307033e0f04030803041a010f0603020307120504260c10021602040c1d0616081b0d0f0206180c0112060918120306060806 64
    0xb18840082c00440d0908601c02d02948031f6100382d0311140003a00388000c0f01e0134507030b00340c2c1d1440055003011803d09068100d0521401c140502c20f000000841040101d005071030080d40142003c1d60090070b02a680e0b00309803405801c1103003014807282d07284009100401c4a04001c200480844178030703013030141e41d982c2d60b1602103440d40c043d2080766404a1501043c0000d0000308480030030941200480303240c448500300c213425031500a03102ca0000702e9101d902c49941c0441c25130003030000510103464407694114070741d00080c00c0d581a81c040c8000651226520002e0f020151118a0703000816202e01e0310b00b10401148991100603040e002d48000c0002a0400d50003070b603401200d01c3c05804d001918103400044d000204800a42d0100f8401446000b01140340400310755400400c03c0301000c024104038030028010b4480760500308100800075a95080019011030a0160341d1161004008001201d0990b1034440748054113804007000b010710304141031180c181c2040303002e03400180071144409801030703045140b0302e = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 967347437 1250 967346187 967346197
    0x1401120c031b090615170f01150c081219060503150712050c04091a0d1713060e0406090b0d0206092b0209011e090915020c0c030606101e0203 62
    0x64240c4c0380210014094501d0341e80a210401165580c12190002c0291800e4106059461041d40340209004228040400c143c180c555001c5003004202442c294a03420b80681001b000109405160400c0082c0c2c040402c44101c00e110f00c040040082a00740804030384c0d500c0d503101e400354282e80b41c6004540c01c5402044c1615010301a81000e10492030b00d01c0300b501c00d40d0001d00c2203200c1c20b401c090620b10720300300304080d00e0b40640025128445064082e220b14081344880010580c0231007040000894415122901b440502501e4070b9400c041e00704602480304513007640d030091000500c1d00d02c0118180c5c5d2884c610940481d0100c0b000d60711764040c4400551262200d131890155070308041d120b004401d02e02142d141c0024001c030f803105d901d070303a03141065259050316144041da2844800814800c114103603025820190003024260400700002000b2000c07a404100b80d64810380c400141c0151518081210560001082d1402c1d00703512107481e0042c0c00072100c07034140c4103140d45140b4464051442041525 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 967348687 1250 967347437 967347449
    0x1704080a03030f0c0905030309091e07031e0c020618120408011409010e2e090b060a1e062604200103180201031a131401120c031b 57
    0x504480d03080d28025005010b108070300c0c101e2508100a41101a0081070003d044a1020700650b180941c02801c010030000b0040c4440880c2c0c0c41240c105001100c5030701003034450344841e200003070b51501c40c40301d041c16022010360314555181000e2007201c00a43c0822080e81103050000c0a88081000356521410100d0070b07a1140303103040c1c02240c0081ca01805400a2482000000980c4201c1d210401d0749c50903601440062442e41d400300b002c5030704180072001ea40c10382c0320301020128107004041205100f0383d501d0020544102c560705090002030318026000c00b004011142ca4040c008006800345000d00301d4911031041172212500b800302c030004036030443c0100d015258126000d2441e0903d04880c2e801c5c281840702041070300320385085510354004d120300d01c220100c41e500b43c2a003d446d640114090007540c41d045031000c515445038480e64a0750381445c0f51068035404042000d003d03119418000c11070580c0003800e20358000d4488008503c0860310b480c02e03203400407860514550b880750307505120101c039032042c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 967349937 1250 967348687 967348693
    0xd05091009051512010f03050c010c060902090a0c020124050d02040e0d03090317012111090702010c02160b0d051b0d02041403012d090b04110109050a12170408 70
    0x8550500c00b150051850131942c00000810b40d072518103960407a0140e001c020959881620164910343c010b42c0c079482654070421020640c9002c5a0120b02003240030303171740000c0b0070b83c4841c040704c2c80b16028056410414070b003075080d25074841d40c0c01200c041d0809510455001e903806e150105d042d91665041782100304a81e100f1035165085c0c00030010010601c04409030b0004081d84021080300102001d0f06040318002508001c1100520980f4010790010741412146180d414180288680b01d00d221980b060309070750000500301c00c680d0070181c18110b070007800e0240c100d10128140261b5080d9801e44015108603040002c207940e40c185144221300304510552540c800101d0b02e0a02010300f030f001001070b00c0e0307079100180031040f050043c1404d803166242c885060348450540111100c1200c004008103950a0300b0100c1d40446681310420400d0086c0c0d410395a60702643d001c440c041d40c0040706240100070665004009503d00841396030484103002000f4000c02180301d0400700307001d0070816600901555410707 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 967351187 1250 967349937 967349959
    0x15031a060a14031303170403020309010f090e13140c0109031b0302032b092402010f0f06140f030d080429040b06060f07030e04140c03040302010e0d0509100905 70
    0x5080100740c405007100016021b10b022440800000b003118062541070700207609040248006603000240f016240081291107900043c0804014184c01d0082111503d16444803001d42010900000001c1c9105aa9031001c0e10044a90341d200080c0070460390840904800b0f00008a40d2a48100301ea40c4042e40c180304d80c560700001c41c0303504135001140a4240300b1003400700c4042442a00c11041501c51107982d200680f0b075010008482c0084002a010503200016641e852a08100c0442d143c070040125429600c000600022100c09175442d00d80100315151030b03142d00310400003941d03480b514107a40200b000700070216041000301600010a9103489403070150102010b4040e08204604031030a451420380c03100800c460382400720860340003060707100d0450701e4104161020303910096002d404682095451101100000c0f941c5141c0340140c1c02c4405055803418182002803d41e00f8044c505a010b4003c865444010381d0480115070240c4008e5034040b040540440c0c041d121030881d41e000f5a006000c16003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 967352437 1250 967351187 967351201
    0xa020c01050124081b090a0b040828050304050d0501090203010203010303030228141308060411090705090901090947042a1a0415031a060a1403 63
    0x40c000b01c500300b2035111000f0864202104455001c400e5a40d0517140d000840320a0100c00158010007a0030000303032404480a588003001d540d158095840a1165084400740118454640c0c2d6201a106644001100301c0800c88d2203480d1607207e41d11800d4407840b41c43d134100e41003000a40202c01c00f107030020000c540340e42e5603050243c06940078454040c1311045c2c5101c10390300e08131041c0ca404104c008556600c1490214012420140e61141241415951528100003250744040243c1c0380b28520800303205141014030001e100c0640d1014040c0005c0c088140548146915503083c22411508480030126000249041c1050404494035140004c0541c1e007002c20400c11020300e45082c82103ca48c82492030201485460502d0101036130000c1c00460f298401e1180d030102c455604448000030360401031619a2611902080181850900c07820000030500f00038080c500c40504451270003e0906011305140c0070050700007a180100e4546c0b00d004089052001c0a01c01c24440400d0708118407900c1d034a08000e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 967353687 1250 967352437 967352459
    0x70b0106080721050f0916140f0306130204050f1b07140a110a051c0b10080703030207090b0a03030e0919180210020c090a09050a0c031109070201020f04050105030a020c010501 77
    0x20345017442907040201094840d0300006040f04034441203801d002d00b42d4209030f00c0130020045110f102d64010f402401d0900b16070303400c1c061301c0c3c020304e03106401200380d420510501c0291607000f48150741d1078402500704800c0004007487d0042001c2c60362841517480a0503d4200f108043ca042e80c8451340c40380700c01c0d000130040558980300341031008030760000c100d548d05c004001c030b03140207807c0940100c60201ca00800040303403020030981007822142c0386001252203650301c51a086050f4001d23001688199800c11401c000d034403441407444016509a40078a0852701c1c05400c0d0520304410301e000341581d90008517007401c1d05020356800d000860341030106024121100d040f00c04404001e078441c20700000c0105483d03000242c5210000c0c2c0241100603566210f0381c80c84000e100e51607090320b16010f00c034004400180760740d24580283d441030601c3c541c0290704c401030001403000100701c4001c2d684108044c5d650280148280c84c2128801d10b002650307542c650b040180030380680310311500b5560900d400824109001 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 967354937 1250 967353687 967353691
    0x60606021b090601020c090603010228121a0607060e0304060c11100c1704030f0f050610050307170313030804080d051312020f03060f060a0902070b010608072105 71
    0x222072428035034410394200440c00350b0680d5807501503808042d06d1081401d0801c0504e500400003030006003000030120b0f51240e403c0c0d0700010244e005d907510300540d81054010864840c1c402c0882000c0003049045d0020312455a40e4440032481040007003030240811565401000e5001c2c0740700e0076662140e603203500151142c00800c5040700d1680040b2900c900c0c43c00c08509414140105580e11400d40b001a254035010541100f40c0640c82c3c502040301102194004180c414840d1059100030f150704164100039017040310141103503101d401c0d051420007250798001100d20517640c20b80080d2508489802042e803442c4600c0c2130141080c80391342c000005000b2010080c1046400d4241034440f00110214100c50782d00c1100b141e8840ca01400d14140010b41035040318901d950b1015000d18590a013050000385403901c1214040401c0c540e080402400b410f20322045002498590f038150f04152003581c408034000c1050060504002c1c0c00ca000030303e1284580c0c0b141410a40c440c2c050250400d80d103450740050a01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 967356187 1250 967354937 967354963
    0x30b1c0803070207210201111203010e011508040f080a0e0a09050a0506010507030903080306061605070906080a0206090f0d0c0303020c041d030706050402040e030a11250e0a020706060602 82
    0x120013000071a42840352600125003d0103d40039a03e8869500643d0300c3d580394181e4207542e1040c003032540c440b20a140300a40c06000914603d024541c504450070300d0030900d040380310080007000c40901000650b80c0e940c2d10744031644070359101c2d2124843e0000b162030003c07a0b40101d81c8810b441e07000040880483e84172900800c1c44441c284659521000152201c0c41210030060005810000801c082226a0b002c1c54110320010003643c5071100e24051750880064443c81940e0941152a00b00000040c034400c1400a01d40140503007022180313034001031600c0c003819101c540034680d9840b081e401c940d10050300f01d2815622500310140d2588a0500940ea4940b0090719030195184c06412520b0032071552200d40d13010800f00095252240b1503807460044c10b00134200300e0f001626000141040710040c009001c0304892076492404920700c0600007440e04900030b4040c00b400d11600384070b80754414401000015208040344034070064445150400091140140c0503000c41e203000d0340811100e80c040399410340081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 967357437 1250 967356187 967356193
    0x1b090b220e0f07031b06300b040615090602010606050403020f031507020a110a181e1e060f0b030f040302120a08062106060d03020a05100504140a0f03030b1c08030702 73
    0x10725017405a5a007400e080ea01c04072641049110601f526001c849860841d141c80d03800308400c91404041003e540c05608454241200301c0003060b169540807032817100034915840203200340b9240c000c001c0c0241c891400301a000e441a04a051115181000621034112140225410034a0181130081d00d0740e060040403500600711a0b0400007600d4101800340903070710790101500c0c00d170300d401058000400f200600e03c3d9840c1d40c000e07a40158004248034180714822505001c1d80c296048031006000c681c010b4200d04010700c1194010f004c840c0030700c8252a030180f8000901d00c0c0544890400f03911300000c03540c00444c185000580101c0c0542e0128055004060594100c50840c1c01d030142001140b80c083c241d1411a8484000074015103002c005503451540680161580064151a010300304056200124400c0b0307254010b120400c000c41c1e085840e040a12005000012810b940d00911402c00200140c201034841c0c1c040d0b001940d82030700c0103414182c03540c1550800040792519142070740040740c0342c40240c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 967358687 1250 967357437 967357439
    0x1206100203030106080c07060e120301090605041b0c0c030b01141f08060103200f030f0c0a090909081611010305070504030b0c070c031b090b220e0f07031b 68
    0xd00000680741621256140c015950b624001c1c441181e802c82c21065030007940780c40b503c000090051210031070702084105210354035812f01d403a210a543c0703d68040c9008a180c00d0400340ca10426601d031040d187c04034580a0b0680081d0700303055042d450300ea00064001441e9000000703613540080030703049100c5400d441010034508100c5061038802d6016030400003141c00580042e005610a40c0031078141c0c0c00d1411030420a000d8a004140907030495440b01c824410300005001c000712802c926181d018a021580b9072030302c0002d05c002008000f082c8a0a51540d468001c0c03141001103a13401d603075080915454140186c48281041d05071003002c9500540440c2c5448085005240302e2001c5400303694101036400c0b4aa00c94410110700c2e0750001c00259000d8044a0000c000551050b072041c01141001c40100e24882c1030202280071501400b15291207a00142504942468508030a8404050100002900c81c034401c024078102081d86081000c540078040c00441007100000813821480d00d24a40040c0352 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 967359937 1250 967358687 967358719
    0x70c081e011802010c0b061507060b040e030a0f050903030d020d24080703020d1505010e090c09100501110703171e03070e0907032007060c14091c0203031206 69
    0x200780b80400f900041d01c0724a8600400c4640803096001000074110300c0d07500f00621001036107504001011a4269250902062586054003543c4005164840038601d481720400c00900959207522100080c0030010401001640d03040c402d49131040b4003100309654840c1101c21310300050a9103906002141004880706103099002c10b44041958009170003070040308d056808110256040e1038081311688103018484130009802e009160003854014102150b40c10303c8103445007810800c08070315005881c12003c0081000000400b6001c480080c02c01a0748105a04052800c05009400c0505172980400501d0b80b030708400c20003002c031810311071880a151004001c0502c0ea41c0b1044c0c681c00c0000d298150700c251103140c40e00c03c040c0c02020b0350500185000e542c510001000301c509810100d040c0000c46c03042d0600800e8000c4c40611015845c0c44545051442c08038411760103014449805013070b9050400040b269150408512140c008040703035102d0a121000c840790301c008503003581c0903541018900e558 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 967361187 1250 967359937 967359971
    0x8061602030a050d1d010b0a081203011505091914030c0604030b07090f08060114010c051b030109150207050120032406070303090b01050d17070c081e01 67
    0x10810594069454103101c0207044a4a4000c130141c0306030165540b0038050200d0741d400852405401d0303c4008680b1040000421901e22400e502c0312126802040350440c5a5490354200c9041d45c1c0700c2c80140000781c4010b40e04580d640a01d5942c5d6410483e2040c0c1c030100c0c0e50045500e2411100729040e034044101c0303a8001c0c0b6441d84200300c990354100c04240024400600d400d101c150f844401490484101ca07510030a0b4450300741191300c107101035000305005104200c0d5060969119403401c0c200b03d140c0f081517580b031658400c0801c08030030505e1400e49103892160f0342900306050319a0004019604404001500d0000f036001c9402240c2c15807170201c0c1440b0104403480c0c0d450040c99800111411550b07820b11440003208100d40c000704294940513640a02d680f000302902c429406079800294038500d43c0b030320349130384130303040c0c0005216610201807000028403600c95a090048003180080e1120300b10301e000c00d880c0c50560001082d50060b4460074544c400e19031030712204211114000d1006403074903200128 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 967362437 1250 967361187 967361221
    0x605090c0108010b160804060c031b1e0305090d03080907080d080a02030402010c0b0903031b090319140616020d140409090f061a0406050f06090d1113060806 69
    0x3022a002e030004008402d08100500004030590036201007074412680e607001994016001000490700745210b0f1f40906501c200401003030300c402c03111740081c401282c60704040c4080103003000c0900d921a203003800c00c061080c4140c035416200508001c9905d015481c018240120403103103210140709203040042c001074005000e03c0f68012a0721015443d8850001000c007035032009009074184a196404440080c0442d0b070f0b40f9105040300300103591241480c900300624903a80031881e0100801c2802488060360380425280e003002c0c0c421900e18a41c401a00c1d01c19207400c892000a1428003815040001c1042007032180a0485c60641c00d940f40e41c03404420961300405290700c0c9a6a0400c01d11080c030029a040d1301809415004d01d18144030344560350b5420050310309011881841980240d46031b401400c1c5409000d026003000c807042009400130001050a500034004c005104018010b40d42d000e000b100d0300c5c13450305000c0103001c102c54200011340b03040103401c00340300340c507464860580061500388021040071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 967363687 1250 967362437 967362439
    0x1050a09080a140909161d0f010e19090204081e0d080a0e06070e1e090403050918131e05060f090106081c2a02060d23040605090c 57
    0x80d00707050200400f1522140304442096507040100401e02e450f94400d50340398800c135510103c00354802c00109009285003100c0c40300d411021042c00c00300405a8400200046c0b8150a1801404e0010464005440601d40c04c103040503a002c003540215425803141c0081081e03481c0c0d841158504103183c52180708410021291207442d801407218080103911900c005500110084404030f41056032000c101d0038080c056a1020200e5200005081c02c1d06048041d840b100c024403000b200301c0003c00000c105107034001400141000800624040c5070766031100f0220030200701d600c0700d000c1803400f0761105070f042e0b01f05442641c50b00056400d02e049032000c0c1d8100b1160395400000340000b900c49105121490b40040e115011035501ca00c030118405004102004c50504036003110958a04041d1024101c10462b01102c0c40d4030b400c0e0841d41e0340c00c0086400c000350f07032681a912150707110411480b8100400c146d03040d6003c0307a941c42098071541d61741c44610b54000c0d8040c603020411038035043d5a90390741d0b914588100e = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 967364937 1250 967363687 967363703
    0x1d070303030507050702100915030c02060118021603030506040f02030420010915090512010c020307120212030a0b090f090c0904110a080a0b060406050d02040e012a0201050a09 77
    0x1800040d1080c0c100b2508200365080480c02c0a1943e4001030400807030458800028061320420803124000102d00c04c0180c8003418104080b04050303070020340350300050081d00a003516103540003059140503412203010309614840c1240c00500303403074014007900301600c0c1c084c441c07814407400100021052007164041e59102480440c0003262041d00f003030400d441100030b414404000d2000560f80c0d00c80c44a8410903070265515000039041c00c0030000d40c0e0034601c42c0c5400c180e140190800307006800000321402540c009441c03c0300d055145400704d2a240400d441c070441501c020043c000c0d50002034205c0f01e451202125000266030700e600f070103604d2a02c12581c0015680c001d40012225042846850780c000780250140070b440035841000c56041c4003941d00c0102960b00c822400b0701800550750400d074012074100c5090140d54034020005110030190b81c4060b104680d203c0044c0303030705c440940c4000b1000010080c003402c4941c030000303450a803c840d001980007650800300043c000e01301030722074050310962144003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 967366187 1250 967364937 967364939
    0x807080a0c0804290703020904230105060f040b120108100e030904090c0302090c03070f0f120c021006030602180301020913180b0a0c0f08090a171612031d07 69
    0xc000f507080307110651044100f04d6588010707251800318402c602c43c10054030050380e203070140403c1c0320413030b24083e019240320500e010f1440040383c000408070f1b04440301181c01d2500c442c0c80049a00301d5100d2540b102413440c1c3c00041c546031800c021594203040307175a600103465a21f201c140078a010f48500c2c20041c40d40b07400070011164140340550002c1c1185010307034200034803103849134082201c061040d140400031140120400400c1588081e8903919801c0d01d01e0008040c42800c00042c004c1c030010101c9040e816100c19030034800a1007045810803440c03a11030305100d81e075500e00388403000354443c80407450100144040c1640701d0905000325083c00030041c000c0c0103c3d81762400c00f1401444d140c42102102482c4006070408a80c06c001814004c1421031400201c2c10881d8401504501d0070746403440600c0b0221040144d045004601c40440c150003121005c001025401c01001e10300c1028181d0003c403400002080c14440c00003908540c0c4245510200811002ca01d00c0c10344503015000c84a0140d4000c10b0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 967367437 1250 967366187 967366193
    0x402061c0c0c0b0f07080c0d0e16051203040807090207151b080a06081e0a0b07050414040b030c100306080a0516080601050a0b0f040306050c0d0c032f07060501060807080a0c0804 78
    0x1004000070030007523400240345c82d4089000e5003050852401c1c280004980301c1c05000030310384000d0361104001001c0065103420b282c49881030726000903125121540e5070110f5500103002001054802e8946010703010000d0844406201242800b144900d1001445040c00100349050700c0c46070409482c0002e00030030920a101d007640d02018118100001180103801c0e0503030000b65110ba519005402a80b01d05484d1400c1a48543c055069844250721903400e21841c40700586010486800114003503403520b41010380200141c0203030040c2e90007002c2501c580da5404040c060702080701d07203864100d030440c0c50015036075200a6a50741c0c828010350f0741c0901c80810421040b95918020003420503440c40c0d0310b090664a48900f800c0341d10458600c01081000501d01100c1423040c41100c1c403a2010b407c040203100c04c11038142028000c24840c0b051128001c810036002207050340f0a4500c21a84250180100d685814004062480a40c5c003540403810030ac0c00310300ca0500700c0c0650111315403142c0d2505500da031591 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 967368687 1250 967367437 967367461
    0x8060a052107031a15030a020d030315030b070c0203160e070f170106090306050f0714090f03030f070c15170a0219020d1808060402061c0c0c0b0f0708 66
    0x1100020329842045030000004850040000041d181d641d00d5068a26299030054034210f645d43e0824402d810243c0c07090016a038909800c02169014070300000c43c0600103120200c000707660b0300050b0081078040200800140d2010340100568426401e98010b280212091900b000890080e02c2d8050380241c00140958860481003420440501c4d000105101c62109000e481c80c00381c1009000410112003031061290038010250841c02c468103100c40317860a0403000304040104003418094920002ea00c0c015a41c610f408590f00300340007800d407580d503035940090205030b82c0f189401b11499041a000001d030a03203414100c0c0d152f810551a10049000b64411800d00704100a0850200c660b091040038000c100000304180c4400300b68004018040c1d16210141243c40c104041c4078959200c0c03030050221210200c0c17542c1e00540d040e1419a110114003480c1c0441c803420380e0300841c101e81350100b200012503125004104141c02a00070316440c1d01c17440d480380c2c0c0c01e00040381c850b400300d0084404908650b01403 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 967369937 1250 967368687 967368739
    0x70506060418063809011413050a0b0a06050a02030909060a260f0a11090403030204050d050d081b221a090406141e040209040609090308060a05 63
    0x20600c00c070000d40e00366a840084400810502001004501300880c0c0b41024040300ea206010340b901e018188a04d03400080e0914105000c0d03111004204c2e4280308058558494861100e4402c034020301241c5083d030086c0707004086002005115005910000407298000c200700c0c1c01c5001254061854142050306000e408400a0f000b00d4101c1030200340000d61111007002d05038213101104507600342c2e0b003013050082d01c0c044c507914420b0115007160b000c2e80c1c00611007000c104030743d82c821b64000b0199a5242030560088c059980a1a0409104a0341d0410081c0100d0b00c540410081d40328051a5100d04200c1109907020712400403902004000984906801500d0041c40441c4425100352594503441000740d02950800100074405000c84c05640d513141c0750140c500900b64400c2c040c40007000904c000340103030841024506110100c10b0468203551607540440e02000300c0074009000d1241c0d6000c52400820303c115098001078045d20209285280103413040048890003031a04c140c60520004c0e4215503608 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 967371187 1250 967369937 967369961
    0x411010519051c020705010203090c0f10140f191101060e010e04050f1002090f1234060e1c0b07031805061e011502070b09040b0414060f060705060604 66
    0x20295442c40c03070700e504e000602145205400258607424a04407141c40c007018080300a210703100380e014001c07440d01c980000710000241171501200c440b81e415401a01c030b2050364144450030000080650344800e0740f91003068001c10b1035886a006000400c0e0a0342200c2c8075000e90504012090300420044000b00b01160300a4010400d940c07481c02e07801802d9107000343c41c2141c2e444d46500410f66005500e0b040c6c17000300e94074400761082028216514401d60f200c050484c1d6000440c801c60010010b8184a031012601c502e40c0d07401c499001d83d442c0d4a0140c0401c00c0548107a11482101c0c2102e28110200c0384c01c4039031aa840550803070039484080301030b40502000381041d4101e001e001c10f0600801c000304400782c0240000c4849541d00e01e4284c0b18481030842c1600000126a240d2152000e80360380082e03080c08441e1400f003210b0300c1d95106000503000d0051186040e903c0303400c2503180b440300301100840e28001c40d400c032070196803421441c2c00c0c801a0b0280720b00144c07a5801c000000386403420981c00c04491030b16 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 967372437 1250 967371187 967371217
    0x10c081207080a0b0f03030a081314010203270a020906030a150b0301051b0a030b0d0503030403030b010f0c0206090907050c03070b15090105031c09090c08041101051905 74
    0x1a15401410031440d08484640000c1c8140082c40320941d100d1081c0020300c1c2e410f0300d91803024102c440200b9503900c074008019003044400c10002d0704000020070400145648103043c00e02205445080d22b006c0d400030342d03152058044600d004408a18a500c14008018010000c1c100b90280d44e0200004080b0091000c1c1d0540100031205000550080e00d07400f16200401c000580620701c00203050845d07a0060500d04070040120b414900104507900381c501008452a010490814101c08103555012400000b8624800417060108041c1c054222008440d0280d0b12114030700488002114403008002e00690401410082d9017144e050040b003456100480342061440c040c10300c6195842c6a000c0141a6074080000082c4035400142010405039202c040350062620350505000030740703903007180a040c50380d81c5c40c2c2202d039a404c1d1b004400003402800280c4007084003100220014201d4007040f6000c4a032100c420b0a02e00196010320b059460001c0c0a645034440045c0103070f0140c3e8168021094081034203 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 967373687 1250 967372437 967372447
    0x50916020c0301060803070c0609031a04060b10080702151029070516050603010e130f0b180f0115210807030f180510050a230702120c0f010c08 63
    0x40c4013401114000c005400042d07a40d40745071b0400c0d20442c11941c000d8020051404000c00200758820060a0100c0c001481081d4540707032131a01900400d100549190000e1141d07941084c050b4000b00a01e02c248815000d90714004502043c0c40e19049048541000e2810225003d0004507528100c481000c00480100f04494965500025180d0800c50f400c4a080c2d000e001c0f0000c654260001500050009545490455041105806e40340b81e0080401c00b5a012030307540c1c00140007550401e800500e80101d07130301201d13041c540041440400e903070036620150700c1102c0080803a010144602034121b410b985041000f1400c200d41e00c2c4c3e040c40c4401c48036150300c82c0d510b040360101c0c0340d400041500034482d0700d560021002590000c1c1ca01c041241720308502c01a0b03500c0c00c200c00d440c1c804501d0b607120f1182c5000c9a0325500480d090b507a0b011988251880254521500d080c46030f580c0c0c0041080d1030080f1030b00312030040703080807a9554400703d080c1c0a81240f1203a110b1940c95005214485030725220300091410a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 967374937 1250 967373687 967373689
    0x11407140a080403050d09120204050402041503050102030117060609010311130218010801050d0312230c0405150414190e1906080a050705332101050916020c 69
    0x252110720240c9605400080802c10400704014240038045142480284c0519209055142002601010b809252210002000c658440d40300b0507111032040d001f00401516070611a000303400901500cbd403070700070700811040c10040009042d0f06ca050024089545603003160b41e00d106020743e09800303c5c0c0040012200c4a40c0081500181294035003c04c6a0b045c82000781c800101007d1040e8001d600880f207110700c29001c241d000c456940d000f5003041008c00c42102f20300c440b0410304402190040511078400a1164280d0340900a0088400869601d06010140c550960452090f882583e0150044484400550031b0880d01c0305000807842d103101043e282d0740c0d40c000b000c08508035078071046407101a00780910002c591040384082c1c090240100340307100184e40d41c10b940f090b003405a18444c10b414485100350704649a2118406010190020040400c0d840d032008c0343c2d0820280200c4002c04412070681e905505024107040b240000c2c02401d00b42c541510482003122400440350850045074409522 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 967376187 1250 967374937 967374943
    0x201090e0c0703140324012102030a0b1f0806040915091b180207020604050604080703060506060a05030f04060e0f07061707050403030f022406041a01140714 69
    0x308054050001c0c0c0e8804440ca80189040d92415032841a400148248517031031743c202c0c54194000f4a94800611040c46001c016140c482c1d0b00310078002c4d00891884003d10070075091300510b000741d900b4842400005120310030020140d210005540312040b2410442303a00078400e281c503d81205000e040010303112041d4954080369007101104842c0551542207175420005c3c0589040315484c40202e0013900142080710540d140380c2e403c281c03120102e4001c03402009650710103007214000d102c01040240d48075511203c0075141c0400d80700585440d0300e03000c00070700c0034101001100c2c1c09100a559451440d0381d00d0039120a08a0040d200780d415559400551407070480070007004000e01d042a00400c5005d103045001007802045130a00c009021004084c0000c041e00a000e41d001d5aa050034044c040c64102c91040f80340481030070802410362082d010081518104046260007014141c909101c60491014501214802242502e001a5248005c1c240e6480b04402411040b0b1140c00c941591210050310b65113 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 967377437 1250 967376187 967376191
    0x80a0b0a0228170c0c060a0504260d0f0e0d1d06160b0106090915050307030b090a0803070503040320070b18120c04060e090c0415091b0e0103090f0f0201090e 69
    0x1081c000005106081e5804c20000c1d5070b8000b5290800b401989030079900e81042b401c4440c0705080004504088081c0071034000240e074505442c5a4082100f100c1d1410f14501404038044014020300500134991101031003902039203000c4039542c0c202c20043c5903034014001d00d5842031410740d40700084509020700240304040058000c0029a1300ca51070242880c041c002198604032240145c03000c0803204000316200814054201c80d00070303441c40003660340c0c07201090400d095010000e01d0b030780340007081003a015000409903014602a0b500d80004e4804481039460540180840081590010380104190030b0490b0041c580c9030401b01401d80704000c44400310b07414140c501d03850384036900002c805060701c2c01c00d0b110f0307040140321402d040500d6051a10b146512070320f000d00a20b014940b219001850100c01c800502c0080c002c480c400c0281a00601c40c41c01d4001d02010300c40c00141503000002600e42c4a4001c2400260300480303441c0c070018680c2d81d580b9400c1003411040b4144800102c4c00070f50b1865500da00d42c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 967378687 1250 967377437 967377451
    0x31c0f02130608060a1a0c0102121e13260904020d1d0a020a14030102040f121203020f090105160b042105030415090516080a0b0a022817 60
    0x4181034203040015002000c0149405c3c050944100100b019111000215045020000e581503440070103210300b901902ca1001c480e05094120002d0200c01d100010740003401c008520102c8403103440d244036102e180340c2201c0303014090740c100030b016a11f0302d0b4001c1640081002d41803c05c2e80350240c40340109050740c2203a0300d1442d000b59580c07000f030040c02011b9070008802441c9400f8220301c14050307000070705407461400f0304c4503c41c40d00c114903120b9890950468000d041e0b40341246440d80d54901d030f10807100b02000e00807104028501800d0005600078020b0300c151080c80241c3d0780c104140d400045034190444480c008a0300c80039102d0340e010411a45040303009501442e041405010381d03c1400124007020760003141005820404c000201d407041c5000361403500f10910110b100780290521600d0510200005940610025800100880000750070300b2614130444640c10b4960b80d42c03503080c0c104d000302c01241c0d036900c0682402401c81216200c0307600c001542414036800d010320101d0402d00b0000121100 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 967379937 1250 967378687 967378717
    0xc0d111821120c010f0209220906050a09061d0c0f011701080307051e0d0806040914030c0106170c060a020f0f0304032a0e1e040b040317040302031c0f02 67
    0x39a42c3c90003c1c0a082ea03040c581103001d520381030500c00881ca0702802d000410303056168100450380c00c0b030120b40140715015080300c0103200c41c1c200491181d006014900c01251514540301880207255111002d09601d2440c000c05001d5511102d801d00c850342c840f4015890401c400561b02071a0601c08010080c083d0560340025030700c486540c600b243c50b150120030301809800c001c00c44216a00381c0045c070040f10403240d1400201544a00d00842c0c0a4012980020101803802e140c07801c081d103002000c2c1901e0315950000340b104540d2003072400441c003403011030020103810081d80c55450703081210007482c0d0303002144100d8040d40e012858807420810240251143c03a04001400c00500807440b0040034a10100c406607a020804845c080c0703034079603540c8100c0c030b0950b81007800240404c080d0034038500501180d03c1c290784503280524041000102c1181c00310301140301d050707880c40c0c00d4068075282441103a16400440c54440c0d01c0d85940d0b03a04416405580c9119151100c04c00709810600103002100c3d0701101c8 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 967381187 1250 967379937 967379947
    0x14011401031a18030306060d06170109021c1e11100503161e110106080304030303050a0509060108030315040b1816030c02120f0d050c0d11182112 64
    0xd4040700300000d00b01140b03d696291041c94210404422650800e504031002581c43e005034100c01c01600c0681d0042c8040b850b0000c42c111a90b4041d08404a141c1c8229032005480d51000b420500c031010001000e40040d890f0240410800011710806401c0d601030307030020422003a03040014403410302804901000078408402d06c00c00000007140700d03400c81020308128260b600000c0c581658880d000070010308205210b50b401c1c40e01d14007948010090904c10081d20b6440c0c0c2ca80c20007801402e001d4a40910180c6414002800404040303090ac1c183d070345c107034040d46c60341c0c848000c00079000d41c10030031302ea9000355240706002d425500c0c94052503041500c11164011441c2c150204c03ca507161440c60201031508080c40181541d501155000c01d100c40c080700a034903001c0c1c00c01710215902601e00d800102a04e00001d009481e18148090408015001000d1090f89002d04401c2058068440c83c407400d05001c000340c010340c1c58604003c0504c0c0e0940007246403000c2c0382c1d402c000d00d0130b00683c05800071305c080050 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 967382437 1250 967381187 967381223
    0x25060b1c050c0d0209070f110102180a0b040501090519052e0c02030601060f1b03020c1c210e030a15180818030f01090506071d0d1401140103 62
    0x8126491000100c80f00318582c0d8180d00440c003580d000806002c100301c001c404100099002e0341000896004000c021901c400c0c6000d901e2031121025281148942507107640020790020641c1120107407903041e0b4a240520340307003e052125446804500000000c0c007400c01044644032812117000c3d008518480c0b801104070160758040320343c5403210b03c100704444030641c600940c0380000c08074111a0390346884071250b030528500b192074010300c01c903010504059003400c0f0700381980000c0b902446c01c2e00700c2d80415107041341403c50003801110b80e0001c107010034100f0038140384e07102181e08200c540107506011841d500007500203410446c14690403a00c41030400c50b01c00031540c0b82e201d009505103000041c0300b4140c003e80c903000c105006034030001d00300e25008100f6403a2900c0c2400790502c5541120001d01010076540b42064850740200e4503407001684072140c030300280100043c2c20904100262000076100942c0d281c40114030710049281c9902e41d05d0b06034520310b100588001c28001c0d4020350111642200f405 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 967383687 1250 967382437 967382443
    0x20f07060f09060b0303031605030a020c190b0f130201301d010605030303240316060e011d0409020301181401060501020a02330703050a090b25060b1c05 67
    0x54414000c3c0e00607c02c00c00c910104080c400d0f0311001c6824400d031a41d543d5181c04000c2d00c07880280c40035501444042201040c00c3e0700400040e144221174014555a402d250300340ea00720121110311100d2009003035000554013442c64000c00400301c103810110301c4c48500c4114244518408641602981c6115040d44600c0300c0c1c445400080000000348207a5182400003680c82c04064504040c407001b0400d0083c218548013108035210102034290f40c068041c0d400702050301201c621030200855070105141c5010741c840c8a10300c0078040352061041183c0c01500500c0001d204020040340c242d9038401d042700030002c40078901c4114512801d10148088070003030440b42500d8955002c903042d948041c0400c00142d03503008401c042c85104100a02d84000c04900800c124101860302030340e04100041c480040c10303800001070030741403402d48888101c02c0ea0751030000d906100b180003c2c0c030b4580540d01a0040019848001c4090398000c40b0080f99084601c00090302094000c0c40700ca204920405100d01045814 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 967384937 1250 967383687 967383701
    0x60316170c2d0f09010e040c080a0b0a020a020f19030908060408040e0408092e09051e0d020a06021f0212040b04021c030327050709020f07060f0906 65
    0x380c842141141d01d905085460140b4241aa0142d0345900004105501d4080c00d10610001c01046400715503035505682c541514240c1c0c042d43d00207900080803c10003c00240c80c10020b520200c1e40c1d09942c1c0d03180c4100003d4200440d803000f10f000b15510b60748580c0b010000a0111364200c41e252510440c0f42c07601500c0a6000d42c88450309801140c01c0101041d9844181c03800c6441c88107400e080c56131185402101c03485844920760340301c10008170741391192011000c0107006a006041501c1c0c0392130384050540d6102098800c595000c030310151502000703080d482010b01c0181c406480c1181404095000030461746c515040000103a10110881102d0303c400c56021040080e000c6046103440b42400b04a00c21050081000d012000140082403c41d03c80e1500d050400c03200c6070a40d15082030038070b00103018040ea15541003d14921030081ca41008600c1220a410341d032040c0106009403410f80c02c40043d40010101109a40b402c2c040c81d0702180340303070003209003044405000045400040c44c0500441c4d41d8 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 967386187 1250 967384937 967384939
    0x9100608190609080c03130e0705030402030a080a0e1f02070e07050403060507050f3921210604180b041506090c05030103020f030607020d0503060316170c 68
    0x4600d00540618007004582c1200b00800c40042c0d90400b18441d118000c0408624030000960000040c03925075041c0650300384454142141c1c0741e503113044030940820740c1e020354075401c08104500084e421800400e220000c906020000003002c0c000111054020100e160214014a29000c9000e9040c4080d401030f10340b084101c0c0250603d60b038024114061400300900c80c40c0d607800821070141c041d40603a0300b450054040b080da20703044120304903140072040d00780d1281f0328403030784201c6d11032a5400c04d000c00c07041d0300358020040450700c0f0300c80c80c0901903030903080c00060800b0017040c0111041446018142c20b541c5034880c100d404c00f281404220390000d84142c403502951132906e000120344400180c0c00640001920048a00c4030218400505843d130001071304a02d00b48400070000c1d08403025504a9000f199030203031109002e0300b4541c07514003c60364440141c10844103804c1c01d038011000745401290280c1200c0b5292a1482c803210b2400c115005040c1900b0700c41c981e4485240200811541248 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 967387437 1250 967386187 967386193
    0x91204030b1f120638032a130e0102122401051b25031b050f10021609061716060c1406070306030c0b0310030f0203030d0509100608 58
    0xb00d003e0707501e4500715220328000e00b042d49481c4503060341c29074280b212040d01401400ea1042104c0d544003685580c00805035240a806100641a5030f0303038043c00d40305c060306008280101c0940a41040102e5154801665041d081e40d481e030418100909201500c000204070820a03518142a55481c013000e64204200b150784c65150303641e01e5180d03403040903600001714900c1305004d00f20b460745505007403c404c00500b850207900c065600d107903c4200305101048030300420201d80c0c25519000c3c100700d020300368081c3d150441c2c81da0381c0780803c0381412600845220064416182034545848610300540070035400703444000e89030070007808a4800d1822692403a1032503001400d6400090342035034040c404610039607040c041c0c4401e03140306000f90941c6694124446006030342051804420107030050401d80025204240d66240120301f00c0040700c1184d0003280c3e405c0441000b18a555126240e0101d5940704030707090b00080c0b0401000400c80d0160b00e0089003404064000703079000941c2c00301203940700c3d4048616a4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 967388687 1250 967387437 967387439
    0x10606051201090207030e01110c090709090c05070c3b01090605180708060d0c150e010c03050306060a120507020703020f0604050d1101030603140d0f0521091204030b1f 74
    0x61f8005503d140c04c21001e0034402880c58150840300e00707144500941c3c0e50006071403000c0203425640800020190b9100782c108010320070010400316100e0040d8480103103c030b007035040140410f004400710300401406d4400b88034004103c1f2000c407651001000802e210380b8580c03800610180c001402244007902e010781e9105502000c03583d407050081c001801e00c10a1000d5007001c5a0240c0360160f80e46112a0049141c403c40f5658080110711021404403000000d008940d00044030342c0304100815442e509030303492609549901007002802d07800f03050f0034418080454030f800c04445035406000c1c03090546402402002d40b55005114030034030501640d80c451501000140001da0725243d04030042074011004c1419003504100580c020031076130300040e24240042c2c060039040350000564044002d1103079916440322250003407c1d0785074095110000e034001d035841c0503107030004200a103441d07014084a04948140c440301402c00300c2907225810603100a00303928100300301e000e440c2c4918040620380c0e0b80b04031401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 967389937 1250 967388687 967388693
    0x501050703090b19060b0c07050a0803040b04150918090501050601030b0604090207051005180712081605070515070b0603031201050d1a1008010e0607050306040c030e010606051201090207 82
    0x1c00700401c824020400d455855413241441e41c420000f8048041c072440e940c11103180c2503681d5454610a42e44150090000402c00e140044180c40c200c441040701d4030309050402101c2d009001d800c25010f000c02c561000c000441c807056200310b6852807580c84001914000d141412801c2d2072004050a0505013005c1c1c5003c2e641d202d15003120100d9228a00c0140c460255203071090074000483c1c60b9010060401060010038801c881c0d1810181e200c20003150801035482c41c00060b2042e220202825491003070090050202c540720786410880e10841c02d40702407a8943c0005001c04800400485074141c02050420411042c8035140780c018200314002c60030844100100138280c40140a0540680a510841410000304481380405860060f814030306034506140c0e0001c00ca200791040c2c0c80c03250300741500c40c0040351000c184980103600907a200307071442c0c0e00c034401d1001038043e980c22601059695001041031403000c1c840e20b00906007507079400755500c030f0701341c462441107070180c1003800c1c0d00f40304120340307000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 967391187 1250 967389937 967389953
    0x140a0f08041d06031c17041a01120201050928080c3a083007030902090c0c030c10021e0c03030714040305030d050a0e0106030b01052e0309050105070309 67
    0x5580b00c05c0a40d40804184c41783e049460202c0a0842651450301e0000d00040000303820560b20000045000d04c8501e0b0b90392980d8803108054084003901040042012040301c0c10301c0c1c1642440c41c0380f03581c589103144004003414151103e1aa112002c10307008203445101c0c07071801c1c0100714800545141c100180c14001255030044170400502480051080034841d410424890195142801e264a0032080d4100c1440b010808002c032a082c0c5107644500c500185001c0d001f4490280d0701d81d00504880032566420103d90501d5115035001c0d0600d00c42803290180c4e0003005c01000356860061038001d40c45010150000304901c008500d0b40d0000b0700244140c40b4010000419a44e00c03c1f058602101c80c01d03250502800c4910480d000a0007601000800c550f2201c0b0740c0e04210300440e80d2081c04c1000603400e02500342210010f00008010340c646000400c1329103421110300c1200c90088410345510101617245810380070507200d9000100b611006004180402803213101d62121480c20244900c000e41d5441d161 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 967392437 1250 967391187 967391203
    0x2070b0405010609052d18071401030f111b03270f06040b1804090c03051b040e0a0303050a0e070312110c13020a0311031e0606070f140a0f08041d0603 66
    0x446959000c00540b805050f40c91f81e100f002c1200080d101380315100e030681e43c0003120038142d00380442c2c104513075414151618803401300e0f1546403084460a0047d8440061840b03c1b10b078a08100612050100710aa0b030703211181c80c40598225a02d80241540c402d01303102d030640111001d03602c02d640c140800c0051145a000720744108542c60407200780000560300040090031482c201424a41800002008004000450301c0300d0b10b0709800188461042c100c20401038800c42c00d08011507810900301c020000740603802c03031600f2440500010450115058005180117240e9000340c03440036503895150f1a1603044a03070251345041790341c054400c82d00e1400200e60100348804644511680c00200e001049120342e01860f51558000842c0340d80e420300345405000c0c812a6410400408142000f080c5540f60440c211003909078841d452075030010a64880c071901e0380004089994a00900151100003600004100c01e120300c291a91900d4604280c001d0001103100b10711203840302c0802d402d01c009035800044c00c02e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 967393687 1250 967392437 967392511
    0xd27030201112d16030c0603090201050c1002070326010620070603051902070b06040510080307030c031704050c120f07030609021203040f0504050a02070b040501060905 74
    0x2034226400000c40030710381050160710b415806414000c102c0302c0c034020b40b42c4031004030010381200c0c142850801c0d04041078000d0b02c0006c0214401e808100b020b98005e8000359151401410f100c3e0600c8140c0b140e02d41002c1c1d0621820201c150b00149010405400c0f504039542d4000c020306030b401c40c2c071340000c6804101c4018020341c4148090140c803212023081c48000c00601d1540c201c2520140b5980e54001b6000d000b051300c866094031005200343c1e445840c140700340c40030640c010390940c0e0242c99003c01c0c000200005080703070240700700c980030104d0000002c00007442114400d5030b4801404000e03003401081c0103c240301c648041c070101420b000220313000103000c100c08002100e51442c45250004000d1800b00200005e00301c81c09100000814040940e01400c07105000303582c201814964505020744034802c03802500125943c0d07007014046c904103030f402564001404180145042400e4491108251044804840980d1900c4092111800b1400f580d41c0010ba0419500e0034a2850701400c60002da01d00166 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 967394937 1250 967393687 967393697
    0x7060801081b1255141b0901050409030e100e101107060503010503031e120118060b04180e150915090a1218090e0d27030201 55
    0x2ca03080c0e99441c0780300041155410121550304480c1a407421340b640c0100b0b0b0f80ca0707105509003016448824010000301c0708000f401c078a81039140c036151040044294040b000d4400c14a003404825280508100c0405d83c89401710310076090036940740812a80c010144c1125001c4d0b824510f90700300180c0c000240003239500e0304656070444e0003811349044604500c000207240d404010400d04800141c0c005a040f004582140c0075240d0a40d00c400094407188020311456414bc0c5c820022802c0052000c01c0d03030044950320300301d4241f030010602d125250b004001c0e080501034052640300282c000c2d0f09841160024808ca52130141414603042d5400901c0d400705410b42d8256071030300e003251446001440002d0421001c90000b40444c01c0c00045c7c5640c1c2c841c8070510b05803084908021648030701000990240c103551010303014000b05101d403011190000000400c0040703075089040400c130500b881c040c1c040d01c03c2e4800300a000a6058110040100700c00c00d10300c203110401c4118200e4450011610702080d40c0d020300300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 967396187 1250 967394937 967394983
    0x510053c090f25091a121602030715050114011404050402090604030209040b0612070b0906071a01080318180c0307202a030a11030705060c010605030706080108 70
    0x6039080c8840e2100c0c0640f9541c0c0c6010400010f03504050501c05848140614001518a03444850401e100d4074010140d1100c180c000103903140341d8484d00c0c00d105885d5206807810039050740c0c0ca101c041703084a10514105512040140140030f0301c0040c02c62080000d2038102c00800803040318103098440c0d8050f850240d60009030034240c03070f12007a003145c00a40d03001d00501451b2030b080c1440a002741c016280396108880785095030515040000b4940180c8940c00300d102d141c100481c0400807554065001106e20001014020101103003071090305000f8560100516031f600d400030300030412517061800e05071140317945941300e00d000c800510340070340e11001c898022640c0e520740c0d610950741d10f41c8004185400d0074420403500340348030703011651400c8101c090b60320b20001950001918005805140e0141e0143c0c0301520703c4001c41c1189035440403000e8090143d400c0152144041402680141d501418503919a00d0401c8070f420b003045414001c01c030751310380781126504207500d4a4072242c1c3c5010820800008a407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 967397437 1250 967396187 967396201
    0xe011e050c01141303030e0303100603090f02030109110111120304110402070c06050c07060504150c2306180f0d0c03050f07110f0f0d02040510053c090f 67
    0x10240f41d94100040c1148601c3c500303500c9145080303500b034800310002400c0a594403540d5000000f076034042d0b040070f591055450704000048008181d103010070b44519803081458405a1000e01c038503918035000f28140030b5681c00c2d04002601c000944804e080640d40180b41481d10511107070181e9030003a17402812400c0100301640054041e02801d40042c0079680e1b008400204079401000070500d01c200a020354a600c0c2d9644019611401684036190301510201180002e0302c2c070810416580714403880484066048140a0040003120040000740a91242c1c0c00e1049030400c05054114840340d0800030520305000c01040f64851209228020a02134030052040415004000380c034500703004109603d0301d03594607003010760b66821540400c2d409080070308041001c90404440c40c601304107010300080000c14541e400d010041038001c11103000c0414901010403203a03140c0201c4841040c1c8040300ea84407206280000031705a030002008081c0c81035161800c551510752050281d0310102c03109410049540b120 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 967398687 1250 967397437 967397441
    0x140906030708010204061101060501030203010e01031b080319110a051c120f09020127050d020103140a0c020f03130e070e21150408030a021c06090c0e011e050c01 71
    0x82c100e618903500100b008100e40e58021040c4a100c01d030b0b03074004d0182941d0744005504070f2100b0300a0b40352000304980103001180c400380404ca100c02c50ba00043c1c01e2035994011682c00d6410000300485003590107181c001c81268800300156540c441d01c00681070f2881c59644081d038030414440404d44944900f8442e40400303010b080d07182c2d049518582d09000400da444205002012003003c204e010940e10710b541c1d088001844080000741081183c0c0042d400d040404020060300180030881c100b544907a1a0328820582c0307185d40d03001e11810310020900012404c80a8240758440c02070362903c2d40b040c0045401c0c041c0850314902214203103111060151034514040300c2e00d421123099940c114201c40311011000c6040c1500303034240d03103150003a22844500c1d08071000561809540181034a81c0c1400072641e1901580d001b01103401510344600181c136020030000040d642d45070b0001101d0fa565035400c0851035017019080b101c100091811466804a43d206401e1003119800d40e08104031001c1440509080c0075 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 967399937 1250 967398687 967398689
    0x10228091203020312010b090a14030102090a09061a1c0f091406040516030c052701030f0201030c0806010c11151c0606030e030304060525080f09071409060307 70
    0x1078195800100c26040180d40c0f54041202e4980e6141c0c440000a4083c1d1000e09039461504010100c5010360703d0310312101224010b11407200e42c995800c0000c0c0109036101c1c1d9103c001040340381c0e0003040f4949072103100108440305120003100328208101c44032641c550b41c0c4c0c3c424030145c91070500140b0040740a80740c60040c035115200a1008008883c4561003080c0001e1103481684540b04841e15010511750080107140c6511000b40503040d510070502003441c10003201c8841003040818203901c045280c40103103c0c208280d0041d145c2c50700606c542c80039940c2c54000c20030241d04504100d9014200440003c00d110068000039110207255500d4007400d82d40c28165030981000345903015190080e00e00c240344040c4044000d01000c80c58143d00150407800307070050081803032840020b541180c0d0b0710b4964101a000042400a05101519030383c5450201d50410b511200881c1e6100307512840c1141403440140000b900b010b400c0e030300924041003010702c00030703803004090002c1d614101c05858800c0031a180c0006 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 967401187 1250 967399937 967399949
    0x1211030604172a0102090901090c020705130b0a170708030306090406091505090706180e180106051905041a0312070602130e1012030203032814010501030b0301022809 73
    0xf200744402c0040c2015005448005000c0700d241a644c0d90f107006031401c0721103010100d0b0140e00008070402c100d1a00c01c9000c406000d014402140800450300003071001d031140d8204a08000e010040f030758078114104074090250141c00000c40c50741c2440700c005840400300030402807600e51500c09000400c55651180c0303070102c42420082c0150f04010007425110405030286078005031003c49005500c91440000c4012a41c100f000381d000f98070380f40e00710f80380d8242c031440582e00c47d07407515400034007600c03000d50050808103007500c000b203142e09110400c41034800f10b0542d4082010801c1c03940c2102d40e004076860182c41410420603688445d2450220060700070100594101003603820006141c24040b04510310440b8002640d8080d19190501071204901c60000500140d000380300080451154080f050001e0300d0481c040144103200490f5001030340c1e030b00a160754030072007134800402c2556090300591045400842c025410301c655100c224200040c80c00480b00400030150300d0020003800f42c0700701806802 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 967402437 1250 967401187 967401247
    0xd120c0c0506010e0910060b0f070515070302030a06050d051b0102100912030507080c03011e1203121b02030d15050303040e070e0a030521040807121103060417 70
    0xc0d4859142804000c210350300c680d91b000f222810051800719200c0c100551f404441c100b400d0440003c841030311900084003c6a46224100c21b0194002400d5603071072080c5080e43d4096a02d20703002110f20140c03000382d0b0044c0d01030006d00000364000754021507039001c80ba84d18404102d200525400403403402107212610b25107103140542880a0102503c0c00950b21503550f00e050259844c2c540c4115020030702100e1036040080240018440340f10b080340c94031200c0840f5864002940d0f11040c4003d0030360b60004c030460100d082110200c0c2140503e000c1d400340c0400914224001c594420700282d140d12811194280f05961a0b9402440c1408001140050007010701282d49803515010710100f101e0064828401140ca80400f0a0b000d2803c541d001042c1c0340e100c2c0c040c1c10f030841c11480001c29038036402c035000507550043c800818005010024203000b0025189003690700c11050400d0341c070140e03100060307074025041401008041109080707154070100b000701100e40d4400c40480c0076103000714410603842c5460 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 967403687 1250 967402437 967402439
    0x60a051f031a0d060608060603060103020105040312051b060a0c1b0b0c0d06030b04051b1c230c0114030103050606010807050c0106140909010b032a120f07080d120c0c050601 76
    0x119a1017078003981c540104a904c0364031010105070707a620742484024005030b000c00083c00010007100c0c07001800c1500e030400c10309001c1404510a048a4020b030862074a5111504212000d4130b5401100e0f44c0c1c060a051030001800a40c8554020007180349001d480c1e0020240402c03d482c018408455002030411010094240c491070807031031301c100641d003e40b103d01c60700c203040c4154400c1d580c590090b004010541051610004141940d030780740c0c07000c01d8555410302c50f9001c08004100c03149021000f014009480e000c010307440050301500202502c107901040070300050000650020302290400400d090610456450180494540c400d69910110039400d19000117005081c508911480450460b111840c5a456501403802c0f6840e042030039038154800c2c0d00f100c44081c060084d481502038000340c80c0590518040210320307800e40c000c0181ca600e521106032003030105401d101240150404101418440c140b20340d0040c80c811742d4840c42242990789602d90705549000c1e1704000c29450303200003664425 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 967404937 1250 967403687 967403693
    0x302190905280e0c130e06011205090102070f050102030105100302031003171e1903090b07080a0b120d03050f040b04020f1f0f0f0306060813020406030206070605060a051f031a0d 78
    0x83c0e0440301c401070815005c0040820701e00041c245e031b144100d006a50f1000c02880080e410710103014081c010842c195801c0200c2c10200301d9800e5a0340390709003d200090303980d5143c001030020311805d41029404051042c028031a45054800c442c1e41140e820000342c03625401c4503c2c802c185445100b80c200d049190350f1043d51610418240a040d01aa290103c1d0462030310068054055490303900c4028812804200001c000e117004a910540000001c10006044c1043d44045850035a210001e42c00300c0d480b400184107881c0d4140607140d40b04a41550001c0141425a114041c40d000600700030300c00c600d0640d84070f025442e1910b01c0100c41d030511808040340800480054141d80405441d000000c4180b040e000499000c1c2c06014211415035481c0002c03552110100908200380020881c0d00940318000000988c3c0d13510080c4c403d89004020014050905104020000c1402d0340214002c80400c14025001003159160045082e04c508000c10001203401c004050410300305c900aa00003001e948190034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 967406187 1250 967404937 967404961
    0x5060705010c020105010f270204090609020903100e06070828090c090515061608030c0a110d0801120311010501080f0115050d0f06110a0302190905280e 67
    0x407015190020852a43c9519003014640c400c0d0107490b4234545030011607144074115507034680c039800407200010b0030305032221640c0c1c0c10b55920f07074400400280c01064408881c9000d1241c014080518207040008a40c6038400750307203401c0e005100038140004040041d80c031524680c0c0c26021044400c000d001d041988039404030017001843d030300341e413203822109020900b0000d07481214014002c8148911070714624008020b01c6601520b01038000d02d2004918000150300600910b0144a001038016221302030610000c0040c042c00390000381c568025045901c0080d0450701c0c45043d2804203400012509a9080595010141100c080e40541c60700300001041c5d080817601c01d42c0703141448000d211056114810043c0382940e80141c0b81d0050b070500c0058001501100b03c076680e184942400b0401d060107c20589098000d035140101098000584110440480c0300c002c4940e45e4074140702410509190100b01310f02d000102c980545401d25181c600800c24949001000b41003444020840b480c1103042c0441c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 967407437 1250 967406187 967406201
    0xa1b1b081201090e1b0d02030a0605012403150501031a030d09210c05101205090a03171b0c01091403090f010c03020a0f14010f0603050c03031c050606040506070501 72
    0x5003d51030980343c450b10b008040764200e08080400c900441c10034040302048090701c001c61040f03074144107201e04203000545a00400e0b000f80030380701619070350b54030140a03611a80141411201094034102c0041000b202000d00380096802c01e1800003180742c0c484081408100c50303000c00903414030074400c00303192240e40002c44800b910ba8500c2000c02c0e0000c001c20124a0343c148a000600070742040c00c0601090600140500d40d08010707190204040c210106940300301e950541f82800e45800007080c2d04141904005025400c0b0f925005440740c51810700d680308647c05010101011460780060052800c0b107094200c07103d51504440c1080b107160300a440355599074000000b090041c0381d00c03070344401c403036004090240c800c540580250002607820350b51001000c48208048648125030005400e0181091007000e101501c4104000f50003415820494a00050040301d00d01c0f945c010028801950a0b43d032004103401034000003c0703a0340d11500c001581c42c2c00382e500b005800040c0428084244101500036036 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 967408687 1250 967407437 967407449
    0x80703061805012a11060a0203090a12020a0308070c1a101a070209010905010b030c07020402071403030717010f03030c020a03023613080922090b0a1b1b081201 70
    0x41c00e82c3c1c0054030a840f41202c5607840c000540042c0c0000e10300c6087c5070019031340202940281d45801140b5643c5400f43d00b15880c0c800d00513070145112000f010780000b4071941200c80e600300600c5070402c650390758603240b03a2400d0580c03c01f01c800020400c081c01c091225001b61400605d080442207400c08885d18603003000f20140d208680880001810003c6841843e0681d16803042c01440c41d6214210007c0319408000200d03000f40c1e0070890b00010615003140c801400b0f548002441d81c3e41484da0004081d0546800c40010058200c40104549003034101e41c1e80807240d150504003135649032400010607000703161f80080e402440b0b40807186120b812581d8000d03075030758031914100600d0100f10800312190108440017400c0184e03c04048d4003151917100500708031000140080242a08103500b1021541c200d400d4031102c80d21291000c0800075080d640580c0a80384070b1081144480c0c1e1140300054404450b1000c0a200da022a4042446070201c418161039400041d143d030364101c820482c11045200f40300364 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 967409937 1250 967408687 967408751
    0xd020c03010506060c120f041d0f09010606020601140102071d01051309022b020307180b041b0f09120804050a0e0628260706080108070306180501 64
    0x1040f904c0c082c025100c2030000d100081c110300450b03501104082d80402c000d041081d03000e2000103545c1032000001004000e040c0b00c051942d00740b141c00c0c0c1c003004a016001c0d01042c0d040582c01d00021b9400540c0a04441b1080d482c0c0382444103401c010b0b030502440c0d4010007040369000340ba62000b46510520b6074102c603801d480d207008020120038944122055203000030341c0005c1c008004d0036030410f2000c400c040d1828071400d40c01c1c8800560300003032804190758004211511200310105005c6051721958080711001e581c24000c0000701c0d14141c0c1902044441c10b03041c000701c11b08054099204013921009800703201d000703255800280c204040150058800d1500c601c5820308003094212919140b203006101c003030508805688480070302000a0300c20521009803100c5071000180303640004038210a1803032507040b002040c0700b0b950310ba80d0a0540e5900540284400000100410000000c0c0841241c1e0851000111a04203000c90302800c030300e10901a095608180d00f0b05216500618000d55a504203004 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 967411187 1250 967409937 967409941
    0xc05010e0c0f090c0f07141605010e150f0c0106120b010e280b010e0a0e10050d050607030c020c22051005060d020f07021203040905090102030c030403200d020c030105 73
    0x10000840030844d0a00c240711001c0c0700810090894001500840b4030030007980c0e10601c074885810389042540784a075250408200010442560000c1704200303c0b04003610303031b004914070900100100c1c0c410031300280d800007000545028141402c0d030100d0080c01c06600000550615410314407483c0c0e200b0b00842044032800030208060001210b0380100d000002e01814100d0a03410383c0e080300078000d0703c60940c10300002e0384004d034007a0b0b20200c00001500d802c540d84a02818020390404050300580c0009000302c03036a43d101800b180000600c1c2d0f50041c071610f00402c0440010004a040c581a03400480e00110304002060f01c1d105040030012b42c07554100000c01499036594540380d5510f2062040e55040001082005510b540d55001041e218211158070380c5030601a9000c200c4404800c1c51044c00341c2c0021a0620050700710307008968101c10848001d50440c2040706003007805200203000202804144007009560030800d5660511450060781070300c024500350400a034840c04143c005a100e9460540 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 967412437 1250 967411187 967411189
    0x60c0f12120c031e0106031e050708180c100e121b1905030304030503040e0703090201120e1f0501150206010b030103030f090b0a02101a090411010c05010e0c0f 70
    0x6540201d500c40c80100d2040e00d80307490b60201e50b40b010704104500c01803074081100d0b80c03c502240c5402070500e42e0300090b07603200d0443d40740c0040c40c843d610041024203110a001d8a140d110300000c4e00100305241000c1c560141540b0704c2d103004210070425410990319511117441070740204001e240010292000501c48415000b016114003907288040c10640c285180400b950811344030700e411200011444c4500b040e101d5000074075640103a4000c6441c3e07400007409100e1403086001158100e0f042d4182402418120b0340040d0483d0726581007c50000e81e902c0505051103c10042502c8a032400e21388018174140c03500a2138003601090103031090756010180020704417440010614122255040305a096909564040760b060340101090b0302003094020340481c0916180d001440383c4040380d00200a5000800f80d110180c13220070f0030007192980c41c810300d182d80e80c0b035003c02654450782c0401e02d944000f10301c10050b02d51056401c0081c4c0349620b08210f1404030f601c0092250030070141280c1c14079025240b50 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 967413687 1250 967412437 967412473
    0x3060619031517070b030705040f03111f210209040c0305100b0a050318160806040c0909083a090515090a03080702100504110a0b0a020d0518060c0f 65
    0x41c0703c0300781642c4200320030801d040d41c413409982c1140503490400d1030281c1c1da9543c0c180d11215a041603030107401901999190b071404840840a0714960310030301c1803403e690407015240b0042c17a1405015500c40352144c140e908090b604540c4a0100200b04025a14103241d0040062404641c0f080000310840404503450030b5074025600d21200c03503500d091540c0d0700c8605a09071ba000c8a103080c400c0741f2500290907130090a107070040e005441810021300c0d59241c076060100b00040c0c503510029110703103000559404a541c400031030301c050720a41c3d08800112603009001d0b101008245035074440d001e4601d000540e16804d030b04000fa12a01590850301c1d25003046802200e00401650000b50380c1c0d0101d80414000b07405a8446039004400d401903800300c00328400b4041c25110304640c11100320900e0f1781c5000e50b0f4505242458040d00701310054078100382114201956030720f1123808410900c5408031b40c202c170012200142c41c20564010305101e884203500000d081c0d0b0b0360107441040810340100700c14401141100c07 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 967414937 1250 967413687 967413719
    0x1b1410110a03061437080d020705040c140a090f060306050312030601081308040b0a03050103060c0207030309270c02010c2604110102030c1618091106030606190315 72
    0x1800c45450072035089080d00c422178410b0402c064107103100c42502000e40785c040208020990100603028501c0582002424100e2540219106038a800038448810740d2180e03807007100041e004a06955010350900c150b485101ca94071400d000400c010011401c0d40d0326030040e00031150142e0403a11014140c02d0403071000d000031245540090310001c0080d03174149042241d071900c54014844103140c0360300d030b0385101e07401d921507041180440c3c0c03144010420052140b24031402c4030014405840301906540e03009040510340d00c01e101c1000856201c0319001201c2c20341d00c4c00c16101c070301810405080c2d404d802a01904503408000d021031100030120911a0003062454440c1e0341040c014040ca80c3c0e1607982c11546a0030401040c1144018002d011000404100604004c1040410b0403609480d180f01140c82610700020316003203504081407400001c1c0a44404882c0c0d510840b1100e880b0780e6000085801d81c024004111ba0061422000000c190b4040d801901401c00d05100c441490b070315800c07130002020003 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 967416187 1250 967414937 967414939
    0x12a0f0207050f0d020d0b280c02060c03071b15111804020f04120c090c050a080609060d05060a0c081005030319211a011b1410110a030614 61
    0x1008043d5a6103003840290011520041c001d030015056038440c00e884850850714881210300f2504405552504105041d080b0f482050061107803455201d4020b4035a04040e2000e82800c0f408404a45202c1c00780110025003594000d0400010040b424085441641d1491418065150002203450444100c04454011001c3c82c0c0c1c4144840701541400300030350010800301c8980b582440b020075618041d010900700f01e405055580141410619a1003c8601000d450b005000d8200480004113030031a5001e980450700321503000080c7e079800d012814000100d074000300540900c008201105a46900c550f030310070245d80d41c442441d0350341560708044003c2e5000e2250b05502c1032118111052210321500440c10661130200407451902640c14001e6038205001c604240e100c40700d15113007442c2108480301e004800d290481c0ca02e14aa030614003043e070720550140810114425050170180c003003154910110540c3c0302080210408800d22045130003000d040400070341007a00c000740800c1811000042c040c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 967417437 1250 967416187 967416199
    0x60f03020603011806050a06210c09140a2c090303040b042406080a0203060a020f03040210050c03121501170703020714060703021c111902012a0f020705 67
    0x10804d040000d00c0b2011054090701d03591150343c0818142c8501207842c0080006450b112101d1200c113007020500342e00c0502040c840d0345809004427809501c0610a0221407440124500000c03c01d03010545c548510341041200302824180c40582031507004000070f1401c40f4454484003911400000c98985c401070384c018080a04110224001c0b40300e02c0c80424204d403400d81c001c00d1801225075114191085030340041c1d0b00d80c0280701100c007135060900c1790690000c5618406c614045030304862038060b000103480031f400340700881354031400a8003c00480705403035101421a600c1d216aa24030f0015407800f02e07900b9030501c2601554003810350041850040c6840c0800c2411078940e20103404400a4103c1402503400058451203081031220502c070349401094195030143c0d0f90007132b0350398400d407007100c442e4180140780c0fa1003400407006043da41992400450021800c0341d050000c0e404034007504080b4400090100c215032030307002c411200703546e001c5168519150742150700c0044906a0701c0784e10b03920885030054 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 967418687 1250 967417437 967417439
    0x60303020c0913050a03091706060307060e0d082b05071709030708041d010b2701050408031602030d05070f11041103010906030203011b0f0c05010e030c03070204060f0302060301 78
    0x840c0501840341d001400300d00140f81102103843d102e141421040040c0c002ca140c00d1800c1c0a41043c0c182d2401a0002c0c40b40140000e0801c1000b00b9501e00061045104001050502e08141d598003195502d6090300484d034030381c07a070781d426004038400001425003c2a40520400034030200c516070191500c1001c80d9190003050300c002d0800c82c140300303100810414183c003040001a000403034800181c07010308112500314100d0000b8071000c1c402d111040e0022210f0941c144207001720568255070549805291040c540fa0000c020740040c0d40310b000d240c21840f050700003c00c01c1c00a0045402d6480903440c021411503000e40d02c1d80200b03a96500c210341c0064030000802e00e0b5100441c104400c100002e480c05000012141d500343d101544980003078020140f05a202c9104000798a024003c070b41a11000100300f0f80c10400403d0041c00000d1f0448030441800401c1b07481e081840400e44c8411041030300882560356032582c3c1d21101c1c1d144e601c9048100c0c8030300d1804401141020142c070780c0c030301580d9004d00124616 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 967419937 1250 967418687 967418689
    0x317060d081b01020d020c010605031605030703030e0d1a040201031d0c04090807022805030714041a030105091e0105070203070f11041a0945010212100603060303020c 73
    0x1118040703002d0039259000c12060039000c4042c4024100c0344051000003501c64140010907080c2095100c0100d00000103210502c0590b501040007003c81c4e0345418011502c02c0302801040d0300a1101401600988020b140f4068410054041c58030640c800d0382c0800044038014012440c51b01c09581665199022000d040c0903410140d01401d40203005441c02800c0c10304650005841c1c46c3d25000d2954420310b42c1d44140514a01905004090403044026100450904a101d0340d0050310040f00c0303202e603840d2104210181640d00c407119604401500070300084ca41300a910b56101d800c061205d0700c0c860f05944104a0642c18420385011b2811079020b54070306006500c3c1e244043e500011b003522854165507040c0300507038891240381c4004906415405011050030200f0160010080c103a00d4a480441003074901c0703201c69201e0001c041c022104644d135003440455840500c5842c8549644290300c00542c00101e0150180000d10400d8074064514941d51140021400d95103030b8440200560b02206c0c08601e1 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 967421187 1250 967419937 967419967
    0x181202152203051c0b0102060a0207030c1e05010e010209030d0201091a0403180608150409050a031803080409061712030f0a0207150903081005060f0a0e0a030317060d08 74
    0x24020714040c1d051190203814418048900b02001300c1c6103a0700c00b80c02c0e100b56018424030754083c80c4107004504040d40c644010342a00c6d40c258005040c2c3c00207901c0b4036030401d80300340c0e1504490f030050000c00c007201c00d215446000350300c070390062842407181e2400d2840d0740d0300c14000c0c619001c2c0e00603c00f4151010312500f601034071700041c0c0704030180300000c0292100f040c8107001c0b2000034a43ca6544501070308007107100100311f103588a060350143e420901c1c2100420030000d040014aa072602c0c0442840498a404d1001491140c10080a6960000300040c1213041a001030302507078010601c0860b01800401025a01c61008100b0b00d154102440000c03984201051216445800d030340d800f41c82d11040c1c4d074443ca09022410b1003409625a0758180341c0905034010007103644902441000040717507040000042107809901101c020381d100000b0f01c6c1c00018402c00542c0c0880a014001c0c0340e04076103e1402406012045464030034440140c00007030842e24080c18600c2110350458941d916000f8072004c1400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 967422437 1250 967421187 967421251
    0x80a0201020c12040905010506090619120e010e0c06040326040905010312030b090907090b0628031109010f0c062d0e0a03020316050118120215 63
    0x41955428441c07074141e0001070002e1442075580d0403025588600b881ca082040380c0040c2c0045000d04014884042692140412140442541c1c0070300d00c02e401f45098100c5604082c48143d0040034200282d410504034150000c45038102c0010680740130140b00014060507001d548005014824142c48001c40c2401003560b20701c02d08030707090003103283c552200e00c101c3c00c1c0c61003030348226951004e030340004514135818410220041021101500d81e414a40c00d402e58904040c002c00040590b038541011aaa88141c02c80340e190141200c400041c40795400454500f00aa8844401080c03c050041d80000343c5202144c2a441d4140c40b8120800c085020444280843c4a1704450156843e010544492851003025105800f540e12140010848540c110103480794041158080e521407030080d00000d8012040e600440080c42017012079007031504009003d0203c1071000d01c3c424030510445001c0c0040c0782110200402c9640032274007459081516014411130440396a00da41451401400c90f200391040d00d11 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 967423687 1250 967422437 967422457
    0x607120207080d080604150b0406030b1f0908120a080103080d090501110a1709060103082104150c08070915051201080c0901080a08030a05040327210f08 67
    0x580ea9038a59418610f401c843c3c440c0000840d0800c010080c640c50726000d00c5a0703580003080382e480340c07900e4501c41ea080c502a034080c890034140c65102220064076102c07030344d0700c80860042150b0002600307200301030108a4103014140c41406800e142002c20455201190f94081780c5588818103a86117444124440d000010540d650a481d2000580814004d0160402010510407283c0c0d40f0b0200c000d0107131000300020403410212801d04108003110303002040ba507046135000040503541c1e00f00d40b507680b0140118980d454010310750410a01090294076002c00030801d460210400280d00706070425268500c1c11204100060f68016050000015183c8403a1000c081800c050381005075191402e05600d8098100e0600c0e903004204255441c61701f0305499004064481c00b0300700203102515010554800140f85110f2141c070380c4045010144182c0d01c01141c88a80f170304c840d500c8080a800305000030385901c074015182c210f451400030074001903018040c10943c0000101d4108189549011158000403c02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 967424937 1250 967423687 967423693
    0x1081f14040f050711160e010527070c0c0f0b0a1d0d08030f010b0301081c0e0913111e040e0a12020604032a080c01091502040e130206071202 62
    0x500b6a081190003918041c105a88031114184105004640b0308042401c2c1c2ca0110001007608002c140103644101e81510000c1d503440d5484c9520301d90704446030007525003422581d40c0e174200300304000381d1080e40001c1c65071080302d10700112542e5185454a1021500804c20510342c00c105901050b4040e10451640c0c002074040742103866203840025110a0758441c06443c1500004100012072240c01c0702c503800340081c40c41817819075050a80d200d60b141c0032400003900c0050340c220410700c0b46001d2072064440040c0106020b6944c6400340c4520034503004c20504031019006541013806900c6c2c08003c0e0041e4240d0300641d400d10410040030800685121781d0352081502400200801240c1c0708200c1092001107034000700b05d20b0410789001850a0005402660788580307400d034044205251800c1c02000f182c12540644d1038507244900c680c010701c0660b074000d02841c0b8400800400c21000d8001e40112009141038443c3c0787e03a51b0109030301010080c0343c0258000e10401103080002e02081031010002041d00c12 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 967426187 1250 967424937 967424951
    0x1a090d08070806011211090906030601060c021327050c22110c0303160906090e010b0f0904060906050103060506041d0405030415020115080a020108010306020d02130b0901081f1404 79
    0x9030801c03581c1b500d0340b824600b140010364074220700b48400115001035003a4000d141c01d40c5081c2c00241243d1303c0b80802841040d8502d2951a11042c54002e401c200a41c00c000c400d426003071121200085c07035880d0003100c40d4040d8645103422407070b02e0040e0768040b11510b96491604000c410b031141c000c151580c5100c0490fa414000c1c404440010005144903c400040d088203003c4411401b40c881011035004404001d034910701804050302500200c0e04451450440b90f03105c60000c800c9070342a01802400760b4001c0e15042002544550316040842255002e0720304000140d140c00a01035248903500401d240c18501845001c2e408081c0049940d1250244080c0e83c02c1507204c0080c400341446a100d0752005030744a691010307604801c612000000c02040c4000e090401e01e582c006005150140310290500e5400f0400e11244203442d01250240700f0b51720080343c6d100d500e90650100507000f40b0052800900c1c0303a40011040324030704496941040012280180c85031400301621504c0d600100c506400c0b686a5007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 967427437 1250 967426187 967426217
    0x1060e01140706060f051905042307021c030b0306060f01090b0f0c190203061501030e03040b0d05060405060d0f02150706020d110a09090905191a090d0807080601 71
    0x1c09440158441c00300440c01d286050101030650002c0d0300320903c5584100b945407802d51076042d50500300d8200351408903884000092140380e01c420081c42c0b0010700885000c21a8250f40480c08615a00d15840341b44c2c1c0c85101006c0c2202240e0000c000343d80c260b8080008a10355150842059040000c1450080c040b140c581d030200b0895000540e9035a8500c901046420000c101172101c0284150303100c0394003100701099000681d80c0c0b0000380840742d1400c00c1100b04501648650802c075440300301981101d030b07500c0e43c0c0c1090740400d600008882c1501e0345080c0c00711703005140c07500a243c06010024010400081a62510800150005400c0340e12246d80340c40000c0381688075020b403403414000c5c40016115181a103114042c0c50394525040c01030745c0100002000d5640211800041d03a441040004082c052440d1803850607510070320340c107110303001c200713140c010411500c100000002d44040c1d900040e032500b100303880d600c6214062032030105011800142131030344512800359000405241c408000480d1074 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 967428687 1250 967427437 967427477
    0xd110312040f03030e1020010b0307120606080c09010b0d0b09011403060f040b16030b04090501150b0301030317060607060e061e060d0605130c091406100801060e01 72
    0x40e014429900d0b0a440030018541c100d001079100050075603a03002d43c5c1111070002048194080b451005c0700010604005800b04258445644110040c0445034001e89800100707440000640781102c0c05410031202240c41100031501e44038a40000d400c2d110940d080c81803202c1150410355083d0100d80e921800100d455a584901c50300a0a81101c40b885012140c1c06040c01d00c0c4004015902140c505020b100004540d01031080e4840800700d45c3d41c1390b035140d00900310050818603a00caa8005d0a005902080c0329040d400000c414801c00c051042c0181d680420140900003440080d002c100400040001c0440322032009a00c900700130125490101c0315a98001110b50b10080c42410354000010442e2441d41240703086400c0f014086141001e2801c0000110111a05640141015259804134231a4050381e0001004294020b071074440c51780d00d910b14003004240c0c105da170904580c10100420710a0812010f01020080d15564000700c40c0c3c2414429602066250201410010340e40d044010080c900 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 967429937 1250 967428687 967428689
    0xf060f0c01060e10080c0f2101140a05280b010903050319020c030a4d0103060b070b0f10181a01050c0a0f08090916020f0c0d11031204 59
    0x80c0031840203070800c0310350b04640c03030180c0d04805e209a026400e84c0c000b075980c050b882e030005c0608543c120380072064901841082d003181d0740e140c035a42d800d000307511480c03052030280b040c1f0030000d403201080a503450391000641007103a080c3c10184405548800b80c41c507941904170025409043c100b0102d0b60703940c2e0f40c031030740345a120813180c040020954150070710141c0e0500800c800300c2002c90003014003070825155890402074003040c40504191221041c002e0b01c49039604480000780328012010701c41c1c400301e03000c1c8039074214400705400240382040c0800c41024510170b641050390824104059541d45010705803c1100240c82800511740010000612a00f50001c03400120701549020a45011240c0d60404644031894868103100c4184070001d090940002e550f114640c104202c1d00d81d00c0c001d0b0902c4002481b518410640107043d0b641040f40104c1301400e4801c0348401c590840c0d803260b4081340c5564a644503141015480450705440c100860305d4828840a501d0300102541c1d503800811100b81100d900c2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 967431187 1250 967429937 967429949
    0x11120106181a030612210d18050a1b0b0702040b04110a0207080c0616080f090604090506100801030b070f022803080a060e0f070507050f16090204050f060f0c0106 71
    0x420030641c0e003085040d148091061710010800104483c00302e03019695100c03130840c1424030202d0441d1414081d07402c900c83d1010074164140b00d1080341e04002c0c0c3c407581805010345030740c3d01c6504505640c800c5d40c0022400c03122800d901c00d0801460303a0030040a841a000c4040d4095180c09100400c0c4c002c000040c403454126800402541c2c0c03403c0700701ca0030840f4080c0c0c400e1044405220303603005484020021aa407950002245644040c10030012525000e6198050340228001c01e010501040701d904c0103014503400c2380d40341044500494120b413808024000101f031400079070003050a1038010070755030f4480d000c980160340d8405c4290400e40b03103445040300d00340002003080d609207003415080301c05e0070341180d00c802d01442001c0c00c0c003500156000303001c1c0075041c942c0e0039803001810700c520420136520401c3e40502a039100040a484156440030454a51000d07d0b001d030500003403100f0b681c82190100c6001901d40040341c003a20040100300d800100c1c1041c5103842c100608100080280700c0c020290070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 967432437 1250 967431187 967431239
    0x909031106180705010e0d08131805190c0e01120605090a0b0f120a020d031103030f10051c061104081f110309061b0c010c020106091112010618 63
    0x70220baa0140b400856a1000d414072000c98400728841d240d090283d2140ba8200c085180c0d19152400081107000c4154024203030b10348482ca50146400b02d5030000f0340512088904602a1502c0d100003001b1240e407241030602040980141602c9940191082d507031400700104d00240f034503500d9000c10128142210401c0e480d9550705071810759031603e0300c5210720030001980c592100540800c1c41c00daa440040d1b0b00a0f208512490984c0c1c20140f0454006800038134a80540c0d4070f90410103030760510b8001c1aa04007098a201c000040f0721b90910f241022500d400e482030500c52041c0b00d403102c17401481c1c00d005691000c1c40c00c10000c10498000c0000c041c41c06001d400c40076005051640b0001110f4000340c08143e040c03410014400c01d100b001822503003001c100a51240f0301d2050413040e80c00381c070078005008190350034039114100c0242c042d07120f0022101c42040a01540d040b4402002c114800c801c2550403040d0000700520080b40b03c0c032500944900101100c40e0360980303544580c0000b132601d10081190300707 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 967433687 1250 967432437 967432471
    0x3050703060615051605030d111e19110a0203011b0e010302041410030b1f021002070b1b090904110111060103050601231c0218010509010909031106 65
    0x6441490010002801080c11680c4003d0b8010f009210f00164084800d6440310301e602400b40038002c071205045060402c1100c0d0003030210902064101c03118403107108140001900e40000d1803400c80321128054112180540c51400707054640d100c1101681d06244a034000300c0b00181c909104141e10101c1d4034031440520049500c000b00b04a1100d40300c0340c109401400304001c0001580c06041c180c074400c0390500a19540080201d00038207085541c20346c401b01c200312490444503551041a075000c0c2603400c0d00c803014111000d0f103090384582800100302e894840d0006c0d103074118896891250300b8030688034529010b50000081c02c00b0a045e10113403074556100c0400c140341d6070481051880000d05502400c441d62440d1640e9071104014452110000300c003901404d18201909500241c1d004020000c218841d808045010380c50000743c4c0881c040c42020441c040c200d658001403904880d80102240000e070300b010302e81405009030a0f012418091070803868140745e00d00b444402e2154208503500050301c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 967434937 1250 967433687 967433693
    0x22409060a020f0d02070614040804050102010b19171c080709060c02030d08060d0c03060e0c1c081c0c0806030709020f0f07260306030705041e050c090a03050703 71
    0x2000001d441c28000c284100040080f00300044182c8508440c8080010303102e0415081c00800791003851020569550940100300070454590050410354100780d00800c0050404010b0002040d0229a00c113000340e26a00700300401d500e106a249448104602521440498981114000401aa15000883c00b05820019010390000c14a802480540780c0b024101c01030f07801080e2210f10034207451081240c0140000c0c0292074150005011a5006402d402803682c0c0c1d090400050103910782c500d4141c0240c45000d1940c0c5000c45100f4001c172180f124449120180b6a101c65040d880030148880e0841c10040982d0001c020b44501c00c449140c070b48034003e00d8270b808402c140c20404180c015a03042841802041700c00340800054800841c1003c0b4100d54440190410651110010305101a81c1711070302c124101c1a0f88000245010302c0c0180c0c110f80c51507031158204020b480401c40807040b1042e0f04005010913920a40045402c08071003030301145403101c0440450814511a082942c880d844041c0410030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 967436187 1250 967434937 967434943
    0x20409050c120a03230d05072115060804050d1d06070f1103070b12060303040b040315050c0712051b071511070605041203090b070303050603012019022409 68
    0x10b607900140e42c10120300c840c1c4020b150311b018095001810a6503840080e40b038600642c010850b5000e00d80ea4541844105100c6902404011610510406895000140c1c0394024000c80d40125445000b904e00420301d80c40444600441d503c01651604550440d25529151030303000f06600c901034003074099400c2c1c290500001508006a510740640d00c00107041103a00c28038400d8550f04400c0700303003080042e110140000c4c91360242d60451491403800040020420185000b190031194142c5414485036903800005a414010311002400448203130344950790a620400040052200b141c83d126000c0c0c0032804503074944036064111102c4c54000c40c0c03032542503e401c280d00d802d45d800010000e14a007802c1c014014458042c0d4415980c034070003090020000c140c000d1100c00c002c0c121038407520740c8440340344c1001800360400b65001030195103804500d00301180c48109004030358040c1c011030741c81e00c0c10454070490f12440d0203691700114000c1c1c40c1c07200310b8101e4000c20034000d0165a840e444d0f0780e0410300c40d0681 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 967437437 1250 967436187 967436207
    0x112209090215031515070b131121060a020a110c1008071b080a021203130209100305030c0703030306090504030c20060c030711030a0537050703050106140a03020409050c120a03 77
    0x7580c2002000c052300003040385200381035100058039030708040e0925000700402410b03004c01c1c4101c207004d00000c201e083c4065901030030318078641c0c2c0d13210b191480b20840010b0b141e1a022a800f504102140c120180e0103028001d1960091603524080300c82d4030624520282c4080041c000302d41c0344000064100707406604024208900030401c1801d8074601f005280302c1d4041c0b400103c004e01850b02c4500080241c14066542c10041d600201500c0e0f5801d08400020f03295465404200d01003480c0082c04101c91140344a038510955040e2507421001d00c131525803805140c40307210f003400002d2401d01c40c401c40da11a07001500f02c443c599002161a030301c061610360b107142d0078690300074000d5104401200100c0e0000815080e0f00041107908902c005402c0d0b0103580003d214800300c039074403480788003270010810005840e01c203c90040c0001c119141e02d0f40102061526200f080580c000030420381440035243c2039000d52852031089080340d56200721440820342000080c03e200f216500480f000c01d082c0354100300310382 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 967438687 1250 967437437 967437451
    0x7050f070c0f0f0b030406110c0f010e0d03060602060f0a060b2106030d0203121905010b07050717030a050c07050a030308150d03080f0604112209090215031515070b 72
    0x155659041100c210014080184060325444c0c035023507054103803801c0a040f00d00301c14001040d50900465003820394040c20b5280f804d410702d0b1150035200d218242c480c0c42002c081d501542e010308410b403603c119410090030050300d40800e0b0750303a8080001e0040030103402001401610f0a010b4886400000000d501c101c00401c442d000f604060305404582e0360210445400020404031203106031142d501c1c054124047c8405410300f0780c0f0b0000013003020700c40d20014184044c400c20031141300c0c9031510000e105074030114030038001c42d50007408005d8807580940d002c0c0108580b8002200c04490342c41002414198046e40142e011a0b490001d0090010401c40070000b03d00098031114600e03909503400404a610051402c0141e2501e14089000b41e581e40d040000c036070b44d95204c1280c807804488122016280d250305050036441004000080128140c000c00410540081000c080180e074801c4102c11030748000c04800703034001c2d600d8070501155503120f4035000a40000c62003d4458403e861329480e102d0300038101c4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 967439937 1250 967438687 967438709
    0x20d09170604080f0f030106030608010507090f0b16120c17180d24290604060804140609161d15040b06030a090b0f07080c0307050f070c0f 61
    0x160418000210740360490303401242681d40d4a51081020200c0c01603d41c181050b800010001680382d0b41074000ca01641d40ea000200b081c0d45860ac0291560000c0780f10f070001c110140c04041004148035400340011007601d4801a0214415582c1c540f81890440b13034200208034207180e90400c1c081813180058100d007502d87c906160841c4180041406040c00c80000c0c4a01282c0a1201c100210b0340010340c036081614100203503201c0f01155101c0981020a601e40c0355011b204150149180080c01d16201e07600050700e05403030241081001c54001c01c00400071380f000b481d0301002040641003040b5040c8108034250103040c0001e6580451b40c0c0134505584102900001800f5212441c5d208540040c1c000000f0101120140c46038400b2a001c0d014000005a20800100420280c40020b422109102b03100344003807801c540c0c4940040041090589100d000259280000760040c1451401103030092281d003003160508901041404040d0310074041125100c56040d010010024080074400251a41501d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 967441187 1250 967439937 967439969
    0xf051602061b090f030d020114100506180409020a03141005070f031a1005040302090606072103330803091507021521070f05180f060307020d09 63
    0xd1070300c40b03030410980c0c00406500000c40069650b03a100f00d03032000210240c195100e050030080064005c24204400c1c40c1c040a0034000a50440c222040307000c01c0d40c0005042c6802d1200e030316420750780300348034410142d00036507900080009039407061200700c01144120f8140c2c024000020900382094003841210f070110b410701080c420840e80101400c4d1180b070207864000b603d940042d102c40300f010b40364201c1580000c4183d0b50440e202c0e51160041041da8004d0764032034140c3d00d5075410301100e13116400b005000100250b4010307910303084912041d40d10620130700d00401c0001144070384000104410100d401a64030902c3d20b03005805819603070100a061440c051414403c5240105103c0620803c014a80d118000303000303811959052009110342c2740200d03040c5c1e110608904481c5951400d0f1256407130742c840d4600021801072040c0804034006001e641c03250708191b1028110020310440f50500c0c0d901c01c2440b070000115072929005188140b207541d0080851440500e405040c09900c2d030004c40030f0b8101004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 967442437 1250 967441187 967441201
    0x912020c0a0f05010c03090f12110303070803040f1109010909051504150f110310051c0c0513091203020406260106110a060212010f0b0c1002090f040f05160206 70
    0x1440b401102c0d03080c2840e000e0702c5a1032030b08540d00c07010360704469844d000c0d4034408100c00c402d1420300031049110340c00382034000041d0130030560344e8010100d00810182c2c00300b0008000404100804c1242d91107071700510b01c0b4910b550001800c3d04426008003a84a0381c0310f81c030b10203110302003080a01413101c10b205140e103400c0a40314101d91190300e10b9454520740d128940d0b0704034202d6940c08030625103020441c0e1034a03401c15074100900807440e40709491141e1030b1080000c111240c004d00791000a58450958200d440c500014030001152046d864401c85a0301c5402e00301040705400030f81400040c660780141d40f203080032009000c100421a454144d00d6200004802114003264403a05656146c03e081c0c000c10861000384c1d103000b120900090103d400030400d03240034012103a0345810790300c1c0b191021545588410000c0c685028403401c0c1050755029600d140041c254a90051041e410060104942c007440100483d050701c43e010340c501223041d5144c0400080610034140343c00d5400e0b6903c00380c9680d00b8010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 967443687 1250 967442437 967442459
    0xd0503190e0705010f0c1a1b120a110909041505070509130504050708070e0106030b060c0309010f09050612040501060b090d030806030313031109150d06020f0903010912020c0a 77
    0x100540741031201c000400c0d17034440c0c025203040e120300703500c00083c544904403030505111105d030a46601d0301b1003078003071004402c00c03c480c070a4074401c08030032040c001182d0700c00005501410104820101c00002040020134540b81c54189600c40c3e4014581598401944d4141c0300071a0310040c580d40400c603050042683c02e035585408111a07000c00e450210b804c1d103440c00e020b4202101d91740f014225104010001581102046a150403107809403001c000740405002405400d02c80e25202c001c86410421201c6065030281007000107903030040c6401880903460703501181076503111352100300c0c5e04032800c1c0410040007001d0055101800481000740c1c1046005c20208081900550000342801481400a607881c0c4080084c0c44000d52401c04070b0080503580c1c2444030006030060300e10745c06940c1c540000342c0c0c2c8016140007240c400718080c0407012020a152581002034100c1c18181c84c1c25042000740c608599401d02843c017015001c0d440000d0030440e0000046e180c03603008134405004c0e404640d01000909814 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 967444937 1250 967443687 967443689
    0x30d0e0d020f0f0406170601140913170a1805150304150207081306110c1014040b0f190809060705030a090f0b070e011706210d0503190e07 61
    0x141ca0a0480350515400640801003c0d22030540140c90309500145009010b1a0300b40340500d942d0541c0d45030703603d4045800041c18452211900144410041116031484006124882c4e01070001c820b6000e55000030740b4035980c01a40c14000181307141c0f001089001a15085000905c01100d0a0349034150381f96160b20140001030000c1c04003040034200b80d4070039149070122003030b9551042d4525603400c0000781420350004280181c40004a4560000c903415500140f10038480500400c4490030310310341c5030203c80441d41c07002c2d80000340303d042c800001c4d4210310300c01a1000e1040c0b021000c2c2c07200c42c203081288090045420038820803620000b44904540c001c03035401d411402503d0482d9a954401b01e51070040c15410340010300418000f1000b4003842100001a0700441155640c6403c0c50407030801102d9104204c1780a04a82c0f00c0c14010442c45e14001e05000c180d1410488c03a80c1c0c0303804582210078202a843d44852011030790000402c8200c100510780340d00e8140b8801810401c1c00c80704581e1595501701 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 967446043 1106 967444937 967444939
    0x80714030702010806040e190c0e06010503100b09012709050c09092a0c07061404031101030b0a0812090906010207030f0b041506060e030d0e0d02 64
    0x400300445120540581d03d02d2055101c4204000007007203072503251219031140725031062803c8048444070384a54080e407805000745240c160030130001c42004010504001c802c0040003410540c00615405070381940c1c21041e1074a81c0640107850010010f104282041d03540c52144545060010842d4203680300c0e1031050045458400102100f402815113040d4083c81000000780600e0301d0307850320184002b4021402c1d213601341c0c2c034401a219034041001d20065800003902404601e8210024228040e00034601f1850145503454042c100140074424034101b43c0c84a0505100307070b6443c00c0f10b0300502190300a580302e00c060000301400d02e0388038000d401d000380e820400081c22076002080c01005c581d00829904103c011664415410400c003c20480b11030340c210001030300c81382891003100041c00043d165460f242986034105464034800c900f0140030410008841e061740d8403090290700445034 = true := by decide +kernel

theorem cover : BRFrame.Cov 967266187 967446043 := by
  have h0 := BRFrame.cov_init 967266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 967266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 967266187 ≤ n) (h2 : n < 967446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
