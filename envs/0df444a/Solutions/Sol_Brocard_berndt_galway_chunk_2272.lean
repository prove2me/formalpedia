-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2272
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:12:14.722925+00:00
-- url     : https://prove2.me/submissions/01a2d3c9-7e94-42e6-a955-0240c1b41dde

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 408453237 ≤ n < 408633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 408454487 1250 408453237 408453257
    0x316050c03060a0501090b0406050f060703021e3403030f12060608090c0105030613051f030302010204090b0f13180209040c060905030f0a030309030908150f150906040c 74
    0x2032010007840740f08010504001c245945065400c804555007034100d030340182d051010134491525440c0c4c50426240003543d03010b584001c070341822070404400404103541020844450004884001800342d8203881c0c02007040b00b40c50200d00c4102c0030101050100b050300703140c9641000440c1c00b840303041c1c0d40f024180c1000c0d120442040d081204640c0d06400682c0418044d500384903081c0c2041000e5800c52400382400b42c0b46082140004001e03940c54050494420b494400003010010366050850400e817102528803002a1246406400b0350000c0c025450310300d01d0508944ea107890030f211840203554010304001855040b00100201608150302c6050b1103031a060000790040e11070030f50091141d4000c1501d0000c0038102140180520b449601c400e00c2a44035035409601c000010580c00280350381030030009140c07081c910303086c1c501005a9108004034050081107009046202c1c0c480c6124011514250300d0301d41c0c03001d01e03058091007002080d0340c101c00d02000150075802c1c9a8800b070384210306414426854 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 408455737 1250 408454487 408454489
    0x8030709090203090a1b12150b060c0d1206030f0b0a020f041d0901150b09010c0f0501020315030613060b03010f020f040e0114060307051e040801090212010c020316050c 74
    0x1e41e0080d0380d2003e01d94003e44603071707085c0310110361103d0204002c10f02c0050f04501d01035800d4414544201d000c1d2003170810038030042c0d03210220351240c0420200541003d407140481148680c44051007000c07100496031480039804150410711540003525840b403891440c3d10055100c001085200600c05d00e0500c0c0d081002c18941ca10b518041c00003449021b00000c450704103500e0350581c0e44000740c000f240c10703810600c2c120708003c0d941c0641c800380c07120030300180e03200c00841780100c80c41d95403d44090210000d1a40369000d0010640040d403043e03603603450340c0d42800e21010034141d4450781155640c4060300c01d000c01400048a580145156401c002d0000c12108100302100040780e00c00c0088203054000028104132100d82125020300400c0701900303010a0900304804600307070f80f000a008404104000601c40d11072010200540b24980041954948076030300c441da002d00900c0141d40038ac1c842c2d503a4116040b0b4184050191141c04900d5078041c6051034102c803c12103007044070003811201400307031150b85104d07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 408456987 1250 408455737 408455741
    0x6040206030721240801020a05090d0809060f0309010c080405101d060a05041a01120b06010c060518010b060c031204050a08030403030605040e0f0703031d130204140d0f0803070909 79
    0x2840d9a502d001000134144501c0a2544000c0c59021070400c3c1d00500600c00340c2504801520148201030302c2e03040c0c541049180c0910103204411119521070004181d001d40842d403180598031403c10034000300074401900c0020b4175504000c0310700400c07561001070342041c099215044001c1820354031090042891258003d0b07414aa004c40f4041d05196490b0200410b201a03200c0700300302040e2102c04e00c0d042e0750400c0301c81d0040e00582100942685c02c103001003006a40301d5085644156080102003185040c01d4451910348031220b560b0207515800c02d04103080304e180c00000c81e605031056000135403904002460074800030350000d00a45440c00380c106114013040042d030085101f41e20940e40000e00c10308250410044030407111046442d0f51000d040c00040a07070018015043d2505810035414000748804e48040124100c0e01e101c1c1c106001a1480c1400042500540305980818803100c101c42180e40901102003200c80d000307000c40074000414000b0802400013190840d82e5450304800c0c0580365826881 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 408458237 1250 408456987 408457001
    0x1e06090d06050112020f011803030302071a1005090c0f0403060b03070305060a060501021203040b240406030f0b0c0c0312041b0e09070603020c030a0528020d030e06040206030721 78
    0x904003c03601c04c80d401c52a1084141a0b0707407100b420000040d0041d00e80030711109090703000c01014903070f002901409000c009400c88030580503441180c40b080ca054002c17181c00a4040c840c00340034980440100b440306000005981c141d04d1346602141c00d0a2860312000c019220714080a501402158004804a00140016481b031007659001084041c03400000901d452890a960f0311125000e000f4400064100c0701540d030070005040c4421400000030300b854898030300c00040990b005247c0b420000c01c1000e0940c10788400c0b4001c14241c1713000d5481d035500c0d280703520902c4220402500104507480c05140417100b85900240251b5030041000b901e0400c405507103c194020b14161110300c070401188040c20880080a0203d6140940c14025013060b41942c80c001c0c02c00f1203090100c041103540c1e10007003005402d080030706419030700d1082d044840c201075151900d9484240000f0b00b0101c60403030306600094914000c2da4003400740c501d5541c9205d0111a5160a002c0d515028192100c0705400c508807070060300 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 408459487 1250 408458237 408458249
    0x50f2502031510050105070f08030402010e0a120302070e06010f1110110c010509010c0806010f180b09030d020109050303040201030203061305040b072c150d0501180b1e06090d060501 80
    0x41c040d08084607480043c078002c0e030040b410801d0420078440014100d1558040d03043e0b0210403280c03651203520069034050310b00095260005070020f0300042040078484c803d8407c41c02a020b03074103002c0d100d18040b198007030110b40103404502d00d96100d82d060b40c4900c100a0403c04441709076512500722079018025949448601d0b21b4544021441c4a40110284034550b0800315a10003004485902c0ca4058822030b0010074403810f0107224044424814094a148000c42d0606115181120344031800154690840040b2901038410500c290a01d140144910700500d43c00800850465a5660044010350310080103141c10802044804c01d00109a00440c2e0240740714500f40009032070000c000030580342a10050842e00b542c1912603614180d01d09214900249080d01c0c40190f0340c05002e0038115911a03a480450900c0c0b410000050031607025591419243c1d03c1e207004d000340c4000b081003043c410240d0700805035031703507011140014a00c3e044004040d600c201404205440e20310b40c40b10002c6030002d901203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 408460737 1250 408459487 408459523
    0xe2703040314030a200106050916031401230a05040e100c05040b0403020d140a060c0e0916030e0106052706060a02061807121a07050f250203 62
    0x307004001c0400501d4540c410050002e6050104601000b81550100f081c0e40c200003242016041d0101d50a41055001d01400f4201c4405810700480c0007000d2546001c403038001900c0c01c510801c20240e50184103040300d00e500383d100000e084c21a000200b2040301408540c0c0b2500c0c42c000010306807605e010718040780b40c0890180441042230416102520800c100d00401c12808110a0203101220720030f03113040da0f405461450301c40e2130070301d40b143c07080340e01d00d405405500c1440c1600b02008025040b0300030380e5005580e2000292410002c0c000d12010903182c41036038080c2c0b00c480d010140c0c4250b200c448080028000881c1580d43c90000c64000c00d0445042198910003e03034001c0c14841c110412074111074140c502c1c901e0302014050017901c400d009000f03100f8180401034507070007582c2d00304032000c098040304982c000207603951b151000c069040c40e100c01506503041000581464082e106030785840d00c100d400145405411034441c20304074a2003103104108040081c2e0070001d42c0341008804908904040c038 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 408461987 1250 408460737 408460739
    0x19060507080106020309030a11150313032712022107090b0a0812070305090a09020306090a06080c010c0c08030c16080d0509131d031305011106010e270304 68
    0x300a100c610142c00c0b400555001b0004041c0ba1340f400a00320300d0840d003000004001d640c4000010b14040807050007800388a0011051040c0c242d00302490003901d601c41c1d1a00d0402090300b00c0d500a0445103104a400103100041c400c021259910303c501020703d100610100c400c00491440503403542844100c02d000e40e00c0008280840c042d03500c28a00b80741c400701c880700e149600c0c0c465801c0d620020702012051420012825001300350003142038a96a680043c455404143c071191076000075042260700a00c52140c10000c6581070310548100c00588042901a084a02003000107540c4a01c103108100c914000e640000103508a0074000f61001d0300050014050b01401285030481002007600301108642000401a03580d60b00304003140d486c4441034801250882d2120444c00003084218a03059903007544801980043c94080001c0031454008451941d0889c1c03030b0801110070450904021426030b10500050003580b000e0900650b0001c19081c032444900240c41e000b860004420844004950020074 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 408463237 1250 408461987 408462001
    0x2a0b090c030a06230c0d022803051e06030a1205090d0c0311031513030516050105010f0b0a09030206031f0e040501061d0610090f1805090a02011709190605 68
    0x220300c0300e907481e00c10001c0c02e1390505072940f0101c0d2291314004242e46a00142c81c1c13a0704c0d5081403143c403c8000c50300000c7d88e074046800001c1c0c003801085544510000100701c035008141c05c18401c81e4014100a0010314a02c8442d60b20900744888810301c1c0d805000c014000000d031030b660240c2110610303225482034415945140342c5040020010030f51a071107500040b0070b4001280034a580c813079010520203102011500035041c02d0f0390902c6a001000005200e0010950500005402860490380088c109240311503407403401004c940a00d107504c0700003900040f030030400341c5044000341d500000c036250181c990742d0302e0070705651001d02990b00500e01c4030541e402704000e01c1001e10071080242181c0ea026041d003521440038100009000b04018400c0c0e8103030b026000e0042c4200c00003400762660b004183c85880e2110b0103400100700f1800b00550150811000a290910100d4028002541a181c00409249a0340303d0071107030000070507860007445480e40c4400404601d803041d0480a014140000e007030f0030080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 408464487 1250 408463237 408463271
    0x12060f14040305032202150c0616020a0b0402040f09150b09010e04031b1506081009030f2607080402040513080301090c030b0307080106062a0b090c030a06 68
    0x8040101032199010801c00031942040880c0e5022001942180389001d45680c0360700d00d404100c001941040600da640403400104000a03e0b00503c10012506952b4030003402e0240070200421000040e00134804070707000907001c2059181c11a100400110740d103040010080700300d904000c016144000a50000e65450303500341b01e0840412000c0d4ac40b48400d41c10300c108607502e244060001800c2044440d1810300c0402e44038207890039035a002c0c461f4403082600a0140b0f01074603541c051040ba80c0949180f0726402c101920a072402c60340e15468611640030171307140030388202000a1b003054040203021854401e40c00841d001621038070240e1904901414a401032004942005012500c0c52645030460300c0428815010703281124005107002c00c0051822070114040d10b060044e5907010f20480300080761810043d0410400d0340c1040e0781d42d92040542041d248108071492042c55880d440240284020074030140c07515a110f200001103841c000c0030440883d00e80012a4000d0728180d41c4c030240c2040c403041700 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 408465737 1250 408464487 408464501
    0x32303070f0f1502130509130b0a0501140103060e060918190317060f0907030204050306011d1b0a0c021f0320120f060102010605060408150c04062712060f 68
    0xf01c002103040c1031915901010240d8070b17016aa00c40c0b9004000545080d107228198005181c1c002003a07032703860511650620207808203000380c01c09100401455192940b2911500003115400041c50069444034070600420f8400a00a04000c484209800044501c00c1180c1c00e11142c510f0701c068040c180a0400034100350070911400b41600322502402b2899841d149000101c103021221703c0025160400c068009200d1a031150780c05002e88400000d061101c0f92034101031282d0240103840680d205550b059021a82000312201d0102c00c1c0f066190302486100d1040c00170f8400341400100c071103019052600030140441c2400026204c40d16401d10440781000032207a0709201d01d0643c109034402025064001d4020440d201e1100b401c0c3c0020501e81c401d4200303500030180a098180e80d83e48440c1c0380740d20750814503210f0f11000d21040106140c1100b0100712002ca030310503568294000030004c11880d80820100056a0326081414085500001c01d40fa8032a5944600740c0003c00c65001817000c1c003a1411 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 408466987 1250 408465737 408465773
    0x232b020c0a0e0a1113090504060c0314011503090c091d0c1c150603120e0a0321030e0f0a0606090203060906090a09050111090910032303070f0f 63
    0x11010701000400a5004140d401080080e8042458010075010701014016203241151041840c000029610056172000c3e0180c0e006000501440300c6040b8190149e80c46594050184141c20004101c042d20364815258104c01910b00800d4140301c580b520403a024868120f03c01255a501c2e40c151001c2c0c0c010800a4800902d8015110210440e0b0000b00e000100a032141800009003811307004101c0300741070720400410b500303808200301c0d9103d061075120304030503066036400710740e4003d00d0750390510303001e54150304407640062005011781c12410ba50004000781c4201c1d00502d40c403180d000c040d074501480500c20030302403800108184525418a02d060340d0140e8031040070184104184401d5860b00d0034240d038000e000342c0710b40070301383c076804600c0000f03001e44c03600602994a07001d4802c20720005103009000c402411036003c12241c842c40d03c01015520644001840824020090030312030040c043c0300100b40341d241c0f098074204400c3e5140c1c084030b0b00e006202151a80000401c3d901000002c41d007034243d40311 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 408468237 1250 408466987 408466999
    0x1c05030424020601061b020d0503040e04141f020a030f0e0c03240402040c02160b03010312110a120c0203072402061608040204111305090112232b020c 66
    0x102d010030151400006d9074829a084007507103900c41c1035407210064203032400d03440421669140e5858a03040352524060303c04940a484030081816100000034001c00e42c1c01248480c4120b1080c1c3d015950020f40c0010061002d15450702c544c18204042e41c4284100d0492aa0240c12076000040415040068480c41d204010b02d407100101d21a1180b608940d41c0650706582c00504400c2c00340d026850f0200400e6a020525000040459940b07441009141281d11034502007100c0158908140c6554004955007401940022a40c201056180d41e0b500d081d400c80d42004481070080b60080303428100580c0240003800ca90710b2444510161110000503d40c031641701414041c285800506480b102001c1d0780000c0001c10004a000c0d0740d1550301203c2a05281c0208554845001c81e041000b10780c14851184031f000e9900c00000c0c142400c00120100c3ca500030501c00881e202c01840c0442300c000036140100350703c5400007614030103c03004449240101d10345c111a0405001c088002d14181035011014041d00d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 408469487 1250 408468237 408468239
    0x5070c0314030c04080f0d140306310c0c020a060906021e0111040321021605060d020405030d020a17042616090c2307021c05030424020601 61
    0xa520100d89180865540403496980e1200e00c40070f030090080c0e40052546014030301e0b0444401c000000c100c481842203454020030303600c1c412006903042c00119151500b0848485948000812064240300080343c98221210005030031300254040341c400445010106101220084c02d5207405050003000b002e040c503013294094144400251a44503210515900e0b02c0c1c58485e800c0e01c51000e400401c7e46032141440071f612583d403820050442c544440300d18403584540180c01c01d60034030104209031219501d0022140040c40c1900f4001b86a100c564504d601940c01d200208242d1340c2480010b80300340d1140e0003480640007038101600d2a1031400548400000108001c210440402c80e440f0b0100070381141421400803642d021030300301403100400000c50199058042071a21130b544c029601000b1582d1040144a400c0394a40540008070700700000c0d01505000e0726006207441e00012841050f0791003c1c000320040e03030341e80305e145401c030b80c010156010301c452000788043d03144241c801001000e440102015 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 408470737 1250 408469487 408469493
    0x10b0304050307170c0615040507090f061b0c0f051003020c0c0d03020109300503010506070b281b0203090f0103110f2116080a0f091505060405070c 65
    0x60310840c4030040004c03120310600041030340c0c0b00b0700755001d2803003590656880f03151071050b60105000c1000c415120f14503010201c0c045501c038602a00c181c8034281d403038080080c00c1400c192100c5942104142600032102240c00c0050441d02500f00140b51040440c8046420541007080400c02c51a0441c2054414004042c019000040f0110759a806540c0c0c10f2040000b41800c0340584003420010705011034807621202c041425064a0481313000980602d034042000c00c030100c0340761201b803040c180e101d5420f200c182c002c21102c0850750b81046a140b1040300c045030400e038241c06c250750401480381c41a510002c0415850303503e841d401c41b601c40792000d1442c1055640c0050300000003160080e040503036401515104003105400c0303c6108200c00d030060745803445c1807941385142c035480e0000b083d0101d16001043c5010240d000ea0b000d8068a0784442c50b4075a611548140144100b1201d00261a180e602d41004038149a400c3c01d40403280110100c0e55140500c14001620340c0a40044108140d5016034008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 408471987 1250 408470737 408470743
    0x152202220819020d0c03060c021605040c0e2b0503040302010f03020a12090503040506070b06120f06040308100f140a0b13030f050c030f0d1b03091205120c0307020108010b030405 78
    0x2c19a0704984240701451141009507401c009504000c05030340c0f901301103030764441e0000341d00c0030a51080b07059504440c0c4c4807014481a60a0381c005580442c1103070300c10b08001c1c80c02c00c0c40c001a204102c42e00c1611a02d0750711409589006449007614180c00016091040d96400000c000d06040c413410b05501e4131f420b80a0041903803000344e407070781c0006030b440144108005040c41101c0080030010b00d880c2d10b8004605124142c4481511201d02c03a000e844146008514003040022141265901401c05640c80c3d480603500000000c11a48054502c0600402c03110014507a1401400c090200c40c2040820030303040c0286c16485130003004986400f8007691034241c000c1840c4509680c0d000405c3d1282041c58503205103030000310055954140204100c0d62034030000082d101c8880d0190341d4401a90014540c00c047c0c014442c004054001003034001f00380300442890030842c040d0b81c400e100300c070781c4241c0002e00c2441c16000903016620301c2d00300056000c290b41c1d000445501500305036941c0c1340345041c42d5840640d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 408473237 1250 408471987 408472033
    0xe01051501030b1f200a03050306010f090f0f06030c11030f0705070b070807020a09021303060c020a05151f05060d09030507080307091505031522022208 67
    0x104142d01e54004480d03603243e020a20811401c0a041640c04012164000d02803008085008040c2c0c0c5c0302c8a080080c80c680003500e200f405415440fa945142c031130200455120b50110800030901c0040b0500007190016544190010a10104004074880c109a401400e503407481c1501e03400c00c114840010f41014003c030440f950008485052a65412a441d019042002642c41a81a140082644404c1c801c9500003007038881d00c00c0340c22015441d00c8190300012400b0304080020b036010170700c00500000d48d00780c1c02280c1c5241980121082d1040c556200340c5404805001031901d403002c0380c1401314803103c1400f424519104025040b9410b070408000c50442e01a00602c05200c41d1a000050705240c040c00403110006d4010400541c2c0e0300d4401c2c006400701c1d01c14444d880031a0741181d1405101d80c81041034034000c08402c0ca8003020030800804002c001074885420310b502520044140c0503440d280d20051501110341d2031000640c0410302c0d000685040964440c5003260003940172241c05800f401d103414 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 408474487 1250 408473237 408473239
    0xc0f1a0a05160816110303090c030106120c090914010914160608040b060a0810050712050919060f02040f0503060709150c060f0c020309040509070f050411090d03120e010515 76
    0x101e4130031150341d4120794500d948101e00281c4e010020a21610203404999051408010b8000780a60307070f540c18510700d05c1d102c18170001d000500b84980030300170b1000303581044a0650040c0d031151600c0051480d120708450840030100c8040382c05041c02d4031750325018002944185603c0d02501030961074180003408414008000030720307454001c40001c41d0341c0d40d545620800303440c0c4541190702062441d850f0100908064a070316021038800740c1c5825515100340122841001000302130941c4d08107011408804013100300045808513140c80c5441201c01e2103101601c020428840c2c5034100d40e240100381814540003400000c10460031400901820740c941b00c809206d030045191881d07029403182406030051aa185a030b40300ea50a1502011030180d000024284a01080b0707803c00c6075855080d030701559a842403140344101a4000420445031800d94051500f0005d5050114035002c44000020031010300c0003012408074030681e4002500503c0c034442d050481010f40000c02c12420603059403e1300d2481603a0304d03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 408475737 1250 408474487 408474511
    0x2b06060203072a0e0f0a05011406030603010902041e060e04030c021504080d030e0f010b01141804152303190516090501150305040209070c0f1a0a051608 67
    0x460510f00785040a5480e00c1d05052842e080c003a1600daa446600905a0740340c1c0740d00b0309003c0440c07828445442018101d43c0601c00100440f440c11040c4a5950401445550315541e1403140d500982c07294001c4040d1014074404007481d002541542c007088820726041410101803080030800040d401207002d034516501164150b01036070302c5000c03814051165410242180c01089071100140ea0982c008042c44044102961b0742c4502c1e002c1e6060803a80740b020f400c0d000490000303200e40882034501c010001c000f5589440e0445200325004078050b20741e1852104001c01c8020810003d500d065001e80d080495000c40500708a01c0d03000c0026500c64000c548070300321020684c0740004000c41001400c00140b1201035400c170080d546e03411030008203004d1280020b41154012103c05030b51080c03060381c2c03180703500420100c0039841d54030003201c4a00914008481030391909000a022884108030740e13a01042d40c60030500c00d4a052224501515005000301e9004005e0400b2886815040344c4180d17440380300c000752 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 408476987 1250 408475737 408475763
    0x30f070e0a2a03020306010e0603070c17090a0807031a0114040b21210720060909010f0f05060c1b010531140108160e062b0606020307 59
    0x15420b8003030003500c221031880b054460041180b5406802461103180241c0b0b458112080c81d9041c404c042c8000c403001c40015014030421700014011080d03480540c01d004101a04185200c00130982c2d016880d00050140e0340044001c00030440c4900048080740941085882c00b5494403500920b105810384445216944446503c81c858859414842c032031581844403551001c520641d860700c1b03e140040003140c4100c1498210603002500e03049545c540c0d440900281281c2d9038a00c40e841c1035103544c00b101e6004008220220007640d0380541c09001c1d120b00c00010004518010400910503000c0d03101c680100b20610030920924000300d41d41000d821070080b20101c0003404001203070240f00b021141ca0450303140840345640c8a010003602c50f40d484541101c070200e00e40b82d4100a040b1500000e0309400a0400800075140804215210202240070b050070790050000700d000900581120a801c5e00c0104035040c030180300d5000102c0340f400703005045c0e000c100072810305000035180e01c100d0720050941241901 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 408478237 1250 408476987 408477011
    0x100c05070605190c0f0e04051005040c090e061905010e0d06060815151c0515010905070f0e060405011119031e0207150c06020912010b030f070e0a 64
    0x421110603591051080106107408012140349564001e80c003003490349040c0410784042e001d84a902101e009645900751a41c6201040101625000f0415010443d080c580090715894500603080c11f00380c6a11900407140c1400440440074200414091140080103c2050403000310101e00c001d8503c00e103018aaa00d8401005c1844074501c840c0051003646131060015559074041140703c004603046011004a46980c030b0035100c10b003241c00b001c990180c240c1c04101144404006d50048840c0301c0c00c02e07143d44500c04503404410f40d200340d104041c05500c3d04200600c1c01d0f448081c0314001b41150078400009000c2c0d402140b668040d80c004d05040c400840820360184004210700b5069052007130081d01600c0440c64001c181030340c04501441032541c0e074060010f100b40046400e05c01d42d8040a05490b1201c90800c00321110750b130080084c0c3e80540e0070003569030113440718001404040c44210001c1131898550050515004a03800d00500c503411521060040c620942d01154005024800104030b0446082c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 408479487 1250 408478237 408478247
    0xd0203070c120801050f0f0901211a0f01060c050717071a0d0506091311010509100c12050915070305040503070f0807090605090f0405010e0a050717070305100c 70
    0x34a01614080c80b440345031030016031024501c0d05807a0140c810711405a00741040c4000326640c1824540e00404040052280c0d548803840100c19000b12050741620201588800d00103503100e03400d952354003010008200d000c54030040610b00400c0145132100c001c00450300c0d401d03143e080502910060800144100d003c402081017050081d000484030b8112050400c81e401d20180d00024860b5001c9007400700060091030a010300d03d21441d4030542030303038800c0704583d19003032040c4a00744050b0611009214945039501c441031100700585c040e442c0d040081c032003401e0040b1169014201c110810604000a240c142c0b00c2001068040c008000c0c1d041e1166064941a1003034000c41e001036415114202000407100c0c60605044201e5002c03900361800c098440444600380c3d010f90142c16080000300740401c0c0c50030058a42e15600a0103000009408030b04101c046003003600540703040e240c0da4000303e014800c4ca801901c49400380344520000b401964619076440391284c1003a40e0316200c0a07903414015000c036001d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 408480737 1250 408479487 408479507
    0x605032e0b0d050a0c020d020d05030c12090d020c09060a0501050c0708120310060c0c2112051c050106020c060d0605060d0f050601180b0c0703050102030f061c02060d020307 76
    0x1c4000303620340d80c0d1901040c00801080794420365203403c014041c8142d84c0003107071000c1c001d46580d003d4455003070303008016a440d500107890b035121500100a101441d0345006070036801103183d940074000f400705c6410000e00e450032081c81d152042000e10180400f55031002c8659080301c20a0130310a880341c039015405418040c1a80c0494841e020307a000e0741304040301d0500198803074041016243c070381c3c581b111301c00c032102c0020000003000e4600d1034a042c044c0c844a800b060607980402000340c1e807008103956802046400d02d100d12001301d21301003040c1201c1c05100c001b42d0001404820701300210b6240030b10007543c07032000c3d0b81c149005180005030700b4015041c90708000050324014110700d99503400603001100403c25001c49056107032404c00440c21541c030a00c80da42007420b4045c042900c1d9030500000101729403200284030703918841c4e00341c0000092802e00145100780e007918030442c51340c5804800d119001c002020802998102031a80741d006070703180426100030f000110001a01c1703a03031f0120240c17112024 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 408481987 1250 408480737 408480749
    0x60e1e0613090311030c0601030b010f0807140f03070618090b240705060c070210031b0f0201150909051e0604030e04091e05010f0b030c042403080409060605032e 71
    0x1801004015000421f141240e00c107912882140c0e903900c0b98100f24000a000d0b2000b02c0c1c121500400c02514200d4051800004c018080d0071441040c00020740360400d660f00c1180460540356a040321101c44010240003002914000e014904001000407150000303008110021031228408040000e1001e01f40c42076281d00c0740480e412410304c0102c0032850741150340c04a105148207152101021711074007a802c0c0c500816200d40040030b1456509888060308060818115036a4812111903051110704000c01041c6041d170008101c2514107100781450341c1012101c8081400d0b0b08002d00407030001405690080d014034001d451102804c000030040d190510340030b0304c4030120104684070501c81c00852000548a98002c100d0004003c144500395100742a0165242d00184581d00d5942001c0e0003c150158118101c03050080c040100300c90b0f03000300b40d001507504060105045c404884a0b21485004d480907040060841c40c107403c42d158a01445013512810411038181c0c9a112801000c1c220040d00da = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 408483237 1250 408481987 408481993
    0x213110a0504031e0f11120d030e01110708070807060f0903030e01050a0c1b061401060507060f02040509011202040f1a01021c02060f090c04060e1e0613090311 70
    0x14509000038902c0c0c100380001e5884455801100710840c1071040303408035155202000e00303100f0445441c0d020070305c505500c51a8100281d5400740001103070a006050300d060a689002400280310075940e0708403042860321201051003000f2010200384a0702c10340729110703840804290350380d03510300c0c00300c0141048645850b08c0500f820307801003c140d0150050f20203650400020080740c0e0f03405c509441036032180e02d203400c049071a2601040c941060744850b2081c0f240150750202e00e41108001350745414000b60700c04400110302007040420071030a030182110f1440030410960510381440e0010300c0220041c1f08581ca03114494070450b04540b200e0304407001008082030b041068058040e44a0100000300705507d005029041e200f0b02100d049440241e9040310603801000207954800304010b4004000c3e024100074490101c503203001d0350f030307601904001c0c02440000d4900380c1043c00000075000013000407010342081081c01c00c40d980e1620700320030582c02c01c00760012034021480d05013a00d00e03000c07001640312140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 408484487 1250 408483237 408483247
    0xc150c0904090605010e06090c090f030c0a0308030106082503020a1803060204140616140a170403032c040b1c0506010302090c030f2a13050301050a090c03021311 71
    0x34658010b17030494032054404102d954800c4108420484121080c40910001380420111400c2020b60b2040b4480e0150032901d0940000c80040c15068090b841110f181c01e000005000340c1f54000440c0341c01c0910200f07903c030940c0e880e42d00d4141c8049034a5070441010380c003045000c03851340308002c5502070303a101000c8400c540b5164289840690b0003401900c0e82201803042100c1c00b0300b03104d4115a001c0560a03c594000e040036500c1201c4480503841144040c424403080001091b980c1d100800b240e20005002030b52185103103000b920080252010001080c1381d002c0d01c01640e40203c01c0003c14050032940015024180e1000501c4e01c8600b8404d240c4008103581e1f04810484001095070680740201e0707000740c0d150b91390034201002d84070840d043d00003c00f0480100303001c0120f00413160813403018242c1000740c041c07010241184c0c6400154880c121503121220804c25400d0a01c20b0781d4010700341c09000d01080c1343c81c1c2c440380d00c800303118803000380220010126928071428990240b0b0a42c1d0044a403036603a8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 408485737 1250 408484487 408484493
    0x219030e221802010e0d0807020d05010b13140709051003090c150512091f05040206070614060f030606030a150f15030302011121130507060c050606060c150c090409 72
    0x10b1255003012030100d055809003041a142071107902035000d900520301c51900d6016800e010408080e01c1007100c0644d21984102040d685500e040c0710920389a2100040610b103068510340f1406001c1c24000900440900501180e1100400104084014100490400c503e403810311651680c50740701566140c140d143c0300c0c0241d940f040080030313100341205040031107071161201c558a0b07004e4600d030f001d00608010b02038026080150400da0748140010105070900301e441c1c03920f400342e0b400041c141c00b44424540800c0891f1614800207140741e00161300400ba603140c04800f0a41d00c000c01c1c10050310200580c500d00d0700400440d0400382000c0b92231001400111000320240341c10310342c1c500044000d5401c02424880d00444c003025a44544000074507007c603c4241011807888aa014016110502e0252139002c08903004005c044000c22503541c0e80100407080303040c410f0918001608440c883c2508014000040b41c4c0020410f100041c1c242d00954a516420002c414078440d4141444d08182480d01450034 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 408486987 1250 408485737 408485771
    0x70b0109020c0a0b1e090102040e0115021002040603021b0c130f0b03030d02040f06080405030a0f1b081c0b0619020708010c08060108010803091311160506070219030e22 74
    0x7841000c401c5c440068840c0d100131401c1c2d0082e800340710800b5603010010411690800111120014140140c990b00b80c0d4a41c25401640c0c0f15420810112750001031504040001084100b10300c2003001c094013207280094000782d0328036807560f800302e001c03174803440c1115050200707601c20030542c42c009003143d03966074100004201039007241c1700b810790051807900d000800034044d81d0310522a0b030740000a0343c41e08681100580741d00055203814000c0141040800046001201c4091482030080d6042a102c0c0302c0c04550b481d00f138420080205015041285901c60b030b407981d07002c0d69441c1c0300b45212080354901900d17080341380600075440700c0c00c10742c201000c0065080e082811307140103071021307a1b401045a8035101426940e10a0810301c40c1c0203da151000241c03a80540e0100350082041041c151406240d5070500c1c0e04008960030070b0b192908508103000250340c04200c040c604038003003810200040704c1d98401508054448407042e0140300280c05100480d403000b5100030349098405020800c0b16000304010031 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 408488237 1250 408486987 408487021
    0x12010b0112111b24090601030204050403030608100603060f0213120215030a06050f010509090f0601020f031b010b0a1a0f2802060703150519032114070b0109020c0a0b 73
    0x19209400b50f190070f011815204084d445049420002c112a07465a07091000501e00100154101507880340301042203801404880e0880c1030910300450720504508011080f10101e001c503c000600c10403504800600703148144007220503880082c1c4228600b070001c00c5807441c429002c00c0207020000b0070031061001c03030751182c030540b8000e49240c60042c040070700640e010700c01d800720540d1161510700014001c103551014aa80040d0610507510061562039105103540c003d00c0c080b0588241811914002040c00d108180c2175400858003011001d10708003250002907190050210030650004940c0c1803000b0b00d204664030100c0081c2402e020856048ac0c0315a158a518001c900502841011079001d0344203000e1900c050030308030300703000d0068a0a42085841c00ca1443c9007050f07498010000004a964444018419202e0031440008150780c0a001030480403c1540116410828000700000c2680000c14a054440c0054016600d8460513030b03440c0b6183e00e208005047c4218942040174040902034408 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 408489487 1250 408488237 408488263
    0xf02040b0a0b1801031e0903090305030a11060906060d080a090f0b180306160f0c02090106180603090c050d060b030105070302040918050a02060a050c06100512010b0112111b 76
    0xa0340e402d03c801c01101a10a84040c600a1a441541b5058201e08075449116114400c1c10280040307552561100c0c215080341480f0000304036840569841018107001c01540030300e031840540458a060f000080c6001d00120000c2c040000100c0c5030444940108040009800001d1408485650314000c400e03440e40400d08012040301e611103850344504001804078000c0c1c20103030b440c2d1141164410300302c48010110b542101040301e488440f50250b10f03040c0000d80602400d0340d848420b0010105003c0d0041015070043d001c040c5030410300e00110346a400e1442c25540122001a074032041c03402d14101400e00e0080299065190509002640390158000c10450310185030030f0240c9a600741a05080c4642c044000d030031504540d0740c400052411200400043c00c450410500b411400c006d414600b00d403c4443e0040340e07a040f1014002c1c0c0c5880018800052403640007808100444000200102030b41c2c062694030948402c807030500c0c8020070b015a2180c400c41e03602841c060440810b6107030b489003c1c1c0440c2c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 408490737 1250 408489487 408489517
    0x1b051c17040602090d29010807060c030f0504090f06060207050d05120d1e0b09010b2106060f0c060f0f0105210106050405041202060a060609030f02040b0a0b 69
    0x2425010301400c559003200505410003002907845894040207584440c1c1d546910018501000300041d02c408032003801040c401712110205070071850030001540c0180c202c02c50540c016442040350a90000f41070040542c10701d01540103840e07400042d0b91500858110100303050505041c1c81c0022401c0d4408403c40d0400da084403c5140c1d100284030319032286c404080c0ca55004400c8180200c1c6411000b00b0000c240b42da00000e140d08401c079501510b81a200703003042006c1d126400051189003202109000d4500d40300c1d11490960010846500c0020300707418142503445034400207030266961415500441400c040003542c3c0c403111a045501c4100c00c0f1440d4010042080118a070f600c00710314040d05841000d01515262000c004804074061000d4042c0200c0759210303200466551100d028860083d4456801185221500f0401070f00700007009104401051501100704060750340010b0f0807003100c3c3c1180702185104c11034004200a00825118950460b12a800c0080e107401e0820082040700d10048034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 408491987 1250 408490737 408490783
    0x40602100f020307050a0302071a0f040c06030506210a1b05011e05070b0c0913020a110616050702030307060204120213112502030106080d0e03071809031b05 69
    0x1407004a00064503000300044c418840c01d0781382e41c000c3c1c0c0142035050244540120503010301c1800140021f040347d04509800d1907405010030444070080c000094401c81c10240034501c1c1400c04104260750844943c40618061007014880100c2031020501494101000d403051101c0c40585003083d070094400c050004425030040c0c51001034446001544245607501c83d0320b03040d069240e03c0f1109401502064000c0001c10110125507a0031003016102e000d108409620380c00c0d410b40c00b40001818401488a6070130210130000840180380c51000ca5104a00301140c40d42d00b030740007003491801000c0c0c0082c68107200182c08540da00d01d500300c40f5000351084a80c000a802c401e211075081c0c035000c07005951240c40603c5609041a20045182d1204000800d600050a10b640000c4e082d900242d01c12003254002540304d0070034a5100f880625640c100794018010b407840c054000741c0d4615076003c1203140569402403d01014401c0c400001050481901d9103418403450030500c2e15503000c1d81d0800100186404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 408493237 1250 408491987 408492011
    0x1e0513080a0209011505040b040e060f040504020f040c030902062107090e071d0303071a130309050f030a0b01150807080f1807090c12050601020c0306070509010306050604060210 78
    0x80d44900e056405820303590326901c2d00503000120503c2505c80c4003407110030b01000c5040e2074044003030001006601c9040e5007504105050028000c22141820300980c1403000304805a118200841010441603a00003025081d2910840090200050007076020800051240c807110419444422040000e0320000c026181c842080d54540780f98843c003111138804500103100076010700e54181d0004020602c010760080138100190855005107404c84060807050a4080350340d50f81c00540e0352023545801d88035a0103d603a1000341c821080d501c2107074404d01d0000c000f18102c0e282802000701c80c50744003000d000656141c181c5070344c503080054088070000301d1500000c1c203500d00c14400280260703408070380030166850300e03100311403140d5101c6002c42da148161a0000b070741c225203100b20114100d0aa80d0a500b004924407600c042c1e50018000c14115804054542c000b80d0300868100d4001d4600e0404c02c0d0760703826030001a0b01601050384110342c89540440d000038155004103405001d500d1012080040c0b10b5282 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 408494487 1250 408493237 408493243
    0x60d0e1608011509091104050a0c02011d0c041a0d03020a050c030309180709030506090705012c01210f09060b010924050c07060e09090c011e1e051308 66
    0x1d5041c800c0f80001c490800820860ba03101c4d00200740070b00508045440c42d54003013011360b50161035103605269201007084643e83d081c8100320280e58030380c05030340e085580801e07000d0f0b4401008410a00c95542e800c1082801440c1c0b0340720b541c1080f406020f03d0741c00003907801d0182d240c0341141010b603124022480610710b246004011540046001070058196080787e40302d00b40c152038001e10590900807440300200101d0b5040242e04d1107182054000c1200f00d0030040010801c00480400c194584211071000f40304440c81e03900c414100c802881e082008112060000c2c02c4000381540111307031b1a180001010030b4054980280740c0e80c80c0608002d000c006e0690300116800001403240904001e410307641000b041c8420680c1510102c040c0c80c1c034908180c490840181008800c2d44604089189940600c565041407040d86600c450f407100078140c03030008840007902050413800c421300058050300c40719000314001e507609421600784100b445106082030002411a601070000e059070101c00d4031740051034001c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 408495737 1250 408494487 408494501
    0x509120903030708071b03051b0111070b0304021504060207050a05060909040311150114012003040902280c0b01080d0e040e0c0919053102060d0e160801 67
    0x24000b58681400b40d225400030740c120041c201d8007414841344042000100c098a00c1c00303940a50058000f090070038180900c04c2003a00c2d002c506002002d0303a05c2009400100310041100d540f031340c45039a250399130710018400d203103151a480400107001c580031500a0340054142c0585006865060605494500b0091280140402981d10210b035000143c0003070702c01d4028180b010700803c03c6400100b00841e000388104403d030800e01c145040c098110040350b901c030000c0c1d000f0107103403c4000b620261880c1015102d106600405060580010310500700383d20340100c3c03c0740740381c0c80c00e5403040c190380c00800101210885203060714a61104030000c14541d10100f0100074098860702c40c225080d51003030600c400b40142c22001c0071107006480107200e00303886400308103124803d0702810800d01075000038a0012500042c1030320444581050006022410620103015580780300114080d06440c5131002800a100d01000032080c54140500e01c102010000380045419190f0725050211b075480e64141400c94881d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 408496987 1250 408495737 408495739
    0x1081507031a0f0109090c0c02150c1207020a0e010602060a0c030c051b030408010e0d0315060804020105070c0506211e190f021303032303070e0307081005091209 71
    0x918400b01507880c04083c0c001c003000c0d06041c20246030365103106140464070702d02c1440010848002c0c82c8000c614040070800ca1449441d1a1103041801c00c10030b641d91600b8880c40041e409000084072803c1d940c944440e000285681c40c1900003d42e19200000e4071420265072904100d130920728141c0d4914028011007105485a80e921400e100318440c01c080b10000c400d03000c00e6036020420010032100400c2c0039601f04520124014601c000040d139000b011a140300c6040801306101070010300519520500c030540254091038503030380307540041c00c0001210940b640082e074001800a40e81e80300d03141151312200c4000755071f00740350199614034a40c8000700503241104250300902100103079201c281030b0041c080c0b44c0050240006d07440c085d074641000301c0e4018640c405d65840c03c90010420958001700307186028003803000f110145102080b036442c071400058416000d108280000707141a81301000700304002d11200703084842c01d18034105000020941540c0340121401900c89101a1452440460f40c00000c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 408498237 1250 408496987 408497021
    0xc05160e100b2203020411090117011503020306010215010602061e060607140313090605040e031204061808030f0103140a05030405090408070209040b090d0e030703111203030108150703 81
    0x881030303100424071401c3c1881d45111261489010025845503c5400a500202ca800642d503014000000d007229600c1d41c42c841080340100014014548039600d2070301007034244c3c1000741e1252100030060303040c10b9101c680c01e168103036003c0001500e5903000a006d4098090110022803503018011302030b2060000b1500c1d150450420029800000c13030078140d08030003e02c1001602d060241f4103156915050640d8030500c030a54403020140003c0c1380a00c2241400c01c80c901c02507185c141000b4220417038072801080500100c1e038039146800d4480c5c03000980105036a00401e41c82d41c074603000d0b410031300a807001c0c003064a42c1d44238800001000718000800400685c4c01000640c14546850208aa1300030020011507449109102080041c1c0311120b9a07405144280f10100e52850041817543c5030800c18047e00080243d100640a031030348020072481c054a4100d6428480300d41c0c210003140442c002c079a071310541848000000120b000c00402c03181c03070078048094446040d031143c04048050300c034510303e0f800400c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 408499487 1250 408498237 408498247
    0x102010b0906090703021b01020307020706030204180504060b0a030f2310051f0909030e040b0607060e190803070314040c060e1504090209030105010b03041707030c05160e100b 77
    0x8901038a80c1c0c0c1d803100c0d00d171401502c0c00e05402c8007000011018a52105580e402100344050070340c0510403100909071501d000c506284c940400c0890a181d03192000d50003a42e2040403074280521a00009007401c40035202c50030840da46c3c609140e03101d103400c3c0103941340d07000215a55550300d281101c4660070902c1c180100104083c083e42c4074010800a800c03140d03074400c0c100e50041009151100140140079565001601825904019001c080c8500986204514011200140d83c7c4c480d4181c0b0030b802d42241c0005004a40702c200c492501e00e110403084a20340d0460360620402009200a52007403009940a10418501c107415014201c0180c0300100707070401c03c0c403042c071140d8400d1140c44851035006207014541820300000400d5644150005030440f03070000f50034007860600b4000c8600400170700248501d03614160301c4040d619605c5040c885680d1000140324402e051060070034600064000d01980d050305030180c0d404541d11040d10a694900041038001044040c2c1042400e0440d40d80a05880c036007 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 408500737 1250 408499487 408499489
    0x9012c0103080901050d0b0a0314010c020f0304140f041d100507120903030b12030301060318080a08091e16050f1e01021f0501141507030f0903061404030e0102010b0906 74
    0xd034006c1120381240b29030307405043c603543c0d584c180d060740150300800501000d51684103c036400e43e050100c07038030155409204480d0304424000126411104003104003140030f4012800280c0c400c080c410340d141d22a0a00d140010648c0703101041c52200040c0d44119111030b07420004080c02e0303070000c841b4640030801030030150601401c160010300e0a580b10740740000f44002d01800007017420505502d503525942c404401480540e8044c442c40c00581c000900f0114006044c0d50b0340f1900317210340002d040c2003081d035002084c03d140d4100024516410100040f01d0800121040b1550325074600108106010807600700140a0400c00600e540003100544a400902003100e259901d5040300c80c41941140b05e80e400b028141955204000c0b00030226134004500c551400341d08480f8000500e2060303100c0c0c012001c42982d071003001c0044521007541070400401e920502c00702910042640d0f031025220318104494060440314001c0a64481c501c40d8903401c00004104004a08885400304d245800c08c01075000b28003e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 408501987 1250 408500737 408500747
    0x90f0d03090902030c07051e070816030204151203030905060c030c1801120e0a12170711070b0f030a0c050f0702121212100e0f0c0a090509012c0103080901 68
    0x3119a011038610311b020007035580c0b140b0b001491200049820700300480c0a41c1038000b0b0050382c0040c07100c100200141d403450300e086180d03c070703252100a2180ba542c924401e14140c0d02561000141035903030103014811401d0a014010342504e071000c4645024120000c1c0b41c16050000380d0380250312440c411404c05100c0e540e03401c8042c41c8214100c0c18490a0400c005501c0003500070958041040750280c4040f244a240107540f5507110404841406219049c04440312504000c950b40a40a80b6281c0400300500c8500c0d0b0400c5402d0f0002c4440702c100080840b41110340000071401524052003c20601141e040e003110603004110f5801b620803000c2003490f000d40307481107a65038544078100555904407040f201c0c003c0c8680c030002c2d030f20180d905010200030420125a44800040102c080790441c58a442801d100d041d5000910341e003501c01e404600000b40901c100d84020103008041d0280000c1d584a52034400c684500f0790080000e0704150143c5080c0d0a00ca48115040325440307149107040480d00d40040d21 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 408503237 1250 408501987 408501991
    0x15010f150807031d060106090801141608040f02150a080f01050f120102040b0403050a03020d02010b0d0308130203070f0510030e03070b0c070c030b010314032106010221090f0d0309090203 82
    0x12007408401a41070010b90117018a5000705000e80f15014554070300b01c0d00500b560450416942d45c400c0d030000708a2080c40950a18061160798a0024480d960b00d26118043c010a0007000e90003042106404815460001c000c0c840001c4640f00c8401c1640d58598a98034890240501500301a04481c0d403078440c201450011040c13002c60740058140f6494030082552508298025170301c43d80101c42d03847c24142c050203100c44120170743c07009200d99400c5602103003600510f900e004080101c4100020040206030901540541e801415140030a6590403d0700c81100107002d100d10400000c03048004840c023134801c0008151800d409541050f0303d1391500c1c0005880145040d0200c6410001280010390800861002d14071401d01d0303010a5046041c0f404105500003c1d100361079200308500316065001502c40d032002c0f042c0b0790b4808055a10500102c1c00c01c003a00341c8400c0040e14984194075408500c802614001300c00b0380d0f092401025860800c2030700c112840c0b0203030108a180f9020b001c3c480707082d00255 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 408504487 1250 408503237 408503261
    0x60a1202220e060a06031704140f0103111b0f0c010c0b0603070f0e1509090c0904030327020f0105040f0b03130b0112031706060f0c0f15010f15080703 66
    0x3a4080b1025601c0e41014801c541c000c6005583d60780c1881001b00d0b140030148414550705115080c281024004414112840b480c540304451084c0c0890241e807007500305490141c1c41482d0240c5414900d144e00005080c2011103124030300481c00d041c01e1500e8001110b80324028169541d0000c000300e9200e104c840740b00500b445406019482001c030345140500038500041441410358440740c41c11a0803000c01000210b041c603c1455a43c2c2841455a000101c02c00500800c0304c4180c0356485500e010390043c0020b54050001310110f500c0c1c3e5481d490f002019200c0076000307131140100d540343c01c00115000e210328016400d00840e0148213110000c0000c001c0c650200b80c0c0b00781021100300a80340c05580030400d9009081c0e1610054202e03040503886014030f86800c0810401c0104e5040072030002d180c500640c0e803001d1403440c010540012145040003e5802460f21905543c001079004a0480c2d00e803409014440710550381b0280000c00c980081124552042c41d50790341041501d5181045001d481c00c8407041d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 408505737 1250 408504487 408504491
    0x10181413050603070f1508070804120e0d17071403090a030b1008030f0c010b0a03050303010605070317070309050610050d0305030c130902130602010612140f0304030b060a120222 78
    0x3040c141101712185d805030003500e8894044440d601b10003400742034000c01fa04100103441043c04009412507095010001040c1420078000040101248103000540f0025100400201140c90032850500042c0443e41c054803454045040c21040b941d5030340703d640801e80e08000f12100c100041000e0032131460b006503031380303482c0400190b50308401031a5030800041640e480400203603d8401001c00d206650501000f9110380303100c03600d03503101c15441e800144128018040b000a92008040c486c00c0070a801002108103a0b040d4101610010010119107404503160310815010550070426000250111540104a030080c02c5865408503000d03000600500c481c29018070814203d180c07000c0c00c03c405000f41010040c0c8600100301001088403c513400801035904d044000d105115141c560001c0b540c2e0006d1070141194444110300345000c000d240d2800c92404041404070400005440060190fa0704440ca080110784520790094030001240c402544840100d1540040e8003044c0d0021034680400c00380 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 408506987 1250 408505737 408505739
    0x18020304150f02030604180f061d100c091d070f05071a040201020d17010e07091205100b04020a08070c020118031b060201020f040b0906091018141305060307 69
    0x1070780068448060b20050030030303004020406642000e02c40c5244141403000c0c40c061608294a0390702414032204000350003c0d840c0c00c41e840d02c281c415030705849915812005c4440c041c026510440c01802c00d504403100281c881d402c00108011502409010103100510750041034586e84801c0d1080040e0aa070070081c0b0105000000109607a40d4503451000840384480c001b81ca41403000a045c2294400a07409004070340203407a00c0324030002200d43c10f607060174205140030346038244140c0304028294030007001030628002c41d00070090040b5042c540f04203415000c0c0f12a8801404000590250085041c00680903800003420b00c3e11075090b5070219030042c180b6440d425281540ca4213088042e8000741d80c00c0448a0304030400d814407100040080010784001c60400f4070b00d007454181072040784211251100c02045240c21544e8a0045076020700340280328010b026103201c8083c2c618007503d410b001c4081080c01d000117030138148407107003900420700402c10080e40c04020791020042401410702500b610034644 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 408508237 1250 408506987 408507023
    0x10e0307050706030b2202030f061903021507020a0305030d110906090907031416020610210c0b04060f0f03050c040b070609152406080604020a02191103010b0301020418020304 77
    0x2c3c5290003686c070b654015990f460298030603c54040007411039401960102e084018200100030190141d0340e04a42c1c0c600c0c1d0f0f92442072032003254020344102075409203e109000003044400402811250a1101c0c02d00c0854039100607007000323024405100b40c0110041007100c1d0303103240c00d81d02e40d80c0c00291400c0019560803d03158242c034124040700d02e40c403407540c0700810702c40103901003081ca40e11060090200400c2420f040c14004120b0030042c03c3e074020080c0c944c200b0b04001d80c4c007074400080c20641c1c0039030303464075075450000340f0000043c2d200001040c842e03d1110103480c424060244079654503807401c0d161a00e40101800300f6840803606958560b0348422850006100000c204840e80d40898081401c40940704a49040494800b000794040784240b000c01a03030303401401c3c1d40d52103401160016115035840034149c1c00d00054023100d241402000040300100700501c0c0440b040100154000c02040d0600030030705080b031181740500b80282d10764807011184180a50001e41c0d1161250202c14a9844040 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 408509487 1250 408508237 408508279
    0x506161415152d0a0b0310062a060b1c170c01150f0303260604021624110a02030714070e01060503011a16030e1c0302060108010e0307050706030b 64
    0x1100c01034241050031242814544001c6000151812a4001e80f9504201f10070707500e040440d00c00c0800f07000c2c80340c443c107803501e212048144100024003460b440b035803d18a8544000d00c40c0c01388543c42561286844000d405a06102041a640c042200001d80301a00007408580e00700b0074100c84c0a640324442c844500f0351144d40300d4010040306686109042c01c501d0044c2c2251020303c090390102820aa14942c18002003001c10340181050b140140c0e00d43c0b4142412950f004580c401626050b002c0203074035500606514005000880718008010b107401c6900461024890103030a8001680f0500a10340499443c0340010340280b42c4404503201d07996034001e03c04060701e09030b02980100d10003100401c58107688400d1142e0070340c520803126181130f03c4000c0100034902d030340101504001d007801c00c0d40b41c070340c46441022804d144505421065918540742c021355030031090241c2010f55091003800401c0920001c107a0710a164000007a266841c10020103d002700203803030130140d000c00d40c40c40c6900041401 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 408510737 1250 408509487 408509539
    0xe0114090d0305030f010603020a02030d020a050f0403050d030f1503080c0102070b0c030403020c0301060f17010b120a0c081501180b10030204061106010501050d090c050616141515 79
    0x10f40c40d80ca4407440c0200c0c486040b440164820014180104030b240e032001c0c0c1c04400c482040ca0449401030b2111072403207044400c4d010703000c00c4515820b000a03011041c0100002c40c200e07104000c3ea014070480f003207260841c040d2254010200720b20900154148006031010001e00301d50f103800030005082c080191240990000180c030150f20840c0008240014158144507021007a03800703400a00c801490206443c00082d0944a0221040142103013116840300a402c404107210000703041d41204882401c2d0780e07440d00e00c1018110f030010180200050380c02c602007400c001262244a20020356860a88100052655603584800c05075468108800c991790303100d105151240706980040e105c500303080010b0050706465480078802ea200600400190382d00c00c1c1203c2c514581900d011030b105441d882d18180ca03100d5074019650200300400c144a40e00344000e10781096074000c0030414451a0102ea00981703e0031002e40c001c94040d1607500141c00410501c204100e003090242c50341c40501d000e0349a0203894211 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 408511987 1250 408510737 408510743
    0x601051c1524050906030711060a0b0f0d120c0807060501080a02040c0e0306041203023c0a0c0b060a030506041b05010905130c1404030506100b03070e0114090d 70
    0x444242404003200300400740110000e01c0720b401544400c0c048024100d401250040d0780705603030000020b803a8a1040c0302142d003c40c600412030300b0b5810309220580242c030840d00c00a0080440135034071203d03494442c403517a01568000809503003044041c58100c85020350300b2015540e9480420059000800342c0c411140200445006403000a11510412060350300303100344107080105c071400964059601084054010f40c1c0040000380380190188250007034010f10088000409004020a2483d5202000b02c60124500d00c01054110404401982d09000785010040001e5100b211200022040589990000002400000c00c240e903982c43c1403038150100c0d0f0803101d015090600f100c0c48500400c1800103002c0900746038040504000200c2c50340444800c0c080c82d550745400030581010b000e500202c0c8980300b407d800960b038a4482c1030488e610039040c1c0301401c18806c0c0c04400900010304806480c01207003140d49641340e900c1d02e0b40045a4517071008001c038035000d0301002403404590f1108070214400d44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 408513237 1250 408511987 408512021
    0x509060c0a05060a09050c1002121c0b012631060c0f0c0b0a0209030a081b030a0e040213090c0f030e161e0f0611010b01090506030601051c 61
    0x401c0c0d2070050704040d000313400260801d0521614400289010039011082d40042d5005d550104170604101e00e4010f141c1d6108400c4940000c0080c640100a60304c1c0702182120a0280300244402004503035070300c00c10180d000c0c610400141241c4407402d191400d41c1020f21600c1c1c010b00a0301c0c0c0c01c0c0104801520700000c4d043d464000381c01e0b00401904d809003d580201c5414400c280050040c0040c007003d0080200504503a08600015800e02c2168180c030038002018044901070100c514001207a83c1c8428031000c07180300401d6003c0625600007007104c0d070209030741d034603405103c49040030300010b90030810444400c6007486102103107001e214414000010720309c0d0f0740c8000300f11141781d01804442c001e0241480903000181456462801c000c5050120f4141121410081c5664815005459480c0d001043d6002020400154a90f8000360300400d00e06000020021020042e00543d208071240c45480d8200300240000780c80c941c043d8010300740d07041e0000b024149010710704a0043c11144070840e504034800c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 408514487 1250 408513237 408513253
    0x50a021b06010b09040c1b050606010207080c061605150a020318060402061801021501060201060e0604051306050c0d11071a040c2304020d0b04050916090c0509060c 72
    0x103540ca01208030620304a10103803081d54100740e04606140b007007411042c001c6455001c6080001c1c481c8030359004da10035051450850940368600261214810b88607680184669480416002c0c00441c07141034003080202410300d8500344180038000c14210742015038040c0115500345006050401d1546d03c02c0d4501d000c01640d80c07800e081c004000c14801ca00d400301640c0030f0000c000041e240c0c00100c0301709000121118925042200040f40341c0b044e90362402107201c1e40d0500000d200d40d0150131607800c0d01ca0f0444409a40e5842005000450304111a01c030080c020380900b600210300541d11160b00130a0003c02d041c6030807a08901d030030a85044a0700700d44a035100144100510024043d481e43c0d107440c50b2a096100d040c952a00f0403005403e0196641c10300c400341d02c00c01c1d03007600d10303861002e0214050f0096403185000c1c6000030040a0300f4140a000d51b080c0b0700014003040f80802d00c0d482103000460409107450408070400001d09201100c2000e0140810500000340d48510150030300706003c0d0000c00c3d02c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 408515737 1250 408514487 408514507
    0x190e0c010f09060e0418140d030c0e0102100c120606091e030f0b090703240b100c031d0d05030a02070e01050d022206060e0108010b030702150a0e01050a02 68
    0x3000c1c001501020000010b8060281c1c9500500c42886250110f401040059010003400244550f0000041035039803200302012800c013001c100304030700c100300f0f440412041014407000d90f44100d540c8411401a0480c5000d0708019069601500e220b407100e01d00660480d040c4442541160265085200860445501000303400c2042407588a0000d4904050140c24555a14115404450000180076160b140c000038214042001403c0003075401c882502003e500404944000b0100320300024845070410f810001c0901b41803141041c410709580d01c600102907141c404a400c2c801283c800b043e5218070049044056070b940c0c0c501c0c03e10600800103076560f444600c0c1c0203403500001c0e034048003090041c0401040b09a8800d03680c0e402c1a074060f030b602c041d00d0808500c98240d2800180e0b03128400c518007400464116409107c1010180e420b880d1702c0c0e2a40d03280c1c0e08140076070004590810041e401142064011604668995004030080d2004600035084a00a90943c0d00441e5000c0121b6404070318600741c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 408516987 1250 408515737 408515747
    0x108070905090d02030a0c05030f030114090f071b050106030c03030512100b040302130b04140105010e0904050d030b0102120a030f1b090302190b070521120f190e0c01 73
    0x1040000f02080105590040e440f80a0503400310140310594080c081070000510032140641142c941040da250b84800c04054a02480c02c6514015240000003d080f8002c3c10480350007042d0311388960011520b45049010301404840c0210b41954030f1300f400100103200384c800d8401641c403946440c2d03120101c8640388500c1c010002e08403200d9011401041001740d01c0300303088405680d01074031407402440071038400030003600900314410f030002e162003045244221714401680c141c1c0d200b40e9540c03030000c0700002003028a0030280c0c1c01801a400c114040d05500d4001c2e032001c020b41c036042c015141741d60300d0340c00b2a44540d0005501c0101003500d400d140d10002025106041c0b5000388400d08202c034100c4013000410b2116140002801451249003440506010071107402c014940c55440179a980040e14015860380c650500c112181000c4c4052800030201640c161400e103030085001c1d048980c0c822400003140d80c409000780c0d0014420511110318450381c0c0c02510940071903580204401c074040b00c00100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 408518237 1250 408516987 408516991
    0x20a2303031806131509140607020a02040b030a08030c0c0a1406070f1b030e03120412061401050d06090303020906040e160207140111070803071506050f0901170a0203060108070905 79
    0x150203004c0d22280025002d01865203000749442400540401d45290246103100d040c0480c06540c8280c204000740160300007801005a4400e0b101400001049002d041c1d4410040200800d100020320000d4030810944002c1d050540c2c1f000c04840d42d00c01c454641c00140000c0c2c494170007560700000108118141c000300820824003072440d21601c511441080d001c42c1030803880000302001440003001030b890360108a09010b810302601d040c2e0b0340c0e69417000400390419000108445e41ca01b08150035500c1c0021040315030403100c2c0900314141d610031f030395180b03401424010300480506a003840704240340d0300c40402a1000d484bc00c01c0160042c01c011008100040484500c602198403110701070000d0391b080c2c1c07180c291a20b0f007801c1c521410030890814a02702485a04500b80360320003c1001424040010400c44103402205010001c1075110b0092204c114042880b80b07802c07215000c010450400c001417032464540030101503549945031540000d044c00380a0b403102017540d010b10814810420244225a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 408519487 1250 408518237 408518251
    0x8040e0601021f0c020f07080f010b04061401080c0f16060506030a080a11030c01020d020a08090708030307050a0e0a032001110a030806131e0609050403020a2303031806 74
    0x220080d11000c0702070320184080c480d00c041154880d01345070f480701c0c000c00c4070820342500401a44c61040e102c40529503a440d03256080700b240d42c00c03d11940d03640d0501e84626009e43d000d00c14a070361008500c1006403030580c40940b03000740c1c840003003101c1c00094001e14080c103038018aa4204030f00d003143c0c505240e0b0648502800c45442600134401110014110804603003411a4904000380c07c1c0342030741178140c2140141485602694000aa642039032807c0358001c0988412945440c00a61100002c080c1d4886c80c84c06018541d60042011a5042d030240c07018001211080c942000c0d0719071104041003c1545a52040f256400b40e1510b444101c0c003140381c4c2100104080c0782080007400618550703561501d2151019081c4001c0700f002c0341c440d4030b0b0008104400e030840075051191035807807171030300311416031940c0d01d81301d054900300010940407810300500e400740790103038004c0030320052540340c0c1c00c2185041e41080300004200005086502028405944150341129400c00841141c8401c00c2c2013560040c421 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 408520737 1250 408519487 408519493
    0x5010b0a031e15300219050402030915010b0a1205252102090a090b01030e1608060c040303020d110c030a081e0a020a03120b1c020411040501090303050904110708040e060102 76
    0x3c804010300c020300c2c405440390110b070b9001c030071503200d0352011310031b440c0d500525085070000040085034600001c4048191384503100c000d825030307600ca0405a4a0007a0001500001c0346030040301c0160305150030a54002c100300303048007180360380c81d40166403c050700b0031140081421031104841111a01c0754905181951300c00131341c0f402c407114000410042e017030300520b001e0310b903142400304e0140d1090b80305a948a107140700716a0101020800c14228141d03e04c9040818840c200004401c503051700c0544007100e9254004161090402038181c540070000880700e03969101d660100c030410303607042101c0e04025010304005a500c0c103100083c0d03080302843c092420740c0e40104006a044055001440d42c1e403480c2c00d40b5000b83c076070050545480150414903401c07544440100c0c11000e4586d120040410440c3c1b0032034080003035202d81c0341c00007101d0085109107404038003003090800c0400e02620007081103903001400000c010f103020320b81110503046141c00340e81c001c01c0800c1c20b1100c4035000d4488c54001c0380034001 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 408521987 1250 408520737 408520799
    0x120915050403083f060d02132a05040f1521090614180d0206072003040f0617040c030204090503120c190305010b0a031e15 54
    0x5802803140780b100600800000504040400408040705001032078210030a0005080060404820481c10f090500070a00340000c50401d291600400441a81c094003215180c0039090508005003400c40081d11707030710200c10400030304076841e203040380f8002004e4581c0c80e10340703080c004800e42d03250b00340d04847c0100200b8920441e20b103410214003480340c0c16030009102d1082805c62190301504940000074100d60604d003a08038800c584030601c80c454008141040c07131034203603035200654a011100342c034005a0014400302d20564811151800c011884004059014a110000c50710f99031090b4440c40c10422019030600074913034856a41c51403249503580c41c0d16641095210798000281c9407200a108660352014002008400c0c820340d48004840d1b4485001403403d040c1407501d036440190165164681703c51158071580c024840c180c140d4401441710750604009503016801441e20307201348400514107828090500c0e40901600c8000b6580c0c8071800c01840c0781050140c00f21031600c428103e401a9092 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 408523237 1250 408521987 408522029
    0x110304180209030f0a030504030308070305160323040c0e10061b0218040501052a03060f06040e09070617070e0d02061c05040c0501210e0c0d1209 64
    0x1040c0d440a80182030040c1d46034002030001e450b207130703448400c504240140000310042c581c0010140080720f011f515001150f0742c400b001203045030000c96031450b44410309009144e83c94440d03400040600340c0c100e5015280350440030910f030300020442d0104d4112041280c140b000c80b60301c2c445190040c4480d003c8662a0382040c0001d0030303149089281d501d6030b11400c610344080d59a1000c085080150a0400c0c009074101802e065019280480d8404a4406e80020041030311015480001d603c040041600d030658803124108001c1414084c05158005014000410700e00010003d442c014009400100241407078000c000d0001007000681080122162040001c0b40c3e40294990f0201c0808484a200e981000c2c40043c000b40900b411040f2031203080244540070603401d5020034091400340b9446425690344500445001c044000f020000280c0c0c0c2000605401c1560010440304076410242d03590343d2680704c0420343e06548814162040142004aa01025044041c0c00302038803155003203488a03400f0407 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 408524487 1250 408523237 408523259
    0x5040b0a030b070e0907020c0148140307050c01080f0112020301060e0a0c020f24090118060c08060906060a050c0f070303050c070e24010507060c030c110304 69
    0x7200261070500042c000403c01ca11500541d020360f10014a54460760500c0d5100070365403e4540c01c5140400c044000c6e07441e00c2c0000c00c1142e90001050161002e11b107000440030880300700614441081c80000c014403a001039010500c590100d8070520003180c0307611050820529003003214600906004041041c06105c5c8815103100d811344801c2d40c89501800020b10200e4014140c5503c49002c22103c0014001481c903690400c00100000d0307402c0340c1e0106120b4054503140c80c1b5841129040115903040407000d04622804aa445200c07803000007000301100001401c01d20746034800720340d00d581d101442c40c0601e42010050750880d00a86044046251040108070948244a1200c0c28002e000c034607000e100308108446ca803c1c070444d500380c0d030401e80c2c2d91034017030a00d800c00e0107101d4941c040c2d000c0200c1c4403001c0c10801d44c801e150b1201c0c08a0391140d203903400705c01e006100490b1410030008120b6580410942c0c01200610026640d0000380303220414001000d40d10b00c0c608069403500100402c002d081045 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 408525737 1250 408524487 408524489
    0x110316031208041a01141503101203170720010e100f02090a1403070623070f1b050901051507120903170a03060902040308070f03050d1e0605040b0a 65
    0x641000b81060b1103d0502c14000c40c164030080203003943c41000071417070420985030001200c4054811140350350b04880321440030300003203a40350b0b10010310a80130401c0600c0301102c0b1108901a0406032000c6c9104400c4090a40e003c545000204001403220a164184c40380380c0d20344900b1900c000c00c080c0d100c846070942c8482e0301360440c0d40140d4031890a4080c4852950403550104e0004141c00c00c40c60f514410034038191034001c0111b11a020703400d00051154015001c1c0c01d0030344040030580c107041c0d40103c00c840790703034210a4050f188580181391410018940080586580e45040b21880d00340f480d090800240b004144c2055014102f440700c601c04103030401c400d40e0500c0d039000c0c2ca240c14555030780e0000c4404100560016080c07000b40160b07020002d01100042a100c2d4407035406100240e1030760b043c0c009900c20b0344030007401800204204804141c41e5058203080600c40e2405a10703000c007443c2800c06503014461030310480750402c0156030f112003080c4101c0c002480c064a0510203c015800020906929 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 408526987 1250 408525737 408525773
    0x60a050d0308190204080604050f060402010c080a030f0c020a05370219030b16090b0708070c0e010f0915030b0105060a051c05041221110c030711031603 67
    0x2800c001c200c0042072903c0141840480c48011034446960b60b942e55a0303040300796400d0b01c03d4010b043c03913601803142c00b1541502c1a078068480703d4010351203603904615980180034403030401d6610032515807112514000c804c4403854980c002c2040140d581422400d100641c1c810104c00026420701e031016140941d083c07081c4003214569403281400c24008910035a4141d1504003015094101c007104004041c140c00b40100e00002c81c150f00ca221149064555600f24040d0401c0403038240301220020300b08200900da0b1612501096010f159159461260494280c12200300c414810030113012000c1c1d01e03c03482c104a8801d0a400da01d05203103407607000c0d040b6410f014907400b0740d4001400000160003070040b6a0301005010aa070b400c11104d0b40104020202030320103d52200c10611058a201e01ca058000048042000e0302c1c2490b00013180118004c001c1c440800344150018040f40624030000e10203032941c1c80c010700c140d4562000031010103040050018288076094440b0100f8004100c0c00b800340350ba2654 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 408528237 1250 408526987 408526997
    0x3151303050408100501170d020a0b0402060c0a05101118040b1206071707050309100e0a08070f0302070503060405071e0b19030c1b0204090804080d030c08060a050d03 73
    0x60a089071148250b40014119108070a0b0101c0102400d5100318121400480c0c0c00c0807208108980035120740100b481000142c2c000040a0041801600c050350020710003051145441010f8580c0c0381000074401003650140c021840c4107810f420715015510140700c05030002031801c2240781d070702c1640c001d03441041030117180c0d680d51410790b90b19011a01515003c0b40d40441e070b4039141400c0f004040d140072220303810030342003010045000d050242040ea401403880401030005458401c015000800b1510032480d028032070b1051840106820500a14246000300303400c900c0810203080c082d2a02e16542e12050203540301104210200b00b0105110060f50044070107040080d420b00c03600f544103000da4018580e00040003482095402d000b80013a00ea5081c651020b01c00800d12030300a845c0194454805912109403015840c01840d00703a114111840c410000d040c1001e03182c500e0350303180540001c0701c07a0109541d20b0039084195003002e0309550061089601039003407420a400701d0701460607180001c040c41 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 408529487 1250 408528237 408528271
    0x15090f14120c0303060a06030c12110912010e330405071503020c1c051c020d14100b030106090608090717070e0a02070f030503070513230315 62
    0x800c00d014071103210540640c0c180d2541c80ca80c441c103880382c0c07003a41e80c0c0748114600e1034001015030080c056082c1815081e11a00c400300c0e21050b6039005001c1c18800440703540420040d014059403081d640c0302c04a08028000a0f140211a203118903001c030841d412a20209040344004054600001c216102030540121180584840c540b441c035003191500581ca014515005080c02180d15074050f15410382000112040401c502c2c580c40c55600b0241c0103000052002c02859450400301502d424074403a8407400145083d0701c0b07000007421502d00c040207140d4401000180403041855000b208050507902602c80d1a5502d8600090180401ca03c07e003014440e0610005185690a000b050020030410508048007002441c6e007d13212102c81c06429541d803400808a0f01c04a603078803d545900340d008040283d1601e651f2415600c81d00010460010050100a442070403140f440f859002841040d910500751080754940c020074203840840c10b80203a0002905002c1b02015604203a04224150a104410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 408530737 1250 408529487 408529523
    0x40b04060c030e04050106081e061e12030307093f062d11040f050405090709060e06090f070906080c040509040503030105030c0307030f060213030b04030c15090f 71
    0x81000ca0443e6513205280c40000101a600a01e084c0c3c0301d4141a2a1001100002c10701141507900c15a04030350400c1507400500000340703401540e02034401004013801c005c080f240c4190741c55544200c034030300c0020b491000200100d0402c4074045a11108002d0101040341a0301c0351108803490780b0040241c0300302a82110001d08c03200354070400607080c186100269100000b054403641c0c0c1c0c44448802505840c181c24049050106403d0701c2c151004442c2d0600102d01c0c04c0c040002615000d0941c0c0c845004090340041c114900e4400c0200a08140341d810b100c3d46000d10810101d40d00c01800020b00300d44250420015980c09156102a5403003418152010740368541900c2a80c080c94110035003169682d81801f0521070004050350495030100c08403034854001c1000c1c19281c003e207100080c000f0f40d4504181c070000c0c803503401034990006c0e1024000e600c242c0c0ca465240c40d400c0103036400d40100e24002082e006128242014212a01d000c14003070220000c50303502c2c806107011506003c1c003c80d2a240c095601 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 408531987 1250 408530737 408530747
    0x1514090609060f1207120e0604020402070c0e0703092603040b04030201180302070e0105030a150f1127040621020409082101150906211112060303040b04060c03 70
    0xc15440e003001c0a4540c42d01d4801000307502c10aa50a6001c030f86154072840d5500311b07600405403d0b80b406400b41a55440710307800c1c40040d40100c04215219a00d90703802080207040c04d81c405102e80a00d42d40421007080e00c1c01c050740c02e11038120350b20001001044c91801494120011242c019604c21442d20142c0d442c0d04049004140c1d21003981c902c1003403225108185030f80098580c0070307282e801c00b04144699a80e020035a58160740c0c0d83c01405507991046040480d24141c0c8010400341078100d010800c004010242400e90380301000d02400d10040f0f4040100019011241400600d000d03601001b0081c02c00c44801c0d1a206e2510000310740400d050952821500c50750000190158060400798964100c201800d0090189800b110036800340d4500000d01c03400c503001082c2d4640460b07102d404100b03081a20484000c030501801c401500f03c0ca24074040140030031710517030401084040e400c51720703144c122000d500761681c09011184281c2c07051106010707044081d81120111501400c100c040850b69240c03c1d28 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 408533237 1250 408531987 408531997
    0x3210903120908030a1d1e01110c0901230a03021507050109060e0c101713050c03070305010e0705040b0f0405100806040b1b07050c0909070f0807151409060906 70
    0x10040c000800c05e80401908064000103101120926450818280007807107141c1d180c020450b281004241d08290455018207038018203282c1c0101641c0d071064000c40494650071007a401003000c840100010035020100d9070403889c44c400c01301c440c81030352865500000c0c482020b1100c601c05e03403140040e440080107425404855480d6101400344443c1d01903c0b11a07442d40e04161b00140141190103640c1ca0384d6110f1840d071080c40d80300c802c4800264442094000c6103803446030088a5903c03c0100c002180d680400505005521650000c03d83c02c11844056050a500b68400d502540c14414048442d0b0b49807200d242034141d081d035001034199038021306145401502c1c0c0c0024420b0203a0300501003400348045c100381c8542818170941d605123400c1d200c0041644074060000e0b109030490700c5c1141c09403401c4403c098000f0400c204441086480e005481036034134080d070061069a110740c00c01c01660020000c194441055030074403904056001c02c62440504c0344070303a010300c91038001a050040e0398901040d0380c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 408534487 1250 408533237 408533249
    0x40b160c0507051306080a1a07140d05040204020f121b04081506030c0d0308040b010b03061e03010b04150510050708030c070203030706090303020d0e06010f05010309020d02120601032109031209 85
    0x144100407d803c0850103246140c1450500503840e80002d81c959000d07a1420b4043c030000c81c07400e460301040001c404000c01c405802268080d40030800400c502d0030410240039602d00c503080c207441504203441044c1c01220f607a85002003103c001c0c00108422140455500d905506c000e0070090700e40d4841e40028204240c10742401c0c1c0c0300f104c0014200074594002d07132141c0700d0b45c412a030212140e600c0d40d80e440c80e035000840c2c0e02607202c0c46202d03c003150303d169000c144410000c041c00100740e0564110028060321102d040e40344102040c0c590409c40d62a00324100031144c00d40303007801464588a600d45022a21005080c00110791002902c0340854404100300c2c1d00c05030704880d00300a401003500e03004000c1e6120540003840300e4107284038014410004181d46040360644040c000805191400640c083c2c209102c060f64052501c045a1015032607140000b6003004400d07018201d00c2d81545803141c407003460007400c12401109403a4901c030843c1c11814202c10780390441401a0200c6010008a132401c070160805 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 408535737 1250 408534487 408534493
    0x118021b120408010605041e090c03140d080a020903030405120a020a0b0a1d090115051905040e070c0507030f0212010e03090a0b13060e060f03040b160c050705130608 73
    0xc4801c100d141c0e000d482624075a4001380580c0b5550000c210503a05103e1701e03441c003502013490480807003000343d1202032624821650040219644d0f11421a103800011040800b500200c400300300040e4800d514681c00421f1210450900318980e000c80d5483c01140107590203200304404142c0c40c8101006410421039009111555003516020030052580100094001058051f1405000c501002c007100c09103050103498852107a01c0c01d18081a08603c0545410500c03404020000c0c0c905040341c0c403421504826125207955a142c0154010b001380014a40010007e01200c0040001c0c00411184210790300100034501c0d010300340c000503600a644600ca40c107650320301b01c2c2c0c49029250210181041c4002240d0246c41d8940e42e1520b0000c03441104018020119800c03003d00c0346a001d0440f40c840c064002d0040343c2094120640840700350b03c2950266800c615007401c00145180d2520304101100e8980741c03421004da4240c0c0d4055485c4014000d940c440c01d4007404030f02c01c408556000d076006100900131 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 408536987 1250 408535737 408535753
    0x1c0507020307020a05010c020108070516170301050f12060f0627060f040c050d020f040312091806080c220903180e011a0702060403081b070e0118021b 66
    0x69942c0d03109800c100e01590241100044540c0210700b061412901a11240f081e6a82c410301107496902000440c0080340007070a02a010904040528078291380c4031000ca41d980d41081d080108525000c01c82030b1050415400d080c000300d1000c00c03d16007110010589045985404000a0414000303018482d85200342d1700d00460503803c1c0c9c3c0140c40c01034009441d0810f00b5100e0304140000c1d22914030000c80850410000319030741003050b6004102c600d11001010341000c0c0c41e95500c29010140e00d440380005120200184405c009a249034450103004420801419103440240c070f0311040313000c0c400f80c4510000610300e807d04901c0c0d0303039080d0102e50100c801c1040000c0340c940070f01044420f4054140180004601283e01e001118520707040c0c50000c1c142911506c11600340c11400e80c0002d10403070304180c0c10b100020014552101a10945c818164032800400700c00034a82d02d44010f9034000c3e400c03650000f004010f403085c001c00741d680301046120050707a41d0f070588200b540e198034204038050b00ba2040c250 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 408538237 1250 408536987 408537001
    0x9061914070f02010906110c09040507050a0308120a020901120c030b0402160b061e0909121303060e01090b13022202070c0608072c092e0f0306021c05 66
    0x25003210b4451003600c82020303490b00c4043c00c0310114241084c44074540c1c061234008040b4501400d08a521034802c1c8101d40072030b51100c011803071004059004450394030300071481c541600400900c030340d8480356000c0c0450900428100081001040341c40c2191010f41d190840c0c008180b0035003012401c0308000d4425590b41c580d8007a0030ba80059046030641e4514a030790f011820b0b17032900725070303040c8444805600007400042e45420008a00005008086507100f041e00240d031a03034a4401501c801c01c1c1c84800d00390001d1444c1440401d5031081025103030145d141c2065140001c4015041c141c02041c50301d01c410001c5040d1020600702162400880f01e0030000041c181c40c68941a0000e1981c140714491100c044e56480c10207454659054505001240d846030101d1641c01c41e00790001c0c29a82c0e03401c000c1a02d03060900105080c0e210658403c80020340c40c00c0d009010f00010703407004200460300c01000c0c1030589010300c501a98809800000c001c1070b0000707040080c0360001c81c1c1c08800001c2d9540100704c036041c201 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 408539487 1250 408538237 408538253
    0x81608220c08030307030b0406081e0a06061d0901020304210314040f0212030a0c060b0a1707030506090c0d060e070b0a0804120c0b07030f1e060306110906191407 71
    0xc51910020303050034201d5082341414026002200c0c520802001d9120502000d00721007514184840c01c0c81c898445d204012815500a46d8000d00d03811542c07000e01800c20b03083c0ca0181000605804c4c1981c0100240030020300b200020b0101104001ca0340e00300000e8007032048000d0b03c1e1481044104c80078407020b000c180b01c0c0c002d45006540b807085994031202c140490006840f80681644800030030021301030480454440c1c1c000d008080001040c030b003006030311030300707104d00e450710f04005048507030f11009090040003410403404d60000150001008100402d400248a030034201c2e400508158442041c06042c2908014981c0504901049161181c0c800d00000300b00c4034040b50141d032442c1500d40188016400b41a0000940e0b0300041407521a070350700e0780d00341c5c040c05011800040c503554504031410380c40507a00703504802252101d030100e41c01d861410310784190386000780f4080b4002c0f000c0091032201c0d0b95010407141511501544515840e030010f1081d86d030042c101c0300c4400c8207500056001c0800400e9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 408540737 1250 408539487 408539491
    0x94f05010204090e0d020a032102070503030f10120305090d0b090d1211040302040203040c050a0810050114180a060905070924090b090a0b070b07081608220c080303 72
    0x43d12040040349203140f40566181401100b89000d030b04030043d4038011038070500c00d08180b032200303c2c0a032405100903407060040341e116a0003074445070408814070072111202c040082e00528901a810000c90903c103c81c04000310703c81008050080000301402c0c1610740d40240316039150000305655280ca0481209500c51005506000005000180e9160361203460700c550040710a2300c070425400c003411a0b0a000080d40080d0050301d4025400900003866511141ca0708050f064141c040e2a40348040702e82001511750680250003104030b0656488016101c2854103080c503a5404175490183d107c2220300b0700140f41580010060605001c1003102254000000c4411901d04d2255a800c0c00da415071440604014036403520b00240c02c1100070070040d03001001130b06910304020036010b6071b1036444001c514503a2110004071441c41120040055154000d4601640311504401d81c0c05400d4410b00d00520740070004194040d48003401101e0454036443c45000b02e003a581c48114500115115460300307540c1d401c2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 408541987 1250 408540737 408540749
    0xb04030f0909140c030a180303151a070303091505041a010902090a0303030b041e05010521060406090f051015141804022b02094f05010204 61
    0x94a40020881d4442c414010503000d40c208500c40780c1c840b5613440710b05900c01381100e0a901c2d00d0318003100c1214406154010045d01c2520300080000320500ba984c2030701115071142c160307030007000e2020001d4000b81e800c9880d503d51504d000500c0511601e0145880c075811100610481e213850308001c100500d0030501c540c035040c403104030989a0307a00c0780c580c4107a00c80c50281329000206201e0400019000741c10962915200500100724141241903c48098400402c040030392501c40004004500b00121100303010148004020803528162500795a205d501030300c002d00166aa0440b482400790100c83c3c4000113512a043e031b070350f400c00c0d5888800030348450342080c81c222061420014402d00e2152074640c00c0c2801501440b050040082c00048031007000384241e802818003011000c2500030b160702c0040000301c24844070f20901d100e00521500d944000c02c0da0380c10b00c61405400d00103018a10f10000c000503a201e6404000d2080c14801000303000010340c41c3c0c0b900c0c80580b00d101c00c00c081034000d0016148 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 408543237 1250 408541987 408541997
    0x409050a080a120e0a0b04291e0103022b0b0c030702100b10110c150a14030f0103020d0204060806182812020106120b010e0a1a011b0b04030f 62
    0x841c0d01000044070b0440d05402c0d01395001014031070004002c06199070380705008003c0b100000707c07452100c1048640300e84003050305118100c1008030382c01d6000603a0240642a500e4620550304560204420005170000801001c50300482100c1300c0001e42e1000c090300c0d0340405441502d06121124042c1c3c0d40094541c100540240305204440b03049038070952000080080c568082103511001c00e484040365a604109540660b4125a10355181c0390b2410b881c2c0c00620441c142c0c4c882e031109004114030700c012020311368048100213101d0314010000d2041c3c1500c0e0110759080c0980340c0c5100080042001d0703400040640174a504001002c5030036615510074201da00280c0e00800d02d2080d450b5112006100c0e001c2c0c1c400d60340649200401c1150442c0840141940000100951100d4401078207200d01d1070201c5000703030032000510100300182040703904152200400e11035428200c0a841d16000441c180c90304001c550003140c400b2030250040010a960008680340c1c060034581001026060454040b07004a2 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 408544487 1250 408543237 408543257
    0x30b01050909010c050d0b060d0c081f0509180c100908070b0f030708060a032f091501110a021810051c020919020318070602010b06070b060409050a080a 67
    0x4107041c014202480382581d1940c2c6081c0502100303100030a220487e440d040340091144a1803034855100d07440300b0700c070f16446ea18440d2803d4100c05c86031407101030380b0340094a00401c0c20131164036004e50494012040c00300c03107404200b4901c1e100385010003485280381e0000003100000c0e01140c11803104400c0d07400c208151900780c0e0b22440e45408600c01c2e14851099030208000180b02e052241c1190b0744c00c42070040002c0704540d5203807200400c1000c0000f0185800c0503081600000b40080001552440c1c0c09441c0101c0510300103007101202c40e50703c40e100341481018804000040001d114220b12650700030500d10303d0110100600c00300710701c2256102c4a01900300300110f07940ca09080c544a1078900c4001c40141081160300380241c280c005089080180407561000d60b110525002941c4140307181c004c0006107031142103406140c440154048000e591400c8030008040d00c07908110f61041d600050a40f4103522044003040042c1120840607105000350311404041000040045c540340340c0540d40d18440c0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 408545737 1250 408544487 408544501
    0xf0106090807050918010b09070203090102010b0a0503060a1d070303030906050a02120c0c0a0b0406021305010905061b10020406050a18150809120a262701090606030b010509 76
    0x506501d00440d0744c4686950000ba908008910304040324a240d0800402c50b100480c0110340400815110200940c1000c1880a05075038240304100c005481120111506883c140110b03480f400c0140c981c0c00d0b60b50312800103500c02d031340c030729680c9005088250454140d655281401402401c0c00b0200301d0342d540c189004100c0354030040c02070398039144010b145200d442e116000300b1207a562280344a040d09002e081c0c00100440c010050141c40355018040c0943c2d80d200008142c610503106030051030600c41c081c0c00901c03643c2c886d0400d603982c1804200c0c0c1c0c0303015000400320103450804811440042513000050201e6202d9000d8090a850002a150b80484111000d01116024040c0c040c500303c1d99025101580942d04c2407542c0c540020b0700c04180da900c00290340100606910002241001c64018208100200b401c04415041581e2050480380355050507040b46840f05a00d802d4a289034004c03618943c2c21080a45c0000e030120f61181c000c110503075582c40c04c102c202a0910030148180c0310400020cd20b = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 408546987 1250 408545737 408545743
    0x12050a0311090105032701050c12090a15021810021606020609030d050a02070b010806160c050307030c150f0f18050606130b131a01020d08040224030f01060908 70
    0xd02416104e0905607a102192440e94160304900c060040300c0411400407807810a00c6414058401ca04d00c0940e111030009030130402c0540900414515404040c102000c504c60400c10745102101360000740e6200f03010140c5000607140d0302121984040c084007410703002e50300040c208005140300e824940520b592000b003607840744401c941c0d42800e900704101d08440750b9110350109030b212000c40d4005007082100c0d15519860a00ad130070528665010300184140c03c4402c51612024228500c2e21451161035569100e440f80901030009090100c80380a240400000c00111502070b034007180100f00c42c1d0320011914020f081e01400c1c0300915403400d805041005242c07128a505290450014030860721400244500d50656200c410200740e035505058850b59903070f003141400d1000008004c01d1054000041d410b803814414035240c155408821440c0c8000d400c600100d40c0180c04503a8030064008203480200318409007000741d0402040002001881c100320017589040e03400d00e540f40200740b616416102c3d5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 408548237 1250 408546987 408546997
    0xc10090317100303051c0e0703060506032418060a020406030b0927120c060a0507050705060406020d02120115111204090e0c0d2d1703060d12050a0311 66
    0x100c02d01c401c00340080381c029001001c2c100d075003002030750542c856003222000f16505081c4042c0c040d00814010402c4c02070178040d690300007104030090109240310302c1944800a014200c00f40c0c014403602c00055216030201c80c2402c14030028810742d000c0d4986110071200941c8180074030340200b40f801e591040c182c10015030302449604c0c0303c0f41000c0b0350104411103110720f0302c014182031440c0c40341c610422030424488024010f0400403100404003400c0c4402c07400300340c4400a0820003001014880180420030004215805c1078200b140103913075144060440019201ea02e566103c1c0a08000000a0030301c81e0b88034030490310409954400810000344540c07a101c01d03400301c42445009091200303000144481d40501c0784181100100c6021808001c04962180d2101205890846c440c5d45a02d41c80400320015920303020303201d16028a6105d140c0c1d51013042d0780d20b002c00c5a4051070048002001078484c83c0c0000c0c8510342100c0355007180c02d51035000901d01c1c1c0c007031007040b4002414881902d020082140640b8 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 408549487 1250 408548237 408548251
    0x71704060509010c022413090b150c0a0c030f030305091c0f050705060a290108040303022203060501180905070506030402060f031009110a1409060c10090317 69
    0xb0301d41200b0400443e007460703101070144da0140d212410012075074010404c3d09100c80841c0d4519413928111210801595910340c88a661141880390301000365a0300c000f2441c0881e01001625111003103403001c180f42c242054401448244600008001d00c10010b0b00c0e1001184641e43c14011640d61081c1561940d00400c0030340100940403c0d0010118051b084003d9042c02519241c0c3c108482038070750915052040d92503e01003a5114880074a03840810090134500c0000e120580301601d5142c0001d240d51401400a020590301048900c8004002003007000122201a01c051049440e414580c0041000b8401c0712101d0584002031501407005008a10529402c2405081510f1030701080c0000395100030012a4042002c02458017510001c40c05540640b403105c450704061070070051450103c0b940c0c00c105100f010010b205004010b540400c00700425030540480e1502c1d40c01480c0440c109000302c20280e1200e002d0141035001d01c2805a216014884c003036602e00307442c451110141901160300340c1e105 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 408550737 1250 408549487 408549497
    0x31207090b0c01090b010b1c1a041103090105010b0a05040b18030109050f01060f03020f06030414070806040c060c0b061002010e0d02030d140f0703020702062106130e0c0f0a0902030c07170406 84
    0x145615145d6101d0351442046c9d00c24603054a84680000e4200d03000e0300806188040e000c4240700305c04030709104460140070f806c03d040e807401e54440d1001d842030145205003100c444000030552100c41c1e1504c0207603000103028009200e188220301e0140e49820210031081015032801c580003480c2d8000030440e10450740c010784980c007011020002e024265000402c10740c2c0701040c6210386513455104100040c001e00b00d000180c2074502741480c00d0540c4401c5a442582001100e0020b4404200b140b01c405030014405c5803a00810702c134500301a4050704159000c038219002e074000c03001800e60040001e000c00340003200104051090340040c0c805600065503125211040701d000107a80d24000da00401c460f03030005080c142000d0351a0010b0902148030005400031040307d0040c400369081a904104a0006044044c09103440740f4070001e560340c0d4840c4015116481180f040d45194449060680185c04005800c0d541c82c5407500c05002c081e03001060480b00c24444107900d4a0b28100e1200f5141503840540d11 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 408551987 1250 408550737 408550777
    0x8100302130b0603010807060306140a150c120e0301050c070c120c1a070b0601030902031f06030c090c0207080d17190603060c020f070305031207090b0c01090b010b 72
    0x707000a0310100429141e900d961000003203001c1ea950005136001300031a20003402c40c0ea041070382c010b06a503401c0d40405007140b60090100040e03aa034006031410384500240e1010355112121048908000c01000039000303548803100c20580660000342e00c0d18a26007903000b480303240c4920440c24800c0c403406034044c0a0604410040c80214070403024042c80d82d00503900144195201c0c806201024411030034040c1c40311000846408001001c003810f680f102c824202000440c030160080380c0c9980c02e01141e02c03940c1d000c0707a4802a02019070383c880c1020b1a001410301d110030340c44d036650034001c0c011008000094418440e00007408100002d604a001e4655991904050390b80e4540303117592040608000c008041c2c60b003003510105980e01c0ba0341d00450080c0350101e204082600c001c1e0510803042c0860105411150050001c01c00002c1118148005040030407200e03a00c25100316a0f800f4642c00040100200050740c4c12650415005402400d02404941d85140d0340e410b1032940c0c3d403181c0d4240d01042001c282e4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 408553237 1250 408551987 408551989
    0xd14060a15020a05030f0a031d070e0601050f12060306060901140f01030219030606030f0c140c010b0a0608060901150f0311090a030b010e070207030812040204060b0301120b0708100302 81
    0x70104040094012540800c3e8540d0301d060440c0c00482c007615240740c0100c0d440c040584e0601814588a41418810b000d010081034141d0320380c0f505000316080c180c00d03203000c02e1850748100101c0d030b000581d00540d41c4d00d84803911401548080d050381d900d0301c42d10900300410040d1812848640c102c0301c003144600303491048042408113001141c0815410b1680c00c0c40485480282c4044181a03551666000a03c0a0030441d02a04950740c941303034201710303d14008801440c1604000129141d805117800d4941f0f4000481c900703405401c041c410700f50000f4050500154403500a0003560040030212540a1aa0b0321f66540c0c0c070690030b1382008000010004070b100355109000ea44203004400c00c03203d109140c01d5808000c501c040716242e008842e800301540c0100912a41080714030b8000d142440607001d42455500d8180b075502031201000d0641440c200030074115a21a840038005201600c1c20395104e60b522040001c0d200d280c1340e015508100008000f031035251084012034410900211802c503500d0944d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 408554487 1250 408553237 408553259
    0x7090e0604110109030b0f0610090501020d05090402070f211e0807090e090c0103140705070b0c04080105160e013b04020c0708100203041a060310110d14060a 69
    0xa4240f418040032030030110108407040801486800440403c0035141000c45c203000b407007118103000b4410032841e0b85c0c05201070380e030100ea00d035681e0301d5030714020381c940c3c1101c2c000a0080c400c54200602480700d50221004202a001c20300100b400c0340e0300580f18000c41d50b00159524000f0010300f8216a5031089002d0009020369012500000340386865801c99403a10140c0982a070251080030541d031001504100c00d69150103511040403180d621a02c280c00c124030b000d001d900924a00a00c9003a400000848106441d03003601c0082c44070b8002801203060a104401000c406134004500151940303031f0f9114154010700d008001da6945000302102414085040e410503031040011445000c140d0081090907511400a0003035607042d103000d0201c0310310389407603945006c107030100d5200e2250051003004041602078118000312070b84e4030a13007500d41d92030b58006824154182c40603009146031240000022100344007600500741d612500700306002c1d103a101d0301d1208000b10f170b902c1e62201a40200b4091801da00b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 408555737 1250 408554487 408554513
    0x103020c010f05070905030705120705040903141306140702090c0906090a030507080f060108060402010311160605040204050a060b032a04030506100918020f03071206060807090e0604 80
    0x32400012070000300300311001503070015a1a6000140000d400303100600d010f0004000904044804410003414800d025482d0130a520819110310340e00d40c8050203060007940c611070780765091900aa0740d0365103000090510300c168095140020003140c40035404410060481d460590010007140e0700303036920050328201d030740003416031a08820240142c2c5402e8403100c1d041c1c0050740c460f202400c1c0f09810090f065260001071043c05072543e1019004006040e070104110b6007103a0203280105a01307580c065480c4180c1300d50003546014501800b651014401240d200340c1c065403003210f0500041e01d946208100742c80c1c039402083e8203d41c0c00c10118901250301113800d0448282007064403103014407007103520400c0e00158010f840580240c0200080744840b5001440a4102c2110400100320040100c0c1201c1d00b42c0344009006800724403a00849a50800c0040000c2c0b040c85202040e8208a190040c082c01c140d03c1031445070300ca070200110704d84030039004440e0450040d0b00201010f503034680b6000034001c1c003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 408556987 1250 408555737 408555757
    0xf0f060b03070b09120d1d03030708031303092c04020328060c030603120f0e0604080114060603010b0f0a090b03130b18030d021309060306060312050301080705010302 73
    0x16540350400181c4003031000400610610a043d0344442d00202030040c202c8100c03481c031071160001c0c9004103c0e15003101c901ca410160403c290601040700c40082880c6109440f4082d2070075901204201c48544000c0c90906050300c0f82c2c2d030705030000b642ca49080740102c00c0180f130f41c6c900440c010702e1100c640c2d40c820f044551050009040b40e050f4881d54a070950781d001e40d9028550010180481e80c000d02480e030158054080c02c0c3e1030104440751468441401d2420b00c481d98208000b11441e20a40481c0b01e41c003071304d103451401480e4135900d40d07640e4005c5008101e206400c80008251a00042440c980340081d00e040b02c45520300c1d540b41240c0e446c00e00400b40c2c012202602802100d0002140c0390402d0310103107200e58201061035a143c0ca19003400c0f00e03040c100510504c558200da088400341c4200100070b07140318068003080540c07686001100c0d61034000d5030f03400400840c3d01e03090000092000a0300700e40102ca024001e07403070042c078144404032124802409080c4641d8002d5000f000207512039402841c070294 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 408558237 1250 408556987 408556991
    0x405100903060906092009160203093601051e1302030c120112050c010e0a0503100f0b0d05071a07021e01140a0e12070f0e0718030f0f06 60
    0xa01c07552450b00711000d90109898007550741800008004005031050106801038041c0c40422100c100003440103200205010160504076000e015058001c20070740e140c40300001e101d000400c85000822180350b2200034044801100c1e07a00f0503141d5005100c00c07034142c81c4041c00c20149084411008140701ca00490780a400c044401d480541d245180c0c4061030180c041d4098080c2d64031240d1861007a50003068001c0b000755040141034100040000551044510081c02d0640c80c01d0001c00020304210403503801036415001d6001d0701e41c41e0400b180c2c811501400130010800c440391903c01400f0300c10056002c018100d40c000f110612808180e10216480d9800280c0e600380760862640c08180100e0144a45050024151a10500b1907801c50b0141e24290700650415041100e000d000030100051420454019900900750004ca003005010316005000b5001d206800c507907940030542080c01c030486000b000a11000803c0000001c0c621020040382c4d08031000c0b59042c00e0b1511580880b07801c00a04813038044e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 408559487 1250 408558237 408558239
    0x70b040b100e130507050f061605070906080312070801050112050405010f0f0b0f04020306210307050a0f060e07180b03070515120618012907060605030d03090804051009 74
    0x140000b682d244604928405410788a01c1c0385041850482d4a40100e4481c0c1054182115240c681206032844041c4605003004901840d062103400c012081d040513201c541402400b0808000002c0280300c5d0341e0349800083c0095440242c100d50320b200a003c0c25002688401c0301041c0b050050300106d41060107880001040000c080d07824040344c203114039850740280c0b60104a1031514050055000c503e20540c1c09520b14501480000d1100070b011641085c031040d00c248102082c84104141d0304030a81c010100c901c83d0300e06040030182201d030124101c414a0070440034485038034010816104490b40c0b410020420104840140301420300402c15a40601c900000090190340d0b5011503d8407038501c0040959074401700100c1d08802030010100e07030148404540c014101e8450f50410350441c0d00700341c0c0341170362205070310860f071079114880b290b0050516000c5600001d002c00ea0344a0341c00c6070400c4003141e05100c1c0007101030b01591880c840103403884000b80000c0000f070a082401b8040c04c00c0f2850244052 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 408560737 1250 408559487 408559499
    0x20c0d0519030c06150605190e06070b060901060c02010c030e220c0201150f060c081209010204091404020d20040e0c030d05250606050315070e0105070b040b10 70
    0x714807035281500094076041c0d82805012440c45941c902c000c40e1000d00010381c0c14410090143c0c40b8001041941140d841131100545102c2d040040709454000c08027980d450040c24280e040308010b49046101c8c17108400005816030052440300e00150341a16242e0343d0882d41c3d1001c2d220101500001c41d00040400001c840c1c0c0034809440030300c1c004650744001040340d00424002e0841d0741680140c0f046d6403101e031007441092001818801162198505552410140c1c85d0651207401030b184806c842c0c4079241d00f03010450358117401a00984007080340401c0351781c68100c841843d255050b00d010350000394800305039001c540c180c0300310310ba07034030065031341070101c181e1040840c0881d110b40c130160007250840c44560030b440c03800780649c0c005052140340540c14078824003d025a540c41d1041c048280c5088506594200280d0b0740004000303180c02410b4440c0352041105011310380804031074000015442d12200d500d290f020b401601c400e15044800e01103544e131659100310204402404052034816440c100142c8 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 408561987 1250 408560737 408560773
    0xe0705130e0a090b0a060e01050909120a0207031506062c0d1103010b0907051801020a021f090603152102030601080a0c050d1a0709030602270a030201020c0d05 70
    0x642c940036000a00d030300440c2071800300100068480c5c401c85003040070420200300f000d071020307055600840300070180c1d48941503007a14218006001c0319240c440440c00804e00c1d5004180318080b60f01072a440c45142d40f451807420304403200c40c05200c0120702c0d4004109188540449007140c1650320184900f080d290101c006511100288004c452081840580c800142001c1c002c02e0b08203201540c0c000c0c40f031300704854007030141c1c054100309480d4100d90340510200b50b0701c2000641a0781c2c0c0c000c1d10450540d190010501c8194040e055103c011510781d06c7c0c0011007601c03d1080e009a06404015281202d0800c540b4071010321504d1809a600d006101c9004096502400310314000c100300300007002403030800c0c41c001c065480203038460741c8507144801d50075008ca81120301d60301070241c202006007650f0b40d50702030544540d8076541000d00f0461002c1408402c0400b0802c03c0d9060b01d200f05400d0340b901c1d004078100540907085000090042e000304c001c01006040020106c80d41903c200e0550300c13920755032240070107 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 408563237 1250 408561987 408561991
    0x50f0a0e06130f05030606031905240403180b0d090206040f1409090d02060403211a0109050f0619051c020304031209050d0503060109170c0f01090e0705130e 69
    0x30907480c2d580000c01c8010300b031000705001002c0603070250100e8030b030503070029860303080c501c601545544004c114002088814008003030440c00088940d901c0310b002c40300048065a089a01b14040b230780100004142440c0d5000704012a824010f0b1186080d501d1401f1401510f494001280c00c01405e01c0089000c0d0400901200504030401c0491200308601080000302c0c81e01900c65001900410140d40c0540c3e4040b80c0c2d80e61054240c10600201949607007514800460700b240003400760300e80f0410b1140010408075850503500242e880c0303603801c0c1e2100100501020400907103039001c4400c1080c0c11000058540751034400a080c2015420009000c2c030f41208090703c1c1c410031111650000402c41050303004522007000c2820380d00200b0400c94944c0d989070b030711555414081c092010100c00502c00741e20424082d0040c250099103520841d54080e0f00380e075a81131001c40c1d1480342c02800359002d025441344000c0302c03c4030310101c5900403a46031808103861503130114017a907241c1803100e031001ca511442c44035a94 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 408564487 1250 408563237 408563257
    0x30102041212090f1a040b03150103110c030d0e01020c1002040906060e030a020d060219020a0c0603020a020303130f0206030f1b03010807062007060f120b01050f0a0e06 74
    0x488026418544945031030104a00802800740c80e080034003180d213000070030f1010707502e42043c40d8080700344114040005000f141d1110b05030110000400a010908854585524400780c805202507483c0142c40d6200303014210b5a07001e55481800040303842d0043e600300740daa02e0f01d0071000500e0007801d1004075003009090f402d070005503500050f0404c8107066921408004100070b150a070a162040030001c2d4031924803c84c007030b2042618101010500c100c0d80e0440e001200d08015010648800c0039005c3e40b103580d0b442c410350324003500d19400103203640a402100c0540102d07502031842c66894201015400d01a800c0603101090554801401a1a5030700210300540c0841003010030340c40c091442c548032580b409601c58640009200401080038006030f440e040c2d58180c01c00c01c050300d21450741d0940314050749018640510550744000f840b03075040a60384600b00360039a103440040c44c105100105942407101805d00241d000c121440e521400b04000c0c01c13690080e131401c80c00341c041610000e06035400030b800386 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 408565737 1250 408564487 408564509
    0x70308041e120e06090f01030e0c06031023010905150d020301032f1c03110601060305040b0a0204080c090a0f0c0504080709060b090108041b080105040b01060c050c06130503010204 79
    0x200702c03440e4204154405810341124120728184101001c030311501d4003044102c0c14561550340684420500b032104800c031510103003000b5241d203001d003180401e43e103482c49004a10958040c60031416001303502050b0202006850f12201c8600d00341c2844000c9190382032800b00d904040c802203c44410600045000b0f5014044a00c090044002e0f041c0c4040480c5c40c156100c18132040358045140c0320800242c598286840d202618075005040035610b0040b007407010692030191758000700d0303942d8252744440d0260780940841405503a440340004202c4c071aa0103084a151f001441041031403424500c101e6102012403004242c50840c5188401038480c850408404514041000d01000a081000c07200070700605000b481200e180494a507e41e02c00c4410312410802e1420004003444040c41081c4209807201c1c11614806076034080840c02000300ba64201c81c0d44000d0000040d940348a600102c9103545c210001c1c1c4861081241040381e0340d40b04803203031a485190000005081d0382c083c400b41009103d12550 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 408566987 1250 408565737 408565763
    0x200607050a21020303090d140408030d0926090d0204020c010c0903110102011104140a0b0c07091104141221090a080114010b0a02100f1a15070308041e 66
    0x9444964210b06100008544c002d00801c009403000180f0100d03503a4030760070880c0401c1c10164034200350344116000028a480001441550141c00ba8070050341c25004412040840f9001e2201032401d0300d40b0398100c00c02c0c890501208505182010b1a1007000744010300c01450826001141429140304c3c48080c00490006441002407180c05907400d04550403d1000704120b811100f80b10b106c500590140d0503003000e41200c071b404140c9403040751340050a0302c145000e445449419981e40c1d100307024018030340080d0920200030140c0038107100f5078003a41c41407400000a80b5264042c021a0172000d46003800301d115002400c102c18a55000c0c5080301c440c9140720a903509880342c1031213100800c960100081c0c0e0300d0561902c1c010411a040a4192140c410000740c3c0d40300d401c1412071510090741c1d42c0000c21403034008108003801c2a5030040141c100c000410351800040b000030400020705440e18107010038410402403002a00c10004290300c5803041003d115241c006913010301483c0039000045030303143c8200d02 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 408568237 1250 408566987 408567023
    0x9350a0506070212040e1003051e160b160f0804170f06070e01080405012004090c030504080f1b0d0503040506160207030f08160809040e0604200607050a 67
    0x5482c0d111580780010510400c44242e41c1c0801d1107944604030b0095101c101041810050345200c90083d900542140e80f1442000340403221812110907540561103468550402c4a0340c008902d001c8504c580005824074a014030003140c100301000088640c0450304a404000807243c402400143c448010075140038004601c01c1403030010b01840003101030380f000702000f000c5035218038220741c181c400b0320340f1984a84851420501414801c0151141069540c0d003040c0302841c50380107441110004241408080f0520700e080c2c0c03c0740e0054401400c045c00030800e6429a580150080501409403503440c00306440b002e02d41828804103201d0800014000024001400703000c1200c55044990000c043d00c2c40c8400001c00b039034070b041070f1000070542c503c2050803030140040c1e003094641d80c000050080c0102c8015290000040d40640354203442149410450250300300002281e5100340c1d401004000e8440700b0002201401510090f01a80143d0401c501000140c0c01d1003160526072040780345401c1141070300 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 408569487 1250 408568237 408568243
    0xc0a09060311040b030f0106090504020f27130b010305150c180405270a0c060f050f090a05062803020a05070f020f12030301080d050a09350a05 63
    0x1500800099051903030a00215a0a410490700960b04903000a015002c001c046803c10f120341003c00415480e0410004003040c05400c110300c1144200c2d0446520725181c010001c0f9203854040510702c0f50400c2a08001d204505002039801a04c00c0b01301101c861040c0d078610107001c400340c00032070f465040b4000caa4007211074071401c542c05c00054134026041901c184000d8013180d03800c10707010703100342d4032107000c580400c0303c0d80443d40c4074000c0c1114806810b10b50040389075a9046040045441250340c500001c0c00d139106004464140c4544e80d103442ca414180e030310601d02500510080d85c0e0280ad0144005a01d81e110381c0100b2659452140d00c203c419a40380c4c820303a580282541e007606050041007001383c032582c8141140e2145034889200720310004c86002052003038100444442c0c00604000400c0b107460380c000059412200d8140840302c104840403c202c5030742c00f0700801100805c02c01d2105014140005102c1c03980c03540380102c0c0072041e00030094049081e8050350704001d0070350002e01403281404414 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 408570737 1250 408569487 408569489
    0x602010c2105221a090c03030304081c06032105031e040804080d0c140307030f050c07050303040b07150606090b0d02160f290610020c03032a0c0112050a02070203010e0c0a 75
    0x12a006e849201101c001180d00da200c0104001c00c00300d0001010a600c0101500420040006041c00c1260760780764034100600c03074030b08030210100c56020b541120505200308100e901c50034006446000b01c5092026045002c04082d004444594090002003140c0317008221101c1d0050807543c48000d0700085090043d0211440ca20106c0d02d90010044d0fa40404c0d001280d011056a0520b05242c1e1815516a5603040c03801d2500075961600000900007074129400c5c0150807020300503401046034031806142d0408072802c91203013001059070540108495072030440506000d03080c2400152800c20303805450f02410181d80401c40c1c160002424030420f00c44021520b80c4820800744405a00a290703600800001500500305c92103580041c0100b02450310a1000c0b0a42c510050103ca440d00e02042e0038201f20401c0f00d1048507440e110801d8076412a500141e22030052a040c3c4a414460301024a0040a81801000500640e80030002d04006032002d1046240e00072608c8080e08081d2840c80400944d184a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 408571987 1250 408570737 408570751
    0x215070b160207030b0c070609150c030b04060e0f040f0f0f0309140112020a020a051905060919080a0e060d0507030e1f020a02010902090a02040602010c2105221a 71
    0x1c05070910002d000502c0041d041b0125040c655107600103490003001030301c19694002c00c14003044451640325031240e0480301c482425900d060000f41d1900c020311045079501c0c03090050300c2400401088405400c0011b003a00b0034040d8020b00500400750300c868101445400081300d403103000903503980a01d60310410f039001a00c50003a01052038084000020040c03000d072551a42190750000304401400e001b0460008001d500c5426240c1a0300701c0b410340481c65a000c00155014012540042e100c0d440101c6d46058011111450355010200c546490880b03400c488291420310200c065001c030301740c0d01e24001c1c2041d0707202c2d100041402d00c1c110f10001c1c142e8800758060346141d4010009110220707101600007c03074040d400c90050700d03901070310401c0f03026001015001e90000400380c00d003d80d04840750001c200341c030f4481d00280f002ca0f080c0c1208032036a0345400001c0d0519595115540aa50810b4021035080511b80401e5007059610310b4182040d90000d40003203494031002c16031925040b00342591180e100310 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 408573237 1250 408571987 408571993
    0x30b0402190f030e1b10050c030414030a060e0109061a0607021509040c0207030b0108070303140904060e091501050901151101020403050d08060f0910050105070215070b1602 76
    0x101640d00780c881c6a100c0d80ea000c05000310302244a003614800d500412911000b0f0007116a4180c900d2441d4207178011070706401e80140b0300d031a04620103601a1003140c09001c100c00040d0f01c2c00e4036080c020105104000a4194140241a00d00000c02e05c00d000e01c8060305645400002d010482c0c1ca4802c08591581d1741a4407400710100c446070083d504c0c00107541400d50140c4400300b0141c03072303503041c0286449842980e903030003460110302000d02940042d040003a0f0b03205030100321031a40c980300c3e500d41d00c0345544401000121a480ca04541c600381d4000303840000c001400100300140c85210b0242409011507444185502085002c90910842c0e61000e00400080d50103006a505011483c110884000c81800a22002036880b0b80c20b03810960480b001150020161aa10f005507000184400c90039200f0310b100f00464040f411082c03808803070050051981c0510340400900e880b005541681080900381e030b1080c821581c0110b07040a000043c00010310400d041a12440c00e000c2d80026880c605142c44110340c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 408574487 1250 408573237 408573247
    0xf04061b0302031c141302090f0c0403030e0105070f061a06250c181a0603070f080603150c120705130e180d020d021902030718140106050307030b0402 66
    0x3078000c4120b4800401d0030b004040d481c1003003403801000e03000075100c041140c049182004441a50b843c041d0903840d05c211400f000c1274481d410742d09140c070400d403603454103c00204410800a8022954004240300604100342468201d0316120050701044a00b5a019030321880f40f03408016681b1450b030300d180e8007116244e040c42d40032114000303081c1e4080c982000030b01d2805021000e124000c03507107c008140118500c10348592400c000b1002d00f0907100c0d50304001001252103529071400005a912481190303070303440391501700d81508407000840076140607050300a8030140ea410300b6141540c0c5118070140d10250b81d849031030484d10021050002c2c013080400100307006d110034204049450004035644c1e14207545440e00d96484000c3c1154400c28400740c6803207140e095940c41078020039091241e10043d002e0301c080f04603600501d000306e4084440254507800070141407040c1d841101c0a07139682d600b01980028801c002441c1544030840030307000b20011403004010813450315030502504602d40c0095030154140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 408575737 1250 408574487 408574493
    0x908030a120c2c030a0209280e0a02191a090a0e040c0311010905040212090c09060a09020d0906090812070302040b0f21101d0c030106050c0f01020f04061b 68
    0x442c1c0d1a694800c40050000c090000d0784c0d000c104440d00d807a0000d01b10794450901c482c00d6004402c1c000d03560a1300948a02c00914000c4940c8628142e02c64441c0140c103180c49142e0800901d1304490000800007943d9850102e581000e91182d8070040f025030345050b076071302402c01c10003100c1c0f582903229403221141d54040000103016000c00104032580100030050400044006840c0c280658000940152020403614808440f080010f801400a9010384850a64040501000c82c008940700c0b030b04880020402c0041108503030080020b0350310000c0000d5524000c0d030751081a102100c409580d59140032500c62410156510460b401440d03500f01146068502004c0328a14050009052007003880480d803416880703005251005000b240561100c1a0325100318041c12040c4a40103802079003070750000c02e8414001c0ca480044c05011b03c00b01d00c90a507842d044088400b640108007408540c01040c510f20102c940900182c410545141c3c004c82d111410600014001c5e41d26103081e0901d069205008008 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 408576987 1250 408575737 408575777
    0x1a1e09030a031a0d230d0804060f050424110a05120f0115080c070b0c04080f0c0a092a080a0506010c0b04170c060c0a020c120c0d02010908030a120c 65
    0xd4a80c0f280440420001d840d580404c0341170039181014243c000d00d0450141d143d80702003142c1c4620305c5a801040a034101a12000031104111002071000304c0d000d9050f000007051780745001802d42038401c0403441e2a83c040c8141c0303040e000350030300074042000801d184801c054070111181d804214140d00480d190314050704103403041c403010b10803c184072011000c159050254011244c015400229139081401c2030619450b45903c14402c50790b05029040822980540c00700d91480c01007401010004424101140c401c014604d0b0440c0c0202d04180100449142403000420311080300340f516180014603001200406403000105200e041040310b0310741720000381c0640c0800b500a40c0100045145802000041d061032103545c4e810507541c41024200001a01c1c070303800038288908664291030f0054607407000e001e244402ca0f159640280c03c100b942d10080e00308074812207505401450308800f01641d414640707065034044181480041c02040620031824036a00138240d18500c14500300d050000b4410318450 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 408578237 1250 408576987 408577009
    0x6061c060b0a08090d05040b0d2d0f0603030e040b040605030a030302181c06150b220611120f1b0d08011a1c0f0216110d1a1e09030a031a 60
    0x1a08050109d41c088105d906940002e242041c25040700c11110030b84501040718040c4003000b00300541c00c0001070360380301ca058000c04007103a9140d04c541c444003140780c0c100006004283d0455812076602c0700700182e1075804100c3c0401c11400f9480040c4d03180300c2d101050704540f50321f00c0f10074002c038500215501c3c0785801d0700383c0c0041c15410040009981200b03080a850301c21490340030426101d8080f070300c115036144c260490004540e000c030f501c10755580d44074401c4d00c4142040d418420aa08424941c410101c6004020b040d0030641d0342880e4540712403000710040c0c0d02c5032140301130400d920010010100355008420580981808101e002e00115030709100706941c4101444648600448000340b00200c0c4903820004000c2088817081d5120340900d03410b44810031186d0415070f02016020411915410a58040c0d0309254009000c04110503404081040743d01d40540300c412000816161214018000d16845001d4140c0102460342c651213031000805450782d20206120a86004070358900d20390313400b45081 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 408579487 1250 408578237 408578249
    0xe01031106031b0a180f080a080a02100204090203070305090f19030c0203030304120f0c0f0605040f0c080f010b0603010533040803250b06061c060b0a08090d0504 71
    0x340d981c0d607440400c80d0b6a80002c0b41c1d61001094003041c138040d4541c0001c41020290203501803100b0882c0d5030184140e080f00380d4840c600d981d130000010300001c0782c907030700052000a04d40d004907501c060740344000f03504aa029a001e01103c99001c005e104200ba0715000307031078012440100038030b584640490f5040e260008007000d0005900b01c41c01040c01c060103410710b8107005400034244d903101d1901d41841d51945400c1c0c1000b1001484640700b030b4035168001d0401009850300192a088109203030b685000041c80050002d1742e0b5400b1146c1c480c00020b00f000074141c003400109025000c41139452002c1800e5840c0c0b06841881010f051006110b40e460322100c07000a020000c0028900381000149000323420700c0510207074000301c400a0046181c0030000001c004514106a50b120300c03400d01d8020307179250f0892041c02081c510500c80454028038040d80601306c905c4402c03901c1d044009588000d013080307424952080801c084e011902100c4640c006c0b454583c080c840c80040c2500c00c912000040642c41640510 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 408580737 1250 408579487 408579499
    0xc1e17060411130f020c010606020705060c070311010c1b0335030a090f03020c0310050403051e0d061d090c010207060c1b08030705010e0304060233100e010e010311 72
    0x3c0a4400c51907040542403180c2c54000710360790050007518601a01280c01601c025100c2c40b5030000f21400c01764101d03064809282c001d0100305007160b40b40c66a0807000d600250401ca03941c1d0501c0e0114202005281d018011145460721481c5140344c24001141e40450f443d00c1c45440809211320002e0a9002c2062154040266a540e6a80001e000014041d411029044030645070490742003607000140055040411002c480c003c890780c8850324103a07002203d005000502c02e02c0380301030540030f242e07416099082c2c803c80c40b401d20901407010400c44020f035111a000a42054641101d4242c44405c260024008405440340c01c0d401800070395103400038892241045030f004085000c1c0100c0982d0300d10900b000c0390700c410201d40e03180312240d9203070810601542c0039480e00000c040310500006c101c804a0f40780c0d4003d048049100290f1403000c010005408544007401c1c0c4e80324011840f407003245840b0300d03040007800d2501350a1545081c000e1030f05070058142c00300e00c2001440442d215107090109400c1c210350b1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 408581987 1250 408580737 408580759
    0x50406061b050703140615150d0b010212270402250609060906020403110a03050c13020d02030a1b0807050301090207050309090906160c02060f03040c1e17060411 71
    0x6143c28040c1e800544048106100c1d00c1c1c401102180c440d010713000e01c00101c60502009010080c50700106012803000480400a0541a510070740240f142440140151000c510401041008950003108000c8170205e192841030032459010100c0041c0f28000d0300d0850170a404031540c9100d5441056080d58180101d0244000b0400103405c486403260b030104040c0000f4500345040f5010750024041219614100b602050550428580c4401180e4101000b80f400115405c00d0000400408210004c655000c00c00810005076034001940284100240060851040c4004000f032000c40700800080141c80b809100a95a008041d281910310102c401640e80103540740076807451088954043e04106e4180c10403d0305030002c01c40d10300c038205c25100d580c0751001c50b8504071a00d01070b9850080d0310000501c401c05414180ca0b016681c0184619a0783c403485840344201040094020300390311155040c1401401203081101140340c0869502000700b1003410103580b20b504800500701c200d0701035902294 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 408583237 1250 408581987 408581993
    0x20a0c0314100213050f010e030d050306011403041b0b07080d05060d02030f01050a1b05030112020102070806090303061008060904020d02040f060f03060e0f0d1d15070302010501050406061b 83
    0x441044420b4070148115a64020710306120600351861140c80c2c812440c2820700d48895000e034840c0d91030040d0041c043c201e050801181505c0e40e03000944282d042101917040e04180c60700d010000d6018a014110f448140050340c3e400170602d007201d80110110b08818403800700040c2e50030081ea046190645000b240c5030780c401d00856010b40780890302035031511900c0c041c8801c40380194130446c000c4420380b0050050805200b80803081d20400c0320000f0014004000401503c24913082042442c2c0c4144140c0344503c2d91191214540502034511003640e80002041c440d4601c0c00b0f890300b100b80301c4581040c1c1c40c40c1c034201d4000751020b000144040c0c0035103e1b0100d8003046503210743c0300d94801545101c080017410740301d00c100c0c8070112941c0000c07a411864110050303040c03075000468100000e403075001003892852105040760420140301c0107030701d2818a08581c40c901d43e20500b4401507440490080c9480c0e03c8107041c000d00352a8103a02c0140107510340304090080e80c1d409609000c0240001c29210704817071085ca = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 408584487 1250 408583237 408583243
    0x3080702030702151206011103070201032004032315060d141f0b0303090603010b0f0702030703030c1b060905060c070909060615080106200a12020f0d020a0c0314 71
    0xd100254048010b00c0384e666000d00305400f400400b081d51a0352440350744da10700103441403818186001d0541d441484050015071180c2c214689114164000c54004075004c1410103140d007003500110b035074070f08140d034030b00c4600d034464104101440781d00c008240c44c5d1840041952208409440c0902400084208100f801090b0350074680322941c1c5011102c1d20015000200300c680d00c000c0000380d807a403c01042180c1c1e0318000040d9032440400420700c034a580d10f03101e0030300a41d9010010608041d030080c4505c0c00982d40600983e0001c50003902d035074801070180d1a201c040001d00e100041d0035040f54031010320083d43c4c4801100103030b0b002030b5090350755111900c8001c0d2800c1042d6010640d010b00b0007003160300304a080e4001c1c204440e00d01400d000145242c035401e5684880900483d03000035401540c41d40c6901951342d07122484010801913944030006501c2d42c9505841c0300001c0c2c4050703441001c003051002e400700040d8041400c2032000d03000d401940e03504d004241185202c081e110740250144214007440034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 408585737 1250 408584487 408584497
    0x90109050711061f1d0c031b04080a060f150911281103031302011437051c0203070201060506030a0905070f050303120903040f090b1002031201030308070203 69
    0x42e00b01d449038030345602114034107901486010780346070a9030400100c40c1e0b4000b05c400f40f4110b6020042c51503036110300325180241c000400c16a08030b031850746110074600c0340c41c005201030f110348009864172612a04000041e92903032414002c1c0396280003d02003105034640c41010030754044050110f5445c00203001040c8601513400928101e6003405c1004c14224900da142d00205100390300c80c4480b0b0544100f50507164002150296036007112610b00000542c4201040010707540f406840f2801d00b80200102c2d03030810191411401c42d1030004c1c8103502800020703414144450074a2410a1910140181f8810ac007924550b00d0b100254010003c5201070b4001c1d00404054030019281c01d0316444e015054002a0000201c155440d02841a0114008038095404815204050003c40c40d004241d401c038959414000c11140c101e0006100c04103055210420380c0c0f0091031210f0020035600007000c100491060703a08074050555000300101544005990308040c1144c0d01414031448990303803842c099045101d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 408586987 1250 408585737 408585767
    0xa030e041e02040302090a0b010215100906091d06010609050118050414151005070f14060106020f06010e070c080313021527130209010507050106120512030103020901090507 76
    0x14a0300d241400d501c558050400c6074001c0300d01c2401c549550240004513051075400c1d900507001540c0c0042c0849110a0103030b007081001c0d000038525559081c00071308a42080c0c00860499071030b640d90340410318615104618010021001d894154500800604021002c5c030903c0c7c10b0140307104504844002940c0314000030800a0300074042c81c50500d10001020104843c014035403018464003090908244450b8030301314039180c580926290380d030b8039001001e41c0451802c0360b440c001300c0104062803200380141802068281c004150f040c900c5c00b600c50420304160001001c012002c002c00407000c0d8411614071511350401c02c1503a40f9102c4584445100b882c5c0b480294008005100044001c8403900090101505241d00c0003100011440d280050031500300c90f90f030307208030070310580e00d40d10810780e00800401c034050400700d14040c107a907501800d450341684a454808c0c440303005003060110a11401c0c144104550403549150304660000e54281018014814001d540d413001421940c01141c00d4602c501d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 408588237 1250 408586987 408587021
    0x1151b050609072d0b1c09151d0a030509060d060b030417030708040209180604080c010506190e040804031a060f011407020409050328020118050a030e04 67
    0x603100d000c00b503843c00c1620070075081140c54400c120421011507040c1313a14244e80035040d4034043c80d14440a0705500049044055075150301412009240b840c45101c000b1885000c803001c1c5000710840c1a003c5440c01d48200048011071140e401541d031001c100000d4455060138070079102d40c04080070940a00410004400d0ba524107000864994a07400155100e203108a034120305003882000c00c2022400103131242d202042114000c14014903045a41395400015541400c02d01c090042d5620318200040d941644d00e000001800c003041c03c0b082c0229071f809030303040d90301c5200030144644540c4101290711800c2d03607000c0c0040c081000c0040c42012100196000300481103941040a0144c1000c00e040d102140310300302d1181e000a8550040c1000307154a480b1108032402c00042c2c3d0280700107410b0040f41102c09000400c09030842180307a050043da00881a92550070b03440122401170b0840b03000411030002d40ca01508128001280082d40300211580751801c031011030034140200c1c014002d03075151030724060 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 408589487 1250 408588237 408588241
    0x1101051321050d09030210030911011413060c1208040503030c210103080a09050f0d0f230615090115030c030609020d020d0506061e070f0618150501151b0506 69
    0x654450283d1051700e00845002560303412a040a030125000084014010000703000303204050340c007655100b1403401500303411916200c811610b03401280c515820040202c5d10745000310702032044421159500300c805003050070301c50a0a0b2140e903035901009100d0640c4c0040002c000c0506690010041b0b25049183d040d581e03c5c0d40c41e40740c00903454110000c050001041e521000510f8644810080000f000c0035100382d40c0a0b8107911100485143c0c441e080d00d1030a5080c0040543c01c881c0d0450340c10303440c0312602802c55410f0a4012400706001400340610070102d150051006202d200c00c0c01800c2a0f082c100000d80324102c0ca01540500f03a41e5000c20303041d42c80820000481221500100408405000100083d54505d02044068000c1c416075032288109000041c0c2640e000400038200d4a02034040260306050310341e20102a50005a0140240e040d1842c0030420010342c087c0b1640446443c1205000c50760402e0003604813040691044000c0140c811601c4640001041c0101c9103260000141c80284c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 408590737 1250 408589487 408589513
    0x20403051c0e090c09030f060606030606181003020c070602030c03120a092a060212090103051909150c050901121508100509160f0302190e090a110105132105 69
    0x16004411001c0c068040c820380c80ca00203001080b007a10440c9c00900c00750170350301c401c018410660807000c02d10341709200001e5454a039642d80c803900000081c0315900566503500c0d90043c2030034070040d64801c2e020b45d4001d0060041c917500200030f0b0f8030850f01c0e20340740048540e900c040c402c024244980c0046c05440001444184540001d03500b072a03441260f42c00700c1090f070f80e1040103d903103480201c000f101c0c0003030138001907409600c6600029040880789070031241503800c0e40180d40c01c591072800111a15070038032001e540c03c03004d64010b0404803011f40c100341d8104541000040d044179641c05400c0c0342580e40c0c124914581c840c104065002c0d181c640102ca058100012000008000980f0100303074520900c00c0c0004401c002c000701c0c0059942c40425069400c0c6160f091007010000441c13210466036245d000402c1c284407880b0114450b030f13501da000740201c8441e17040c400c0c05241c102c0c0300c0b02c0c1000300402800d0000b8201d80c00180c01c54049550828100c180049244840000018014014003c076020300c0c00e6 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 408591987 1250 408590737 408590761
    0xf06050319051f0501140d09051606020c3c1512010509060603010f06050a030612080d0b010912080304060216031d0406060e0f040e01020d09110301020403051c0e09 72
    0x8a43c1051a040c034006454800540d444d071190b0240d021444410030011071604080c2d00072220b03941c490022a0252103c01d031401c1c00d03102c41030708083c00590004040000c0c61416141c600030007140e031680a062104100b46010510952010b502c1035045510608951031b02e03040d03081c24099083c040300316251406072604c500c82420a01c50280f16460301c0001c595545032000032207040700c000030b110302c010340d1034084140c8180d000b01e4040c03014165544030004004405881001c0d010b4804e100c00741c0e03101c940d22902002c840d19540503074104100b160f024411000070012903403140303410000080e142d941d24602203001e07204491046c059a040000c2e207004045e084000e8100c004204440c402890780c5070410300088a50720301c100b4000410360802c0c4040d80c1400411200d080b00050700100303045440d404058266481090b19010003503403200c545050010003c182c41802030102c0007075161a03d140c13034031503881100c1c0815404103240c00c0354603052180544d4440103088005803100f84585406030040c14 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 408593237 1250 408591987 408592021
    0x20f01211401140315040c0806040309080d02010626071d1602011a0d03020c0904080316050403050615010908060c0403210207140607050102030f041a010f0605031905 73
    0x38030700000c00c0000c01c032580303681041c1940b06000b400a040205501c44203441d403c1000e8415034004101c9840070801032410700c0200e1159000b40c5851011925280b5940e02d07146800100d10110391400e4418050011002c07000c0c0c40202d120a07442200d483c03c28036250501e000c1f03520501205071300840c455045070203402e040e07110346200000741420030b8024000b40c0c280d07007a10713904c000c0c50540e0002842241c58086840b0100c01d0080c41190001e248202c0420440a0b05032403e0364130b83c80100c10425040200c0505440030403140c44d2083c242840e5507a00b554510020b40351040c20a806c243c0780742e03a80d110b500380c40b0090001030202c1c0d51074101811125071580c0540001c0e0348070107076070801008401400240001c2c0880c294000c221a9103007950384040c2d070181000855003d17004000d41c001245007400550b01414040301d6115082c2000d1825100590180c030700030001200140c0100840c09034001210100d4401d8280300e581caa40307030000da5518030340003001c144a091402007800900705500d41100 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 408594487 1250 408593237 408593261
    0x1e01090501050609040c030f032006061005120a0b0609190e060a05090f06061903050f0a060b030f04050c13140a1107060e0309040501080d08010b03070804020f0121 72
    0x41500c45a00303012012400b01c85c0505224000d0404200045071582c00c00e50881c02481c1050300c21130703d11403100c030b078285142400d21a6400740040c0001403504804802203d00107040c002d19001c90100701c1107900000502106209558140b181000c2e142d0100b200c016510081070304183d00e008030820410f20016001e0040803404440004055040c0382060340c0c10b460b00286403c9156540c081c1c0c000c100314000b02030a82200e000d2080b240045001028482c0e01d000517200480e10340b82c05044540d21b05801000ca8601506004c420006034195500320f80e04900c0780d034101c4e02d4603540d5040180c50001304d070415030341000c0724480c1c00303640c14400d0744150449000c00881031810b0301c0d035014510544610800180700d0721010005c0d000010315543c403058603005140c05587c2000c00038400582207070340980c40803420b07805c0303400d0500200364003982a50140220498a6042d400c1c40c04c8010003000005000900407000ca100b69411680030b510821441c2e0912284580c07004c075941c2d6502c000d005c00310280 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 408595737 1250 408594487 408594491
    0x1501410304050619150504050604110c010b0f09061f02120a090503060601031e09020406080a121106011401080903120c0c16050915150c030306180f01030204020c1e01090501 76
    0x200c030b00c0c100c0034081c64070741e541c170103010342032090a01d4100320042901406c100e50090703a84204050b103200b0940600118411032000194100030301d000d111251029081140c030901c4034404104050b503482c010203205100e01700305103d000404030b03000c0e40380001d04944072424a0002c00d0684040307034400716810075104103070181d8503581c88202c015030030f41e00d410030542170704200c00e025180d00d410250f0050f02c40c0d50004201081080d601c022080c01c01124a009940c4000c10f0008400d500f50029080f04c028a40d41c0e000381300c55890810400c00c100920b0745220304000c040e4021900e120420426591000d10748010b40c415070500002e51010740c3d100501929142c010f81040c018810301c0d00d034610f002ca82c006400ea104643c0e500300501d40284550400300e0f84406010304105258100f100544900000b04000303507602d00b000c00070080001c1440440c0340c0c1d4590140c0c2080b11105500407154116a410b403409070b01c40c01f86100c100e0400e602c0f04402c0140a82d840002558042d0542099006a02440003 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 408596987 1250 408595737 408595771
    0xc040308190912020d08030a0b040f240e04061a10020f0f0a05070b0c0f030c030702040b0a06020a0311010f180204050f010f03030e010203040504020a0815014103040506 74
    0x607801c0342c10322000041c0d0320003102170004010a919000440c1c2c41081020005000800303e0006011204070060381038800341d541d007441521012006421288414400100445901e401c1c21004520ae0082008005944815410b1840003036a0300c0460b03111801403804290500c04d06c00256076020100b1014400d20800c0041c440c806808070b410500320f0b03000005440030700e040211025045e0312008036a120380c42040c9038403803406010f0002d0202d40d5803c0c4040c5991701304070700402060b9030701201ca542c8200c0c1402710030482190001070000c089540b500748801102e03040380c10f01d40140408250710034440c1c05c013245e01480650801d00c200309a80b003114104682c0c0c40700b40009548030400d0242d0034807181085400d0011034040d050704086100140304072440c05840300d020400340d0300050b0706040415848428846d0b05019003034210302242081c81e220500d0101c01c042d158142034a240c6000005003461074511020302d081001d515404454000e1a03903d0078603140c41661104112611000e42201c016 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 408598237 1250 408596987 408596999
    0x702041103150405060d0602130e0a020a350109020a1209020a03020118030c090515040915020d021608270102150c160c150c02180c0403081909 63
    0xd81e80901000d00a0168104402e0180b10060030003600c015400501002410001813041c001401071400d50601e03c0c4031286031022924400c0b03000f03821200200e005000c00c0b89010b40c802160078000e007004102e02412100016020720704020700a60741000f0780200c0011a4907a80e81e001085030001541e9031041010710340300113104981010f00000e40c8902a0f120400142d8820030801d00e080210b000000c40c0c25650350740e01828498994008414591180704100a0300c10b4071043c1002c040d0300340d40070702409416944410856004010010045501090304010924035a040c0c0c0d41050f0b40b89014020006181064042d035080301c1400b00351601105d00707000c10240182c8100740e983e4410703001400244c2d0a21114104034000070440205d0740700074400710b481d07a180480c0340c404603070198880c020705d107080403149610700d03081c1d152000a114910070b0030401030300c80b02003c4181c0d00d9001c00342919915620309000161013140d00c00303405201c010440e000408200c4102010500054507006400c0b0340d142 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 408599487 1250 408598237 408598271
    0x1111501061701030206030f090f03160b09061b03180106090b19060f0305060103090519060c0e0a140a0806070801090b0f0105070210020f1e060906040c09020a0c0206040b070204 78
    0x100000307400c40c1090001c030b600341d8554020355410927040e0341966040c1000e4880c0c189560002600e00d140f4202540580c02408800d048841d0808800c00180c000f910380a06115681e58041d0305881c0070305070003c0052540140862140c40c410120002032045c00d54610003880038254182c0c039207210b0104401c0c0c1b10a03a402d041c018000b1112203898041400c050514150010324009002c181403545030000600019000e1040120a050040340211701202034100f000498402500d44401d100c10800341c0a85540ea481c402e80031142d034a00350022000081010a082110562158000303100b480140278009170440d40ca40e042e101124020020304450408005d85031203104461400b195081102802500b829400d10700b402089004680304015245603803031404403030a22540c162141040d41d8125014144901b0b0703000325596000b000e00303041644503404a80352511806035282c0c1d000075a07002c1c3d640a80d0101001603001031001c1d84a56031084060810f07441810101d200e2442c120203154800710380 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 408600737 1250 408599487 408599489
    0xc0318010c0f0602091c060c17011a0c01090602121603020301030804030206030a1e231006120609091a0906010b0d0c02030f070c0302190b0d0b01111501061701 70
    0x78019024204a40d200c401c005e60203055002d4000c10f401100d030401040402c0e100034494403403400013070008603041008003041c001c404144c0c4501881401008500350050b8004046d030f19503001540c0d074107811b0303580900425003d200142105d00100307504a204005485441c0300700240b85501d030340461940ca0403022480240002060480280401c3c40503040c05e5000e140e01032600500042c06080440c0300078450241c0c445800656034495400a14411680b00810481c40100400302240d00f05041e0740c0b16422118060501041600a000300c01000140c110300001c140b2a0700030805507003242481c6100c8031a4075a80c0201e0541240840c1c2e2480c1c00084150490b00c4481d8118140b901400c0c425001d0b29001c00340e802188000d1040004607059000101444d03071052941840d651316510500000c14203007600a0180e8040389002c0012018140031100c2c42d602540300003801004810050b0303258414041000300c1c1c0d20440300c045036400303007003c0948e061710015101c480a401d13160340004800402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 408601987 1250 408600737 408600743
    0x209031515100906020615030a050a0506100902030609010e10121217090a0206090a051306331b0f03020a0b0604020406020307080d02120406050f06040509030910140c0318010c 77
    0x1006c0005d04004071251011b03004c0000600343c0d8595401501e4252801c41000c03002d4410340c10a01c240400300d04400005401400b001009609600d08080003a4a020741403140d84101ca9480c80041c919503c400c6000002e440b156100088141c21070404854451079941980080741c50451404030101700f490026105101c074000038000c2c0c240704e034203104042d042441c0254000a0300d500c0402c1e03c0ea660030030741c440300c05038040c0011320502d025040080b16075000f0804000903031701000110381001c605a40100d0b8941820102007110b0b184c40703546402c200680025001d2452216840d04069012904d035030710170300402951b0100e803104420003040344614402c980143e8020401c060010704540702514946841c84401424044928551040d03a642101d0807140a603803103040054a04020503800e4000034195410002460700420741c41d641d02c1140e00d20703485580b10b10401c1d40740340c0c480c00000b090120054101130303c0f96065021a552078202980c80caa440e0403001960403a0b5210b04842110720790 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 408603237 1250 408601987 408601993
    0x211f0509060d03120e1b06030106090e040f080d0905010b030633030313180209060d02070c080f21090a030b130c03140115140103020903151510090602 66
    0x468074200710800070365640072020310036424004803606140b0320880407000713100c0e00076207a01c1410f8080e0000324446030306001e10420080c401400302d0f5500154443c242d561070440917400b92035034200354200720754031000140301c000c0019810880d03140030380103100318912900c024026070303401e00101a150344003140d034105681402c0f003040d090080c503600f00b148112601c036410b00401c19036401007400c40d400f07001c000c4040208442c08010410000916803008000450300f18102a09000090064813601c2d003030100c1e0719008140c040500060102c0480202011001c40f90741000306a0882e40b0340f1002e501c1c61030700040c2400c91546500080088440040c002858a041a400c596809048030360103441d034101602200900300020f580328100c0c4020f075004845091b00d8400b1141600e0039207906214045c3c4061681074200704500420044211284c001d09001d82c8900c07600340401c2c81e040b9a05c180c1c031301303130103c901c1402130301c11488540c000c410302c05071000c0d804494071000a8811801c0c0d40b10300e0005038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 408604487 1250 408603237 408603241
    0x603010603030f0507030315080601030506070807050a0e01031e0b030d03020408060f28270201090b0913060905010f15120911031e01050a0905060a050705211f0509 72
    0x544031300010000c4520038240080e6030700640900c0c0c4070104490700200302d035501200c014001d04c4010028136501c14854500400325150000e0002c0a60003550804800e00c8200c60550903168000d4010318174925140001c00712400c9141c0b0080f001d041d2044426009008170b01c69031140b02d01c02e0003110280e035101c100500381601c0761a680100010028100120040c03018284051002c6031441200c1e2180c0e28880410900d0700b00340007400140d00c01500e10250603200f80c510780142d0304401d00108882044d65041c0d04d80e5800d4011540d0035503a680b80000461401c02c003c611503c2c543d02c0181aa200c80309080300290311178213580101e900c1c80d80c001c1c0c04610064440c209410306a001702c0c556a10038119549060900000b192405d10b604140c0c5003124007005140145510034031445c0d40c000c141100034084a002074481e1078450070301411202400d41c0710302c006031260740503070700316858644552440c0d40590030b0464400d4041030b06880c2010000c0706690044a102403c007a00010f864000f0451911a = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 408605737 1250 408604487 408604517
    0x2040311150c030c030c060f01030209280906020d150302060304060506150711010f0503100303030e030403020307030b0702010b040527101d060615031603060e1e060301060303 77
    0x40c010000507030300c000002c0042030191907052000c1c2c4440c1d980c1000640d158041c100625050500050580c2c50640401d801000035a6464044d50707009150910300001140c030060006090300710580481600c5403c0c103207280104102c80e801040c103060420010000020117560111070302e07425100295029a090000c2760200d50303582e010607040070005060303444501c903002010740e2a400001c0107842803080100003240950300168040c2800803245030852035850180003a164019181c0806000c05965075054411000200704441c007a50b0024216100d003582d0f86080c03101f07940300300c40c00c000650030007071030b1403071402d15001d264042c7d41880c000c1d00d820f40c0c440e41c05158000c0d000c0c0c0c0c0c1031528416024074040040f414411490822480010480c0d4554203000240c5400c038003418060103050745000c009403600044050380e81040c441890a11280d121240031070180403242c000c01c460320001820b000b0f64000c0b01d030005c1c210b035820005c0305c140f5940307020030542200c06074030019001c181080001c40301c0c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 408606987 1250 408605737 408605749
    0xb12180c011d0901030b04150506010836071a0a09060309030203091206060301060e0402030c01440106050c071e03140622030f0f12050f180102040311 66
    0x402c412480c511a0b60b40d8907040010120319003030780141ca09980038024041408070b20391510404041e00041072086081020009209103001001036021950b201c4515030312420f5109402503580d84182c1c0d14450701c1601c0806500c4e0100c602c9107003001c410050341507260032500b100b40c803107190301d9031586d0070410b00e4010258044c00002c1003c0b0114013040117580340c03a54451001c0c05d11104170000601e643e28080f03060508443e800d820804205404400b00001640e0008170426000000c1c6802e03040f4070140c004049074881040d14414402d0f502c07001680b080c1c44400e001e040054a0501904c1c10b80e641c420701a21544544001c0c91203e0300894014440c25016004c01d030001010301000803100b0303a40b0349a9070107034a10200342030303000d81114040c0304039281c0c04009080f5480602c100e0041e8803516a8015024503030720f181e148144000c00e6545058076010341941c06011082b000140038501d130210107409102d8049802d01045059101d04c0040c10750148255401d4035440f2405000d0344000384200301c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 408608237 1250 408606987 408607007
    0x80f030621030a080c040b1306260408070303020715020705070f060203030a0b0a05040e0726032b050f0f0714090904020a08070602060403090e0f01090e010e070b12180c01 75
    0x6003801008009004211f40d001400b14215a0100d200203501b460b00c02841842d01c600d41058501d40ca40740d1011000078440d016821a81c4060036a5840d13005140a401a0041d81d8014021000b40c122800c40d01e2903940007021a0f51141099503201e68a076403550107079201034013588c3c0c0160f1082c40015841c1c00a82d000341301c3c0d00c5c4018024044240c2c0d0300c0c0014182c0d9800f4020750419040b0400801414401c0100003107000d584205c50001a0350040c4c90541c0c90003800d400008401c00010380c0f06046074030359040c01c3d85220b4410705020320300e8146a0303d0401001aa940007040e00f01d480050701c480d11075071502c074003480501c803d9441c021300c41d010429004400b074000d80c2e0002d0042000540f01e541040b82c07000800158015050901c0c042c200903086000c3c6a010055248200f420480084080540d0354159008540c0014408400034489401800e0045025034140310318500031070380001441c081d2204c4568011030043e903035511200a000d4903981e0000d000c03558042c000c1c42c425507010b500544 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 408609487 1250 408608237 408608251
    0xc0209100e0c1b2415060d090201080609042105120114030709150918020a0807080c0a080a030c0f0c23040c020a031b080f030621030a08 60
    0x844003920303100621106076050b50202842400040c24a40c0415000754078210340020501500034007800e25114134040198407808400c2c80c0d5500c0001d5505083d91690031000318018002584412602c1200c1c0300921007400243c2c0418012800280c451501490340e40c400e91744283c009101c13035141080314807400d030400101c4081c407200b440700d5030720011401040ca00030324a040f0f990406caa00c0c1c1c01811300f000e42c117402000046091440364085550000c0c200c0302258100f0200040d1523501e10b1060b0b0711044c24100095001036810707000181030400160480503550310f01e00780c45080c4010004c0001e814541c0c8038501d05500281914404280105c482d4854240928020040d8140340d60703d10649a9858028000001912000d032407003610503003425040c810262000c01250008400103540d40c5d034001c01c02410003074061042410240d09509040030302c0e42c401c11064440c0c03070004050b1981d41045900d00d029400d0508a5101520710641c43e0307115a003001c0295284c201044d10171508540018008 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 408610737 1250 408609487 408609511
    0xf0615140c0c030307080d1b080c0a12020c101107051009060207080301120512030c092b051510030c210b04080c0f0313060c110d0b0f010b0a0c0209 65
    0x155100362010301c005d182441c822240d00741da484e408031000c0d040b00d80c0355000c1d00000b0b8a1000d1050601e03042408550008010490f031500c85400c040b08440e0f52080d240041d6240e40045910402c00e0b2000030001c1c0f5520604e8010f100c0010300000240c100d000b20440a88142c0c840c0341d040c0401501c41e07108a03100d6020346400b42c50442c02d502c2c0ca4000b50700c2a48011071550030141c00e9801d200050100501c160031444000c0e140d4106010700c0b12140c0101c4a44510600c1c0c14130300151080d040800d403058143c501440e8412000c05402c02c3794640c03110042004441c03400400040d03564060400f0401030f03e500c070140c004e0840c1803409440381e90b006110a00c6140c14280c00c0407001c240044150342c415072103410302c5940c03540e40814440c1480c080f4600f84c01990320500080d5042c40b031032001d0b601074038a40e141c03a100e091101d0601400c4100c005400940021080d91941d0901007101c550394443c500452002c2c110740d903204926003841c89002d500d0360000d03034060720120041c40d000703401e5500901c1602072 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 408611987 1250 408610737 408610753
    0x30102040e0c030f1302060315030f010c0e010e04181b0509040c03060f06050f0f060d06080706140301060503060f0d051002030601030c020c0f060a1803060f0615140c 73
    0x11400741c01054480a14600001c0b041203030142c80c20f031060b41d10510088000b0351800e1560302080341800081c1c012902e800c4182100d0199450801803003110a890000a110f4100d00c0b5002500340b161448a10340021401c2c82c56a00c14201030060b00c1e146010a19010a103400b075485403404000c03004a200107801058500140380d40d5400b0300300d070095014400c40480e261440c9030280c1240d201070b107158480c1341400070420140e601c41c06407448810098980071007000b03080c400140d20344914040002410314142c03001c660051700180724020780c1c1c15502c0362405249658540741e41070000b44601c40000d030b0200300040301400d000714100c1c542070000d4540300c689070659413002d09054000200210700b56001c8104403196034107000700206c4003814005419900c04107000718840d100b4400b96540a01000a02440d03d10f124125018510113004240d4085a840f480e01720080d15200604200705820030b40c0c003003410402140d000d41001c000d40c455010a50301a8501e00247d040848080254011404 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 408613237 1250 408611987 408611999
    0x8030d0e0f0a03020c0103060e15091807030606030c080a0809010c173403080a05041b1401080f150d0c09060e0f01090203010303020312091603030f11060601050f0903010204 76
    0x400082d88a80c02030541e0710b00c590001800c86e502580140d00c1203001c0f2080c042c00000d8050305040c00d15003914410555991088084101e040011003050540700b00742d000403c0c00f4541d8040c41c01d9a1140c41e480000799a150500c5a64600900018045840810000c113140d8002d0192019040c0301d141030141d00100460754600c550004003001004d41200503c507a070b21f00c403021040410b0240e403d4108400641030314010102c0d0f0300103110079412540d99005c202440a40d04006013031403113030303100e40030001d0322459055400800c0d0272425001c02c4015003c2480d002050301c0f15440f50b01c502a82c810342540502c20800084a040e405071040c02001d44081a252018010040a415075071640206400c20b03d200c007085a0050748030014282c0b0500c01440000e502004450405150b280702502d180c540003101f134203100d82d940d980058420541c400208250b00189556030400003a16881c4800d1a1417142c242c032200c00301d0315036000907001c0003000680000314000d801ca1300d0000c1c000608040c1c40d41 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 408614487 1250 408613237 408613243
    0x120c0c071e0909030e150c0d0305041103070605040e0901050105150d090519170c120d060522050610050a0c0c08060408040f091811041b050a0908030408030d0e0f 71
    0x31000703500241ca404c2c00c1a0490800506c1c91400341c0e00c036a1003601e0300c3c800f090129101d2200c010000c007019110700100313043c04940300f603450140034010192000550303205006802648144601880d00c41180e002840004040c80b5983c120307000500407644a0601e00b0206013558042c00d81c181205590f0441040499400c206151000544829114101c400d40c204201282c40e0407006034103030f200c20403410640d25408195840b1800120420b0703a01c42a2648818000d000c036074101a40141c5407000030b150041ca40d458614449a031084104460f84401c0c0c1404503501480a840d000f00b0030410503015054402c0310300086142c003d2024044040d111aa81400e144095905070384050000c5014040010300e920000d0041c1400401049540011605001032000c105009000220501c81801c040d8903171f5080802801182d01d01030b84072884002d00078145400c11070001d0001420b10001080e110f00010848050300d4822004504140044003014080c03c80800c9908440c002d007106490350b03030010 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 408615737 1250 408614487 408614501
    0xd05090c01020f03031605090d1502030601030f15060f0c0501060e01050a0807120f1707140c0f13050403020a050a060501060311031e101a120c0c071e09 67
    0x1540500160140d0500082c5011090581c506854000300305200c442810407500c510811454101a901c906801c030000318001a0284054500310000034001f0a26020341d00840c8500800d072070802c4448003400c06102121081c1001c0c08011880100c1801403034007408400c04058180d10307080e2902c41c044c0d96110700b03568056004c0305111011000622591401100b01000307070444200421078546840550b420510f0702e400c1c0038001c5511030200c602800522010f06500d0704a601d0015a1210f491600e0705008049480c586d801d40144280c0b540c00e482c0016010864207002885041c2e038490780c03840c100060801030411025032040004900c0054003d0210900e81d5000e0310700000c1310341c50198040d050b280310880314490403508004100803070f00070780c0c420000700c0600a07000505a0390215903408040e0702d42c1000304090b035080300789070740041c180d4020100f800058609c0205500c40f2070458000d4061100382c10081d40001000344200c05011284c8186040c143d25442c40881d40c40180c5400c0b1403034 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 408616987 1250 408615737 408615751
    0x80909071e0c1b17010b0324100b03070c05010605031209060c1006180c020118080a030b0301051003111c08030a180609060b0306070807030f020408100509280b04080d05 74
    0x600b03c443c0c1c6a070307000707118118410030147d000d04600d4206c4180c20403d1380044c83c80d0f24030902da80340400c02e41c0d804e15500001619000c035001d9070700d0a10300c00141105c0d403560002c55040d030911601041c18107000c12a1100714004440a60070102d43c0c4040081d942c101c5000b25682e44145c0c500c0d031444440f03c1c003072800180f0080610380074001e000700400c0140c4656aa010003560b041880c081c038202c40c120600784516030407005290b1140440c03402100a0318140c410564598205001d00003c5200340e01441c04591190701100c8441040c002446084500701042500c0328136000c440101244080000395800304400d940080c20144002c00780c0111101008156040f41c0d6400c90301c030801c0942c0c4030381c0c01a154100c0080000341350940004041880092103c0201911800c01c1022400540c043d50003030060041520388135221a00341c8801071600320340c1a00c040c451003102e04c140c0ca54550520902900c2091803c0d0550710644a01d510050b001d40211400102004100344504032403080c5030259107 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 408618237 1250 408616987 408617009
    0xb0d0b090a0510090207050c0f010e0301090b2e061404030618021219031101090503070503030f010b0304050307020618190e090c060904180f080909071e0c1b 69
    0x10800410031072103c05422540d4014410080e036008038200150403803225404445d80200f11041a0048410b0100c201d1420f41541c2040030650400c48680411445451101d081c481c0b0f00311980c0c01100b00504070a07000031520340200c0c0910210380700740360044d81c003046018001e01c1d20ba038907920070041b14010070352541d401100f81a080d0462401c4680d510b0080b04c480001c100307803101d0075003044401380310000040c1403054810610740040d50a42180b180503800078280e9032640050b0801310317141c3d8800c80e400c5103900b07141c000105c0c030640220181c0c0d000300d030404c0007141400c20660901070310380d00040103900030700018841c0303080c0c60b6103a110441d4200003241070200c8162920551400c1c00c400500b2051503604500064402501c801c0145c921403103081314041030340c851454000410041946020b071410b06030000300c0007805424001051480400d60320030020360b407002e1003140c0280e4200d4034444017a610a0b1642c4046118107200c56a10703000d011442990b02c00c948800c0c107400c0155200f00e06007c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 408619487 1250 408618237 408618241
    0x120f0d05030103030306050409080a0e1201060305061618090203041502040b0c01050a024f080c01020d121e02040f03062306010f020f070e091009030203040b0d0b090a05 74
    0x642c0340c06006c00400381030350144031503181655254468003400003858100320411034495260760707c0d644c1e40302c00d0741190b100802c001d0340c41e0300307041c1d448041c11115400754115103040b4560261082c2c0d030188200412070940005942401c071210080c0d803000e0400c2d6490483c0e031910000c83d420710320083c40241011b1100c81d80e240c0d0414007290a50b40b00420203015244180100440c000d21180e0303655000c4404c50b09190b00080201c2d61114840130043c40c42c2d81165005810340d6072038141c0501c442a60344030780450300c2010450700126580c00d40e580303410700000e84a5400584840c5103400401001c0d042c3d00e2000110310b806468902203800c1540400311911400e0410000d0000c94071805a000e004001d0480c07500450b000010301c004c40c00750000b4100042c00100d0115180b00780483c180e6821234000707803600740f2356401f100c1a0307420003a102002d0714090203001000700803441c13080e081d46980c5900950304281c58403070303811626040740b02040300c1c00e500e5580360070840d615408c0443c440c0100c900d0004e081c8c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 408620737 1250 408619487 408619493
    0xc0a02011d030904091505040305130b0a1d01110a0c1706101a0708030a050118230601090e09010501090510030510020a11010c02070302031c080402120f0d05030103 72
    0x14441c24450540e00d09030507103004010381400300489000364415036020402045070b01c0e1101150f03243d244044401031815060004045c3c2c0038004000b2020703602e1051820903102c00e8441220f11a9189020200705c6010440f02c0780321108902c003410403070506201e80d101100d03803800ca0405402c2d44c400c4400c00d88200382400741901810105d03006141450003002c941c41c04612100b8102264040c1000d040c0412001003103010108048031000741c0d214524a8607800c2a402a6010305028090305040c100142568404440a4411092800f03800300342c4200201e0503150b500300541020b4800d41c10000f448201054219000701e01c00c0c0102c40950000400750f140c0a9601c08664015103d81c00c1c805104904101240c3c000582d50140500b01c00c0c010b940b07550710601079a9480203034542113919402c007001e08050326004150034044900a80c1521032800669481003005030403201d002c0081204d8002040142c288800f0068001d1241d0007166100c1e0001054a89030001100c3d038107001800c000014020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 408621987 1250 408620737 408620741
    0x170d1a040f0c1b230d030507080402090604050a0b030f0604020a0e1e09010b0a031b0501030509030a0c0503160b0103262709070906170603061f05090c0a0201 69
    0x400c051420801140002c040000c0c8851400c0d03181c2c400e403001045a010600c60300b141d508100804004481d007814192042054882500b1500c3d400468503101c0081d0b02a8080c11015100301d60040404071140e66080402c00200000303481c074003001c0d64600c80710903552400c020300e440e14803800000300b229141c0ba204000542c03000740c21401c0d1031700000307091040369030011521144c030004448603003030541d41c2c902d4654014031003045015409580c840f400001e00210103013034840b00c3c412a1101040c20785400054050704d0302551082c1d0282c1c400c00000800310700c1640301c208064401e07002c0d680341c008802d032918001c10034034a0541d01000e00d80300400c10040d13120010086502e0080c000760305a40358214412540c02106001c09201a0048003801d2000a003000045203500003020103c05040041000704882400d0088070301081c50300040c1c5000306844501244542001001442d032592030f0b60000b84d1840ea42c43d075400c80c10294038000305407950381065042c030451010090607190755540c0d40c0282 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 408623237 1250 408621987 408622001
    0x4031b080f04031e032016090203010806130507121505180d0f080a1802041407030e0307050a020f150304061406011b110d060f05040c0b031003170d1a04 67
    0x4c507200442500001907000030840c0b00702c03003c140000514041040c401820000c00076403032512041144800b045110031940558183d480c500105d41c0965a0884512080959000003030003d0340324203010040d507504014101c41041c860320100f24001030005c44241518400c0e03034603241055803c01c40f81c0202d4420044041d0361030491030003602c4001c3c0d03000c000c2c28540b0003908a1403020303150145106c5448140ea10990507030b44c0035104124400c0c0300085049910700a60b0b02100103424107070b90104003400001501d00c030326000320191031038050741d6003000f850464080c40103030442401c01c904100e080342c070400717144101e0051402250307804829000e0720755580010140f9042c0800e01006409031082c0c8010036444d00e40c404c2c2064084084d80300010742c0300d50014070042c03460341012400c0e13000d54155000540121b1040c07031980d0500d515160f040b0500c0c04111030504000c40d10540400115040d10301c02030f28081600e40c034602c1d22444296100641d0494014840a824442180c0041d0306013445144 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 408624487 1250 408623237 408623273
    0xd120e0a15081006230405030d030506040c0905060d0b01091502010b040506040212070c060b0a0807141012050a02040e28020309100504020a0e0906010f1d04031b080f0403 75
    0x2039000e08110020300361119a8000144040800041c0785c000b1480740d0849011300002030840c0c0345281d1899008000e440115105030169041520306014a400790402c60156400240141d0900840c3c9090000402c0821005030402c01480c2001070445070401c41c4201c150325a0780007007176070f502540a00059407002f0304000c1c0100d2042251801802c4a0124030f50880d500303180040f181300da64289000900b204951700c070b07401060030720300240f49d40b80060008110340f40075080003800c5600340d007048080e41500f1a92004520107590032100c6100640c461f42c0d0052a450300142459200c41030b040f0411422a010188840912a074418010751100b540e40d2095100304158030310b00d042d0745001d4540040c40c0742c04c1407030b075280c101160071075413140f54030300143c000c0760041102403504000da40e548400a00c14040c01130b140301004984034010000c107140c10542d1416001c40d03a2185c0e98115200a0201c001c24104204604040006001d0304002c210041c010740d4410340350760841c01d0203170014080541d80 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 408625737 1250 408624487 408624511
    0xd0c0227040b0709030201050708130e010b040e010801020304050a030c170414040b030d021c050705060a050105011b12260c03240310020c160e0a0f09020d120e0a1508 73
    0x5c00050382c0c0700c82128100380c1d1102c5029294000040c82860018480d00104003c03040c4c2c030004035812041e00d000d0b000310380e485e15a400040c0d80c0d80030407600300e00c007e540192054201602400100e400307038030000c01d20340c0b1504101413410303400f62000034260081d400c0407040040c600c41402c12840d050190a04240c1c0490141017003104804000c0c1d61542c4040c20b580d4800d01e0344440c100c41c14000c4080e25003594000064540340d01c0c0c100d90503c0142400d00802e404603021942c50400e482d8024410355860350300c04440300c4103803034540c0169800da2400e0303901d150040c0c2c000010200b204a82d00e12078005c00440707555a03104d0601d400c40c0c0a0303c40e1100100002010f42d060b00705d0140d03038006543c03108242d810360010f0341d52092465880c02d1907918040700603e10480000041c1c6003c0d1445041d104880040042142c07420182e0300b00c3c02d9414042c00130358400d0f001c1401c18041605000d8003000307040c1e542401c90600240101042e10300391aa442420000300e4592509103e030b403c1241e00e40d0200d0f1680c54 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 408626987 1250 408625737 408625739
    0x1140709061b030e030111040e04020427030c02060705010905060103020108060d0302060606091c0c06120903080f060a2606011406070602090406031a1f05030d0c0227040b0709 77
    0x200070010b0300400c10207001c1180c16203e42e40903842c203601191181840084007030781c0703945803130b0410300d588400e8600701d014500c2c2102044558207207100504191105803031655915585031822140924450300a90780200d0400400002403001d00c2610391040c42200901500e614600014141000c01003000b40650307001414200042c1d03012940940c07201c4200c90300e684803000e207008140c000303100c034a07009140703111070b07180206000c2e2a070700c1e03c4129584c50f44e0b107a02500100d40c2c0ca1042d2001c0010080101c3c09510116a2100c014036450343c1c0b09030090848030026544403284110800401c160000c0b02c152400b01c10203591040c00b04a025240c180c00074141d5a10100c04141d442c0304c0c001d00940055400b1800132030590300d80d040701004540045c4184140c00900580d00c80e240710503244659892800700200c404401c0011000d403c90308014054801d007040000c09556103085058220303803100c05d1155002d00311009988420780b010b00400d60004a207454505411100c1c40034250300203100100780 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 408628237 1250 408626987 408627017
    0x120501030b041a36031b0c0604030b0f0712231f0e0702121b150f0112110d0501050405070603090c151b03050c01060b0711041d0114070906 61
    0x10100d0b065200004100e500d4252500b001040030f400c216038244140000520741e201041b407407032403450070081c6c04146c03004104643c0400800c0d108a02c030003402d45000500248035019070b00e2400c0e601c07051900b000a0148420742e0044202c071119420b0b01000440205100074103102c4001640e030103140d54014541c40301d400e60106008502034071405640a85500028402c5032091002c00c44200c00300d102540c4400e4a002d0056403c5461759805034a48100401030740040d000d1100140200c1c5045d1240c003141e400c0205161141c0c54111040d940c44125081f1403610352605100800c800d80074100004240c10185019424031040f540b0080c101400d01001d030010035490741b060011100e03110b0300460510b0010205990b188204200319010b44a410800018190031500034500a1501070007080f001d601c510780902c540c024200082c3c9101c44504c4550300c40c1c20700303502c5200241300d88101410008028101242518040261034071050b580a090158081c0c100b404500034281d223051401045240791 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 408629487 1250 408628237 408628261
    0x105030307060207140a0f021f09060305130b010e181b100306150e090711060103060b0103020408100204090c080c120a0b060c1e061b0307120501030b041a 68
    0xc0409004180e00041303480800120b5001406011a010150340c075600d510309029007211040c4a06a029502420072401a000b01981c80080100d06444003040b45082210440080000403c2002442041100c1e54041140c511040e4000c000700344403142a480d00002071168507191940e0760089070b02802100100e0100808010840c5205542d0311031090620501100070b000c03e81d001c00d81c1000d4840d0210740c4c00e581b04c1e04d9010304070801d9800081036141c540302203e10b031588240c0915035410103801031000030402d0b040030a001c0d40525025041c00d445011107402c1c400040314136003c02da800501041030250038010460b000200d41400d83c0180b81c158042180ca102c1e40100078044d032464030018503140c9065100381c4090002404203515008180b401a0b134660324070000c00710308101c03001caa40d4150703030028080d407144a034001301030f40c5543c0c88400011070b90005818002401241c0105543c070135034600c030f010b00030340c02002000032a00307060401610501300061341c002d0104d4a00c0800084207032035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 408630737 1250 408629487 408629497
    0x1090f111819060f03140126010f020c0a05070b2106040914010903020601080f0a0f03091a0a0f021204051306030204180c06090e0109020306040221010f0e01050303 72
    0x1928603902003103150400582c0d500581c5200b060708064041012940c9580042810711032000e0303490030020b400591001d040059000d2151010700d84034a482410342403445040701440b68041400450070070340001c01201a030700050005191907010030381d1082880001c004401c01031080082d81441e00c0c42c402c51201d80d22450000400e031406183c00440c130b443e180d580c049003040341c03c80c91414034030340f045440c280a0304117490241d00521a603c00841c0d0f040011a51551203000c210003010380011581e1103034410b086043d0140c05101c14000c00040c204050080f0b10300c01c0700340700c00140d5036480710900a0000221881a20110b51119030681e1100c000070003141c091f2941180c201441808650242d00034001580000390402d0400c1c401e02402000b412809000758401c24000e01071070340720001200c680c6d41500c02c4e8a84280b100d0700400c17020b09a9402540c0160000d0805071038409102800a851060000d6030350b04071880000400044190354000805030180d1419503c89514101c0001d07528028 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 408631987 1250 408630737 408630757
    0x5030123030a02030f010606090e09030a110f0d02100e01020307022d01110301081e0c04050402041b020d1d0a170307140c011b0308040b09030904021201090f11 70
    0x100081a40079501001210700032980101128000500e00d96070354042c095900c01c07240411a01000411141380c0d40c51030b9032180b000b4500950810b0301c040742c202e41600c00c20b43c0d50852030080005c1c203c4581d03002d03c50210340040d5900103001040301802403008549070304030944000e910510034020303c503501003603680145110700182008070181d2800d940d032404079018071155640ca0050174a00c4401118080c604949000b410307250014000144105c5810a926100a5503004140702421624003907100c55009400038200103100d03103007500710020290079500110051b034040082c103d85168001000c50300c10415a40000030f0007001c0000c580007250364052400603807003941925600e60810030565001e19000b035041d282d00307101403290704c0c1c89000750900c00e800130382511308038a95410000d4a008040d641035640031059aa01e4441c0e104120010380240302c03601040201042d0b40d59540081c103144120f040c3d811a0551501c1e0030042160344c01030801c5903090400f00c1c0380004024a0040d20f01d407040e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 408633093 1106 408631987 408632039
    0x13290a0e1605030406111803100b03031b0c04060b0c061b03060f0310020a0f0315030503071209080307030c02030115050a06030c110102160201020d050301 68
    0x801c44640040c030381190322122150307215400a590240c0140f00c0041c1116600000714042c0d4002c0c0030002400040c500711348010302c1d0500c42d040404840d0001000f4014082022a80f00e01030b0126010000304c0308600440322220600400002d90801042000b40a48070000280d261b048411601018425100050070310100c42c1400007402e80c401000714203544e150001c010906041c81842601030003603040150031500c450014114034511900c036400700500180005003114202211800100c807004400c10203d28040110350038141c1214100207418040c0b5002e035010301c0e040d4080a454480000c1d0801810b91000b140b69089200318000d0103071400418021840d400140035495002e0b0843c1d0741040340d213001c2c1d80448580d01144c1080c0d62000021488a401c9822840e040b081141d549002c007000c560303044c0514100240b080c209642903506100c40052001c03180a24101090 = true := by decide +kernel

theorem cover : BRFrame.Cov 408453237 408633093 := by
  have h0 := BRFrame.cov_init 408453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 408453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 408453237 ≤ n) (h2 : n < 408633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
