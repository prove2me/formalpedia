-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1348
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T02:30:38.093866+00:00
-- url     : https://prove2.me/submissions/dc83291c-f3dd-4e81-82ad-18f08c206caf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 242266187 ≤ n < 242446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 242267437 1250 242266187 242266249
    0x19092a050a031e0e010f0507051611181006120204050f0f030f030c0a0c0b0901021203060a03020a0e07090905060a0902130f12110a121e06020313030914 67
    0xf10b65003068074011000d005655001d580c040c0030b4074988040c10100c90500d0041180f070381c040c4083c0c0d00420000d0702401d85500c4d680e1a03082c40009005641a00040020600042c0b0011003c3c8240b103034440d44554450305e8076000c030040101c03040882002180d8030600050015541e10000e41141d1402100c0665a10a141000908044208440c00c5061000041c4441210008155189428010250001c01310380e1080121240e100f903d0416005802c07410211842c14205c1e406143c00440140905542e25201c1d408182090455004148401106c004001416900002c80b42c041c1c14044014001401d00c0b00c0452102c41e100d00800d8001900890001140c1c01c024031000000c2901d0846070f80101e907070707030710a10907a0034621040c3c1d28502e850082111504140401c441110740d00a1b0840c403007681c40d01c1e2242034441821401c001411341d00101c0300070a01900245009105601610b00720600d14540506035250983c04032140c10001100c00301183e03900310742c1304c28901c981701d0940c0f0b0a9000364 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 242268687 1250 242267437 242267471
    0x30f21080408040902030603120c0f120406080705030a090f0b011e0e0a020d0e0d080103120201020c12070f02130614041802091015050a12090f060b19092a050a03 71
    0x405041e000309e01c081200440454005030583d65009010140c560308400c881064105201e103004e86c00114501d000410961485200110351080380110002001c1c40580c2d544d40c450721150748144c4124510304018045107002940200d1b080e01e1219004800900e00b51007100320800003001d62900e0703680400d0b421641070a035045014103201c0030041d2034502426140c09014520280010313902200801c0803900300c00d005108580415101d40020405041a660004655031004d04212800b00c01e09040c02c0042e29200b20003074084c0c0c100e000c041001401d12180c040c1058643d000240700e1800c103502c3c050b10340d84155942c54078640585412411ba55410001000c1000c5907200c5450417490102c04111164000060000205d595441c0b55003158407081d502c040e00c4c0c450750054070030680c0107410f0000644d940d220a58401024200c1c2c40d0002e001c0d21180000c0840381d0015007419114058251a404e007900d08103004803108101c0754612001a000034481d006001402060582d40e4080a003071040304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 242269937 1250 242268687 242268703
    0x5060924040f08060103350a0c05030c0d020c1008060909071502030307020c040504120c050709020403050705090702010c12050a0612110102061612050c04030f21080408040902030603 80
    0x954034101102d994601850303a8450920003942c7c1c102c3c00f611304110107042016001a10703815240b510710350702109031105480c0d620144400040c03190740808000001c00a00117070861f0007440004c4c0401101c40031010b4100103440310024410b03000c1c9a4000c8480d90818440d075006007013900c010003903a60b03030224a4070380411500410044d2456004080c8021f900000441c8641460b0b400c0d41c50a0b80281d0610040d504250f900500e60b100f108000545248560b00540c983ea00550032140050350301c440701c0307040340d0140c2c0090315250410203003070000723041c01c00405402401030310080147d5100303840010210107541000c18802900e90f03004c039012441e0f80d04041c0203021440d0180481d94120301c3c00a82101c2e00002e0349000d4041c686c0002d108104031400019459003d440341341d0180c0880c02c9001c018200200961404d007010300010000c01c2860010900c000d1242e002c2d8417504490301040c0302285030b100111020080c514081200142890301aa070403075201c4031015840362280c0300001c1c1001e0f81c07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 242271187 1250 242269937 242269949
    0x6060f01110d12141006091a030403120603020a0815010b1206120f010c0e090702060601050a050a17090a050714010c020d1a16030b12210c0604050d08010506092404 72
    0x14040174000c581004c042c00e0000c50b80c042d1a90540c0944e50350b80b0001520a0400c000c0f062081440041c012900424442800d010710250008100d506c0381d00003021151076800c1030b120342c0c0c4400941c1c2e03440d895458041d400b400318600014142030f098248100480b03c004c10041c00303001d007008880d00e58102000350b001c0d8812514003d0003843d528035001014000d0078510648100403103800701c2c42a43c00070131039600880040c0d441e149802400c01c4d06403902d6110198802c00c01c04038504881c0040d071036070f007020f000b0300b45200644200c010a04044c0c5c5850b04580000c1d60504554211103060ba800c90b4134140e80503415902c0313a0f005a0075091a0754056250013074001c1003402801040100c070b4078841c1c519608007080e2420854000030001748804110803031541102036201046110100701035030f0820381c0c0c00681e40300081c070303080069411074103004007680c08885640c08110806441c54002d00781501400c826503c95003400c1c0384070006829840301c49a900403042c0c0f81c0303444d0700620034078408880107011 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 242272437 1250 242271187 242271221
    0xa030f02030f1213050d0c050919020f07030e1210051b0a0306170c010813020a080307030302031509070c1103030c0106030b0103060b0609030307150f05070206060f01110d12 76
    0x410b043c0c880d4000d5000e1104420903000c5103002058510b000840c034181036410084804410782002c01b44000d014003c1c20692140070312102441148201d40001c1c427000003207605030303a241c0c1407030700c1e0162001c180d806145101d80140c10114250100014008290800002c008201c0361114030182c0c0490341c0c2d0b4110044180000204075480a416401c071500300e8406a01e03040701050201c201c40d032208801340703c0030f0018003100042508004505030306581d00c0d0000f0703c030742d10076559042540d1441d4045c01048000c2500401004010420400c1a8110034401d0720707140c0140c500280000d0029000c4680205070b9072140340300407541e440400c26242c0d003040080081200c182c9030b080c0a81d01400920044031800e08100c079110880c00c1440540d1290380010300154104850f5582d40781040300381403c83d400e825950a85848003802d0340c00703814000c91150700600000c0c20181d00b4007040c0d8400300356081c1808480d0300408510074000800c5103501d03c25203030498040c001c10380c0503800703410301980c1116100 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 242273687 1250 242272437 242272453
    0x2070210020619061a070c0905012409030f15090b07021b060403050c1203090d140c0102010e07060c020613031a010f05060a1407020d030f0f0206060a030f02030f 71
    0x203400140c074900980c420f42c1103850302003a8071804800c1d0b40301c50013450b0051110842d211040040c9801030007044e03104110101609840c1c1d01101d04842e0260f004040c0c00130744240000340031500301d9403000c030b00c50180760003240e141c03d6071a207500704114071000503e290300e551f51a0000030655805801426440300400c402c0e41021040203650f01c41d50f400c1da2840d0000c29a1040342d0346041c1003160b0440781d0040190038042280300070040390241440b191022400200f141c0d600c0b0341d48290102c0c404a118084a080300240145110301e0404c03050784d1641035a1404114608171000020807408503180703407421341040c0c100d910100c0e165020350131040b445680386500100c204103050701c0010000300d001c00b41c405c8580c1d070b4002d0008413003403503c030b069000101042641c1c0324038401c1c903400c00500c00464000303250810325030119140c0b80840c0c00030350005040400e05080698080014010610396200405d52030030200001200d078440c62000405a50b400e808400840d00d0500c030030b00c0441783d0682515101 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 242274937 1250 242273687 242273719
    0x20f011b061a0103150e06060c0f010e0114010501080403090504050601020708010f05010e062d060714071a0403020f12010b100216060503010b1e0c0a0807020a0801140a0f020702 78
    0x169a6400e50b980c0841c1c1801d4020380010400005072003120310301028010142c84003814002a940107a000c1d2616000d68449000444000d000e003614003070141000081c0b5000072009032564074010f070045410000d100d0140000300358013030251400c3c1e5008890028841c0c0b51440142d140c111244e01031000b41d400c0040e441700c030784c00d580c0c4458100c03014980240d507182e580700100211500320700207900e100d240c20903c0e00c084545e030126481601c078000e4541840c00000ba01c0f21090803100c001c1e001029031141800340240904070204c0b0540d034400b104060700f42810350b0700140703080c169038074983e0003080314030041c440010003508101510700c400340030280d280c14451402902c50780088102034078940c0c55200068428031800c2282e040b1503003030640a080c0442071110200b40480d85490300d03a40c100500802d07800040500450503014032403011147d5814140c814807021403816808101240d1415410b006105540100107a003e1668000000d1038005114084000d0007416006500300c00114200c48003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 242276187 1250 242274937 242274971
    0x50c0a121506090e0f0603030d05060d170a0306050f01020a0803041502030c04150f08010905070e060a02030c07120819030f06090e010e0610050609060c0f01020406110307020f011b06 80
    0x9072407469480286075620011003d8601401ba115540c05600400240e5600541680b105401c000d009150b0b940c1140143c54004184000c02815050202d0003e20a0740013509440741e01c004080649004069004000010b515071180d907102420340d10002001504000d0401d00301e80340c5065802c0c00310f44904042c1d21050b60740d0818059000c0d0407090707652410000703000d030040950782405950f410805070b081010001c05418054210780074089001e000300c0c030075941e02020340700348030440e4015500c410720003407172510304041341d405100a617689005410100d0b000c84d0448070009000c045886c403240c19401d00700d0007008503000880a8a107000c0000c2a0b40304683c0002c2c3c3c0c01456a0000d0062640e61548151280e00c01d03210408031003d00c200c200402c1c1411000307450046001014641454141c0500909066a140410100d03941c0000c1c1404501e4100c0410301d500300c0d106005605180c3d1f03d9000c16504102e03444040d0502040c611100003044001c005070440030ba00c82018012000d801e00309841c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 242277437 1250 242276187 242276189
    0x20d061502070f0812091e15090f0904081e040902070b01050f010806100e1512010317030f27010c0e0a1409041b0302120a0c0603050c0a12150609 64
    0x81c4900070a4400612000001040d0200c1c210a08800c0d280114150130041400050705d200441902d04000e41c41090740c5a004040c8c00240021806a440454404100d401760108144a2003003a181e02803001160350403013a070f00400300d0241b865205034612001c0407054001d690101c00c40da030000034070750b081001c11010303a412110705803034004012400c3c5c0cac019540300c4070899100e9000503112081c01d842c00d02c00c10381160708060160040503800e0681d007654005a103d10078040b1401324120040003000075a42c5080c54409201c1e000c0c9081d0705000c0301c80d218009001e05080c034441c0c140848010f07154003120b00d0000d0007801a00810001e2541400500660b4010814070700ca0540701000044003444080700510703004c0000c2c00080d00d0365031942c0306001c12083c000c5070b1034412004600800140c6410000b6014580c610707004010650701072a104400c03000603001381c41054200710034081c607a810034045d40e48810860516041c205072040c072210080c405c0c001d680121851003080000d410b90844100b034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 242278687 1250 242277437 242277449
    0x4051807120303050a0203010303171b0c0309150a2313090c09060e01020d08040f170720090412170a061a03060a21020303030a0c11010506060904020d06150207 70
    0x2021325904c1c0d040c0c0740105e0000341300240109214400481804107e4503025501440001d00d040401c203c54a81902d02d401842804196500001d18049540381690070f02c10b1100031112014602500800000d0107010002c01902c20340704414110f448000c044002d846011440c603030f01d02b00c425510090403011300b041c12905804a87c1d414004520700344a0038540e652408103800810342000058422151074000402c1602e1503d4481c40d10000151a1408900701da5000d80b103070307a2035590ba4142400c0000c042d8408000380010382c1400803440d1540250158055042010801300003c580415602000d440507144004400c0700100102c0540a80c0000d00703807080c01240b1501c400323180c5141c080b6444207940c55544038110450802c19440d942d0b0386c400c5124010f0080c030241a6569000c24a035800950754801d0306900c4904084070958031100c0110781c5160000203100b64200a804135101e40b00324491113004075000142c81c03403c001e80f5089071004000317070310719100d448544540080d1200c40300d010785 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 242279937 1250 242278687 242278691
    0x50d0c03020a0e03070e01060f050403021e030709020705060c0702030a06151403030c03041e0e07050d0b060307090603050c07050717060903040608060d020d06180c0515030604051807120303 83
    0xf0f2040d003000500001901c0e42c4500d903034403076403e102c0c09880381c2d502c0314034070400c21004100100058444164440c204200c1c4420030300380c00000c070b0130142008a00d40004200340e206211106c0030440004226411120b074042e40b559074003007800030a0910851500103080281808584001c6410394008402100c10f421103d5207481180800c01d80c03240700f091b15144a03940103000034000000d06e07404a041e01015003a0703480b034055840300c540340f941004883c00c80100340040354a080c0030350070740607104044104072419459440d0054028000001c0303030040c0001c00d995440020013000141c401c131150150064102c0d14180d5441800900000801d100e012050142c2030219404000010550701070340c1041e15118801d41e110000e0280c03554200006991003074043d1081d201180e0544150101c40007102519202c04455050040b194155503000b94011004101048207080001e410b480c0c0242049601003400d8171407684640e040880050081c13143e020340000011034103003040d880c200e5180300e41c0742 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 242281187 1250 242279937 242279957
    0x20c0c09090a02010909151d01050f040c020d0c15150815010501020a03140d0f02090f090912070501091a220206030609040303240302030f03130302090403050d0c03020a 74
    0x441d5840c2e0401d030800030b0100d140b40d0000e010070800c40e00801d162030210600816190341e500c0c40c0000d102d40090403010300d95041c0006108a086c089107003078601c0001c0e5014022100c200342c0081d6598041c2010300100900c908141d81005404102a44001c0c10f884041c00b4034207034007403000540706680c440c04c0900e100e00340f0703840e044950b0b40c100c05040720816005480d48000c0740d102030720015000b90245081c00010131124069001904c111030740006030010040c0c85a64500c1400443c04035014960302c02c403481c03c20440848400135440d88074070715000031b05884201d180342607805009800401841e240c9074042c20a0300e801c0d82e640243c03142c416032030352906403a01a4454030724000315003800b070341020f030810000d09281060904550024828076000070394480e00c200b820750002e1062a03802500021007c2001540fa080065441e012100d102551500543e0030300000b42424500c0001c2c010b903903880c0014141802035058070217002e004c01d404c0c400c030018034130010020f52003200c7c035902189040b00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 242282437 1250 242281187 242281201
    0xa200906040e070308031e010321020609210706050702030322080706051312020f100501290f0301060512010905060f04021303020a180501172a04020c0c09 68
    0xc110b410040031015240803411501c0720b2085603c000c00c80d1001e12120082042e00d080e0b4554224000e50041032003491034803e6000945001c83d070a0281d400710b500090501c229428045000610000101e070901140814040103503124083d503103018203600d02e00000c011541e0f401200540c480d4044400341100300e003030320444201c030400c10070001c1d140300d409000000004925601c419000510304203064030900c43c9a40d00181c0700c5c490240038005070003030341c00c11000300310400c66104a484020010700c00e03507041c02c1905488030f5000c444801d98200380c807001e005034038072201181c80c1201e2440c141d03981d0750303110100600a940440c500d0080b0400140000541d18114800c903400b903071008080e101800300c80d04c00c0002a4000000178440c101c43d40030000b00507650070003c140140a81d907041009012640001170440794141d004050a217000e6a40c100804000701d1040c502c09042201050000742000304183d03a0210002202d401c240300007800d039249840000c240315501812030f2aa80c05582e801 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 242283687 1250 242282437 242282441
    0xe0423030c030a0309020f040905010b1f02120d02040f080106050112090b040b0a06150816080403090e0912040803070c08030a1d06071212060b0702090a0507020a20090604 75
    0x107440c000180c20a101ea548010304c030350801702d0304a00040170411202105d1002030200c820343c9004450f40e07950740d07074000c0d11f07410000059412003920000c0a401aa110003002c0d485444000340c42c01c2121000661200b29402641602e01504240b1545019203885040290080c820b50284e00d01103030103010321080408181c05030710b10a0394014074840d01500e03182c2d5850000b1a010300840307512907c440b00130558180b01581c40c0c14a82d8940c1e9042800e0a0007504080d41d14000f0700c8100400210804001c0820f40200042048071110f590000040c3e85400105007000080c102e94060f0b0180010005484100000500040c130b0240c0d07800c0180b60381da006125600e200707200683d0040b5240e40c441d8042a051040241003140c00034004900d030440302da84100c9080e641c074007190045102c446104d10021100d01c01c0344054400460101e02e80794082e00090110700005010100c8581c648002070405442401000d140603070040c00c551041017610640c05060310030030411070107015420300207403891901f4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 242284937 1250 242283687 242283697
    0x6010611030f0a1b0605090a03110c0307050613080a030c151e0e0f0d0918020c0307060e0f1507030f02030c0412020102070f09020a080a0212070809070e042303 70
    0x1032482c0e4a00703114980700740c90140850b80d445500c04441000000410035030302869209200180203000d402200d8540944295002001542158052010309241d82c40005000302642c1007107915503122601d030030a0300501c10380ea030480c0e607050264400c140c08141d0020344001003184511f04550b50046041000021201d030000f201130340c404040206082c4101c03e511000082d005002900c10b2191721052320344c03a0030607004820700024803074103041040d0000c415805201c00080340b000d525018581102030f40d2401b0340200a4041503a4100c071b0443d4503010085424000c0704002540c171145e13492002004103600443d80da40c040f9050402d1b04c042c5450342c0c402c0b684031302c20110b8682d040c103003403050718075014041510490551150340e0010982d010100480350040450324005603440c91505002403446001038800003000e801440b220480918000c01c003680310050740703006076807561081c03541c0e4941403142d440000c050003504207000034011802481120f220981118821404d5041b07000c513a42e21031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 242286187 1250 242284937 242284957
    0x60507060e011a01201203041208010b090616210e1206040609080405130c02010b0109030b1b04170609070f0803120a060302060406030b03100203010803071104021b0601061103 77
    0xc02c800c10f68a80d0300a50400c851442102c08040e40040d00c01d641c00d142105203000c400340d6100200c10032080101503c404500b00e1118a0100d569502d40074190030070340540310344035101d04004a0300c66a07101c091070761080c040ea00124483c501c01e500d24031204036081100b000c01d00048440c0090000b42c00d201e03d10401d0300c0da48400415080d911512100020010307880101c4440c2c108000025050b41d03809200c40c03544003c0000095060a03c810190854031401c0d00c40d4103100351031400f00041600f001619900039414200c4219216036100450098400c0b078100a2050101500c2c1e098017600c0094010320500c1c40c24101d40e00e8a48600810300030b40c489109107011940304008140401840326040c40e040b00c80094040340d05a20780e40041d0980d00280c12640000c1d0340c81001010364a001c0180a140d101c00003802c62865040c440610385030b20610201a00340d49401400c81d4103610760b03030b04880840982d00410700c045100244e0031070300c03204c01303204400c0003a410300f02101408401004485a0b000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 242287437 1250 242286187 242286221
    0xf0f010605040611070518180c0603040f030e03010f0e01060b0c0307080d06080601120303050714250b0406090b07020105100311061c0b1002160603091506060507060e01 74
    0xc0b4001003141c400060409a60740c0f030080400c00581078a50074000d011440800028071f41382d20701410110410443c100ca1000710f0303401901e80409548806d42280d030055004841503c140d50365050650342c0e100a00a401d070150303c0d2142c0b180c071085d82a800040e001c10303030000034400d140d590b80c5403030054050100032000c1d94208001d130200140c0808000d10340c1c0c4441d40c0022503083d680b5100c8605100b000d901405401182280ca1001c240d030611503180c1c40f1100f82440f405100e4040030780000c60007451100c9604900e4604404071501d201402640b81540c4011241014605031402c071000c0c021060781100d40200d6840804d01d0540107000380c0c0c0c03091561003220030b51540755889015900325035440003500401c00f048042000503c40402080202e03500c840410101000390a10a090a48900c001b046411200034003140c070b14900c1602013101c446180108242069040200b4002d03243e0201daa02c0e94a00200005d0540e084006454101d000b080100014095801018261111105800c07041030f = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 242288687 1250 242287437 242287439
    0xa05010c021309080a1e020c0915060c01020a02010506060403030e09070507050105071805010e010203031f05060a0f0305100311040e010e191103031309020901020a0b0f0f0f01060504 80
    0x15108814040034640010040b960019a40e02c0010468251540540e5030050010b0b04441e181e401c2036003683c860398291980c0250300c0510340000d48503070003000078030b1064000da00851100d140400c400e0900e48001003215580d81113002c001d40c003c0d0300c40c071003d8000d9400c190005410746440d07001e881c00c40707030107071501d04004103014200056118001c024800303001c024800c803804200240701d0f291040b00c3c00c1c0c907005668420495492641540c65001d076040080000b4a01c40716640841541d8210003002025048102c1804d010b0b41c1c4c14a45405c03d0390041800b049144640d98028dd4504245445840400440c1c035a401c58030717001200c50001070415001010000028200707a40101c02201c0000000030b0180901242c0c6420940049800e404000384c0c200d0050601c2a130051000200c8800c800962420950003c184c40c0003085104000320b950780070500c1d41040c0d00074060109143e034403410f4010340c0d282c8000980c001600c16602d441550f070007000010700c558400d0008a0507140a91a80d500702 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 242289937 1250 242288687 242288689
    0x1b020a1709030706121e1a030105160c1136150105030405070f0803180306100302011d0907030e0c01020c01090902090406080304060903051c0f1b051e070f050a05 71
    0x218841e44c000c0c0359540e640c2101b10f400c0d040c0541d001d8240d012030b00c00705114140c902003d000c040d04409140c0301c3d914181c03d001490b44280600d6103000c80301c1c10b0640380366880d0700f041110100140c0720280c200404c080b24101010b01a020343c05000c810502c501100007081c1080440f004003110008180040308007156050346c010409998841d209004a91080d5100d0500d503120f050b40740c1c00514140d2002c1075040303440c0310940601b100d40f8015001400b1614000125000700c0000780700290600544031034644154440c01c0044a1102e00030313005886a0401e85001001043d1728009607200b8022070b070001d41198808646041581816034030703641c01604054900f4002c3d4880e1401c142d100b517840d400003440080c00d0001d8002040241c407000c4006146040685c02e045200c002e48000c0540c003103610040c10703004211032041c0c00180c6001c80151891803500c40d5103040800001d009840303407145a0340013208018400c0140200941641e0a10780d544081114403262030081d20b911102d080018402 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 242291187 1250 242289937 242289947
    0x1b03090209061509120d021504021f050f0c0a020109081501061101021c09020405280506220606020c150301052e0c0201090f06120f1b020a1709030706 66
    0x1c81c0f0b45800506281c8004100050740c0740c080c641c3c8910b025000302100004603034041c041f600c8449441e0000a1151400740d00141c4680c40e240a0011241d0408034100c20440c820f6040e102204082c0400e503540e000307181905a40d4607038401c0124001402c8480c040390f60312000c140101c075403031401c0e04103c080c1d00b442d20a90703208031000c00c02d401c00c0d903080c010201180c3e222541210006400c0100041a01039401800309172540240103c110301414a018480d1810221649407501234102d0001340a845602c005040d59124001da00c0240440c0c5c803985492014039030012003164050b40840d8140801001409900c18900c00c40904103241030004002505004c03102c1400800c1e241001502000c5040220700344c5a00043c41c0c071f00140c1e0380b00201013156003100726540601580c004442c10329140c00d400030000c94694408a14607038072070850300e0620310b85801c03003200383c4181e80c0260662028000001e5560410710300a0b14090b400d9048281480304001c129400320030050081c0460710b080810540b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 242292437 1250 242291187 242291209
    0x271e0102190303020c010b1504030b1e1509010602010b0a031b0503010903110111090904080d0608010615031103100e040330150b030711031303061b0309020906 70
    0x41540512200050000080100c0700761040c443d480058484007402d201908580300c0344541c50080640c50116821000040103032001c50740e00c100a1281995201381c82c6898507000c40228012402303110030320000118071100010100002d8500350040d030303170368a4100d090707980342c0c2c0c6543c0e00444410000c2c07001c600800c684a401c240e4025803001c0c400d0b07580010034211041e091003500000c00d1030310001d1000ca001e005080032144e400d0041c2e800d101403400040c02c980000b80c0300800564002810103000c01e1203821410060032601c0082140603600d000c3d16898015003801c200c0081c0c940044820b0010380803094900800c00702c3c12a0072098207041c90b20361070500161050703091010381c4428403100c3c00d6060030780b04c8480c464840042e001507403908040030303511120f1002c1c1000300d100e8014400100c192081da45d108403680741500202141606c4181144100314205007a8000b02e40702009111003500103800c4140a0900d606a45051510890481c0e4100750002d40c07066512001c600c4030f15222240300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 242293687 1250 242292437 242292439
    0x402090312030c0406020d022d0c04060b13090614012a050a020a0905091218091005150f040501080a020909041a07140f0c0114010902271e 61
    0x1d903901c40c0c00c585040990011901107910741c1c0001001c0c0038486c0d040c0100e5840b41d0381800103006607482807041c4003c09810010340a1092080702c8c0b0040c40c540c0800c00b080180b4005002004400c0e140c400000c043d510a688140b590000c061002900e0111440b401c01140c44020366100300300c8094004603407131240510106270180e50280f01090001d4003206607040c15220f1402040d00111910500041050650054410928002c100588081d0100c0c0351030041a03441c0d01070303a4801220394080d0b07140e01800300003600418a003082140052111800905892044445800510080450119910905510702d00c59003041c0400c2000b94050440d035034110604610142c101048a000700b01c50b0b0f001103c050381d880c021901049444685040a650400a94600075900203d5a20400c0311882030640345094602d0000d40e0500009081d800000c4080700300140e047c4c15651912444083c1d00130301c0e00c0000030080c40c1d16003491042d1590200c0e500d14005813140184140703802c4450205102e00d210a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 242294937 1250 242293687 242293693
    0xc0303160614010905061005190c0203031306051c18060b0f49020f0a030602030709360506030c10020a110301090317040305091005070510051504020903 67
    0x1030742c800c5000310300d20307028003489840080d0b00d02d00714003000a800c020900c0c00c002d020301041000050182e918511401140c90700b00520481e41030300c00310703107103218411411000b903101c2031011507020307403100c001c00101940e100700202c05003d002c603010880d000214481d200c0c6007004808c1d070014882e0b402c0780c2c23030804d0000c200c106c80c85902004a44004000030307401101d984002510810180c055032447c05e10083c01e05d1000a81010082d11030340c20030441c00103449500f10840b00915541d904241d0006154400420364aa0400320805080120301e40681a03041c0c11555011910810301000c0202c213084c1c02140da4126880030710600d00500001d0f00700da401d405080818802c2d0b07201d00c50340f9101001582d0081035440b5003402e140c8518000c041c0000d2107030741020340a0020135030082000c0001000181c6502054480d0301c1c0a072040e104002d601a0015540030030480c1054024000e40100d030f0045068501c000440a114802c80d17008854100e4052111070300000642010750140078580d40142c11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 242296187 1250 242294937 242294951
    0x1a1b031603110610082d240705070512030402031c0e0a08010e060412093b06010206010308220e150105120f1005060310060306080c03031606 62
    0x40804034125600041d004524480700d0203006440401846034411000fa88220056051100082d103603140750038807020f000e00741c56450b0301051842640e440007603c900c04461145440800030011080010f0b041c070741c0e40c28148000f514450050045446855000c0042d010342c2000d4080d2000e6074001400a03601071042c0d5080e0a8651400b200b1400700d0511900c40088980760801040310718602600201c8880c2d0400c1451030080c080000c01a80240d8040c1004e2400d40c00b1400459042c04035034041c840c000ea0906a0410350f84034056081038004140103006284c1c2a005032034111004183c9600b801a03101c48010804a90108045d0542d603006400900725080107070b00c450380020883c0c002150388080b40382441099403518140305407001c02030800b28141841c0c01040b1181c1c0100419021440c00c50600246403c0201c03152480580340c0100042d071a800c0c2542e94040d907a07400d00441011910303001003c500600001034504203081c00900961030034000d03da40f26501a80e164003228032035180c0301 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 242297437 1250 242296187 242296207
    0x3020907080f0a02040807120218040f0204110910140d02120603100603020a1217040b030a2d0e03160f0303140705070605041109100f1a1b03 62
    0x1046004480070340c0c680c801c1d400c054504440d203000c0540040700d02d078810001004041d502140280450342c4403402070006d0803840c0049617034400d18984401a00a00c00701b0001080b070041c401650083c021707101000a11441c44008141c0d1240d114115400200180d05020071446080c50140740600302c240d007030a04201d600443c090742c01034400441001194001c1205a08081120280c81c0000f808241f0010f4910340105001c150355014684100039802e40340414024000b810a00a9262451061f034803645c83c01040c180e1340058882d54a594104400c011070345607503240c0c40a0010001d1420b54003060b403e82c0050040165258060242c00203104618900c0300a051104405001e80d495041203201460003d0842d0904120200060052014090500c0d0301009540c3c0345648000c0c0080c66484c1d0f824500c00c1040585176040e4829094020005100c031400d01100c00c803560102c1007070080b505e580c101c1030441e0103071203160400360701482406030710581d4040201d16250320b00252454440411 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 242298687 1250 242297437 242297449
    0x170307030b090112260a081503031611090402060d0b03070f0f0609080706050d0b0105070f0303021c2a140f0a0f0206060a14300d020d0c0b0c040302 65
    0x1904c00b03c2c802440a41500a001c0018540c41d16042261460355141ca401c95030401c450040600301c0c0704001c04071000406c1e05411219100e00850001d04403034541040c0c2021a0030160b01e000e08440d80d03801505480c1a034200110700c0c5000d0342d03000f00348138140881000c10b0401404107040603036146c0310706800000c01c20800304903403000d800e114012104060901c800a4802e0342c080c0c1c030412047d80584e10401c9055842816519080c046a41c0441c1960640004035101e00a034903001d800000001120402c25816900810741c05044212620050401907528000c40d02a40c0b0004c8441010180308807030030b800c910700307482558501d0601c0e8403440c400020901c40360300864000c20b440740d80011120381050f009202580c1001031072008052610b00100403403011000c52140d0902c141c014141546141d42d6034621408050b40e042c1000382032060300d54440c4140c9500380a8140e44d01560a440b11a64804903400d19480980e4840c590b11005555074a0703a040b00041030021200d1081c0000700042c1d8030a = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 242299937 1250 242298687 242298689
    0xc1e030f2010080115030603051b0a1d010b09060c060c1317030d1a03010f0b041109090c07060906090303050a060b030603120d0906020f0304051207170307030b0901 72
    0x9040882019050071a48200d106001c50454850110761968240c1c081c0d009032058192121200c2401c0450030350001131340a0036894100401c00d0080d1304d524020044145405501c80e03400b120902d82040c1c3e18820841c8044c403d41003201c10018800041c00030401640040884100181400e4941890500d00034104030080d00c0c03c6a170750700f000a0481c003064582c92100c0103442500b441600c20f9181070b5000c2d60345e205204a21a180c3d803580c45031181c21071010702d80c03014008050001e201c41001c00741d174540202040b41d1a80d100d42d00d0512022220004802580e0ac2c000000d88880c480b515200551840c2d500540f0702104d4654464180d00f00003146801768501041c4280c40208250400c05481c0090781c2050304400c51501c414010045160385c005606410501e464880d590303694010000140a09400030340505180e00000b0040758a0034081f00440c0b007030740528191040050304071200c0c001445102d1016249040c1e1503c6030b41e00700f803202c0040d070f0001401d040c0009c41c510040c0101790b850400b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 242301187 1250 242299937 242299943
    0x504151d0a0e0a0e010b06090415050307140102061602071701061a04140906011d010c0803041410020a0e0907120e0d0e0d05030703030e0a0501151802070c1e030f 71
    0x100000c0c403d14840d24010100543c4003070f4000d005140c514804143c940c043d0303110003072050392a1100801d50180001c0e035140a0b10025061384c0d00d032612494171b4580110324400e290700600c6418000f60b03c1c0ca400d24440040c6261940c0070300805440c08d00c07800c1805440541682e56550303074200000e2181424601048000001746281d901c0c0c7e890304820b50341c1d80d0000031a06014031b0201301003040c0c6a0f0b0000c4070301065502080304030340e505150001210b40c1d03004031900408160b80002444140300e600c6041d042100f0100c41207070709480c00854281c0c141e000780310035000071079910300d4012040c0ca0f04c40340d241d912401c60324250b03125840c548090400c0c0d43d00c1c050108001d402c164140d5201c20392200040c98510001c2d12040c2e4100c02540d15990380380b19268000e020141d071020880c22250060004844a50304000244a085503000c901c02440a46200d10291007110080321603003c00c81d4000d40300020b40103a81d20348090704d0620340840420f100d00000301d902c0c0e010180031001802c01d000007000540 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 242302437 1250 242301187 242301209
    0x305040b040608150303070302100e07030c0b070c17060402010309060e03030a0902010f020a150903090b0a020708010c091203030506120d0e090105010801031e050111030a090c060504151d0a 83
    0x1d110140203038184051100500030b400800647c03012030740009001c0b15200d84842c000454010f43d0f58214102501070304001d004281c1840001011442d10010b000c0c1079009244514610307a40f00c100d00703203441c00ca50504171903411078400200590301a80c005030070140a03c0b03000c10004981d0740c4d89420345c3d204031915a880c69580d0044c03000e55a0000a1452190341c1d80010500709000ea1100c0c040381840c01401918141c03034154900c00c040c45040c1c070b10002c005050340b940d00c9109454000e51078543c1130007584c083c0d40c0303441a44a09a44124045021611030320506021042c0c1520210b0181000600c1c0903004000d00d2a1414880807c02c2103040c0c0c0c900aa98805000c40040200300e0b5400d0181d10441c10408034500500225134525140b031141851145641c0465510b40b40090252a600103248521103003c01040310003240e941003940c5031485004040101c075183c10b0203a6840c042c902440748840c1c4a4200300128a000d61b140103141c8201d81c03113045100e040703c80000d0043c016504180b465030 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 242303687 1250 242302437 242302441
    0x1260403170910091b030c1707050906010e01030617010c0e0409080a051e070c08010c080f060d05030d020403060c020706031a0d021206070f020c0d0b0c070305040b040608 75
    0x15901111000400c0c40002005410b42042c0d2429580c814402901054041d41e604020080103180d9038044485010a0300c1c1000d03465507414449203d20b43c5200e003200d8502441941003240d040480c00000ba1800240f2400140e164034004407032010300004440d0616503140408241a6000f031034015032600700500110b1205c0c420400100f00c42c00d2070301d0890190f400d155641d0b00151443e0243c0d20140220700d08251030780d104ac402c3c90601e4501c8004030000b1100007801c01c0c180510304000c40c05450801000f81701084420300210b6881204682d0920003c0b4280080355080c50a40416003086010390112800c0c0100c0000310380407079100d0350003229040c0c3c2e140c600e5030380c01c0e4040c8520030041c4013a05007040104030759034001c000b400004012034407944414a18034115a46c03d100518030f400310000b103c2d018540032074003400064503611100e0140c452044420700514002008450041e0710841401080d20394044000c01500005012801d0010510000c6100e80d00040608020000c41d07a8001040c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 242304937 1250 242303687 242303693
    0x41103010f060b070308041a010914070e0a09020913050a0e0114010f0b0a11010c02070807050f0307090203060d050f06010612020a05031302060c03040608060906060a020a08030402012604 82
    0x11070801160100c8903041220400040240400380d404042d01401d00e0310b140d41c0d80b8540288505031045501c10344418600000c030707004400340d1049001441041c02d0300b174240c03506e09040c5c990500443c603190f070050100034140b00f44465900030b40044940a007924421003501e0041c0d0054440c2180e00f00d403c03503910099036141200c01d01036010115240d1214a44c0c55040c1000100c0d02c442c28001c405120348006883c19000380f00750003204e600700040c1c00801002c80d00d54402502c1d8003240c452910301d417182e4000415507240031f0640002c4804020002e001030740ca045168400794000600e166800140b010420010410600c1031078165100680135201d81c0d810031001406c1f610305030791103032422441449040c0d0015000750861b5006100603c06001800c0c461001402c6c0b4441c110a0b220240000308001504c1034200381201e00400c411214214969986002c0c03181b540581d803030030700050b0312900711040480c02c1a0700440d001401850051529007002030b40d81141e00c3c2c28130100d0035845c510300400040c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 242306187 1250 242304937 242304941
    0x1e07080a11030705010c0302060406090f02090a09031206050609040504050c060301080709060608061008060f04020409020a0e04090f031409061201090b0d0b060f0a030515061206040203120c0c030604110301 90
    0x1404c0b09081c4020b9085480c1c80095403000000c0c0000c1400d5903643c0000b0a0140c150764114550385c0c020801d10861030100748441c054510464110081043c0028828090055000300d034140c0f071b4040c004c203003040d0740001000060710b0050804d40d018041c041d00c0c1c1d6a10b41704c03035001358080d00140f4002c0c4901d03840c00c218103045507450340c00b4600700403a00050040c255120131030116102c0c421b180a029644900d0009030890100401c0b171a0700606c00100056000b220b600940380c3d51030f8607100c1180d10007219040c401507603050800240440e10090820703000174001c220358560020851040c5050106600204101d64000d1010025480c040703001005010341c10b0044800c080c2c0e043d1000c108540940e1780303041a002d00036004030310075440b99000e1502612500100301c000c0d40c000e0101c415001c0d060159021030704050325950300820960440c0c070724003d00003640c42d00a9030b001d402444e42200350f200100341c5810445a90700c00703001c1c000c0c0c004800d613010480e0078080e900410360081704601c40c400b0142 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 242307437 1250 242306187 242306189
    0x18050607050a0c090507080a09050f0604050c010e030a0206041a040308070501060e011418070c05070e060f01090b09090a060504090302060a06150c0602030a02160c080601060905031e07080a110307 86
    0x70b590341c1001e041000099101c11f0f002c2c0c101005000c08503c02c5002c0c41c0040c00e05284082d01e480521801c5c0800041c40400203c50103240020780301d2600402d0702c0000c2c5501c170b540d5154043d4001d24104810840704405116007500c8a44041d103c5041030b0b181d40c2c80101607880a40150b501d80e45507c000e000c10010548041d0052030308480000c500482100415205450b50032a028080c503507800050159000d90b04408500380d0181c1503c0b0425190720044000703600548038079000316005d9055100f15401454a0300c141c9034810b0000b400c28104008000702200000e16807040c16803145c5000405031110b00601c0c0c0d86a100390050021407421040003802c550640d0700c044203903001c0058440e006600911402c241680054000d80e684c1d0f00c0700c054101a00c522120074040300c690a0404c4207020f144e24811050701c1a640581e80566030303070381e011183e40480f80281c5500d60840c15a44000480140900d0b22503400c1c40c0507603d455544124684c10518441e00980e003032203400104406a2a090140c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 242308687 1250 242307437 242307449
    0x2070308061e0d020109050402040b0c010c030b0d0f0c15020606130b0a030305070602071a01080d080126012408161203080a09020306070c150c080718050607050a0c 72
    0x580c401446125003042c00460700846029002c0408910156481411910003401e000340056584581c1c032102c0402c164055046107220b5440d00c0880100588640905411100000c1c102d204200c1aa21880f0301105004000c0391103c2c8000400a4290403810440d0010364403074005d0403481c54070303105004404c0340c2c1d81c183c0095540f030326200741c0d003d6950768440c0069075010303d4241d482d07481c13030300e0504000e1049600152070b44008c060010302c010400e0101030b05032030601064508442210905840c100402e011f80649881803046402c0c09400e00e4a03402e85c7c6400c407100224018207815021004101c8000125042a590f120b050101c08010040c00031042e914044103ca01c45c60511201c00d002c000300402070030841100003003034401049410441490360018195030f05410910740c0500030000103181101e000b0503100e415034607c2c0d4584110748041919490350401c2d9070b24013030126505030103111402410140d4201c041420703200d58000d0030015225400500881c48941840340c0c4000340d03940300d9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 242309937 1250 242308687 242308699
    0x1b19030f17010602030a1209050a0605100e060906060d020d0c030c3507200706090b0c0a140307050604050304030b010f0803071b0803031905060109060503060d0c1502010207030806 79
    0x401111341d0020441c0c000700f11134542090f40a40503000403000c1d10020034054042e1054030200814030215a00441c011201e150038083c546588982c5040580c4080303e80d550b014403042d0004a41d030400310000c040701c50104d44014901003000291034120354180c2c1d04100025034600c41c1561850304248444002e03013003e448101890600281d003840c20046922184c120700042d0007060341d05005030441001502013440086a00f84468901503655100313125000000300e01c1c0d038000420750800c00c1102c0c82042d644010301818105a101d400044503a841084103071310080040790041903007440201c3c05188200b01556950f440c0d030170009903460040e0401d00c020b03100140204003100c1e001041300d021a51041d2501c005400d808038101d04d4210a62212507140000020014035001031003e01042c0d42c44500100705685500004540e14002c9016400c0030907410004189140f8010000144062054045518803910785900403a1800c600d100301015079000708080c010181c00000850b80018147c400c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 242311187 1250 242309937 242309939
    0x904173a0b0d15110702061222080711120111030105130e1504061d01020d0e030a0f08090106030f030f02103b0105100503010515061b19030f1701 64
    0x3e03588030000c40c0b40500000d80d9440d029070f04c0001106081e20841a00103101c6902ca020f100c0035550b01200480d14501e1000d00c030400805940078a2070030404154200181d213040c4500c40d0b0741d0806410b208140c2c50360004801e400040072030381c01d00881600000d403645198403549402c082c02191410020001101801e0803014200d030b040c0040c0e40075058100041104c4103469501b03107800108001e01c4618039000c501c094101046105400420095050400420801c4a060640b5403240503041e09a000200c140c1d00c200c00541c407c40903150090384d68400080d5039962a500c02c07441c0850110100d011400c0041c1102099405000d00c03041c151b0205400e000078007610381038110301285442510f01c640700c03c407603100e5000f1404602c1c604589400000300403d04041242014818092041e07501c02e600701400111040c041c030504d02e0402901404003420050200900300104241c0c4041e02502e1242d134051140c0c001c00640c0105166000b503c81d441c040322104c0004280d40341c1444001c4c000160000 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 242312437 1250 242311187 242311193
    0x10e1e030307121803030b090609040b130c0807080d0809030f07080307111e01060617010303211e050903030402031005060f060409020a0206060904173a0b0d 69
    0xc2101c1e8000010310704021a5012104414001c0070304c100030b1309201901c0d0024604140d010b0340a1550742c00200e80070409980e03283d080185102040343c00401144482020400d0440800c0c044401540320301d14a824a944030000c4921f48003003a8841c015a070710401041007956000402140c002031458059481c00d030315101082c00714410018010720200c80000012001e83c458005c0d03030520b03410107054034020300801064107000103281c3c0d0056000e51800c0c40c00600340d4010341ca500c1030507190348003580c500e07840e50300e0a0300d607142c0200e54460a08441004801d80b40c1350b0f4403420f6680c0c54001100d000600c17450304101d08841000b8165450365004000380000769900050309451024620700108980e950714011500d00c015071143e81e41c0002c03020801041c5c00050b5005840f5035245503003250502e54420041000c000c9081e50007401082c45500d40007240c014a8008005444000e40c0e03240c0c248008108a20510344801160142155580e0a000105916000c1c0c20380c0650b0444100d10301f411191 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 242313687 1250 242312437 242312443
    0xf0705130302010507140f010b040e0a170c070f0b1804050403020a2a141306060f0f050423040b04060605090405060a1d0115050a08070f0c1202010e1e 66
    0x4000a03052040c08205da008020464001007185400c010980b8248002c01060a020f4a48060014480e6050a00d4100ea1000000e50b00c0c00b4940c01c04050b030a40318603019070240303540c04403110213024028054049201030711450304200a000e4140300303a94402c94403402d5581055020240d41c416400c10303082c0800300b0341c00036030905030b1500050a02114600383e20911803c032041101510300d840c124100091070f0480100c40c1541e640f003946d15004020a03003c00004550803401038101207009881e010180758441c4000003010701050030b01d107140a071103000005011003040d801a8840744810200005070030640104010350005580511071541410006851809100c0005000d00c3d61400012010f0b6240c0480300020801d4035580341c080c005016200300440000d000c0c44541c02a4404407180c6188200b0494111032070300c5d0707200401a142e140c4125149001c081e0600100400c030540540812000301d001d4402d060715400002d0510b40003000e060919080c0c1d800c03641c1c3c00542c51841c0e00b04000c04 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 242314937 1250 242313687 242313689
    0x60305041e03231315020f1209040b030706081308160b0412020d09050d02010519031b0e0607020105091f0306080f0106050303040302120a0807060b0a08010b031e0f030f030f070513 79
    0x11450030902e0307440c5c0500f21b20f018498102e08841d403181e00f0040300541703060750082124520548061150320545024155030f01400e206001c001192a000200d02d8a040b460580c0114810003200e45407c500c1044190010841d04042c2c802c60599400e1008100741c080080319114003071300190024070300420300900050f6039031107514010340021688804582c455000c0354152000d42e11030700501d045c114001030041110a21005000c006d155007100454010b6aa01d00e484400406041c9051121f80c0116241c1e0001103940d80c00c044800303401e00c2d504035685083d42008401d543c0011307602f46844c800e680341170405000e4500907403400100307000ca92000f208440c256601543d0702241c1c001074106091400f5000807020300905008940e800422136190030a004002701290b100090584440e081da0882d03510b440385542c5540441510313064901001d11410a00c02a04240d5040000a50394241180e0224114030b564540010400070801210041141c02002d1858494200b001ea158054005141d23 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 242316187 1250 242314937 242314949
    0x90f050601080714210117060103050a11040b0d15150305070306022511091e0f06031f050108011a0303041703091e040b0402090307060305041e032313 66
    0x2145819607140b00f004c80c120b900002e608295032249641024500800c85400e01450280b4400030f40308000e00b20740003d505042c0c4c2c0e08100940001d00c82a5a40403080c4031466130315801c00e8171194510080da0b01e00700034281d80c0e0700501044088801900369403044680c05403c3c0303003140b210b840050010800002d424030a50342d100070016030725050b0310b0032010300e1001c0f8038450090300d281150300301c204005007004440f90071080d0b680b40c849850b001d0701c0b103a146c1b4500020303001203a01000010002200d160141c1d81058015094130b10040c210300064040290f4009940590741c0c44600401840c1e0003441020719241041024000d240c0080c80046d80760f114031302c22a0014400822016040b040601c04c170341c03806000601c519480b180140c00c01c03804002c00c2c80c00e50b10407450020f440100742054000c0382d42400004016013050b0307003420f4080c0d000b8900504161000100781525415081007510f4000c8a40d000f526110300c0742920700143c0144004442080010a01c14043c95140b6181000c0800644503 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 242317437 1250 242316187 242316197
    0x1503090203070f030812010e0708070c03140d0209031c020a02060d06080d1e030e10091506080f0f0d02070603180605040b160905030a0605040f060504060501090f0506010807 76
    0x1428000640307010301981003c82808407900c000030420406500400814190400030561aa40d4207070407000c20008031032900c045024040051039991203483d4000116100c1e0a0403280310940b000400c845810922401e10742c1703907001420b01341d04d180c200a1a0140d0a5242e40070802020b4601c00a44400c80c2801c020f00458012034012114146074000c0c202405000040300c13a0f80e241c1d000000c1900742411107484600c00305142c0c10703003914480e0040c1e0000074940002004402c410030a01c0c8014200700006481180c101c401c5400c40f20654040c01004041c3d601c0200705408a82c0f0ba030f51b00b41221103005411070350040440d030b0701554010644204407911802c0018002840d2400080c60049005008202c0b80c902020002040065a51203029a0380303500c0741c020100342d9000642c1c909005e4060254960300400f0307184000342c981d4018075840307445000900e2400c0d81030703074610701078940c2501c00f1104542c6070390052066000300d103d010f4250b0072034181804582012070010700007100107401081044 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 242318687 1250 242317437 242317451
    0x609090510050c1903020d0c020c0f060c10020f070201170708040f020a05030a050d0f050720010219050309010f05120708091c030614120714030703080a0c0b0604061503 74
    0x28200152092081300400d21514541180e00040003135015403050b60f45289030610002e800d6100140350550b20a0191012050b0406a01009546c2c0c104032200007130b40c820184981c4003490303e40040c207810044080c12684070080c610001d843c13500f041412081c10310500042141c904d50140e0841d42180d00040c809030144901e00100321116080d821990301446111000c1d010443c0002c0c0c031111004807039031840c85404040e00220380303074455030101a10310300d10314056008101501c0c2d00611644014011100c1c03281000c110780140406a803004d445940010884241035608580faa035102c0c1c0c0310341b600d0751034001d0000c0d41e03200d80300700a41903404201c0e0600001e200981c0030020044001580c070b0021500460100008010b806140980e810910100c03c412201d800c1103400e000441480d035000c1c8c103800d030034000042c19070b081c030340d0080794144242d41001004c610ba4000030086000b03280c1e5516508081420f001d00701c23901c0a000c21340034a01e03040c400c1120312620354070030251201c81d290219040d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 242319937 1250 242318687 242318701
    0x30510140c0c0115140f1e040f06081c020705010507020a0e0403090b03100302010207080a050a02190e010f05040b100807030902060906040807050114070c12050a1502040603060909051005 82
    0x1000310f1442920f072080b0300c12010a55007140c08071908481d10031908003618140e04018000d02c80106000d41c641f504084600d00c0f92403034250440b1100c2d600014002518940d00c401132031034081440c0b51580c81810340d40081c070340d40b54140012409000207081a600c0e1810a0b03000c9030200700d1030701ca840103504000c000b160402d441686c0003401045081e111a80703e0405490300c240d003006d00e100c100e0241c881c0101c0054410400714100345529003017000b40041056980900c030014907180103212000141c0c80001c00c0340c41350900294041e010951202c1c010074182000c0c4411a110322412a118200c01c244a403007165010308030681c002002e16000c41c6d0309006101059a50040c941401c0c0c0c00740c03000c907001c10712031800075801003144c000340e0781e51503180500e00c68107005100c0d03103d01625070001406c06000403a59820310540d000e100b181103c2580e07182d5107514100402c0800c21034480c88e0000342c00c00204d54540584006018003103000c00044810380d0ba465610008400b8115440d5180c02c002081 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 242321187 1250 242319937 242319941
    0x2070c080d02151e07110d090b0706050c12150f19090b0d020414070906090803030c0a120c210e0615010903080313021e01170c160c030510140c0c01 65
    0x3502c224013400c24203041c604800b40011a4802c04c41301d80e48900142490f10512466010f011103050900c054a401442c0d11100060040200214480c000030407610300d110f03085412440c458800d00c00302c514010300e604100701e0a040001540c900ca18600300789140c20b200c00c00a018215041020002000c1d141c0310042101400c0518002e0341c8285440c0143d04508003038410f50744144032994451800355152601594034200324000d401c420790050000841090b4030100a00c01c4070503034104503400700901041c901c2a201c4125003000003d00d080449803015140403201c607080180d12900f0f0124681c1540c125aa400b80109240403421056504242690190344140060354200851036600d1a120044106900303596008a0203080c040c8140c0d1414044124041c058000503943c0d00c0c0e03030350321044402d1007158001c0c0600013030640400c0450441d81030148001842c5103e19081054189075003802401d040b098801480c07890f0929294103c2249003003422503000180850480c0c40380901100b082c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 242322437 1250 242321187 242321221
    0x50d050604150605030103050c030a05120d020d0e030c07060e01020c1e0402030702031804140c0a0e03030c0109050606091303210501061e02010908091201020f03040602070c080d0215 80
    0x2e1184102840401c032698040e0095050728011800c81e020318100c1c406050ba201c0381c1f81400f420300e41204803500e000b088010010018542580c41c00b40c2011001c0106c03404440c400c1400068680c00020101c99800080c0044001800d9504144903102d0364000080e4480d42035083c014481c2042c044900340004100c68507030f00c040000342085449182501020703603a82d000e01c1240e42c90903100b00c4d50384020b18040c042c0d881c6903100c013440c6600c0c40d1602804080ba5400054030b1100f445009501c0078070710788003000909042e61002c1d00200c1c4560982c1001c5061100c040c1007a40200030600800c44450404015401e0155043c40c0c50007103402d50080032906861606c5c24055260b00b40000000d0565109080d84042c0c0c0c007640b45008603d0207030350141d08a03003450a00070601d03001404049800d01d09000d2400841c3e081c040090f00e40440f500390517580b584100c1c1d0845291b80c1c00714810f424030a86c00d0224016041440007440c02c141c5148010f5960345036164129456a484400160940c8824001702 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 242323687 1250 242322437 242322461
    0x60519050a120524040317010b0a0e011209050106050a0e0105090601050a021c09170a03170a020702040e0717190602070f020916030c03330503060a05040204050606030601050d050604 80
    0x340080c080720b880404040b02617405800142e80200500c3c00e164000b88498100d4540d0411246403030740c0d0b1001a56030840c1da04445043c400440c1e0b40c102600102d000b1220034621500002981509090030005e04a074182c222001c46a8410010310082d02c8890390941c100758242881c503181d43e407650003203280400e117500701e2030500394595140b500300d1b400003442001d4485d00002d20011044050a1307540d298640500940022503c1c024942c4041d900e80301e998220503403000c0075282042940109003076800c1d00d20880d10a500001c4208261885040b200b041091540d02810814401880c51085c0c0007180030041c1040e640000c402c410042c4040414410395809030250100386070240002084004a09940c40424104818540914840c0c4550104003520200804400c81003582c1da600014200c0140c0d4198074400c0c00102d8039503404c0100500c51440c440f0302256070f140a1060005586000d44450b024240030b0043c40700d540c2c4c0001c00d4070b085080441c00018075079168000507000c0e15514600d2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 242324937 1250 242323687 242323723
    0x7081602130c08130b04030e030f0a1406070e0904030302180a09020d0c030e1509250623030705070609240e16030206030403050405040f060519050a1205 67
    0x41010005035402c085100b81d810f495070640da03030b5405159000124040390050030780c034441d0300040c0000d0003440c0400ca41c400c090112601c802a03486501d282141452082e00c0000f2100034101e500801082410351121041c070b0244a40c104a0012403020070000c0d000400703041d000b08280c0c0078811420241490720782c005195245072961409100f0007075001240034410541004842007035940603005c0d00c058101044020030f8842c4582c0f025075441c20001d04200e04601501e1054041e0340c1c0615141c4900f0711a145c0005070061801d48042d0098500150103135040300701b42c0584460404010035654840c1c02420255510180ca18145006011141004000d0640d0b05589001040c003050040f415102400b010010040103d0090340d4402d849050740c44a1190284e06000500741400a036401600c00e0614a0405441d540040d080c1d880c01c0102d40c3d0804d80d122404c00080c50404080d03184442c800340507031145402d00d004240040014080c548061a0003a21842080410041860072142e40d04007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 242326187 1250 242324937 242324959
    0x515030a020c1e01050604050c191b0b010e10030c05091509040305130b090a060507080c06091027080901050d09060207050607050a1d01110d02060108010c03020f07081602 75
    0x103c0d8400703903080e41400c58942c6810001640d509207403284600407110750035203e040429410741610b0811700340364141d04000405c05407000221440103601d52552040034440c415605101040290b043d00400200c620801a001000815103031401c0700d003030b035005548034a803d03a14003620819041141c2c0015803c40150b00801040c19401400f0300140081c0e08490210035642d10060400d50103454070b40c950050038032100b00001402071000309400b511506e000e50804001444a40c24230701d0441e52140c80f60810903030512b0301811031207040300c96802d41c103404801000c16441c0c40018400108000c2000c4800103803d600307030303024600f42c4000b02202c00c03061000011b90300d0071001a4000d00000c481c0c80c81a000031910f640e00900a50705000c2d5241e03581c101043c1d040c3c1c085103130750344001c40c83c606000386c00903d907800700814046000c200d42250018031b440d5140400d45030071a001c1520032410148103001544a0f03103a110200d0311815003020800340c035119400d0352038065020b945d400950100c40000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 242327437 1250 242326187 242326213
    0xf03131a160c0807050d020a05040c0e0306011202091e150406181e05040314090f06040b070b0a1a04050414010e0a03080615091201090203010c05040302030c0303040515030a020c 78
    0x1124107075910700040d01e159503524000d02c01040c0440c100252300c0000e904d424801c40c00c050740002085a100e00e85103c040700c96201080c03c0410030b81045d4101300400c0890419420700e80100d98000000d10000302c1c40d01c901c2c075513480311000094401018040029007000440d079450300709002130a0542407029103085481044802441c082c00c02c1c00794292180424041c06a1521840c4e1040344c1503100e600010203451071a81041d44031020f5541d00c01d541c65500c80c001d03152800580090212400c0803550f45149052146101000604115046041210361412406000011100600b040d0350110701a243c503d452180340807450b0700301d05c403076190000d103d10490000500c08034075402902e0300c07040f0ba21002c051025094403032030a5a42c0c00410031460b00541402c0030501101504000001600807055000a00390b0340c80a0410f00001c50202d028801e40c0340c1804010b2460108800031480c0601e002d02003001c1c0c7c0d031600b015000d5040d0202c00514000b10680403138040d101e440060760000c0c03620320 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 242328687 1250 242327437 242327453
    0xc0415080c060a09060c0602070c06120e2d0a061104060f0e0f130905010903050319090f020418050d08010e16140904090f0b07020f03131a16 62
    0x12084034800c0c0714014061006050034021100340b0710050751103418503410803800303940a1402d0750702100c2c0302e9402c20400c004510354800440280500d5919090101c0d0b07944010025540a52101e0129811102801822140c41c20310200c5020f9190091503541103034070562810020348503005044a03040c00c81510f07603003520100800a031742840d2690413081c0c42d00c0c02c0840c2c0318405d07040d10981060000d074100c100761a0510360343d0000002800003007031120700d641d6070310709440c40c2e10030450104030003006024160f041c2c80300d5140c0340c5802c1c0e82c0c10080c03c0c01c6500c400ea40c0210080c8040e01880e640d0004005040381201d00e120f60b179401c84100c4410041043e00104160307403d11801400c0446400031480103000c030711904070414510760300d180103003201c1c5000381c800c1d5100366483ea60156503070105200241150170307483c542c036000c2c1c042d01c42c19180c54400681131820b04400e00c92103800030004009e01d10046058101907444880c2000c41100e4104d040460ba44542d82c0307890300c4096001d003c8002c000c850 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 242329937 1250 242328687 242328689
    0x3021612051b07031a091228080603101401090209041b0e0f011d040510050406062007030f0f03030902090c0c12040f06080603030f04030309060318080406110c0415 72
    0x31150484d88030400903251a242c0019102408941c011309450300780781207c0070107000605428442d001c180c1801d1206504290b007500100e01c040752402d400c01903203142c10310aa1800005003d424811101215208142114140241d08420380d011070040055213660340800740050380552250035070045034034003820b4030103074054035803140b40003c40603080e5500c22045220182c900c14400c0c40c2409480040101802009022009020100b540007403c0c1e40c450042c10014481600c80080c00249050003500400960714a01c080758011301c41000003400b020303ca00d0101d038100b10100951700c12842c0440203080d680070060352014011081c441440710210040c10601820800c03240301031264038140c6824061882211524041c0c403030b04000040c0181a4540e00010040c01d0740e19000c07094825243c944c20682060b070000e0300b481d200303004d8141c03d481a0903004007907451042c0c0321502d90f61807803482d2050340101000c100b4184220581140200505140c500c1c0040c000d000e40b04003010405c01520b19 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 242331187 1250 242329937 242329943
    0x5030106230d08030c03041a010b0a02010608070806071805030102040e0901050604060501051801180308120a0603020a03030f021608160504140f09030d0218040c03021612051b0703 79
    0x40d00c200d4100b40351038118960450750000e08a41144d64a924045081d00010000c7c2d80041c4002d0484191103c170314015800b8140341c0c40d14a80307882c24204000d084402d20303000381c0e1180d4000c900500030f02e440010410f511034850700d40302140a4070b4048040758001d05a0040360190300105011138603240108000d0303c52241d80008110380c0d51044104815145e140c0304047c0496000c00050f0006402024040b40019041c10700446000703c443c514803980855500941c1c1101c8041000e60702442c10040054120101c00d41c1408060705640015103409a1444010107006088000d25040340c02403242d80d4140d50080848a2102d40d55a0030759195402c03006c01552143c10f685001ca4149170510030510081014440f18100da80d403030320b00704241d17000908244c1c603510040c0b000c040c042200e400240001c0c00d60030002295285104c0a2105441d07d5444900c141801488007004800c9250f20b04c1440940112050711199440ca0042e215449040200c103080b024180030000030200000c2c83d8411284 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 242332437 1250 242331187 242331239
    0x3020a06021603141e09180405030904180b072303040302070311100509121c090f0f05010807030b01180f0807090b0a0902070302031c0b0108090d021e0705030106 71
    0x2040b003e103950144607207a04200740104a00c51030340601c200c5c202038a036111003d81020002e440301610700300d0652044034101c1f083c2d44000f0300f00e0b0b41402d1074050b0701605640a03031700c1d0b4000b6919680b45060000002c0181080180710041d80003011242c0c4200481e00d21111115682c0b801e00d0705000b500c4400c1408190303080080f8100c0000241418103108040c072445907103080c1060701d0002082103107802108500450b110305119500314010034203d620000da920345031b0025007480e00040103165050356100c000f40615020302007144d07981151000f60701c03030080e107000620026803600680c1d40c88402c03140003064510108020522910702d600680c01d5034140400c40d40b03040e5880e21503809035a80000007580008164030100008481038000e40081da2081c0180c074200075005880c0c0e030b60304141c180420707407850700c84242d03885650308440c400b0b40220b822000b4000081e03070141c01969a091200c03c2134001c8441e18003004043c1018801280138003002402805040c0e555081259044030458040c80184 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 242333687 1250 242332437 242332457
    0xc01021501050d03030e03130f0e0114011706180106020109140f03041e05060313020f010806030d1103040506070c061d011b0305070b0103031d061e030403020a06021603 74
    0x990295031090407101c0c010140d0380d007200e2a5800f00c01810000001004a11041c84404100116800410080d0185246452003030b8500f0703a016603494410f9001d006004103072a85020503076403140d10f4607002c8241c0583d00307806442d080046a0701c1032481c08142c15502812001140503a41034000c94003c9001c0c1d0800c00c0c103041c51810842c1c94680c14043c0c0852a0700400c0100120400b945007440110401004a0010b695a0000c02d155a1084900108440c9000c24940440c03034107092a10a820080c43c00040b1403074400007095407130740d42800c01014011070044200440313100304115400b4201c05412561a0003c40c81c1499a02003140100e0022510010320107924805120304d49454440513034850030601d1188a0544141210000c107801f041410080040403550b40084d4038000c6101e940d643c9590401e40c640b40768888202051144102c40421411041c024800c0e02c05521003200849569242c0310791405901c0c2c0300c0180b00c020001c074008511000392111215140c0d90343c1d402900c81500c22 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 242334937 1250 242333687 242333713
    0x61d07060212071b0e28140109020313050f010e07050d0b01090c05070614090705060f030c0306040e1b1305010e1501020c06040905100e0105060415020102070f050c0102 74
    0x200e8182c1510540b58405010201c08101491030883c0c038110141100e198864032a82d41025000b42201d1049610040c400100d0030084030040040003010501401c100d92000018890b622000620503104043d4011004c614001e00d406880000c1540c080200c8004036511458680a8000d00280c1d442c1707030107801c2c400145800c103120030840e5194412103420380380e07003000301035002000030419103810082e0900102000454912030004104101120000313586400040b09140030920f4110a020354410711040034040304038810b8070b030003210090481e51240da0710f201141c0100407691000040b88a100d80035881040d00300c11120a5080c1074910304262420502600d041d29002e10410440c480c0e024009440c054000740710440300e14052050300c010f405540c00142d100d0b00180c00c8030b4000b40da0f40c010301c00c21040b002c05404c02080110480852585010001000e40c0528452103104020b460a0100707190310030360499002c3c41d4400c525954850490400d207a0724102c402d60b00f4050700c2800140288 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 242336187 1250 242334937 242334943
    0x10210150e010b041805040507211502130b090d021f02060702060708041407180e0c190e1008060703091a090d0e03031903090c090b060405060304020d061d070602 71
    0xa884100c82e4400940303080817415002000014026619401841c20105441c14507180c007501011490141d09011441400c2000e284624183c281392064410000800343d110070074042c0c402c84132140b00c199110796941c008a60b189810f9903000f584071050075000780144110f22800320102c074503982160365950b1120300507030359010207860310740c0490090340000300014510080400f01c080094241c5110316900c24490405010040106d518240c03a41d0170b600119400b088154100e94003115500030207040200c2d034007215030150207180c9400340e0010004022020440540d801064548112401450400c2009000305211801140c0d42d8180444c600500d40c2216203d0740946c40b40c401400c0351a40d180000e0315017614200903250140000d10210741c09000c500c0d00b60000307200c2d54802103403081c61481d0505112400c0e8000c65210352030140490b003e900ca0905803000e5a405641d510f030b50f80c4072800056800c0d5600e55004102c0b5003030a8489011110302c902c41c11020510200310f60050f03880f000700340c2e2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 242337437 1250 242336187 242336189
    0x2031e0a021c0e040c0c12020c010e010c0b04030f090803040f030c0524160f0b0f06010c05030f03041106070f0309080a050a2d0c0302100905100e010210150e010b04 72
    0x2c005040d90031004158034290b809042d4001040c14448614001503860a5500441e400b140000d07802182ea92030310755030005c4010b800d8800034070700301011904075564020307040e001420140403c4054082d40340c4107405035186502800c0c000c400c9a0700c0d41d945407c041c20100d5140400c9591480484002a140c14a984612030b460441c09056551100358450010b080c1c10840d10a50929124030107a0041041c821407007851a00414050380e40f490002a10321099101400590420090a6180c1302060000c4283ca0207421001c00240d500d441320300b408050340300b405800980c85200003840300108403240c042d10b06018401d40710600d0301545c581200c0d0715607000031006030294200741c82039000261124101285075001451210745940b80d24148104000c0400c400c80f408880d00c48144194580091540c0b00a041e91405402403400c05011070030702501c600004e010702881d4a000c0120341c2c024803600130940d41c120b400300402070404ca12034010b400b2900c03900391035030803810000c121440d00508a038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 242338687 1250 242337437 242337493
    0xc010c050a0f0c030216290901050412030c060203090102180f1c0c1a0406030e0606101b0506130204060806010509061e03060115080f090606060a02031e0a02 69
    0x2c10459003616042d01d0003011102d0031802c50103403003089020855440a00d07809064081c4000038200307140140c280400e549a1410300160070b048c02203c0c1d40d41e910070215400c1d1040319408115a245c01e10b8242e8009002c0d6400800150011041100304841540604542040c980165288605460601c008101030302e0049070000c2032050104858008228100c3d4000e20900685040325035a2240048089518040048450000808003c030747c0d4140607484420541c0d1014150504001c00010b9003d104042c00c1c81c00e0000e01c0f102ca4460200580c1100003a0380c01105841807440c145821011500c0384c2e9508a1140d46070200110780b0600c00100907040c0c039005800c0400a84856013042004400d012003034036030340300d02040000039403400c0c0804ea00802945e035014241c20803d03c0050b0000030000e02c90b411000e0100704221070b58030002516904001c094407055601d181c589022821441202c0440d071200e000e01d101400e06902420041110209076400d84003049808803101600d000890701032 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 242339937 1250 242338687 242338697
    0x31b1e060c1c020a21060e070c053f040e070513090c02030a080604021603030b0a0504050411040c0215071404081603051908030a1518020c010c050a 65
    0x810050341c07035004011800c2807621444511101c1c400030400d80c0c1c030a000d61000103941c1400c4518510085480002d0b501c0c04c40710500c40b081c10201d1030f03961102c000305814100400d21804c64213000003881180d201c480c00109040d4404103002c0004400c1c040e80d14048016104c00c0b840c0403e40b003100c1e0560342510024044140541c86504003203d468001012a000307141038190000382080c07140c8a5039402100c0d5801960f183c54180501500e0301400038080c6015600411400090a80e8403000450417941414005903510401c03020031804c5080c1d07004650000d18040902041c001d645000151141d03080390700f441483d6200b0812601c50240b5029516140d61a0011548050140e40c00240c0001c10001c614100360341d41086601d007982d011404000c0b040d800d0b90500030300c8401c0c03050f214084410380305856040c2e183e5640c1009880002d0281100f07990714440f2002580f501c0c21302100421480c100c81c8a501d919000314002540202c3c0500529843c18481c4901c0030f0142c42a240441c10589030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 242341187 1250 242339937 242339941
    0x9020405090c1f200309100314010504020f0d470d0203060c0f0d0513060b030705031b04020c030a08101a0901050706110f090a0902030c0715020408031b1e06 69
    0x8552501040070384138101804240b203002496200da00c15400811800c0d0381c003240552050010081465060f00800d00403801004015203070441e09080b1405007840e0701c03000558407043e11001d00c142c074101800c11903582e000982c03417141ea8141d0018440702c0e00000b4036000180041810845850688031000b9019000800012441058240507102c0040000c0b5541d05d48034a8607004011284100c0d05681000f4980030302c0700500c010f61141d4a00000148e00401c0fa1342e04100000b0f076076554907082a0b04800081c2d0038112107440720f40654002c02100d004807511040f00b000090141e007400c840600740c07540c080c080014000480c8169844084543c9980c514040603240115900c1c1d0007484d0070f40b011a110510382044003000802880c020054626540c0c90700000010402e5000065210348061030040c81072010450942081710342c0280d0098001c00c8140c81c01d01050041c1c0103642c4086018080800c09400d440c075280403204610022074190340c82e0001c240803000703905a0000d1110913030752107840 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 242342437 1250 242341187 242341217
    0xf06030c0813022b0206130e07030905060a09080d09030f1407030806010c0302011d06060a0905010f210506010f031a090d050307020717160e04200409020405090c1f 72
    0x2803c1800192011202640b1380700b070340c000c00e10540c400c40303641440d841048410445841541c040c25041816407500b40041c11841d2103031030741e6060152680648039528202d00c42040050340440d0440c0070006d90038825007211f82409442c1c5040c4092001c08902e6030390780b03420032f918400700b01e845882e03042d280c051094480713000440300b04448800803405d44d940e0b4044000c5040c0d00340d03030307004070031189400406062419400f44403890340190301c0600650704000040c03120350510b29002c02940d48002a031f0704218131512210900b100400d4010300b842c0140000031880584500820081d00e001d0071080884001181080d03078070300000c030baa429054001e00892001648600b00850f001425841190042c6448a54080d40380280c0a81c002c0c544c0c0c002e54440761096106040c1e9002880043c20051301842d2544642d20800c0fa020944002a00700b04105041540c50341d000f4005580c0140007004030386401c100380d90f9903200500307110f4494034a04420340c1c8082e000c0c2d100c1c050711504a0790350f080c1d1010000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 242343687 1250 242342437 242342479
    0xa060510120c140315100f1d061306020604020f0916030902060c0706050c010e010504030512190e01140c030705071104021204081201080d0807080a060f06030c081302 73
    0x380b02034080040a1000049403030311003014500a260007007010343c00103800410410007003032440c08038040c0403001ca00701062a420481610400500d9500000407118101c0000c0061140340714100314841d20b55400306410384c1c00190300344510320a0741c4200c103100c203c2c1704020043d001240c20304102008101100701082c420380006911501c050301150a201003880564185202134211100082c00072807a0340c4d509009005503950b40c0f64201c000c00241c1450385000341180700d10b800e60b070b800ca02e20002003400780011004184802e00007460820080300000d01d118040c0800c0f040c07082981d071001c00070900e035a000d401124006c08140c0c965034908000c0d503545803405845032820703e5010390300380050019031030090180352240d8420a8115039410201c03224602a00e811303004800d0a0b40200e54000ca4a03400080954001c03100b8200782d01d41d650b6007640c9402414040c0c100740c02d03100b0144000130744ca0307806802c40300341c140280c0c0360420356a84408100d02ca0b0760200101035800351a0040034441d4900306 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 242344937 1250 242343687 242343701
    0x31f061d031f020a021e010c18140607150606050a0201141006030f0603050a2102070b03070e040e0d050a120203130f0f1a0601120c021b030304030512030a06051012 72
    0x140141d8503c1c403079100000c01e006e031401c910001c15944a81c00c15040c250303c55180c051160f07480d8801c400361810318580b9242d50f040c5580c03c45c0a00c40001d805002d0044800041d20b030340c200c400c0180886621158000c0168204014013800340d800c100c0d0307015aa0304c0742c00050b4450500d00c0c14594440303140010440261118082000181e55a03440120200d0b20505c501c4203094040d07808502504d02d0850208000c444080c00e0b01e046401c010400d204940040d02101d82192082c41c11080d031000460000c0c004040718260158184200d010018031940c0000190001c49601d03214254440020345110060344400c6444031440502040d401c000160042e03001c940740e60240610303690300041591083c031600400700021001040d800c040003565a0b01c000b10602e00162010180f09460401d10003035030701d43d401d10038055203c0d01c0062901c01074500700262402560018101c0d802008034a202c020280c0c415180c21078090f09100c808141802c204512200c10025a40c6102600b0a000c01c200000e01031 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 242346187 1250 242344937 242344957
    0xc120d020a030818011802030708070806040201080c190e0f1e04020711030307030905040f0204140d0321050a15080303041502091002030a030b01081b031f061d031f02 73
    0x13030302501c6900f503024480d031a000000011420100420790040600d004002e03441300010303030f00401c0180702c8540e0110703030380780c0184d82800c005480f51640f8100f41d98601800c00203013002c6c1040c03c48543c25581c803000c0035411f000c003603486002d40d50281d024804080d05602c2060501460070300007010038201940245005806582d900a000c00d81200080c21a4030400050740020000001481035140500c51071004110140c2d08601c0c0c1881c2c1042c800241c942034868500c03824084c01040c0602d0300503900041c8120062900c50402401d101420006200c01e03240520310500d04101c45043e4641c4c40080c90540d16408015401c56445940d16040c8004c10b511800346a0b07003c7c0902c2600b500d40101c020034802480c1c01a64982c41036070390040c112100007201740e040084520038006540f40210b03500d0740d0100308072230440e42d90391007000714107422030f9241180302d0203200c101c0002580ba501071075040c1c0f180d64200f0f48500c00b615842c1010b50b03800c03040361050341c101e81c00c840c44042d00d00640d000b801c442748 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 242347437 1250 242346187 242346211
    0x271401020f04170f0717100605010c0f030e0603010f0f05030c1807180303090806090d09090c0315080303060a1d150d02120618070b030a02031003140c120d020a0308 72
    0x3c2c051340c0280c10002103078041d1120110858011035011003e00c00c1840420f0101030800043e40360a0000b40000d0b54068050103185801e03a5135424944164603101b140d5101419a0f543d0f565034210b0045a941e043c440c1d81d003440c5c60520041000e16000c01c1500c0343c148020080d10f4a100ca4000ca41d80841002d000082881003500d03042000c0b259000d0614000d5000c0d448040030070b842c0005190a001c00204182c0c02500081340c0d60b480c0c513030810300344c074261344080c2c100144550f8002c5045c0c000b450101150201b00400102c0091011300000007144585000d0360341164080d170364030003541301809004259242c018010000f034940203090880e20744010000780718200c01c0d120360700030419141600304001c01c03c1e00070034104030300301c64240d02c00c02070380c00c0160041c0300b52481c0501101c900c4c00040c025514841e0000040b0718415401e0050030701035030b04a0300c1034101e40d0070640405e56842440c20101d01801008040d603203035407004240084030000b150060000a0501c1d60101d402c29801030041c00344c0e01c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 242348687 1250 242347437 242347453
    0x1626100507020d0806030d080a0509120304050309181003020f040b060d0608060112081c110f03010302040c0305041e0203160824100b030a271401020f0417 68
    0x948140a0a8010707180c40d0081c0c00002640c04004040c81c000a200354000da000c41103400310f882d80b00ca10258480e0b85110002101d4540c403141a003499040e0304000802c00020040c0401e008010004040030b42c011100001803441d1a92070304400d0b47d0071207402d0040603207441d0800250501a548070700d900320007000081d0441501c00003c406400c440041c1e01180d50300d2505100c178050810044e805003512800c5c1721601805507560362900d12610f180c06207e00d85c01c1001c42c49032652078020140c0844034007030300303603c50341d03603103004c5000750402d1005074481e82c2010304101540303000e482100d008a07000421000c5c1003168007580c10050034400d80480c1c240c07003580404ea0070441c02c0c4180f00042c0812002601102100040c1e40c1d80121029811640c0c44c0d0301041403184404a081c800000c1b20f800d503080c0790b129036031b120018000b0b005a10000140868102d190301c0345003c4082002d459a21403000a1a0350040c64042d5080b4002c407440c0d1440038900b04401d0240300c528031100c1c000c007950041141c5c181 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 242349937 1250 242348687 242348713
    0xb16020f0907120506120309190819050c0406032a051c151103070813080a0302030f0a0e1b0406030210230a0c11130c0806031626 57
    0x1c038030122001800100e821041941019280c0220794100d40300311135580d00c0c0c0142d8040c050f100d201c1c120040344281400d500c10920788e1440e000300c000909202050794061045070303855103400525600200c07854050402c62036140d00d418462041607075001501612800c480000a42c01809445001c8203400542840056180c0d18540020035141c20911700f90b4220109141462402c0660a01038107101d04045e10b1001d086481b6051341e41c0800c0c0b61410401036112034400d800d00104100c80a004190f000a95480d444e40580045014260850350300d40903560714020541104c1c0707900f00601c00f5400045c1c0380205d8986910403d215080300070300000c6d5007aa240d002034503484c400186900819070544000e060161003040c11f0300804403110a0900e0101c1030b040042190320842c00c0140380342e030740040f190704544400c07507007040c24011860204690044010050007020084a885101c2c0c0b01d00c0c60040c407400c01004126044484c0c0701000b50351000b01503008030345820415505132251042543d14811 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 242351187 1250 242349937 242349949
    0xc010935160609150201090b040206160f0b010e0c0c0a0605070306050301060e0703050705071101050a110105090f24131403040b030403120c0203030703050c0c1609150b16020f 77
    0x240200c3d101c19410500d450380b103450103440807041d142076900d461908008601030048aa1f4000d034111051503440f085203410040b841c00c0288003602e88408a1015020840b0312000503060715101445003220381e46169180300c00c1d1042c00b00405040d08500980000070b081600520b402041074200441c1690700c0c0d001080c00c4600552281100c0e00c046d00900003600d4140c030986800003c5460514902529600d034143d648500a0303400d81002000191410068810041c03080d40c0e40b203010003070245042c80c450b141d0f07031400fa02c0f034403030641e00469010710054884064082601c0b000e4100624803551100022a911348001c0e50a03560007400d05030802d014007080c00104050000b2050746601c0e414941002000181c0e900e000c280e0861071700d0401140240c000095030350000031450045080d6844401030000c5001e070b10300382440b42c401c503a500c1c8280800303c0d000b40c0655010240810011410301e2107201d01e103210744158255440d00700401c600c04419813504082490014110000c22040c010104d60 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 242352437 1250 242351187 242351189
    0x16020d0b390d0c0e10030f0c020303010b0a0c030215040b0702010b010305070c0b041b1d070507082703070617060303042402010e060c071e0209070c0f080c0c01093516 73
    0x4000380e41c1d10900811f42106200b07900007801a480118110760621101c00300301c1c0700d4024080c061060380d004c2c1000f018402c1040d107214004240000e2501c1c2047d1501c8140d0001c107682c440055400d000b0005410f52081c4241c5108408554500445640640398011003034006441550180b92500101c0c80b60500400020020b10318584c1ca2649884c41501030441d1050280c00f030820080100182d00c045003101058070490800c1c01300083c034800314501103001001400c41d41c43e40502541000040f41504900c3c0911005101e4071462600e40d601c0042503101e229500400958690f51340d00741c22000c8140581103101c1c5401c1c000040c040b02c002d1003c62601d03400710380c00310215100080500802070a108079004d64500d44810142c41000d550000e805c0000040c401300c204a1401e5071139040c00740070003c40003129049408d440e5a61014285140c9550f00c0100c81c60103c1c009540c00141c083e40910004280e24449650809001d00458032a01c00c0e040d4211116240c400c143d40c500d01e66287c041810 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 242353687 1250 242352437 242352469
    0xe0d080301150801180513020406060302180418141911100c0308010b1305090103050a0c0f06090510050c010507080105130b010516020d0b390d0c0e 65
    0x294496250030914100041414802001c1082c1d200c0100641026440003402c01e24200901080c160303216400302c0001d40466001075805800c141000030346a4055004000c808c010441c01c40c5407600f400c0038041665400d614151142c54484820000b10302a100c00c90061400c010a1714503545001035600103840c250b501c15520405c1c60b082002d000e02d051500c241d0340041e1405d03c0700c414040e545000d42a0481440780c5011504002440441c1d030140013440707070192000030840d480c9540c4030b060155a542c4d607402c0841c0c0d003000980021070781400145029003141d0300c07030361104603550425092107001d8406020300b0080c4242844601803c1c44203001d900e1050480d665120ad056142c803080124241c0c5481e030340c401161030010303015400d991040454006808841c10001980c4007032003c9840400b800c840130340784280c0d00d03040c8265501892040700041940c840300341080364072812007136945a80c0d4080c058004004002a0b91140840d40240072503101c41c0c10980ca00e01184030129040c0710380c6c40b20078 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 242354937 1250 242353687 242353703
    0x150801020a0f08071d0a0b0409061505070b010b0d0207020a031103010f0c0f0810080d0906020c03031306120f060603090c090605090105090901240302040c0807080c0a0e0d 75
    0x4080e501407140c900d410708034644400b4605100c000901103c145000c0600c0740700c1740816000490700c031031212600614603a00310350b98403983e843d0607c00404140c003e0014000842940324903503482401544c841c603400441840080c1d2030010349204551100c00000c00d5141c0074060103001d80e6860101c1801035009210700c0c410158000c003014219600400c10342c3d481d1f031070601c001e40e130b4590200c0041c0801301c1605218400e5102c00400310050f5903190f100e61030074441c24040c3e400099004070043c049541603004c0300c2d20004044101610b078010b21800c05c2d00c00340c5c1d680081150a02c14288420030141840e00015203050f1201190141c5078603400c80350200e40c032041280f04200d500c0100c14010b001c60b02040283ca41072800050400e4810310841c1c1c032403000c180c08130358802c00170342c400c0c2180e0001a50204001852040c228903200036440264425850000c0c0b038017015026a608910580385690b6500556840c540c1403d41034000358080c40c1002145800100c0907102c00c03448440e03d6002d0594 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 242356187 1250 242354937 242354947
    0xc1207060e011404080f21090a0311030c030d0c031d030301140612060402071b120b0a0203060a03030f020a0506010b0318031206041d030d0606030f1e05060415080102 73
    0x2560b00b91044511400a65114074003008041481002034a43c68508a40c4450790750200d20000607000c5c0500d030a4410340c01c800c00c240940c0c0c0f080021040c0007075200c0d403105210811800c0446d601c81c018842d4996140c1c03c20480e140b024803042d401001c1d1030fa0142000288100e0030364801544401c90702102013554130000c0103101c9219150f03c0145180c0040702c4c030b5440d20b0400c01c440000b2441c080d100f640116000b2a0803410004252101070001000b1402188a40d0303488a200140c0072000364103490b41c05800c8049800c4a05a0080700d200b880081c200c404101d183d507a00302c8030111204241400c6024182d240c40014600f4010b05008119070113030380342c403407c10740d4411568036507802d42c0c1e468592040102071065041001041d0f07200e40f0403100080d10000c410b5440415480180b02030400703002c0001c107a0900e807003a6012800ba2021b542d8100841d141400c2d00c4021564040c2e50440609a030071a1490104483e41003139174003040160001c2207004445c854100300034001d40042d007083e5000b082c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 242357437 1250 242356187 242356211
    0x1502010b1c02150d1d070510020c040b0d0b130312060303020c0909030d141f0f0603020919060804030815060f030901060b0c0703050d0807080112020d080d02041d0105010807050c120706 81
    0x40071b20060304080f505140300205802029546451010300709009035198181e0820540d20100264541a0840740c0d800083c60225800031881002e031500b10081000c0608550200020f0300c00e0006480c1d060300101080e0001d40208043c07900000c02d01216848208038003215840c1394082d046142002c12205142410300110002c00c0000c0b80c0c05804140708124002c00084828030503040131076516040050340da66101c0c1c04145100502110f2010118601e1800207041e6030141c095881a8069030381c84400780c40380c884000002109039143c652085041c03001d0f1015030480300c0259040b5120b10000580160b44016081198010600c94030041e0040c1004009104081c0300512264441c6d103428286441c10000140036980180500c000041007100c5c0c120440d15170303600000f8402c0c0c20000c62034542880c10101c0c3d02075030040c084e0400401240801a0b200d41150154a05882d8140c503000251f985003827007120a50007107034145040d0f02c036a00d200c0b0f5040d580000108480d9004010100320420320344 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 242358687 1250 242357437 242357443
    0xf0f0b0a0515120709122009060a0b0a020a0b04050a0c0b0c071a07060603060209040606031a010f170109090b010e190c02161502010b1c02150d1d 64
    0x5071195000e407400d0a00380300028254021100e6407802071a0080036a2118081180c52101c42e0704030b241c14a469140780303414444000d92040d075980080060075a03c80c114403c0c0442500203550a40e04049c0c44030090145911400c0544114855841200c0804500317441d0328001034801d680648494101560b4031040c4030140004e200030b4100c011615182000d0030301407668514140c4507000c0000103a142c00880403412104179140b80343c01c0310092145949a0500c900298001c1503040d200b54a04140001c089001c0c1c00f40b482e00c0c0717100c0b6400800441001c2c00540e070514801c81c880041110641c140c2d1750107410b000503103002c2c210b004400901012540f51200201c2c5040e000700f80e11540c910204200d00d200b00c0020500c8001e502b001140b1001c85220070380c40c0590a135205600e0195072900850800c01504000d0040c1c3c4403a4024000d840c60403007400350300000d044007501000c2d81c0c003813070380302500300000a440c0441002103214501b010191202c0c0455800c4800008107845407880d80040c85410 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 242359937 1250 242358687 242358689
    0x1030b070314102601021b0c10120b0d0b070c0c06032f0904110d060f0608160504050d050d080105010f020714210304030b100f06120f0f0b0a 62
    0x10341120b400780c1c20b00071424030541c03001303104030814440d01d40d900f41407407201182d00d00007213040c0500075500d44850060940081303052901020300c1e4448d48041c40018602401d4103207040c1d466403508240c0760810000c04000e020444500398110444d9105000020021f1020a101d50f00f142e90700454002246801c05900c6040e5100808060928445800070303400c01b5001ca00d02d842031b0b00324402644101302c0d0041540a021203580e4050311f0507600d00e8810701080c000b030008006000742000040d40741c6002c20780d0050301e8002d00f00000c07040b6000807a0261150740081c4109040c2c200b850134656103c0000d1450488a041207070580c01c4001c0c1400843e4100401c1c2c0e0141c8400d0030420070700c804104009641c0c8003e4031411010880010060149455034543c2900440f501c601c682050081000380c10303a641d129103c1180c2e010400030008407104113900e208400e9950740d81c51486601e140c25811030350150260344950a480d900c103e4292030744407a2060511040419001145910501c0100810a216 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 242361187 1250 242359937 242359961
    0x907020a031725111e0105090303010b0415020312131101020a2a030f06060314032107120504050106080705011704061e0207030504090515130c0c0b01030b0703 70
    0x4410300482d0b48000c1c1c000426055030b50515490f00500c3c14049510b0590404c504109010f01c5a0b0750340e0342c80303072580c81c407251101c01d00003130003161a55482c8517900d00c024416400700310703410b00c8184104881c006181d48095500d10440f400c1c045418009880201c050700c000c810004094444802c00206009a000d40242400030b02030300e005545031101c12120883d040a040c0710a00c1c080b040213031400207942d001c1d64002c01051407070310740c0d4034101004206600040d42da40c01e1160812080c0c1c000001115500c01c020800850701400350208041d580201504031401e0010380768080410482c6072151034400c40c06a0008121580b071706c011141007845030b4005a04201d98103421a8212001884a58205a0101d4001400c00405156114200d4818021000540002100028180c3c800060310640702410b504000c036490781c40c0e075008006a044492a04500c0b5440407041811182d8485061044281040c070044000b07a611808440c800341c104417034441c881c20900c040d03241c0c580b152841d1004 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 242362437 1250 242361187 242361227
    0xe0a02071101030b0d060b030109170306030609060103050c01050d060512011a060a0c11040e030a08010906051c031101060503030708070501060603020c10050910050a05370513020907020a03 83
    0x6140b4003017045440300f080b001e00304030340324502281d0780d803030941c80090b00c0d58012000d1501c2940006000207998019112140300388228404143d6044010648038101c80d800383c000d107030800c58440151015040584007609940c0e0790f03240014a5121070004220300c5400c000005070b84003d2a481d01500d20040441900070b40c400c0c0040c580b03d0b508050203008664212500c4100f4a0301000020098174007004003100342e020101e81d00d05c2c0540c11030412410b0795010041841200d03220810f200c0ca501010f01d0000d84400c0344d00150000c68012030703070716202080d503400201e859074032240400d01c0e5a110400443c0d80c20400501b0700203100d401e100345005070040740307010b510b02030310240c1003552041c040403c80921580c40000c9195410300300600d0b401064030035824040380c03511129101c02880200d940d0580100b100700d81c2c10000d08554800312a65400c120748049003400048810000c10b00248460850203400380d41402580d9400040b81c4105119030080541003410701d40100304641079003005c00c0300782d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 242363687 1250 242362437 242362451
    0x90106030b0d020f03010207020409080309010606080601081512030f120f0103020a03080a032004090c0e060d0c12050c0c0d0306030f02060f091801140d0b070c020a0e0a0207110103 79
    0x42e90320080c0260554040300d18050885506000130b0081c460600001d40c05441c04401c941004071201c065807042101e034000700001e07a552034041e42d035428210b806600007074903c00040d8040c0950703544800680c50242c07605130050303040303010f503441c5902400f6a402000d001045402c3c400d03420f0481b5550001c1000b4070b0fa502035240d98085040e2040701e000051820002040000700c080c42076000f8080020f800e516040b141c0060100d07024540d10901039140154100000e0f00680c0703000700b07a1540c031484080c00b20340c542019100c80c1002068104680020042403100e462041a82802400c1c001e103480458903541c0c81d101c5803d14a400c4146060707409041c148a010000b16032101d1820104640540d00d1607a94030001c0f00c8079070184103600c007440e44408103050400b84c1c041003144e000c2c10395698459400c10b803600401005851500008001d0440f0014000104828425801c00084900c0a40030a60540e01d4502c02031070060121040811654089000400c0c01b03003280092410358002c6c00c0404c460 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 242364937 1250 242363687 242363689
    0x50604060f2405160606060e040b090a0203090c0607120f02070f0605030c0903100506010e0a0f0b07240c080105010c0b07182111030c130b0f1509090106030b 69
    0x1249108600b522040c1e4680400e500500403402c035846122071003200c3c0c1c503002043c58080010110740c0250f00c0050140281c0b01903904080c07140c00030180000300060010350701d0741207000181d403000f04a0711681c022603484034104d4403003a003d0003480c0d00c20b8091800c407050201c03009140c610071708840f404651003180c0030888061803581c0e081c152001443c120765650ba405440d031510f03100e5a20110340511514060200070510707a800039020784401d0380e440004250a41c10801c403101103016136103030300a07030003010815041307684001c104052140301c800500c1d0080702c06142034941d091000c1c100054541c0d5100240592180b400c40c050142400e040c200c40402c1d842c0c0c118562001421401800030015400c50180b00069140c3c0007401400c000080c20000300c1c0340e4010f1341c2200d00c822035200e841c5546111003450003045a4449640250a51000042450741c00c0c0203800e03445041078015429107801b0b0b00c5034550320021a898490301f100c0da41c0d1030040380280088160140e11910406182407040029 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 242366187 1250 242364937 242364959
    0x6090203040b0f010302010c11041d0307031805010516020f1c0c091401030311070806090c033a1404060f0806030604021c050304090c0305070909020301031a0a02120a050604060f 78
    0x23504d8121940303116400d207a0000c500103181140140f80d40303080e0702c050051104c82c00001030090078800e580300410150060040960343d1450300441c0c3c0810001c0c411090004604a129004c82c0e00082c00e00101d11451004116241e107240b030742d503640c1030a00040c030060000c014101c0004080c100c40402c034000340f5050443c1d200301d040c0030003420070200c5100c03002c8a40003001800c0103450070b0000c1d03c240381400d0750389940c1c5100d914180b0f4045c0c000c0c07039250302c00e9894001d072903004450401240c0e081c02c8198072185040b00310f00d508640502c40360744c0b411301d040000080500050003090b20b420701130542c81c0e500a0071343c201c010285442680b0a100300720041c0c0391101620103026400b84030042c042c11600d481402c6029a402c1a04021324151074603c940740d250b00450300440c101d03194010216103a5030010181d200900000d008110840d121040b501c652040059024a0340d0000505100d0f13404a043d02d103000030f0b15500d0f04e180e180d00c2484185d15080c03260500900c1000c0400c400b80d45000c1c01149 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 242367437 1250 242366187 242366207
    0x212090d120b01050d05190b0d0b0c0901050408030408030a140304051b150c06100b030124110f0705040e011401090f14090f0601090612022206090203040b0f01030201 73
    0x29409880d00b4540049034040c4081d14021202d241003480289407142003081440c1030a0030b6100000d0400c002e4041c9801e100301002c0540c0c4d0040381008107942d070840480c1059000d1201c250401004100000c0c40103410300141001d007a02070b019550700c003024203005150b50011400310800398010010f1000051001a89620010012225103d10b84103480000c405109502045134400000a09045d504001140c1e1a00c0754080845400140d030720f645000907a40000d024550b1410319503800200001e441c001414403082103890325005000008180d00c0c02c003034100c3e003034980507800200240000d00e0540200c444202803440200200b04841218604040043c4116002681c0c1e540420b0690006034200c144504071401e031110107802c0c04a01260b440c0030391145c1c16000e024007000828134034014052001100d04480382000c130448603030204842c010700280d41e5662241c03514588071000c000ca025800060a804070010f8507480d00d81009400400d00600c01c11140c00c002c00103000603078000480c45 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 242368687 1250 242367437 242367467
    0x1b0303070f050102131d0906090703030e03100608011514060a051b1e010f021305120f0106082104270204090212160c030f14040902030403030212090d 66
    0x1c00c01a0300c90070101c0c028403039506128000484954045080c00070801007140c10000250042055511844070544805080d51f0702c0c00c030764000d0001000403c1c46605144410000102038a0351058041c048100b01c402c96070200c00c507a5100c01d20704440001c184012401028004814a045000e09000480a2040403011024008042a05480c492401720001400c02c008401c0743da0340084d51205a40c400c64038868a40550700b00900c500a1100500a6811030445131044c100998141000c0008400c0090a001170368030500400d2100c1038400d004110084c29a400a00008000705900c03022500f00e690b07a01000c40010007080203400d081203101103104c0d1403240c1d02c102c44ea0b40003038001c0184c030541d804078800d5400410b40e520020040c880590140700c48018070b01b2154002001500c070512001c201401040c21191528030706401800300c5607000b00c50400305031419880c0c9183c07008070b2300151002d40009074042442400800130000c0103401100785002411403a0f4111002040b113481d101d0f8103 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 242369937 1250 242368687 242368703
    0xf0a200a032102070606080307170c030a0c0f0b100612060f05010c05030705061005040e0f0c040b04090605090c0a1a03070509010c0f0b1501050918100506070f03021b030307 76
    0x809488400c2c2c0e0306072071009074030420078040181e854030025a26023022100f5101d111300d0441c01264903040204540031a5100c5018600304501c102e000e45403c299a0b0040d180340036805011000550009901c1d4880c5890340b4100d500756041840042510242000c001e16a0b4600b060602c400b044a480020072601c003445c261101c21210b02d403c5045000d4040010940d1080105000b49014240c0481003540d0301907808000c9100c8400d8166034a021754030b0307110030715003002003041c110742440c0d0000310174880301410103d01003103e80c0e100c0c021a9411155104513401c1201c03144490b19182503000e0081030b0b00302000b1003040345c0c20603046c2a0b10018020206104001443c402c640c0d009005024056400c40f10301010b4940e0360408059020381207644d0003100118100b0b2282943c0140c09a03451154050310854650300c0400b142d4882d218094680a1003200070740c80003602d0703943d1341c0c000d0aa840c0f0074000c010b078030b0140e0f1030041d20340400440004881d04100880202d99140041a20300240e00300c024 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 242371187 1250 242369937 242369987
    0x4020f0111030705010b1309030f030f18030203031f0819170c160b13050607020f030d111501030209040f031e03020a020f0102070803010b0705030f0a200a03 69
    0x580781c41e48803111400c40740c0000b18680d404e022041d484035104804c2a074406c1b02000c640d48003201112450b5500a02081d100d4102c2c0744c4c103610951000800e501c60510010f4820000d108a00c03604410003002c4005034070000c10801c041c802d143c002866102c42c110110030941c1005441522242c40402886003180c40c0700f0b44100780142402d08450394980201a40d640301402850142c644075000c140d4841d041c42c1d01400541401d03c0802c0356805e9901030200c0043c903007050b0410003140e200141c01c0e0f0780700c0581070b40c100603540c1c2400881c4103550b45071162800480d00250300f90610541c1482d422040e03803010010400b5132107041035142d1050b40030000d200840c41030720301aa042d6894580d5a600c020a102071030302c019800d0342c001e090034141c5408035030b500002561103909038410204002e100510070320040000d121884060071043c0d106100796414400d400003c02e9a0b50884989940018450070703000c801c45100a034403900c0d00c203241010740303040c424580b0094076040d2100508040300c940c3e024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 242372437 1250 242371187 242371189
    0xd03050d020a080103030e01020d023d090201080c04060206010e07050705010606020304051305010f170f100b0f0d05121602091801050705030709060c110d050114090a0201020604020f 80
    0x204031800401110300440d1100e0141c0c500034080c05090004601044058440010030f600000707503034071045003e500605880100c4954440f03044d03502515132944041d141400c0c0110140d294204500d03841c040b100046058281c00010090140070300b038001001c90800c401d000c0a58040344403810355042000e1810541c440d42401c0366203100c2d100b40504194a052800700c2c410364040020070444a040f00c10a10b00000c0c00585011902c00303101b03011803d441e0b0441001000700e03822203114840c80c024250b5403100c5006862030f0805d01d0a082100287e699400c882d0510324080410b015504029504007080800c0c59907000c2e0303200c900b1002a03001c5e030f60108034021602e000718034104165074050003503203075030504103000680c4c1e007030107070305518a942003500285805201d0000d50f481802c0303650390200518581003043d684040c080d00309641c0d0242510790b00c41c45803524501e044900e4800c000004101c1107d0004202d42d01c40944441c000c1c0d089813201d81c0141c0e0340010400e4219170100c4402c09000e82103c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 242373687 1250 242372437 242372447
    0xb1002060a09031e20030921070305060a0f061202280504020a0206040507060c030504060809280b152202091f02060c030601051209120c07031a04050c0d03 68
    0x89502c20740044d0440061001d5500c055104448075400703000003c5078040b0702206882c2e01540c4003554200a818003000600c00d000c0c50f0105c64008a041500c8000303480c0d031503150074070604845180c0815143c5c17141c0d01942001f441142c0090071280011344d08649541c2c0000d003810f44480a5421030b612000c0040d60f4640020106802400014004c640c0d03401d844002030b480d1a8200c909803500e00545400180043c0141d00c0d6030402580345d179881e403500d8242482598004805091164248503101400100848400000302c04038225a100c40301144a45000e01e140c100042c003011080c3c0c1640e0301e00a268640d4070701d6045001000b6403644140c100c8404c014000c0c0031780c0040303580c040d200b05203102c2c4803159404035a801082580c29207060703660300c107020010b51105603100790002d00f0400540110301001c48005400c40070403010341e0700c02501100d007118903410003a10a1078541068604004000120110710081c076000498820585040d444003512805504040781c000c0760000525000c152040d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 242374937 1250 242373687 242373707
    0x81e0c0d02031b180901081207030f0c171c15090b0f0a0b0c1002040614090d1505100e24030a0609080a0905010c0c030210120509030a030b1002060a0903 67
    0x1007141d83d03031901c0680d401200c40400f64000729014020700c0d0004100544c0218030500f2460311401d03541d1800c41c450340e0486000800c09000400c0000c0348401000150000d41060100c2c040c46810540794204c1c6040701d00040c0e11080c0c6690107503d0100003034624510340200780d04407911400002440310100313000c104410584100c213640950300340c0d008034015284102820031501c9800880d0b85015040d8081e00880c8210b00508010841c01d0702e240303810460313135401400800c9020780200d20011265070303100b609014100440061a17101c0042004122080110100902c1c08081070304c02414201c4110700c0c5808803d5188201d00c003100c04a28198400700a041c0505602102c20811001c190604070000c3d0403011418002800e0340000282e80d40c0b08400c201c402c0f42e0840162043d0f2483c0d035003000a02007414071000140a41b0f903888189400f000e100f0035202c0c0441c5c201440d0388010301413008084403480c0c84100d100e03c50019103280d1071980025040d50142110303100240100c0c2900b420f035024804 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 242376187 1250 242374937 242374981
    0x2010527011d010603030e0907080406231602010b010219020d2402090a0506280212070f0b0c0a3905030901030f05090c220507081e0c0d0203 62
    0x541c03200d04520b41015404102201e00aa840000c11140743c020130502e00401c2c0c506000250249001c00c000c202c180d41304203950000074040703c00304e0021141a82e10380070200e8100070211400707862035015680a015a001d00e80c004d101070404640342480040c404403207840c0c042c0c00b645401c0f45220422441007040c1c80ca030305100d0f4880a4000c0d841010754044c0d40608941802003c1e80f040c0016030381800c078140c512010500300c6412500c03051407140c1017100c50111541045220b42501c4040030300c41440140741d4903019008200d400b11142c20800200c240250281048010130800c0320417070b44d440280745034a50094408030482e005801c2d04454005424482c0d000e8107408040341d0b0040000c000005c0c0584072082e2001c2c041d2100c0700210303400b00d42040700e010707826070001c41111280b403500c00d01e42403241640922030070b01240145d02440c1196003c68a40c0041034030142404112038940d8042004108201040c05e418a019201048940103e00700d0020003034012003c40c0c00b404085ca1440c00c200c2c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 242377437 1250 242376187 242376221
    0x15030a0b0306010e19200d090804170705030613031209080409020d0507080103050d05091809060414011a04090201020a141c020c0a14010c06020d0605040c0201052701 73
    0x107104c1121410090f001d85600c03200c0b01201c81d1420001c3c0300c9000300d0114000700c605884001140b030045c002c10742c0c00314101d5844290744001900000380034070050005020150003007112181c00052081c5803d41c540c22261180c2d00080070800000030001070700070102e41c1071070040848245102642c010b0f02407560b004000e81c101040c0412200d415030302601d1961402c0780c00340110348481d4000c2c2d600c80000c1c000544a50803003280da4483c140940d00074050401c01806035101c01003d283c03800035507803050301c48485a0300407d0031701c0240982101c002c40c028a80e68002c21100d60303405484903005e8003401c03005028644407094401568002c2c482c4804164000e90411100d54003070f0411510f96040544a454000c41000c6400c012480043ca454503010050302842003181030038000c5e45c2120b404c1070050304100c0110644c01c0012203070b001400403204030f13040c0490040d0800040106039203400c003c010840e898213040242c60a9210740cec41ca0986400c0000c1480c602c12210310a024017100020303111501 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 242378687 1250 242377437 242377439
    0x61806050f0d05040f110103090210030509070f080d030b031203010e130501090309060206100f0e0901091509021008090a0209041407081e0105010303020d0503070e1c110303040515030a0b030601 85
    0x2c05c0000d560010140314801a80040820b080150210780c1c544001a40050700f61820582d4580030350b020980010300f510442d1032003552090074402d5514650050301c3c55401010710b41c200c01c0d0701030040f85032400d0101c001e010100740042c44103985020501c101003000c828100885c2c4002010701600441a40190090100803481c1c1400744c502c2084c0c0c403954005104450004031411414901c400036542801c2d42c1d80d510320300d8280a800b08000250005403155039640503840002c00510486000c07440010340451130300118010824230510110030301051106000402140c0300000c640c42c0340c21641114502441d85541c10401022141840040c1c4c2e24451943c0c04215004002140e211800001000420502c00d10499500380d400c01e20004015070300880540301d07036600941c0950742c404010b02d00710300c0101003c00001c041d9251840401c1c4407480c090703804402e100418264051007001900150300d000d1a01000c15181c01003548505552000440440d020905507005825072680080c210380244d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 242379937 1250 242378687 242378693
    0x180807030c0507050a06022d0319030b01080601170a15091e020f120705190801080105060a060206360d020609190f1b1e061806050f0d0504 61
    0x1ca06242000d44051140c140001070b80d103031404034003007078a1080d80680118405814900420311800116141c0050102280c081d034034020030180030141d280185004882c480410060112034a140d11541049203c10410400340d07088201c2c02c41c07101c128180e89400e41d461103601001420540e000d007640001a16000511032000e400148a5985203d11401c0714500302022608074420b010b0703041050352040c083d0002d41344010b0500781e4054540e0802d149042a1282503200e520001c03620540821107200043c032603210309106007a4481400c0e01d404c29800e00700200030790ba9000041c54040106c02a0501140910581e501300360115400c6000207100f0340075101c056200c202e46015a00103100340c0001503104040054110841304180005a68105c0f507034403112200c0010390302c155401e0955400031140082d4000301e010040042114428960710410ba004000310220b6100c00104140248610f01d4803509902c1e5800310390850038003983d24104203046401d20b00811071081c0903503103008108018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 242381187 1250 242379937 242379947
    0x30209010f090f03260703020304031202060910240e0403030b09040b0c030604090503070c0609060c0302061303020f1009110405090d0c0203070504090809030607030204081018080703 80
    0x804401d0300c4611904104403011140100300f4803ca1600c0800014100003042c2202401d00c40d80d01448424001c8000101108a40b940b001c0007c50040c2d1000808205000c0b4000c4015003ea0403071002d0010b0b420031003002ca0707841c0b000343e8129800b1683d03911274a411418014503c6040c03c4400b4101c00c041f943c41900407254441190180d0209090401001362407030100d4003248103c0e03020904400d19103944030b2a0107960001481700b9049980d032141c000100d20700700040c02200340300d040ca104225091103401042c4013051380c400c03018840c4450090340020b0300410007036480700403114005100a42c90070100d00d4101c8200d617949150280e414480804038403904404280303401940780001405021083c0000c0300d00458480c2d10b248c228400d10103107588140c00c410382950009040300c0e00707261074000240445d0681c0200700c40c4050000b031480928203050081c2c65211141d4141181024940a801034540881101d0740c0c245540e11451400c0100183c400350a2540d0440f01040d12201c0702d14000e44 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 242382437 1250 242381187 242381197
    0x92206020c070806010b0403030f021e011d030c0c010309050a08030103050d0915090e0601031506030c0e090108070b0705120301121a010305030405040b03010f050705190e090c07060f0504030302 85
    0x1c007030040340404903d214000035624100c580c14200149402e02d5030310200d51144002501ea0114007039400074070401541c14007d5600c0c40d880d20300014042c072082d50140e007009000c8d00403d1158005003c44008204003042c400340c241c1c020309000c90608a9440d0040c06c2c1321045400821020f0080700101c00d00c0b000151541d0180400e840b0b60381c02a455041a00242014068540000b03400460070b11910a038020b00507000841810041214502c80c41c0040c04007009070010350003e0b603038414288420381d000500202c3c5000c00d54100b2010350500e2905034540a0500580d01d207104005004810400e08110320041c404040e21169120b585440808810160030314003075070003503080c82d1030b254850f80001d0003a04803580900210321381132810301804081d1456912141d8155a1040350540c1c0c0d004a0240510860342c0351342d101c0c0d0361000401202e400e100300f8000038042101b003036100240b58440300c4c2850f400c000e81c000c0343c940b24880c0f49402c80262880c40446104142400e060108040c1c141d00648 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 242383687 1250 242382437 242382457
    0x7060c090f0806040c1502010f06091a010e0d06050612060403030501030c050301140106031a03030d0b010305010b16060f0e010c0806101b0f0302010b1806031603020f09220602 77
    0x249a603502c6a50701ea0703400c0c0a0350017070151a80c5480402100d180c6008007030020400c0c0c000440c103801200030070f01c110b0300d02e40c1c031800d142c40c0c442c0084009001c5d8080000b5907a042400c1070000c0030200400318080000c0240c00401d12656034010a00d1580e45005445200c3d950800301d600c9071500f841c005001d01300c203110445403000c0c0003401048900d010301603191015100c00d15856980c0c81c180080340603202d06e20700c4d80000030300303184144030b241ca05000500001e08540c00c0455403c0050000404039217050748400e03030b003a405016000c000d010301c01e19a0b286039040180803d10038558900d00d4020004000d04205561038140444005038111003e41e20030b80044030b8452000361808003d44d01c400f5496026841c0311001e19500700040e0b59482c0c0c1f1070a85002e480000b655a46140108440c03503240d600301c0d081c3d200d0407801c00406103000c001c2010f41020301f16020800d10300d03541c0892000d40e0103100c1c242c1300d4422540069110b8002504040c04074000d1000c1410451590074100000d6001c07403554 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 242384937 1250 242383687 242383709
    0x90403020c0d06140c03060f010f0909022109010e060f0a022109010b03070f0e0901060f0602030c01111801050c0a020303031e061203040303110f010c110f0622020607060c09 76
    0x941701c0500b4400da9100b180050201c0801c0d00c100001141c03600c407600034002c180180383c6004236803010103102034801da03411205440e0301000c00710140000d0b0303e00101559096810522035641d0b0301400b0a682d6003010916240d10f40d5600c599283c10003a005484c1150714403a001076400c40c611100030085070158030844002c200c1300c100c00060603151a803034050119007900c0490b08120b40070204503096845404003000180f0f0310345442103042c40690756484600103a101141c42c414995003840307258490001c190b00140381c940c0c86076007415a114820501070600c01c01040701d0314400740a00c0005062a802002d981e62494907560394410b96480c9100c2005565030280041c003203040c080d10f200340b00f05008000310708052569608170740c0034149001d0002c0c00d00510100180c144402d01031183c3c818900e8581b181c9090280c44500e1601c2d000000f1080c00d03030b101c2018400034207011802c040c90408001c0d10301c06c10200900104d0030030702c00d00e0001041d440c03a000c80842465800700e640800ea40d000d4200c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 242386187 1250 242384937 242384941
    0x20301090c0e06090105100c080903030a02160f030c090c0e040507081e090a0803101e1703090f060a02030c0321091216020d0209040c0e06100c02090403020c0d0614 72
    0x3446883d0001b406410307040903076140003400b1240160388042c907542c4030b034101034600424000480e040da0000d881600241c0e001e010082c5441302c0943d00b10000e082002c0d00c0a103120b1868503036406c00201c42c072a190742643d844238080c41da6813042252005200000d00140102c0c1032014004003410302c00c440004071000c1081e580c4044000c880c1c1d8060240000d8001041d20f60050340300c807a425400602036440844030460005080c02d600d840000c0c61003010301c580301e441c4c0c1c5091007480c2c2034410304241c0109500104449001c0d580c0b050142c401d4500c0a83d000381e2584019501a031443c070500c0c400b00c80521011401d984801d0700ca0004950f03045d40c8050050454444000196075144c005600e0401c0c03400600981d41c1040821008400450004001060b90445500844e810500036101230b103c015002078140314010012413255000340050361584a21401520020030348911004000c1c407c01700e42000c101030505c00c0020041070072000345030b1502650a0b1414100505880740d0002c0051440300c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 242387437 1250 242386187 242386189
    0x50c0313090507020718051005030607020304030201030f0615141e0702030c0910140f1c060c0e06070303020d0605091e01090603170304031112092803120c020301090c0e06 75
    0x141e1001120102c0031b03450102019407490002420004041c0804004c070820001101d43e42081b29070701948198010395501c0d0b0450000500351110100014911800c0080070086640b000720038211441c041d02d0000c0c90407076080410700140c400e840440c0e14000c11102d41d1490040100c0040007568422812074a25254040038441e2441040f03078001c09942d050302c03081020311910071803441d40030720082010360103100c4100002c09242812482000c030240662720751082008501c87c00b0340710700003410040726001d034600c001581481021401001c154012403030340b80400560700f102c00544402003004d0b2051900c400300161160044500a06548601c4000540c85600e88106802d80c0e401841c80c404411250340f4a4080d0b44c4098400c8080150540460a06a07010b011640050050f108225601c403580c604200c814500c40708008441d40c0c020540c0481d00741c00612180441e82c1c041903a542e00540300c1d800b07036001405400013035055402c080c02101003019030800503080e1030220361525201d4807250 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 242388687 1250 242387437 242387443
    0x1050d24020c1f09081b07030213060915141207080607080403090e07020604020607020d06050c130506091804050a0f03090611030913150518100602030705071203050c031309050702 79
    0x10304040c0c0350b24400c001048030207568034200840b0601000c11214000c0e90389c2d000c91030041c1d0100184584a1750384e102406807903202d004603040007042d0440b0b860300a0400c1081000708140712507940c0715214040c1e442155402c10703c0600000d14080b0162865031416800c060010001114100d00150b015038020a5140e1424191170169855030f000301696501e5a0a01526600861040c0c1c1e21201e08075a02000030308500a2030320480f1241035850300c805020869150b094002c0d000144514800e110007003940e1100050f508c0d41021514051407a074403582051410602903100160101c4034810324101070603009030340d03401214016640c2480d07041241d04d51a80340c2c0141921540d125140702c208400003002a00b00600318001062140c242c5650346000401000d01c8130480701d07858400c0410421000c0356155050002d00090003d9072404490355a1035481c0c02c0f85002e81c200104010804100b414850310075206070a01d41001c0381c2d52050181c3c1040b18884042c0b10302e004240c1040c0003d55210f00c08 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 242389937 1250 242388687 242388701
    0x70507031b02060d05090a02150a120222030f050c01090e040b0403050405041503020f090601080a020d0609021809010b1303170d2d0501050d24020c1f 66
    0x5075541d910880d5190401c80c0300c0c0502410690740300d030f4148100c2d2003007685485403e0151544100504181c0e00343c0c4140050580701400c000070040c001d0150300d4010350031003815403100c00340c540c00503a1540b491030f2100704114004103c4d03854051424010040062812140800b103004508031555410400c0044070160018081c640c05038201d03401080c005035003621016002446030411505046d00e4401140c03c4551003190780f1030090700001c0401c29410804070394003000c0000c0c0c6801640b45055800a81036960183c9000381090380000d01001c8407409a004001600c0e0072074040d595041185410403072440103041c454407429802000040300807400c021a2176501580040410061450301c4450301d4101d901c904205c070300b034100022042c001d20352055000b5521420300f208481d00c000c01d0604140f114000c05420f40c645000014000e070707500d9040b500589a071065a0041601c542640c1080300780184012001030390001c0b44d00d403030141010441c01e89882241004005200c0d411100c0425a685 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 242391187 1250 242389937 242389943
    0xa1e18080f030f131101050703021e1501170303040f0303020412030801030203011a0f0f010e0a12050d0e011d030115030b061005030f01140d0512030f0108010e0c0402030a060506130e070507 83
    0xc1e175980510b2540190f01501c5043e0090054620380307244845816210002000c4172034440e040b2440a40c2c544250b0403a560251400e01180c074004004101215504c1c400a04003078160311800c500741c420588650101d030080e00441410750344002940c9000307030104c0402c1c00120b100394201440b0306c403050015100181d4041d00106400716882441c1c00f44412414030000c15810030400b804006007c5d1254201d034001000100f6510141100500302a400d01b00c01101c3e480030400f50111410480c0c0c0d00030540655440300c1c8000f04041c60a1000081c010010001001d003640b15145c4000306020703644010500c201c10a8a0752941c02c0e415000c1201d41e4401114880d4403075400500502c10858050500090440c1c007400c0510700e105075480306c6e850402050030114070254000200301c24803420401180c0100940002480000f40390f0b08200d403903c1c0e5180d00305001b80e030301100084081c00e00c0c0d00600c2c010704014110b9550b410307030801040f200400703d0203108000e9541601040c00b0b540b040003282c07106c6030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 242392437 1250 242391187 242391203
    0x190905040c0602061314030d02040e060f011805100905030105150109090603031e11030c030a090e0103030c1106040b0a1814090f070c060614090a1e18080f030f13 71
    0x18840d61000e020f10081112007469100c240a501880d926506c014804bc004c1c1011041c8145090400c000c80760740040c4900c0d0400042ca401c40c1d00e004200c004a1003910b0044070143c0c0700381c00c0c001040380c007400c165102d01d0781582450240145900400304125205600303983e683d403006e845044030005e0b545144001000120b110600110001c900d40307034684030744002e240aa03941e011aa0007030313195800003104143c09400c0010010f104507041034000005155403620000d0941c55170707c0c0984010001c1c44060b1424203002c107101c1b82569a5000c450107820610310072519080b440300024804203249035007444171307500e82c0400308102140050035400d05100400f240f04558900405820b940406071800c828000c3c034003501e50001b80503024081c0503000c3c5081c642c007260201c001704403c101c0301412149613030b80b0b88500d00015242080158420104003503001c1900c0001030b400c51402c880008010b4013000d408204100a500310b80001c0d07000e180054040c50b2551101d0f8841c0020705a0100000c00301d00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 242393687 1250 242392437 242392471
    0x201090f06090329010e1f0e04030c03140d0c030b0306040809010f03020d020d0b13050f06010f0c15060e07050427020d1406120a020307050f190905040c060206 70
    0x511000304000d0041c007000c41184842c045189981c4401800f1b130809003480641c3d804005030a0300c801e24143c00070b001400000000b5107404810400044054405020031444070422012705004140801880c9000c03c25180e407400441c80c042e0040c4500c0c800c0d80002420309210b4031047c40d002402178003454109012a2619040e0340055408074200301c84001070503001c1c001000c0e80070b411b04c0948544484c1004c0030038031003002e03070410290111001107014024604410700c03030b801403081e80c40c9070f0001c030a08002c890401020390940f2224024180240300c2c5a0040307248880850540088086444001104030142c4030950180d603240a18040c445030046000080d0880701004144000c2800f40c200340107103400c001002c0078056484614518440051442c14442e0505051061041e00d810610103803495508030340c002601c2e0b4030f50780305103440340781c0b403c0d0042e0f0240d585007004286d607a240b280090391503940f18103000180008841c01c0d5220242690001021f50010a941c0e00c105c603c40700140b424 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 242394937 1250 242393687 242393693
    0x81b0c1809061f080729070308010315060e0c070b0705070503251e051b09040807051e0d020705010f02030307030e07050307080c0f03010e0d1b0b040b040201090f060903 74
    0x10452502c1c511420f99402440000c20220a004c070101400b1b000f100000c007a550b04e403200109540119055a07141010014903021035440611241903e50190856000e40345a0803548003405542e0060602e4003500400d110421a403035008140071445405860310640d40c03201c09030f03128007628101034038a400410482c00b40003c0040c0010f503501e14040c001030b110f50720b40c031252800c00742c50240758031101c5245080000e0100410042002c8410307030a1250701401302e0700c086031190901802c01440c500c2c0100b44007042000a0082d424041c260010482016680301401c41d91141c0c5c81d89800c026025400c2c1c041111351240c4071019081010703400a51441c0c440c20002c170010720710303c220b00090340901f250104150b9800e000100003880900000d29041e016002000002540c2018040c4a680b519810522074032001c14500c800541600340001c1d00c211584a40c5090030040600038000c152070010402040f401c6070100740514000e903140e100180c0c540303966000c500c0303c0307024290110391900380030000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 242396187 1250 242394937 242394961
    0x406091b050901020109170304030801090b010f050705030706020c03041401050306091302031f0c2c091305012d05010602071e030503030c0306011205060f0d081b0c180906 75
    0x26000c011310000415800c40d0300d40564120034504108411480001032205241d4415541e0340506804401000301518060010b000c046440f001e0b841442000b240070018080d090098454290304903006558609801030500e031242e1203401207442c0c84d10100340c0a00f40d0352144c03069034406c90002e451210507494031480c106132408200c100706c1e070500c01d1401d030075001e92403201d8520b2032100a040115017500641c001030240c0c0c250303c2d00c802d05804919045071203070100c48241c801c1a0000e4940c851a901d4416041c451090300104c080c2c500d60910803010042400041c040000c0382d140e080101d908128101da81042d44c01c00e110741001079000c140144200f0300000090304860443e000c60100341980e950310700d81150130445003411a140c000c0100002d650700096600402408410108402d20b0328400041186101c20b080902407035100c0f845078108074404040b980180150388444a1072048080e844d50782d0b003459190240180728090b403852501c00050309c11070003015280058000383c0d540c2c2c005490 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 242397437 1250 242396187 242396197
    0x20607110607051b0307081c08060120060604110c060f0603190606030c150519090302030118030e0a0803030a02030709120317071e0c0c090c0c020406091b05 69
    0x64020070800608000440c01c100714800210140071043e000b0480000309400c040c0e0301e511041c0c86800085075010081500345800c142100075041c070006a850300c41c01201c18400072002444a400865001d6081c008001500d030b00c150801c98052000300074a0501e04400d0064074105c2c04a80d02c2800820b5500c2c1c4c00078031785980402e01030212045c4a2032a0f42241c0c10803000301007622041c0e5254410b20a100401842501800003030110700000a9012401413083c850040240710b01c45105803254a5544203000d42c200440c2c00030020301c0800356001890b00c080e4000d010843c045040729800001c1c90800015103021207182c1c0d00614190b86d03c0300d08074400307036000620807000c1020082c00031890070b10f440c600500c1d150081d035520301c018050703818640d0702d100007400b007206000300c11800b0640614500c4203044455482c0c905000240b070340740382000c24080603400c00c0c51b80900f020198001a07511803050480e275402100c0070300989503031b034030903408449140400b0740700d2050314040354000c140100001e00d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 242398687 1250 242397437 242397439
    0xc0f070f0506120a1113080613081803030403210801061803060f060302060301060903110603010324061701200c07170f0109150c0e03100c0207080307050106060908060402060711 78
    0x1041d1030a00388401700140d07016000031000302006060a100405c020007040c1d030f108201c0c03100900003101c507440d0390f001400b4102916994030228002007100340c6046c0196001984d108012540b50350300c404481c001e46200700d175401c0004208000014074188142c1181c03002c2d5040380b0192150398210b48904001c2c0022140720f40401e500c80800000684070301006500902856407a95091401e5160110070020700880c0700b0302c0781c3c5081c001480418000b80600003c2840b1012800446011a6070380c8050141a8001c0c0419040b0181c0c0e04030601c81900704181c00315104401c40603140100603055030900402d4540d07276007540584000d00c00880f0001c0d030140f20040c501c04440b07465140c021858291445207008449000d04010100ea800203240210744201d20941004101040070802103680d0f80748400c03001414988a912800190b80203121660141243c801580e540c1e143c1414401e01038100c0c1d204140010b0013200e000109142e0100e90355000d65401090ad900e070a00c1a180c584900411500079 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 242399937 1250 242398687 242398691
    0xb15030a1217010b0702130203070201090c0f1401030e0d110a3804020315070c06150501091d070f03110304030c060f090201210905030c0f070f0506120a 67
    0x128042180c1c0c03101600201d41e03a07542d420311428002510031050354180e0008245100c14881d0400683d14a60242c815040c0f0050060301c9603a1a98100c0c007401441ca4040c4c00003801c0e010110f111004001110242d480c0e09004c924220001c0e40114121140e09480e0901034200d642c990f070744c4501c1021303003d01280c1c8580888003005119114680404075410018003200398018061805840b9110344082510321111580f01610305900070a803070362808108010205e0420b00001d0040b4050b503004485d00e40c1080302001820030400d60450021611b000d86030206600c40d00005001c0044c0d10f030203020540501d43c40c00c0e541c4410109540c080607840c03282e01030684030310800b5074540c04080518401e038026980c0c1e85007003d0b02c2c1008800c860110041c0e0050908140b100d80243c0d80000b007500c40400c2e07034500c05140000b60742e4400000d00c0007002c000c0c02d0b40400500c070f91074100d00241c641e541c610000c05441c0120f6035014000880c581500c01e40e13410403000d10050082441e6042002c0d0700169079240 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 242401187 1250 242399937 242399953
    0x30304110303073c120c0212011503060e0102030412140f03070c110f030c0105070809040e030c0f0a1509050106080304080d090f14090702100513020f0d0b1503 70
    0x1c0c44600c240415210035045880c400c1044040c51140c81c0408040709005280c03841d2085521814140780c804603480e0240452241b12108640f540c41c2194041010f243c000c000d804c0c402041511056450700c41615551f09180da81031400f5810310849005a50204140002c407216000585000300350350320503403403500c1c01e00c200414010490019072003102981d8458094048074600848144d04e03c0308c030709020340f0165041404503100050032811035202403e080c2d8071030b205468044114070655099a0308035041401002c0601000005042c1840061042d2075107044082803c82da21821014041d001000c0d01584184001e600d92004610174010030003c9442a210f58000d40345512550100c0890341c00042c01c06400d541c44101800a00400b02c0c49441b010318126070000214034500b2143e118040f682c011030324407070081240d01c000c0604000c0c1840507140c422006030202c8056003042e80241001190850302d0324100c100c6021310b9030301440d203000b40d0300c03003030707540b00203003105400468041c440c02e81 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 242402437 1250 242401187 242401193
    0x10509071205180d03060605030705220b040f09050c030f09151f0608092e0f06210b04060518060a020a0905090c0a050d0902091006081803030411030307 67
    0x1550310400a0f0070703100c500441c5801481e031410002103662801c040c40c1c034009001480e0321a0440e50886505d24240e500d5001c110f82c618603154000902000303030075100e400090143c84040c0640200d402080c3d104610790760f44c2d0a11421713148119413110741c00c0e0707042000880b00815154801e030465450011074840183d0900ca00300070042c20750381481d400000c0f1200d508400340422440c00a00000d01e0005030500b40300c030040390b03a81d040d5454102c50030420040c10200c1e4a058011550001c203009080c8080e072001400c00c5c0040026000b1801401e00c00309002c107a00314002034001c2c0d81644229820a142d88a403038400003002c010b080c0c0324140c41803c00c9000f094000f04401d074046d547c04000181e55460111014004549552105006055500800151440810036504155001c0c1011640c0b50603010495009089024000f544401c2e050113000100d40e080c0860307810385e40b141d15817148507101e034500514244200c0c2c0c40f00081c1c0d13000300002000075a210700d0295026101400316410401d03150b03 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 242403687 1250 242402437 242402441
    0xc0302031b040b01030207020306040b0402030313090204080d090608270106090509100603080406050703120501120203010b091003060209040b030f030307080c040b0f09150c03070215090303030105090712 89
    0xd00a001c070040518011409207440e1244941c1c000c002d003000c40c503101055021035281c00004001624440d00c0348005425500d0034002c4442000348020152031142c2c40d20080002904980100012445a99a031050490051009509a034010f8031b80f0720a0756561b114040b003002c1002840101c0c2c012861010307107560401d00841c0060890b0134004182458507860340d601e040c50504041c4a1503003001010404107540008480540c8d84a1820b0382d40e0344800d0a00b0b1350811a140d966000c054900030000035031a01d0541030340546032003100240051401001003100030502501c11000e1601d28180400c00074201d0f030b00600040038058400315603400c0c3e52000900b05461384a21039185d410001c1000507042d440582c0f258400e07049402c0604203401d20303107620b8541c002e40382d42c840d00000004800c803695071a10b0041c112400794210b11551074112042d810340783e802c0402e0403401a0744a8001c0401208400300381e417000759005e0011810750b840d0004016200304090325070428824a8003180310304c1c0c400b134 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 242404937 1250 242403687 242403703
    0x51e06120f030405091b04060503070201060f1502060a0c0e10020a0c0611060906010311060307031d100b0616060504230102041404020909010501080c1611040b06071a040c030203 78
    0x440040c68543e0302d003000703010490034000c02040c50300805880711b141d280c40d02c000f680d003681c08a00e03042d074680d80c1e0203105900402c1c445c0c20110b10030140b908001102da0300740c0f04000d0103048c2642a0380c0e503074980369100001c1d00c04100c6c50501262101c0d00c0d0f03218a0804081840384003400744101e5103100c11903204c940503c0d820384c01c400006860740800b6900400e0400c40c0542048941d4020002589140c8860490031000910740d4801c0f003001001c030784914400d4000c000310500c60040b20175055a140300455503142134414901030542404c061415500d05101a2203941045950440403a000e603642c850040c070b00140704440d01000d43c100500500451400c44080d010309000040e07540c1d00741460641140355000507580b00307138010840030303031a03403102142181110300030700b02400e00d5100d00b45400c400d4010030008038021208060305100388524050840310b144c0701645c04028a03840142889854480c030b1001400501282e4079640340c01c4694030010358058091908011840e40f2a070000e070403e111 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 242406187 1250 242404937 242404963
    0x603060e0a020109050105030403020303040b1003050607120b010c050606040f020c030a0203180907170411060c060402100203070c060e0d080a1205010923091e060415051e0612 77
    0x810040c1c90110358228003000d0241c042400c09230305614113039400a41e02c0c4001003004043c08804004078141d80c0e01410450302843e44642602c01d50f207040756000305003654000480f501141451081103882d401031288512054010340030348101e40d6020240720281101e43d0148043c17550070845021028030074005801100d501d9405182d845141810440300c1c0c4480b19801c600c690402428080025000961483c00c050a180032025a035900d003041101d200561209a80240c40040d501d0340480d03011510510a40c8211012070300c1500385c02c0c049a07071780501180106101030403d4140410350044810680042004011150100190b610a0b40380d1300410b0b0b5200100b11480340602c0d10107001e0017421302500c21510100314000c910b401c54840c4e40700541e004c081c44600314002c10070241c2c0c28031541605501c800c60203003403400c803048645c3d07949800f00d4059401c5005482c1c0815416031034091180511075444080c5d0780d00340d0010310764482c00c01c00751282e0780c087e40c403054440e125482406082c12410b6 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 242407437 1250 242406187 242406193
    0x41103011e06050a030b030c131e0207030f0507110d0606180c1409060f18010909090f030f050d05010b1909030b0f180601080c01030f0207021807030603060e 69
    0x4981180c5444084100da40c802600000000c14080b0580c0702c82598619030040c540868000c1342c030700102c1c0c1480030b00751400f500440820b00042003007040f40c00032010f10100b0482c0707240c41100280800100d0140290050003c2e00340c0d0100e0141030302c114003820410f40690740c103081d03070601100010306064250700100d424a894550400c8001d00a0340d566041d00e41000060289110001c0010302110104a140100c0c803008241041d558480c401942e24001582c0205580c0e0325a0f540a082403240c861002400141032040200b001100b074007854030303070341ea00909491414940b90f800380c41c0003010380b43d002e00304407080c000c44410720600e0103480d000b8054042d1213982c0740c64019040ca11a0050b94507032040c04a0307a682000050013800f41b19502ca60f90038070160940d150b8100b1060324480c00420b2504500c6094008a850341000c03900b0300c0555000d88040014080081001c4240d0044403030180d071164042d02044804d00000340342a0303012640e0310f4002241503c039924841212404102100c3ca03078 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 242408687 1250 242407437 242407439
    0x507080f060306130b0709050d050a14070605030a020304060905031305030d02030a020303040b06010c12030b0f01110c011103161b0509241c0303051009021603180504110301 76
    0x1100c016405900070005401510341e0b8a00030030501e09040140300c0c000c10300d514103400161440e1040500502805000f014640b035100103061039a82d9140344542600d10702ca200f580786030581d000003180401c9544070307110309065039a04070818009400007002603030b40c0f9486103100b40c0090030a000411007922a1031404000c0d500700810b141c0340c49000c0ea141d030203540c002c12004403040d0f000025a030703015034072041c3c800c070725a68000100c0300c040703810710024000400e00e5040514079800da01f109118581c19540240301180c584011110000440c40c40e41068200495000480d44101041280041e101c01124a0300143c0070403040e0510000500340c5002c2800303824800c18001e0017501a0040508907110980b6040c0584004a80c020004003045850031a00949549488242c0a403000a85500056042c40000d04004e070181c101207500302484101a10701091343c00d200c0c0300383d441e00154520016440b50300c541d02a03d5007410500e0801c05101e20440000341541d13240508050800040d4160f5265 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 242409937 1250 242408687 242408701
    0xb040906140c04261c0215150d062018030f060606030106110a0501060b030105030d0906080c18090a0b12060702060c0f072a050a08100519050708 64
    0x1244042c0c01003098002c2000104640542c02c845602840300400c0c40c41649820203290500c2d0061030031000c5882d040800c0d85028003034000c0740c64044000c180c800281d0996800e405024240140000107501c600d8200101c0c0c00f091103513008110050001c0c48440d2240b901c004403209641140f501c100405442d40466522802d0612000f0141c075401001041c4504281d4001021400140502410044148050640e05404004100b40c02c2e80100080280c641c031001d51008551007401850702a108820741e03d18200c0c8204203000c100c1c3c12540c5ea8031400d80b5850400d030501c4d0710030030076116460b08404918074107a441d90070050240121860018232142a48203101e00c00f00c00c00c0c0c642030b468110008011100ba004034019a0080e0440c582690b102a008041ca060f405161b602500038468840e0054000c002919003102018241d80b034494650f0f500c0f4100005000240681e1b05950003040d42d6600110060300b00c281c002a0104900210124501310030f001c035513046903200300040292044c0710310 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 242411187 1250 242409937 242409971
    0x30c0906090b060313170f07030807020a0506011a040302041b03053108160b0f0105101403060301020705060c070209060913030c02030106090c0215070306060914040b040906 76
    0x900d459076041c040912564001682030100412034a0300c5905000300138200592250360b10000352524a049072102103840f018a0507401003a403c070081a28000820f014030b00020340008201e501c01c1c0200174603820300074080c840b1050020307001c1c580b2005000c0400143d0300c134000ca5502c0d00b440d039004100500c06240c01010ba900140800788490254240444e00784440700c201309508514407032100c000711082c54004030380e00c06c100d0038100e58000c1c0c19200341001108041c4078040e07403c05481a00c20b91301c480802c074055211400d510045100405200000c001080156510075030090005007001c1654072013a080000c1110081d80d146800a491811450a800003030741151090300e2401c080c1c070b01300341203070440d148200c005014405012007030000c56600b500004064411060240550480a1400780d59404000014202d240c82580081d1980d8401d108200480d261540c4160b00c50b403926a070000713030205458545401a80b620300030411a2140d0080c02202d600c06e49001454004107000660 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 242412437 1250 242411187 242411189
    0x140412060c050f190504090207080a02120c0a0308041e03051306030b1c02040e0706020d02010b042a0903080a08090f1b0f03010204230109060804030c03031a0a030c0906 74
    0x402d0210500009440f0500071040d91103445896082d1031007018034410a1303409004503404051840d000040f05005c0003400c5001c0c000ca40d505e0b400700e4904031600b01c030601d0f450040d008c0c80250f50b170204000d4404244144e001c0c542042c0281c1c1c4603d2480000071078005210110003040d8049080050325104641d1001c201d140104000c0c501003102500e080006004031794503540400000903c100b213841950f40d1030b0f004140d95000e4100300c800d0241c0e02e41c8003a4544d0340c0c1c1c00741d54016500e44292964642402c1c054980d203a422500d20b9218418840305544601030744116001c10044454800300000741940000c044425150300d0f407440d185030500004c1d1a0021181e800440c50b0084607001301526096407209030300d540c1c21a028040b10307030408082402806998040f001d145101036800c01004003101c80d220541e0401c2c1c2c0c604c0705a58481c0000d4683c0a07003070720001c00040101d811100440d00c00d50000070a1051005050070441803480000c0011103282c00644020706480700030482c03684540304c1c02c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 242413687 1250 242412437 242412461
    0x212060a0b030f01030602031f03050609070e0f0105011124040c060c21120504060903030b0a0b1c060909050c03010c030b03100e0a20180f070e0114041206 68
    0xd14601e010303c4220143c010621008140070b40210100307152040b11140c00400d04910302400e035820781e030790405c00d90700c2e4019a078140040c02442c4011a079010710105c41441444089040d05c2503920301001143d51a00c04110100b03140502d502500031400d00020182d40ca902e61040c0103403070300f05824029500c0051703a008105000d0782c014080300103990510000c940c11140780600303115452000c400d42d60220b007400018003681c40c1104000c01c0108540c003911909010780e40030003406200b50184415080a0301461541c3c51040c0b104046501000d844485240349050012541c1903680d00351106130341030350a08481e01c0d00803140e02050ba040910a5054107140d03441e081c0b11518805000ca615003001351440c0c0034160f15038204140c3d108080103038082c0340e5403003124422004c0130a1002c80c01c452140b1001c0f4810284e00c0075040710044601c050f20b0080c0300b942003c1c41d030b50721034800540310308080040d05810720a0790b103540290b0340d209802900080519042c207c1d05010f4510302070040310040c010503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 242414937 1250 242413687 242413709
    0x12050c010e09070c0b04140304060908071a1e0d060b0d0e28021206010e04060e03120f040614091b030d050301031b150c050c01020106030b060409060b040212060a 71
    0x2040c0320390300c000d13050109900210224015200ca0802811003a1103000403601440f00140004034a0741c4142e112044810300000c0e07036600e0703444d28002413114050f61980d0001074424050322400300c4d00e4004894000c02008c800d0b07403400144842a0044d18502d40c01003c410001046650388070010b4082d524482d403103080540102e070366500c1b4007454040d082c0c0e00061046203c0f01030a0454130380003e0424060205c1c000c68900d580c1d10515102800030440c3c0460303065041070040e1400d2940002170707460800300e050300ca092595500ba0380b91a11100100250f6200ea107600104d0842c2c103420403501d00420000014080780c80344500c544841c403d2003501ca5010f90300c92154210019844005d0b241176960114002d0110100c007011400c448103940c200342d004410031104400c0701904001c2e0f03040c03034911500559048450200041e03007290064403000d055443c501d800525070349010f034000c8440900c107100014200348140049001c982010f0888056004998184000d9140c031000c031500522201d418 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 242416187 1250 242414937 242414941
    0x10215430305010f0b0c0c041b021e0d0806061e030105150708160c0f080d1d0108010308090a0b04090603021507030c080304030e100f0806040c0c080a020712050c010e09 74
    0x80b10401c5034070f031051542501010a0502108901f8420038000000c002c01c140884001005090b0b16078041078400400743c4250706002110142c032100f5104c0b4103980f00050404a144628256190392004000c075601000c10404129194101d4110f03034601034a030b241481c0c4960401c003d0103901011110b10004842c0c00740000070008100c0c0007169180d6200200016003090039107024249441c00f41c11a003640c101041d0046502c44c80000c0091901e2656603c58a000c50343c0d030000602a07407921403045c000b911030001030000c548a10000d00c20034102034600700429a460001e07034813030f4000d50002500c1c3da49070201003095140c014074101d00d890300603404515100b0745680141c044541e81100400c036510100020f024036000300721481c82c03030401918002010b110040028154201480f4800100c1c0202001c20070a090520503840442107903250401590902d8441407500e07000b0700c44250441c85080760102d034042c0001c0f01c640100c2d100d54020300c00b0724040000500b1880f0450380c800c0c011141481 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 242417437 1250 242416187 242416199
    0x70c09180c030b101d0601021618020a170712050a180f15060b09030d0207151116030602090306070e0a0b0d1812030b030c010e04020a0908011509060e010501021543030501 75
    0x6014002c91480100050351582c02c04014dc8090f804484103000c1c1181060400c541150031102c0e01041001c86c000c20030903952060300c204100c0b030403900e0f03040300740708203043c1d0500240c002001c00d0350719800b40b9004080c0521400c4140181c03480c1d1340051115481c0800c64001c0d9040402c0306080b032945500140010380e0402d00c2420002c2c5a90420703d08100340401c520440c080c0070b00c0030711740e50300745c1400e40303400c160722400c001010358005900c03103000788900c0c00068005032250085181c241c0c401006004000d2070f14109a480c1d030003c1c0e0100c0744e10342d510500384e0317404c406013100412164800d000b400c40441c110703000541180c0c503100e0594001d8011070142c0f900f980e031141066940d00c20403100103032180d10250003143c4042c0b65421200342507107070090385000074909007444d2046a00d41001448503580744e0706041c41c888800c0c032a06000d42e00c000108503540d00b4034100c6a0703009002085040300615140a0011292052505200003030561580b00c0d040d038510305e903400d032540d500c1d017024400c40d45401 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 242418687 1250 242417437 242417459
    0x21060a06061e120603080a18060905060a050c010603030807090b030c09120307050703080405100201140621060c1b0f0c041808070c09180c030b101d06010216 69
    0x25420351010742c0d050b4a00305224020901c180001900c243c041040b1502da01e8080c010b507215140d044081480c0d01c0d0442006141c01703d814064503034680d2a085501e244c00140101a041111003905000090020b007403464001d01c600300045000c1d6030f82803030314103103c00c000d000381400b0b812504006408000b00b01c0e0740210a022914811000c0c0da103810102035500c80c1c6070540c001c0308030041ca01e014205002082c404610003401c26114116901c18480507080380c00c0e402c0f900c02d040c0785264440f1807000a162440d05010750b690070b5021202d442411440c0349002414101c04480d15a8809400b007020307428006695001e4280f4442200141141849480480d03a1288190651882151542088947c030003007690649602580655000e88624a030f1820000c124000e0003070041d81c514001c2c440e907082c4400d03644104103580050b12420707510709680303e074491003800815040303650003030f01000558480003400f800c03040003008003101c2003030a04000080c103010f20b0702d4012f08005e6501e041841800c0800c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 242419937 1250 242418687 242418707
    0xf200f0c01080f090613021503160311040e010b09030c0303040b0a0e01090e0f070908010207031d0102010b0604210807030c0204060f060f0e04110c060103050c0d0c030b041121060a0606 81
    0x40f60382c0c801806e0a00c0001e01203080c0e410164503e8070044107011041d0100a610b028125280e1000d0001b00c90a0202409038040c6100b141c0e00140c400c7d004000e11480300d00240310401c009425501c04050042c0031901d5075204d640502002080090000704203640600d2601c0200002d20f807100d4440d03d000714400740c030b00c1c000c0c2c188520300800c440801c2201d409150082d008248500080d9120f4000342405070190514a0384221324150710000c1d0381d055881032094010400004010310304060030240700d5000030b00d4402d1111030084010350403c0c01f1940d124003a08004d232103030f90f658100030040c0c414041903418580c01050156030140044c800e240e00114503660800d8036107002084002c00c000094041d00400400105074070000489003d04007000c94114162070103801112581c00c40c1070700b80542085011b001410b120444102400041d00d601d90786500079014009042c0c100c0000c8001031040d1440070500040600360030914960807100340310700c0da4800c2071144104001131501c1d0002d0400c2c004d07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 242421187 1250 242419937 242419951
    0x313150e040b130c02031b0f03031303031e0504020301150305030a0f0c020a030b01170f0d0804060b0a0801050a0b0d1509080706050a020d0b100f200f0c01080f0906 72
    0x603440300074483d450380d02c405911803080311020302c01d1035007541000c3e481c0e50100350058400c501c1d4510041c01c10030001600c800900b0710200943c1396030380b851040f440410401070100c08140e100c0d10300c500c0c903400300c0d00d140024802d09100003170141043d104250031030b400f1110ba03082d1030141c0e0b21300f00003280700030040e10601c024904241898560311001110607907400740c0020b41c00310b04500e0100c00c2c0071214070340c1c030706036a0520301c03443e04154804840c940e126403802c2c12404680c8118607020074641319014494000303101702004100a0788800002c0c80d500447c1c0c000402a0390f45130100142ca8065025900031604151200510f0714070540b10409241d40d01d80c41c4402c01600d60901030f081040750811102d000d500041c041000b81401c40521010394040c4a00b000d0305801c0c80d101071964503000a04050100c615140c0002c2014118005e48034003da040c03040302001040d548030140320f05c051008000041c070071405401d807040100700141c0801e1015222042c000380c0c010030040c983d07000060031900814 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 242422437 1250 242421187 242421191
    0x21120806040e0109060504030905010c0c0315020418090b07090303080f15060f040f150c0b0702030913061505193c0f080903090108060402040f080313150e04 69
    0x603541012070090400e125030708003150f1030880c60a051240e1a1300c51400359200c1c0c0e4070040b0060f50ba500440d5454120940a400800008070400000302841c0b0201100c091031040942060f6507603d5003607100c03503000403042006454881910030044100c01e82503110303c590500b2103000f41144c0f4003e00c5810020180e100d03a00b1301502048038401d034410400114030006125513542c0a01d1024160390380c00912802900c02c00e41780d8040f4112404400410842c040c568404c400d03550140c90380214240054414070a5000c200004009522200442c21804c010104007003400c82c41c002c982142c106003088514200441803014000303840e0300d03144c00e1179891420719006144803566182200b040156010404104515092a02d416401135000c10f00703200040e112000d00d84260b40040e2032201080301c90046c5034004020b6070820f90301444107550848d07400760005003440d4454041e104a440f850304074a8140e4000700c0c81c2800610020310500c083c09140702500d06008003581c001c2d2405070a000003a00c20f903 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 242423687 1250 242422437 242422441
    0x110f0d121107050124080c0d0f110310090312050106140f0409050f090613081e090301050901020301150c0210030c03020705060403030f0f02090d080a090e10211208 72
    0x1401c00054071111608407008000f805407118240c248000200d1100010311444107000404590214015280fa403000d4541c8111882d140c0c1d901c0c00a110010044a101c44062203425030354800304030b50102c0140502000a400d005401c01402c82141c855001840500b44001440900e07800060000c7d1000c1038041181c9a00f4001c00c1c180082c0a940c0188009529100812902c2c1058000f44c0d4000c01601c0151485511146100600c950f1115000340c91140200860145441c02c00c828030071314100d019030036003044007000001c0c2c251001582d00a01c541e4001c4010701141061900d44001c414280c00c01c0601102e00f41d022550001074075410b101850341e1003d80c030003d24005d40440c1c0985a004c8295640c52a06107030190042c01000d482c10f0310a8908410124014070740c2c0700300c5100c0d03c00180345043c1c0d00d210396512032080e4492000ba8080142c0e003c070014503d010000750502441d078801c00340d901075080c0191146034900140038501c1e0031921050310300106d113001d0a6072080e52020b18100d00d080e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 242424937 1250 242423687 242423711
    0x12003090d1703040309051c0f1103070314010504031803030c1b1701200408030313020609090703051e0121020406120b0a050f060303030a0203060109030b0403110f0d12 74
    0x180702c4020b50000c600c540001040101507002850106485044485800140300b01c07949580c51021094000c00030703005412000007240c0d400f82200524a002030841b468140c890380d841e24094406501c00f003203a912101484205074001140b0f1901e1010310200c8040203180d9140108541607190020345001504040c1b103207030448000501e07018107401c064642030622803600d138a00030004160343e41121150151144c1d611031081c4100c03011101100021403c54032400041e0342c1d12032245d07208030791120307041144241648414010a1290400b510006080d1030560380207104800783c54240c0ca1088a80c034010301c6202803801c540b40030007a0b030074042000c00000f07201180050000c0d400400310011010280010005000c2400384913020540040c0301c0383e01d49040650440340165151603040c0c00c01d2002454158031035005e140d00c0b807414500801030075901e44844131440015201600001c001d0051404030040801102d221190f00c0380040001d5a1904001003600b11040d420500340e9403901400c80103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 242426187 1250 242424937 242424953
    0xb01140108070509032803020708030a0e010e062a06011208040905280614030a03020601031511030406020304110f100c061104080604020a08011b1b060507030506012003090d 76
    0x300c005202014148020541ba0b0030f0390b500c814503046005128040300410071100c0401a2100f020b05030300c8071341e04d1180000040d90200740c4c068045d40c0011090003a00741140b0503070321004c00d80024010310107811514450341814054144c019502207071030700c2400320000c0c00700000c96084078001000010143c0b102c1007018914001150b4880c048001040030074035840d1079070300c500c0807100c44919105078080103505040c0c5540c0861000b80c09a000300b4010004a0300201d00041e000501c030000156888400e4200785140d00305580513900203030b011080000300850706020454040040b1b801d05001800100000c09502c20703440140200800215003c0c1082483d801110f00e03072210043d44c9489940350462540d8803103080328141d10414101d0381c0011107980c180301700d8064120400c0781c4042e00900707400994000e901014100104160641c001010940502c605401240343d5900400e0301d0070008001000c64a00101c1204900307a144403000c00346400004031900801d0a0700c500c40005018240b4100f = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 242427437 1250 242426187 242426203
    0x1d0d0c060903030e010c2606060a0302031b04060206011809170903010b030f0a0c06080f06040b060d15180c0903020405090c270106050c0606040f020d11070b0114010807050903 77
    0x1140d5800c3c68004292280c20003d40221507021802000e085e05101f0013182422034195100c1c1e40021080000e2441c2d14801e800031030303125154280b5401d042e01008510b1340b06074002d51110300140c011308014810305401331a00c2c02aa134500c1c0d030504c20018540c81c0c00c0724040d10174059407c0b0309c00004480c2060380b0290410756900030010240c4c0c02d941108594152640300034601140e900715100780c0407034118043d00300c06006134002da0000b61a40e0301c0d0002d020017002d052545981c444424044d011100c0090300801c4082103507492899011071403d00f12042000881291807403143c14440b04c0d061095008c00400b0403a5011a404211034454a204a04001007840b5507500852151000c00c8031140443d146451005242c1c400265680d86e50070490700e500605e41c04e0801c94100d540803901038503080e001404107400c5044010b20300000403c0d0f400461b040c2248540706a140800d80b1424041c500f8a034500518135200045500da05c03480008000000007040d03402070280206034403103503482c1000996 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 242428687 1250 242427437 242427461
    0xb0a06020d0e1c110f06030f0112080921060603030405180c040806010b04061106130206030403110d030f0f0b0108041b0333060b0906180d061d0d0c06090303 69
    0x600c4203507141001000e0940824181d40a09025002d844070703406c094044900c52180c9100248942e4208071a075280b450440200340c075450410300c421103442c0d450f031024440d251105072100140c07203065140f0a0910708010440744c8250403c0c402001641c9880c5000340400005840c003012540e1545400c0720240143d802c034513402d109400c0003103400013200d00284140c4a088e210b19640e580c1d001e0909a88082c01c48940c40d084412645000050400401554001d403090030b107140242c0305010b04602d8500c80a62a000007a154822130300d06000920aa00d800d0482d62418410032103000000f0b40022800f500041900e40c000f22031900075100c6009080240d40e001c104c2100b940014001da44078918065498800900003880e010101805446100c081303440000d20582000c60500c200105900880851542441989103c0e901a41c4244a101c0c0a9110340400120024468070104032500208180c40703641e40104048110b19800c51000316200e03500c400d0204a1401d240b900324058041000702e0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 242429937 1250 242428687 242428729
    0x1606030b0312040305070e180a141504060507110a0c050d0302070308040b0307080c09030d05090303091903030810081207080d050a05043e04091202100b0a06020d0e 72
    0x44100000862482c2c00c41f010f00212005a80f12038043d07484500410715950f0060340101080000076a003d4800005a201503090380ca000e85d00202c080500c640448048500c00e40e21400c001d11541c00908401440900000501100070715a941e071094070b043d4060903100d01c020390035100c04c0510030003170280517550000045840d00d0b1b6039450094281c005844081c0410308050006003400751140550b1400e00000380200019400d00c0307010303512a448155003036090b0100b080000c4480e01c3c1c000c14001150004010588214514100101707500c5010303000d2140f6212002e820070a8080010380c603510580426003180e0344041030b2504145902c1000c402801c40350a08080004d107801c0340d40b1007071190b801000c0c01c1310307824140300d070903109120303800f0418031040104040d01d0955441c24000340894080a44005000322603510364002d400f405070001401640a800c003d5005c1d08240075002d890041a41c14503461401d204d000383d00c038411280050200083c003214404580c0e01e010011440e203c0c80444 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 242431187 1250 242429937 242429939
    0x180221060a0b0a210209030613031107080606100203030708220b09060402030f010e12030a0e03040305030a030f060b0a111507030f0e06010f05090403170c0304141606030b031204 78
    0xf42800203080c0380480e20321030004401080031020700844081d46e80c000c001d043c4954941d100c031105004000f0081e8208141190411240c500810401d4090f01d041d000900c02840c000c010030050b21411402d600864000380140480d00c3d81050500d908000e03140900403003869035040450800011850150100a04800f0f120282e80c002c81e01d40d0066009505507061a05001c000310300741c40386c100480c00594484078015168130700a402458201d80c5901c0e020416240c850650345c42e50b08150016a11500001901c180740d0381c0610911003035802c4240c091002520300900803840d406502c2c1d242007070041600c403a0315848400e219082c10b11404a582c04482c0c01e000381c006000707109650240031081e2801000e0b40d4880000a4442e040f41c0000c03210161607800d000070700c0301c58640a401102400320007460000e030301100d0035042e48500c052a407199142d213400d00b44100d0808652903802290340001103a80020070060078240c05840490070049245100e00d0082071070550202e41c401125600450 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 242432437 1250 242431187 242431207
    0xf020309040c0c050c030a050d030209010c0c09020913060e0109052215110f0301090b011404031b0617040605090a05030d06092909131506180221060a0b 67
    0xd10b50f07200310f001d01c0864041110700300c00e05a03190300c2210054402d81c00711280c07050070742c07013030b001411400c10601d00102c00da44603655600c00442c0c1904210310950300480c40d00300134100321582c508101c008030418802c0500d80441d91014000602840513000e8039040083c42c031507111840400700f25200794032180210700c9810a96442d40458984880c56810840d1004049040d00140c41d0540d01c039070401c41c035607440e0080c03c10040c44452803207410b00c100540817466600307100020348025030140c2181e43c100182518003004141440c0c0020041c01601c0045c850401d000c00380705640030350310540000e483c1d01c440e54040d00c0d00e25114401015031000003801013a41030341f5005601101c03007041062022040e400340858000d51101000320300f614040110103003a140c401503060b00484101d2001e04202c13219200e081c0ca04419600003844240c6802080140c0420b42c0d5003001c400086100c2181000000c40c070307500040092984d014808448007004c0386055031034081c4c3c1001004401411581c0d000540 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 242433687 1250 242432437 242432447
    0xa050402120102070c0b03040c0b0c0708070b0f0d0905070503031b1e0a06021c05010312020f070b12040213020714010c0c030f0518030706092c04030f020309040c 71
    0x194124000c0c0085101d0203a10101402502c00659114403005495410b0809049050b00300400c10b40f03811140010008182000d82d000f000c040b40480042c02c0d40906041013580703030034034070b52105800900030030211480354540416a042070340d000e000820340e560320f42001d9280070a15001154180000600404e4208090a207075100304101c4081e600e1482c2c91154403001c17400c801884140c0c603000940d0480000d0100d40c0200650407807003510361041c20b085100b110071980d0980088403e4080908040c0f00c0580400070003400e079200500500685060403040003207806810111400c446000002c9070843d07032883c050080d160303d900d90441d21a411030810038585600014441e545518001000302030030b01c2038120592854240d29001c803540c60359503088495501200070f00c464502e400d081c4800310380d01840250001d000380d0b5035134007101d81843c42c06010003400c1820000350303003d039060011010300004c0c61030381d03c1a010b00b007070441c80c288003005030709500c030304150241d005141c590038184098100c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 242434937 1250 242433687 242433691
    0x160203120301090c080a050f010b030a0f1b0210151a04030203030708041e05030c060c01090209040803150105071a04050a0c0e04030801080102131e1e06110a0c06030f0908030a05 78
    0x159450885c0781c5c44140642c41240e4003594141074009040e001403000b005018021034110164460005030408030b074580008482d00c0000b1b00c0700d003080781480701c3c0f0b60720741c10002c41c0c07885040c1c1c16003080740302d82d611400c0481143c54840c0f1010319203008850801d116424013034500a40e0080c06a0b80d480c3c8142c80c1c9050280d02c640201d200b140c90341c1c0248910b0301d440030015420386001038014464002c1003400c000c40b0b070304040b154172079079901d03501c40c400142c480909a50141341300b500d005407241002401025040c0d103c0c803000741042401d0140e4400710342c118000b600b201d050b04402c8002034540d400c0c41428824002000b90240102d603400064010111844510643c0a0707950210b0f1646c03541d030828240c0c80303422034902c0040744210b010b110100341e2051000c040d030248129000b10550b506076400308612080d00ba101d03803103a03503030f4100700032504240c0031101c110906d006844200d0b4180c1c0d80610340030250080a00700359450840c1140561544c0c40600310641010086850789000110b0001034041 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 242436187 1250 242434937 242434961
    0x8090a11180a06062604060b0a090903080708070c0302100203091504030c060b04090206070b0a0222091104080d0305060d1a040c05010806060d09050c0904030c0c0e040816020312030109 81
    0x10441c612081240a8034202440c217a20302040d005903c45444407405002c4a242e400d0f806940a03800103025485031240d105410322944401c00d10346003402000e0601c650080400742031000142d88000000e40c0403511a60080b071113000180c4030340350854018641031201020851003143c400c00d200505401001403400c4030300c210b00601c080da001009200940f01c40c9100290410710900c1101c00044841c0300007507000a082030010b0900f400120701290a45400d6410341c40144070741c1c0140003200860086c081c141010300c5580d45080d140c140501e9444000d149940101681c42020482903a2400070f1342075901d800810070b05e9040302c402900b0094020a40381110144081180090f45501070300000e0302c01c000007042c150400401030303030325000b0705600c05086450b03003e4409200c4480d61030460035405a4002ea492454024081ca06144900c5040c1c004089080d0301a00b0040060980380844800c018502c59600030760082e4800b2920b05200004c1c0a00c100d14007000119084031079910245080c0c0b1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 242437437 1250 242436187 242436197
    0x120705010b101e05090a1203030f021303050601080c0d02060a090308131409090d0c0204060b07060b10030902210a0f14010b1207090b01110d080103060b0108090a11180a0606 76
    0x400390b01034411703200c0c02e54400d406c2102502e0401c0300d0110a5064000b950103803d02150041c040f1034200200e81c4008020000d00c0d82c2003c040c0148601004001d02410303446006120f0000300c4800070b4039214660000922580740003440d042c030306100f001104010b5070b0000085844900e481001016509035001c1e01004c1e2a000f00702503100e203041d40c00c1da0700030300308000a802400c1e90118101c40503a03260805a8000c3c1c0c44480c0040e00540000091001d54001c01c0700048400704032007000002101c21500208050501141201507a5268070300c200032aa00c0060030300c030020041c4403d040480d00840540021071414514003403103402c14502c607911000070b008001d030341120000c000d40c0390030403400003d113580300050034851881d06500c02089100141000e031624614030100500d0700000c80a13410004484400410420806000f0281c9144090804000701c0c901958201c0d0784280880010300102401d000001158a81010740f216008460300300e03103e00c1c50701440a1019101d94820400011 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 242438687 1250 242437437 242437487
    0xd08210604051f17150405070504050106020d0e0f0a050d0b090f070303170606130b040602100605181b130e01050301021c110f1206150408120705010b10 67
    0x4080412800000d18482098040303134244510603c0c0103006505243e00d03440f4080b440e03ea40d20b20a244d45104034415002041114180801d01094901c1030384884195444048203c00c255000310321200e1061082d900e040c440810000092074240e01940210b400184071400213061000050550f44602000d200300c070000200141101c1d80d81040740b0000e00000c9540c0c180c4581d40e20140e0100750800c4004008034209100846c00c0c00e80354400340d200c1d00c4c039458002010040142c051112041802981400f0448546004046210580ca11b11400321460b6004001111034680d501600034000c900d16080d600c4140d42c00c1161111031490003019408071024000044910301402100c0420151f217101085540c03541a07030002800c60b96800050000040c452180c40204103c0139081104d002007030342d5500c0c20000e01b48010702e030101c280840070040410003400600000a5120800090002103d5461203107040890040901c001103607441102c031802c4181256000c1d8142031001100d6000d49444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 242439937 1250 242438687 242438701
    0x180405060f060f010309170310060305011202060904020a090b1b0f1b01080c0403060c03020301061e020304061d060408010204060809030405090601050f0c161d04080403020d0821060405 81
    0x1280848041d40e02000d01d9501c1c500704e501c0398001441c810322070140720b04201c440740300e0006940c20891300301520000c285001c01600c3e42c1805002d0041658480c030351942c8039103802051080c03084440341c41c05140c000440c82103251113200c0502c010440d03a0300c01512000240c0d0750103402140c200003662248211404e10a4850300400d080d440c1c0003441c1190800c01d60301000650b24000e0041017181c941c03206000000c081000e41c01030843d80003555400598a40c10070740702400842110756610001d40c40c100554400580010403901030b03071401d0408a0403240400114056004219001c0381c100d200843c000a115805401900c11340b0340c2510f0f203030126078917141019900d00440c425181e10840c45400f0586a5000e2801440140c13411411580b524a40000d480d10300302c005003026440070660801000388540308800e070b40012042051110032420181c952071018001d078000039100c0c000c40710481003044070080840780345542d507141d0340c100c480301003e002c21a240210f80d000d00442c00d107000074100d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 242441187 1250 242439937 242439961
    0x30b040515040905071a070b0f0405060106110f010e071d1501030b041b020d11071a090409022d0904150e0c0d08220b04090b0f18040506 60
    0x700e5191110780850015041d02000082d110f4003200395080d0040e0b20001ca4072a441d40b421400c2c2501100782c003561048949480401c0c004000e044c10341c6000c0c0078082c4800610046041e60460703600d460702c0c0100c1003203440d00c1c504141d04d1961101180d803a21240c2640303039602280c001e04503644401340c0100e07950351852101244030110f07a0850216240d0000b902e00350300992004603410005080002c1040b00b0a00e40c90549500c01c41810141e07110120090300e4940c042107c2c115000f0340700241150900d40746150b95442c90144040240e02030100b1102c8031503d99900400f0311a40080032000102811911800c00310031000300300a44101d006440751803402e180c002d81e03029661081c90840320210248a4600030180c0e000003ca56010311440303c02613036100c184c80783c1c1e51400f805c0c5460382c613003440002c11200b1250301014080300c8090030b820048540690f0540381165800b43c40801e108102c0d4000410406044120a901c2010305201c0240000c4201c641c6224511520844042d40c03070304124045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 242442437 1250 242441187 242441191
    0xe07090302060f030705040905090604050c01030b060a140c0d091502071401050d140115081303020705090403050f12070e040e0303011205011506050703080703140a020f0c010f0c030b0405 82
    0x2d00840d08001e1031400700c10790300007154050002c0c030b0190306154032803085805440d02030390b90308655805074050006000b02404440d1040c042400c0802420f902c0030003092035401010f03c81c80c00d1200071242d0100c0c042d00c0c01d040700d0b0264006d1064401c1c1610035600909201103034004e87e900c100000b0806450cd40c00000c2c040283c485035400a26809014401101c0c550b00640449607066180c4201110301080c0110460182558103402c080444c3c404030010301d070303410003000350501200903c0c0b244080f83d0045004410344005403800d80c103d0380c9605041d1411711841c0e05108001d2000282842c000070300c082c1035405820196100f040c12040401044245d4500303c001c803c058100300010000740c030100c04400c0c0b00707510402c00031600240c0c014181c80c07003661903488000407401c00102031080583c00407166620018a041c100869140000150b1240b40010028100b440c3d000540c2e4400704c41c400140c2d210642d0300070003400b10100c290580e6001e08904d964071008281044040d458030301d0540200342c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 242443687 1250 242442437 242442439
    0x1f0605090303040e150d0c0801290d03181d06030312070815030304031b0506040602030405150912100e031c111905030907090c270f0f0e07090302 64
    0x5051074140782000c6505031020341240d12481341117600e4000741c1c440c1d20a104030140a6040c1040032480c0800103400e50380c0790340d941c0003031684a021070070b9400303440689040c010b1410358200207021070344d29056400c09051040c8000c000c01c0520700041403010700070044142601c240495810ba25417406160b9070340500d02c9030364001044c5000150000348a41d0400d07034024850440b51140c0560140401e056611580040e1901f86101c81c0714044030311603960120040505491081c6007519040c00207440c3d01a80c002c41e0b1240c5800500e4007080c003e088203545260308014403580800d0b0300ea401d01c0e69501605440f0303107001e605040315080b503000088152418840500d84403000d8000d50701c3c1003801000143c04888000800340001c450b007003c481e207010200c2c01662600c981c1c1e4101090428580241a032200c1491400c00b42c9604800d5809041b0801c0200f0240e0090380707000700e901603240d134030070b054201c1c900c000780301c0c00c0c00520035076001a52400c03290500174400e5252180401280e00d40128000a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 242444937 1250 242443687 242443693
    0x4031707030512070e180a0b0f0d060b010309080a1d030706020705151207080a06050d0c05010e040603201306060203300a0c030c0e0906040b0411031f06050903 70
    0x11201640d500c0383d01540700009141c00d00303011403160006612120010049582e5141020070041e0583c11380c410044d049a04681010516070a1800155418800e820092041c1c4c1c590000003000e9000fa00005011039211030300d207495035100301d0020010b0280c4151002c0c203048019000c1070504010803141c0179541d0541c0a04642070078082848000030ac183d10000b500407003042103142100340c203c40346005a4031076a074140b890802540c0071080c0d1b600368006600c1201040161800582c04d04030040c2128401c0c00c04a0000c41c03950b00040007084143e20203003445048100e90404486110300301c21050700200e40b441c04403442200e0010864205d40110000b42e801046031400e200722403840e800c0310807411a078858152000101801c4561825140b50091075240c6180704034464060181c03140c560414501007159a284500003003210a01810302c601440d61404040465121500502c4050a004d1300c55952406d240200502614101d00c00c0c1d0300507500c0c40004030b0044c0c80f41c000c45020500083c01 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 242446043 1106 242444937 242444947
    0x61107080706080105010c050c0a080304050a0e0610140c0a030806040e0c0f0112200702030106080307083709150c080d0903051b03040317070305 64
    0xc0164102090600c0403541c00840ca90454409190110140980e814840c0c00d000c12140040d0b04401c1101e000b00d070080d00080204103d40b42581e410f42e00c41e40ea044800a421800c0d644180d0044010140004840c4952803040410030001021460400702d040d220745066171461007103020400a004000300b601d050f1268840e5800c241c000f918a81d821200041c1001c1603440403a81809440c0c09150b5440e2210790081e405003e0800000325001000d8500e080036801c41c0f18220712940c00c0c0380003c41c2c42c00003c01900c1940f41e1101904c0d081c414600204c00722003c4041d008030700ca0502d416400035030440b0304056160070b68140c9034288180d080003000c400260382d415000060224081001c00040c18500072120390100020000680210510b0b08650321f00c01c680c0241c050780444c00340900b210101200038821284107002004000c0210a40551300e030048540140c0032800070b0203 = true := by decide +kernel

theorem cover : BRFrame.Cov 242266187 242446043 := by
  have h0 := BRFrame.cov_init 242266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 242266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 242266187 ≤ n) (h2 : n < 242446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
