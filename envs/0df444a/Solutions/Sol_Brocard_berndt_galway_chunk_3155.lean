-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3155
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:49:37.790771+00:00
-- url     : https://prove2.me/submissions/a42db1dd-083a-4cd5-8b39-deb21809fd56

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 567266187 ≤ n < 567446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 567267437 1250 567266187 567266213
    0x206070c08071403030408030405010b010804080d1e020a0504030516030b0c0706020d051302010e0405040c1a0d0608070302090c03070207062001090c0620120f0f03070504141c 77
    0x3c198055464001c203020302080a14000c03030003802e40c0c0b40c0d242005c0ca01242110303c84030a071810320501c181080042290322064505012300e10401003000f94152007608101d1490542c024185440443c8204410790f01c80054003c0e01e10800032514900010401c40043c00b809100c0145034407070040c009900c0501000c00f604030f80b8820503015051000d041c00302420750b8400c90b405003203101500500b109540e884507800d440d0840070340d002c03c624109034507220b452160720301520f2003100d48075040c209601c150030304492500580c01020001d160316400450b03154030030740c40300342e100c1c0c0d202e5070100e007107078001300e080f46d0064086400030300283e45070510544901840704041050161100c910915550081c041c040309a0302c030306180c2d90010306005019041d05c0940209851428288040c3d00b0101c00c00291581c04034440f100c4203440b0140540406410700c0317441d1844030301000110900c00503640050241054404407144d055001c1c602c0c40a1040b03884900c100c61400b0b40818141a0106500e8a001d071 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 567268687 1250 567267437 567267443
    0xd050a091a07021c03020a020405061212091512070e040608010e211809040c080316230607031e060803070506010e0603031209011b120c0206070c0807 66
    0x1200d010759800840c1d4150011502907121960300050310011854203c1c1c06500ca5a000d070420071035070000ea10000c2d518580301d00020702a40e036402c01b0a52980e1112880484040d271502100c00006003031044801c66003154070040c0c0950504100c01110b040c03080c09942c003074148440048080d0781c80e99421510840600c00058200382d4072a004a214242170141c410620700c01350090800d03040090b441c0c0441d1a01032120128070078188451107001980b1070003175000e00422220005030340c8881c1002403448110781e014481074480040c904100c050f5005890640314028124481150031701c040001c0d580d1030031152201c00390002c0c000100304500070350180c80c041d040c441103401d8048100c2a008101d4890b034025072507980c004600074040250403c00c06001d002c4075000034840f030500f140400d9407170180001400c0d035000349600007500c000c800d6004046081c03140e115460440c20b00b9102800c6c0703c0b81f2140d0340c080c45051070400c0450500002d00c1d140550502d9450407080510b507200c2e4201604105811 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 567269937 1250 567268687 567268697
    0x20d020604150b15030f24091b040f0312080f01150905060a020102090f12060c0a020a061406030105100f14031002070b100e0c0d0b0f090106020102030a06090e0d050a 73
    0x3858040e10b482d40d61300749030783d141c01c025696410306032040c0d416501d0041c070b10311050b40d4840400b000d207180c1120603880400241e480d4841c0362a500f03044680c100d12611560795114021500140e034101070b21074001124001d000751065024070322821107404004403401d02d40b10032080d004000f031300c96080960303100c01304502d000880e8075141d000050700c65108070f2815006030340101c0c40c1c0b411f41c608404c16075034008084404000030f0109201711070720740b1402401c80c1019880400c45010050003400411451948000200483c004030190440e08c5101611040e002e986003600085207200380c044444192142c03200c42d42d45040c81c1803151380700e00d500c05d200307607425010f0144c96400f100f0b0540003400c00c007803003901034018a18080c0c8440428024a6212800c880b210301c1c18800030300d15400403650a02e007100f502156220f80070000c105124441c10340250051110030000070000d6065028500604e0311a03800d01001d80c0c0c0d202a5804d607030140800141e0358020a5440c070200e40170f032004016007506410b20b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 567271187 1250 567269937 567269951
    0xa0b0f030123090a05060f040902030622120518120726010509011a061c05150907110c030106060e060a0e1002010f271103190609060c020d02060415 65
    0x101e02c06550030740da00c944c0207480340d0511005151844c0f01e0392206030141d40820400f04103400080e560b05028044581c4204210105d00510b42400c0e9015120394010365030400c043c3c05020300801c5988003003003040c00c408011340300d2a045d162000c440300c8010303003840c010702c02c580c10306025001c0c80391503825a88070281f50300b40240100800b80100c0340b1800d040c070300020344280070300c9240030143c100b4484680b18000070072070403000c51103840074040c410003095400a980d6655002050051400c58160f03030b8414035100403c5003140d4400070f0610722468441c1941c5490100005140c260b5410307000c0c1201041090310ba407140341c1401d00c0038003140241407a00c514140030000101d40c2c0303030103207528850051b5101e00e01e01c21541e0042c02441c01c06400c42c50301d10b0017182e6810703500f1114244040c0c000c2c940c0018146400741c1c2d50342045811410b0102400c03034404a905480d0000081485410494501d030504e030074180003170700210300060160020307000780030b41d6030309c2e0340d0f13450310040a2400d2691144d5171061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 567272437 1250 567271187 567271189
    0x606090307030b01050a0b040807090e0717100f0204060e06030903070606080a1a060603071b080406090f050406030203030304021311030a020d1d030d091109040602090a0b0f030123 79
    0x80740c0d100860284500c501c25504000501c1503c0f0840e411001512000b00010807154400066220460703081003070015855050811890900c00c00790701c4225803901400307820920760004245045104040070041203040b0108803c2c04c142e0180d48102401b2442030200740c3c0c0d1034204076004590003030400c07040ea46010b03001d5a440b0100d070026080035000383c0c010320241041200c2c8410a0452942c1c0c000b000076a458030f0000200c092000611800c200200001070382c90110103298458085a4454104c036102d0751641c40007400004984510400ba20381104000303460304252003804160790300034002e5450f5a4641e001d01800d42200d02007000c000340d5600151b641c55400801850055001d442c026070780f000c112290700d00b687d20401d103284244c0850318800c0310811000080301c0c4104000b21000c01d01d5401410054601e40c0e00508003074000b00b0490800041018641c01045182c60071691410002d4441000c0019800b0f072401c031080c0f03501e0800050003800d9556150001d000c84000301c60541d10f500300 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 567273687 1250 567272437 567272443
    0x209010c06150501080705032815060e101107050405060a0305010f05060a06031803140c0a05030408150103030c150b040f060e1b03160c0c080f06100803030f06060903 73
    0x910b140c2501c24403480180001c0d81c0c4a22881e810001c240340003400c60a00001c3d504500c06205401a02c5070440e0380c1038902c03c00c40d07810180c0c80020001c1c240340b07403030ba40380b9020301102502d504041c881c405000707102c85254090340000103080000002000c00c10700704014070004100c05030103e5030040b00f103a400000a40700340039029131032100c20750200712801d01000340020351107540c000605141c105900038070f0002d55696010800ea4144c41c1050054082526686152095a074200d020340200c0c0010424004004010411034421070215210b0102151a150b4181c3d800e00004000561440d9580f01050103070303014010300f0f82d01c2240010072101080000f03085445035520f800a040c1c8070308041000642e0111500da10240045501d02002160b0310a40541d2100034601c8042500d0070361039240c5244120b103158503580d4045405c1c1079158440c244030b0381e0740b0000808500703075110700b000040c20440c2e80305108085a0001c03000314110307110410b0190400300010030082e00316000380200410f545d010 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 567274937 1250 567273687 567273701
    0xc03030306050f1c0314041502071a0a020d0e031005040609210c020405151504031209050a0905060102160f05030106080c0607021e1509030105060a0602070501030209010c06 76
    0x1903103000030540d192805010050b46103108042c030801d0350003a00d09914400b1a42040c00c1a454500100d00d1680d00180700d0032805903030006000001c25134100280d1075000511a001d844900400560324250210032a08500c5041e603c1c40058124001d84014680902a28038421a004003540c0950b1044d800010880e141103500f55515501c618060044c040f0844079800f4400a51440c0640745140c40310280400e0305c5100024040c0350f5440028a0300080e10ba10454100c2d001420b22106449046602110760850300060700c00c601068030391242180159410300c03c8400140c48110300603e011610382c0248001050981540074444d012a40d08507561142400b4041c1b100105540314140001e02d801c41c1c070103810441b03c42d4024031561419940781c00c103860072070f81e04a90070005020741051500da10b803003100703046030040041000a0014612030000c3e2911106c00c0c2d000b00200e03a140004c01003a01300f18490303080982c01810090103594030030b8001b06107140042c1403075007a5543d140e40d03031002c82e103030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 567276187 1250 567274937 567274943
    0xe1309150207120c0c0b071109010303020a030935010b030d211a0d05030c0a0b041a0f0106050f2101060207240e041d07140126060d0c03 60
    0x1000a000c410408960380d400710f0500c00c0c0c501412410710b142d0350910480c0b0107004200d50180d003ca0520200705600c41100c18200002d0290660f55a407460f004c0d548029503c01107001c20451040440c41e150608070700c482141d6030400b42051005640c00c82001c10301c44066640c855501c2c1c41044800b92410010358022803059503810b01d01a400954040781c1e00c5114001e10300b46802c164419011070107540c030a0740d50010840d03420440a41510308507242d0701c10a00c2861071801848500014040f480382c10600c0342d80580f030f107548101c03049402a11210400c80380c20042d5146e000040c001c0910076000740c401c00d104803482c2d03840d001200200340d0b021400010800c1d2079036040b400501c60305a050018000400c04154501861401041c2a00e07104a4440110302041402103401d402c90740d47d60040110342d540704000700c41c60312500e8600e58881a140c098041003109542414440d54403920090008000b1003906048100c5d120300c242e440d2000140049a10191001e8110f0225105940420044d44 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 567277437 1250 567276187 567276191
    0x100503010e100c1b060b0607020a09020304050105070c020105180a050612240d080f0d02030a2c0a020f190b0408060703020a120902040609020408010606020f0c010e130915 75
    0xc100c1200035283c0c401d100404002c0c0044c00504081915803404e44ca10b42c0c13045000c50300c00650808160a40691903010f54030a942000008d000c209690045000d107000b40000c0c8003503507424005a9280001c500c0082c0054030400490002042c407100c01c2c440300000500341011603a54200042c4c0507004880081ca14400d0f031820700c142c040b000c10760044407084440c044a007001041000412408400c40c1c082c045450000380c0c00c81e00020f10080314130041010000319107904041c140782c00100b882c45010709150451400c0810241c0c00300004504602c0d02000801800a05600340880c103008807a070326800104000c60071002c415103605440241c02100c1c8903a8856245c81c0446180800181c59801458410801029401d82c040a4024054180c402c0400e8500c040d201080061040da80320809241c03001c41e000c100f246c81908000e04548940e401c0b1a022203900c0059078407416094a09404150002042c13121420400e20b0758030748100351500010510318070703229400c082c40040000b0003404c1d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 567278687 1250 567277437 567277453
    0x31b09020a020f060a0902030a03050a020f0616020c01081b0702210a33050705070606030308090111030606120403200a1e05060a0f15080307170a080a0203100503010e 73
    0xf110400c0503ea01002d00c03102403001001d20380100340c5070070b03503004060100701001840c003a07000d008000c1044114510b07001c41c0c2c00303442c00b041300c000b090041c1c00e04800107000700c411800e4551308ca549428001c00351800080800304511051800d69440000201e07048281c01d04030300449001c104411000c4103521025040211017454610010b1b00c1e19a41c80350303040b10303030700031043d10b880c06014000c08003040800004070340c0c9a00000340c0340c034003514100905903410b21030084201030303105180e54020303040d0100a06c200c64940d00b03803180e40d00048641c540c205200344180c01c202d1104083d00b0350482d003c3e0038441c6101c2c203801c04880c1406427420840c00c00d40c1c401015181000480c2c1500d041000e090b02078405404543e580300c9843d640080c200803503440e102c1803203108403403480e80320f03420451981c00700b134002d9a40d8202d41c50300e07908804801d89000f695010a492092041c50854420f1400c80c0c0ea8040566926840d40c0001d410140400802003146031020070240ca01340705603100407980d10700070b104403 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 567279937 1250 567278687 567278713
    0xc0a050a112707081503060403030c0908030c1f0902150403110907050a0309030e10110c12030f071518150614120a1e05070e040b01031b09020a02 64
    0x7001c803401c820807100c1c1d1201503030300ea5005800102c0d40080492070440021303214840c1142c902c04803441d51580c54041c07003060000f01a0198003880c6048125110010b00b25961041c05849000c0c00d90045041e401409084a285c3c0300e90700e40d0f00610a0840700096600110380106d0f0018584421184414000050910030302a0032200b26a40d0202210b45200c07500d09601c0c001c2942c05058440070526459243d5882054040d041c0344e48003060250604042c940c0c521002044294030040400381800b81c60090661803d007421203407041d44942009501e00381c004800c070b00c00c5610908041d100c2e4000e0001854000c0044d0250902c01e032284140c3d03166603489030400d9529500c4d00000d08140ca03181480c01c1003480c54110300381d5840380e0200c90302c013071003800000c042e424a60300c043c00914444440703420764840040c21500c41c00d60b9010381c4c00c031400c05850388154410180140c81c00b800b1071364580c00400000340c240c0441c1601c00090842007009665030340c0d699040c1d8201000210140c3c00c440741e00001 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 567281187 1250 567279937 567279949
    0x2004030b0a060501120b12100b04050c040e1b0405100c021c1511070606080d020607020706050d02030a021c06061803020f1005040807060c0c14010e060c0a050a11 71
    0x1d06291002c21000d880c040010b00550030308201d24a032180c07241403c00c0d19603620b481302203e4800060940d1602c4040154210080c010004210b200b10310381008200344007106000d690658220f0302c3d0310360240c4c4a206c00d415680c5a540101c5003039060410002c50f8030b4a800c110301c100140a0380743c010354180c2600c100903020000d01c07114a070301608240e000005c210b101395007a0345441c01c50b6001842114000d000c200612a994025003410300701000095050750005407095075005d10380c03c2e600c4070344804030100e0b2115194418000000c0742401a90304142d0b05900541d0080758a190051600d19899100c0460103000040c04102595a0408208207500409a0b440e04503a0090824501c0d085900040d41c08c0f0b51000c98900480400034450445400b540446d40a8440c400480c0c00050365400c008001071501001121556034084000500e05801000200141d2050710b401c200c0d40305181c240f04c030075000701c11034007114460810888041076040c86140c0c01e0900844a02410015131014404 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 567282437 1250 567281187 567281191
    0x3041d06091003020114090d08030708010503060f270d0207050301060501020d0206010909060e1506030d0518010e2409040c080402010c1b090608100c1803152004030b 73
    0x701400e034800c1003040701c45070440c00d442a02c0d0309081428544440b280000362070301a105030250000c0c8403e9100c8203008012014602c00c85540d42c581d900c503038840c03081c591141c2c2c05484582c1c4800d01007020900680b10005044012465928266200c070240900e15151074502c062000241e00801c2d81400305080030300488003e00420b0000b04410140444029602c0005204040c1310654501a039010003071590050720040860104460100400362060052054165503540c401c3c4100d50b019103aa600503001d484050360320030440c0e14081290801920090f0900c0c01303d55101c40f0a60340c0320304107010400d40f450040c08448501d42c84020070b07000d000c00c03140780d0b00c0c07041c0502c052002000010303a44102c0b840c0c0410351010303070700b00d403a1400040001003107400c1d081419010b003444404140c9038000114a08000800101407104140441047d43c802c081b8400c2040785504010b0b040c0046130003011000c910f000000e20014040c1c0b0744155410007040f5800c6400c48250300050704200740503046c0c88031a = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 567283687 1250 567282437 567282439
    0x18051c080c03070f080c2b1b0602040b03070914062a0609011d01050903031303050c07060503060f0405091c050d0c08010305060a0e06060d1b1412030405060901110f03041d06 76
    0x10148901000c6038000b8201031071f1301c0810040c00b80e030900c00c403031150307004c1e040c5003a4016400c1d502c40b0b031110f10715940d58204903410400a0813030080040c00c108003903042084082c0150481e8030700b1607030030f0107208894840c0d41b210708540602c02000300302c0c0304100015413044103034a0000480440d02a02c111131074010207103144c0c544e070410301408055403003c0102d0341c02942116103188603070014641542c1c1d0b40030b040711149041c0204000000c01c585c202004500c240c608071214101b08020341c0411041712025a9a02c04903880142b5840f501c1d503400e440011a5442c80c2001070820054841000544041d03500b04c01c0050801c1c0700400c00c01004008403600000c2c00c207801e11030040c0b140c412907680d0b4002030046104020290100007804040142e40e088221019034115030f0300e403500948142c0c6071005070420301a0401184030981c81d00c0100a944c2030fa58010b1480b0701e00b00700180111110b12031846114400c2c001c900b000050a90208010802817440310f541407601c3c5440c0701002c4081070014186 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 567284937 1250 567283687 567283723
    0x209151206041d030a030f0506040213030803060a030c17120a0e01050304240603121107050f040b09010905040507050a1d09120a18051c080c03070f080c 67
    0x1190280c0352804800d6014a064400090040f001c80d0304222028090101e038050380400580d8840c2e155050b00582e0340108034800500203a20341d803050008901c25040c10234480c01c140d50013880041c2055008641026000b007842c5041c40d10b98441c180e080c06a0ba02c4044540d072600f98506840c80c0901000c102c2c98400b840b843e04000701c60320003500a40b07801102c181048000000030b02000b147c00c1042000c0e03481e5400c109504071450540d01d008000c10700007500c1d1424044503800229118000b00001e804418000d0314040f0303d403406006481c0901c0c142a0380c8a91a94031620194465201c031a0090030380807000305a0b81803d040103070910709184c00450040004001c00d0041002c903050540a1001482d0341c84443d0f82c95034811400c280b51650800b0790620005100042951b010801041c0210680d4912440a41e554100002c03e43c200312000c2e002b4080c10001000720b07100c2d00141050021034401d492800400d507481500310111403034102c1e003e00002c00c55102081040198081c941d00030180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 567286187 1250 567284937 567284947
    0x402040e0a0c180306023405100203011809020d2418020a030305032a09030111030106090312050910120e011a0d02010e060301030c0305120406050a05181201020915 72
    0x20118010659000103445240c00141c2003030a4100040040490880000c00c107a4100d447c0c00b403050a07124083d42034849115480c4d00d66091031041c800c889c102ca061511010b25110f0007c0d01c140a0560400180e130320181001c0a84085007044500d00030580c01c1f002002a42a80d06401004688910500c0700c1413403090700041005880d10700c0404166901410241e8032990303504443c45100b40500004a5100f04004181000e210340c840500320302c41e01140203004071128a0040c1600340403d12a0b400020400e09041001c601001c0d490380306e805681c60000d1170100f003000802e2241d0004000308000413488840d0944064862080494204092000b440714030b1030601030324025440105600d00ca60010790724102168003410030312801541c06401c141e22036960341031423050113035144006d48184c000c07001d444020500c01c10823070b030603030f44203458003820040d603107408640d10b13045010700205200c01902c80c010130359981910440c4007036a40c000544e031000014103001c1ca4405210940f119180c2c20300c5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 567287437 1250 567286187 567286217
    0x16090c020a1707170d0b010c0b160504030b09060106110d14300603011d150c0d0f060302130c0e040c020a14070603050f01150e06090402040e0a0c 64
    0x10301100c01d9070440403030107161658203006000c038858003000800542d0308416500c1c000010350b0207015085c0d0941c00c100150a0101c00651340c02090f9000200003083c40750020b000c0224400201e84170417224074109050a4403951348180c905004c2d501100164040c1e00100903982d8071480b500500c4580002811000c29200c1c00500094441d617061400c6100200f408038640700c121443c4c0303500090105189840c2c2d00d003500928041d9a041d55800e02035400c01c850308904401940c2e50510031943c80e401400281224070204070010000740c1490070418003040342e4210740c1c41501505a070b6410408000401c540341d407041007941c0241d2803200c4609400c2941c0381c228581c206200f0031801c02d040d03802007440c003071484080303044c00c0790050020880444000460040140018000c0034bc0700342e51010001034440360301415074050244140c14a101d40708041010319480340d100e4084ea07100140100b030170304c94180700080c26a045070700140d001600680410002002a000d1109010000e0400c051902c045503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 567288687 1250 567287437 567287443
    0x110703030e0c152b111321060207060b090108151501090b0705010209030109080c010609050114040921030e2a0130060305010c18062a0516090c02 64
    0x4e5000c031403222501e452441403d814894407220b0828001d010410884038488800c0290000341019485807580c1c00c2c041413a01b012034040c0c0d00200c5d10302c403074020340c2c5007076030303504c0195000c1b8904440c1c0c02d0b1510544052902c606442070f000c3c00726140604240004800e034005d240c08018050040540800f900c82101d9810500031b1090740c82c43c0e120950f4441c21420314901901c101d44003550103603c1e110900060041c82c0d0042e0090319100802401440d40c0c0e82c04900c1a54020300440802039100a403502103480c1a50103046014492032035051049420300510b9040761940220303d01107500c55000940710041031011513046001410350751010305404120308a490b1000348420f05020052048051020312002094003c0c1d564000300254007020f079507004041e00302c40c4412201c96082c1100014514010541d00144504881da000d21440c81c11008079620310704507481082c00070350805e0b071000504132907428882541c0108000c1028a980800001d1804040c1e4481c140241ca8040190701080c0e000c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 567289937 1250 567288687 567288697
    0xf060e0a0e13061410051302030103050c01050702031e030307030608070f3005010209010305330f0402030a090506010f08070306200a0305040201080a14160201110703030e0c15 77
    0x700382c1419a202c810300d022001400c0c6a5100d0040c00003440c01c00180a9900e450001525000e4806035071445802c1c42d184183d010a00008026400500c1c5000c2c803548110090061107000408541030f40071580c80424880c03040485801c0b1a810000c104103840313815010b00d0f03005220007001130283c00e26100b01c88110103640e02600b00d81e00142c1000031261715150030340950031454803641d204004890314089000307600c600c19441c0801e042100041d4909580504040c0302c0c072403501e092400b00c1c100c0030005c607900d440c1504198070010b0020040c120707841e03034400ba5101d2085804000b40b401031904003140f814905a1100300d44140008007409040760100d44401101c0e8840b4002c105400141036200ca4410480a025050309000c00c802c0e04083d81900002e0099000780ca0399011038a800b00c0d408c00703035420030070413407500e090700408604d980c81c030000d4100345100c1c584000103a01455241c207840c158030541c0140c00003074580040c40c00b695801d0000c50155201150513041e4000700e05d0070030a0a00078 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 567291187 1250 567289937 567289951
    0x305061e040c051e21010e0a090813060504051c05030703050706060b0d1b030b0a0e151c060b01020a0f0609240606091a0f0304030c020a0f060e0a0e 65
    0x1201010710712103010380c040e5903065090364541c000740ca0540e280008550450701611781c0071801580c00319a5280d0840b407190590340b82441c2880e0560340e111036000a4080d600703007100e003000104002a0100000c01c0401c024280701e80c1c0c2d042d91545400104003e402e14890300c3c4072820442044040052000401c550342207070b0604105440d4010b500700040209400d41c803034002660001185203003032585600c94121280d01803201440380703103021070440448130415041038120646550a012100c03580700c3e0345c0c2d40204001400342c207040101000c1503505c0881f4520b0340000c4c0c00c500700c40e01041240d01603152110400e01c014007012031182c07240c0350080d20003480a02a940c2d1140d01805001041c04200c404100c960000303210f101711071108030003c101920807400010400c10011942412407110300070b1324404809498245041104c09117160781c0301501c2142404829840780d00161200f4020000521200700000f01031854020040c0c40c0004c43d5031858414016002c0601c8482c3c0304034456900006 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 567292437 1250 567291187 567291191
    0x1f171b0306011e0909140607180603020705013207020303100513180308180604150b0604080a03030209091e041e141b030a0b01050114071209060305061e04 68
    0x10341e03e805892000c2c600d40020381413a081403401414403012600300c1c3c120703601604c101d40c040d6403401d504940c034905200e080c02426503d5502004001e10a8024000d443d0141d00005a8400d481503282d800e20607011101a401400a1445501ca968803400d2580510303980061491494030002c0400e0800c2540242ca1007070003541e007094540351341607000599849001201c2d411000f1103003005042c0703940031501a511000500c1102014600104507a070203558070110003594408080061710140156a5100b500a4814080001c000e01c0800000760b000e4060b840050341d8403030103000d001d00500000e281400ba40623034050b4140f12508920042d40c0107401a40d118491080003111a001c1115980b000d02440408161030b03450b103801082d450f144101c05a000d00c0003070401014182c0300e006502000c0d162800000042007154014040028052440c0709568644070860382d4203440134055604210000b40402007e1010326011301c60150030907011180b203d040c0442184c81c500f203890760314000e40525 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 567293687 1250 567292437 567292469
    0x709120303020f16020a12080d0f0b0a0905010e01050105091e0105130f080105090f1b0105040909110a0902040b181c03210203130b1f171b030601 64
    0x1500c20360589081002c01c1c490142c2da100c8107010010700c512213600030b91103680c00ca40001400205090500042a4042e9065007840c04504401c4000c00320788d000106025203a05801e03031079070380b413a60410140010b804009615410062200b8012005801007410702200b0002d02c01e04e9610f85c411129081840110360003180c40c000e004131100d004000c1e003018034008000c2e01003a005c0c4ca0b07080c80000d5400c2080200515580c0d281c0456481d0000c01d2509210b80001e0041509040580c000c80b03408001130500d00d01c0e0580c0d910904007140e60a00c02645c0380144500000c24a1a003141110300415403400d0030b40c14075081108035003a51290304000c40301800e900455080300d0700e400da40c5405d07946103001702040c90002030078090125911b19a034904250906032495240c00c10074400d0b02e00588054144001d034044070380d6880c0078980041c1c0303000c1f07135440303101414241d01524141c0c1c1006810f200e1030910380528080086403a000000b1400c01440412a03040d0003240c4001a0300b60442c0d16041c5103100300 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 567294937 1250 567293687 567293693
    0x405070905160f0f1407111c0201140703051b0111071416030c140d0503160b07080f010302060f09280f030b0721020708030612010209010c111c0f05011103070912 71
    0x5044042600342e0000d0000c0c2c00421050810000a24000c6c000c0e0bda0002e20011241a68185c2c400c4910007070120b902480307190044903d09403a1003404880100020360440c070090f03460940c0e0171480088a0b6030424650500e0b4844043c4101e050420020028040c0c19045640d17004d410300085c01050f038801d0404034004516030350410030308a0f058102c401d4903a20300e03000c80e04100c0d103d640309099810b1004000800c91152188180a20481c0400e021300080d034250340c2041000d600001302c100c000c2e20203001d0326006554080000e00901c0c078401a8950414081d038408845242c01d41c48002c4c200910034042011440c08441589d105065141480d25100c20300e03c5c00c00c4004c001c0c000e070324ad131a102140f11810000a28025401104e045580030b0300c51b448880700303900307030f11841242c140010090584c04001480c14400c00d01c0b003510080c000404140003210407952010884d200b5602030036148262000c1c814288110781441707100d100f1443c0780d454500000783c03409003903204547c0c50401c095030304028 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 567296187 1250 567294937 567294953
    0x150703090212010c030506030615060304080706022a0109020604050906060f03010314060c04030f0b0711010f0f0b0301020301050a1e150507030e0103230405070905160f0f1407 77
    0xc66500900c00340281407030211260080c04a112a003000c280b8090100b0050704d40007400030312413030003a144c15144161482c10301106800c0a00201c4030210180310f404005841c5001420b0700010280007408500320305424400c0c21420391146120592501030440d0260319048219804c1c2d031000d40d0140840c0e22040b0200381140718440d4803406c44a030201c008802c1110201050510b014480c0849030b040d180c1e501c00c4080c03031055100041068603803078141000929a02c00c0a6070141e15404c00d201c8802d034951341c0d07a0944d00b00d040420a00c030340c1e91540602107142449030940801c400d4008504540c1000e020900908807801101040081660500040c08040b12a04050f01030341c0d0101d540c501e01088050100d80029408802203206100c00a00c0c9511911450345201d800d01d088854246040c4000740500c80090030940b85402034130000318040d0303058060540610041c07200103443c002d00020003031080c3c080c010200204818580002841c1b41d20580180e42e225407144119a9a200c0e441d000d45 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 567297437 1250 567296187 567296201
    0xf1811010819112a071e1509051c03031103040f03200304121e0b010b0705030903010507080106090b07030503060108060f030a0320010b030a03030b0a08060a06051011150703 76
    0x80300d40c2c40d514250100d00034146250130032240304683c0100e494105d0340355412406003050040b1140c402040210043c080001c00e95104203090500525468401081402843c1007d643c24503030b200114104140e8075100310055685001011400d50400703540300e0412240d0014081d08002078014134240012058500c407556280c0c620840b42c1d200d65900c030081001981d1901a98080c029808001c6101c20b0380c0031109405a100500b4810f83e0300b8a0401202600122015a050b100510400055840074460a401804592140540f9602d040d000801c009040d400c100f044a01c1030000c6030029170007405036a0030103800d00b012b84c11961050049000714a40d40c0009070305204226500040c19000300c110a41d10f02c0200d1804100c0311f00c0615030382690024003c80d505135210000c0c000c08248203a01100041c007000f4048400e09546000c91450300106803860799145075a028208140d00d84100c252005e2046828442407048080706030903121541d2000103d489094000000d102a21940c4500303 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 567298687 1250 567297437 567297457
    0x6080c040e10091a0d2d14010506100c06020d02070807030306030b100302030c060c0703050f0304050f0108010b0306010c02030c0d0501020d0c090e0403120f181101081911 75
    0x460601c0c0c9003a1200300b4207118030030a00c06a2070000c0d0500c100c402c034400d03510105000f40144050902c5543c0709400325211800d008000c0359030469141511500480307031032006010f10100900030300c00d90030341801c442015000b18424504181000784c07847c2c1103145a200d80790000c80040e1a104003480080103071090a400170b01c2841c000440030101601940410b091b07a00400406101e80d0300e84403554603544081c00042d41c564407c40e20444240f8007003000700507580301030003614061980d81e59a0b41c9480301d842c0c1c940e4920380010030b0a01503410a99140c0b030b41c00000b40381400e0035502d02018a0814440135288074100300201e80c81601f035450400c0f1048580300d026101058001c1142029030007034201c0c0414020060803c02241d644611800d401c80540302035003c40c1040f615990f07015a803070400813400054254072150310540d4581a88100511520000c00700b8100b0344561410328182408255228107101181c002d2141d9240701024000c5400c00c0720070300040002e0703000c451286030f015010000b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 567299937 1250 567298687 567298709
    0x31903050d09061b02060c031b031b13081218040507020c030d0504030b011202010905090717041127190209030d0507140a02130f1b02030315041506080c04 68
    0x4013200802d0080501d94a00d0560300b5600c045d01d0f4401e100803144420342d4844000145200000c0398042683d004580200c0302161304505141910310424698102d01c9440d040c101c142c1c2d0341044802006d0244514581c8802070842c5042c80d015400c18151075903035400b9000d00d60350400691124003c0050f010b078140c000301101c0c1c80c000c54072401012507001e4007044810342d00c01c500019207107400030401540164140c6070244894109410b10650200051007075007000340c51440c90320b4001c01c2d50440da001c0d900a4421982c1005548244410907003044501007681d4440210300c0301e01e16540c3c01c960703040740e001d08420040308803a9180101030301802174540c3c0d050241c00a07044140d6009402010102d01c150468040d41185464a64848080b800040d4020741404506400e10300f442d8810cc00307001e21420006220410503640c2c20034640b9004004003d03903c0002404000c9030b5000181d0b40b0020201d90921400d003030070b0311807400b425141c030912003406440e8010070b40200c00b003c2542c0180a070b038110 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 567301187 1250 567299937 567299951
    0x1020f01050117010e01060807090902060d02030709061403060a15120513120c050d0804061409010f0e07080c271923060904060615030506040b031903050d0906 70
    0x11019501c0803100f0340d043c0720340c6400f208030944901070050b80c00b11290078000d00001890020490050641107908a070b12000800403400c60a40d54030103140991120354800d1816814a400336080380c030020740e40f041c0650240300304601980c54845010039a410034810701280d44c2c44800c20340e000c2e02004400b046003800c040070418030340b2420340c403102c186000300c5151040e2080f800c815552104035010140c143d03000301d0b50680d4018042e007801d582203441502d001a208950000e14200c040301501e5505440e51a00100c1400002d43e014052000e00c0c0d0801502945141c104074603960f689a0301198040e50200b03040b07610010f400e800c2054038049220841b5410302c0c0c550341c1081841030040c00c07a101c240c44e140420025a503e1030409a801400040d00301c8180c6a00040002c0500b000700103c49483d02d601002c6034071046566000ca103d960b170703203011420703080160821099580c0400c030a8021f62003104569116902c2d5070030a8011501030405548d41c480f1000205c02418031a40c01408071420000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 567302437 1250 567301187 567301199
    0x918270309040f0509060c0408190201020a0f050102031509090322050d051e010204050108150a0305010f1e0908120703180f06050609040512090d020a0e07080112050a1101020f010501 80
    0x66100f42c144105541b2681c1c1c030303008070200c0d90042d401080c0c0203070b00c010394141c2441e101c2031800305418014011030700741e401c5580e2081d40340c0103c030301d00321801d035004024003104040c58108070f001c24104a07100c035043d1400000d45a624003880c1d549120380440008005080c2c19188000000b400010309a0001000b0a040170765440c0700d03150801c00c3c003200864080303055950610071740c1c0036184160760340304c80d6440b50414902007516602000da0322038182c0f240000044c100340724103104041c0417580811640071450402200c5001d6140182c1d000f82000b00e0100040c103548111400104980c00c98030241e22035210440082282151a1500c0e440000c0e4001c18002d8541b00031030911b1141e80b0078400c0b5512003050141329076054400034590760040c001d8015690703000740501001c0c00c015045122110345600017a00d40301203a4403482c0000c04510510102540c003100b82c602500c4010354145d00140c0c1580d0303081c0c1e240c88005010744403484e181ca4540e0365a200b0700c404080c5d09940c100901465031904 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 567303687 1250 567302437 567302441
    0x31a1302071a011508040302010f1a0a0b130911070f030309120e0901030204110c030d0b18070c080304080405060309010c090503070e1504090f080918270309040f 71
    0x1003001e03140b504034504101c03440081484100c3c1a0380f0851402e42810f591440281c0c0d52400280044080d55265140030304011f0961203440f0107070740115058410880c2107020b0000403061074102c04152481006690007040d068011602207500d07a81d0f0009000d01e100c280f84031680500300000344215400c40003501416490381000c608a03028100b1308000f6401414280e4000e82400006504030710707807400400140c60245d008246403413203a210686024000340820b0b046900c4030100d22071041d601d9581c07210f1820840d1001d081c442842604050504150601801403409a0801028a00d0010000c1c0410808405443c02800042c1c2620303200d040c0906060301030803600140e2000203840b69400100c81c58002054022200c514440c606141c96010b00c005241c6d03900b03280283c115460303500140008200021504120340100c0205403220304110070450503c0303c01c2d100c0c031100c604040c2808800300307090421036840c0c00e0800080100c2c0602c004154214040d003003040703a1080c9040e40c901041402c903 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 567304937 1250 567303687 567303697
    0x81204050307140d120614010f03151205010e0d081303090b040e06030d020706050f0d0b030715021219050310050a260610030f1109010f0e0a0905030901031a1302 71
    0x70703185c0904d02d840304c4031140120f4100c1c0c0300b4185101c91480e50408594061a5803075001011490042614036044c8050002c0d08201d82c40000300854070b0001d4014001d003886890741c2888407001411588209060041c42c407480603260810701c41e030b42c03141d1600300f40c01411717042c0003041c03480c4040d5150f558842c1503400950742207030322070700a01598401511542c80444c6070350a880c1c89844841c20404400d0904106400c61403100c50010b590f4101c01103695030400100c401002451100201604021802401e00391644420201581e00b84018001d50041c003039040d1f500003144c5402230701c80c0d590302d40291003032a083d88002c0e008803001a0215038000e91610700c112590f01500440e00c80080b09454955409045400080f4006002c000340700194a4001e210086801803200605400c101d0002511b00502a4010b004240000234100000d0900c15034581c0d000342d082c1020840b07101ca40e100d040d160321490700b0403030425540c0c0b207000f0b85049031451030b0303604002e000c1d002040b20703902940340364001d43c46 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 567306187 1250 567304937 567304963
    0x10080c07050d0801360e070503030c030304020a06090f06081905090d020c090408030a0506030304090c0c120f020a11030f0f0c1c050a08030c120f01030b0705040308120405030714 78
    0x1c102158000026040c0305c0d103a9842c01c600644a0010807030440c14020b00c2c0c210040b8156014106001031142c0d000c00107840c44149603c0038541d80d042910410801c1c0d04e0310390110b8240000702c2c41c200700f00410060424202d81c50780c10030402550f81c80d9800c1ea100c141111800510602c5c00042c4641000001840107240c120f40e001c030b4010b0003080040004240d811200188020403c00018440c05003540000760840d0014084a08094032500c0101c00c1c0c0e02e251000800080421075410140b00244d1840c000031580341c18204c50101030688025106c5450420240c808451074484040e80c8c0c80070841c002c4e04040401c01d50f44090400a00d058583d0052070f402071160400e1081c00c0f40c9a210340c021884807691040c0103002d030b41c4155589a41a4000030500c569a220a200e2800100c02407000d0354465180b040300c00b002c640c1149030820f00741d0380142c41d040401c03038103000a20005240f0000c0305c400a45070b680c810b107981d45514105280d48500d0a0080080d0400f40551501c010006480340203110 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 567307437 1250 567306187 567306209
    0x10306090f020925020f030403121103210717460b1f0305040309170a0c0608091509070515040e0109090309090b151801080f0610080c07050d0801 64
    0x2d40b4041203070340c6d41d82000b030f160881d0410003003000011642c81e00008102400e0500d030207000340440c0ea42e81150405050b50050101441c200c40603141460345155024541e030a003007940e40f51900180060503c0140780850500c010404504181c0380c12400e6204141c5d0703100700b21703e140d90562900c0c4865a85002c0000c209044c115200b40620b8440d04020444001c2500c1c2c5401e205405401c80280202400079401d114280702d020844140c0c14003100d4120642078001c0010554074500360384080c40c103a0000c8208007007041400318468011030039000d498007001c1d0320700c13654039405051030600c81294819940a03101e0342100e00020020805402100d03d403884081603607903184006400e99002074030007400541210820700c003100d0301d03074031503c40500082c1081109036035910403a0038680c40115103526900707107003030040e009680c05546940d1090074011044070b681024408a011109076030144000d120034070000494000b10070f410740d010650013204943c000074921802502d946020300454510003 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 567308687 1250 567307437 567307501
    0x4090f062d05040c0e010f090f14011b08041203120f0509070b04050603010b0307030b0301060303050c010b0409081213060504110a050619050c0a050a1203050108070e010306090f0209 80
    0x1c5440d01c2425843c1d0b400351241c0040701d002c400111203010140c0c01c41424481d10481c04144603270940d0342c40c070150980c0e998640960088030000f4010300e252041c611030000300503012078000354064054900b2103607103100d0410340340e0f814501520020064801090072510781034102c500d1100e541c1107a4041c41041081c0c0702c156496176030340641481a401490b8000e0340030001089550044801990b2100c80e501e0002035552501c1300080c2503406542c0705900040010910400d000310a2050300f035800c0f411201004085140d40d2100580d00071444650b03218102c00703001070f1040a111806080c0c00e503110300100b1003440d252510004030155840105d000d1120242d000c503036428190121510b0704101206081c0e4030f4106001141c96030700900761941507008040042000030020403081038002c0c46265644001800700100074100d9805a120350860b501900c001c121000f0079108060559030002004501c90000d030030900e50740b800f1401d0003504003000e03900300100035041c0703096243c0250300c04c41c00210314 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 567309937 1250 567308687 567308689
    0x2010f170c03061807020d08060423100f18180f12020c011d091915080c03010207030c080d0204030b0f040308090c010f081f27050c04090f062d05 64
    0x10000300c5c3d0351009030340b1030020380d1000c40c002d4020310ba0048005001158600c844120701d0350f11000120400641c640d800103120079014950b0304d072409000241340e8400c0d11032810200000003c0c060500c0344d0704c143d03102c0d18801c2401181d0b06010405411014110383c0020a1070244103074030701000b0b108010300440c40341701455881544a80310a0040650409605604030100030203044003034004040e02c1c080c1d204880b4090340300d00564505403612943c40c103040f407401c4225030400c0b095104040c0b00e40d10400c40800080e4108080015040e045103a142c1c4880803103c00c1382c000d20940e0406080749030103104110441c0300540856200c0c42c8039a896540c140c03203038520b00e990740e04685110703404500b07990403081045100e03401d00f56012003612518040c000c264104401d407070b039498010060b15620300b100b448030101c1008665074550350a040811091501960404040c040d6006940342c4a490340040000001180c000030050442c091209040030703403085c03005802580c00040d203105e5900d02a00010b0b5 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 567311187 1250 567309937 567309979
    0xc07031211120730020d0215070527040906020403060c11030f09010302090a14090106111e03091008270303150111060705130e090a02010f170c0306 65
    0x802d00751000301e90a0040741d42d00c0040044d403400c040140c02402c801d015a070200380c0c00b000c0c0814085078014040007408400001d081c1618401d0301000c56841c1420302007150b1344041182c00c0c004070030780b08100c4d25007809402d0641d5028403550b968401d05007005070051043c59030003442181d1044004204400847d0426641c3c250340d840a0010303504184010211070b8a42c500a06110034149401840d01c0407020000d2001405508410b08218080001076001d041c03c40318117024000030706201c440c1c02911800550784e0403651941c8220300d503000030400203a00081098502d1440000e1400c034000910300b5009140000854420a505c1d401e4060740841c50641b501c0781040c03132840005503144d070b0b42d08401020340c001c00d092076504011700007924007a41c00052110758044c026981e5041c3d80c48003249030592007030805400260440b5944c1c810b210380707600001955803140d039081c2044c8111001004080d5010b10821001913680000c60f010041290403020080d84601c000325240ca032055001560924 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 567312437 1250 567311187 567311203
    0x706140703090201170709030204060f0306110712200d020f19020901050915060f0c0c1e190b0408031b030a0f080916030305090405061f050706020c07031211 69
    0x201081c240c0016601410780300d0f00d07495000c2c801d410880b21f000e0750381e030101c1c0854559900800400c02984020300802c101d82c004c5480c0c800500408500f011642e840b03040301003880b00590000c0c880e107081101c10300180e4804140034a0800000c2d940368400c9590040c3d207550b158080803000d801007000b400741c000032005124014940142144486a08050501413200d5014100c1d0640f805004007020a45c1e46c0c510043c16000c12414845880c1d054100c000da10780200e004401d07100c0e0b00d03184000e5050056611210b0304020049481001c030380c02a009080e00080d258020500d410300005000c201158000000d0250306550488070882d040c4c581080307a141d003d0a50410001a4039860007803040384621142c1d070b0030615490a4440e481c070950f0991104408903401240031890104011140d031500e40f1400741d200005503210010301b2008942c00c010112050b44810038010007044110134450550306895090000104030380303c058480c02e1455a10300e0b15600d00b000210b500000c40780344480130507055 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 567313687 1250 567312437 567312439
    0x4021603020c1c0b063006060618130e030c0d022505150d0603060b0f03070605161407030507081e120f16030e120a0f020f0a0b07061407030902 63
    0xd0004031103645400304c0a0340a040719070302004404083c0c6490000d0780c1d00324000498200800107078248007414030304050000708108c0c880c900c103000e8150303007001031200100811000c665000f041c00c99610080e00404681644500da0310000c03984450354403001a1410104030716808680300b0310540300c820701d9003031514150b403003194282e14020411410181d404031000300d114841d1900b8011071051900c11140250b0003900c100c0d8840c107200d5144c1c2023a014100a420068010344041f03410300308040c00310312a5840302241c03111841104400d003d15003c0d418401840036081d15145036481c24019a078004034004c3c90150300803600c5c0344032540081c10795440c2e040750f244060111070004101d00042c90308080310154132180100701d2590415140c1c0ca188216900c2511085440303140d43c420301a45804d00d50b0003c030340d0342c0060407000104010b0b078003440195604841011000b40210b010070015003555000c5c9412078004507085003017103042d030003540c41d44a135910024856070343c280b4100c0580e1078059001e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 567314937 1250 567313687 567313729
    0x191508010608010b210a080d06090c03020c0706050912010501080105090115080c0f21010c020c06070b010b0309010603020603011d100e1306060503190c15080a02030406090204021603020c 82
    0x11004511002e40310794184074200060306c2600300140c582129540c000502c402545586410611041680d4440c0600040d4289021818142800d80d001c2d6962103c0c0070700e4042c4100400c4014455a6903c0150903421600c1c000b8080c030750303440064078040d2a0603664071a09500705020502d017581e038104010120b50040004000c00d46590040c410740c1542c2c0821343d42c20040034500c0c5084415404075000b00c41c00ba0a000007010b09141c4c60083c14000b10100007441075070104924000704001d2048241034910b88050b41e59a6240e1940c5035005048030392000750400300100000a4043c100520303500700241407024034599a8680328500303684c02a0313024048001d480d24011440c00240c020b507906000303104000000d901611400041d141c460200c8102c00e2081c8105a02e03000c11000e2502e4000400040000b66580042d02501034108400184040890343d804400101849010b4001200441e00a88215565820b00c07400002d19030032603509402510900e6100740b514101040761805142c2c134903d032 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 567316187 1250 567314937 567314959
    0x3010e1308300103031106010f140906040605030d020615060f0d1814160e06060a110c04050103081b0c010e04091a0108032101031505191508010608010b 67
    0x21480d09505092040c1c54081028401e00ba4a107241d503420502071402511007015441c1120111403034840d058010310003d440c103410801030032682c44c0021a084000b2030f0400c2d0181c0c0d070500401c0041569500596041c49401c0180035002c1d000315003140981600800a003050040805006407840354052041c10f04074100450140c5119552200030350404086078048441309507146c0d1030b000d508903c200e010ba41c000540b1104e5001c2008056001032080f45814807080c40d004c00001c2c0c441c083d080300c0c2030a001038448841444802070080c5410748200920030001542c60307040800064200a80c950307820020481007504038000050039034504901652000302c403920707800c1448050495034100310350600e8200c0c040398048050b022150302810148004589490700582060020711182c0c0300c980e01c80200320010700110302004030402c20500030b40d4003c80c1980710b14245029907034120035001c90552501e00d2990a0180e100940000ca90710000203205070340e20703048107c2c00c849140c41d02603401240264 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 567317437 1250 567316187 567316207
    0x806150c0c1c0204150602010e06061e120303071d1f0e0f150c060f01060f0c03050c1f05060301020a09050f060705160501080f0903032404060b03010e1308 68
    0x5080701e1400094510710b02849640420151a01045c100ca0242910041401100d90911550020101800c003d00036420b240020606600604464042c030b90301d410f40c500c1c0350742ca4410003100030040c000200ca80d6854090002850100c5180c2112030505030f0101c1d00744589003040b54900b02004207451041146e058110a403280701106440d40c1d0442c241980d0f2003a02e07a12400d48030000e810344030004d0b44d02c2039084110750814500070007059410000c10018410143c0c0101e1032030902c2c015080140d82484903003820f0b600c41c058003051410030b20407265144105200458120358045403510240403580b01c1004250a0b8040e4540e05000147c44490400261929807a0000c41103030150409107000c0b99078980b9414440102c1008041f190a818200900c0d40e008120662020304000c1598082c2004401c1c0d41d00c910000d807080c1400400f90000d440c101b0301111021001c03c0000308100800d507a43c8103001132541003441341e1000310503144005981c5402d00c00c40007400a51010303d0314a4510425 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 567318687 1250 567317437 567317449
    0x30115110705030102040b0d1b120b04020405041a010f050936010e011703040e0609040311061f091a09040c030204090606090f0c050417030c0604030806150c0c 70
    0x2941690803031040784000a0982c40078030040018110720415036645400d06000d62081d40c41950500006005055032125240d43c026041801e0700503001000c2040b0b40500001340290059030009540145400029000b9000044410030010300c06e0700c4c0e0144441c440b80050b0340c076004292200790800c1c620008000c0d4002807448000d456503020070880c20a0f007441280302e10300c000903000340c2445e401400040c011121351004017819800e4640c006d614217401e00c034501d040304002400b0207018003e418007050070180503491110401c00c5000407070307605280004c1c40212406514418040603001510003003502102ca00a06040e000092000607851103900240540310000400036039041c02080008001603a41e8001c42220310b01072000410081d0801243c42d0485012454049810b0701e011403d0302c2407a00301b8180c80488640000d0981164040e40c0854290b20a22000d040c250259404100c01c00d034000c1303006405000159a0006410010f07001e01900348142607146507154440e9501003800e00e850303 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 567319937 1250 567318687 567318707
    0x90106050706150b1c06030201020c010809031204061a04060f050d0512030405010902040b04230a02040305100204080f030301031a1b0a030504121b06020304020409080403060b0f06030115 82
    0x3031000040c212507210a4003c1d03004098001d45002c0c0c000256030038480521030305c0580c520808140421102e8070710380c0003070360b20040700a4083c18400382e000081d03182d82060080d03c40d419418841400185440c0c90702d90000e1100c80c0312140710448482c000c07035403410940725200503602620014100d09040004000c43c40c225907004070703198030405803985c5080640e400658056071180001240115291040000751180c002245010354a018560300d84030300c07818240c1900504054203007155464508038100680300341d4201504601c04c20120a03124403840e4010402c4521520540d50520900e000403070303c07480300384405462400d124844d6a00c0d9541400c8094000c81e40b0b06038824000180000002180c0102e5403241c00300e07580c1d070200400d01c64559072620f41001d041c07a202076405000c03140b00c00c034502c5214000c0c00141d400b00c0010110b49a6500202174240c00c8061551544c1d52490305002924040260502482c1803030102c000605244040e2410ba030898403040304450a8400308807060314007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 567321187 1250 567319937 567319943
    0x604060207140d0807090603050f180f03130311040204050121060f03030215010506030709030803060f041b1202130302040e210c01110a0203090d0f0b0c07050c0f0901060507 76
    0x82003400710481c44100660011003c1546440c4014035282001801c0e014a5501c40b400349801c0408020540c00c1a82c0e08a9201c100d200c40905c21078402140c1310719125491001096500c40007540ba54140b000c1c450401c102ca01c2241001c000d59104020b10003603008a115090102d128488040b0290f40b08070110100250705030400542c69a03145203031502003d460380b041e400342c0c0004000b04000c44c060010a80508015150036180d410303c08001030513210b8030f11001c0d04144011000c00c0c00c0c0e9540751181003c1580080050002800703c04d0040c0e0445c0215400001141c0c3e5102211000300d01402942d00c2c00f40410b0302d0518041c50341d02400301400640301883d90314007461441a01c9810040e142d486c6858602c4d552170b4803500085034035401c581104600f50030341c88060020300010790b4004100c80c007d00e400c0d520350000b50642c1ca03006080c2e0003e110024603a102000802075025001030103000041e00481c102c410130210002800322601148001030342082c81140140b200c03c0c0104000d10900f44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 567322437 1250 567321187 567321203
    0x30d0e07050406052d03060a050702010c080601020d050703021006170607090b0d05060607020909010f060e06060a1b0602160b010603020306130b031905070f05120304050d020a0b07061409030a020604060207 90
    0x1045c90000e42032440440d1200c00c000d5503001444401c0e5424440d8503031300c507240e003040d10710b6041600020303549030b0052002d44100840081c0c0441018402d00c60441c116440010a01485480c1d4400d02080602003840e080140b081000180c50b0701c1c4a05198005c07034205206107442c10741100d42c0035026201c010300e2207802403410000d04005031242d00c4014400d00900000040c0b002e9028050420382d1401d9114030390740300b2940140002c5a1b210744c01c03580388100e9400d04c0200d188044500b002c100e000711801500061020845000c460210152050010b10038980d46a440e070304c44a0580803400143d481d280c010b03102c074801d2540f20a0f141e1100184100040c2101c607030450b628445200f02c414000304881c00c2c3c04c04070b0101b192030350124408c0b010384011600340019007010344006a407402644201d91042800640740d00c02c2d9282c8043c140040d00441c1c04441d580d95440c20120041c00300c080340f0307501100703810340040d03c590f102005a4a98958990241c000342e21203846030006500710304002d950400e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 567323687 1250 567322437 567322519
    0xf011514250b06030a03020c1c12020714060c031905130803070507050d0210080411060c030c0601171218090721050403141b030d0e0705040605 63
    0x4802800e440e044002021658946005502d84400e4456002d02254002e9110080b04400a0340100e150f251075203055890030b0b40010b00f49070040d195000740802901d0010380b0030305422110b82c0400c0340401c0c1d40c901190a200002c1d0304050044603c61144a212035800c03c1c011103485091882000700100490303d4041d041c00814004c440c496403503640b00d490706510004040c0708020080c4581c1008207002c031545516540310707030041221304c450b0b10700c52410000074400103010004801c4011143c0c54000d1700240c0c6400d10613807001c0d5298800190160540303d000d000003040003a44800300340e0b140404015040301a03001c288440c094002c688a064481650410b640c810384030200c3d83e070300c100d01c150f071080104d00c0740321200d048040b5401c1d5454411824441040040b07504001000e15900b02e4804c0259140710342c5c9110501500720401e18a03160200080742d1151700042c0d0048030035001007101740d070041a5207200300800c50f04584261034100200103103000d125a041040080c01600701410740f004c0d6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 567324937 1250 567323687 567323707
    0x807081e0d0204060305060306011a0c1213061706030304060e0105041a1903150303121d070503070501021f0b0319031d0d0b240d050d080f011514 64
    0x507401416141c4800380e07020908114141c1c3c14021140c0049095000e096194140724080d0903038004159600300c40c0e0400101c14804000401442c21045070584001e070710780b04a0108a4180c400364400d002c00500e0008694036607201034500f080c0660310040c0254034080c1b4044040d10518004031406062040c1480b000a01c00912564442e040e0390082c05c00d40e603002c007040d4140a1444001e050000c061074030784290104d4034041c050b00c060343c1c3c25044c8419000b202844e150050858294001c0c80400014900c20b01610005851810740c1c0c0d044069540ba00c0d10381c801242c1d03810206052144911119088115808032503120650030b11707014058801c40c0c02d6000e20f16100f158540f0b400c42c0010944011417011070410858065601400c40326914000c003c2d4075210100140039040b002c00d28401000700030020407006540100c12030182c040303581d142c0d0301d00701907484035943d940c800d0204002c8070004007040d2030500b420307040e60384c1140300c0521881390100c101d070b03410303d076084108e076060080080d4104 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 567326187 1250 567324937 567324997
    0x20a110316030501021b0a050a0b04020d0813030501320702071e0503060705040b1e0417030702120610140d0606093603031806110304050d0804080708 66
    0x3450040002680d12140d281c408961b49401500443c01c0b40c120094201c001507002c1070034640150040b44c2c60342d079920f40d4000a050014042401441400e00041c1031f030000407107804c0201103a004000800c058507054a0700040761003a41c901a000142c00c070500218504034106581d085039840c41142c400a464401c040901c9151500a4140e814501d9080140340360030444d07254031010514100d410b061400e0110341103802013070042080741c1c3c60aa0f10702040c9170741400340e4004108120400040f66240c1403440d40307a5000e5107040c0d000391942c1d00918904c100004000e40284c451044100400d440c101030860351034800841941e100d1104100400810801d0040c500a0403c0500000d2402740512150b0002e281d002c07600d0010080d403550813915603e40803e52450607405040c0030610802c2800e40c0942419504c00040c2114582000c8402003210346010710311842c4524100c4500c58650780f411755584008039001440c1e420304105a00010350104054004842d10004600e843c00000b00e101807 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 567327437 1250 567326187 567326189
    0x17070210050403110a0f031e0c06030b01170103020d03081b1b0c0d03021b0103020708070b07080901050f0712090b0403120f050603120a09091418010b01020a110316 72
    0x4006400801e0920a21445080c2c2150b015004c41c5d603140702e01e20b40000702c42504401d02c8042c1c401c64510f440d0b0641f04401f0000c80d0006175015a802e00c07038a88a20019000309806000c01740080d0403040e07088138290401151300e068a0700102a42d454140650b01112029002410707402201840c1d801050030000c1c0304042c041046641d6145d401040702111320031f141451183c41d00788160310440110340800c1d004102d28150241c921107081c824080000160003a203d2100c008101010001e004424032851441c500d0060313a07956240c080548a0286807404e84100340c0380104100559400f06449600419481102c3d417184400820000516103030014010400c0707400340e020400da4108035410038824070418410a6184904002074281480030035616610f4403210010010006080e156440c044d240040c001c0000100c01e001000c5447c4801c11203050986030700501c403182c00800c82a0410601410010310360680c003c0170040c1403900c030303c00c1506c8413142503a0140148007401e1100b00480480030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 567328687 1250 567327437 567327469
    0x9020705030403030305090613030807090503060c040e09030f0a0c0201030603080c0c10021506061b1207030914010e210109060b0a050a080a24050412020f19170702 72
    0x50b00c90b480c0d07042c00b500b543c800800080c4242c0215040043d070040c50007900016541620b0512504da4a640046c0c81c100707556004141c1c580309100c01c20911414440080c000e60707020003403080300d0303846602d001ca070b1707038000c8903080101c2c40b50a00002a100348244c0d80030100900500d0003052080c1d49841c0c0b5100d6601c20041200c858011142900103070a1200c145c4000300e101b88024038040c8038910601480c2034010b03140500c194000200040000e580c0c6d080410700e040b80342d0940d00000389400d900c0c0065031224108a02140310800c00003000050995100c3c031410041e180c9240501c101c80c100b06024a80003481181c00110800c41c2142940920480b03000d644100c600007458040001041004640da1744407034400c10b1400d40522400e00c0104181c82c0070340c0e100c00c00c2250840700740c2d01c80080740404414801c0301407811040006210100e1502d400860154007583e8102da08880c032540c6881c0f0740b0b84c0e444103460b072518078000001c0703121000010070114070500c036041810a0380004c070110340d1300481d4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 567329937 1250 567328687 567328693
    0xf0b0c070218090111041d15030303131505151003060806150a09050621010b0301140708160f1809050a05041b03050a03030b011710170606030c040c050409020705 71
    0x3c0001400d104200d001403c591100b0b007407038a0b1402d0360f0104004600c844100409040c081280c5401c019a00600c500c0b0003015262285040070342c12000c6600c242e0140c612a1203008401c0c4400c00a20030b05011f140740035548100b8582880c20701c034040524403540002c040c9e0720000020011700601056005901490070b140350f4404130f0003000300341c21084d040100002e2402061260303903034a010b400c010041d070901801d042030410b080c0f0140103002e00c04465406508060b0800c40c50002007509074403994136910392014030b880d0b030140c1100c00440b4440b0900802c1000903808076040c066990410034840044489000c50384600340401512400d03158158501c0d00c600c00d010400c41949100d0081b6148102e02c1c44030b091454651540c1c42041020103000d041e90764a1244c00c6900c1809125105180d100f140c01c494200b815100003070040c24480e4880c90300743c50007424422080881c2c0540107800060003844c500404004120003004080c4100c0709111040000040d150701da4000350070a507001d1405 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 567331187 1250 567329937 567329941
    0x15131a040503160b0712062102010c0c06020303011502010c020a0b060604090e0c030f030f0a2607110106140f04112a06060a12152304050111070f0b0c070218 69
    0x70203802540e00301e00348942542804403c8c071031060b02100c2c83e040070340400054446c2215030b00050340daa007246103010344854200c820110b0780c035400000441c12607001c40098031820705804c0702242225807551841c00160801e16800000c119040f002540080c4014110307858980d84030b0640d411200341e906400102d800072800303680503140c14050450300900314000342d0b20340001c40e5400013851140c00040b400b40318803603141010515401813591407425540102100e1070620302e00180c005502800805400c1d800c1900201d4031907144106100c0f100c202400100303090004a081002030002c40d503106103d607206010401100120b800315400198540c0520031034100718160850522400501450141c0b555500802150407401044840560070600080c0303600700c01d01c8007401404900b502840440aa162000d040c0c51040e81814000c41c0b2950080001d0303e1500e61102490203600e6015080035140f00341c10000c14043c83c8019480030001103031910f48007445d0300107050344c4100400350b0840091042 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 567332437 1250 567331187 567331201
    0x90d14010c090f0b03040b07030507030204171015080c1e1f120605011407030e032a0904020312030424140901050610120b1215131a040503160b 63
    0x2003c50f0103040c10408107440c510703098544844107500a445101015503a40000345800d00c02d606450203401d04d08011866440740b0451143e030317125144000d54030a4070b000c81500c5441c000d440c2038000c40d43c44501500261504100300b240c82d60000040021151800ca980986030340c5503801d01c691544402c400c0240312641800c020591a0b1103460034080924006062011b82c1e004001c90b0500586802c80954841c0309180c120380c031150040010790580300b840b50040e202183c0b07405952914401400e5804c0c44d02c82d00c400c1190604082c3c070040e415070000050449444000c2004684c014018200b51111400c0d101e1005140b17440c214003c002c0590b124043c2459104408001c0c2c0c10105090091041e410035100040341000070080f503209020011440b22514007894200d0705201e00000c04034005942094080c6441b80040000003010141c100005801024012448004260001c0c04018040316005c0a88595840908183c03450700c028030610114207080c40b0114126407207119603a50300e0414070 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 567333687 1250 567332437 567332459
    0xe0108280518100b01090e18060106050d140c04030807021903060f0f0b0102070504200d060302040e0d091208070203031b160605270604030f03080f0c090d14010c09 72
    0x3040f40041141001c420b610742d0303a4801008402d9a0059103102c072140c59501e02e900030744400c0b0303100b20610f001ea9000010410340040103080d0300700c0328200501415649039160b818400084904070726181c010301c4148040f503019009850f00900c058a981c0c00240c3c80c2d904070040d986140d20444620352100c00d82c01c00c038103071802840180c0c2c0b200e0000340245054040041e46404142c0512400b80e50349206800e0350318051f1011415060303040503019a100b8000c600030006c0c050b140010713401182800a21500f0343c0c07000032410812070181c1d44802e074a0741071030f01001c02a039000206076501c80c0248400400740e0f600340000e004888541c01140c8802140224450070610444010301c0d10380c1e050030040100079041412501007103c203020644401034038112014400c151700e0041c0703420820203d40032003040758010706445401d00070340b524007440d41c9219411881000860b411024441c051154440c0340c00d040d80382e282c08078841c070760000204c0074031148142182d090401000029070703a0b003020460340e140c01c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 567334937 1250 567333687 567333703
    0xf0f0d0b180402131d0601030b0c0f0301150c1205090307080d0e040e15040c080c040510140315100e010b13031e05100605100e0108280518 61
    0x1510440100a014480e1400c412001000613008820042140d0450308140d4000c031503040c62410100d5a621400000c0c2c0d5540b4001d00044075141108400300303041c100c200007920045c80005d00c908d07141da07092200699120b0311586081d130a02c599680c4c007a000494000c0f10211211050b915035481d1070310081014607100d01c540c40a5415000103100c1180030364015050307600d1400540c0c001c1244d80d802c007101c52a00300c40641c2010081208030074882081900c2d0f001c80102d0303550104503101c0715042c10400c42201c80613140842401506e010810291900c86200d40b80c0000043c1980c80c0e280c1550342d280b085804c102c44003210341510f41e8040c4601030601c4642409018102640c50504074016600440c40c0ba480c00080c0c0300c040c4400c22590140c1c00c50b100d1680141e840001d682d0203d040c0c5038030001a104900880b48100b6030581003c65051003120090840d0f0f105030358021060700d0382c40307419400d4030000e030800c1c40541c0f1803001090650428000e240c007452001c072000c0e100c6500e2216041c1082c941c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 567336187 1250 567334937 567334939
    0x50f0712030e0109050f010309050307050d03141b0304030f03182109030f060510170102130531110c07060e150d181e021302131404020f0f0d0b 63
    0x80601c2c24400c60f01c86e00b409409550307013824005603240050800c50b10b5400b8104008100c3d200e48809802d00aa050300403010324039003604031401c0ba449a0100c007030040102c00300a00c66400500020300840d108145c41c03103034842d26090002d00c628402809058100041300f05465094044031690b502403071100100380d9918840c60301c1e401050131942c03880850540c513035001d80b41c00e1301e0714003040074410030304600300060850031481280c1440901e03000e03002c4d40102c0010030b40782d030361403100007103908080c40280b00c56200680342c030411000c440b18200d0046020808407034060f5907188110315082c10900200025040b2400404185241060003003049101c2c001b920b00408030b0740b980c508103260b0102960480d12100102094034140511002021019444054054030807030111150010042322a080401d000751544152420030642241c2644038000c04e03195030200c1e1881c20000d084401022040075400200094500209090b020499802c031001e8101c42503070014020b4036045803482a00310340c01c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 567337437 1250 567336187 567336197
    0x606070524161b030306050618100c240b0310021c09030f110a060203010909050705120c041d03030705130621020d0f05010f1802031b07050f0712030e01 67
    0xa0340c0359000f0b04450581034030f00788040e00504034400f094041d80020001c0e1502410700c949075140d542010302c404a8405030b0718001c0303254114410307082c5e1003110074540b42e41d005040c560700340c4a004e08a002940950041d9409503548103148085503a0601c0410826940107002584907080b1013018400042021909032001d49007000d0710001070b400102803284440c0d541842081c400d008500141407086510008200320b00c004008901d840303066000841c81c50140003161806503c1c0d8041c01211480c442c032001c0e00398080b0101000d5868290400b00c80700202604401500c05004805440e5400643d0f60f400842d00100e01455110707200502c01005080514198411148001800804100b42e00038442219000aa98200100103400c006c54210050707400704040e694407150149549458000c601420402d441011031107625070003900d0141a401c11030030004001109c1022859000840881e441d0068050b0410111401d0003110020080c1d0340340d0001c1281c1910f0b004040750000d15a00d41880 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 567338687 1250 567337437 567337471
    0x41107050f01151203030608030d0212330409021c1e030807120b0d05010e0c0904050309010e010c1203051801020a080606031308070501090b011a0904050606070524 72
    0x104440358040c100c84d02450544045101414210080d02c5242c200c2901407100017114801c0d034000c0da0040295803d00815440151210709030040489503400c03030b454180210f07529441440c2c00390003644280c1c0740014000140d000b619400300300b031400d01c82281507481e08014412403c0c80110801501c1d11101070003070b075041c1011564050040300016020000304004645c5280c0c5202843e03000c0801c40d14000c2420607103a02628105010745076264189510340141c546503009414030001c590b00a40e030210107541429100c0e401100d10800144060b81080156206200491900d51303c01081c9121740e80d010a840c9405802000010340c900900c481980c0704024005d41c003580f01c0c0d202e5401807022116145d80c2e48a00301142c42c200a1320401524010002842d0b03810401c055000003511841503540c4c26450381d9131512140004440804029051420001500d20307107000c1d803249504c103a000780f8503070408009458807840c0a01d00000b110300b14403003801d0a00740d01014004143c0c08400d40c48190444 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 567339937 1250 567338687 567338711
    0x712030507030e0109030b090106030309050301020a020307150908032d04020d030c21081b040b070b100b0f180619050c0f061006170708060f04060302041107050f01 72
    0x15205810010b410046200c201e02c500c0e03031045011400668014a500840e802d002d100b0300d00070700b07035803004a0204204980c009041d041c1802035510804503500510309050154407403000c0c45503484039960240703503100610000107480c100510701984641412848101200090351165504032800c07000c125200e01c2008016a200c548000e130046d81890200010803082c5040c1c51003480d41d40c0c02080b0f902456282d80c038060361200b24940b1aa070301602c12000d10001d0040010288030300d0294003003599040000f540401d6410b01e107182c01010192404918968fc3d00c601c1800390840c5182d1080c800b40051070200a2100c50441009030301c0480300d99190016001002e80404003095003038007417000110300080007a030280110700003040c298003a074203a031500314159501a5464040e00d4049103030315010001048502011901c2048203884090007602e0313541c1007210445095400356407140c0c45000100c0103844078025090b068034043c030903a44a0740d181c42e0681c14007000c020300c544186c2c5011301e41045 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 567341187 1250 567339937 567339947
    0x92a0e0a051003060e0703020a1b020105031f1a070b0609010b0327010e061806070906051b0d0210180512090111010513060c05191b05010617071203 65
    0x8a407070481c2c1e4041c01201c00103081e00a0001c90f0321000000324503000f007002840e0140c000340040304c410780d6020160703200400007400d640c0d0a04000707030005e201400003801c0c40c50b00c03c901d0011000c0303000c02e0a85c542d50303581000f032980203103013407400100d000891141c003000b0882800907003107501120385200640c18410385e40c005000040280490a2a0040b05602007246440079102c181c2c000e4000e0104510131018507a0750031003619007428800000290000b0240041003d074003810403540c41c0000a494014111140c0d0403c40440f426080c1144540280c0d12040119040700803168000d005510590303000078003280e1603e0802a0881a14100c0100041020444500c00c8920580403a00d07040610012503144804126800d040c0d0300c0c06c014060a6241511880c2c0040d129100501c00b640d00c01c0070807a494041c2c0340e0b0310341040e128140c41c8500140298a000d403000092443d84040e180300c0c0c0c4800c1c0c00d540059002c02036a44011203042401b4030306100c41c4c409080c0c0a0b00c100c214414540d00208 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 567342437 1250 567341187 567341189
    0x120f020c0a060506060f0301030b0106020d081005010810080115141e040c0c0b01030809040b0406120201080403120c030209040606050c062806060e18220507092a0e0a 73
    0x101c0c0d030f52a000503103a80c0e0b40c04161100c404c0d603622038680b00c1d80c482c50f02203002d4000b07010b1103002d886090900218a071080c01110310078070030702c60245142d034581401900c495401800715003103c450b01c1c80104502209100d00051000702035207640e00b45140101003225055031003500ea0080c1170301c020042480030b007145691411081641c000504031101202103c0c00000f00c2d20060901c1c0e072003000001403114040103061201811a01000518146010002203402d248102c044c2400307400885400b6600540e04c55074007601900305402820b03520000d03102140c416822501c04070350702140181e21801c01d485440007901017418401d241c17961317030044582e958500801c25101240c803401e41070702040f00380880c00d000c1d04652005220036034441a001e0300007420300d0380880c014010198000e00041082e01c460740902d18200040e903100102c0300c5100f080c8940700c00c00b034076940f140000009090210348100300718841b0803040d943d88901090303031300914602d01e00103800400c10321110200c507550301c1c000004 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 567343687 1250 567342437 567342443
    0xc0102070b0d020c0106080f060a02030103021f020109050105091b0d05060c07050f0d03050a051003120c020301140907080d140d020d18201807050721120f020c0a 71
    0x140d10b03550341c404800d0183c482e16003001c0c15035080510001c1d8000c000a6440402001541a661980d9071140304600700e0000348400b80d4081003020001094a03409150420b011815100102d18148a43c07509425503d040d11548500d502200c491007021144031960071850004a0f00300c3c800d07488079240c1941c0e4140141c45259803101c0055280100300c400c000c00210850400d090762031003401e06c5d402800a19003200d181d6805414072002600c4803400741d141c070054985c0121203c03040424144212641203104074101d030035660328600c0201c05c490102c0c1041c40381248030014601386c0d08040783c190501c25100d07410350a007c03201101262800c000d2040e0b030b0f9124000c8400584620113158040003030141d14031410140103604000909000c444d4082030380c170b811007901c40341d101c01446007401010b4444400b0200000303420000306030307214812002062600d008a80c90444c0742d0968804001089814401e40046210403484042c1800341c0e01948400c08440c400840c105445811215104d8030354203001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 567344937 1250 567343687 567343709
    0x305040c031106160303051803070f031404081605182401030f020307021606090602100509031209030309210919080703110f0307270f021801090501020c010207 70
    0x220b80c0039180c100c1603034030341188591510855000f505005c2c00425055405410418108140613006080001103956603940300d0150380420001b6101103803003030664000045101c1d020440052240305c2000226103420040c512070024910300803c000241520300342c00c02c201803620f001c00c40081c80c3c1c001007032144404049088a0040c00c840102c00a0070540c5a00a62920210a00002c2d43d0f000035402008080514102c6481e919103206941218240c40f030000141d00003640e26419200c07540025030010111000c0328103210f5543c2d1002140319044030849407a90001c41003000b11102008034030303048074a0401a0300c2012030201111414810b0003465405080c101401d82c8e44c4d03207104c10505c0c00421800c000d40391401e850307240460500303500c161803d2007504400107036003061a001c1211801c8900f5018000c11a038021456185a107210540d04a88181c0d00e40d601c035000c1c55540020200740c050100b035081024141d030000b504004490b0002e0703045612102e40c041850360009001030a9400520030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 567346187 1250 567344937 567344963
    0x6030614121504170409390e0f04050112030905041a0405060f1507033905010f050103081b07050108060609031c020607020f010507020a02221b0f0305040c03 69
    0x1408500480c042c1350052401d0000340040c2c618455409a9880541d0b0381030300c144444824101250200c1d8240c01304440400034031202c15030fa025213400343d070340340c0b001d441e0301c00035201c9400140444000f60b0000c41ea6000c104038400070103078810851800307488103c5d020440601c184505c0240078020400d554002c907500c50120342280d42d209584803020074014540ca10040e80e40818520719082400300b00d002c40e9005044209d034070780d00700c24131241400d604103c0c0c04408030440000f40a00b00c807072042e102550781c0c5401c10200300300c6010b100d01860144003080d568a05021240602c482060b040408a401c514801d21031607a2003014180c100d40203c40c1070381c03200300303110000303050030340c100030841c007482c181044241e01603004240284a9001d6400795400012101c02c900d080e0b560840e910001030704410054001407501c001d2200019030480039011000c01001050300407140c0c011300b41c960003002803401001c03040d841f86036500d06251500d414405800c040c1c1e43e51201d4001400020442e81540704 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 567347437 1250 567346187 567346193
    0x12f040510030f0e250312050a180806070905091603020306120708010f05182509050a1d0a030503010e15030d0c050d08040f031d04020406030614121504 67
    0x20b40c82809100b00c104106401c603000c095417140070b181041c070700700729032655403034282888880f880442ea00106030000c40202e0070803c075003680c0000c150300103011a8a07031001c18203000c00d00c1880a401440000c000e242040c10000d07003030b50702c5540070074414500c2d10100030964242110700c2600e040c2d03c0c10302684a0711b070100041c501034a0030220b42d41a1003080300000d1500015000b840610440031030400c969265003c0e11403440b8020842c80f001648a1522401c5c10074002c0303c1c1a40e50315002c84003841003502d4202100070fa45090781e58081e03458a50680040080c00d403401c081e4940180402803152043ca80d0700034000303000510a1509211034000015100015222a081c500c100101510042154410f014144907007144083c6d0f0644208145507000b140030f0b0003000c4c001c0d900700e40c904100f001169001c9030300c0c0400111100420354241c410300e00c5921303a80081d20240240d600d0201c0e0b160304207107088980ca00c602072568892441c12603225040f00000c11099043d480c0340710501a5951542 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 567348687 1250 567347437 567347441
    0xc0a03150801150e060306060306010e0c0702040507050d0f020414040b06071e0c1a090603061f022103042301060f030809090f220510020408012f04051003 68
    0x548500c42650803c0001c20400078501d55280503210036020402c9551940b00505540e2601161304070380513440f1380010b1004950001d03441c2e91105030f01501a140c0b640b01d60102d4240c850988586001c0380c8041400e1f251003105001d40e200c07031000040c0131800d103840c11201e0907240c00c0c0d00c10818000c52fa60131420700242c507031004030b8100503001640c180d14403003580d40c42009620094010748031400455070100300c1000440200781d0900045202c031b03040c0014001000690341c000341180d80e11411546407103201014016a24611a10325005030410b6000c15074408403444181230401003610b41001080b0000d60180c484400030051444814031040014082c580140026040041d030b46152101c00020041c40b0030013800d501d10103440050240c0c0301c2940700108104d05592141c0200a404000d50800d0310850500719003d019400b1588203020000021040b6401500042d015945aaa00650314100c1c0005040c81c0c82507070715980e10320500740c21600d18a00641c02864400c0c1500b8a052900074400c1e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 567349937 1250 567348687 567348689
    0xf060c01020a200c060708250605220f1b120f02040b030c1e0303040b120709080f0a06020f0c16030c0b1201151404080106030c09050c0a0315 62
    0x900210360711034003000003a1980c4681d00350000c1140006030365595900c0003207426102c6800c060040c1c2d0030110ba0703503204800ca03041005002000031541e81c2000e503030404032491540843c00307103000048030f0420300c80c500c050080c0029407136000205118003200041c440300481d2041d0b500170944100c02c040e4084c01c40003041da982e1003420400c10408000d418031a00448510007944201c0d01081101c203c0d500341502c4224105080358003c80c3c078544c0443c0c04a41c44540d40094100809503840c1540311440c0d0780050b000030754150f202d1550394080149480c0c111300d54030040c21105009007513109400d4400703907441d04030200080c4400c3e008540840030410120655074501ca808082e11481501b050801c25608141d120a440c5800c0f500313400281c03284648201c3d8056440d0440d0003605038244040b141010070010484070400001c0c581030150f580003800540041c2405900104455295090065029120350815441103181c10244510203c0002c12615042c419040100b810313407a6002001d043d43d05 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 567351187 1250 567349937 567349957
    0xa0b07060603051507080708061e040f020409020d061703030703021305090408070318060203090f1809030d1a0d031b020a15110109030e1908010c0801080d0c0b060f06 73
    0x10320351103079041d1400034400c0ea211798039a42d90540b81d5503036180101c5a164044d90300307a4209030488134608000b0400d012800800301c0150010170004500c1d5400e008981c019400724844981c0031800f180c01941c00d000c0e002c002e005501113102e201407103080e150707103901c000b420f84014181d002414146c80a04260100e0040c8402494042c9905d0315040c4002d032035012280803000104010f09000020841a0503602510002d41c015030404075075106010001c0b402690880d444204070000b940302040c090310082c45607003a81b010b0354480304901d100e0f10a075144504070b248071002820b81c1c40e00340d46403c070204240f0768240c90720f00c0e80c01d0b606a02d1480f01c1881502c0180d0041340c00e08000c07604078412103443e0f804841d1a920030158508404480c0c1c00c80341840c0c00100000c5000500a01e146050f1070304044086800303101040c4c055075000a1801c50ba0403c540d40c0c0452503040041003401c505112602d00d04d28241890b00c0d25800340d07a01c08888000c0103255512035548030130182d0990311103100f40d0780742d0384d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 567352437 1250 567351187 567351193
    0x90a0b060f030f070305072f0f0a150204051c080d050702010b0a0b040b03070528020a0309170604060f4805091c020d0b180304050a0b0706060305 64
    0x1080160110142e0080310320210f201020004220042e100c2e20690340308841d1940c03442414204c0107800ea540702c800307112000101d00d40b0003544080e00c0d024400c0002801e8404002c0460b80a43e1412001c1c07045021800003100d0300c14482000180c9501c00d200c08810f801c14110700c074140d480c0c9032450642c0a85010400854588810890790503015407141011000c00c80707511f00a1990f46094800d18429401402c0314001c080c004142598064000b400031041c0b20440b030b0000e082042d11080c0594000c94220005038003150080303003410b03000198100a0042e41c810140390002202c40c0982d2810f001c2c0008080d45c0e0350700c3d00070350b120401d45e100029115980c03a0311464404520082d008413069880451079038402c2c0c100000044600800444000c12240c82d01c60504803c0020001d100a0042a006401000e02003030070046c0c1d90350a030641a103108549036015401c014900c07020a040700c003004880c1e075108100c24003042d52907003001e10032a42c100b09103541c2c4100320300d4120043c1590b60300082c1688 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 567353687 1250 567352437 567352447
    0x80a0902120a0c0e063a140d030606030203090a0f06151403010c0507030909090302070302061c0e010c02072d060903031403040b190e030406030902032109090a0b06 72
    0x3010100e41c0c001c1380c0c2a220f41401a4840000300454104180306402d82480100108581c039103840c0e1500c02c014008080703041820b41140c540c0501903002c50700c40c179410f41180414064076a0503100750006010245000c50035440e041e503200755501800a000b510340800d0f41c040d5800c0004940003a041c4410445c5031980050791350b6501c1c0188180403203000d100b5400c00b511401901d00c03a0b800e4900703564042da18044114900140c100040115100c15811402441000b1000d6100c05008103117507a90240c0c17141d10b084c29100d910341150588400004664103120b9104085030380003e5410a8031004c1480850141c9561098000004a401c04400c9400355500c00115190810016802c490182d02c5668a16030180404203123440201d90052600081c40007060402e82d000c4682010300104582c00203264020010700d62a40e00b083e0700a0b07000a031a14098021401c0030302c80c03d11503014041c0d8400034840700e03030000c0c0c04500072170302514092140b0000007140c000498224021411b400780c031042d0343e9 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 567354937 1250 567353687 567353693
    0x150f020a021014061306030209040f0227010b0a1e091a03160f05092d040603050618070306050108011d030c060402010e01020703021f0f020d080a0902120a 68
    0x29410030222100036001e4940c400315800385a02458010801c50000d0841d6036031810100516007410800c444007540d03640c00c0200058443c00e005034090343c019000c20f0000b000e0b92042003126119070448030703042c9591440e8080e0440c0c519a0240c19202c000510603100c1607450030031a5250194201041504490b8008038480354000070008142c0b9041c10882607050480300c01c8040510040d03842c1040461060390415045101c2e40e01101284207034500a0720304004480010407080040c2c02521030b50300c045000704c9450302245403a9600b00b4055609111144c51074941344e8031010000d00d14800040f540c010361210120070b200c4c01010b954803000400165844888040c001d10f000e18000100041060a6100f286030010986440c030501c2c0c8010b10840d03545600440d189080c0c8000d03d815842110340120060342c0341c060005503100f032a6420008141d030309000400d00707054900d451042d90007403c0a008000da0181c9046d5100c8102800032421810600c040344100241c00181e402a008408400c010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 567356187 1250 567354937 567354941
    0x2090324090f0a0804050d03050d0e06090c220e0a02120318010306030f03030b1306140f010c1a071808010c0924110304081203040606060306051507150f 67
    0x319402000c0b549081c000c600035550b40c0b551200041d1900c0d00c148420091445d00402c1091080d1007890b05500301f2020011600a60302c00351004199a00031030304001d40403804200d85016200129024a4481010b085031812a07140c00a403001554030b803108000340705410044800129409440da004d42d0318240c141c1512030b044030703945825041607a614440d0b558400c0c010781003602e800181c8410841c259a50070b0740200003d20f1140e40000c540c050f040c55090080c45140010199082d480c4d14900c0c080b010801e003c4c01c581d05c2541804032080c0000d01140103601100c19241d04000c0c103030410b4643c00300a441d40c004801c840118041c0281021820b0841034200c589201070580f03864012a4954140d01e10a400021042c2d4468807507002c114801846030000c20103400c0c41b40c1c2500d01e415110380301c9600f422001109039000c51800414442084460f1280c0d400a2916141c200a0305090800160310700c00b02d1500d140201c0b4011440c02c003840004404541d81c400300080800c9500450350700400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 567357437 1250 567356187 567356191
    0x9062110050306071709011d0106212d020a062006010e0c0a0507050f010902011416140c090f10080f0705101416060606021b010302090324 61
    0x1286000403000040c140c107000805078000c2030310391504428407201001815440030000c01301d01007907485004290340c1c856265503c43c07850902074004280541012220502c0d50944018550f150745405401d00100b59001c0414603400e8032485500c0003841006011201901025030103540400f01034000140c1d103410881e4180c0b60400410280380750a0040300d582d8581109200c0c0345581d42070b40700040c290a045c840101072200446c1001400c120b600c4c1c8a051900d10400740050580e99520300395000d542c1c00c04c0705c4940705042d107140341b0f1900e0765026455007240070002c1c00078090180aa00c803604c00e078003030050311001580a481d0803400c1c50455107425201c0e005451f00c2c65401e00440b03000c01c29050109030b034a1201400c0001708415442c200a00c0200001101040308020716110600d40b0314003504010031041001d074415004114441c20b044007100c0190780654250b502641c0d000c2d402c0c9401d40c40707000d0515000d007001601d480e07460001c2810180d10900200d82070710918640e40d600e11200795128 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 567358687 1250 567357437 567357451
    0x19110a0e010b120a0c022107080f090306090304060e060a030902040203070f030e0106061d010504150305100e0702250503010e240603030d02180409110114040614090621 74
    0x40303e991140c040007030895800d80000710068114000f401c00000e42040380344444508a00c401d40360800984900c101508030750104841c01c1400039000c4041c0ca410020b0540182084001d1440d162074000084d14482c02c040313a45000c1da4012070301c1d01245000e46c1c010b100c101d0300a0020356807454400360040180115146000220745810513444c4221414462001a0b5409844030030829410580c450440391526a4090402104100100e0600115200700c0311442007504e01080c541440340615400603819040038400c520341100300014140c0c0000e01c00e11011b0051811211007500c0301c400b000a46141c1c110b40d4043d030a10080d0341c44d006002460520302c214502544c918103803071060030b4401c40416074103150b040d44140200106003d00b94000c002c0f1071001c5200d00007004c018408078043d15240c0c4000c0d03940b03200c0c4130048001c03940c102e0380d0010b070a41c3c819a800d00e0207003040b030060003604c3c083d822604805400b003062a81c9449560450b412098801210860f0140100c10140c503034800725040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 567359937 1250 567358687 567358717
    0xb0a0306050a1413030c05160305060907080d050a1107170c0a1706180c0907080a0e0c0102061305011524031a0103320108070819110a0e010b 62
    0x8090a240c4283d03005000e4180d12480c0c43e500c010380e031800ca41c1c09101e010103446034041c078030054040c00d22030300407100103602c1072003d000e003881c28040107801c007222540041e0301508004080401194450700311901469a424000007181e03405110510300181074001171900060710400c00c1c011100002c07031100d00300341115000e0784a600c4079400030703060310f008011204650203103000ca10300c00e81103e035014100d005001120000400e88002542e401010740c0d407040811010000d2001540e214064840f144403084c1c000d001007482c000c0002c0d40c07686d00900c03800f0742040701101c803020003800f9000710a00d0900c0d035004080c00f58442418054014a2032501c43c1c000c409000b2130b4903014013070b00901519490703210504003c842e046006502900082409440404c0000101c4c078541e128100c205800c0880b021282d880d5604101017a46030001540001c1c2090784026030340c0c030a408020140302200c0d5400101d04c1c2aa403d800301141913000c1542004000404200c008560032604102601c0b08484080c07003 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 567361187 1250 567359937 567359951
    0x12040528020306131b083a030207020111030d050a0b0d0209070e0d0602031005030c19052e0e04060501030b0310020a09050909011e09030c0605060a0b0f04171218040b0a0306050a 78
    0x107072112110215a5482610756007c0800070102d000e0b5000d0213800340181000d00f00400001d01e102d05540c84a183c2200403a521030030302940f0105441581006502514901391a02940d00040c64150000b0301003404c0104401441f841034841c8841241e240754840401c0d52a030619801a16840c0410b00aa0b0300038400d15050bd16280fa01c03401401c800d01c240c00c0f080300c3c014140070030712080c10f071030f4000002c070341c0c0e50b51820082c41c280e01340d0f850200f801c1c256030b56078000f81c44908201c07d440d602c1c0c3c0071a0400d81407014145031680c0102c0d8400b124200f10b480180d807003a4622040c4d5207810145e02040e401000c020130465134900641060b618001c1e00030b030013180c01c0880700040742151100840600028842130784100007442d5984200e401c000e0013407002201a5a5180e031902651240301d4548400402140801038200d40c150200b1281e003160340507000218010781c072880e807805054815150080301000352401c0c1d440e030b1707808155030700d40140c1290f51041d16400c0c10700145c20103807180e2170600e1801c04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 567362437 1250 567361187 567361243
    0x110607020a0c14150301090b090f010f2c0906011505030c07030c02040e03040b0705010b060f070b070e030a080a0f080402032112040528020306131b08 66
    0x41070420341d90b10215201c001401d1a480390480c0544244160704120005110502c080c040c5000d03500031f107103244022034541481802c0c080c002801800c44881d0b040c2102c010701c40401e41a00603c256441d000700d40340508141c00380e04940658020418102c52000d03018040d40304404103905050b01d00506188500840c9184101c0d014030048400101c2060300b032003001c0000c1c3c801c2d009511958002800440d01c000c107010000d003568003540c07000071001000500841001001c0c040e11000c04c100b250399904001840e030300450648242603008142d00700e11000500050700600c0e2141100a0140c01c581c900000f514008001b6030000034560701044100303802400061280301464071980d8040c01825200503000400c1c9015850014014144034083c4182c0e0320b094036034509140304038042c0b0010710004200140112108000b82c1383c2100c58040f840c0f503840035840010304903800c4803001c00f00501e0b040b00c80c28104001c00c0320041400c0e61001e1100006091a400030354035074240c034003c0c501040d41003000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 567363687 1250 567362437 567362443
    0x207150b1c020d08030a0e0d0201060f06020703150902030a0f0b071209021f020129010807170c03040c150c0b10050d06050604061a12101d0c0c01090311060702 70
    0x4000294003c0c454240c0e9000034a0f45400b4540114020b5000301d905500d800360070303081100e280841d10040c0c0d5121020403c43c001d80001d4401804035001908400d03080d0f4440a5140d00f554031075651a640700c0c1c50240442d1010001100b44580058a141a210341841c040341c10000965621001a000507082e0820300080d00c1002016035009040c00469400c50f503504d00c000070281c0f0303c0000d6550396111540c041c0880c10b100080e118140c00e9003100c9910050000d0000789000c1c142c8001c001c015041420301c00010380b00b264200d400421110740340d0b501c600e0030026400e4581c00a181d00c6a804440e09e10080d0812801c088661241c0070106840e030b610041351005100900c910f552008808180a0200d9580d502c081d4004001038404207016488000b82c0c43c1e0405c501c0c3e007040d1a80341c0040c240c092030b061080036980025002021088180c0340c03540350300044103003400141105d8520804991080a00800c40d100c00140b070000303002d00840ca04020342210600340e40c00f0340038042c4500160724180b000c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 567364937 1250 567363687 567363739
    0x9150c090114040e04060b0f18040c0e0c030a0917041212110d080a09021207030510060f0302040c0e04060f050108090d1e111e0f0c060316030207150b 66
    0xd406030a0540d503941b540c40c080c04c18109020f400000c040c2081c05143c803030000b042d1410a401071002c9017420a40740044d6001346030340c020b0241c00003110a00c91842a014101ca0b00400d0740306012640000c1402d2100306450018011070810200107130000303140368a4031840410602910201101da852000103a4802c1d0200e0380c030000a80010740d400b41164056240c05401c0740243c080001d00d4520b583c00b00d00700341e902190b109495442501e04100300001040201050100f0000c141700c3d040c9090300403a0002c4d02400000c0c442c0d03846050120903240704481c000721807440100f007804204d584030f1807030440c00020300078070b40003070141e10005d0111403002850b860b4040b030076540c3c102c0c010343e40b40d01c61851070360030046102000584020000c41160401c00344580c0c050b4280000f00e6041a04000c40c9422444820080d00b81c01110f8a4015a40d46405995020300602d1041846542d0004218002d200d07a49008100e40c62641940c04180c155600114000c02d0507151022282c00e1844803c040e2642 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 567366187 1250 567364937 567364949
    0x510091713090603140f1504020d03051309021e120c0304140a0803010951080f0105010b04180f0b0d030201200c0709020309150c09011404 61
    0x4110300c0350420685500c0107140a68969011800e00c544881084060f500780b5030080d00c0b030b40300608a600700048180040280c90000d0380c01841c4c130340e00110032240007a0000308041e2040d00e0110520040c540500108d9003810742c45110641d90359210300c800340094000c4460b281001000d0884202402c08800803104e19071440302c25126103649124081c5003e40c8014402c944000340d5410081e03849604010820683d03108011207034980d814080c990044a9014055040800c40210032030b40200007041c02100350240080809140c007800300484045030340d8543c40e819841c101e9080041c01c0c90010400d01c2441d80150002e00599903510082d90460003540600c500e02c4242600101c5542d0259012400311082c2040109409071842c000400c03091000b80e066000d41d4481d600361100e5905241e400501c000c07840c00950401505011469403060f41d4041c10303000a42c0003001c281241010481c0c420040007210031090b6528184052503e9034100c0f1440a0228001c404180d034940720410554003901c80e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 567367437 1250 567366187 567366203
    0x30906070204091a040303050610050a170411030f06041703041718060d0218030118020405041b0b04090501120b061c0507062304050d03210606080103051009 69
    0x940d035000c001c020100c2c454110b41019043e00c0120424a071821510f00c201e009841c0011145810820b0003d00c030042c4041c0010048100031800000e034001d0030038904031050715405a21036446140c907200e01496204840d80c144515140320448003400110b09225500c1200404441c51600490120600043d90000e00f800e1300030b26a17124060307420000e8100070180303041e190b03c00304614001c50900ea111a0381c0100f07031034001808d040154845140d1100340e140580081265411000035900e02000ac0c1a0092140d600c48000c241132048145056403010781030345904500c00e0341c40154000d40d9200f807040c410040d0516000143c001c1c003030001d21202541020109801e0340d1210200081c1900481040070b1140c403e00c0c61402240c001c1040f0710250455440b034454164004100440c04203081c00c40c54800c0c0c200300301c1401907440d01c4190700d03c1103606042ca403254151000003a0f806810301c192078803030300b13241510001e8056402101740d41200d00600c01c0c0c2e4208604218040d003602e400b0300001d44512 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 567368687 1250 567367437 567367447
    0xc030e01090201024c0b03060402060313020111060c0406081506040b0f0d0e030408070f050a091121070e06190e0f0312090901081f02090a0e13060e030906 68
    0x481512030303d12102e103074010710004140c1c0702c044030503841e50892505c1d141e8018010400c0c20305c42d034410b06441e404100d0003010585415800901c141c0b1004007007502c0d41060a5081045901500801481d81c042d102034900318070384010601c030140c005104400001d256031000c1034046c0713541440d199502c940034014034a400e0501000c807001e035002c5011032a451030100301d00e030000c049520031a06000d00000c00b86941e03600d050360040c88e145103030300301448011302030404000580c0d071040c098040300c2101c00041a400002800300b00d042c01041a0950482c240c0341d500588403581e0480e0380d100b0b61391503c030790b010914203000303001c4a40036140c05082100c20344001015801c1c003a8401c90311501008202d03422031804036010074100200c52000e01890040401d64450300e180c00c88045000d004828014605411072901198440840516543c2710541c0041c0d07030000c0d03480358544207029143c0f0b0005142c140c10410f048030b038001c0c5158410b07500e052910840c641c0090010003120f040e080000c0000d402c007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 567369937 1250 567368687 567368713
    0xe0c0705010b0d1502130e0a05010f08030c1005060103090b0f071d0108060f13021b0c010e0306040b070309081c2405010813051e1b09041e050609010c030e0109020102 73
    0x254001b480024a51000c800c001414078400d602040c41202440790104565140403422a124402500001c4041d0001d2249030b0403883e0010f215203403082014400304580c1c0356540180d00400d1082409806202c1d81c41c208003070f08004264460041605556040c504440810f40c00c06420400d05194002080c00003c140f951070000302003108030b48020600c903422040711036140201e0b8449a1152521204010038510700d0700248120042c09100f03081001750b100c640d000180e220540140002c0070101c0706008104008d200381d00084906d0303030021309c0720740c0c5000c443c16507a1642580c0b4400105039090101d00070205405080403803080c0e60707088041d43c01e2424140199052480203004490708082c44119001050082000b00c0c03d81840e0300640060401680656040c6601224881e03103041c0c0803540d00d80a920350301c501d02e60141d00a900c01e07d00c4540d414076000c1c2d003008038001602d14400c640c00d20025440641c030520701074649440030170158441d081640e00fa2405c0c040c029000d40c0000d50500c805e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 567371187 1250 567369937 567369941
    0x50a030b040c0806090a0c0806091c03060b0d0522051009020105090a1508070f170406090b010801020d2405010302030c070507080c102d090e0c0705010b0d15 69
    0x141c49200280000b5840b00042480d00e0300c116018442d40d171000d0b4940051042d13400b21480940b0441c00901101d141c0b14403030030350780d0000b281d0008031340321080290001c05100b030f8005000f5101032050a50780e2012424800e01404007940c1d51001005d0701303429100720400604404407001c2d0300c040505a0745091045d25001080e1450060707061240801040301503a4603811010087c21130000d482e00d142400c4400140360010007000c0b6028020390f01c018000480e040702c0c1e421181010307200320340302e60b035118542680540064100140f0085400b030000c23030145010b40207030561969a601c00c000a490000104054021400303215281409500b03082c0002d500c030340c00640d0b010840c5044149000026039449182400982c00300d11036400440c0320f04074070314245c440c0402c0f15625150444505501d1078050165401c20701b5400404038601d240b8030302041c0900d022200030100b040f135603030492403e0040345005500464045906511381400d025661800c00320100c00aa00483c0c1c1c001c01d00c0b503e08082c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 567372437 1250 567371187 567371191
    0xc0305090c091f121a0f0a1e05040c0509151810030c03050a03081e151201021614030421110405090c01030506030606180a020f04081606030501050a030b 67
    0x41c480d07942c203d540301185001c90444000c02e41d0004c803d01000b4641801405001c00c02000b881148007401403080d90410f05004503000301490b20002034801824001504039114011518010b900381410070041c071501e1542c8500321207065031a1100b0342e449501055540200c840c58503886540004210414202c00c08980e612945c05600080919103948514110398010b07441166941c2c03100b2154010160701500315030300f00300c024100e0303001800d40c0384020452307a10003018440030560b0202400c95071b9917803161800040c0c2c80800215500d1540c030300c00c075500d6000030301c00369200603181e0548200600000300302c0301104c0300710700010a0000c06003005101d00d452001c0030342c0e4105490103c161941d03190310846000c3c402c254002c0401220400024058800042c001e600c070fa0040410880992a01440c040c00640c501c65000c91566410415034024060515020405280814089460301c030001d030720901c030115800280c070035581d900411000e9903024002e003038200b403c1c203004200240c50252aa9 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 567373687 1250 567372437 567372451
    0x30302090f120706120b0d03030209042c06010506040b0f030a020408010c0e0f03011a010c020607060c05090910122d082115010509030f06010602100c0305090c09 71
    0x2480341000758000a03408642c0600910740c41d04946001c01600b5000ba0a4000c078007014071040c00400c40020003d038920100c808050145500017425699a035103a521903145030045160b100700130a4172100c9840b003e40000030280c1c091044200200703080c036103403040e2003c8500e40d490051511900f004c820040e60009000302c90603680074000070a42c50001c0c02402045d15607540d03070010b0b00e21a1400c0282c0802051f1220340664500304c5c08544040d04031074103502c0c4020a0904a024025902c08a40c9074400c2c000007030543c070718090204844a070b01070010180c485c0201c424646c142c480b0070043c0c000750054426158107054800140000800c100c03100ea41001d2080480581070703032440c010f101c580e46011001c0310714000c00504846100301300b44a00400c0000902c8903583c5141420782e64003002c400904d500c1c14030a01141400090340c080000718807460385007040d11000d5a584102960f911044006118190f040c00214504c1d14071a100e000e200d54111402440441044420321081490180c105 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 567374937 1250 567373687 567373699
    0x120203030f0f0a0906030c0f0f05121602060601080f01150504031e02100906120203060a180e060f0910050415020c0304031109071403090c10030b10090b0703030209 72
    0x641400141c290180c0a00b030084401c85a4665294000408410311500035000b0b051030039040480c0305a102e8115049081c0b94100034404074419230040c2d5040c01500310180580d07a80d001000100c2e80c82e9012844074046a80884103240c40345401902d942d481207030b902598001707220040140880042c6111004051414068078241e03d90319154009414209d01c41d40c00440b4041640450502508024501800d0318003050b41d81d060150041c0200c80d00b40913002c002e500840820344c5907894002010041c01945079000c14081010301c5c1401a106051450350180100c400044031043e218031218400c00081024050620031026110002c240151050300c503400c0002c418a4042078a200415000302900c000b5910303145145000c0c01c0c1c1c00001000c10380030b84064803e1003199600818a1141e2011004401c1e442e9540d0300380346850811400480ca5100c0d00d6000341a034401c0e0964031020300540c0603510310070407606c540d0082d02c12020030b00c03580c192101e0421160020a12903130142114807001024 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 567376187 1250 567374937 567374947
    0xf070f060e0904030e0d060e0a020a09020c1005061906021b041b120b19031407150c080c07090911030c01022a0603091609110a08040f02220605060c0712020303 70
    0x80d0710442d088d0503983c13460340e0700040101c0d080d0728041315942c004103017090080d4a0700d00c160076401e48655080200302c440301d448201094003503507031118607003141024155145045588000c003e45e01d0708038045e254118400400481003500309409841e45c85141048420082c1c10101c4048425a045541404803559200740140d800c0c0c0d6420461078054050701910810f9504608100c4480903883c0c10038580b592220008114801c43d1949141600c0304500380070003100340506101102e4818030241010b9400341c1100810b006205501010314180101001075540c2d281005040e0348074408115680034ae1301079a050058141d2109021807031f0320f003000080703403170381c0401d004560390b03800035103015031766410070751128440a41c0440448010604900d06002000b4442d01525051244241880c20002c4510014090040000000300400c3d80a04800440400c12a00c1ca20014002d50742030701160500c0000555884c0001c16114168654009094110b00c1d0041002c807507000c2d404126014002841 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 567377437 1250 567376187 567376193
    0x30209071101060f140108101202030f0d0504090b1c02040213050a0b09030c22021b030d090506090106060518011403101406070b07140c0f070f060e0904030e0d 70
    0xf9000241280030b04640f406040c0221202e10011151210f41003002d141c01300301c20001c030385600c1002c980c03481c103031540d0883c45800482e00746940f80d4911510313817080740c5038080c1d10f541c8440180111a0030788410008500d24030108804400d080152102c02c260030216030016240030790007461982007002e40d844841e0703542c00105c1d40120241d84255071184010810100e14202809282c02c0b0f10002c440101090880700b00f40740c2d071400c807061105c030981e07400700f0302c2c0c0d14807000b88240160000000c4101c988519a211034000030f000b40400c211024002d20011481b02181405007505540741d5441c0c0c98203184040105403140d0421b5101c85041040540f101008104008000c6004010503460040c607942071043c60344100c5581b601c0d060141c0f4040101001081f120504d0784c1d0820040e1600d80b071400c20b0314000492a0254921034030f21409000000c91100800282200442e401c0c185108a00c80d076846040c2c3e400304101900c00d8000b5400d44c00180020700c90940c0561810008000c0544054241c0f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 567378687 1250 567377437 567377441
    0xc040e0718050f090102040b04140105090405010308070507080c030a1b0e0f090606030307030519021c0302040e0603030f07150212131a090712030e04110901090f050901030209071101 80
    0x281c4a4110382e031441480444410801000da1048020300298501483c01c0c0521400740300b6031040b048001c0d145e000031131003684101b048480c00800200f040c407055840f400e040d5210361101b0402c0fa518800c105000a8040e0b005c03c43c451107000080c05044d040c07101d5202d519400d89402441080c9a56082c07000c01c80d2581d52074900e000c1c10314070b1391440441ca4880810b9103801c00c0503151074400e81c428004000004d81c4141150103a041d0445201039401ea084426894500440700b0341c40e00a850321100c2060704d0345940680100d0720303044010a080d86908003816124400c2c45a10304c1031b25000c00601c0041000215202c091281c0303040018a010b407071400c10000102d055507110a8442561202e009201070440d0304d920a8800940040d072900b030010140d5a03d85807441114410760003129543c040c14002c0e5250301561a0240092040035240740d40c10389540d1000c1c0900f408201906408501000481c040c05c080c0c507000740803000280d09680030002c4818000f0120740c10821f0340749001032105801c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 567379937 1250 567378687 567378719
    0x524101214061008010e0103230615010e0d08030406090c090603080702100e0108061512040506040b01150c03180315140a090b0c0d09080c060708010e0403020c040e07 73
    0x31001c01e1407818100e0403c9021031408a880c001c201d0880014000000210303541c5045941c04004840e115a0078018040c41c28608201c0d1401c0b80549002c005847c440000e0a07546503509a071103200c900501c004101c0c0a104c50440503100c800c01f800002d0000d0129405401c00030b00a900e00c1d07142c1aa150381c0d502c06c0d5850f0b500122031544c0007103462421418950040707900210300c1c2c10058408807010000030004480140480e01c11507400c0b0407504590745050440d412005c0303006400a0303c5c1b810707041c103656400041d1000c61384014018000180d00201c0d007000039040c45155190319015940303031800c48007000148400034600b10740000001c001126080300c54014088400b02090f050400b0340620355801e0000c1043e040c00c2c0c14151a0300000714000306040e4009c920001c00d43e01d5010b0100404010500400010034403180040d000040090001700107100d81e11959645402da80c80300500c5522800640b001009030380407400c40686850103800001800084604403602d469072030a0381c8c2c00e01c0000c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 567381187 1250 567379937 567379961
    0x819230d020c0a090507080a0b040605030106270204060c0f0c1508180309130908040f0e0109180f06180804060306081b0117100806010308030a05241012 67
    0x2c5241c120410f42480d9039100000c0c450b9000c02c0109141080002e410501d004200300b905650310421503c4a90352039100c5400b0f040b000e002007103440d886149910003130b44403036060100c003010580c00d408101c0041c000c803010b4070341c542d580311600310301669001c0c1900c0b05038a080700c0148480e5400b199000c0e84241214071410943c0da0300c10a424907403007103421046c0e47d00288940b40c104015030013007611041800c80d00400c20080c0050906205c2c01d06060780c1c019500f00081c00c8504400c0003522a401441060607210198010000350b4801000e20760f0903004000000c02503205040e200011078940da005a4560f0780030324102944200d280d079048001d610039000786000c40d544100a0094100803c4511220301680c2e5142442c50f19000029000340551100f0044e6034243c0c10016136010f00000c82100205010812683c09513103c0c0b600300f08540045580500749480d020015040544180000403100d000d807401046280014080c8842c00300c00d09032880a004140000c085a02c04901c104200400 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 567382437 1250 567381187 567381193
    0xc100207060b010206091c03020f07030c020108090a1a091c0906180e0a2a02064303140f15060304051203100b070302060609010819230d02 61
    0x40a80307040301c226104020150704550089080052201c00042c802440d0703903114908406400c0084400c40191183c03000c2d048d491180407401a041503007000324080740b0340c403d0300d40380400e9490418003603490a1506000e0450070042d03104203e42c0c41d070440c00c207400600d010151200202c0e20f451000c0030511044003800020010003042200c1039106500d5041b46294500b0005954a488a41d10403400098031088295a0321202004c082ca0980e0880c070b41b070382400c010f0045c500c10b00100a5224082200c6140e001c04000750840407140428a0030099100310010b203944c8540742c140c0c60000d120710907483e0001d065580c01c40b101190ba05080991040805083c1d03560310745031407400c1005607108101d46a000d21420320600c4000740d404600868100500c021403512603852a00d00d040540955003c1924001d00068040526a000c03c5482c032494041d120302c80c5c0d42c0d0707031244850b80d5444e020b607128010303c0e03640c47c844000521602000079620144075200c2070546c03541d40c400381402c0c0f40015660241e8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 567383687 1250 567382437 567382447
    0x41107030804200303030a0f0b0307030c18020c19110607060f06080303040b040f29060a0602031e07080702031c02010c1e05090d080309160803040602031c020c1002 72
    0x110f44200310020951024201601c800035040c0030035030302d00020f400840559143c07140c11003005503e0f40300900c00c01008044071442596410903d1001d03016000d006a042c0880b0106108920705000f110202300d090340003410440c00e2522404901c48003000d003141c0c0c9005600040407a0340d202400752520f140140400121201c2107130a034411110941d00c0301005410520801c00410301843c1c01c0d6922a41224641c5030340c4c540c17490401900c04490000605000320050052201c2c170303114407420b200342d2041d10310b182c1c05511140140d03900c1c041c800f01d0b1740108249000301850010041c02504500380b15001107401c0030031a0740064103200c400350620420303840407200440426424000c02803142c1040c20907600e00c40040d884150880d030901084418020009001c036600e459150f0241c0000d9040b103a41926402c0074060305480d0407002005091942c020031000c41e4002d000310032502124000d8000b1440c100f4071070303003001004040000c01c000c825402e01455190300d1050007441d0b14100300e5440181d443d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 567384937 1250 567383687 567383693
    0x51324060f02060f061c05030c10020a020105090c0a0902090f03030d1e051501051b010504050d110303090c0d050a0f080a090902071a090304171c080f0114041107030804 74
    0x100d54004c141d140003104400c00d0181503220245078408000b104c900741c2880d0b00850800340c0c514882c2c5031844003580305513090021210351aa004d4098031125600901881c0c0701c203800c0c01e60300d5042d000310a60106031540d0400280845074020603007810080c0a00c0016440c0c0f00c0000e00f540c0045400c0b0002c99120b006801500300320241010850034113610800150030540300d0390021218003d04203045c002c0000d07400e038050250081c50035000d02100001d0000303180c1440d203240c42e2800d0103e02008103d981c4034500899801000740c904c181d620a0091003030000b504100190314100c0082951903020707026600020a03524000c210420740034500103a61140b019500401d10000c982c407407100b552041c0003510000350b00c500101c1095084c03403c1320691f507da040c41203003513105a40c01003026101d89400d55607d554003082080e40d90480ca002c0307503001c03664000d00b6650401c0440f0b0400481611000602c00314501d0309035080e840002401c002200f039402d00e40e90f1800e0b8480e0f10250041001c1404000c10 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 567386187 1250 567384937 567384943
    0x9070608060118030303020d0f020c0d2a170405031b1e061c06080f070801050606030622091406040c08010b0112020c0a0507061106010f051324060f02 66
    0x1d40c003803920004a44680409510145036800001c040640008042c0d030b54031081d4000d0f0001444031001190303114000305505a807100d4408000c0080b5943e80303401c58616064944040ca120301c0040f4110210034642d8400900e6030041c4900f03140320f2010f0ac03011540c0e48080025500804038070341c04266809000b410843d145102c808510305401924004140ca138a403801560300c1040200c00100e1849440b21064000e4060368000c0407452048086120032071000044601c100d42d03600c002000303103468607420322450344000c58031141c01c6145100c0005400c04980400b12216100b01800984942e040d0b0b01c2d03c0048482c0c3c1d1010560707510005c1807001f840406044540140b41180003007000c00f8070a4000f038503038980c1d2413100c4000c41d804502c00b1a0280140302c85403030f0b1640002911a096114500a040c0e00c200c680b80c100c141c4130313040c00450074003080a075030400e80700e0041c40c080480c000303210204003400040003540e82407800d803401100482c11014108001d00b0751521603014016400000034a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 567387437 1250 567386187 567386191
    0x3051305030c1008070c121214011a0d090b01060809160f05010e0307030611070b010f050105030c25150e060c19110619060504020a0f050901090e09070608 68
    0x201c2034001004401083d90f4210b90020a880f03582064221a07603601403d42d05c10200040203400c0d0b504544007251421380c095151080d40120500030028140c41d1a40b031200308209008170f9602e1100619804110320107100940390000100f100400e0540300784c1c1d02e5440007413080e4015008120504180b00500d2024030207842c180e07a4040f020301006142400045d2007000a10695052103500b130310803421034500b88500c0e03001e190000130604c641006e040d94000346a2040209590066014001040e805403011031201262016034940b13042d0748660440c0c0c4100e610007541d6030507000f6a411825018a400361050346400e001d50004e286209051801c501030f02c81071030b0fa0401c15001042041760380c03824030045d51600480754415000d90340203170000b528403030b82486c0c1c07082461050000300000841c142c000d00c254807481290503c04240e0f15000c1c40144e02070003c007903022841c0740e141080f2141c030540c05848a25014500845a5a81da5483c0c9041120035107040c055500011000d01045400005082d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 567388687 1250 567387437 567387439
    0x90b041a01090501140409090b070206010611060c180306041a130f080d0914100606090b03130203100e330f04050705040c020a0c090c0e0909031603051305 68
    0x98900401480002c0010100d4010326040c0319142d048580c0d000b02c04c4041d43d014202c40201000025011b08207002800c00442e9440b00510461001045892240b242c00e640002e00302c0040c9010780300d0b945107515a41110400c8040ca524074900401156001c04c030640c05640203038021040d01300c802601c070301c11003001040025100e200903081c20015064404029140e50010304654451500303000c0e460180c036031454090b00074000e58064040c94440842c51500d152a021010020981d4489090781c903081980708034887d00c10184000703121003c2483e0b4820032284001c090311806005002c540c0c08481e001f441020281d0300040c3d2482c04244802c018001c80c0054070000b1100d0942d8130001a000c050041007107140d03c11010214040050400001c8083e0400a009102825031264000c0d07446802200540380140b030503800240d82070092258002c10003066075080141040d64040c0310000d4005005500227100c10004007000340c1603484000c1840344207980b4555214240c59580c02a482a50070007 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 567389937 1250 567388687 567388721
    0x2306040b031b1e1b010e160f1a090a0503030f041809020f0112090b040809010305100803030a0b030304050303040b0c06010e0f0f040303090c06260606040303081f090b04 74
    0xc001da103d080340d1042403103a00403083c40d0356684501d20070070b031051400016200d41d030a01c607404250960101d800c000c0b401c1c01c9011030780981c0d611003003004030440b5885081c00003c04030324020f5204040c400208040c14018245840c2140d03900040391a543c40320618403528800482d0501c000248500340030018400d0324018050000f09800240c03d41801003030480c1803027004240341c0c4180c813807500021001038008005128619190802d154650720403030045000a00e000001510103084010000070f50704110300a50450ba00c0f002584010401010010381c1444140301c001100da0f02000100003501c000b4802c141c4800c0d98408081c0b805006800985d05521980104480501c450f25429880800e13401540300c0b54031f40b03040503070080240c0a00270300440000140802e15981242010b040180d070a03034900e1606030801f0003281d601100351699588001c0800c81000840d02c035243c903a0304501005000d010002601480c0b94000003c3e0740444101c030b03100d00c6481d6203441d0a106110856003c1102 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 567391187 1250 567389937 567389947
    0x1506030e0c101106010605030403080a05100501050c07080f0a050706090e04080d0204050d030816030905120a090e190507050a0509040c14070b01210308012306040b031b 74
    0x680d81c603003800303403800360207030300480e062591043c031681d000c155018050301079500c2540c6a480c000d02e164011601034010035449808a120b06400c0d100c0e003841030410ba17110400d0903080200442d07843e031215004450324031500760045080c0301c050000c2c2642e100000d0040022511900d819401c00050b580704005102400e40100b0203400400748a40e40654802c2c2915604e0300c041400c1c0c4000d01554000c181c0052041c9840d004143d005070700640a9805944e51503403200c0034110072001c1d10141100208950040171010920311055409002d90402d03605022072000d44410f46512805000c40d805034210056880c1a48511000d206560f0007014500e040d40c640720312510b0240c41c5120f080707003040c00303a5a07070200107140380e03c51900401039402c0301000c3d40e03944840c0d0500c1c022088081c021001c41822a4041b098131006140c140d1016035803680b1001c0340c0c2d84c0b902456030602c0503a16076800207403081c804000d02ca0b5076001c000303102601c0135034540e50300c0e821303d00c4140b8204220303080e4000c803065042003 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 567392437 1250 567391187 567391211
    0x50901060503160e0a030c030f0311010203010b0d0b0307120c030606081507390b010e01030201080408070c0f0902030405060a050723040e090304030b0a0209010813020d0b0406150603 80
    0x401544480b0241440c09000f5032040105c0c1141082d5800030701041c0d8031120110400a840343d1803801c070b5029689100c01d55611007180d03800c0744403e2003004031901003040b100ea080f034415080fa1034107000050541d090280d44140c2402509119a011211311000184c2441004800d01c20500070b00514001402c0c0e0240e81c1424441981c400f40894061000e603c00c0c25000021000d070f401c100913030209402d800418000007805142045640446215051000129041e0238015002d030407030303805a45d44c54450302c4079290750040790701001040e40d2112808102103036003030244400100600013010016541d1506082040c18050081d18615455083c04180200b0a44c4001000d04040701d03103070f2030301c10842c1c4012076082d50301c01c0303500c030312911509030081100d031200100140c000c880c06003440070040d039a20303038107e0200e102d0460031030302294070440818803e5003031403400000385101034540414034a40d511000003450088404407840c44e00c1d00c1c00f0301119002d901824000f4200360900b400076880c3c0d01 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 567393687 1250 567392437 567392461
    0x2c040f0c110f0f0d0c151508151e04080409061d070201140a1a0a1e1e15110109060b010212070c03141603030c03020c150313061e06050901060503 64
    0x20310310108a4561030203014014075240c1b034402e001058004110010f84074028440d5041e807482a20190b000b50303c120f4039409280342c03642c0e09c101d90b40708a000714404900d08041050700068025100c1d011b041c040400e40e9800d520030170000e040107201c5140301e0884403444e1144128010300090840e414640050100041c0c481c1064100820040200d584a10740d80c1e61078000b641885c44c1030b440581c903080014000320005801c8044c00001000b00b44003a101e400d00d411003226440c0410a00081540421020f01010030000b103440d60b5141c801800c1400302c000303c0c2074405140c8240c854a40d603144c151141c1d0780400074036400f00c0ac4c0c008414101509038a800760358600300c0c40003500c4510700054554602c0010b00030301ca090086405c0343c000581d01e0303003001001e0100b4414110054070a440c0c50300c0f01481c1c64600e000c0c0000c0004805443c6036209180603015030b40d801c00c1160100c0d1035030034540701c5042000c1a210702c4452244000350480c81c24041140380c59040e404042802400c00078006001110 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 567394937 1250 567393687 567393703
    0x203070807050411160b04080915070605160f030c020a2003060f0106050a0516020d03020f0615130b030c0604090b03100504020a15090b1c0c2c040f0c110f0f 69
    0x1b0302030010b07a140d0801c03030060720176444a545e0201e0303180e60400b450403074880a4207046c0c0c0186000c200139074810300c0f0703c5012038620700e000d0049921003800c6e0101c140300c1d8110411001c1d5620594070100c000e03a0311101600072004945211950409000d82681010091194402044401100c0e1035250600240592040e5601e41c0c04000f000205400900603901303001030150f0b40500030580394229414000c1d11403590722030448090082e100820303c400e000b0303e110081d40390700824540402100030180380c02404107419003500b5000d40d142da544030f95039003c0a00001e0041202c0441c00b00350950401d03041c99441c115004030546041300b48009038036070081a00a403014030419112022203070710240c0e9000496448201301d910300142c04029903c0d0303080c05181d03400b1020b40510104c1005c1400340e44002103003c1442003d88005180b00512202a00c48860a48003800000d41c080e4503100380000e65820345403590210390942604e1081c10780030044802d1902c0c0c1403010b07150303031613190311415155030b03403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 567396187 1250 567394937 567394943
    0x2901091a09131407030b010f0c060b0a1502070602190602072303071a0610050d110d150e040b071d060a0c020f06040b09060307020a020307080705041116 67
    0xa0300d00d03518059024104441101100500031900c1840c42d603000c0018099211142a048103682d0110300d0542c000d0048040032241619040c2d0584451242182c0c41200824265145900c030321119401d80c0700c0c20b03540d80241503441c12000321140408406490681d0039400201198045800d80002c68a800500c4c1a030b5a4010009030741c0e84d8184c104a114542070480c00c400980600500c4803248100100408080d071003800c1044420301040100c0070181400c0b5441c54110198100800c50a0711030310041103148840e100000d0b00210010701004e05400420920391090f5884080010380c040d005090301c014001030b00d000c00b0a103065580c16000d090081c1042c0248175181d03101480451b055094030502607000340c0740c0e80c2c039441e15190080c0b0030311240d4403d9019005010344016a400d110040750150343d09158541e20340302c0300a0130310445030701c01030040d001c50040300c5141c00107035000d1082500400c8040010680d16050504000845401c000b02c990606010444014051418a03a0b07001c0e01ea0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 567397437 1250 567396187 567396209
    0x206160507260307081e060306060d031e02061b0301080a14010b04022205030c010c1b05040e0303011406040e0a091a0a060810022803020c0709290109 66
    0xc202c0030145115800da499040d68807101000b0000481c0d03000d44224841c02c6880d00c546007203c410304c00441c0e0020243d414940640100c2c00007034082c101142009016482442c0c2180280c402c840803003802d5040641010050300f11405110203900c4a1581400fa000140c128910319458960346581d030300540c2000520a122442200e12030030030039030000c00320000241c001d40d0754a0407100038440e8020003c0c0c40300d41800308203602040600380000c80b002c2085041c0c5075064059480c0d126024100c403640030b202c094034181c880210b100c0d11507004040710b902c01c0c3c00c000c5440307504244146510300c444820840c05103500780005c000281001c040c1e213030030800113840000c3c100f81c1800d065010400f68407265290742c081c481407040c20044d60b88100c0c00c96640c501907030552024521824242d101d8954510f90344860704002114400103281c07250f049116608005103010400c00101e401c100d034a034001030440c1d40c0d400340f4020303040108444410031414041c1502840d0701420019200012500030030707403040 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 567398687 1250 567397437 567397463
    0x9010e0a1b0f09090b1605090607050a0219050907050702010f0e0d120e130608030301060e060c06040b010e070503070207180b0d08090a1e0506070f0209090d0206160507 74
    0x1c0050707021401410b420301c201002e09882d00590700c00740c000d88104948080000b0000f803c0c41c00c6041c648024003404c0c0ea00c4501e098103100805c6181e4024a01c1070321540660080380006984503418614036507100041504164680410002e1000008081406001d0700300700700c00040c0c0e44842045030b903e0003810440d10803c00341010801c6902c00803001408881e400e03c40c0c800c0c1540042055000e24011142d04403012019128002a0340c241c2c41400210382c418001440030b54040c5c800341c045085c0c040d081900301042401c030545084070079035003a02c008136070400500403500881c40040c0c1c40090760420516500304214001d60b03640d028800d2000c0050217080c58110b060403038005606400000303003240705807000c9060000841c0d110500141c4542180b100000d64014241d490302121760700da180311112580b51800388091a40801c00407105486126000801a2348000f20315024020308801485050120280a8038040003c0e080940c40243c141000c410306a201c422211003903400020a0213507 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 567399937 1250 567398687 567398723
    0x50d05030d0c0c02090a141005061603020a020d1109010e0f0612120708130f050102070e0a0f02070b0703050705040828081902010b0a1a130b04060f030509010e0a 71
    0xda6803d28000f0340c025200014880500041d0b00b104500529002d00b19009031180b5107071004542241c0718083d04814240182030030160540c910541c1c55010740140c0d0995090307940080d212001a0000300c400600d0080110341c1800c0c011780150161034802c80442d00d5050013420044031120007010b0901c500f00c1e015000c10615824810006d0300501500084c2d1a95400d01c0d04e801260030158100352400060240042d864511401c80c00840340103802a181050525240c2c90640c1704c001c00d80401c00b500c92a22100640107072004011050155400d413200f82070a0340b0060a480c1c01405010820000340800d214541002c1500d07441020602c0c0110710aa4100b0f041d44d0107545070300000307003140360089082c0c5025403640d5001240760301e15500070031049919078100084074100e8015121000002d0400d501c1c17880c945070041c00c40000d40c54039415516900c410910140c0d009802841c0058441d583d1781080c0c0390036006176908128544000d00003103180c00300c8107a0700e1120440c0030740312000640780c1d0400 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 567401187 1250 567399937 567399947
    0x1120b04140703140c03010e06042f0d1101020d030b0a0b07030e0406060f090e040b0703020d0b330c060a02070f06050106020706080a18060c030212040b0907050d05030d0c 75
    0x40d135000428618040c00c02c103009071120141580c040c020350804123030031071880d004200c5a10459101a1014403500c882411400c04144070440090324030420920010030341e075401481051520401d01a400c1e40340e182c2c002410482c1c002205014941004800303001a55629550740642e130812410340d888498909049940222045840341c200d441d205006c16100d5024294072100d0380d1685480280c1f55071241e610108a40823200a0290810303030300456851f5100350020071131055220b01c041901d00340040090000359249000e00c8240304110f405504c0003118441200c030365841d0703080e903908020b9440c82040d25030710010711030b86035594002061010800340300d0b0405c103102d8022000304815a12500080d5a0302c6040c0601c1001c1608a00011083e0303000303000c0c18900d0300301c0d0031000a0203e03040d07460801400301c42490601303058081c402c00c6d030000c081c08000c0f8892401510168442e0520000c102c0c10200e050b00710300e02601000356080c020980001c00c0b1038002d04282c10001d1003000183c400c940d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 567402437 1250 567401187 567401189
    0x90f02010f02010b060f0315011b0b070e0405151005040609052e050c1603050d53060901060e130905030310050a06020a0201030e1002040b0c0601120b041407 69
    0x240c8410082084881002001c007d03501c50220100300b0401c403001c2500549040c10031499281c3ca40d00c01d000140c00096254440541000960030000100b80c85280002c1c01c0e120304580c00a01e13070014002c0021645401e0250001d0340c222401c101c1d1a00703040c107038000c00780d030801d014180c085d41890790840f510345118a112000440c0c81c0160200350034070608020300c180c0c4018542461032092071181e8102c489030714911411a94458001c00c28890004016140c01c04bc81d0003250000f0359103802c1c02200030320524980e50707006001d802000c025400080202c642d024070610690104240e00c100005078461403012030540d0094102000120034000024500000c034050011802e418860341b102004800000380d4040c00d555100030707000584510501040b03200b01d12a520060744080301c030001650081c0d10079410018404180c5004040345003074682682d000d81c1c400581201c0c001501d803501c160500003d800340c49204075114412a998a4040c51580080c1000d490305600d048185100102040710130 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 567403687 1250 567402437 567402439
    0xb1209030d09050303150906060d0e010f0c03060302031c0206071103070206070c05011d01090b130302030715080108070b1b0c040f05060a05030a02090c160c0308071104090f02010f02010b 82
    0x112a541052030f060f074598100360340c184184070054a4560191070544a02841504060150342c20300f004000036a0103484a000c01450556a901c110032001680d0b01421042c200c0303907100440d2540c80c0d84181494125408203440c98855484810740c0c005d640400c0b8690051302a11317004204003100c0e08018114490030f130000f5480400061108104030000b9141012940243c0341c4a0404208409400881c0d10441d041030010b1b0704074405100300ca84281c0604010b054850080e10341e1a100e90200e441e0a206811034458501904c1c25846500d510109031405004024050f205c261328080714002d0034050351402d110385007040380346404140000c00405588c950700900600621390303010114401010251440c1b4000c0041c5440801c850900090043c0c201d43d001d040103201e551110130f4002d4603000f040c080c040c07044004c074907000415202ca058801031401000c0413a030ba001c842c030b041d000007482486010702036820f06103800045428850310030700094082c00c02c00003072240b0607070803401403103000340c52 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 567404937 1250 567403687 567403691
    0x10090e0406050720070308130807030f02040509070f0315230103110d08160f02060406020d02160b0d050403051e090f010201020405150903030d14160503010b1209030d 73
    0x1109001d1141c0040707008520a48480316a649000c10304c0200d500c1c1901d014610b680311010030000140f10100405c00606960f0000510340c0d268003589080007250750003554110300003c0341c04254982481025040034401d0002c0c42c1c81c1e807402c1850030101c01c451201905c10300002201c00320724078003908410089803d802c17001000700c2030452441000d003402e00044e40c03840444072943e0510f080c000d441640c0980c00c600c002d41041140f41c40c0501c0030b148100c0c02c50f202d50182007174030016101c00e4050005020a40c0103480c41540a00c4028030300180f02244449400841e4820042825624101c0c0c041c0703c4000808100341c1e4450030107807014454441d00c41600900c1c2403900e104040c001015001100045410080d10010000120b00b80d014030302a01d81d0228400c0f10807030000d8a808000c111039903014040d2420100c0c201440390450710050000da00070214917003080200d40008010351f2404009040050965050000f010224024800d00142d1414aa8003240f0108010001c0e40c139100b500b8001 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 567406187 1250 567404937 567404941
    0x507020127050c0303031512010603060e0d1b081602030c1207030212011a06130909060204050f040e120c0a140f0706030603031202030411120318010315030210090e 72
    0x3034a0488041c0e00425140343c01503030018822032401101700d13800340084e000d154a0480350b0f60b041110b003101421030b0031000c1d9a600d400200190b054000c408441101c00082c000c00855490050110403030041c04282204044070908005011f21040d035012007480e0111017030344900c0e44042880c001980c5d220310f0f803202c004841044200d01c0020301d442664402e441da484166101c00c00c080c00e8a0001d2004155a03003040c188212070708101d4040d000102c524a8904200d03555442c180045945121041e5400da0300040c040c0700307d041c26070724549100412b42d02041030242c408aa0364803415214800c00c415400002c92981600080280308240c0d900300c1d41d1003001414880c281307a5206030410511b01140075400340025000d010b8429072084a03019242c0104414844d24003000951004100b12088240c031061400b458035008111a85900c181d40110f640d002c203a411403980c2e6645240150425080c0108900400c043e0b003104401c9a0313061740d2200c01c811040c2003c0e1100c4400d81c2145e1140c01400701 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 567407437 1250 567406187 567406241
    0x90301050a06151b0b070210152102030a0204020d0e030c0309010906170a02030a0e0f1005090d0e06070602040b070b070311191d0d030504152105070201 67
    0x100040449039000f007010034101d48044280c40e00d852844441d6100d00000c81214040b903000c00506a1040e070910503a200b0103112100e002c01c4654501042c0302184080000f841100d5889000c440386403004449907000301c54650019995158142c0b00a008540102c1d82d0026042250003015840c041141500c1d281d0840413a1140c0d2904920082400948000c0f00043c016000d8410092031b4100b404087c91140d5401d168000031350301c054500c400c0695210154007481c4810310100a8905200e4040c2280310303082da00200585801404840c07440d00701c420a0031800b5001031182148507000c1d0381040d01c480a90424200900403944401c4440c140003516408000c1403880b40d511900c00740c1c40c01c0144502c1072900758183d000d502e030305106e880c2d504002c2c608400d000e440311203505c0c05500c510320440c082c05004a920a24490b50440c0440c0c00400c0a000307049840c540601406000c0ca40501410000c1d0f4200700c01c10312081403401869a600003040300d081c800e40000e8920541d80c038059000c1c51000d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 567408687 1250 567407437 567407441
    0xf0e070c0804080d080406050c0301060f2715020d020613030c14011d070b090d080d0b150d0e1b010f0315030b2d0a0b03070302030f070501090b0c06010b0d02090301050a 74
    0x1035045031f40304d103444000b81c91174001c0420390341699069610440c1c8402210000da400c50900c3c0841e0700390712155190301012043c0440c03007001a000010744039000c0c000501006c1c1c0b401e0807500211055400010070805080c040d500d9a800e000c1e0545004101c580c0750342000c0809962000e0315030600e5003490380d095041400c2c15035202c00e064a4034200c8000582d03c1b17003a200c50380240c000041d400b007120f40c12a00461500405809440f00b10200002c11984070000503840c0c508038100080000c0010980c00d10f02240c5100300c0148815a4010b050045080000350740c500007031803140c0e414447c1e10700000da2500e03c00d500c0214800091030040f903070591241480c02c0c040c80101c0f80520b081000000d1000403891000301c4044140d43e8804540c059159100d050001c0c0c2080e524140c0c0500ca40e0f8000405a42d00700202d0402c003d540f00501b0342d4905200006005c0350007600100c0406504000b40c40e00010300041d0a1b044810791010251910301602c2914007902c500021282d0560a00003440070024250b = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 567409937 1250 567408687 567408691
    0x7020d0c1a090d1b1e080d0606030c020f010b0904060e100c120b01170c0a230a030b0603040c09020922050118060e04020906010309050a03030c02070f0e070c0804080d08 74
    0x1522080380082150300781c4c3c1d80d10f0000307080061038035406003840054040c0107603a0982d0148204030f03403410040a0b805220403114281c0c02000000d40701c07240b00481c1d64050107a94000715040e0000d000394130b201c601080e19440c001d08010b000c1660703091078940301300c01401403e0149410310420310400502005c0180300d01d41e484500f003401494612420402d60042503103074208903400158604607603072462004659004446500d0500030a200410b100c1c040080d980d00603c2c510f42d600e9501e400910000900312105048544c3c0181010800d001c04503c0014407a42100e19004015a840c042ca4012501041c07a424403041c00c11a454143d12007a0103030b4000505881c40d8103240d214034948418044195511031045c01b032084000070100e00513043c003071809a070089040c1000301d02546599182440e0004625065000a586e030740c036030a105a05102c034074014107000003c58011802c04120552110340a4140b40030f000900040f0700400030030209071001003603c481540e410f20b00884c0e0241400c80c003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 567411187 1250 567409937 567409963
    0x30f1815060a0e0708041211070e0108060f010b07060b1503070201020a02060703050c0d0e1615080610050a0e030a02130b0307080a0c0e0703111810020607020d0c1a09 73
    0x10154003246100409529134030034510b90f034a807407440e16140c45035003100000c1028101008546620b4401300d60040020740b009000048200c015585800301f00f5040400103015140100f80c0714004020760042901030340c0c0c1064110000103203a519010000e11542d201030445040c0100c0442000701c0c00c1e4065004d0192400f0a8007660903583d2140d5040f0100c5504442c9900c0c0c0010600204070180c2081c2e021030561200c0307504a5400c8041c070b500ca880750140316400b10300302c62801008220740c0c030780c05016036400c40e00035103480d49810018030300038140d0b000c1d0700c2280c1e0420200c0036820005031740130011000c05030b80280008030301c1c04c900d1040d440903044101310070340240310300480042d0408dc00141c0c900e10a400c1581c84008a007070401521003080054054410551250360003401001024020102001440390030220045044184111072054513218000e54210342c04001040d43c000c501c602040c40f291420000d800d034030b40303031810302416450b1010580903801800c00129040000b031805044034 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 567412437 1250 567411187 567411199
    0x30417190f080f040804060309030e0303130f0608010605070b0603011e0c03200f0a090f090c090608060a15171017060c0a050304083105060f030f181506 67
    0x20b1030b15080c00102c902540c00402e00350040104009603842070727026481172071003858a104c1c01e603030075000a40385030400c41081408450750041003000c034070072402c00c01c0140018280484150316000001d0007074054821702070055446940024882d50b001e40c00080309848080289804081880404008007803080320000801c0c44d1850340003240c0d01d020721548000301d041080c0740c5490009442080300ba00070200d041e0901000c9000030500914040e01c0c0005000140000240885511002403485096602841c2404190824456507441e0180702e51b003076451409100302c207110008800c50b1f540c00c03600b90240e1001d500740700340b02e1800d5051040c0d4040700c4031405c0100d0428070154040c0e48440c03058580b60f070343c1c0c04100029440b10380500043c5a2090040080b1410007020824a018154540050300d03041119030071501d40c2401203035480c2000d0202550b4190a044803401f001c0c2c45032101a0100810324a0f0742c8c002203440209000d075590803050001900c0c10003e4180b00080c0c1d507501586c2140c4124 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 567413687 1250 567412437 567412441
    0x10b090d05060a090c0f081e0c091807060c12030e12041403010609140a0e16030302010c020708030a02100213091b0f05070209010605031f06020a02040e030702010203030417190f08 79
    0x20040079400000e41f09503401a001d08540c0c02500d00b01000c00d540f102106000305405581690398100d0a9441030510151400002c81900201410710405400c00814441601c2020022541d400001da020710140e0800081104034050120701d0440042c01700d50a0990000e0b0100d4400b18a64881403851001da0090046a4440503040b082c1c2c1d0066280881c002180000208041c1d00c40d0010f60913001e03084140c8002c1420204400103e00c402d81050300981e448080400d2002d0341000700d14024811000507500b04100c43c01c000351649071040343d04880c00e40105401008188848511000304121076040040c03000845175245260302e1003907040c010a00c002100c012140c0508100c0301c0301d5600600c6485542e08140050716140c02c060401441e8400d041e0170400c0d02c10114400801030120f0350020070000e5110b204000507504600c1c0d4915141e0001c2c0300c55801030340c00005036900158405030300c119660200000388528002c150703a00030741007142805000265000300c091800d111466a40c000f5503 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 567414937 1250 567413687 567413699
    0x3121b0c0306070203041820030705040816050906010e1012021b060403121103010e04030c0b090c0a0b19030518010c030606080a0519050c040503072c0f010b090d05060a090c 76
    0x41d23068107107403244922440103405900300ca040c02154004071508103103040580f5981490310744091981e40c0c8180504802c0240690b141003503880383e000b0404d203842140d07035031900c010440030315100058405008203002c2420700d444068040e9445250100032004d074000c4200c80007659a402a00c045c0c0102e146440d40c4c54008a813802508440c4e000480ca0b00d203164645500e003011004024130039020010311403d03400000b19424602c80c00f81d581c1d100244180c03482c1c4070410803030010a602003443d00008000780b0340144030031400d40311540c0d190700b40001c440c0d441106254800302d501150f40c490b9440c15201080382c0d034055000e1000d0707601d90b680e56043c6940b0740040100b10ad5096600d00c044004174482202e003110b4580107658403d1140c0009070034180e403000403a02e0403055810401181c070824014071400e0111203642030900300800601480340c1480c4c241c0c0041c100d41070043c03034804000020705024a03100e420404401c40d601400b110f08616041741c0c200c0c02062055000c44454076040d90010780 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 567416187 1250 567414937 567414941
    0x503040306150f03020f04090b160801090903020601051002031b0313050d08090d0c0503031201080d090608010b0903070b0c030d1d070504050613050705130503121b0c03060702030418 80
    0x190340c06900c0c03c10040f429a001c001d101110100705d02c1d030054486808000180d0702d100001d0103420800340b2030500302c0c507005025000c40c00503045490340e140f4180001010030360000c3c0440c1150025a500720181d5403038001203045110b101000c440c00c8800c80481c80c400c600000007000005034409100440e9a129010000814a058030241102909200701c40c1545048007800c0001d61044c1e030310482990b0ba501c0800c0c115001701400030f01c1b11882000400501c10144650000d28826180c13140526042c541e0103401d400060060031011503000c84c506902d6101042000f01030042c99241580382c1c1c3c004202c01d55654001850f00e0032507420003500500740d0040d00c603c0d001d005064005405000d040805001c02420014802c941c404004442c0b450062054031807140a004c065484594400300c10903600040d40e0319611142c001d601c01c1e02c03892440350855080c0e800e0342d01c01d07140030b135029240c03030120602c1c00c0c810703030410396141c00b400050040c2c0b280c000009108540c02400e01040240700d8501c4101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 567417437 1250 567416187 567416189
    0xd0f080c0a0507140106030501060b0903060f0108030403080f0d1d15010303020615040f050703141b07061d0111040501030f05010f0b0a17040636110418050304030615 73
    0x12680601843c1c00050202c040d072014000410000103a060b5a6103485003903c1c4c0310380c0b050100301d0001440050606060204607844040e00c50740f40000c0d40351204003a501c2c0b06904c40940b00c40c07804651805810f1101c1e04881c410707100002c0c1407102d40350900c07510004200e1505c80410b0352080984400b5a04214030a060413241c05030013920280ea1089031004400e59031880d2641d1041c1c0d02c06610518480c54880d517800791565640000d03618a422100c035040d4071000d0012440300c042c1075113899100803074808540389640c2c0220701103201214038000a0003c1040e20001c003080d4204041190b0f82c0c0300c00c0c0041d104031542684d042c070003581c200010004690080c014400c41e4000700d0010b00030541c9074002000945610b01d401d14800e5a25002840700d01825501168095281e01042d800caa00c00309407500c0c01018a044c10403889480c00c0030a08012070b036a0028604840c0380a00d000c10350312603001e0920040002c86080c840d24a0749000e50f200c2c3c3c0036000890303080d40340079040044c00050304000c030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 567418687 1250 567417437 567417457
    0xa030b10021005091510050906120606060a0903060e011b0309030e060906120a0903030b0405061e0402040504090501020d0e0a0203030a0522080a020f0603130f020a0302030d0f080c 79
    0x31014489000c102d00c06000d000f41041c21070302c10030640d1098024010f4945210b250b1000c16421402d0070402000020600036084910400283d443c01060301d5000c1000c6401117012110b00d5521141d2a6090f01c1030320403903001030320440c03401d8a03c898545040d003080c410040400780f501011600c00c00e082c0c040b10b011160180c0004c0c0201410788003030401070028408403000070a028101590864240110181208c011040340d4a031030459041581601403014000011103041c0600e207000e03408a405400d600c507125030b201000781c00ba0342c50350329a54111400f808010b08140045900c50a04a0103940f00550100c5d82a10b021031240ca44000031441d141031680c000c02071407400240074401c64841d000044c0c465000d0140d1154500911000800700004000c00300140001c00118010000e4091481c944240150803c00400c20054901e00001c0d01440e40501a229a000701e8004070741004442d8200035014401d800c5603030401ca130425158076207403040395202009503032103200f2450240900da20318 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 567419937 1250 567418687 567418693
    0x1020c04110d09020415060c050d0f050d020d09050d0c0b0604050108060c070503190c02090f070206060d0f201002010902090c1b0a0b100801112d0c030a030b1002 71
    0x502c000d005400003210b0301d0000b4004501258110308440d11000350740d00c1350b40440c010600450030010300340415810140d03242491200700180c0f500180852092000d4040c00d20340c0040d0010700d00600b5401543d076190403a085480300399015401030070078101c095040c0c500d86500710000380315161a00a0b1410380d090580a4042601c4000c03044010b40c000817030071901d5000a0100819506180340700d05d6480c500780c1e8510105123403d00501503c0e0401401d01c058400041c4100031040343c0004060703401c8002a10310920740c3d00141407200f445400d446009091224024100c043c074001e090541000030b908030340036088a035454100740d080f15008a0001d4012008030700048200310b0803030240c02003d4200d40c0343c0100014407100541003000109085440c03610a03401c2c010101c6140c0401805445c0010080080c0da0441c612039645009001040402d0704a48903085070000d4440c2c0420141c0503200c0b041500c0f0300d10083c0d6183c43e6000303c030003080080d103013903c000d405141081d05810400f0076078000e = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 567421187 1250 567419937 567419947
    0x3021015171615051603030c030c02030a020d08071202030a1b110a3003050405161a0703051e0405090c071511090d0b010806100803031f051c0201020c0411 68
    0xd10420f000c0102c6600c00340402403180600062041420084082c0309550000d1a00100d15018040f10103511a0008542c000d0098241c01074002a00350741c06052424941250740d0b5503501103d401c180354401e504068008028411240e120740c1111211222048401440302c904090880750803640902da41c48590260883d000840c0034007802c09801e50031402004411000d1091041d10008000d854500082d07940f0b0802c8103214050005070b4801e4110460302d2a0b580c6407034a4240710700304580310300c0d00c0c203500022103a0805001d00102c4d604000c980c0000c0b243c3e0002000e01e0326441c2c00500ca194056403032840040e03040030a600c00c4a210783e6000114154880e10421503000034400751099400d05281008400034544c3d65080103c03440703214021401c025814422280d060000250140e070031807141240a104854002c011b0f82c0e03000e910f03121080c030740740d0000c115100380c0c03001d42c5e025a40010031101085003041d100701c406102d050007a02100d1034012140184402c80d41100224030404d6800d0203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 567422437 1250 567421187 567421199
    0x110303011a070209010e370509030405031f11121603060b0d0911030a05060c0705210408010e16060c030905120d0206010b070206070f030210151716 65
    0x46101c101140808901d0610b01254040740c410b840a0b00400503a4850100300801c01e580a0041841146080003003503c10740002d0390080e9846040314100c50311502c910000c1e0a01c0e0003001902d0090000804840c8500d40703d403190040000344031880e180302c5003082d80c800d410701c6405003241c0740d4040344032080c1140e0ba0750310010b00c10064148421300c20941ca41c4400280d203046103010707100d6aa04035100241502852604000440c4000361150081d009960504c005c500c02090b107a500c42c00f10480660f64010f2864082e08051000405090700c8a54040c9111030413000300180068910200c001c01c01c420500c4a10380d61158003400d010743e80302c5802418024035101d604a00d408503c60700b800d18081d40c0f1000010180c140c0350301d2544840d4044124003c0165040058030300401c45803100d0361800b0b000f500443c50300c1c881d5202c060000c010448008080500c01c10075071001c1c0c001080c080001524407200411212807d2180c0411000c0e42a80f9500c4d0f54400700e11911a00c1d80d114001711441d127001 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 567423687 1250 567422437 567422459
    0x30d0810170f0708010c230909091006060513090b1f1205040602090117040b0105040513051b1005040b0414060702130506043804150305060906010611030301 69
    0x2164101e074500903032941c0c000c0c2ea40200000d8000e88501c0c0004151140d400a00030002120b0030024008001960031800460310810220741001ca8140c0300300b00a40d64800e819440e10a070542c00f9500203182000c00a0104e5100000d841152a98a2640c003015902e07103108080e41d04511a40340d12408088251142d41c0c00382458450410b41030170301045410702c410302c0d403041710011241500d8050700080c003103001c1c1d0ba1007503000c2d10203510f20383c505000e810140c541c2e4209000502440f070155564030701284420302c100343c480c2c3c1415800411501e140105054400107151307850082401a00034078000b03911140a1420754080d84d0342100c40d6820300b40b4090721440d203802c0384001c0e40d4114900f04018005615485649201d1040e00600881c0500f055414003044489048030b9150180301d1301c02084034254a4410f1203c0320b840d0404542e0001e142900240c0101040c0f00351424241169a000003041130204074948650000404e444150303903a840180c4042050007080c2c0aa03400c104014400b401e2a0 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 567424937 1250 567423687 567423719
    0x1902100b040e2a0d111306080a0f02010504181a040b01140706111b0c0301020f070f022817060f071b061406121203070c081606050402030d0810 63
    0x1640b203189403c0680800300e9041400e4030010340d15108860382584071070803ca10036450b0000881010402c80345043c0c0050b8588030300090042c4048481407224040d03a10810584000d000011448a10b001d0b040c00003030001c0c09d454000c1d85010588522170003a07442c00c4d21440c1805241a12941000c848106174184254003024048482071f0303840c509958941d4070348020f03040840300004060040800c403506070345005040c10140303109a0042102c2110807040390700340d400c12540407803907405082c228030000c0c08000b01703003552145007084d24180380f070240d11b10840d070343c00c940c03079101840e10440d5144200d40c2c590340b088544518500c0000e003c500901d01c82d0081458641d00d8024101c030180c026a00e20f030546a202c5a60700001004109201e427074508600d140364003840d45802030448459400e00b01406000c0140181d00340706c5054001802e10a03582c0c111540305403a04110302c20000e01d4584074005160a071410703806845241d9215000c2e03070003055454011468032018800403464060510345504803 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 567426187 1250 567424937 567424993
    0xd08060604050f030a05030703020a0b1005180a0b09040303020414030714061e030708040c0b0a12020d091415070504080709110c0d0c12030908090f0301021902100b040e 74
    0x8036070000c80400c0040c0040c1c230013a4404d034082d081002150602400148002e4800c400f82c0c01181400c104a40d5600075145000a19800c0c07a142a658442040d0080100002d5140c000c0481001c100c00c040e4150300800c103440d0810082c0c1c0500e01c140d000d141c1d44003240d0041c01e5080405150a00940c42c144019140d24004076004451001100c005220b85403c20350707024021824100031b22040110161010700507041c800c080078101003151100a213100464544070714250380c0000c200901d0f2030036412880d45d40e900f00354040c0341844540251903684569042c5242101800004901c85a2040040380c0072106004000d0024505101c4250020190340c1e85029003d0700402c40d003848183c0c28040d120701a0180d441c5c903e010041400c3c042c1c0c00c412185411070815203171120610029841d5801d50304411800d030340303003a01280101d0120740240300b50240e402e190102080810310705613000603495003a9402d1803050151060150a1005843c012030003050560041020703110035109180ca00c00038803003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 567427437 1250 567426187 567426193
    0x10504090b031603030302070b0105060c0a03030518150a0b030105130303020c071a0a0905010521061305010e090d02011a010e04110310050301180b2a0301090b030d08060604050f03 79
    0x4015260014002400e1303204a000c290080b551005001001200350300401c0c06886a900d0150b0b03100c90a920351022500041c145960740000c602c940c030107403141074843d42c00c00040745c64550058280c10380c20001101c01510300c2d410101d80f501a8101030081c5406401004c540c00760408895030150040d4001141807141d80c40b5124000410442c101401c4010409100c4543c2da00c10111074028892200c1d038016905011041241c61081c55500e41030440c000b1070300344081e403107440f00341c001094542d4021821a6070b905005c00865441803408078140650600000c4038a2509d003c0016030a0b174502282006c03030700c514210b00d08451750081c0c0c140c03001c0401c01000040c014035441104122600240c3c2c074030040c0c05030340e00180a2801c0901c26051600045100928001c0c55590b905120302c20040107051602501c41c52250724080e03021108000310f4420307078030325180e40e12440c6c1d610040c0303051b4455074803d114132000d581086000350030040c094600900454541801c0c8003e0082c1590301d100f4440e0148 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 567428687 1250 567427437 567427453
    0x1b3302190302120d0f050603060415090819050a200303190b0d0b06100311090d05190b1005041b03150905010b031008030a09030b0711240a0605010504090b03 69
    0xc1c0040100741906805100140711603505c02c9000440303000500080c0284d12082c00e01c0003040f0300f22a0001ca10700300040120f0569124a8a1140c80c003c58030200102139190000f000c04503040350242104110b0340c2d80c1c5484a9481c5004030040c4014440d103103500390010804506c0c40c240d02c0c082c1c10309000074103c010443e90980b1f408103070030019101080c0e80e818851824041d552400b44101d1454404c10301d02401311900e1a9400300c403d12408850324452450b801c0141c0800c2028032684074508890b40c00d9031700c1012241070654440744100c9070340d641c01e07481c4100440c00c0d14080c8036070031051314a00d0140d4a0811040e105800400c282c1003455121254402e0000717504800d4024503000c0c00700c902c152a04c07410b15031100c45822440f90065409a00705125455110b6031110b860012250403071810b00b0161100ca80a0f02c2c0c2c69041c462218070342c040c80340c1da4940d16003d0b510210f0100707240505d600c9a0380c1c802c09201d08035181c500400340061000c000400c101c14840e08052603d000040c1901e07908 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 567429937 1250 567428687 567428713
    0x904020a0912030f1b0c140f0901080105060f100c0b04020a0b18130b1c03090902070305120603010b0d0206070203240a0606090f121b3302190302 64
    0x103081803200490004004d2100142d2a0340d109a4400c01c4404401d1000384d01c0000f950341e10144141c0c0c0c042d081d051245000862910b540d540e11100400740f019110400c9542c6a140c40e50180c1000c407000707402480710403040f0b009405c006041458403805569416000e807402d0340d5140e4154009482a83d00c44502c0402059207103c0d40001e141030b004c131810b1104000e10705001d0107100f40340800068460781c944030418005442c2c401a00442c103219182c444611300e55442c064945150541250324a01d1000c94840c04040d0003900034000031b49070310740443d42e03991610105400e84207214020343d0040200320130100141440400340c1041f510040542d0382c084510002998002d0988443c03010b9001504141305610029200f0b0501510562078030424450900701d003458000300c28031529030381d0151000190309020040b070004d01d9623441e2182c0c1c20f289547c0e9041542000d00240e0003240ca4440c1002413801e01120002c0000c0b03151110780103003020004a51b0314102c00307640b2035010380541c01528805a82 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 567431187 1250 567429937 567429959
    0x10020a02030f1e0d09060f0c080d0e190818060d14010e0a09081204080720041104080d0f0207030b0405070f2111060d090605041a010b0904020a09 64
    0xc440000006107000e043e22007602c0701407108105294016005900f40b100724a5000450a090b5280f90500c0c06161083c09011610038040c148041c0c410240860003c00105061300200015027041c0c1c1202d0f22150042cac40101180b010103401896040c0070020359404110700d070300c400100d45e4020a0607042c00d500ca0880402d60b030340b035001020508503080c014050400071607056900407011110400c1001a40c0c1e490515a204c4c83e10708000d800c10102c0040c0804c8080011106490380c024a2204080c40300221810b050030340b08a241d110314104500001c50303060382c0c000d07074040303a121030010840c4007000e210030b4400b9101078070410114041c02d0380101c003145280c0c0781240034078032840c01024a80e150141d522103020941d0425540080c14600c0718803c85008004200d80d580c0156107030704500219000603029203d50543d15032064202981b280900855030711181c4070700e0190103c80d04842c444d4541c3c000c40007090007507480d41d16051000310b5160a0030380c00341c40c09408504020054644416501d02e03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 567432437 1250 567431187 567431203
    0x4110d110c06070c08040e2205010e010c0216050d0201090e1e06062820011a060304030512060301060b12070f08070e121005010b040602070605040e0610020a0203 71
    0x20540d100041900200c0810010943d22510310300e0410318004280d641c68519205170700c0ba00520501da50049400d03c44400744140080d031000c02a082540c1c61b03460018040c0074182c00d1909954a070103050b80207980042055628080d170400514107060070103042100403c08400c05074104001c3c200007040d140140803109004075010350302d4031540480d01440c0180020001d00990081000307004205001e400c00c40b1400c90a03e070b01180507694400860b0894261a0701d041031403950704600d203031605030001944071b1480c56000034601c2d404810030b01d050010a21090720018002030301001640301241d900700c002c94115000400120364560703128403041064002d80200b80c0312850030401d0140c0c2d240c109aa501e404081d5040640300d502d00000c015110060b4014914001c0d86003c488090829003404180300d07101105074100850358680c22070742d009820500444016104440c00860003602a10944003154040310324516103644100c05c1c0301c403940703071148a2019407040b1400310005a0b41030040314 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 567433687 1250 567432437 567432461
    0x712050a0c14210c042f2506110316090e1b1c1b110606030606040b040b10050307020706050306031f180308090c0f090a0207020a08030739030204110d 66
    0x7501d082c0d484141c80d507101203403188610003031070800801d49011880307209100e072030301450842001c203101c2c0e041004c040c01d02711b40d01d00c4070100000f0801450a540b007900c4285035400c1ea540c3c050854507000000c05024041d00c100e403000c901041c4a0340101250380c01410b034000708684500405a2401c10101134800420302501d4240b540c03401074a44d40d92200314003103500c4004005085500780200465241c2c1c4001d1300040c040d07601c2c4d031040c030420f8580da004500d01300710290000c410300702d614800400a4200742d6213400103000b1a20009034042c403940a49004100080107030042d145988008000c0300c54410541d218140c9488050442d040e42c0703401c0300c2a5134001d0b11902054a090340c02c44e414005ca10244c217205006504d1074450540ba9506c00e43c3c3d010703114420069035000240002206104140d000880c0c0307200014008040003201507400c84010140c0307001e69182d41c944502ca9680e01c000329008821641d40c603200b0800751525800024031481d50250041c90481c8421030541501c0401c0c601c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 567434937 1250 567433687 567433721
    0x8040f030606060e0303090d020402180a0e041a1b0306010c120309060c02030c0c0d020a120f200102030a12180501061a090a03140712050a0c14210c04 66
    0x4101e000e80122801310210b8040307020318a4a1940c40004080c10f00440340a40200d601144000440c1d9210355509101113000b0b001c0ca035601d585450001810b541114119105607503040340b00d030801001c0100e035000b080f03203610300c21849181d011100381d070f504012b00e141c0c100b08201d2402008a0300144c0b940c4c50a01e07541d580801c844440342003d500f90f81c441080032003194006c00071500307442008a400e000069044035102c01c582c0301da000041000c817031030b0032000380801c01034241d5040200c0000880c00180c45000e070141304040b049403217840c0402c05485103001d60404c00440c1e4041348500004010ba10614070f00049030400c085241d5008a56000c0c12a0a40c0d5144030501403800e21000451880e0303003079607a151529090401040e000304580c03000400c91100a08400d02000042c00808090b045658007502140d0040c18400da552051250981e40800ca45c03801103017030b0305040b6a40c618114003404004681d0804649042a00f00100d0a404d0b14020440e08141641d41d0380144100d0144003048 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 567436187 1250 567434937 567434939
    0xe040203130b01080730080c060a0e0307030906030507020703050f0c04111305100302040b030c120703050603030f18062a01050601120b040216200f030c090408040f030606 75
    0x100b2803503501d044c0c101102650100e85c04001c040520000244920301c07200035050000c000b5800300d2140c901d18100100305039808211250001c00014040e0703c10707402c0f41014003080b0032803840c0e581c032842007810280002d40205070910005d4001e82015800c203100388111a4403580d00c1d20b800e0304241080c42d24010980107951150103525090180e00c030344d00703014485030380360442c00c1c20025244c1c01180b04442c0101e1002d54102950303400796050306c004080c8603c50340e58918042c0e040030b0b0160f025040b0407510340e0f6a82c0c0425481c2d44039124a0f4072030000a4000d5140240200404006400c1011003410032409a4080d26103a00e07040064043c104c051184502d2991100b603284030304a0070114036003031a81c90703c420400b043e03a000101e41ca52508030000014411181c4002c10042d21414407078098408002c0d03610400c01019000c60034803e400e40940d86000c200040820a0941301810041e9040d809030510307005515204420a410078401d40449140540d6604800420b11107940f05076141503862070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 567437437 1250 567436187 567436193
    0x31220011a0a08072c070c12030506030a06110d021804061203080123090411010206010b040b040b1b060703050601091502060a0f0b060c070f0b0918070e04020313 71
    0x1100e070808032002c0b0744010400d820721803220b41d1245070b845003040080a00e01d95503200c0081c00c411a110f441c40c2d400c143c08501e07020001500b400d84015040719003a0107041e040418500c45e00ca86402400300401800342d00701e00b500c5180c0074010ba03000403954400f0803c2045c020380841d2004003200d11100d806503c1074028001040b040350040e500c010843d014807034030000002d512500c4941901c400702101c0b0366000074422882c00d103600e081001a080500ca0301030105105500811003c00c1000b44d080360081d0780c0f2821f20070100d0140c4d2240c0300c242103042c0401e001071000c44000e80038015842c0f180d83c8404c04182840b40c0f07004401d0321040c0c0482e0782d9105000d00384d640051040302030310002c0c0c688600703801c694100a5130340500400c090360f183d41c0c5803521142c101070f03a0032442c3c0f10344000380807903251a5607444840d1a0354907482000d040d01d001120011312401000c003a90213001c0c0050850b4049040421030032407942d001070144040050b405002841075071144081e5024400c21102a010f54941d46 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 567438687 1250 567437437 567437471
    0x20d06090f0b031c020106151101050106021c050f130b0c01060918080d060b1309051b090d0c05090a02040e061e1903140d020715020703122001 63
    0x20080c1c00d80d00d0909005031401d07100040d08403466050120341c0c80300450945004c0303006000b290800742c02c03501080c18a15106900801101c1c1c4042404001c01141c0d984400a84e40c4101074a84116050a041c03090100076006c2d6010300304507200401c400d85012142e4100060122290300720915910003c510b108205009100c1e00010b05501001042501c0c00c03080302c1e0300c8038040020020860400026144581f4409800010081c0344090383703181c664544a1040020031114040c0000d4107107482c0000b282c102130ba23941014406000340710b081c03600b034803c818000044040c280584203c0c0c3d082500003a20b13280c4440031485005d6000c00113032070318200342c012400c8100203003d4501c2076079910f4030721303040c0074001d40100718010003200c08803041c0010711840c2c40030803181c0c2c2c0050503e8441d9042d80c4e840903400b00d12019100e1045d4240ca1080e62601802d0b0800294240c00d03000503444a901070001818020b4021070a00340ca00701400300c64015402d48000c5046aa4409041e944031407403000b014102c1c0d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 567439937 1250 567438687 567438701
    0x30c03090709090312020c0a0203063d03060e031207020a0c050108190e010608030d090227070806010e03100903030b120a06051e0109060303080a020708030a0f0b0301020d0609 77
    0x30042070103050f1103920010710160b40c0940c0d44c0c428990005100400c1c0300c00f0401070700803690240c1555054600002c43c1507098441254000110000e0303220381080310318040f1521071810460745844103ca085482c0d003801804261001505448200260b40200800c02100d0f8480c843d15070051400400074588112064030652206050001c2401030007040e12801e1608030480110001c00900422000011400f402071039203c0b208500001564452034034640d001010203e0007034603240301c01e40019000c0107440083c00f558080b00403142004c03612880c4140c1441d6000700f01450021403450202001904161040c55030524056444464000f00341d0540588946003008980c0c496600c0d000c480100c0d1a9201008020302266941d400103120b60400304850712450105142940d040d0f840c1c1c9000300060200b4001500800c2858002440210301c8c3d0003221841d0b41e01c10300d02400c0da00c54004000c040c011440307103403540d192500340103009500d00344050484010305000c00f080b050b180a096604032114 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 567441187 1250 567439937 567439949
    0x18150e0115080a1704180b060d09031e091d04030c0b0a0203040506070f020d0c02030304030f08130b030c0a0e18070e0f190e0712020f0403060f0510120302070902030c030907 76
    0xc1030104000d803c115401c03d1006c842030312800314145041c5e0000955a1151956500c00c2a250544000a042c0d000010401c1d4114040782c131000a03c52080640c1d10020713510891880300000485900901300000d04690414464148043c848000360784011625900f01d03125002c00340c2c04003c0005000b41000003036040541800c005102d504162030080d2540c1c011070450b0144184142880210345040048800541d041418640503106038a000035540d8050440c245d10b0704a040000708241b02c24000700c9000c0c544001d00b484c50040d0140c0c0940311182c2c078000d55a80004d103101d078a00360340030300c400d101d1181c0b07c0d035650030758038410b0b0b4010000d2519280000034000c03a582100000c01901828044d01900c0d10840d040a15a650304c60803659070f2400e4440c03920040c0042501614000c1e05c2024000340ca114100a0000110048420080720002c48186408040040081000c04810100489454003c0c8181c2c0c1005e503c8203107201c2070341c1c1b01390b982d91030304100002040b814010621250000c1c3c05 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 567442437 1250 567441187 567441233
    0x5090c0c0304051e1f0806060a0e1005090306070206060f1e121c08010806040320120d240b0903161202030f03030709090b130c090918150e0115080a 65
    0x3840100040c181070b0010300350748c0942d00010325031880c24050b072982d808210f0010311494110070300d56002030064102e1a44c0600a20a45000c01c54040c0089601807044002504840030b1000701007c0002c208400c506d000003851800740d0032043c64441550b031406e0701c500d04004000034103958200807207100303080e850300c0700b040254401800b6801000c61350304d802035014944205007480441c0b076034160650700f5920007403600c1150a44805d030b0038203101030b02543c0d05100b410000100c07145458100020b50064181900c52082000c0c1300041c09800904240340000c1c00701d58402d80401742c0784254030642c3e0800d1009910008404e011490b0401c0802d40a1801001039419070404103c0a0101301003406034403600b03521910388100c1d548aa1586000d0600000f100b88070038101d07038001901d0741380e4034019a0000c0c0e042410903446541080244140140d00c580701a4030501990009001403a0742c00502540e13540326601d00650f400000d520381c01820000d00503000704041c03132810300c0601d80070401c4100e0b480 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 567443687 1250 567442437 567442489
    0x110301021206300d0806060708090d2f09011208040911070b0109050a0501090e030a080c120c190206060904080d09050607020c041505090c0c0304051e 66
    0x8012088655002a02aa42c0340c00b00360a550300c00e502044602110010103d00f41040712211000140d6400c0420300f0b42c80d000c403d91510404c0c40f81e07900ca50301c400b40514400300729041032400e0130042c00301000d00560400c4951802c1110140c0300a220301c00018000e10b80e041c200416152122110340140091000a4420b103a990703501091801940300e08440290b84000c1c004c1005a803000312405142e010710000d4040d030712200a10024038041d100444441d107408008108000c40340f240f07150240c0094025030922a4041c01100c3d8100020442100c0a4081c020102d1000248000c24002c0f080240785c1d5031102c580ca10f000700d40e01c074103007115406c561120341805034545a6043c501c0c0c010350000384558bd0f4108529945c2d0282c5040c0318018502c1c486d002c1086242c03940032940b41849681194288a01d841421001c0b1056490b4010554070000c01804560180f480710001d180c0d6841c4001603d003420b60b6903000500761b5440b100d45c0045103588424625a52900011074581e521007081c1c061010 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 567444937 1250 567443687 567443707
    0x608090d0806090a180c0e070c0302060a0b03190b0106170412050a02160e330904150603030f030e030a080f060a210b0117060a0902220911030102 64
    0x401c405044940501e80e420040b521181d00c64201e01c5402c01e802440e410916400d1400c80741d0b0282c144640089002c013040403a601e40c1c4075055100c215130b090b90082100d40c489204442c006d140034800190300d131048440048200301a544500e010700d0090102c032000758909034001d00711112510003003054114130400c0000140301454804e40c0000c0d03920305681c0b1400041e0f010381c42c24089900c005e005090342d0200140035512245810704c01c0f8800000c0849000d510350b44030017015098078a0205501d40f1105038501e60821100c41f1b03074068040e54800c46004141c0744610100d032420742080d8001940c440c90024003942501400c40c900522800540ca011601e00004012000103883c18507803403803001c0850001ea841c1000200500b03240d4800e103000d000b190344400e03000040884101c0d01391400600024130040400010030f420504540904100d42d501160315006002080080382c2c0010b42c0c0c510104400fa0702e80320101944a034120004801034503080a100b1502c4541006201e80c1c0104443c583d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 567446043 1106 567444937 567444947
    0x2090412030b040b1309020604050a030804090b10020a0f060f020c0105010801240b160602030a020a090f060e0105031b07080d06120b01120309051005040608090d 71
    0x12500203401480140c03134103510324a0348503001780c0d4503402054298010b001006d00c0100414030300707603c03800051503103d030702d4005958a5401003824094064648038000140d94121002d264600c1400c42c003d544840750f2500400f01c2410b02c1c19042004078980181200c941900001d64894001c440c440c2d008003800d2180300307140c0d0b0a10015031020680a801841c07182c2641500c2c180a41c00d160b60702c00c0503403000e42980c5116450141c1c24010800a102a5000300344154015940d01072409009000c09a50b401ca95100107054004206141d0403c1c0040c140c1d860078280b850300c2c1d69604c3c5104071203028914000311003101c0041d94004100d070110051403a15420501003209036210140200d01c1c49800300010800240301d40140104010748045915040c800d180c14080c140e00d4401241c0000c0d1017294840114002007814841e55400442c00c6a001c4082001002030910841f40244 = true := by decide +kernel

theorem cover : BRFrame.Cov 567266187 567446043 := by
  have h0 := BRFrame.cov_init 567266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 567266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 567266187 ≤ n) (h2 : n < 567446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
