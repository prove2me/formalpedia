-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4536
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:55:59.574918+00:00
-- url     : https://prove2.me/submissions/9926df48-1922-4e8a-b8fb-64af684c6267

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 815647482 ≤ n < 815827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 815648732 1250 815647482 815647493
    0x10b0a031236170304050904150203130b070e01080c0304050c0d0302030d15140f0109090f1a0d0302150705070f030c020301110c03091c120908070501050415080603010e011817090607 80
    0x30050030032512740894100c03100c0da60145001841c80b402052030311b03402c210b00c036040004103820300400c032034100128400c006200d60b8112070169044007280d0003d80c0c42e66900c1c94041e14207240038100540c000580e039181c9040542c00001010002c698410600c10101d44601c600100c9680340900b005041241c0000c03412030030031b41ca0700c40e55000149000110303607960b0140c4004580c424041c4000f89174558141c114400390b0b21846070300d9903030244e808010504280d140203413a0702c4803141c14610402045c0c040f40b0850b05c64003c0c1e83c0c00581180b0700001c8c0100e00d10b400f410442c1c2e204001c03400703542800c21130098584424151000e4080c3c40000e1031034104c4040812080a048045144462300386030808030106030040e02c41200c0708050749a54244031306094905240c40d449501240c1004020401071101c00d1f0840b0480e9460900360030310050740e460710300000b070140c504030040d10b01070741c60031980d0a00441186109520107000720400100e0151000b0910080d2140303a101c00e4210310300f0080000001d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 815649982 1250 815648732 815648749
    0x4050d080a020c2106130302060f070c05061303020609060601050405040c05070c03050c12011b1b02030a062c06040b190207080901080702010b0a03123617030405 71
    0x1451050b02c0c5110b81041c0080e019084120300e0803040c10304c000c04088a050200305107500400030f08800740400707826580003542d4000003800c01100303004032408550a07900520100d45800c1e4400103031002c91814907018198509100703000e400502c603a8002c600840c41c00b2a10368040c50060795494a45401c00040c00003601004144404212080007620b011a4400b84441c000e540b003400500b007d0703158482000310101042900030724503450070000185103c05040c1090748a01300d400c089034646101144000d800b0308490010b90103020314a41c810404c0b00030340c00320003464540000c2014540010007040228100ba5620440c40d610000c040380216020500b50356003d462001984160603174440700e182660450501242c0180d000f080b804d00c01d681000c1c886601040d030384002c01a5907600e10024501c0c3c0701511018060b00d40500c090b00515205101c09044403c10751005801d1000048000c0c450166050b041071200016043c04210000c80e100c040c05500040001142018105000c00c030460 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 815651232 1250 815649982 815649997
    0x603120a050c010e0c04140c0913020c010e07060f2c03030f0a0903060605060930030406020705090901020a02070603020d0b0a0806061e010f1809090b04060f0204050d08 74
    0xc1018080c0b0040100b0900805041d41c2684000c0c1116220000030703c42619034031f0340522148444102003061a000d0b80c81650070303044c4200c40050011143c0c545440003445400d034915625404c0401600b454080007034007100700d880640d12348517071001885007210308054002090b280402418000e1006144121301c010f840400181901d1400007000c074914456030020310b94001080341207504209009091041c0d0f4010038050310520b04d05014600001d00c0b01e04c080c910f11a2110010004400281c03003c0c801803120078500c003c0340d80d19030300c0305006585d8100c00e1180303a2040078284000707076034403006000b0717a103030181c079a00140005410242d080e07002c1d40140350f0003951655506c0c00e029080d541c0741f44103002011718502801482c02c1035028026180d140f03041a008605e00460b1500191368060102c0c0c504001c1450210001820440c48041c00182c562080c0c61490400203840c0c00d1064103000140628460700b02000622508004a41a03010318031415a100700d40b4003030440450034072001400030 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 815652482 1250 815651232 815651237
    0x3010e0d081f120b130f1509020604080c0901150519120911011b0803060609010c0210170906010e040b0c1c0c030b060301211406040803060406050103050603120a 71
    0x110014150b68800d490529807046881d03c03e282000401d1154039000c0c4c0d6084952030300801c1e00c10300d190711122140d25503214014156240c21254030b01c410483d83c003030144107a0081c00a035039155101900c9960f160703d00280c0e80b05a00703160000600f50354880a04003100420340306e450421a850a1081d204000480007100b84a507640d040025081c9501c10000b00c01c0c8604480544803181b1000180315405180c800c501080c10b9461030008542d130340e001ea03035025034112641642e40c95030b0380040700d0004101c0700094102c070311a0914822241c2025100b00e0300e10320760210940b15944c2d6040d031641e80c082841a00b81c046c0b02000071802080a128a059000c011103812500c1d001306401611110071140840b0742c103490307440b52408003480d4140100440c12a00701d45460442d4181380101d803090182c100400f88d5420354004240130402c8170300c85010400c00038000d0b64494a02814400469402101c0c071903c541d1510101182941c000e1241e1402840050000c02c071411003500f40d00c4499012141030700a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 815653732 1250 815652482 815652511
    0x605102105040311060a0f0c020604032321090607090e0c030402041113050f040207080313031e02010b010306050405010b0703030c0e100e030d050408100b0a0e010e0f010503010e0d08 80
    0x4191404010080c00b41644078400100c07c074140160100310b03040341c20f9101c11500024240800f003603012050108084405800006503e01e00310400103d21400010700c10056040d1520740c40e404002004611800b088015a44659540d075000c03100380c4024011440414400008160200301800c003a6501900c0038000240c1103640a40c005044c0d0803242825030300c420150300511036810f00d54503072100100161030079805c01c9450350b2408413601005024003000314060200b141030502c01c0c1051041160740013a005041d01669100038003918640c0c82290100b8100900010b082c200307881054100c4494408150a00003140d9040307000e0008403460404220380c0e109034402a546071042a0489000ca466000342100c480062506103c44840480c05219041c04100308944000c20503014100c1e03a00d100040084034100007400b41e1000f50040c0c00c00d070381c0f0b50b0000701d1034050300644280540e4000c90301110b180c0c0d0301c1d800c1600b0307240b5003100b41c0c415800100c05000a240103407580b07a00108101ca00300b5 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 815654982 1250 815653732 815653757
    0x30309020a08030901020d0f1b05030f0301032a0f150e030313240e0121020d020c0f0c0f040b0f132f070b090102130906051021050403 59
    0x41c0d614400b904882900e8200180c903400c10360301041008420852030500c05481c04034a40054208003200018181c0740d00c0800d403503410004140200d58a402e000b598042c1c8950b141d04003030201c03500b4141017081c81d1120b4000d210510b40507c2c0f461040321404c01c000c0300c1d0349081c8044200c0c03611110f4141d40520414040d250216a070602c05480c00301c01c0013100310120342c545902c890004d150801840d10001c1e00c916903922541d4000700021000c0c2003030805c5448500000c2926038988003810b00c401066101050441c0c4800b00c6030001c01c24200e070142110b00c5001c52441070b075141c0c84040e0741941e000811210541d140c1c1003a800014840d2402040c507403411109801007039201c4c0303904040e0311070281d84886607035520705440d60004102d51005219107440c2400826014107201c0e0003001f8004400c0d10300081e003030041c250103c4000c0d021040b0340d90042d41c2e40307581102c0039007441d000f940d10500b2400e018451242c4142c100001407039610402510310001c0780d60b66001410301402c144c0c100aa034030820b0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 815656232 1250 815654982 815654989
    0x50a1106280219020f07170c090711030a0206011d0721020705030310030b1b09011206050d0b060102014a032d030705090427050a050c0f130903030902 66
    0x109032069070b005051702c80c9054074564103104007904695401e4412140503485180d0024060303107000800c0d1041f4003103844e400c00948120400d001c001c23003184000211032a885502068290482d00c0030940c02e4226036441d01110301b0b03650202c50f02c03400100014060082001c03800059244181405c0c0014500105616041d0941d44120745101d113048071040c0c200100b14801c040d46900111040ba900e224404444040070b00380b1440743d549040020703d080c052608040c0390b000c180104401450380c50b00345420f05d03028600d00720403110180594a415040070300a10040c2d041c02040c000300300c0c003000340381c0c0b401544000448503101e040c01640318000b00c5440044100010520300380007408210340c032410415034005116a40b000603510030b0040c82804400354114058400d0f0030300441d8007054070b1503a080d00c0a011141900d10075400d0110b4000c0609010340401d400700e8603030051040c0d070001c20a620502400502200b46550800c1000c440c81c888d1801c00e5100c1c240451007850081008060358000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 815657482 1250 815656232 815656267
    0xa1514010504050f0a15230a15080103110f0a15030c020105152103040f032108010306051b180111011505090411030106230306041511070b0403050a11062802 69
    0x80320300000400505154501c0d00310910b23402000d46550f0400e000c040004018203011040c0710041c825441c034007200304150341d098613010100502910900b840381ea56490420580c48014003200440d01d4500e40f29030b0710b8818002c40e441202d5010450301c3e001110300910580c1c0c1984101d0f42050b1400e08403010005209000030f00050112001e4051031034254244203c01c00e10b407002054a440518481500080e0040c0c0300a04403070b0000d100054994072441d4104180003d0100610325030000940c1d03140024000c480c040003200b082e40c900e510034010303950703803400c84101c08400c202e030807517100e0108868541202803982c028415107000403c0c900560103c0d09484058001d028281c0602e400c00c2501849030240084c00c0908034024501c3e800d00c1d4403420000200c040c005c0d6105621500c4024007142c2480c02c071500640d00000090880c5081e0a00405a401c0392007290000340a054060911140c00107800c0d01411400e40c1c610102d200b80d0b661103010301e1302c44508140c01c9030203104100d800030364002c2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 815658732 1250 815657482 815657519
    0x3071809020a1e06030912050703020a02120304091109150c07090e03030103150203150103022d1210150c0c05092505041a0306030a1514010504050f0a15 67
    0x20f080c2c02604058107070700300e601203d0304801c04051410403c0c1c004910500c00a20050700d0605000d40ea86800b410100c0c200b400c481c0303010b0b401c00e0a1100c41c40304010000001d00444030104402c2060039960b1030814907601c2141801544103403080c42911410320344800400d02101c0e02400c98901a99441094040c0c2d1084070381d40c0302a82002c40100140f041010405100c03080302c850861441c548482c4112215a06d02125410150702050191000c8540c800303002d50020161491a8008580c2c0702c06020f99120040c19141038401c1808135142403180d008000503070b00c03080b821800d0482da000d030848141c4000c0c0f80648104c01200c0002405480f07200105015280301001c42d440700c1c242c6141e50b030203c81d88030180810070404200402c041c00b510904440e2030010300c46030568980b90540081c0c81c1c91002d800103043c0004442c0c080c200f40541d41d00c25101c3d0800380c02240c0c41c0380e036100700304021074004582540d41004d004000031300d40c8105601c00d41034140c3c091015034550b0380310030798031071100a4600b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 815659982 1250 815658732 815658749
    0x6020601030201020c0105042303101503060b030d0504170304030b1f08070f09021e030903180d031b0f0506090d11030c1c030603060c0302090f0f03071809020a 70
    0x20014410b550341800401448502820090710b03040c40c0400c031056812240c421184c00c0c5074085050441e81e03406010b40c0402e10a440b206200c0c09448101d81e480d05030441c07004590080c540494441a4103000c14121035802d082e031600c900b4245061450300320300e405000080c0e1a8001000080005a001c2c0a031500074012001c01110818880c1d04003841100c141e04080e99642c0032a10030001540701c491414191050602c0150312080301c020714040c9000315449025100e9000b00c100444c52000001070202e0a901d01c81550205030b2110501a524401d0000031b8001500c032084070011840801d43c1240503403050b0441315000c08545c8a9a080c240309484c058036030b4100f0840c00844603842007201c03000d6140312015510b00140c108840b03076621034141c0b0601c1b010800d465492481400b0b90301c01d0005640082041c02902c010b0342005000350b201d0540c5034881d1300110b92410b01414031031600c2c0d07807224000c0d000b4103800c0c0c10440613154011509501200076500c4031140d00c01602e8000d6040001c11850 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 815661232 1250 815659982 815659993
    0x140909010b1804110a0c0501180b060a060e030303070311090a0b1308010e1917120f1503101e060e070806100c02010e0d121e09061e090305070602 64
    0x106420ba8840010911a0700c02d0f400d00944201034100e0b001140c0da00c0401d81420000c05032645000f40c0900380c1e001001041d418108072610034464000340d140d02c075050858206038070a494540950f008a00160740c150140c0c0188002055540a83c0c050130940c0c0004100d1810030303036024005000c001d10340d08100720300c55001c611990b403294044811400350a4402c0280b1003072000d1100181c3c1d07010640c4070043c07040c280d400c400381400080c0d03080b40c0d080e142002c2c40b60f541d43c0406070400185801035511b000c01015907000511002500e40c004c0901d403a00070060301c030100e0f03a20b08030170107402820118200404188205d02400c03156105550050240c0c0e0f00201070f40c0b4000303038042c254020080080b402111203611041c4010b42c0311220020190742401c0c4420a200c043c004100c0c8a070289100074080d650751120520059041800c0d0000d154a4201001d080c07241c02c07000b2240041c43d8400d02010910b4012410000300b01c02006440f1a00c0d41c0ca008052181c2d240c4070145040c0080c1d2143c400340c2c100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 815662482 1250 815661232 815661247
    0x806162a06050a2c061f0509010905090705120c0103150902160501050a020301030b160e2e02030405030d0302180414041a0f040f0302010b0303030a1a0409050d140909010b 75
    0x4a02c40340d40f902941060140028105058803030301d60900038403058109004005031448505183e00c0d0784003511025184480c203603103cac1c417654003c01090300e00c0501031280b1040015286000700c0c40b414120302c0c11000d440d0100f0030300c006502605006201c0c00b48000b455001041c0a800c038400750262580b5240009080074640c20982c4c04c5400203811041c62500400050010418103000140c0010380e0510b5540d0203003805ca0300321106901c00710010380c07203454100709c44003064810000121040310510340c076080e103c642c80141c2e507a01c41c0d840380c07075003642140d03109004c803038007a0f400b81140c071142c01310600c100c1c842007000400310b40c1c81c03108800030340064009201c04d00140031034204646149650084c1141000c1240810b4a80001e0000701903001c800290300825100303402070800c00d030b00501240d407030b0304103805881c01402541c034240c048518005800c00d81842c050041840003508500a0640100c1004080301d01030f0f0403510110406504010301d00c429181c82401e10b00800c1e88000c4d10381c03500c00 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 815663732 1250 815662482 815662511
    0x90306111e03010e0c07051501060e041406030d0c02181806100b04210f0804050f1509040504030c0c0915060c0203060c031b030c040806162a06050a 65
    0x4000d0a0200d01400500041c007a0071200710307407613030000360100205d0340300c000c0d62801034501004088298000f40e40c01d000001c450703400c413070815a421021038090241000055043c29102c80c11110703030f541644441c0014800d9070049407401d00d29400684031030069444520101c02107803007990481e0480c2d500140601e4010411311245030000310500c2c1d20072826181041b610380c0d0380618014041d4513000515540c00c449801181404034030f5221903440070018482c10030400c1ca400911907503005469420703407800c040c90300550040e004d421400d2202d08000f80c0005000003014020000c50501083c4014900818410010040100b20064000c503100405601c1d0395084106903204005000603c0d08010040c0c1c3c0c0816495448000101e005459503500003170700d204561001c0e403180300c180000090002d030f02d02041c0107006450748407003202e800741c581549031400d400214240100088420b012a0440350030340b07101021400c5507458000c0c000740d01780c95090840e14155008041980d032034180511010 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 815664982 1250 815663732 815663767
    0x102031303110604210306080a0f1403040b040e040201090b0c0c0a17060406110f070b01030c1e0b03070509060a08060f031b0402160503040807061202160201050304020109030611 78
    0xb640006032046084c10365940c401c00d1806042403400500411502101901c03941c4200020002d00341121b030320030740c1070a0800740201108016110b841000c13985044428000081314102d424884500386454a07000c2d0302911094040c1080307040180d00301001404520090203084100d0b1100c014084203540403041001e050407a510048402c20341d04520342c41c0d001d0210b2011fa1158001a011404000101500c0010700c61010707008288080403c0709414400c0e14440c00b410380388510034a080d155118154a404841360309000b03299020380300e10500002201e240a59000380150034043e00b00080c440001707055403c21020000054031500400540d4070300b2002c00c900d1a4401d90141c802a41c244032400c000021800955000b580c000904109420080d004100456080000d5949480e107904441c7c0e10b4059510482c0000303040000046d6202d290780c8200e8180c10784400102c41128003d50054400d500002d00c2030303041c04a00100000420403a000c0d030000000342c100c1d401c0c0c1c0c03000c0040c08032034640c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 815666232 1250 815664982 815665007
    0xf0c0607080a291c020a080a0b090109111c08031602010b0f09060d03020f0a141b01050304030f03090209040503210907420905030d0c02041d0102031303 67
    0x98403c80071000c1410307a0108030041d50320041c2c90380c450688501101212042006a00a400c01d0f003491000514500c04548810014442d01c180d02580d100c003550107090b1034003d03402601e030704200ca41d1725115182c1003005015200400c03a9207500020316480c0c1c140d0036081150103103800041c02c0c0d00558096030a101e028004041201c000704d29040b0a400b04000020040405014407003501051080c54020014200029202012180c21a4051411150840e001c900100e00d502c00c0c01c42e490f080322003040f10100b00c00c41c1a551242503907901e880454061910354180c6060540d036203400c00251725142030750b6210780d015000441c0e503800c4901c1c034050142055044584910220024070440000100344501150310001c40d10000f4404000d910511f50304d00c0c0800c440700c0d220208080e6901ca82d1594080304402ca580310300001599803020300d9140c14902c448100001e4071400c80390010b10301940301c0600032101e100304002d454007081e0741600f241d0055420400e542e0207500300a08041d440155400391 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 815667482 1250 815666232 815666261
    0x170f0d0f050f0a1d0a0507061b0f0605181903021204030803040f02040213090605030d030923070b070803190902090f1302091509010f1503020f0c0607080a 68
    0x841c0340002c0450203503200500703a20001c64950300100011641842d41c0e01007008800e06079150a03215140c402d58800c3c4174412000070034920062a284401c0c044425514560010502e030520a4107540c0c20005080050414001401c0c2410400c0840000c100c0c92045000380814100ca0101c603043c041c0c90004800000800c51070100020310000b00440292500b0036808101c100c0c0910081c070006d0701034082d60f000c2c01c042c030703400000004c1d00d05c0300c580159040302d20035020790b000080c9a5070100c066581e1850081d01f05900c130700080944141041d03a42e43c9102c0b08406035245151a00740e138460a60040304103643c0d141c00801446214181c0003440c401124507a1810008100a9408201a040c00034107288205c501c00c00014108080e081c402d0300700543c010310f0400c141c0761074031000014910a208560184039104008104d10401010f554151464602c51b58104d440d00c400c02c5000c7d602840004207125018820380b11000001c01010b0b02650072600c0d514500e143c40e08043e81100d0400201005 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 815668732 1250 815667482 815667491
    0x708010501050a1e031e0b070c0b1f05210c0a0f0303050d02041d150409020a0b133602090112051509180c030f100207170f0d0f 56
    0x2440e9568002d14088070350000315412160043e008410481142d6030001e44182060084101b2111000080360f00c000d10500840d401c607118000c0458a940b4082c03001400207104d4008680542c01e20010650426003269942e0f00303440d00c0d070b80496054101411407607a8150881c0b02c0c2d43e6511402d0200808948060300c022807428a031804094103055030344030103000c1c80000501c101c4042c60b2501114090312890b21188082c2440d00903000c4891412107810341c030304801c5414030301145041d020344030b070241d001172514020504001004078152302000000e40500400040040c8203074620500c100a070400d440600c41040140155080d080d14004414035480c1c8108123036800e580c0c000c801c2030405035080d0400500d60b90b91620820040300b20a103031590000c1c40b00200028070402501204001c100c1009640300511503900381603035200d04007002a90b6030004d50200030450395507406010728034014109900882ca1240d0b0341080c0313070700c003115070b00d903200c4001400b5008070402e0141411007441d1000400 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 815669982 1250 815668732 815668739
    0x32206050624030a0b0a122d021806010309052a0105032503020c031602120a0302100218150405010327020f0301150b0417060105030d030e010603080a020f0708010501 73
    0x5a510009010b00311907a178400350352049850384c180d0280501641c690700b034171502d4981011040c41084500b60008111241c06a1060822400d40d1a029690140c1840000403103507074000c1103088000c01007410195513040c03030b10128104000d0340540000349900d501c0c0c554020f03d00080354082c0695482d0512a0420a100f071000707019840b10741000c91140202d51170302e5000000ca010b44100240042030b40300100780381d03040580c90320302654014070845880d542400f8070354015444255684024000d60080680b690a26009030000c08403d9044501034650746080d600003040700100780c84c0c80c0c5840e000414144107950301440341205000821000b210503440c100035500c020910782000034000c000c622101c0a280c1c4094100341c9444d1007030707400d0424041d2225983e1b031407500a0320a4224803906090007d640c0c04010030381c02c0c160782010b0050b0078007509041c4103801918500c0b4040d1290b6588403c0000480c11354405001c4802c0583d000c1c0c0761580700c2c9a10a41b8101e01c94000c0002a4035000040 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 815671232 1250 815669982 815670049
    0x1103100f0f1a090f04020102100509100b1c020f06090402070c1a0414060c150130050a0f080d1802041a010905010f05040b0313031b020a0302060322060506 68
    0x441e400040b1200483d0b140ea05c2d40300403410319a08440c41c032105401c02040c0501000085903140141042c644e04001d214413410030840c07048840d00c460f004c24142c184850700941441040c8144503000075011a1400388070ba4042030880e804141c0544450911000900a0110588003100f80c2c02c80310b01b03602c0c00e0a0601c20009d070010102d10206118200000e10311008500c140949110603844e0310121003150382d00c5041c60582614200c4001502c000460100f042418a801d0b40e900300750480c0c024050030296039147c4000780c0c10701c0000d0307031200f60a0084c0c040066007805000524058003548002a881c00c3c07051005581500504c1d41400e0311051803100320f43da0001030309085480034a002e5400c15500e0704c00380c4d0345101da038125109041c000001c01c60400c15403e0003070111842542e0b10b2030501001c0c00469010003003040c00a40c400068202080036141400180d90480e20300e04140a204414141801d41b4405120381128429203c0c0308000c100c0c5070041c800c0404030307000d107205480020710b07a006 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 815672482 1250 815671232 815671249
    0x10090305030a0f020a12081503030403110d0213020a1d03010e0c101b12180e0406020901092d1202030c1e030307060e070902161103100f0f1a 62
    0x5580403c1005094410160720070010307a90300a40140d011103525081200c0101240d104480e0548c3c3c20143d0750308040d007424000112400c49403c001c814030882c1a25081180841702c40706c090b40d1049801c041c40c12000958402080c14081c1c5803038007039200786072203242c284a24400151610a915208001101d0240402c0c4100f001d1001c580d142a4210680d9040c0e49105014031111000201c841074242084003103040e8107440c0c0c1c01526904450380007540406400c600d1400381d42c009080c0500420300140c2039802400313400c0d005060524103c1e40f40e00351810507044200412038604c00c182d946110b040d241c810307107001600302c1c80102d69030a0030b2900403a9994080345109401a054102c0010302000d8990076808100e000505499403644541002c0c00900260300b40c0f03804600036282c001400c01054405c40704c8a03d8420103a030204c1d02151238140446207110b00d5142c0500032001c1e8160700308030360300c5280c042c41090440001c070203401a04540031207000c1e540503003000c649204ca4074142c3c0d0b6040803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 815673732 1250 815672482 815672497
    0x8071409040c09091d0606090105100c06140c09130506060a2f1c0e011209030e04020d020d0b040204060917010612080309060f0103150c1808010b1009030503 69
    0x24007003510b1007680002c0703a14000c143d0141441e1450600002400300312501a03421080c50902100d24540701e110130410484c200f8030503941d10000105c49512000c6c0139500942c001801044009807001e11540c90302d1000c44200d4081c070440c1000200c65074a03181071460103005a0840c041004103252600c0811b620748240e071120028481c0c20000f843e089044071f0f03808903c0d482c5913662064410110445a641e5100383c500c40710b8100f501c0b00c1511a0f6034405c5c6103c4424690507962070440007140011900140700303024068080080b203080c11030709a100c030700003480c070680098230050b56409955030240c1241e0602002c28483c86c010401041120303442800442a20441061055081c111010480c011301d00350303001c00b2403034200b01c44000030320121401551250f03138070505541175a0340b80c1500f1440c905090000810070800502c2001c4c1d001c14030750000c8031226280c00d000444034080405000f843c4110340c48400c541c0e440c2e2030489464200182d0040d005d40060801910003030855480f1600c0303020f0f407071 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 815674982 1250 815673732 815673739
    0xe0a030c140f1002070804080d020607140c2806090c081005190e030403150522050a1112061303020c120309011803140109030306080a030e1c080d05010608071409 71
    0x81d0a406e0045a40444000b8440340d811140340d039041d484081e40790281143d03403201055105044030f40070304a0000310b8030440c00200103480d100314042c00c1d0a001441c07503046072050b80c0c0c69001c542d0000780c8d24801c40000b80d02823006442c40d20301d001c005074035141c40410132003141420a4103000f9001d01c0c1d4004600c06446400004c9080d0710f11900e1180703180280c5c1c3c00506201c014104000304c1c0c07021544074501035a554030b01c0e43c02e000c503101c010034024a032543c0c004203c0d901001322000451890501461580d03070007440c03039110420b4914410b107084801d0322509480d03000300b5404001c0507010443c914020234140c2d028942c44007002e0000742c8034041e010a0314140668080c6031354018211190310340289d9170056240801d111500905030007021300c5102100032034a050004100d80c80c0009501c43d0869056840d10740c1329000800780096a180000c4408104044126000002f40d034036001e01140314500500180640c9481c0c001045240301400c504103001505400006041c0703824125410824190b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 815676232 1250 815674982 815674987
    0xb0609040201020a0510050a060b03070507020f22050a0e120d05071b08130819110a050d0503071703100303030c0e2d09061011010e0a030c140f1002 65
    0x10700041c0c0c20101c03150b60052040c0901520b02c1c450014a0b4491030041c46010020070031562180d080c0382c5180b01c2601c44001082043c000d4000501d81741452a240c03000103440844544c00e205641c0c0201c01d0582c21402c180c035140e004015a082d031620900c003014007840b000381103140d010741402030b41b4800c20758400010fa0f110800214500c3c001c000c810751a206445110020f0b03002c6042806050700412102d24074108019000111500d000403003404000340b0541c4130541041136903c0e0100d5941c1a02081d42000340f40c000001d90341d482c04620480c690240c5e000e07660340c1c101407401d841c00e005400001d9402117024001d000c0c0d01417103400303000181c81e03241c2400901004203c400752a003c0000c2000c0b5446003140f0301500a80c500400c1450015507150b5000c08035202c80c1c01088100c0c801100c00c290400303902c1c501481140c4c0301d000508402030310800001a02482c2c000c4040c140707800228180e0100d5014901c2d24100302c1c50740e9040811010020150401002004001e911072aa10411240c4a40c01 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 815677482 1250 815676232 815676241
    0x305030903070b1602060a050702032709040606050a0b0a02031602031504320d0f261008060609040b10090e0714011d04090303060b1c0f090b0609 64
    0x41007201c1c0b505400c080c058020b4600380030100c080e0703220721259000600441b030108110030360b14000e0901510f982d401a5041c045c0c00610520740b100740748003205212003003c40c1006141c451204050086000b4000071031081d091105020795030946a0040030f056004000c00710b055540401611400c0d450b00152030012001400020f15064504040169081a54080c4001c001c2100301c10f5041c0c1680e882c806052186500c000e004100742d411604245400c05110780d60914850300300e2803080d80c200c0c10440425035206101e41c44010a0300b0505400308001d90078007481d550200880f130018000c80006050501e451408140003410242c001400000c0b1f580100c0c044014010b4240c0103028100c2e0304000321106000d03401c0d40d0301c00b180b00d5200101e840c180001c0455128200c0c56107120a500701c03036000c01d41d1140500c002041c258a06608040c3e6522001ca400c0304007000602103101d0021481c100b0414002c3e00904542c101c0001c8180b042c0b404410324009080c0ea120540d005000300d6480f00140c0e113 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 815678732 1250 815677482 815677501
    0x904030c020103020d060e16180b07080304031416170304150915020d02041a0918070c0c030312050f100b160f05060103050f0a0b0a05060f040614041116030503 70
    0x500e0700400c0e0303040499810008d804540c08508244c003020766603401d880f03590034003038949220b015009103a9046410000c07180440c030800c0046800038428030b03100c10b28440b41407040310f00c3e400c50b035801d4559030000ea00c84428444460381980d85940211a0f00d8a1400c00740d60b140a1030f010742c2403c1d0700d01a240c4986c90113000044880d20701e09030f0800e40c2559140d8030086088001e62060044900c0f0342040071a0080e03504082c002d0b40c6130708030050184800010810002e0b8110b140040124042210702c010690000b002c981c1d88600035886501e40fa482c04030710b900e4500944e0001400c00104651a20400c1418043c01071560119003003400d14070b541e03410100200c0d80f10102810060081286000d00d00700700311002415a0403680603005071401c09184d1103070207890300001e20024009142039804107000d005140d020303e1700480000c0032045800c00420129054075459400004001a146401100d50600d4010020750304440c0c10a54270b4840d203070800f0406039164410290400074048009100f010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 815679982 1250 815678732 815678741
    0xb0d0c0f050a0f090f0f170c03030901050c0c1302030a0c020d050d1505120d020f0c01120513020d120323130305040b040f050f01020c03060c09190e150904030c020103020d 75
    0x614200c0b200030301a1200040321b03021200d807040540d0130303c8060009070401d4000c2003c0c1810140200503500d050000c0d00119001d0f00b194205004900803002044000d0381c8061400340d12020801c4050385034940394156000f214048a0640d0554110941c1c00c07180f1544042200e040c10340907800081c10a000701c212250815041e0030107900040451940603407440001800c0903404515401c468001003107206450b2a481c084070f50502080400c080c11603866800e0308001e501ca81c400444180189490700068075500d2404016181ca400c3d80b9004401c01d545030141c0f00c040c4c030140c4001c00242d401642c045010080c000d200700b1050204060860070540f29004842c000c0c9205800e2540b210b444401400846004d8443c0a01c16110000b210041d9400424107040b801c1000b0040c1085566500050b05140d010440456004135808900c205001c0c491001402a00a54460a1f00c0d840c09040164185440e4242607100d10340b1481044006031340441c5804920341d0a00e4050784420700c1c00c11200240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 815681232 1250 815679982 815679989
    0x2090603010306060504051b070b060607050313030209090a0201080a150305150a0c030e0316080c030d0b030f0105041e0309030602040e0a0b060315060304020f030105010b0d0c0f050a0f09 82
    0x19100000002c248241d5030410000d542c01114100000d0715103071580c44845282070400c41071030405001100100f0b02c0c12a180341c4c40080900f40c0d618003540e565845085500c0500c03540080802980c080c0b0540c240500c1565215010400512080165400103050013100511210b0001c0d150b0600011444020381010011036108080b0b9813950000000c464000200300d03610551140b1300312030041388901c640140e40c16111804c002c3e514010040f0b01e01800f00d241103a041d114100b0400045074a14000c000a080401007030b0303800103022180c0310815041c0001d48036580101c2c0c3c1480144004a890081e03420301c06c415101d0901340d14181c0345010380300000950f101806540c40480c0000e5a0700d2034041d00d40c8240441542081081446010040c090000343c5a400310481d01c0c21340040d84e0300f84140156049130000313002026168140002a0a40d40240c0285903034882c040fa84482e940307424001d441030600d007410180c07402441140010f02500801c21b181d02007264120f01841c200c1e005e2000303813021707 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 815682482 1250 815681232 815681239
    0x4020d0c06020f01050a15090b010201140c07050106090b180403110303070e0108130302071503020d020714060c040608130615060323040c030f0819170610020703150209 74
    0x40310303a696000303500c4018031140b11441d5424400003548004140c4210394032440565462850381e1308080880004100309000107056650b5031141454600c0c4002e94a4400c002640a00f50303248203519140d42991056405600c072141001d03001d030035503074800081e00c1c20500c018074042e5056135141412550403600d480100440c3c00004284040558465000500d031142a2145500394441413144560580c952101400613000000140500e003180180d41c800407519140150401803080b02402c201da0094104036042488180304101c80041444001c0e400302080442600700f03441d148014101c1c0000521015030b4510141c8ca000410910798801e5012003440d00307040700f40e182c460202a0041c0384c1000208007205415902c0c128400080403c01e1141d5803280e88219480d145550764801038004090403202120107100d9009124408400fa081503a00c564400b14188100e400e03d810415024103154012648841156409070b000100742040b21703481118502c0c607064041000000740121f2910650 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 815683732 1250 815682482 815682503
    0x11d070c0803090a030e060c0709050c091207090c14181c060504020f060403050715020f030307180e04022416030210050f220503120103030309060b030712080304020d 73
    0x1031100003d212024144246c40b141c0b601003001040103d0b5014400c1c0a110b294046242840700f40040c2e041030f034100703013122001410040803000241c0320010300b40c001039455000007402c0140000c54064910303481d42d2810b125010601c1d045140d0264816685000b08ca4070115207803030015200c56415052280c0001e03100088001686031440152400742c500745e101e00416500000c0310f00c0c10900321011613500c40010000c0d945454036103020400d010360300c01c05602414400c800c012000b413000b10700c5071119035141c07442580308201d8943d10402c2a0011010314007030300e00f0480142c64030750012440200c00955201170f807a04186e580201d2141400703c0360740101e90b0180f4410103400141c50440c82d10414014855551110b59130f0b190441c003203809125a80f100210030aa01d0f10120a10340d2190040b000d413860001340346031042c80f00800380e00840c0000d5a03200e8480078850107104d42102510704601800d5000d00e041d9081c10101242100a0003403400000481d0465559543c8121507560100801e82c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 815684982 1250 815683732 815683741
    0x190902130f0b0405090309011b0c050d03080907120206040501120608010f0b090609090a021207150525110609120a060b0a060201061a1b0a05010e010b0108011d070c0803 74
    0x1c0580300e0024094010760810000c28201c10000c030035074403800c8069403284144500d40f0300c40c3d11030003944001030320302e2000090049440d0700d4984150701035500036202c2c14120f0900082c1d06207000c407030354031842558035004210f00060341d8800c221401c40d00c0918040740c2000541c4440c60040405d9805a1010343c039183c0e6104044065030808a04007904441c14481607803030754180501d441d011200c603aa25008000c1000048c60200803900300c0c010154101d5241503281d54441400c0381e207c0c807076540814070108010b20f081c00f4141a41040d081c2240030701c0c4944041d952241c040c08502d0303040520a50001c00c0515050b203841c071800000d821420300303c42c0c003500c1c1c50900400504100d214036008022415000c1403843c0140900300484184a1701c84000c0d1202c1c80b90f44440790040380b0b040d4050460391405540500c420012161414007880000901c2a40d03840310a0848120482440c14010301d4001000208100c9984000c440c0d040c400302c041d01d503503040c002c40e07003500050002000700c0804024003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 815686232 1250 815684982 815685011
    0x20603041518030f02010f050903030f1b0d140a2913050f0f2427181c080c0f090a030606030c09180f050f03041d0a020319090213 57
    0x41c613040e01c86800800500c1c4418544006481c01212000007541c4108089000402e450040a50082c401080300110ad400d1707443e1124903030700c121010200c0d591a101901c040a402810306d0390403100054082008a401852400940039025031180b0b0140c42800c54240c3c8bd1580388805400040c0041c0412240c40d000d20001e80000b0142ca041103c400440006aa0544050322002000c00206040c0081e10404000c015003c903a1024005020002808140341400340c0803040b40120100445048200b605107826460007542c1d04560000300550b15050880c0c50f0029011030b007000700d00004c16030310042005003014502c515540e582d0071211034900042401450790201d800d507403203800f845914544d510003a100340c500542d2480b02621182341c900340007a90b040110010144100c0039204030344903864816007150400d13440440254800814034611130901010181c3c402d40a910850842c180801c41c0c000d00045003010b0320000380d480c0f00c9002503554840c1d5540701015140000d000010881c1d928 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 815687482 1250 815686232 815686247
    0x190c05060c100e1f090201140c0607180f17070b030f07090506181311220801181202010213090615020c130c0909090b010303170402060304151803 64
    0x1d07074051519142240300d80d4085584e80f04e4110078207803000062207140b6000c00401031410100d0610101284582007020000007070f10113920000043d201e40e01c2c01c24000f9081038108608142c1c450140707841405096003041c2c0e030000303880001090000c001c0307800c2001407400704c41d13800c40d0f41007030320100412456600079019948a0340266503408842a82e4005000710b50081c1c0710441061074880001c4d070000d05200150109140c45481d01040702c09600c2d110b901607501090700d0328003400710000702c004107a1600320840e004000b610002c0000002c0342d0615103082043c1d16000740054126040190014800d40503102c940d6082d408003034800c0c0d03403442d044000700814403038201490522601425600c2c00420711002d600009480d030110240720441213402410301780c0b40b078811710881400100320030300d40340304403c0d0300d920540c00340300700f9415421301400d0070240e40d0070804140b802c4410400183c031682c1c16240c216612840c441c6581d8200d1100c080a4965041400044071001c0e022105045d480140c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 815688732 1250 815687482 815687503
    0xa0605060a060908120313140d030e0a020f010e06071a040c08161a07061406030637180c2904031203090b0f070813020102190c05060c 59
    0x5241d201240d0782d1074280ca0b107078090702c20412250465419035103080d02110040d5841098503900c5d591030300ba0369030740d0701d078002004402c9801d590050141400050305403140078140b8000c0750007000a0412a030003d0b034001d68065a81d4100300e01400c1c840c4840d1141400c1e40d8040e5802003136450085410345050206200445040e24140115000003a07a1701c5c004c510115400e45100d00b407500719043c0f8151114000c180c02d441c020701072082050b540030800701d2003403501c22106001d419510b0b0600d003003010300d8906c018025940708503424943c1d2400c4120075a800068006441440001e024000038410003040110f4901c070035030303400b00c01d031004201e440c80c0380009039a0380d92044078800c0e140d882c40959a50a0b01640c2c184000d0401c400c1c0003041203511b00c40004905031801240446455503800f100980645007001d03074500d04028010415080102c0030786c0700b001800e03001051111900001d60340e040b58003007442ea40c1c020180d01c10034002201e08072005450087c1000340e039046400d0344107a07034850740813 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 815689982 1250 815688732 815688739
    0x3060a11190509041820120f010605130e0d08041e03080a050a0b0d030804170f0a020705030d0e0d05010e010203130201020106050906011e0e180402092503020f09030a060506 76
    0xe154070f04260805a036100d0698109110b5800702c50b0351403a44205240c006c0030b00c3e51110b01652040150a400c010300300e000c0074005c00210300da6180a06102d60401fa05c0188816942840c1d48c42c1c20307025000a4144041015141038041ca440b9402e00c002c0494021000300d02c5042000692424141c014541c2800307241040b41c00c102d01d548565001c2c003243d082a00040e4480007030781e00380700840d2003035030505d42150280c1680a00d141c1b0b0507070081550340c0400003402554030041100d090b01501882000002c1005a0180000c8010004020418110f21200c540710307a21080084050100940c002c1c5883c110160003150740c1d081a104680782500d030303450220b00641c02d0110110b840d05020480f40e00407403044c1c5130808064603d030004016080c9146050b0b0400046218214499072900803020f000141008100741504013030040c0007460748000c4c45810004c40710071411000c1080580b00001c3c040440c0b40041e1104201c0a07a02050310800314000d606105411480084c02080e500c01070052608a = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 815691232 1250 815689982 815689991
    0x90a20030601170609060d050708010c020609162106380619051b070303120f181707020a0e0a1b0504030f0314220504020903060a1119050904 62
    0x50243c3c80c0c40c103104841d19904400c0980100d680760074444060354005d8820020b4580703458688c950142103500d40491800141e0042040c02202e001c14840d41410405202c1c40038481420b110010403802d940c1da102c1d00310fa6800c102074800b8400150b02c8250410645103880d4585039002240344002c2c0c1210400c01c1c01c0d407181101c00112850901d007280d9000582e0103111310300c1aa403d03003d840ea900800c059070205005071884085401e41401108003840c42622040056076410303c060302100da1171002650401d01d4220042080c5a2080c1c0403501c407a0701004034806e19509042c0b01c0d80300c0c0103101d030094020505502c00704040501201c0c181c401c0c40305903130070080c9503200c00f030840042d0700100d00b12000c10410001880411143c3c81070b450014001c1c00d00030f81008036019041000e0f4850550140242c0c901d01da50006541a8a03405c4003d0408950a50030000a500025261a809800040c0140d40e40c0c15105950100038140da03c85501300442003088602100003401d1580f00b40c0c00c0520030f502c3c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 815692482 1250 815691232 815691257
    0xc01050708150a0e040b04020409080a030507090f1d07110d0509240d02090a0b0d0507031d100b031006080708060618070c0318080c15030114090a20030601 68
    0x507881d404204d4001803803604190705c90b502d80724000716000c1d100780d0b00180c690580b40c0200e42000000c0000c2d40c02d903a000516032031b0980c0c005002200d0343d044580c03180742000e4200500d9000003c00c00103200c0c000c200009903268410242e03090040481c2a0011380501c88070142041c1d0440081d00c6582c0041d00d1425401e400381d100f111421160b0744034422281030074023024290050300d6000d4298000090044a00d0544a64519020341c01846426041688880821000300d41c5406041059001500e4040c108081c1d0804940c48407070207500410569962003501e91a07a070104280142d921001ca01040039170303151080503843d00c2260040401c1845014045440d5090030a006c411380050002005604d4513090000c8a0440d8804410b9040140c404c0c5220300c9559400300c00d900600e064401040020300000600620085010218642c0d2406000412003404440c01d003520200d400c40342c82c0515940c80a9120007000b15600303912031002710716002a20b80c940074009500500098071410a0202c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 815693732 1250 815692482 815692489
    0x22080f0f010e07060c060b0d06020304021009051e0a0f060201090308010803030606041211130b0102010612113105100b070210052104080d180b01060c03050c0105070815 74
    0x21554502c01a032040d00c0400482e0303c24800e18079600e1041801082c2d039840b550000740103041d41503069491035800428001145040c1d142502108001d040080b8000d2400c03002501e407a628504200d80a92482c400c100d441d03441008100c003030510382d00548031072034407840000d009209031501100411104400800ca01c5400019248a03041c014000c5240c00d0405070f82024503808290210b40c0040382021703404a555031609014090410305800040000303202d40024203680b8160301407840c000c1003014420204034441156030b8811400e84403030310003c95016407020000760002c2c24864114994050039001615508010b02030b25603026074136260380e02c8030152201c600c19040300030342c008440150700b880203010340c001c1c00b14040792034002c1803003480006640800110407a4222001309002070150059500c0b44a08105400c80f0344a04809070500c2d9507000f0566410302a5900340708003450a4010580310340104c4003030800c1d001c0240000e09280e640079200c0c2d05c5c242e40707110756200801c0c0001c0e120f05 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 815694982 1250 815693732 815693741
    0xc17060307050906041d0c2b060207060b040e160b0a0c02090601020c060d0f1109010512060105090d0602030603010f060803040b0c160311090105040203150411130b03010303030608010212010b22080f0f01 89
    0x26411006c442c1c01c107a5270f50b04000b03601a1404942981e00c44d200c0f051240e80d039100c0c514102000601520f40c140c2800a50500c2e002d0507001003244200c2844038107102640f007000c00c0c5280381e040d29142910385501c40140d141400780240d0719480400001c00c070301e2081c119009500c81840c548018400c4c450219410292401404405800290180000004083d1511840350001c0c0103040542c80c0c00565404651034202d102801ea07207494000081c0004d5003401d102e82c2008610740c4c40200201c90400c45c8803a128442d5200e42c801c5c1301c04c0072440c3c40500006000c1390b68603201c0080a032511650f00e280c400c0d41c103901b5202951040c078002000091608050003280c0c82960400b0746041c400c1400f004201c003d0125400741146c048040c021456030390400a00400601140b11100f501c83d8034500c0d0080030348010341c000400c680d00500640e451040d0641c4194151035182a10303c1d00d40c0c8100356540214100301c95004410780b5140c50028051301d000c40c00c20f421491b00801c0d2050040b88441050990707 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 815696232 1250 815694982 815695039
    0x80c071d040326090f0705060f0913060902040e01030201030b0d03080115020a02121516050a03093e1f08091e010c17060307050906041d0c 61
    0x40e1009030004000a2240407692007081041c0522014801e5400070107110070300c01c80310944107500c10b44100501c4003080201e00020002200d01c1c501d402c190501c008d1043c01405038290082e4151600310b000150300350000c50192140070300440d00c90341c0d07640090320314010a102c00d9001c01e28100407040e07d4180004544001030305516001b2040e403900c030000c901c4c6c0000080d00d9045001d459032520044c1d507014494014090071034000c0201400e12061240301d030314041c150a2200c42424103840703003a900101901c1c0420098180001c0e9030941e41403615421901c200c6080c8800820b500740c040202d0304d8044181c02454032980f0314200c0d04070105003e014024202d4580e10030440844208019202e4028164031210400c1900c2d000c04003100b940d0701501d031000c00340c18146d440e00119580301c2d074004428441d402c0b059403498074030305022000c25141e2107240980750044039040700041494490b600f0000d951046000c8a642c010351406845171502c026165180c8201c068804d01c12011881600143e400e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 815697482 1250 815696232 815696279
    0x80708060f03030c0f0f1e0601061404171c03020412110d0203070f03110901260f0d0e040b0303070b0f090a021c0201080f09030f07020f0607080c07 65
    0x280c65100401200c0401d039466941c0c18401042100202e88051000f5034401c403600740101009000b01d04094101390502c4c0840040b400f42a4021095060001c1da560450f0001d0078030410354101120140160300c980d402241c4441c0d81451450f604803000180c0100c400c10180e60f50300c46012110044013a44190301c074004200d0704844903039004c00c40002140c112410001c0034518841c2c025404a814100154010341e1401c004d0702d02082800a600401c0302046422200d204096040502e1651654081d41c400f800c4801900c0034038145034000c1000c2d900a81c4408122100410041d400805421004040a00031400c103580000b00d400c000056030742044e40800c43c445039035030340c450491130320320020304190461103420710ba203000d620741c002140003400010001140034030090001614805c07014140610f189030700c3c400c0024a140c00b105030789070503030342000c003a60f207842900014980781d56280790300f6808800014410f0400004000915007a5003020a49518a0303840390074548207900c409642d101c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 815698732 1250 815697482 815697497
    0xe010e06090a0905130b06180115021213090e030c0a1506120f060509060708060d030302040801020a050307091a0909191b09080a1e031b06090c060807 66
    0x1080c0340010207441c0d4048050401c100240d07079080a41c0950b5429a20400b850b0704014542c010b21155243c850b60011702560000162501c400c80c5884143d014030941e24012049056280c0d101e2081c003180c1c000c110018943c44c0c90709245250341c1e080c860903204046400f442c0205c2c118003480003009a07103008010801520081070386446a0107048049080381c560541d81e01c0c07010498032440390042e01103e00802d0040c4c001b80082c03a145003280d40241240f030301035014604004105501841c800e0f0b00010665070b102254901c1c0c07070182c02902458014500700e50000c18284000303684407000c3c520841155039685052a5588120f403c0400e5504e85600703030394401c010310505414142d407100c2d000505d00038094004141c0c0015401201c004211180c1020303d0018410740942e408490100070305002405841107181c01e0b510080148170020064250110a40608042c1405401e5000c07070440b04a00900c1c0c00300651802d000202850242120303096100b25002c038006105a03649813280c400c640700c5a8 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 815699982 1250 815698732 815698757
    0xc09060a170304080a03020a0303110304050709021b0601031a060a0b0d0225060501030204110f04050909150705070308160206060d020406091401080c060f03150301180812070e01 78
    0x30322001c51912000e030248410040014811020840d20280c20702a6000d004801190303d00201a51000d40038030900d18028001c1c0408107501050040c11207541d5900184d840041c042d07054001601c1d034210107000c0c00760740000410300010060306a031482001074415403558400081000500300740c040c5c920340b07180621141c2c1c0305106a900a01390250079a04107000c41c1055047c1d4081002410700441d6a680c6580041046003420301035198000c81364080c2a090401008081d0264010746c400d961244402c034001c0703010b000c4144244024841c403c1411011440e01c1200038015a01c102012800203440c07400107105550b604d2074110741407019602400281d201c400c20411100515001030364050340e40c882c00180c2244c640f1074055105004030181c6031541c034040046040110f00200740d40550400c000c18101000540101e90740b02d00188144a00990047c2c042401001d0000303401651905c02410340f400e00441d0790291880c0d2142c400d007081d00759640c0000f02c441e10386513062103020880d0f05d103000 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 815701232 1250 815699982 815699999
    0x305030708090309060c030a0f02010216170c011b0e010e011b060e030c01150f08030f070f0209011413060e16020c0d23030f090d02180a0e0c09060a 65
    0x741e0040e20000c00c40b4245481d64001485a074494130001c1020b500000300c0350602c03074002c059085200d01070300013141410300910032a01c4140e0804401442a20301001c00b940c3c0101709030550b02c01030398150003001607100004095031003101040958002c20046076152580e0740c8500b0115840340b03410b03502c0c030108036810041c2c90800c0c002560708540307030b544640070a01c4240e41080600359800c1250001705d000181c1c1e4002e02c451112035040400400f0221006024102c03000045070890790544d486140c0e603d44500b0089040340016900a512240300800010051000c0f40b0b0301c80390f2541103e12420f0200303207107480800c072051071090640c5004804005000085001e0003a40400e509005462102813004001081e10f038201504442c094000c107845204004455044100d03406888019480c0c0003130383c40d19000f24050007010910901145202e4821034864030200b04661142d06140d00c1c4505005144038080c140d101c000713a8191049041c02011881c04c3d000d154025071015042e00c06450602000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 815702482 1250 815701232 815701247
    0x6130c03060b060c010c090f051e010c15050901060e061905100315081014010b072004050f090f010204140f011b060516030504110d0309050622090903050307 69
    0x681c1e224500713108910800b1001c1c0108185240540d4a0650032070505410004600307540c1c200c14020030a841c02980309500703000c940c80d0600c50900b01f11488a5040c94107510b84012030b0810340c0b003141000f040c00702a0105411002c00d4901003551840c03613954440c18882212080141e4090302d8a160900b0030031802c0001038505600035626000c68143d0681c00306516544250344414107640c070046140580d49c0d82c500c5040c5400b156081d00d001c1e90f500d040d14024240c05000c10241c540c06200c0e20141004e031b0580741055034288050410300440c0b40851070710b004c21a003100c00321881d000f4058040d0350800c0610032203058a0722038080c0070b21469503500f80000b200c88020014140015140d510061034034841015804502c136010228540c0381c14213404280b0071108002c48241802c041c180300000c0e50480b51100e030044107407038030310b0042d008dc141107403a002158005900b1480000300180d1821506029542000c0900181c0d1032050f0355020ba0710403280c8258020f000240d0520129190781d00c6800c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 815703732 1250 815702482 815702501
    0x30f040303020f0403080706050c04080d050c011d010c3f0f1815050c030106112e11030c070b0405070305011e1407020d1b06060e040506130c0306 64
    0x2801070510104040c070014507805900141c440081c0403647c117080003c54003806502000411503a4202860101c4055a502043d071b00725042c0180426040e044110940c000601c801c15503800104540b0880e2125009000140300385002501c1c5182600503a0050b00c4043c00c0b034801180320a078590040c01c210061300483c9000aa60346032540b20480340c1d003915005081114180d40c2c881d003120b0515181501c1c2d120f0310313945149819800c040c10003100044e01e80991b411030741c41f402c1c6407248017585410780703081001c03400c0300c075a40b41c0c0602403280010544176404448500100f900304400300d14448650b030540800c5550100035a020800040001c040140d410b410a101c2c00441c0c0480d501d9546850035254406211400c0e0001c00f141905852a140504281003a150580780fa950500542c02500c43e46140500014000f6903446110812918000d0400c403039040750040000b00d40b1254050302c208000d540c1038500b48a010040344005042000390100740c2c1d404090840814555907542e409882d1804 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 815704982 1250 815703732 815703737
    0x1021203010603180b0405070f080712020108150306010305070f0e060a03081c0507080420130b0a05090a06150207140f010c0f0515010902161e14010605030606040207020105030f0403 80
    0x84c030a0000300010350b540d020700e00ca0000381c0401418094414802c4025910085080d44801020000324081c290003049541e028a01034096a950740301c654101c8410940e80bd8061141c000004288000414900280c83c611048040469900c84880b002140306654007940030300342e088101b0020311044010030508008c10041c0600304d0440c0d943c0b0048071011542031000c11551410081007200064810210101210b158200800c4c41000718402039095603401021503603401c1e425506580345400e042c01008020224465032038110049401b400c039030321800d29003590108196040030f0021420f032003070f50a8030400082d1030f40d10008012086d0034441040b4184400150110302203450074010b00f142071300a0008120501c0b00d12003401c9403900c164000400c507071050081c400c41c0602680720244441e0406443c010310308003208030082c542d1840e24018800310a40170389000c012010340201d42150b904034181e400960b85e0100780701c1039102e41701000340000c0307007080011112945c0d00c860350341040c041d1 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 815706232 1250 815704982 815705021
    0x10e0601050d1b090b1527241207020601080a0b0705130803070231150510080a050c2a010b03030c03270a0515071209060e01021203010603 61
    0x1020b01c1c4140005a002011820f0319a070100c015401c14002080e0040306d00020981750402680c405080c01c2900880c0540420700c402403441076540d0044c07004d10b0401d810500700c1c040c5544c421503158603880540d41429500c070700f100145505001040c8641210f80b82805490f0fa51120f54803103030007101c010104000d02c4020b000382543c1c110b10b085244d029140038402190380b0416401048150380603d201e454224100c05401c45141d1007510400002071030380e500106034141213080b40902e00240780c0100d034102a4a12000215550155145028a4254608000380d454841458901d4851b4a21400241d0729001042c0c2021004104404034050030740000201011414002801c550040c0f5031001107074804642c02144182c4402c0c20104250101030040140080c0c40c007181701801c292181d14881c4c8200410190f0700584c40007120710903507004071a08821a00004007174480c41c06405a8800105203264880080d400054116100d9021000c0a42140c0ca4804101c002e030005052601c0c450120 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 815707482 1250 815706232 815706263
    0x23403080f19120e0c030715030b0411040e010608040f020d0302010e06010b0c070b040807030b090a060609050708130c030b0910020f03090c01050403030f08060117040f060509010e0601050d 83
    0x1085580d81e01c0201d40c0d80d800f034030f0301010710311001611071040a03c02c164005042e40c0b0310580d00000c11208a600d44c0c00480025500b030740d002e400074082100c03001c2c0c1041c06c000303180300010500380c014004c0d2000c0c4d9003200800c0c1d0300c80030216030107802260002e03c1c40603200d0000c4003525020b0000074280b8030920011403100301c01034407141407403001e0348900300051010560f80e2180c0010b10068014020703001c40c0038142071428000a60360441c0b48000b070040c150000208511a4041c07000300d0146401110a02c040b9603222000c0008100840380c08c40000c1140c00031400b0369400b4a45c1009840d00503800e2844a821500d40303160b007032800b070204082881904001030407110940040c14034040030145040d101e2900c0b2104034140880d104901e410000100024000a0b8000f039031000310f85480c3c944009199108801a590a00c5440a501d880e000e03c1302004100703c024182c21641030302c1aa414070094403107650345800e0f94002c13003166090f608010014082401d00b260200c0034103000701c1b50b460303a0292 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 815708732 1250 815707482 815707507
    0xd082205121308240c0f0c010c0f0309210e120a03020601050f0f04050903090d11040501080d090b0d1e0504111f08061302030717060d08030705030907030210023403080f 74
    0x541204610380d454106401d01c0541212b504807410045040a1002d400560380310b04194001201c030a411070300510b03074049505d100d00300d203080c1300c10040c04c1840001a211680c40d038800104e10114010300c40c00c800428281010440d40c01001405824000320202180c104809400000c4c0740d0305c1c1c00e01c000c1c003602c1400d41d60241180700e400c0c0500511030500798248140400c1e902c0582290502e40c0c000d11445285642c080702490484016900040d2200304c190b041d00090302c0910070082e070300c105207000780c501441c2d01c4d0300081c007507803207042c1c02c9060204002c1848402030046002400b0504840040744110307015009250f4020300c01840c0c5084000d44e0394644c01281c0064605000203a5081e00d44464a03240300500c5801000031113000a02c00065560b4000f00c3c4002800d0104004021000c601030b0075003000ba00000c0d41d8000c103002840d100c05600295a003494400d0070754245039a000b822104401c96050300488100016182d10040c1542c50b0a04180c4c410308810700c4408040050350158035 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 815709982 1250 815708732 815708737
    0x304080f0a210c0201260106050408100203060f0105130b0706020d05090d050901121d010207020a060e211903020102091003020c060f0402120d051207020d082205121308240c0f 77
    0x27900c0b2541c4480c00c02d04003d01d0403a828a00d107410a20400c18480181d59101080c0103c1000f440d00030b5892460f896101040c000a40c014040c4140c041102800c022071070700500f2441c0c0d09074004101a40e2112140365441c016440c9140c0407070002c004c504c0c080e520840f201220503060750400f18007201d00c10060a0003242260202042d07035804500c2d4001c41c07901c0c00c031540003044c503803600000200e040c00003d040e281c0511814940c0d1400c41c10000803d0105004595000194207540055000305044c007a001c0d5015034441071040001c100d0140d5501e002c0d1090b1000842084000d210702e81d24110540407080c2e000e0010381e4000501c1501002024040000328031180e003d5480c65203841280c0c01880d0604c0000d4145c001f5900003c0450b01031640c00ba40581c3d100403602d0004501118680210019400092002d8142e004442c20050b1a650240c01080c1b00c1204c00c0c0040003140d41d5529403521207403c101040c0051030b0300081340300c032902003500090f0001c00307440403180f9001d500b6050107102d5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 815711232 1250 815709982 815709989
    0x2070803030c0c06010618090c031404050601170a0506010e06030111070c0806060618090703150906031b03050706050c0c04050a0504020a14010c0201110304080f0a210c02012601 78
    0xa40001d603a10843d205000c014010541030a2141148501c003001000c03450700350103200c81680e84c0b82d40e0005114440e800c8a1001d9200700c40001d80d604040c100320391aa0024007c0c042c406c150188040c004410009034200c0b0550000003401c8542d00349040042e40040107858641e00d50f48071104100c2000e044001403030410b1191010032859403604400b2414004000d1040340b081205204054103a83e80010349000740720111079901c1c09954200e0180c0061000c01a1620501d1080b100072601300a2940550b06907409228010480c500181c1c0310901c000440c00010400d4100703400c1001079a020300e001c1c0c513541900300d050307400c50000c0f580814101c4100b203500f2010141c4540c14032007503003840100c41d8058042c80d082501c00018030300010300191407080009041295090907811941014016580540858019075100c0c1d40d40c42c80c00f680d201c00301074090700d203c007174810f0b0742c1400d680050100060684030b0300c03442001107883e00156500040c0085110030000380380101c1d15042441075250740607 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 815712482 1250 815711232 815711251
    0x5070f05060f1e150904022e12050717040326060405151f0c06020304230c010801030201050702030f060c030a0b181f03050109080711030615010503070207080303 71
    0x40d0318010380158520444201403291022581d030901c0000303228280965100501a6030005c11601e6078130100e0392150700038000f9600d07071000398040e416140010110203452202a0303a20345c1e010549a03800300c225101074505002052081120058598412401a9000340282010740d100c06c2524020301340856070b000c8800b00c0347c04480810a092030700d03214694001c40304100104c400784141c000700d840405018400c19500c0011441c402009102e00312010b8807942c800300540d01c9017001d141c07141010101580c2d841c1074504008100506100000340031090180c140e440c0001c0380d103107800540707241d403003103200b6605802603c02d20141c0e017004000850184981184543e92440e001c40f148007200c04801440744645000111950280d4071007042da5040440110142c580c0f5900100b04a10112290b00042103075082c1407050092040c94005000d40c50300424443d1100d1855208250311490101d0381c602c030006c03070b20402c10070342d51145c0051503000300e1900403650f140752140062842c640007250300041 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 815713732 1250 815712482 815712511
    0x11220303030e16061413031208071e0509060f030f0105030d020102040b04052b110109050901030317090f0f0303041704050d06020f040f2c090d05070f0506 68
    0x10198144550303110700d40c5540162060103c10103203c03000080710300c5070004106101e290b00b00f0b81c4a415003290000300084210030300290b5280b401642c840b0b11040e448002c01d040600042820740561650f6110a816024426081401c00c00a42d00d50300a910116080b074024810b194a1041d0745e0020b6020315200c0052202c07546c03614080526000d66502c06508590041c481017014104420a84064030070407214031803906415500701004006c5440c206036001000d0b130200041c082007803a501c800403000c0c1e07170394425151110300380300c039441013840010000756040c0c090507003082030340244503040040c24007070700d05209251000a15118003a14800110342001051008020038080e5500160040c4040c0c0340c105850800000c0d803100c05120301502040d000141d03013010858480458020b40a80c03262010080d0300c075010205070040000c1d410b1100041032103c0049111805c0845104e1b2a0040c0109280b04141c0c0342100c40d900310403400c131760300103034031920100050081c0002841100310001ca42c1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 815714982 1250 815713732 815713739
    0xa0f0207051c050c070509132a08070f0e180616030b040504031b0f0b010f051e03030a0e1f052808010b1c0e0120090a03061122 56
    0x400450980d40907409200c0204a0b0103540700340420803d0841d0011181c7c89443d60300c00000300001c10012a0003000c0b03140086402042d0070841c03040410038403003080d0300346205841b00481a40c40945005248229000b41410402000440081540030000c11043c00000c41003506062400c6000c0e80c2445480702150003031282c40380c2c188600059801c088805025504154a02a0441505807101e005a0401810f18028081480e2030510420385c80349003081c1541c0e58038001040200c0f54080c4500c03880b000c0e030b1088903c1e42450003411020310000d015504c0c101040c0c0b000e888600006044030340003280c52a1040641e0388079100c0141c1707000c0c1c1c1c2e124207039580e950045140450a010b14a5007180001050400107e42e20565040c1500c0350000c0e0280c0d2032980104010021168810303211110b4280000280314180c103400030758100c00f0610b00700981001440c0e900441d40280c90185410420241d0200041000b03030b0445200700515002040c9080c9080f80c0e00880512500b94415100951481c01c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 815716232 1250 815714982 815715013
    0x207150203010602190c0e130f110907020a1505060d0204050f0601170403020304090510091509051014060a0509060403081c0507120f0b101d011b0b0a0f020705 70
    0x81400b101c0d000305c441780b000580e850815295071801aa0b00c10b4505000013400b01c40340c024000095500085d401c00f1500040c0f4081c02c910b0100c80e0164021f07521180031a0f507035800054035030402940449801c48040151401200030700000789950351102c1420054405070711741d803207140d00948142e05207001503d081400980000b25001040c0e126450741010080840c2d40030003603c0541e000343c68045503e403074501d0054044001d503004140820f20304404022001140c8060324100e4101e00024012550b13a400e100148414500c500b0181c010351380180901c61403d08001d00c20382d280c604003103052071050000703d141134010390003c5400460000e010070f0f05041504080c000051a22030038400340c580130200078200d60762204611183d5446200380030701150075422142c00c0300c4000d002d8024018507030304000c044000c402441101c031b540144400503117511031400242003030410002e0503070000d45036a541c9407046008044007541907441c1c501c1c07e948100360006005960081004100380b02101400 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 815717482 1250 815716232 815716243
    0x4110d06080d0f08070509100e01200c0d02030708062d040f02041e0c02030a091203020606010513080313080c0a0f170a02060c0604050607080105180702010207150203010602 76
    0x8041d15522060a140c059903100040c1400f0300700364501a4403507250700009072800c0c000e484205500c03203080030701d136240950301c8620300e02c0008090742c40807121a035100c554000a032140c040101e180e084a14203c2c05810050040ca0381c0d5480502121482e5075210324103401c04030103a80b03200900ac0410280c2c04001c2440b500440c4c0f03020400d00182c8036003450303510440044280e00d0024007440d21303084000130011042e020414110041c400c2404880d02840d8029145ea110702c1c81c03000401d01c0940045201c440c06000b1003802036050b0010318482d2206d0006407450f8112517034020350200d4680b00400d98200c2070024000c0700c401e004680e07149a0a0564890900348550511170003500301c0041005548812045030b01120100607500e07401054404c2c03018100000e0385c0c80070b500100006402d108100e000200288140d0060041d01c0c0c00d03440e814401c07110380f64284030749039102552603202d440004444000b660803540c103000043c41c0c0041d640d24502180710f01108401d0b00eaa01000421031140c05000b07 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 815718732 1250 815717482 815717489
    0x611120309060112030e15040911090d0605040c170c150313060e0c1804060506090c07120c020d0309180c1704080f0f030105040617062404110d06 64
    0x812030440c6480e041e0703141e6a4005105504900f010000b40006060080c9030200b030320200500101071800c140c40d115040c0798018404c840170a4540340103540408512400d031110500d000b49412a004802d071181c9001e088082c00640d90340c010a00300003116201107a503054012031490140034481d00c1803003000800e0b8118089448020010000c215008009254203000607500c10800540140742100b483d1911a180c1401900700b003000b402e100314a4140302034a4030540c8990420310260307449801740000500c056408103c182c2080c0074001c00070320002c0c0b00c8094180e007803411b00f40b0003001703400040011040c50019404128001d07028028140ca448641111480b0480140844d481e100002480c240f03561000e124800007420218040080340011201d800b01400447ca48911090b140d04842d903001384a490701c514a41080050f15141b2008450030800080340582601e9685c10b41c50059001c048000d109041c00d080625a03042e81d4a20400d850744070a6140c0588520480d005002210480d40 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 815719982 1250 815718732 815718763
    0xe03030c0c0414070f1107170705041104030302060c09040b100c0b06090705090d062d0b03010b090f04060e190302120f1c0f09080a030b0d0507230303040611 69
    0x1c010405400c40070004102c1000c5c548003041c1e08000c80c41b942012800d82100384e01e01c0b410b51003a0303154000000d910056443c100c2c1c0801110200009424032480307140b000070056000580051050042200603200c8031001500100c0c07181401000100c04070308030004130740440c0c080485a005d00211010305984120140c81c8000c1d00d0501c0c0f140500b880c041c06291a1184108008000400020750804c001d00712340d640c06070300708500e10000103684030329000307010901c42c2ca86000b114079468140641802e1581c0a4408036480d140c2d070460821000b4010800e58145440c1c2440c2803c1d12010003443c41000003250384076034803007401c0c80c0081c00c1016401e00c550306030100b801418105030250048401240340484c14206003181303190b006001d010100c2068070640e25088a01040c821901d004003080c40059804018202c03d010801ca130784003d103003010b41140d00c4902c0c2070205407402d006000d441c0c0c4c11a40d42c0304203e86030307a000914580c0540c10240024034003400d121824501040b00081b0382035000c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 815721232 1250 815719982 815720021
    0x3031107031707060b04050403020717030301140f061309240e160c05160630020c1f020406112b1403040501050f3102010e03030c0c04 59
    0x5407125400382d030720400d280c4001c100c00580a0104001903102e43c030051806007091015151504010b500e50146200d08400c0e0f0000d811031400c41040481281e058070304030341d81c010303004811000384050b2542513605640c002d041003041300e0b031030701e002c01c500d80092040313a0780480e100141e403030b01c890000d034014456072058042c4501807001903882d140c0705600190710382d150040181a0101264150054040a82540501c0341500c08040011141500784e5180e034481801030350b4110f805144001c84407414641250001d07a11403020507440d00140304164006040b201e030302074030546070a03003880744440c5c8404d03440d4006420880315411503500c00d0702481039030243c030170003401c80f890310040708511100d0f0600d2025a84400b1015026085e82110344a400031411f44a143c2454803074001c0000781e42c0398104601c0e03100024612606003110001c1903a00c0c0c1400325401c440180510074110a10400700e043c4184455180c2060f00d0030800f0f44000e4220200074083c1c020381d00148422205c1904100388d820410 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 815722482 1250 815721232 815721239
    0xf05011403040602071109090102071e0302030318032a060915040f03030906090f0506180706030b0307330302090a0b16021c17031501270603020403031107 68
    0x100c02580e500070b801550145e51541079140c8040e130310035003200c01e99000400f5003d00001040560140a2251040c400003100044440c0f41c0b00200041d00b00040059000300001f655175086050383c5100b400fa2081140e00700b5580f1240e42c52002902c4c003c444820103400031100c001502000515002407003174024100b002040c440c80070340354100410150512030155a10010588240d01113405107402920030000343e1141e103031982801d0034880d03080e903c0b4860f617000f265500d15520540350307090301550300070a011440c05a05402408405080c0307a8140980040019040c2003600702d00300500c21000c6130300d49105159083c030100c00301c0718854000c00d071050107003c00c3e03a150400c0640a540308002da940d150b03621030000e110a4000c1a40080d0080c10024510a100c0301c1900259061407244070741c114103050a4000c04d8481c00f0894942c140c02d602480342d184654003d4804201788103181b241804602550304140c029040b9541c00b40d800030380e00103820002d25038001116000191000040d0030f07010714 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 815723732 1250 815722482 815722517
    0xa1a01060c14070305071d0708010b0d0b0d02060d020a110f07050d05010b0d1110050c0604060b180106021b0f03070b1b0129010801080a080d0e10060f0501 68
    0x9903520700501880d8401d500d00c0381607104109050003154021304540e01c05480e2005003100360340700c5000445681400d8042420b590013801c006060b545000706290510003260307507100203840602caa07107030000c091024440c056220500104036a145102d80580d641702c0703400c4000d100189030b000342e00464102c0003001e0490100031599804840342214807801d4041d517420040d004201215aaa62040d0141c03601030400140e0013814008010494500d00055100c520079a03d42c4a001655803450301308400081c00234116910060310840c2c0903180580c184d6500303481c02c2501d00280c02c2640564072507242e448103041850481c0e2a4544142c0700055802183e101003580d0700c820303000345215004040340b030406800100d0300c1507804003c404c00a2020070300d0100c0040d4401c01c09101921020141100040030354001d03400e01d4100e0340703030400501d80019961505185034000c40c031b11070710071030316281d00d031030f011404104c40d4074075085100c0c0000e80d03189011030241c024112580038505001c02020380010008 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 815724982 1250 815723732 815723747
    0xb09120f0a0f060f0e0703020406150e1e1c0c120f060b041e091101090b030c0a051b010506010206060a0b04053003120105031207021915020a1a0106 65
    0x2079105442a41030103003842c02801a00380c824181004602d4140144c20045e40002c0030004c0346e000fa034003086016142c181c1328100303030b1804904002250380049550403a040281014515030b104491003071688004000140d03c1001c0d06014600e50048242c0349000e1200c500195401841e003c51003c0e030410059607514444070308090041c1443e0f9940c5400c200710703100e0381c0051803c1c0d025025100b002011a01c0000010440e40c3c1c0c0a42c2e00c540040c00e4054507500894002c401d41d40d0303010100c0c1c1169079410714540c8503407250020360104041840040c1d4140a1ba000740907150744102c00100c1c452030404002464100700a02e2548100c01c000010801205070304201c0c0d060721b0058920a03400d004107e081d1038051031501141d41580e030184035440070980701002800e0245082d410088069a82e0020507a48200d0746100708018481040500010701c0d04035184016880c00c0c0c4c0c0c84196091b40c0d0556408d9085c8007000d03000250b041101c17032404000500c8030031000e54071301140081c010350505600402c80e1 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 815726232 1250 815724982 815725003
    0x180a0501080703020705070f08030a3c0309020402030c041508040803061002070b1209070f151d0a06030e100615110f1c0e01030e0a110d08040b09120f 66
    0x144d000039040700b806001d000075070180095404400d80e01d640c3d028903690b00d83c0300f49024000510040c5115106c0410660100c0100c00390b0b061400c40414400e0840b00811102d00d100b50901d40d03503001140040c0c8460000d188035034040317030079079856601d1f0031030108800d4040404070007000060b20030040060a04000c0d42e1304000103440320780311892104000c0e880d029a6400c1302c1084000402d488949210550045100e0b450030703001d0f1900385580d0340b081c4818014500400b20101410305418071030502c2440030508503806000b0072004024407901051480c11690040c400080d02d0303818101002070308001e00e03818a4070036441042440c0c60241803800109103a012601008451011800710380d200308411451111242d0030b03110003003a06a1484c00f0501160300010104403032041c0b682456010b4030401052180d0403000c0c28052801da610941c409030b40214403584003132a40f5044000c0b90b0031502910150007406111640d030f507904002c200c00d058641d490100e41d0707800104d601800d00c0011a20910a = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 815727482 1250 815726232 815726237
    0x150c1122050901091a0108071502061501030609090606030209060105040e010510140a0f170c12041b0902090a080601060212130e07050912070602190f0611180a05010807 74
    0x50b80c54070b14a460151036140409070510300d91440c000c00340c400503074540b81211070b000200c2c1e50856880d419054181e800103c6040580c000d440001d0010712840340c045030550051400081c4030b0340300c2803403400301d51001d134054441e07a940f41000d01c1141003540c502c82c0c0040c000d017400350400c0d20301a0984050603050040780c1c0244901030240e03802c035024440c60b0980c0440c06210a032140d80009000708030038004410300d40003800309200c004207480c43c408414000c0380d8541200740b410081c1000c0f070707040039030240044800c0b11401002d0811040d84003a12806002a2600941c3c1d907000300040001820320341d003100c40160000300040251540001d01182c0071440c2c1304106450301c90404540801c41d8955004030503d003540800c0020759540302d0000c01c01003004940e030300e040350780444019944510354014030015901481010640d10240380321100300300c2c13140c07190131503c50300341e031300c1c00e080e07902c17109a4110451002c107081e151010906032500c9690020f6403010b003c00c0c40c0c00b00081040001034001c006 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 815728732 1250 815727482 815727491
    0xa05060d1704120b090c0103090807032102030114091509131b09020408060916260709020301030c060309170906090a030b06180402060301030b0c04150c1122 69
    0x30308031141c07416140104200380e030850758801e46040c05403440c4400c50307081e8480c1c01000d140543c10740c000d02c660041541c11040040c1030039074035074007941e8012103886600b4030020800b0305000b00d0b1380e80780020360281001c4010600068161000d1101801c0c0c0a060200b844900c0c83c1032200360b0b01e900b035100394040700c10f98026980728401e050580c405080026603581e00c071001400490032000300d1f0010401c0b246103c0443c0d1840e9903501070345444054a03121901d40f441d0a8604001079843c40003206400402c2d10b650410045000d18420701d401800d520074140b89401000400c14000c240c4030080c01840707281428040c10025540d1240340340000c4507864520b01011a0755001e0391905000d60f038031020040c01c1015119100e0502d140c0102c41103075642d104a18030034040b40c80301000c0407902c0c01070741d0180c00c013400c690075541c0304095403000034148508400c05010000e9403440030303581e00010f5801c9484030000541e90303017030070b030030841c1644207090040c00ca0b10362000c0e01c80207801c0c96840c019400c480001d07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 815729982 1250 815728732 815728763
    0x9010207120506161e020604031b12051803010911100f05030601031a0418110f0618040207050a03090e07090e04031101020c0102071a1b0a03091a010810050a05060d 72
    0x48000005514142841031041704a000c110380002e400703405280070362510200c800e0000301070440c1030302114000b010000100a81400c3c5400744010f072200405180940160040030b101290031512109002d654844d50510b0000c81410120560004502d15141c001070f800d1440c0805805880050810380c1015078401c480310022a5101004410040c020009d11040000c0861441d006101120035502003001d0b203014100340c58a02e59003800c004018100500345148000951fa5080c2090480c41c0c1140d002c02c00fa0300059010710114000d40e10a80700d0a0059080488200100b10003c100b002404070b082c1d0140b140700006003081e5407080e49454400c1c105070703030102814060302a140e490f441d10740c00410250304020705540140b50034155042c5040d119520300d00c040f180d541c01c00001c158807460401071000d1181c420b801c103580b841c2c06851105443d280d140c280001400f8240c2c0401d00d160030041c44038950012a010305a000012044144402d0500380d0010b500c60b40901002001e03140b501e1400f0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 815731232 1250 815729982 815729987
    0x140f0117090c060c100b120a150f0204060804031b1110140f091302160f08040e0a1d0d0816201f091709040b04110901020712050616 58
    0x50b03194500241030640c489040d03000080c1d40d803103c10b00100c0030a0030011100540d00f85203481d85415254003000300015452034a070951140c04c040e04240480d85c4071030f070685c40055a1b0004000a007005e94449a2515040c10010031104c601d1032010140d03400c09240c1800700c1c0c1c00864103804108110b40448001024a9050391203940084140c0e0b0380030400701d07402c0c520f000b0850140c42c42c12000d452500e5035440c4111100708a00c1981d4425a0320b000c550041c40100d0300740d0b90b4400070310b8401e04010380741036100c2d00c03c4140c600044810b040d800d5100c003510318804100403070009241c94a000206902050b140300540520402400a07002800f40302a4502c0f19101d01c0802c070104810304140b0fa4288101201d0b01d803903010f405040300000b85521000c110301c0e101c40c400d000025411024603c01d10f81d20107072450845d031101014550207600c030754001d11140d8407803050700601e09030304800030307540c0c400c0c20000390420947d030380a1884040c00480350000b081d808100345910501c000b450f0200e03a94510020f = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 815732482 1250 815731232 815731243
    0x30507053f07021f02070e160806060706050c0a0306080f0a1103071a0306190609060f03020c01020d0f050604090f0b060103060f080102030906102d0504090606140f011709 75
    0x6540f06035406105a00400400351381c01c075090711a82520810340d01c4890603400c0e03183c183e030413201091010505e40d4a85201c3d803502c90b00504010006441c100303090310380c2c0090302c00c2502c400840180010f0503a5519801d0701c500401006944003400300b0442c1c01010b40d031034400c2c1c5040540140d0120700214001e039005d008100107801e170f00c1ca100c0707121700b03c1c812384009903002128000e0103607a203c080c000350781c0c0304460001c04568065913089030701400c0180444001005603910030525400340004030004000b2300140604484489000500303403001840700e020707580c000e8402801103203098007200101c0c00d4150014903642c1c002000a00c01c0c0c4911004034000c0c04168003641040036441c80110703103c84190000d5000d80340400846050784c907604c1c200e4100040c41d00c41c1080002d1113941c0505000311410550008071340101c1c0100d11036030f5030f10210307042c0c0d603403003600301c030815074034402403040d036607000d80095190b1000c0c3d90456590449000103482480410b482034280301c0f400c030020b990408100b21 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 815733732 1250 815732482 815732497
    0xd020409020a0f03110f0a0503060112230607140313080c10060b130e0c09010c2a0915050f090c0712050a0f0e130f090f030507053f 58
    0x6143c140c555a050450005000040740d40c4541e01d0314600c2211880d007002c584007514001006000580d00e059010789128034682c04c21100030090b0380c00801c4141e0361a51240400a021000c0d107401c0ca04500c000704080c00c0500040300d035a00c14030500080a51040550aa0039482481d4968500203e120140782c4000c090701e4082c42402c29074046491546440600301c4600e0380350030b681c2070903250030283d03021120403207440d18aa0300c14001c0d070350598403e15905400034068860a00c151007003250308103405001e049410100944600200b00255461082c00554600080300c000d0381402c00001070301007403c240c0e103103108052050204410141c484101e03031416902c2045142e0704410038101504036000704247c035002c280c1c121070750600c8600a80c0030381185040104016840e0980b5520003000b0107186c601c0782d002070390755908040001d0301c10f140e4012290290301c445403150304a1a041d882d040d40075587c081744801030954440b21300c40545c1542e00d009055047c10340d505994640c0078041d405202e4 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 815734982 1250 815733732 815733749
    0x30504080a0804030b0f06090a180f0b1006051603212d050603102003010801051b04060e040b18040b0105010f0201020c071202010e0d03021f0b0d020409020a 69
    0x700d5210801c503041004004407407041483e00301d60351318142120107440040700c50315003008903100021448051684038080c60b00c3e00c006050b444207000d0701d9003500015080c2080701c0156984c000d2280200044406078001c2a40d0305d001458450b02080c03440a192030060001c0500890010117203001203003c0018094506954040285044e403105a000412480040001340c420310704092000c00e850303000702441140054002d00c00340300540b103501d00401004507042c1e818415042121649490400194020550200086503070706001c4000b0b42203c103e0b0000e0701d4502c7e0300b04010411740d50060010061f220048500103641c1030a4070228000b10394131528102c07100341c03501c2040100900b030f122a81c1a200c003a65030404115504105078201c1c8035038045400d055100314010480001c441401c440c4880c410b2600421404108002c00c0102004600480c090380000e5a1030b0717025030344035403004d160012084050140c007440d0780200ea454100020084d0280d512010000c080d52200307201c00c1c00170700146 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 815736232 1250 815734982 815734993
    0xc0e2b05150c090f012f0f030c010b09070305070c1401020405041b1e1b152f090d0323160c0902030f06060c0a08070c030510050c03060d03050408 64
    0x211240c2c2c01c5501c002815031003040c6652484805510407075540e5090007034102150016110304050031070074103c50a40d00c08a10810818854400d01030001d007107500748a500110305140341c0c208000c64440010061010145044104199603a0000d058070a00d0340180740400b8090500c481c01d406885680c01c02e54215082c640d51251050300a00a02c504019640c1d4149291500310000e000e4003001c0d0540000144d50002840300607440c00703000e19001031040c0c170340c01401c80780d403445081030303401c0b00e40c14810400c1c030000c100041c040408441403000e404410001d1038001c040f00000d81e0000c54200c081d04000b40300076114030007845002c451000d0702c28034200545440203006104e540300003488049409085160300001c844480b0300989000789100103c0103042d650f000144082608141480c0d9011711030398010394081000c01000b841c003035004031848003140e4110708046117040815a0340c01b4059103450204080c14584105481e00304000b100c420421103042d04080b5410f0260b608010018000c2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 815737482 1250 815736232 815736241
    0x40504030e01021c08150112060b1308011419090f0507081504020f010809031e04060801060203030708011e0b0309010f05060102030f3702010c0e2b0515 67
    0xc8000c20718909402d03402c0321000c14040c61101c08144440f0410740c04180c940b00840c14482440300c4404071217406150214900c44102110300940305107a010642040f0001201a12003044220300000350400800a0001e0003005020001600c8010440110100146100349031a1182d4000e10441c5400ca00c02c85003417043c0c0c0c140151540030a2040403001c0c803a0601d0302d1076079042411003903ca1313600100b107440c1d102001c00054030290001010030748240000c10000300000700c02004c02550a070340c805000c2c0c48500309000070305002030607044141990f01c20b10420030025132080e94a4155902c071840d60340385e030071084000020b66407a5000480e04083c0071003044120b02e0150b01c01c009403204c140003440030351200741c0166142c0c07054402c03062020b10104855841c00312070003c0070600c2c6c0040711400c0c01d501d0084075100c081c0c00d6400785860050351101c0c0d081030b40942c0000e6045885008482c048860038a00d2040c00c007000d0811415045194814919421704c0004c2c0700d4907000400d0302d213111606152 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 815738732 1250 815737482 815737487
    0x1909090f1a070306060f0c170408100905060a140a0b0604090e21130603111b0303040c050f0607060906091e1506060503010e060a03060f062309010e04050c04050403 72
    0x80b0742a8001030f00d041c0d000204548501250300480b032080d00c4100c0c6c00e80c1c050700c0349130020508140000300b8010800c40014050700410024030099599100014104074034a1f0841c10b080c170113401c182d056424403d031541c0d4220294486038009040c040300140343c0e08480302091450085610242050380381465445203018085461902c040b096009500814050409454036020395105205203003201001400b40e14001cac0e0002441503601c0710300c58242040d9094115460420650003201030704088180000c10101556000151008a8002c95010005c801248403802014400703031006403500f030740009001d803a07408200c000741c004078044145a40680000c180b04407a900031030b04000b6500040c071a09a25104032402d80f10b0381d64401c1c0ca16440c1c410340110590003c0d100c207910805442c40080056068071503c240d0706030320080030824500e040718114040c1d401a40c1d011405440200c10380240e0343e000d4284e81542c4210400101d0342d1200e081c481d142101c483c11250b0441d00d0007084c0030500d40c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 815739982 1250 815738732 815738783
    0x71806050f09130b151c060b01020601061407030c020607050a051b01021e10050a050105030c01090b0403030507140f0601030605060d021f050c0105190b1909090f 71
    0x1102514100e086a80d55028080c80342c8045030b02058442d1900b9080b070008801c480d009401040607901c085007502c00304e0009050781c40740e00009040c004810300010401080e07000d001c1201e142400035103030541c0342c800081c00e43c010400a4002e541d100196000405000c0d0381000d41d400c1d005085281c031120f03603180aa5a60802c04825902403042080a0b000003c00f19540f60080318107034050900d018240c107120100860401d01c0c3d40341c500481c80218511805403241c4c43c41074030242408100355142c0340525060000400c0f41d0ba04000280c0f030103001860707614003280d00312a03051078115035a60032818040c4116082482001e020f004d8203010a0420900040792816203000794402c12160300e4410800c04002c0e10f40e103009410000300ea0040401080d0300042c80c0500c1502d042491074030001c88082402c4882c22100c0c1c003030340c2a180b00b00c1c9100d05090f200f08100c034501a00e8054105403e801d0f610700d2840d940c800c0151a6844420580811002d880841740c46a4400c0b81c4408485210340d100b048407 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 815741232 1250 815739982 815739989
    0xc0703050c0306010b0f0702240712140408031914070309090f0203060f040518030a08150103050f1302030114090d1206260304031403070b10060801050f03071806 71
    0xf4071a00e400800d903900d14408035603c030304941207079901d080310985c288a040030b1460711000307102d0034140d01800c0800e4182c0092080c903100d1901c2140a03181000003928840e4884030303e0000c83c10511017400401000800c8035110f032400380a490b10407000040885003800008030324142001c010030443e0030190032001c45000c3e500101001c0c0122000481071004030702040301e5880e4044441d0840d903242e4202507001d01c1e003094201000380c01200c28038410310f16541c40a5588000109000e0400c00c05030301228025046001c03d180034441410700d03a0104d8502c90700507042202c40f02c48802c8a004540d025404014039405006075a891407801a40142d2075070402c0c240300c000301e001a800d03500d6071074983c4181026100b070000c401048403821409400c41901440100105100802001c03003c10000c90303040507a40c4c2100b0095584d60181d1410440d4500040d0010764a2020b004051026907005000103064a10540f40d0044550741d4030002442c10000740e200100f4009500b80c480140c0e40550881e5081c5d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 815742482 1250 815741232 815741239
    0x304030210150303050c1e07080c092e1e18090305340605010627051201091502030105030f15062e05030a0506270a020c0703050c 57
    0x8180100c1a100709032030b40900c0032480080340c0c0720180002402280070307040d005102421500b20015140f02d00c3d02c0481001c0c0200c050303600190040040490401141c9100001034403042002e0a0001070360603104106051007600710350000d445c0041400c05484080104031504000300c1b0f00903500c1c40d0301034244490080d0f0400d80010942e1274482171a90047c80900c40c1d140e80c5041c9000090b000f02c2400c10004202c0e15580c1071030081061219543d02c021030341d01c0e03000d5440000c055150407005040b0745903000003c0c0c039a0401c400800b50b80f00c000b41c0c4003011036405603400b9840024550700c0341e00401d0302600050801080030100b00300d001d02c6a000d14181c6000340c013111000f06005010503502c0c6264200541c81950701c00004009041400006008040307040d045407d00042044480f4090144140680000e001004000c10a0843e00815070014000c0e40d003482c208000c03c0c4070708840c0101c0c10050120558260200d5030b41030140e412102c50880f204244c80d400d0381c41349070040d1107402c0761500e6480b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 815743732 1250 815742482 815742493
    0xa0c0305060118090f112217070302060304030e120a2307090c020c0310051e16030905030c1905010f0204050a03060905070f090f1b211107030503040302 67
    0x12594091a000b0750303c1004101d56020a501c4c107800c060250001c049084034964403449079200704e41021015041c2c5640350761240b02030a50700c180d44124105190f00110007410940d115400180010074040e09594040d45d40954079512810306403420406003801079040714205e02034400c50007020401906c001e22481504400000107007140500b604550700c030b481d0b1504110710400c5801003680c0223064100304c0340103440307900005800007828802840740d403100a68440d07041010b040c90508e141040f141030713805080f042c1e04000301c0e48808011690207050a0666828882040c000100103035000d029a030411900244061118503681500120701142c41d50700f8046a05401d101c14000e44080d601c02a081400311440e5884401c0036107c25641a13440b4000e03500042400c08600041e10007038880b42401040004503008200c04807508801204110a4100380d14021698080300c100407084180c400d00c0c8580c107011088100030f04109407821450400007403450101a008400385100e81d0180e005d455 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 815744982 1250 815743732 815743741
    0x3070f05010207060c0302210405100603030807080109060e13030c0b0a020a03110c1507090b040b1c090201080601050f0909040b060117040302031209030c0105101403071a090d08030a0c0305 83
    0x4c00742d004500d102d40c204d0701072a0b012300c0d0840008500a40c00790256041300d041e02c50321781c1c452045038003a030016800034540600300494030750808a26401040442c074104026031070408616405c40300602808018242c5040c11030605200d42c40c0b1600558000e85400d85070305100500c03e00a40c82a0b01d03840100c1d0900d404000c16030b98178010354084807035600107450034003821040e1720300511000780030a090240c0d1420203c1c06886190141020f401c40e01001a0341d40500840c9110304850203800d4401203040404080050741c0c0300281682080c13003801e00c40e849016600c000d0078140103005200c1e4118035a801000240f0041224041c0907078000e032030706910818031301050003070440300b15800740160b03000f045584000b080c46502c495000100740296400c03d0003c680050a40748255444a1050111801405812204100e8040e00c0000300c00070004a8900000300344020692050a01d07100c00c04507580c1d581da1903038034078023030010341c45502590b030b0340340500030140286005411400001e24100008 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 815746232 1250 815744982 815744987
    0x922060e06130b01020f030a021e012f04080f0303010e1003030c020904111e030f03041412010204030b040b0f0c0f030412090b0d4a03070f05010207060c 67
    0x150140da0050203503030742d00c0d02095030304018103c014203150440c4110f2607507101c0240c0c2070000d410000a558041d100e080600c1e5114190b10103d01c1c003120140c0d240c401005400c40c00400801d5415100b4503030a040c440051082035000d000d150b0080080d40100102e48000d1031000c0021416503420b281d02d808141c844805080100200b804000d02143c0c0c0c440001015251211200d80d202e4412500c1040b41c10b841c0d40852841d52600980820304401f10000c556603282c20702020005020400055051038034288246210290341342420340100300d845c2d0704000c642000c0d012280550340000328400107003003d24107520050301c00c0b00c40340500a06180070840741600340003240c5007181307a440028115111619502070407101215090144812144000ba086d04c5e0403010706520285140c4c0011804195802c000011540305450101c0440c24000206070b00c00c1914100d080309014010303064914400764486256200300c60f0b0140000f200008000200881500142541c0d440703010300703005070050754006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 815747482 1250 815746232 815746259
    0x110c04020715230703020d0f0e060a0c05130311150a0206010f09060308180a0e01080d11010b03061303090f320906190302180601080c04031511092206 66
    0x1a01c503500c1c0a5021880301c5200e1b0300a0f0841da103551a0005288116400050489a44074a07288481c0c003c2420019480010303c25440c0c03458650510b503103015404a40e61220030803038000101142c480041c40d6402c2d442e103414405109811601c960f50301d200080010303588100c01d104c0c0300304210311600046200b6120b0b0044c5000c030b84d48005050704028001222000d203807114204c3c20f42151252000040c00e800c800c036400d00801090000d0103011900b600b004001c50301144010099a050440481881e00d0015010fa07000320100d0040c0709400952801312910720107a4020800b940b028000420f03e400030300c24001074141080755280d48240e61340a0191510003400d2050360002806000400d5401e0044034141107041c000040c0c942c0c55183d81c0018000700025a0011200012904100352560805101a08000d04800e1182044d2071907607a1014071682c112b113890815100d10b000e0f942600b046c4c082c0c2c2c440420003460b200c15003c0c4ca0807490f96505011208000081c105400003503401003520b00c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 815748732 1250 815747482 815747531
    0x30e0601140924040c020102090306191406181305010519060e070e060d110d090210020a0b04200d210c020303041505040512062a0703110c04020715 65
    0x40b88007000c0b0943c1c01c0000514004980005554003003041031200d036800d100152180b0ba0640502890b2500188408101c540c1540d010140b10450001c0c40b17a5a5125011031440500300e618030840c603035070030041c0c0c0300c52042c81d00f00529a6080c10b061145100300240e8404100f0510312040001da9580d486845240c0e90640c0c44501281d003144082030340e410a6001030242c6504900b022901c1c0303d52141d141090340c00245034055450391400e80c041145400160f001000340607100030f201c2c048040c1c0326501070b41d078058001480d9083d01c0502200700d09032000901c811940007082ca84d000c81e0f1030308240300040b202c03c2c00c500c423030819200d102c0c08035405001c030b00e61400d0700600154107160900d4400c03920040c0c290382010078841e00b4400011203030b0f1003a540802010401b07020307001d00d080900303030040c0304520446003a5642000c0d0345100e4122880c0416034003055050320700000d200101c0b005050401c0220a0400c1c1c000d4000183c110600c40c1b4800c4594108800004c1082442c8520381000b038070218020 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 815749982 1250 815748732 815748781
    0x20c0d0f030c031e020c19030506070804060b0402030109050402040b10090603020c010204151106090718090201090e0c0408060f10061d0d0f0201121515030e06011409 73
    0x2221980841d20540c025502103209040042c002d24441051030f002050680040700164005013030706c441401e100045401d4550103080d407804150555480036100d00780105440208541d100c006014000541c01c21a1419000307401150b40f540c4440c00300780035043c01c40d02030f402a070038001c002e50305042ca0146038007858074580c0d51303480c3c45040100c210080c0d0311081d1a000f907590244000308900d0b130754800c40742e195192a1181e00c58002d0403142c0500340790f0020003003a401d4124110070009aa090184036036040b0504000251030b0a89100585184805070041c07081850a03c007000010340b55100144207440c1d401c000c4506950360300c5800c04040e001101c070911402c2d6280010003855006a01201121081c42c844030703034421404005c1841442d40e58810f03601c0070703414250310055581019040785c444618840c1804007a4001b440c5860451091244400c090590900101d02a10075481800c085104a007650510759541450b100030980380036032707544a000308202003110000d00551102545c100795 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 815751232 1250 815749982 815750003
    0x1141f0e010507061d0a0c140901030f021f05180301050420010912030302030f01080a050715030b04050a0615210c0c080c06070306080f0a020f011806080106020c0d 72
    0x344011103031070300501c1003141c40070f4640d180c8014401c100b584006020039158002c051310703242401d00441400d9554000b1043e040c00300181100380d15032111640c15aa0410300f114801011440480d0f800103a4503803034a8400c81c0c0d0031030445103903032242c01001612101003840404814010415003280c0041d140208402d407581281400c4008110800c1c0c00b03140141841e504031551032050091141c041403044001075400002c000b21180c0c1c2541d01d5024000203c01071168105513601c00740d0724a185d020344d40030a00300300310302d800c82803194000c8024194060014001c9050040c540d1f00038100601036241d1340207801c8400c0c520288110b9400c4601e00d550780204050703444401001d03004001100032401008840c40181011416100c000d05040c03034080d0060146c0d03c0c0c0741030300508a404a030001d4090b03070000040089a584005480c1c1056a0110742600b4601e440c0341c0140c800b800d112544100c4510084d400051742904114007504032405902941c845d03a603c40d08000c01c1c2585100000c2000302e82 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 815752482 1250 815751232 815751257
    0x71805181003050304080d020d090e0f0405010f090309050321040e0403090b1b060f01050a0b13080a031707090f0e04061512110901060e01120605060301141f 69
    0x3545010340c0291804502111a40e2a52509801c590154100b0b5056501c07001c40b1904603a81040113140c151018641700c04036038100788910000d42c0c0003400100c5115400700100d0140a0f0a61062540107401c140820001c3c6407460701416021141c49101c1c03003030080d508060701400b00182c8444030f1000b1000414609420b142102c4050440900305404000000300d0215000d02034400401c4110142141c1c0d0000c01882c0c01214a8100e0041181c2039100e03600004110a803642c01141084c4c6100e105200d803594130034900c04150403c2d541c42802c0c0d071302c100c0110406054000b01000f48083ca401c0000c81c076640c82c00401c0d03503039100c0e40c818040c00035204501040300c0c00c0c507940410b8225210b00e00110303140d0302d1035a22019020168004e00d49050304440303200c3c104070034403c9007155180300380c907004069854904090107101110350400c1c14013000031241e00c200003031648804003601c4003e013040d03200e50311000204800c10581c0720300b030b000b0b0340c100c1c0c540c0300911040c201c080e400810b10b41d41d40b10800c1e01e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 815753732 1250 815752482 815752519
    0x17030912070b0711040f060501020c040905191b0b090d030f0c0f080309191511040f09020a08090a111c0606030f02190e010e2706071805 60
    0xd0500068105000304040400e400c4049030041404034014610045850b03210010841110a0b400c00d2030314403031400a04000c1649c012400038514030003102c0000780c0d011641031283c00d000490210140c0b0034400c40f01c590400216014014001c400078441c140a9500d400c5141d00e40e100d0461000d501503035200e203641c00240304d0f400c42d8042501c50f20704041c444810303503610351001d8006034085400311008030030041c624004100b401680318280d0088403142d4a075803a00300c4540c140d1010fa4034069150320402e480c80d0301d00700c00c980003050b11481c00311380d46691301901c00094000c2c4c1d40300000503407d0030100c1c0c20a140080e030711900c90703044120440c0410101080200300c90046901d4102003c0c045601d402040b01d603c1104000c601030b424540300c0028503c100300380740c80340070100c4ea03504c00d60545c180440d03c01158a5419140022007a010640f04d0030300b04885c072000001018040c1e40c86c1031881910301008203840780624507035181c110700b088048014101041d01170180a0b003001c52518100807011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 815754982 1250 815753732 815753749
    0xa020114090c130f0504030207140609090a0203070c1407090b0627010e030d08090d081006030b0105280806030601081b0f03010507230a090b031e070c020901170309 72
    0x70f05080000e246410003e0b600159001240c00798096000a281000400180315012000711011a603031882d040004002881c0c2940241c18200b425034040006800c40f40a244400170813508030700d442280307100002d84940da9502500400350101d0800c40019a1414503c003a02c0481c440341500c414111555021240b07000c501c1440d450403c04034040d05503094605005800c507404455481d061f8911300429114a0040c100358100c0030000110304200e62840c101c040c2d02c4c04c0d00c1141c1303400718001a403400121028001d2180388140c20100e008150469040d108070880d011340302d0340b5424811707031b10f4508042d210107092049148603000303c40507801950040d02c45030b01307001c0018104000f001d080c0010900b1504111506004580000d6002003401d4002c4040c1040d500700e600041e00c0d10000220042140900c0d12540c100b050000c8041190040c500c0b118407800618003a40300b03003d107408840108044117200c030590090754400000315582c80750030f500c0300607c184a002145000252400d018040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 815756232 1250 815754982 815755009
    0x240806091b0307030606030b03072d03150204030212010b030d11100606090e0a150308031302030604050120090a0302010f1e0c02011e0837020a020114090c 68
    0x21581d121240d400e52008001c0c50051150359070020303a050a02c2c1d005400c90351801ca2691080c3d000041c100b008994a07190900800e2000007a240744944499020b80b01e501181c00080855200d40c1c092a0854080d5000c3d0007101c0c0200e892420429022481c00d003201c0107040c05503015007000c0c3c4a021064010103942841b0450401110000000034012004031250364004800080c48218100b15546400c3d40840d00541684410080e840e01c50141c014151f1440c40001c2400c6001b000003040c03690340f44008600942c000c1c05655080c9803d190aa00800c03200081c1d84c003510000ba0740d068805018002d8403003180003d01003501141c01d41d001510010007813032003082044034000700c030b485500154400900b0423070b403a1109906c4100c00c1c0b0015114058117000e000c144441d4208480754158080751050b00004000ca415413592644408280075001001c502c4024501041c1d9100600350240d004204122565000300311003010410344c40603c030420366241d0050341c400f003c00b814525020850b403100 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 815757482 1250 815756232 815756251
    0x4021c020c012a200a0b1302040b01050a0c0b0613020d090b1311060c010b0a090905190b0f0406291503270102070c0312031d2a041524080609 62
    0xc90032641d030744000d2440221070807d40e201000307280c001141094002c855045800b401d20074106250420000c11100b541000500750000d0b800100310103880d0440b01044000a044c0705540e1141d480c1c5101c806403441c45002c4580004620004662020001141049580c001500031014200c41e0405c00b981e00800310308203295680f406146803e594000c00b84000703042d40507011540c2400341c01c040b400d1800c1c104010003480c02107400c0400017510480c809134003850450001065407607a0805400030b042c075118031070500c0700365405030162840e52039154529280440c1c1c0000701202d14602c05145001c1510002000501c044039501401520f461301c1d0b01d5840c548000605014443d01c96003614240741c1e105545031203a8802c08201d41d6494092a4010900241d030300c1c06d91050507040e541c0c0d842e041910400e80c1c500c0d0034050f5144000081070b201c41088028800e0000400906140350b02c0740e0b03a4412500310030b140520310b4105205801e056110450350307440d24402d66a40405009910400501880d007 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 815758732 1250 815757482 815757493
    0x3130602010e0a02090408090a170d031e0e0c031e100b060304080f0906120f060d050601050105070c150f0f0216050d020f040c030213060215040204021c020c012a20 72
    0x3c8d1a200c10040d0401030010201e0f85e600f65001202840c2440b440c58000b404050504c40706034402d1510b020703800c0c1c100032803000c0068125144049581041145078000340d150090780082400c10b80c80e242c1f0301500c1c2541342c0c1950000014185070404075000d07507080d2a00481c0c1480010040f03400000a000700d1145049c03a5071405070120b00094095020001c480f04181080041c801c520030300f215207990203042a154038504070503640302c0700c1d640d10052240c3e0b4100b2500180d20701c1007220b00001c003401410b0020b5080b0301d25903040310140c01081c4084690340000e8180101141d218400a1881400101c104008441605000520503400004038007644c0006082d02843c065403200d1117690000d05207a9801621040c499048002e514181d5205008542c000952902480700750313040304d604103604940041e51006441c40710a126851103c02100203880800c0c907600d21034040d042001d84c22641d00300d0010404006803075401c1d050321029180c00088503016041410b5210901c40c40c0d207075808008440 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 815759982 1250 815758732 815758747
    0x30403050106030302210304020d020f04180b060306060105120601050904020c060f07091406091908070f092a030b041e020d05010b09030604122003130602010e0a02090408 75
    0x30300b9110b0310307801100180e224075000d64020000c0030400f04e0701400e5400da00e245041540001d140b444515002030312403054022014400c0d541c90340000321505d07040009400f070f418241410303101c1000c200e03003250081c01203000042196108000300ca2020441d2001c1e189247c40c0c0d800111055001a0a8075070025420400b8410a0004008440c400c040b0002c03000020b20380f40800802c10541d980c40103600b9491401410000c1d550581034881040701541e0b210042400340c51450303c81d041590102d8100c0c00748a0b40410998002c4c0034034401d803603030000103010403000d681d6580d0b0f542070111420f403074501c261130758940350300c0c403a400407600314000400c007081000a03148420b000210342c030b400d03005669001516a0105446000c3c41d4014088096001d0416403950080f9458840040008010302003c01825015901a0244040540504425640c0d914100d000c080d92035000d000d000004c000c21040020301e1503c1406041503c1d00500c0203084a028285d007480118000a001101c11003000d00011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 815761232 1250 815759982 815759993
    0x31c1d191217010b1b010204050a0b070c171b0117040209060d0501183503090f0303010603090506251d0907030c080f04020120031903050a06061112030702030403 71
    0x4030f02030f200c1c0030300840d034507800300614090401081c0e8a1551a03401808100700c00e5403030b002200221940300c030b001550380f82e1503c3c104080078515040502d10310045602440050400601142030440c503962400e440c018480c0150351032294170314074001e4600441e00080050a000141e6500008090301b99914416995642c3d030944034525001004005800e040318140304140b0100300c1501038603000c080d100410717000410a180461030007401000c0000003c680304100422048401c00640d03000c0e6a200c0d40c4038407000b070190075000000d4174a07100e0200843c0302c5500d00903440641d8103540e80700400315a450318042e581d03545090000c00441081031801016a100c000304140b240015980c0000c0038800e000000e800341d600500070007001e11064040200507600440c0c4260720304507401c0c14a0f403107122600340601e1407146581c01400b00880e840b82100994060300203e00503806034005222260320b0307071003c440070710352000c0c1200b981d401040b0a01ca0200e5030001541c10945620540345020345035180e5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 815762482 1250 815761232 815761277
    0x60c0b01170a150b010212070503190908030412032619060e01030503040e0708090a0320030d09061b0206040f0302010914031305060f180102031c1d1912 67
    0x10241c3c0c0c907496035950000366a060003480b04005541d81a0303800c200c1c2d1515025034034080c0010b8041c0681264003182c031302d9400b030301d81c440003072000008582d910f0b0f486002d44403540880203001c03001325800500d00ea218117041e110400c40408000c401c0100c950f01d41050300e2228141141a40c0c100e69106400300b000200c41c4800e0b40614042e500540e80d4030b103001d20190458400514550401201d40306000059034041400b01180740c2501c0c2c2100452803440e0802c403040203543d088016484001203d40b4210801c2e0810b02ca0240541130810038101c10001c080c6801c2000310b14000140c01c440c0c0001c000a08400000f100c96000c2c0c400042d0012041d07403800c1d06c0c0d03034003c100f0001c140c0c40450782ea5040021405020b020740b00c150380742400c1801500300303801c031800340103420703a2006103194000c0010791003081075503100c0075003940c208402c0806404505c014001c2c0313045100304020407a65881d50a2001402c0044815060070b041800c5205031105500080ba805210042088440c0c10704004181c6000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 815763732 1250 815762482 815762513
    0x40b07061e06030c0e090105040314030907210302010b1507140a080c0f0106081504030825050403020109090603081e0d02070305090f0a0f090f06080109050105010f060c0b01170a 78
    0x2e0074a1340c24181240301124010062074004980c5c100130030000000d078030404854400760040c003901d80703a4a80c440f0003820a140307604800300005c0c01222001e84860161b0a65543c0e5009030005c102e400c00203003d002d04051160a440308490701000401c0000d5040740868012144080c21f59085000726602c01d03403241d010080303031082680804250000e60a0a214034001403400c88010f02080034084030168030203030010006418003400c0b10006894241c81e00c9200340c2d90410886a4880800c05c41e00548207420900041c4c0c0042c0c2c4d407400c0030440c200c0c04c3c4600340c140c0e60411a824100082d5070904021503800300e843c2e200280040c403086030780440c64006890360510944036035455014a0060248020b46014060300c130f02d4030000c0400400301d08806140030b40c1d41c03140c00443d08015121130500500601e41c0300090175031a003c804000d0040641c06103058502e00390702c003d041982c0f80821030307600b16045009440000900700410126950304400a072100801c025140c030700b090307901d40c107821100d501d0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 815764982 1250 815763732 815763743
    0xc022206030c0909020901060305060f04110a140f0304081b0604110405091c0807020705060f030730050703061707030c05010f0c0b060d02060a0320040b07061e0603 72
    0x19007070040124030403035500503001d6a103080154060701e80010300d4105061003640180755031100031230200c0d260083e00c0b08801e00c4c0900103100c2e00b8203203c40d120441c0d100100c660006103005880c560070b507800c88111401e94140c0c21886045841301e4a62502c40d5104208040c01e1089080521115401c00d10600d8403640c095614800b41b29401c10a100558500030302680740360b0072000b080d6808480f21020960415480c1c41e20301e1071607503100c9040c1d00d00019500025071141011400704039550082008602c581000c0d0798004101214140c8a00500c0800c9050341c5c1400490080b081005d1f0b03e03038080f0368852220310740030441a95500b005a110000104c040380e0303541018105005111408203800c00601082c41e1580440d40070400c010000307080100000c01614034040420383c41e555214101c4611500100741990b00c1c1040072015004000350300c1544281140d80130b00200c2d500c13140050381c1c2292214030205262448075139070031b0020000d41c4c6402c0000500d2045843d015a0b4034030411019500c9036 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 815766232 1250 815764982 815764991
    0x30a0e040f090209040b2805010504180b130629040c0c02010801090c0e090103111504061218050609070614071203020307021e1f060308040512030702180f0601020604030806010c0222 80
    0x148070556080317339943d031400d0f024001c1c1903000840301b22a071544100048030340541000303a4900380d0041c203c00c010891240d1404001054141e03114150700c1d00d0341e24219820400319040c20b00c1560308900c415000390100301e2480042004103000d0308028890100c42c03820450000b0080002500c8078020781080da250042d010901403a410201800c04900822080c4141854a8400010440304001210405c442c1d1a113a01c0d002e94a071075000e03d0f81c050761060942e500b45c9441e03030a1a640700c3c40b83c4904030005103540b84540107100340208590295400c80c2480ca460328000700280c01a6001514100c214821424980441951000c2c0050368403a9640138082c1403100f20484181c09444240c1c5100c1689001d004000049540f4100c9080300c406480c01e92100080f0817244d402c500583c0f02c081d400000c5800548c580c044030b824a1031080d0041046041540c84040049a560004481c01004a03c0400201d80c0307541c0110350fa401d00301d10083c2400c0c4003800d032001207130380803240d195034000160305d9 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 815767482 1250 815766232 815766239
    0x14180411043201110c060a0305060321120421111509150912070b0a050a0c0c020f1909050105011e020a0305030601050705030a0e040f090209040b280501 67
    0x80308046210400a500c00511212500b80c070040c40c59030a000c8079050181c403100585820380184034203003202100400098031810341a001401506084031b82d94800d02900144400841c2c0384180d0909050072030891505000c01050f456080319005031050396400a011349261748184146e000502c4000c40d44e8854003980102c501d0030307181c10342003400d00c2c58141e60301d410031044040c0010900315038a110000c503c103d8487c03120090411002118114900800090403018446124689402120b076000200030581e520715851045440d603600c0d07180002c4d2461104005803400070b4030102d0071a401000d0442da00d540d500c1490008803036510240066444600401c034a682000389055050710008103080d083d01e010800075114410004020148140440410001d0740300d2000e0380c808950190469070346403205c41001d0141543c6210079032003142018041c1e400314100340103100e062540940000700c0323500d8603511981c4411008000310086900342c6416400002c6000306002ca41801c6080050319504 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 815768732 1250 815767482 815767499
    0x70f030507020d0206040209150907031e0b0618030f010236030303040803071e120b06130303050706110a23070804060806030f010204091a0a0302011418041104 70
    0x203008115806542002103061003a036004510b955000f07074110b0b002010b40e0b03910b11004400ca89444c1102d6000205070f020041c0c050b8256000c00c0d440340401c0500101c2000340c100480580c2d415805264100d0403d020404148443d0400d0640300803004080c1c034200c1201c110714900f240c004101200d1a10f00c0102c00601026041d421800120241701e40c1e0400260780a000c41e940e8440540000c10060b800400982c1c081d10400a03150754651050741ea442002c928130008001c9101590142509032408900ca0440e00c0d20300111480c2545038050407541a00e50f8a00791200c1e003090700d0076200c580c0c680081d0b456080d0010300628040e0900d4540b10355075000d9070440d10380350803502c4010250500801030b0303102141c1c00505030b50807160703a13180c10000307591074802107410901e960528440315030022402040c5075004d80c0210500d8401100aa080b0700480710070005030142c14031020307011841d4041d0071041881c40c1ca00415102c403480780b0510307100e00104082012100ca1584800c407080000c1000d114003030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 815769982 1250 815768732 815768741
    0xd050705030316061109030a020907090806071709061b220902030405100902090112030c02040e1e070506030105190f0806010e06090411011b05060a02130b030c1602060f03070f03 78
    0xc50001c040d401c106c0e03440c0c0800e95800e540707440a80308150020008140c00d1051a80da005030600c0410b440d1103081c10f503070140c50f055500380da01034101c1401c8009010300900040d918801c0c40f00c80040805804c004003540065400303a9007039440c403201e40040540040c8801001401001e030007000507940d10709414624108022002071044060410480d5070250361841482c50554014904a80041819240c141c0701c0003d6404000d41141c14401e1400c02044040b07000c85440c81c0f22009040c2a03200d080005445030401c0c0103542d401030052006104c6d9090032140b69484880340c54518411607260400c114158403542e129000b6607101c2001448818109080c00d500001c05807040c1a0740d0426550744100711402d40e10030f81c100000ca1148a644081012500080a400800b078400c40c2c07c0044805000c1e6102980c0e090915103d580002814044201100c0c45030401000442c10800c0d0300000d02aa11406a4140d038424400c1c00000d0140c080c1d80001c50194425844031043d240303821201070180c4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 815771232 1250 815769982 815770001
    0x50c0c0319021f0c020f011e030e071505030f060105040b070f0c0b040b071709130e06090a03090b07020f09010b090406080705010c030809030d06030812090118020d05070503031606 79
    0x102104010f00d2005801441100c0d029a0445041085007101c00048178403407482105404d001d10081c645954194050740030000c0700c2c914106071039029803a0510301c0b11f0219001030300c800141c0108009810100e940c1c40d002d400c1581450600c0c41c26640c2c1d80000d8054120f443c00342e4282400c6c003406410000c92292100007012502c4c1c495041a00c1c0c0500c0341207034010000c01400003401421a94480c15011044507800c1c9001001661744d0a40000351030011314040d880041d1522505000ca13a80003000244000301c41c0d49a40c412020074240101c508154200c808203d070044d005c00c50821059544c034024038040c0c61000502d54441d0007030381c100030503511360380d0140b80d03da00649801c3c091641d021140102154041c14200e0040e140c0d20842807961040820303100c40180380070307008010070562000418402540e44a8410541c032007031a0300e4200c03200c0040e00901c1644a0f8520b200508141d801443c2d054000c00079a400300341d03208046070442c5d00840c0280e5140c1d6120380c1100030000c8074410749010 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 815772482 1250 815771232 815771269
    0x50405040f0305070f0b0a060303030f1a1023090f0103140105010c020114030c0909070e100e0102030c0714030d0c05070e091f0f2a050c0c031902 64
    0x4604050315400d035450740e482009020000009884000c4c8a030209031040002d920a840144e10f1030000381e400010825404102e001070300f03050441d1200012405000c007003028196881008200400800c400804014424414020300410b0242170b00030b59039000c000e0940304280c1d030b90340f0503000d410850b1080ca018541c5043c945420161200b0074012504241914400e09003481600d505000507540340511b84882e84180030000104401070b207087d0081d00a8000544d00c0d1300300c5803103036207003a102000c481400a030040700403449010030a10540e042c02000300107005032460040c644120302c2c20280b80e50440946000d084060105904042000b85e0055090b031800e643c0400036541d40e107446202e80d1081c415181c401e100480c2202d0310500c204403808801c42806da1201c041ca04260000d0000007a4a03035085207032003039070354000320071203020303861944542e01c804d0072070a104e1000d40b010380012b400514035201e00b40280380580c1303007004100c50b484181e904444c1101014030400030051041740d00e030481c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 815773732 1250 815772482 815772491
    0x40915091803200a080d090618060501060507110402091f030c1103041406030601090b160224070f0c1203090302190f060c080f0f0702130b0303070303090c0506040b030f010504 77
    0x20b600f1004580c010b2810392180e0010f0392942c0002e0b102018001500014021900d80419031b100e8a100000c8490710711700c111418480f03680d1f140d00070f03a80c034005c100340a860b2442c030f0000d107202890700c0c0c3e0082910143c01015110f80d8842c03805484842e00d58112441c1c0804d54406031030005a810006c2c0c01d03d43c100c040001e5144c24182508514110308a1036060f02420001c408500e45078001c0d101c14001d08454100c0540b913895144440341e90081c0c6940603405900c03503206002003020004d810143c44100f822655192200c0c565401c081c0c580140001d0b40d890141d14004248920b00180440c03c1038001c1d52045042411801001000b02125140b2414a400c500d401c10401a1030728010044550604140351507910758240200b403403040d01110300c15a01e00140da081c620100c6406002101d009032032054031030a04c00301ca0350858210022456043c1e1007032000c0c5c0d00192181e0413030350150f4482d4109142c6143e841c804034171150082e0b008548410804420031050005414116004001c110741c00d00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 815774982 1250 815773732 815773787
    0x20d0609230c1603021005070215190902100f0e04140126010c0c110102070f1a160b1e1012081b0f0106050f06040915091803 55
    0x3980091126850001030610078002694004104181c1d03014a140a0030303030b120b0001d9440e000b03458404000d059451185403a010810152001401c020285060280643e55440b0a4140b030300700106000d10034403680c0c40b0903c0c2e100503200d42d840400e4881d11500e80002c142800000a400701c4607007000b95005506e0300008008082c110b451242c11034201c010401e00180c1c2c2c01d03040440d40189862070000035800c10300c0009100340e00c41c42402c59240a03d801c849001e1400004907142c0440e4824207812085c58802132024a81103812a151036008100c00c0d4641005051280c00e03410b0000f8080c0c802d0740208003085490429480c032556002a544000303840d1380f80010143d8a5054140030707402500c0c0151038050200840c490440d5481590450503a0200190000f065600c401d1342c1c151b040ca0b9400c041c1c0004190821117000740c51220300910403402d05051540c000e005000705810b1031002c20a2440009261b84244504440c10414018a410144540c2405040c07000302010316030403090f0107168203 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 815776232 1250 815774982 815775011
    0x40605040b0f010c02012a0201090e0f0613140901051512070e0a0b030105100303031d07140402070f0c0311010503010b120402040608070e0405101b230d020d0609 71
    0x7030640c0c182424144001302c05400100c1c2c030901c02841203920701c003101481d1018a1560311640440324403d90b1280c1185844001d1149261000d54200041c0c180d0f40000c61890718069100c1c590300300d6590350008500e280c8280c19075805400369250b10903650340b40e040c004000d1040c007200001c40e000b65900a141c2480001c0c0b181e0f505440d200d5021250440c0c070105512000d00c0e04180c6803404010001d01207420402543c1e400764031a4402100400d207042100b441c002e20340e140c0c0c2032140c8401c038060145585812030811644540508082e48107500f0003001d4001101c440d0040c005038050225100c80a0445c13900c032580c1c1c2d002d5103030a030501c13000340010441540510100d540c08400c1d0080640107840e2840810050b1425070003010700303070082880105040c41c006060f2031080d40560211086a042e54400d5011580c171005401d264001d40c0c03140d90480742c06003005080f6075011010150400526000e2205a034000d030050040040d00040d07400b0f00d580e1030f8041c990240614801c10403200320203440ea07 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 815777482 1250 815776232 815776249
    0x3390a0e01210b010602030a0806040506010e01050304051c080114060702060304030e0307030803070e09010f0e07111005010b0703030f0b0913080408030d020307230a08091c0905040605040b 83
    0x50b0724414001c8000350302c4012122820200c040c0e405400c42485503181c05001e520f80c1c000d00411000101800d000411525103409518010b61042c0c544000042546004591a600061055529120fa024907a8012180c0300b01120b10b282c0039610068a54140800507503410082000c5502c90f404c1030101d07801517603c40049a8020340d1505100040d680c0c000046400c01c101a800604030301f001000704503d4039000403a00d081d10100301d40c0c0411503a2a02e00300d0400484038040c000410a0342e00000d05100d01401002045e401c1e03503003c655100e110291108140d0f8800d802600380c0d043d000c24440704054060140410140c60540140038403110344020400c0c80d00028a90120416400700c500180000001140c020781414415a030307039040242080e4029610640d00400001c64080380d81006444540a0f40c1c170a4403140c16061802401e400b0131581e81c0805804a03c05000c0d003ca480090100080aa9224006501c61104580ca42800c00040303440f00d80c003160090b402c2459007407050b61034081 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 815778732 1250 815777482 815777489
    0x90a1a0409020f0a0303030b0112051504091a16030e1f0b0d0606030602030f0609071202130b190f0507053f03040b13050c090603390a0e01 61
    0xe001580105070b000140b9110402c80601e40c0001d05042c001c024940e040d0804441208280c8907000300c401c1c1c141400b000c80b80708440c261540c0c01e410011030028501500402d42c4c50317014240402d50000510842c03d40342400b80c801e01604440c10030071901150b054004d24080c9512000a8030142c820000ba454403000b07940c2410141603034030300176025141c0e280c0242403035042e040300c1c0821660b0340b2843d2081c000d41c01550390300103c41e440c6001480c81d191400907544200902d5481010641303c2d284584043d401203181100c0a0140840c007142200070b40000d0181c001e0f904000c0010000104409884604c0081c80102048800c2081e00045003000406c0e0401c0005440c40070304801200e038101d9174818849c110304407000c000c90088045188403001031401240101c1032402c0649030505180d0003086000d10050150b04155601c00d01840c2c00d4240d90741c466800380540b00c042c005142458002c00b4020a0406400c48900c3c951480324031a5040d40c050700011707901c4001d8541804020b8480040510 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 815779982 1250 815778732 815778739
    0xc020c0406060e1009080d2f0a08030a09150c0806031b0607050f07061206140117040c1802040816050603041b080d090612050115053006090a1a 63
    0x540c420b417482141514001d08200e001c1e60803121080b0401071940d06204018a10f10303d500c014950b86804600c0c0140601c0301d0000100007024141d43c94040c90f410040420300e86030769840c0d00c0008512002d07025603c02101840028803018840e601070140980030784100c1c06984010b0410111411140c000e48000c0f40c01c43e009034903030485141c624134001d60041c8500e030724021a4800030f181600071030b100319105995901808680d072920100103240d844903030028000f8016812180300c4008d07501308580c110f401005002d55075501c40c5090f90000d030200703440f01951039000504202da064184041105540d810b1000b0300c0941c50640050300500024001508079074502c03016041d02d6181d40100001010410f0039599005140c4002400000880c462030011810f41004100b60301d02d0343c480c1a06942880302e0750703120341154113400c031095081030390060108084141009076114240340602401018000304051785d1610005001000401606088600d810050410018040c1c0154900c200c0805c0c0c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 815781232 1250 815779982 815779999
    0x90f1a0603012312031c0c0206070509041404031d01020105090a060b030a0b070c20150f040f080f1e030304030c11060a1812050c15070c08010c020c0406060e 69
    0x703042c0349440f4911510340b84c0c0310426130303164a0440c0c0d021002d001c0da00c1064611968010f00c100010b42500d4403000b4840c01a00007100041c45c10f40601c0203041e1003000030700001010b0705442401031880d001698184c0204401d81404818141c1200100c240a8020304c0240700c2030601f855115660b480d003400c018000d43c0c4900103204070340c07020040c1c0c03001603810a8410600c1c0c106841c020b0402140a00b00355207003545016940c3d9402c0300440e904405140241c04201341c0d40d1540900b4a6a4101d29507220761000200300006d0700c0d44c40d000c0c0240151202c14042c004000384020790a04d452184100906c1c1c81c0840c00400300014030220583c1c3d8019054140a050200e543c80c00750189202e1881e146e40c00100414000c03016540440c990071180c3c00c150050084075224000c1c5c90400b2140400145150b000504101d07250615402c80c80c51070000d0861070b03003440c040e551410341045041e0003084003a90744082c02d03030100e58104900d5a9030a4159070800c840d0b820200000c24070461009a81d0281d03848 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 815782482 1250 815781232 815781269
    0x60804060b04110d0c0206070c02030a140c040911090105030706050d0906140703050a0c02031c0b0f0301111e04030c03030e0f04061508010b251a01090f1a060301 71
    0x7603822501d0943d00a01c10566074890048001c0010003000c48080010b2203258001400d0301e0280040441c1d003a0020024140f020550359041c00000511800c290a4080c4690302c103040d840e41e00074003508500c100416814003400000340040500145d00c104c0c03182c5e1140000704551a08103044900c5100c14110109161265061001c05042a80e000d0212100780000f001079540d0316074002401003000c2c08041c040e0392054041241d407806084035a401c12020000600c80c05041c0f0b40c4042e05103038014111009002e03143c00000c0c00c5410003405601a1140010221509154203000000e02426100d15a040c41d003151503005039840e0070300004082c407a41640500150362504a00441c5c100001c0091005034ac40314900203070200c07501c40007030208a81c0000880d9103000e60060311081110140500c07218210112480740500c40e41d00b050b81c05040d0800ba003252003c0d044403180c0a040d41c088045540081422423000312891100705444a1000d021140b4160b59841c3c210303030450394040e01c0303030005080 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 815783732 1250 815782482 815782489
    0x14190204050c030105060913090515180c010807050d0b06160302060c0a1d01020c120d0f1d0d0c031505010f05010309120f200a020108070203130b07060f020a030b03010608010204060804060b 83
    0x309c41e0406001d034812903959040c5c8a80c020002840b881d034500400b0f040708211000c4076a01c0e01c01304409804903244100007585075100e43c01400912a01080c082a0320002c43c001c200b00307a112100320816030900000c600c1c2407640402440303402900d0304003031901d04810f112008180680c000c0c80c0a1490361003c440c2400c5a2003004103a480d100d004103503c040c07025120080743c0d034451080303012005c99003030403003060640e0085881c0030b080b0840080e2183c42c138aa1000300070b0031180c8444200c610402420010000c90030090510342c12400c034890004455041c41996940020300ea44654109810580b1502c00104001828200b0751105d080050b1180d2442006440e00c180380381040a1181905000d01c40848000540a14650007130f218011244c442c0c6004a851307110b4510300b4160388104c4d140c10401000002d0050610700e002e03038000a0002c80100780c0f1070503640480b90362800039840d107035004a2441c0a11400d0300034001000211f140910f0600041c120900c010000344c40d03e65102170707008103500e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 815784982 1250 815783732 815783741
    0x8070c0c0324050a1b020c01050d05090a08070807061a060d0e031905031905060a12020114041e0e090c1905090c0a030f1a0d14190204050c030105060913 67
    0x90364500501c038078034004c0c09240c01400c04030417141e4111035482c40c0c0d011590021442c14040d0006039525454619080d106030040c20029203010b80620070064000c000c100b00368082c01075a4070900c005039960615040c20700c02d50b0041040c0040d90100581c01004540c1e07403900700c0d8841c403185500030450038849031400d070840c00f81d9000c0c1c0700701e4060f003c0c4804007194000d00441c803d8624250504c5007440004002003180e02c11110260850103100f400d0004c0c0084880f0740c10700500c149000310420303101000c443c80d01e82042e030064020440c060540707081882082c00d40f102820300f0114261040c80c1c5503410640c3c9420320030145000d03181c11080021082c1d030042240d005085c029081c0405418050005a545d500803040300d00001e14144031002448168010004814100d00051504240d00002c02c0b8580003d404112242400e0840d182d802c0041485016101502c84102c81c00c000030900500040d100d005100c0812000100b0052082d982c524050707072030321a01030702c1e003c07111200301100c0300081 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 815786232 1250 815784982 815785043
    0xf21050f060109021201090b010212070606050a090b040b010c030909200f030f070f020d270b04060f0c020307150c0512031b0901090308030604061d060108070c0c03 72
    0x50250500104a410182c4c0041503901030710b118181440c1c0c0d950048508503608921110700607086880d0030305041c103221000c2c1129502941001900c0c82e542c0c000070341c0000a81d4410340ca007a4940980b0600340c80c00d0b21903519070000c00e003030520401100e690000c000c41e0721400380d1140a580ca0701901e200f18800c2c14a000c0c2c000c2030300341040c0c1d9003404a112070020380049070341000410071a000a41068440c1c503d000480301160020a200c840c0301400741c0703180e0551806492800d41501500c54070349000039106005141c2d02400607030700c5040860040550000c442c0080034000790402400061b10b00181c072a040340c07c03040e00d50f9a20030707400a080780c0d01c1c09000d80241103481401418114800304100440c01090003072681040d0041d43d4015070814090721040300d0220702c4218003040840c1034a0300540e4803903002400040c6141e201c0e150980c040c9200d4055000c1000700e0010004079503000780000341c0298044c00c01e01203482559035054580100c5000052089001400604c1c6c807425004840942 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 815787482 1250 815786232 815786263
    0x3100305060408300f07030f090308041b241407051507030c021e0106090207050303010f0e06061b102301090507020a030e060405090403090f0f2105 65
    0x240d0a05003000a444c1d0444901030210a2000c5001c048074150110030000c00e80c4a0b4100d807403e50340f010812001904018076120500d0340341c1242c86000d11a51082c490b01c1403003a15111860304150406001038191980306803125408080140070703000c8031138810450709080c0e6001c02040d8070000b40071658a02500b20000b844040071486070100b00c03000c0b41100e15140c0c0241c0f05812582c0b40e0b002107080ea90082c0c43c01c40540c0020100608454898400c05072204552002040303540d03582880400702d03440610140c2c0c140d080840103010140d400c5030104014209849159800d06089002580070311450010120410f0210341e1801200000d0041500c080c40b1000c0402c40513080c09020b090a9241c2c903985a6582d02550011030340604a106040c040d0b0381c180c2c0184041030081d94183c0744070305140b8415a0003103080c00000740c1542c039208118030681c030964680318580d16002489000034060b40203040301a0304a101800800b040c0400c1128041a2901c04900440142040340c100102c2c02940d618 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 815788732 1250 815787482 815787493
    0x903210a11040f031104090c0302014a03010e03030106210f020307020c40020c030c1c020a02061c061707090513020103230406060513090b0c03100305 66
    0x1503c0211802038011203024a5003040c1c00e18a403004c1208403500000010400142880280095446800c014200c82161022640c800584540802003158804859484081d2194103001445000e446030131290390250000c1c030030b920351042c02d1501ca0005001d544104640102c10380700b01c0d00207014089010918030000c00c000e14100c0000e0b000380d8021510000517214400101000e07061050b400d411041c00302c040d0091a4015900581003440304104880301c1200d010501c11240c1d890f0301c0100004e060110085a40300000f665090030010601000411007200c07543c010a1a6004110910440d5040780c010703903502c1d6844110f04040301c80301c6520603694984640410115519244507580400d00412a001c1e46c0e6141450010b07150220b8012162810900b6024019402604141040d080103582c00303425a1420290071110641200c050340c6068544c40e0070441400d003003c040402126100b418010050703030392600c10392071802030035201c115a030020016132000007004c0441c0145510038140c40 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 815789982 1250 815788732 815788739
    0x316050606090c070b0105040c0c081308070e0702060718030f050706121a1c050a0f0308010902040b16060b04020a030501031b03030c0f02030a02060c0d02060903210a1104 75
    0x303030364060807101e890040401c00007080b40e6110f21010341313001e20b9110180c030041341e003054140406088000d2184050000a610784030000d240c00010300f246122151146982a02d8008101d2507d0002d90000c40920710f003c092020890380854901d90003401b03401e0061280700240c15804602e1010b90014201c00a0718501101700f190208043c1d003218055602d07100702059040e54141121010081c140c02945181d26510309410850303650501840c8401021100805d50f0300c40f01d003040300e4500300300c9000c00300301d0040041503004040c540c00360400c44000c42c10903042842c1c243d001d110f000f440c42c13241c80001c0c2030041000000d1b0000007010a007d030047d03440e03a0250101034013412080c0400c44410040422246007504103080c0d0400700c0f03070140e90313071b040c0023031251034a038142c3c1903011050b605405000f2a172000740e25014014800707000760b0801002030080c5035000a0410401504807107031504100402d0b901c2d010b0000e501902d00700c0884409010307844a03000d00d0018103d050a0701c810305004034000 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 815791232 1250 815789982 815789993
    0x1005010b0a024810020307060f09020a05061e040609031a070221040f14010e10081f05041a01080a050f0429090d020f070f06110316 58
    0x81c00000c00c0c1d5000c580748000d04454840e11294441c502490340e41d1a403002040c044542d0284404500c0c1ea41c8094030858020008504400b41868119026030700c00a01041040543e01c01c0540d81e005101e010451a480c0e0341c0010340700e0b20580f107000d108030300c0850000c105840c00710006e43c1152000f102d4a64035940d401d006080301086100070707520307102034640388101c2c004003490340c0707200d00203139805055911800c0f0819010904040b140382d800d03000500c40401c0e030364080b0324598081c04042d80b4801001080130001803080c4444102c40340104042016103042641110100d500501d415941c1c81072880e6129010f6022020b48e44403591181c20300c05100304000310700e104107219040a076101d00313007940c0780203583c002d481e402e0329044507403100c4800103408a4034040258500313405800d4088070a40e000380b00c003805040d00381c40031100c42d040a16a0001c4540411a17402400e4000015003000d40c904844c91184036214030540041c0074081703200110f9043c042c401c9600a85400b40032004805180c1084c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 815792482 1250 815791232 815791237
    0x1062a1212021804050403020718020306040f1803030209060d0603080a081b090616151b020a02010507080c07030803042109120f0201090b0403080d050c0c030a030e1005010b 76
    0x600003040150300740d07240d0740d09280200d03503960f44000720000d02c0b0a940000c1c4402003a0090040c0e04500603100c0218100381258050581c1c18141d50000d0703241e0a00c02d003048111f6801c1403481508514000041c0501101c440e0303008401e1b074150800507100c1c500440810340611640c07143c1c96546103040c2000c81080b51850151002c0d868035078411000d80da800c2c42d10704000b240b140d801c1d2800d00b02408032841e0340c6860300007050110140c651417406450780740d49d0340824000001080034900d4444e2050814074044144010542500c2d10007884000101c0d000030b0f016218100780a0301490700082c584000302c0c000c12440c0000c0d82e00c803504d25601e02d07007400d10154400c511814140d071058040f51005200388070b06c290314281ca03905155850b0460b550356410000e05640d4108074103100404100284003210600504021802442e0f402e136180081c540031003c65000401c42c1501e007006205000c0c001c6c07000400d84412188a082c00156443c090449a05e0718402c03010704866a0f08000003c0707904140c6101 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 815793732 1250 815792482 815792513
    0x60f0305100603030914040f110a140f0405040f02070506090d0314071205041a1503070b0a0c0b0a06030f0f0219061e0e0a030b01150504080601062a 65
    0x98518403004031040718141c4401c0d100290000e20840310500034a0195069000c40460080001031480c0340b88440d01c0540d0454400b4482168010500c060300607080700704110818504002c0910305081d1648800c00c501072801039038003030343d41d59107001d05000e02c03a411500709a400100b100e496207016460560b640c0d4210b80d9140029081201602403065030011307550182107035880701040403c0b070030040d500520000f4401d84203040e54880c01119100340c015082d005100c0d02e41001170102420045c90700e0312503254400d01c0392090401062201c10f030b1012202c0400c0d039008001005c1900caa406042c00703800942c00180c010b820707000c200010007250341e501c0d5034054801d403600c1c0c81c1c6440801c2030b1011603030b4621980380828101d44401c0b035100d1081d01010400c1da00c0d805d0007107208818070049100c00e05250022650402a1801400700b6808581084085003c5161151604d03003020100f5464040610070032044c0610f80b22000003c1d00703082d1008800e0b1403003086021545404c2d003002c140c510791801 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 815794982 1250 815793732 815793743
    0xf090d060e01061a0702010e06072f04060e012313020f030f0f040302061501091a130506030403270506070c034d0604090507030f0e0c0d0213060f03 65
    0x42140c9144c1000001c1e0340145030145c46640300e540d4800144600e60b0b0204004544c1c00181c0e11006a130300203106810b4a40e079403c81c041451030340700ca030103001c12500301e60030082840000c20010000501c4412000c103007000c007034050304c400329400740c046007030904896814000c4600205502240d40000d00244d071140991200214090310b4011080340091005d0703a02600580120000800e1290103011140d034211061401038070155640707500d1400200091078216194400240c5141c02442c03050700c0c03070060f10b806c0351b4031032541c1400e5a003d82019802403407810304881900f50f4520000c001c480f494001c141c040d00440d9500f107645007050401659020403901c19814210f0403903820098207040e10f00c40d55541c007500108150f03242102c0750710b000b140707402140d400c07a0541d4603041d00d40c60003410051058040c00300c1c1c54180030070b025050703a0180d020500c01d00e107801660b0500e8140020703071580c00a01690880017185030350001c2481e202c0400601480281000800100c00075a002c0d203000701e034040c2c2c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 815796232 1250 815794982 815795009
    0x3060a180219261605010804032118020a050406060804320a05010f060f05091302030d11010e06270c0a061d060405030303010e18070306060302010e040507050f090d060e0106 76
    0x13080304840079160b000741400101d049001074000703402400b940c0000b00c0c1e40c039118150072441d1650304d4142e454541111604601d4448a981141010b9200102400045170305100701ca003040d60007000000c0c01000940106907240400c0c003841d01505c1c5445141c03d140703032040261200c44007000d0760b9641c0840100d0b5150300c7d102c00c040380c1c0801c0784120000c0c0c0320b80040b01c40a6901d010304100c0755800203800945200701150401e401a6002c000c0c07894003904689174041d000341d100c0c0446084030946032200d511a044841007151a00c030843d02c000001409290f0324004800640e41c5515100c404030070550001c3c150306001c14065040024070000040d001c0c60030b026202c0000034460140150701c11150554006d0006200310001461426403000902c83d07031303540c044a10f441c45807410000b42e0080d50410380e03039a4180300b0340d640559840c0e203548041c2e5041c002c0c0d0411480061151003041741c06409043c011803040c409650b6a18646580d6401120501c4401540300066008002d07910503446602180d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 815797482 1250 815796232 815796253
    0x803070f020f0c040b0111010507031d0c100c031b0b150103090203030403030c1a1504050702030c06070e12030c0106050a17060705070f12090503060a18021926 70
    0x44a44405921030b000e0074806803041e06002c06011030340d081c0350510607c0700441100240034484d0603c80d10043e54081902841c0740f40d40d007401d6800756400035041c0c104085840b075a445115850b11035040c5031515000c900b189090498140050a19015a500a51600805010303039044c00c24010400119000700d19261580190104e400e6843c0c02501a0414401000400d00441c0501800781c02800101c0000b1201e000105000b482115101c1000c3c50682500030b00707040510a9aa00540b280001c500c1c022803d465251b998000502c1c070020800e10070014115900d501c0510003160b40d801c0110382d203403088a1101400380060303000b114002c000e10000020039005a040341e0500840e00c0303019056949942e182210541d1000100f62900b50070588020f0010b40c205440098002c00c50781c603101c22509000400d803c020002d4495054241410b040d1403001c2c400c5900100c1d10717030b41181c90043d0f62141c00c0d512800e8280c0c5501400000406080b03905801c1e18034020240d8080702c4070f05039030aa819 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 815798732 1250 815797482 815797487
    0x51b030703110d020f12030703150810051005132d0b040c0c0215090f130b0316081b0f03060709060207050301090312050712020a120501080705151b0a0803070f 70
    0x8800107541c141c2e501c402070014186c02100d0042d03130001800d1801040e2880090044e10f120986035000d0b00880d0b103e141c960381110300a02c551500190251100103841d0301c0c0c400001d4040000705501055241d50740210240404103078071002c0c1c0c90300b244681091085e6041007450090080380c0c0414012810412490001740c03003207040c1500581e004142e044441c11034400c04400f0b07004540c280e07400c10784442c2000b046a8840700c03403c0805440381000314030085d111041c581001d0444900d103e02e218000028000c0d240041445082103040d000c602016507650300008020507015a074072500341c010081809821382d0f20072280f4094448a4080b245040d40d079905143c01c03203a240d0409400500c542d002800700301c44c0d41d00b040750800c1d0146412081405114500e00403a1b002401c2ca90100b90440004421280940038060040c0b0f11754003d410701a2800011551031400c0031031264090000007241c10780b070821601c030060400e1040080b03402c000340e00e00d0010302c540d0040e03604001280b0240b0b60150b8003031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 815799982 1250 815798732 815798743
    0x218091f1505070b0411152109101e05010920070201050304030f11012f0c0303010b0708040f030501050a11160b101d0106031b0f051b030703110d02 65
    0x1542d0380700c43c500b1410352501101c4a401030000c541c1001c441d0040c90450b5500d6500882861300040f015a4520400025201c141d1024190740380402003d020040d01d204080b44440c2103100c40c410109a21044846d00741c504140e2004e0544164603007400465801040d03800b10040108800380200e500b024106400c03010f001d8004001d0008000304001400684104405c0440d501c640c280701116200101025095543c5c0724030403c254519000c6205604c0c0b0036841c05d07500c4031920401d851a00d289113005507164401401564219200003d204013000060000c40e0001c00940300d41040207038592400c0740c00703094141c810741841c6041c4030070303d21294014011212090034841e81d40c4421456039030703259450f4000070490401180001c2c40054003070340c1c2003039004070b02c642110303110704075070410034007404480340c1002c410114904d00760b50014080c0c100c0c0414441070700904149485080c04011000f580c9020007030b080342c81c00b022500200301034004107401002c2d9807200580361902a02d0500300c0e41c1380c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 815801232 1250 815799982 815800019
    0x9010f0614010f0504030816060e0114070807050c1b0f03160e0a060e040303111b0a0b01060302030c0f0304050715030b0a080c0315100f0e040c150c02040218091f 71
    0x808100c3c21800c404500c0d40350181d20711a2708045400900200135a003180d01c07061801070840e07618001c008140d907008020740d510100f02d0900d00c1c1000784841e19240d03200f411081c1036280341e0084212810381d55490711500402103008044038404081140b504060040c60302c0340c0400d03e820440456801e03070340341c082d107001c0e1903180c017280c00e150f0740703645089000c1d1488040d01d103443c0c40104980c111460300c03101c90000820500c00140740780f00300c038940380d81601390591183e802c142c8140140080504a4800c4404620380044d6103512600c032810031a0070305c03074035510a1103000042e0383c1e04901d02e40c050300104c1a42c0c0c030803500340c80500d0b41c900845c0d4640c070140072907951541085003206030364800c01031401d401400100070140155121205500300350f4454101c16110703103c080c00c010810650703101d1000a401d12092101c2e200e40c400d4406451040f8400c1c000348501e0300070880c220021941807003429600c0c0000d103900c50b82e0510198190106002d10560743e005000d001012807181a4006810041d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 815802482 1250 815801232 815801243
    0x2030a030c0c03140d1509020c0609010b1810050406060e041505101d18010806070f171f060f02010606030207020616080f0c01022a0d0809010f0614010f050403 70
    0x88046003814454160720078003140002c11743c2c4441c072044401100011b0300241c2070048005950700d6840828030b141680050986040d07a04124000d506a10781c0401e4542103035001401d00703001c2c0c071503e01071300b2020340f250412900f0a01d4400d0000b0001e500c404003d941240c25241044101080300c206801509140502504420000c1c85000c0c2c072442426001c00384642941f08010900000d000101d0320809022104a0360074984014004001c05005441e0001c00070700381100030350343e0100d004e48150440441c803540718a0303a01c00100c3c00009106103501410941007498001c9403550400341c03441c1000c01c144401586418400b25400f4042c0c400c80c0c2c545070b0018041c5040c0001c1058009205c0c148201c00c403101d003028011282d509825074040c1c0f2717802ca2035500140e20761400d00301410141049141c1d820080b004c400d003a552644010940000161755460280030a55035220540d02400300302f0130f08011a4900103001842c0e04d1240310b52154454240e076041500103d2103400c03501e40c0118003004c0d25 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 815803732 1250 815802482 815802497
    0x501090b241606090c06030c1803020405040204020d0504060504120906020705040e0a0b090d18060f0e0307150503041a1b21150315010b09040b030c06040602030a030c0c03 75
    0x2038801c500005001c982e0b00c0031030210020700e120703074030310050342c11403c02112405901c0a0511555425018185002015103048503210b40001809c170040320310b62101902496440c800700e4195111030b01107419140041d90140921f04061818800a1000725429140307021030178400c14486218030801001c590a5034010094079040008102c010080021500315501c04c059003c7e0003d509802041e06c03c4141802410510600c2030000d45407003100e002280081018040520100790071900c803940303115103458a400d000000c0d03030110f498145250440e04d214260f642d0104410b5a01100451280c2d101c0d000005078807909809010400d0020386454402034008550354801e0351803100509151115001021400380c1c1082007a46411030660b05c121241507044155080c03400c040107a054034011240207000d10b98944031064049000d1440c0c02c80c441c5480d80800030040c1e504110002444500400150381d403035a401c000b950342c0c0d000481100120341440c54400f503803030241105c00c000b00d4040e2107170b51 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 815804982 1250 815803732 815803789
    0x405060307170703020307030c09060602031204120e1203041a070b220803010f0602010c09050609040b0d0519030906030e0607030e10050414010b0a0f12030915030501090b 75
    0x110a000180c100d40c142d4454a40000003581d010081c400043d409844812091030608443da015245a90081c1c401c1d9030041249010242400f02e40039842034100c42c940310f103846101c0c03003250304a4008090981c03007041044000300300c800100003031040380d0800f04102e1a013400404507a1190203130240c0503003105400030000e03a54951070f00d039a6800941c01030315001c460707031315568000c45a082030704000c0b0013013542074041c451a80c09106a07821500242400ba000510340310004a8910a0ba500140501c0c1c4079045a401c0fa103510000640144e488400e84111005c5068000320860301d511040d4001a5642c000003112802842100c10b48542d140103840b40347e407550703826405005000031074a803e201e01ca801002441c030702d12815000d507119160180c45103680002c0c142c00c2d03411180d50745115002c50002084007261598030a021189a10410035101c94507050a03100c1440e1588401d5290680720300140300b10350b06900440c141c45a241c010481451a4000d0102d26000d0507040c1c016105074500d03c1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 815806232 1250 815804982 815804999
    0x20c0d0b0901140118020304230d09090905121c05040501020901170403080c0307050405180406060b121923010503010513031d040612050105090114041e0807021216050405060307 78
    0x40d684203028510400e12701005046100000c00e01284007007403504525070340400907900c01030000c000e041d207400074010305040741c55068652104201a0802c06000582c0480e102c45100c140d820800c01039408102500d032504019010b9405400070320300140c5041200e2005032950550240900e426a0711000c441e590403001c62035a40c401b41001042c0304080c00b00040391f0342c407034145004924401d000e100d054241441d081d801d0365819007041d241c2e040300313101d00c40e8040b640740c2200d07070310810786230b1090464003560310030600500261100200448600e074070f0100f041655031285040301c0040e0020065030b90740c0398040c1d2555200e40801400904021a0703481e40c0840c0058011501c3e41c0144000780c0c0c103640381c901c7d004564818008840e60b946070f200f0010000c0c002e00c2042d61080d0b07045500c003203514143e075032603503400840b512441c040305030000300c0018011085d041e01c00719a80603007100480b0484203206a910308507010001a5140750402c08a070340d00b014000d040c020301d0094024401c2d642083c450 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 815807482 1250 815806232 815806237
    0x150902180420040e0a0204030f060e0c03240a09060219020f1f1d010e010903020105060a030308040f03022d1603020901090c03180c0501090b0c0d0807020c0d0b090114011802 76
    0xc1170b1041e002e20010001c6030340001a80ca1702441800005400c44042d03840c0317800d201c0441c6007244240c208203800c180011420710b1a0003480c082110004035680c4a43c82c500060043c07070400b41c902803011035032903010004810014a00d11080e021100d9a0203000565552021a041c41e80c3d0035074400f442d00d040c01800c07500040341c0d40354611140c044c40d80310480c2e0745003100c03040b036504092603440706c040009240d028810319401502c1a101d0250250864501504480d03020b0001400076400241c00410316100f03020f032100840d40b2130300640c0d48100030741a40c000268803e0f9100401e0240300c00440b44900340d15a8a003c59074042e040005680c83e20f0ba07094000c0c001340000c0014941c507456024640083d400a059039140304880100080382400001001550340b900040f24101c800c028800b83e205002a003803401040d039161041b0f8580d035012040341881380303100810b5003010600d4080006c05c0403d070751040c803d88070800200b181005410841d032900070b0030320409000d045441210003205159400 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 815808732 1250 815807482 815807491
    0x109060602030414040b092409040c060c1b0605093c04150f03061404030507080703090e090109170f1902031605031c050415150902180420040e 63
    0xb03140030703101d0013146244004482c00b80104a8841c88e076076000d403503010080c1c4000b5040d01c140c90245055035610011450a020f0030050000319401041004450840708191035603400c40349801517600c000c003604503005840300e01c0c81034a1092141084490030340f610081c95070203d1000080b9201e900c0c91181603032010030815000f540b6558040600d541d0640c0420040000c80c4990071143d203981130901c112400180c46074001e004400611012981c080d003990442c0b038000002a5540103207107002d44040c3d070143c1c030400720071800740100040508103500c041e2000e0300901c820340080096040f9403065204210740c107410000c040c0004560030303540146907a5240040e004803407074103009507082c08a80b01c1440301192254130009600101c003412002c807441e041c0710303180144110706041d51074030140d036041146940600e9071101d5a142c0344010b4070700240100004041190350384001d4041d4220f01c024416010b0065050020b01081e080742040b503400100c485082c054141403c00d540b503421400c0260 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 815809982 1250 815808732 815808739
    0x5010e040c200304082b02010b03070b091807020a0c1a0406030f0f1d0f010c0e1e090705070203010513080f0c070302060a0509011209020303032d070c0b0109060602030414 75
    0x1201040055081080b001c80104290703821255441c0e82840c6d51000c514510503004590403c00d26504036100000d001017a0b0755a0071900e5180d20702d10001c1068884c0c100b03c580001c81041f01800306e160b4010508020450042c40c5007001c0b03940711441d0a203c4620100e48524a440c10041004080e1090703101c0d921440d440c1d140400c024440541500986401c4c024156401d8090b0120214002d0208000c5040c070350104000e000b4910103001c05480300740081102c0780103429441c900302c0501c5c50070061410010b8018007000700ca041100d0000c0040d0002c0c40100d000b90301e814086242d01d0000c1500b5040e03a5031018000345011040884007200380c00c9841588000d101700b00e030200060b50303004050a01c03229140c0e146034481c08943c0c00181210100c03011416203510b40b00c500405600c01100300c0e40d112014041c40c41c5401904404030310301590307215250041900c00313030030b0008031a4042544000c0d140039501202490b40c0b1049410110340380b6208180150b4810002040340d89914140040b81c0030004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 815811232 1250 815809982 815809987
    0x3031602031603210606020607120b03060a0609110c0604031b0819080105060c120f0d020d1a1206040f032606031b060403060207022805010e040c2003 66
    0x802d107040700500c105022408100c801e0540810030f035440703c0180306545920802c1c800d252a11102039220000070b0551010441026a4180d841860307410003441214054101c1d071325807819603200e030010700003402409125030900480040c82a010016105034901040c054410f5403200d6906031844216564047c0c0d4032001c0e00070500200f00b042e806082d5a10020307030b200502c1c10306250024010941600018400d08040c0200e90b00b0400c005941d400070b110000c03056980304000750b0301174500c0c013a051515040c1800080e881c0d080c042e042e00300000814400e01c42002006c010b0b010490a01c0001090200a40c80302d8001004550301c00006403a05029007060403d0007110540024a9404524069004081101480541c1c201004400116902210603414654490740050014840c5200141c2480e4011844200359aa40a4840070703c19a100e664403d10326802560b010400b418454540400c2d6503805075025070030305018581144030a540c840880c41001d2110600002800f030103203c092109 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 815812482 1250 815811232 815811247
    0xc030c091510050705010f09150510152a020616030c20091815060f040608060a0c05090d150b06040906080f0d080112150906050117060105030303160203 67
    0x888a8002c4220419076070580d0355261401c01030309450080e02d40c8015a4940384140c0042003600d02950040400840045003688503110789444038182034101d6040740e1780d220001c114854000c8801c0d0200c1d0b4140e42e0846075070b1081904400e00da101104042d4220000300160a03c02084c00745a5080c24889e0402081e80c0c90706882d0000388040c14140300d0090f180c2d0345800c81d064509400b000c0e80c4561901500c0d14004004c800840c1c0b40d0a070201190052a10301d0085100f81e59003501e24004e034070f8050410408c0650f106c0105560340019100c40500d146800c0204030000d100384101d03080c441010b0445820908261b4451400c0100442911007140d40c0e2940d16000e40d0b1000020002040a500041111420031400506007034814035025a613600602075809850381003030742141128840342030141d81d04001e00b0980251000c040703e0142e0307545403070300300c1042040d240e102c1ca040e6200e071031a61454600c0a140d550346e44c503082c010130b43d041d401400003480e90304103c0b800803008810340c4152403d0116 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 815813732 1250 815812482 815812489
    0x9150403120906060f090e1b010e0a120804031209050a06050c011404111309020901060e0604150207140d02010c06050a0b13020403050606010503070e0d1a0f07110c030c0915 76
    0x1c0c0c3d0f0402d00030543c0d180e05c02c1224018901454501c5079a0350054035215400070721007200e0f0244507070014144882c40094045c5135072481e203401c00030040c0400b400504015890951090b9016000840326503002c47d800c6154507200399601410b858015045000403810003009035150380220302c3c9094190340320b00445090448100003640564487c03511071140484460402802284001780c034602c7d289002c4203800580c0d6007002c034504542030f03070800011588801011500e1071042d034101c1d01914400030038400185a0010311042101e442c007511410b10084c10080244032050940301a0008000202c20004603002e0303804660000020503000420002c1040030994910f5044a4040c1c040ea0210b41041800000e010740c541c0080b003407820742d20314078101001a04071003080b041d0302d00070051252200100b11030020f584040340094201c1020307521b400400f807041e24408442d14400180100550000f045000402d0180800000d000e4850320b004081480f034907050003442c444080410451a260646 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 815814982 1250 815813732 815813741
    0xa2316150c18120c15020118050d03230a0c0e10030506040c08060306070f0201020f2818140a050604030503070c120b060f03100e03090909150403120906 67
    0x1080e02c031510a1800881c00c002050410b42c0103000d0000c1146001d000101218120015680403405c1c400c0302080141c800ca0042000c00d060442c090350201056061010004400c1d86051082c0d40a01200b0700c140600d24644d480348a10090720050070011400420b4560041c640d061500d1400c0340345460341d0400516001c0141030030341c002c03e607120148201400c01380a01e5100030701604014541d42421030102c1d544802c0101000d0070800b1104c0620b00c40740c401c1d011070700080c001841d42078941294843d8448109818159000d6025511352441e112030300450141d00030b8600a86049441464440604030070210310380d0495020b101400e0220f9140c1c1c1d50345c050300c017a5014500864590007140750248840300c0707030f41000b1030581240c038481d0009008410410303070082c010354404d0003111103e07010030725010b42c105140c41450b051008803107035201e0001c090100a0801c031444101703a01da00300007a40f150903c10f1114049000240001c01207405006408000411184e00140040c400c0e102d040450303 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 815816232 1250 815814982 815815001
    0x609060a030e25090e03160f0b0c03060f031515010504030b15030f070b1e070209011502011107050d0e01020a0b0c0a0905010e030604060f060503060a020a231615 71
    0x82c8004a03070710942204581a800070b0401c82000300400079000324641d40d00d0082d1044400847c402032800c000300201071241500281e07003d03c8550040c1040385000c416908111011f038040c0d1804803c2a0647c500020303010910200300351941c240d0b480301c606418030040d5181d00c4905021003080300100242c488001c81d0710808030740e41003500d840000c60405042502909100c0e059a20200d414041988117108803401c3c1001c01c2d0f02d0045004564514020030300503804040d6105040500004050240c2007101c0d41412269008005000d2100f01446840c012001c001e40580c0c005d0f01200c0b4664012100c0c9030f00000f0500460784400359540c1d40740780e460350441d180d0b402ca48000c2845521107800805c440702509090030034142007035210021075907030a001800a050107840d14003540b502145903200d10003610001d425a04189403c0120b64080d50120003640005009559441060b030344158000386000e500243e00c1345058804030074a400308124640c00c1d01c40008800795010300365150310646c0b402 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 815817482 1250 815816232 815816263
    0x7050a0803010801060f23010318050a060b010507110402031503060403020d0806060f16061503060603140304030b012c090a03110106290c0624040603020609060a030e 73
    0x40b5030506509a0a49416500c101d10144441100341300c2d01c10044861a18590500d0040307119524640c012009010b000b911014447c45030128a03040c090045510007242c2c2c020001071001e06427400044900e44911070020704228800c51401c11f00340380c00d030001e5070020034007001d40408010301800203007005001d68080b000b60307029407256450550058a2a0f600c00002c80f5400d05001e400d0022112500c280e09800440380b010030001020441e03c0e502a0400ea041440f005121544a113400c100814083c00195000403100d003424100030000401c030b8040d254000314581c5640d03e03181d1a03085009440e8684e14003e03002110a40c081031604448521881105004095280c80782c2400760442921654250190341441d00c10b1180a440361900520454081d40100d481c0048103500b81e414003441507010b0301805420180914210110ba010103410780d00d04030040c1c01d00a580400c011690503100003904407a051006261516007100602187c1e5000c1c18042030b140c103a0076505040c0440e9900c00b11a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 815818732 1250 815817482 815817487
    0x8040e0109060803030403080402120f101d01092402040801020a051902010606230c0304090e0712030c0f140132091002031f090204093207020307050a08 67
    0x75500c1d0501841d802400c00c14003031491400d1079100100150001800a0f006109000c2c040c125900304002094200b005542560130800100742000081c000708410520510344500901c800d010040c0f26076402c19074841c3c0603c1a0f03680b01c44800c44501c980c24281d44103280c0c28800040c3d031000c05c0c0010b01103072002c0e40e111980c41c0030949000703250b030038003000710004c582c540306092000035081040890041d04e2800802d2401c514140000018072512042051500020600282d8804a60441c900f00a003800c190341140b078440060590790300003002c0141c00280030040d01c2000c80e9141708000c000ea802021581d8a28541c038440a0039070304200d5010310070070450610110400640e144c2a196402c0e40c0c1c0d40860107090419441d5518442903280441c01c81e8000045081141480c0f1b40d06030304ac01d04043c10801940d40c5820390300a4109118440b082d9082120401c491522000c0220074115446445890801d02d0324100c03495030001880307101988802c0103510b0209008100c0c0300041c40c40b4510195 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 815819982 1250 815818732 815818739
    0x102d02030105270402090c0f0409150806150118031406240109030b06040207020319170c0d030f0209030a0b0603071703030c09030a0206070b071812061808040e01 71
    0x9101008922041480f07001c10b2000405034820061803600150111508440d039103440c91101224401e0320840340820700c00240026124005402064600c0c0031003c1601c0400e0703644d041d9a445900032941400054941009080c1e10343c040c407040700c0713000c2d5008144c901d205d40ba9a110302c00d203148400400aa50b010303c2c02c0203242e5007581184100424150780703113807862022800180c182c040c02d000041201035850002405038031180d0640c0c0155400408480050803030610040c10003906031001e82c1c8501c055400029000d0911045030415060b07400204000e941ca00402c0b0020162040b5400d104d54003007102102940e406c014613440d10340612042c200ea41400ca040510302242548090034040c1c080703c04080c2d0130000300c140e0354410700c1040c40b00e50380c1d40c5280003e4141107018100a610400c080380103070074020000102c81c403400c000d8482c20340391404030892030300d21a464455692481c210410203800501560045c80d00780690407a50048085281da603070100c0c1e0865000000580d000c10b0041 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 815821232 1250 815819982 815819989
    0xc020c0d03031b020304051c171204031701230a151206050d05071208070b1303030f270501140114031002040e06060a050714011a030609102d02030105 66
    0x31144049000171072030603280c040810342c80c0803014080d0350070202160001041c4100907840352500983c00c00200d5540c4d00b0300b07a125844c2402a60150009001c954480707105601892080b4140c6400303984042600d4950b40010b240e4601e0812410340041c01d610001a0380c1700c010381c4a24600c00310b611241c1c51149800848412900e0755802203108031035072044100840c901040c00c01c16038030f035040c0e524061070050030b00305c1c060b00c56410020101406101007010315088105890507444c441c1d0b41c10f111041002810724240c1700103880c4c0c800c0e410710341c0c1000300c0d0f00880741056059403441070b4004030b1075005451090003c80d200b41d02a1074014042e2005241303619042c05488507503040c200086040c5414040604407810300180410b004280c0042c44980071030040301940c4207a40d001a6181e00a03052902080c068000b500c4113509860440000150360720340800e459203c0c14030030004148407600d8040c0c0f24007910b1822500e01c07504c2180340e0602e0001042d500a06400c80c40c01c078000d070380d95242c0800e1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 815822482 1250 815821232 815821271
    0x1b0109062d02070c05010302090a031707060f0c1215030506042a0b07080a050f0a031a040b1302030406151d0a0b0f090903091915021f0c020c0d0303 65
    0x210712107510411002c3c0002c1c55002d400e000b603480a10303005888071f075281c02249031550a5040504580c25020308041241da0000040606511a01c001c1c400306c103a01855200760f9080c0c050364030104411b0000c01015218130360050700122055009904160740d02d071100d5080030307400c0d6400e80c0c1d003640c03403801242c920070302e405154040e00b9500440c13812503107003031003454690080307c6c1d0080c41c0c59400034410311900e00c55010b555901404115450303540d0794801003e4010300a1100c480012184002c850000b4942841100311501001d00300500d40c10384281120000e50000f04120b0b08a41c0c0d80702400002d0601110100185c50400307100ca2501c00000501500700e84001c00c1c042c1001d08115140f61240c94800e40c1e074000840c00d4504d22056260307140082d0450280b94080e0390045a10003442d041a0b0070a40d51004a415032100c20392040d68041d812a21003441e0343d4200640310802c003154a070f4200c1da9010034103440b201c3c410b4490241c2c0c40c0d4009170b02d00c903000c032099000940314a000c1c12524061400d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 815823732 1250 815822482 815822561
    0x50403140a050d0503130803180c0418060504020301060801090305030717040c0506030a0b040509010c1103090114130e160f111e010908040b0408060a111b010906 71
    0x1c144080507542ea640d81c440d44201100c003004004008520455002a40103a080d43d0003451241c03680ba107081d0f81800c42c844c03440d0b80c01c964415030204121500703052142d01d100c90700c3c0c0c000f00700301c0580f9a1038050162201400403030305990b8070880002c00c0c0340c0a1040c103030a03521035542c1a50324186401c0080c03012801d2940300c0d05a900820070300c0b00045032455600d044640588040b034482d510000b00320300400d4070003260754205081c041017181703010040d4030060303a0010a4654020300c0918401d110703581c0c01a00801404660103803019605110f0410280c24440812031b952000c05407210031002c0e80c0041500d064600311088180f081c00c842e005503801030011643e103041034643d411903264581e03401c0150031a5904000c10100c20002050a422800805400409140d69256200d40b10f0801e0781c054841c0c11058000c0e14049041065940116400902d0f407648081c03c044840002c00840101d0241044056684810460001e000380c06900c40c0c440400304848500485140540d003600070f10304 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 815824982 1250 815823732 815823773
    0x30201090e06010207170f163321060e01050909150403031d19030906020609030f090105271f080f060d0f120f050a0c15021306050403 59
    0x508000c4141d0340000c01004450402e141c020003902c001400703d080c084010b0420100d8064000b0448d0405520b03400c0314102c03803090203030721424500807191034201a08542c0e14007002c1c4541200141b00d921070a0b00800e034600400305840d05544201a013001c581ca00d91020790340c1480040100186c8c6005103000c1d07480310300301c00a4808035082552464800c0c00041c0010141030b60340c60300c6400410085048500ea5945408990700750351078007210b105407009460100c001511452010130300c2032000c00e40d1401104054015814a440d403051360400c6e801040f80c050412100b80079075046d4400910240300e00840c2e020a1044512446c0140316128441065480490b00d110807500002580001541d40c0f0880892070414181c4498001600d07400b4030640c0a480c69010841100502c800781e02c407421071050716220211075101c03d03003040c0c0c1c513801602458004107440c1d000c1c2d031004c07a81c00c411550325042c6003240140303044043c9030319281d040610303000400080d8000c10103004103c0003400c050351240140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 815826232 1250 815824982 815825009
    0xa0801030c090c17100f0b03040606080c0306040f0602091f0908030a0504051c06091208101a090a030c0b0703120e031b16090515091b070201120204090603020109 71
    0x300c000d010391400401c0768078613032500000144403c0c100015540944940604680810358802c8406841e400c00e0f00c00784c444a24013640010300f000c000858144c43d020290280c4669036840d1211510a04120030680d4155020818a4081d640701c001c0980020038142d180c240a0300752040c014003040c0309401a504582c020007070002c120f0f4111003a10708550044801e101080c03404410310420b000038010003492075080c0403078502001080444180410890781d00ca030301e1a0345450301c554400c10302d032140715440314600c42021071b450146802030461910140a03000d03401e40c1c0e51b03035901500c500755001005240005c03410704e0815030702140e11400c0e00a0b00c00700344480c48910400f10740381e11030702c0010b10041440340f0608400400c04c0c007042c0703410f912201d6045034103640d80c50b00340c0240504071541c3c0c07106100a81801c0d414904030f240e8034080c1c0b03032800300107000507511415071545600204099060103154680510700990b20300051002d01250200491207618603c009000c0e107505810551218104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 815827338 1106 815826232 815826251
    0x103030305011e140111010905120d06091b05090112090501050f070c03020c10110105150f03280201030b061912061a030c0f0a0801030c09 61
    0x3908030300c0d505201030403c0f03c00c40c840c0d900800d1440c21594035000c05a512490005001611010000841c0402c5071100b81c5024064800f0300c0c141000014480c041a10038007c1c40001d001c507007400e000604503a0b0b00c01c00c45407050308401c0200032000c982480113a104124401c41c4200c250001c11034800d0700d00b03015020304421511106a9607528000c584002c0c0304036203100c0a80e03010741c0030301a144009420048910402081c0c04208035807258000901003083c401c4d540942802c2060001e40100e08007408543c011000c1e081e032286d045a00000d07a074000c5800301e0740d4505071006440801000030701c0164014a80380c54015040600411103140401d9046c0400000400e662580c00300d054548d1800300980c0c0950044002c0185188040a103005820001d16040b103041c4c041c4030305004201c003c031680c9400140e011400184c00600400500807140b81c00c0d409446080014041c4008 = true := by decide +kernel

theorem cover : BRFrame.Cov 815647482 815827338 := by
  have h0 := BRFrame.cov_init 815647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 815647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 815647482 ≤ n) (h2 : n < 815827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
