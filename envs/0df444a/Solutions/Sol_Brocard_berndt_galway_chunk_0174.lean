-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0174
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:15:45.813871+00:00
-- url     : https://prove2.me/submissions/33148112-37fd-4284-b427-588c78317574

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 31115113 ≤ n < 31294969 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 31116363 1250 31115113 31115129
    0x219020303010f080c01050a030c11011a0f151b0705030706110607020a03050f0d0906020d020903060109090b060d1b03050d0906020106030203030901080403050c070303020309040e1b0105031f 84
    0x20300d604000c86480d000440f90f120003090b50044461100c5e9a0300f00d000d5800280061a00140d2030003841812500003001103540d81c05946004004c4102007412800d18a9011082d5903405a802e0034109000303928184407481d003800b1109001e0184000b26130103084540c0c020a5040741d0969480f080024104812584640040b1307152040707000c00c41c4010701001750301c41c14a00140c0381514540c0c40c0a00701d031003071400600d44a24001082c0b02c40000f20342c080e05050703030484d50840d10740d40da0081d4000254050700103540b280c4030300c5000186601c100c1c001c020385594024035400311501c4180070300c0120041190211040598044507003403d0600881d0840258000e01c018034907890780c50006400c43c04160409411a41010828000b513140001107642c04a020700c1e00b9016541e481c2011920703401014051000e6020342c4000105156000002d060810822136003006580141d8012664450104010a00904508550941030340c050390145a12242e01804145040c284902d040c0c4403020580140308 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 31117613 1250 31116363 31116367
    0x6120102120f060103090f03030c050c06010b070204060806040f08070807120f0801080a0309030b0601020102041503021324030509160806190c081803091503061201020a120b0402190203 81
    0x40070b1200400c0740c0c00c14020309041201b01d0042d182d082481080f03440240034542c5440d603012409100e80b0840d40d4002032141030350703840e5131615801381c030942c0650016881581802d101249003040803480794061380d031101600036195000c2d0350b45521034022000a90b0075000c2130011101260100c3c48946a002c10750b81d03951840c0520a2004d84500d00680102010750711036801100081c2e04800c0ea203042e82c2d00900940520354911300100e002e4404c84d0442080b85010100345400644c151f0003514240c00a62250b10f400d903240c05010107111455854402c0044400862014980c043c0e4000c6401100c108283c2d1001e02c20a0301100109006034800c0303905070f025404210848180103040050424404c0052080301501c0100421650001c0d026100041919200030202c140410850b40f5402010b030690304004e040e61101407503504116006030103108213951024501006208881315000d050300c2b9115240d0800c00548014401c132400950455400c01000325402103804141000d002658001c42d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 31118863 1250 31117613 31117621
    0x170a0b01140306071d122103040b0603030703050a050702040b061314100e0919050403090501020c01180b130b030c0703020d050406021207030c0c080c03070e09070b030612010212 78
    0x340c580200108510100445188680c8400e00c0811352480400e1040355010034a12901002c0c1c0c0c202000b5203407105888400c0c5200042801e5080d016501c11400754800c0f201d582cbd038071300c2803507200c0c40340d220000d0008104000d0005106e00600243c0700b00d0b030015100084540b0103001140d5180c1c0805a0210030700c0642030104510002c14505d1085202e096a900504501401028108034003c1e582d00d40700300b00c408009820000c007584401811513071780000b0b00c4541001e0802502100b41d0f8040c0d5030060240d4041d14410b9401040042c1c1c10101c02018544411302d0102a800d042c2c11141c015114244c01d44c50008220f03200001560241d80c040314600e40c1c030105843c010f494611308915030400d00c1400c1c041001001d4021850000740720b9030b42446a42d4001e07928044402c4204100020203c20f900c4501203041100050030420800d03096046803c00d646501c44042c02c540200c0e00351680c1e6103c5d000511030000060301858201c540600f0307071b8041106051035182a030300010082c0383c0201d8880204 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 31120113 1250 31118863 31118869
    0x9010f090510060906030b01050402090d060c030b0906030a02010917010b0406090510050108040b04030e13020a031d0102040819020d050a030206040c05100234030b04050d02030c0304170a0b0114 85
    0x100f0028010020100134a074515a28200f2518051003814401c95010801c44070769225004030100d00c0d6071060f8100300c4200c0d480d03000760061041540050103240d141000407440c0c10005400c0c0246a0140c640e281e04620f0126030755147d01c3d130580b401e01c840d5268030107090305032100d024041c003400d80755102142c2d40c5004406401c0c0e1a4041e8801410403842c075061101140d05892002d40203901450403100c40105000411620420303900d013080c00d94800201da24107103506d0740c41284d48102c4618403d95554000300380d10300b40c0c0241e0052564542014040d40a628800f082000d2618070103440184003d40640b5064102000c00c601a009030f0082070030001081f605420f15400740408603a07103592110400d000940d101d41419007100c02164945190320900c0860b030220700e00600e95004044140d440b442c09900505041e141201c4038842c3d2280001c43d20300110503a61003050600c0250b007001c0c541040d1105202000c08100c03524020200c80c000070030805038174140a0000390324042480ca1005080c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 31121363 1250 31120113 31120121
    0x4022106010306050708100905040201091a0a0311190309020a090c050c0d0c0b0106050304140d030b040e071401050d06080d0f0219050d050f130e06010809010506060a0809010f090510 80
    0x5c00d50810011000700301d80b40d43c1c0c80b03070140155203c18000207200e0b515440140c445031095005000e69959001a03800c2070161280106900804ca58040c0708244c032048281405001d0010250ba070f1000001c4849c02003880f03584504e840e94001801503c0032962045158109c41e0405c2c15040002e2000074000000c100412000300c01e40e1441c40c0c0301340010748640740c4d1200100b060184200f00040040481c062002c0e00c02c005800303580c0d10f01618210700280c1e070080d0040401c003d080d17024a040260070410004003084c40811503190881d0018140094401120030383c1c00440c0c00340101c0d039074600c0803030f4280c410880580c105030151288400c001d07102d50060720300180c40c1d50a03002401500e81e1040000c402151002c2c515189045c9181c4803102c1074223812090290400c800310380154a01c0000c0c00392041425036001d00300a803600c00d441c0c0c8074504150300743d60003158100d4010a08001c40d125130341c4914a9560300540c26400000d00708502d00b00300050325404041a9800e610940c01c1407012012445 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 31122613 1250 31121363 31121371
    0x40f030207081204061101090c06020304140405090c06031305030301080c1c2406080114040c050303070309140609120601080d0e030705040b010c020d03030207060b04020f120402210601030605 84
    0x100912801c210702c3c0f8400b50600c1540191010040800f040f194194025000740c940c039a4404c0003403030035549a0200135980d401c04d1041c4000b50500d560f1034106401c05100e01405003400b100503204610440c000d20240f40d002814034503075020114901000b00b203007400614007a1148601409d02010303e0301c100180d41c3c449280350456008010001c2c0e002804441030314010051080401494010719803204009019030b034805901d030350130000c14184107102d240843e0320651160500b0304400381c492040c5a600d00441100a000c180202d5081c0019103000030a001c061800500182c0742104000c0465416040d0350700d840d80d140c0c01000107201c6203030140040c200c804103524101811605840c0001d9954009109050285584034400d518030f9101d1201c1c0b180058001d802141981124500100254410001605c3c0c461910b065001c503071500b4000c8441400726401a41c0c182061140d034800c8840020700102da0000b007807000340900c0840c00c1e9500b04a1a01030000e0000c035851428101d081d035200030 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 31123863 1250 31122613 31122629
    0x105070305160309021f02150109060501120b04061701020a020d030b010c02010e04090c080604150606090303030f060807080c011701050603010b0705100609090201030e061b0a05040b03040f030207 86
    0x50704001d100381400441100d0310200b46004075075040d00c1d00109070f07201032158802c0385400c0320082d143c40803500003034596200d01000345d12040d01d03030f40c52650342c0440b1100c0c0500341c0098911088543c03183c0068100940c0c0c9000100700190f86aa10380a070148121504084a4640d4020504426164041c4280040d42c03a4901302070129240100c0020701c8004003183c003c0c188801140103881640792580300c0581203501205103805640c4441043d55102412541116021084812111a9441d80c010042124207d8440030600d07421603a054000e8280007081c5c10060f0f0385c400c0c00103840740e03081000c6c0b4020808803000c2c0c0300302c42307a100c00180001b10131010910b5400711030004102c2d50300d920302200e044800390360405841c0c0140d860f255091610102c411410241048004654402154010800f40d4401d8904002480ea01044642ca40c0011181c155224102480c1044d0106164009086011072450038500c0c0c69140c1c107100c0400d070004d980540d0a400600501020550104541e001808405d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 31125113 1250 31123863 31123871
    0x4090207151401180c14030106080103050d030c12050408090a06030b130b1c020a08010e070509090c010905040f110409020c190f03120e0307050a110a030c0504090f0b010b0c01050703 80
    0x4050210130840401c0388502506a0311601035840a114282145503101c1442441390380e540c1d141070082c000c1e00d080c0026103d6000700000d600410703000b4840e60790a40c542c1e460340c8030700700d560b0340a45c4014040200b040d94819002c00c0700d480c669035468615005044c0e680c07030018000e801e00d4140031000241d82100040186400c0240107159940540c402c02d104640e9040d1030042040c2c40424031040f46503014091a609100321040700350740102c0c800098400942d201c004503625011800c1d520a00d090300309020800115052101d4103141d004840403900350400810007918051041015501a41c042c0440c03c0c1d0200f481c424020f014045030303042c0c46006201e0410f0369045d4640c03020010120360010140708089051206000807138002d1041d185e841800e581d02c6691608103a501c8014006003100c15003140c49641243d450003140000c04c0c0c80d00001c458a0082c200420300c0014035002009036a00d920b2000783c00002104c940c50795029040380c1e10615210700e80e21750050b00b5980d02500302e400b40b41c20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 31126363 1250 31125113 31125119
    0x15030703020607080a0504030203060a0519060303080610030e030a020f010e030901021002030603070e04050303100f0b040501051810090806150d0204050a060306020c0304060207050901080303180304090207151401 93
    0x2d40c01c2910074040c0c000d55200d96900c0001e5040e602446a079100039014045d64081001e054000d1384528800e1146e00c100070307940c0705040080821103409000007030200c0d9040d00803807941e080241529002c02064200000c2c203008004a140c0b0b150061021140103900c60394481c4015042805107481c0828540000d6003418a5800042e40348c00000000082242e4040300140d0a5a801c1041c080200f21441c1a2440c9040c01c5c108241c480c2e200300e81d00c044071071600a00103880b1042800b031004890407401c030542420304110044400f42e000d10034002100d101208010039030380d10002054403072320494454480d0030f49890340075401c182c0002c003440a50309409103085c80382d4480460300c550f2994121800203c503038903e92400000c1690b0740001d828144003040700d00301c2503070000041c4152075040d000c660b000c90b0365004100441d5024001c46030280c00a0020464001c071081c412203940c80104141da0406031280141422600b020b0b1080d5001c4000e00e42c8a80e05242078403445400c0062034082e0892581 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 31127613 1250 31126363 31126369
    0x40e010b031003020a0b1b0a0302190614090303060112060b030106030c0507230c0d02030a03050c07080f01050a06050108090d0509060904050a0b0a06051333081503070302 75
    0x4052044010080000002035007111121091502031540107220303191a40c0c42e49284c16894000b40c24500750710fa68941e4070b0b140100e000603218440c80e0305500400c3d9040f120050300144c18101c10003242d5403a2118140c1c5010311a01c50b9041c82595410015a140d00e4203400040000340c1114200e00e03994074003182881104036580449055510030300380803600003500542214148200f01c005481da441c60b0907011212640e900e5102500e011500440302000c0c10001003064010303040e24000d501d54003d00710500024015000b401c011024041550307540c80d81e5401290404264001c940b805942d1002000448541481010094502840c1044e0203281088580c3e640da00035404c900140300000c64a05c140c0d584c0d0200711645900d0140c4144290b0920200c0d14007e800da2407461403262080d140041001440741040d030f1030954044a110001903c0d10300744911800c1d200071001c0c0011005512034000180315000b0400362102030350f50400c14034001c804aa03800440721041c51103900704001c00c0001d40d03 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 31128863 1250 31127613 31127639
    0x120c0b0705090a0b1305040b03010c020a061d1504030801060e010203090d111c0515071202070501060902030c12060303040602100e010207060e0303040b010e010e010b0307140408070602070b04 84
    0x514203090103039a844007007002442c120740590001c1c0d0030104c009052603080a421820504543c2c00395018803118408400b0942030b40e5a012060f00182e200d0020140880e682e900003201a804140ca05030714280b400030340301e007003540446c6400c1c1a07584032001e02c010158003540d503d004005c40e1030040170004a84000030348900c903880ca0030388a1482100c80d4010301030790700c07281d14600d040140001001c000b001c0f0a0303440522941c1d8140c81074001c503408880740341c03001d4000904c14083d55450101c440700652280700290481003040e10760790b59440d0003040003042031004600540480c1c2c00e03552198040a4800e090400c01401c0394004c1d001403000b00521a00001c0ca407442a10341c40c404a0900c108988107402401020800f600031070034030840c0d0030003890200c0214000c602500901c6917503a292184011071240a220f6a40d02e2482000104803c110800c0a181c00400601e40350691440c061100380054015800c0041c96402c209400c002c0385d40c04200100c000e010064506080600c4d00440002c49 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 31130113 1250 31128863 31128871
    0x4050619050601170702010f0618051006050910050c01060608011e080c100212030408070b07030603020112020a03090b010f06110f0a0f05030c010c1724040b0d0204021204120c0b 78
    0x40800e2a011a1750a4001c1d0031200e4054104c5004010b4117642d014009000008408500c0c481c510b01000b0840d01c00000302010190760541d02c49510f0301c2c01d144103011500d07a01d52100c10070400140180b15000704203000b000000c1c4030550b5400d05030b5044c42c1d01c80280c3c0c01c9144807042c00d54241c103420045001c1c04a2a0a0300c80d00842d0361481c203030442d407000d03030034a07a45000c0f20104581c00030402041000c003101522920340100c407252425915542c064044854900020f808210346141d608c0b03403820035400414056a0714a4045412492503a505144e00b4080c1c014900c0900c030558140209640840400d90f0300508100a1801c00580c0c501d1031b40300c41d0035000c0901406008964041400403c008a0f000da04030500204844040c9180003007080300400c90358410010b5920120342e1441c0500703074511a8009003003124807020503840c200002804882c10342a0060901d010a030b001d43e0b102c1c40030b4142c0da201c407074542c10b030f9103041e180107204101204008824000010b07991070108030f142c000d243d48 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 31131363 1250 31130113 31130147
    0x1c05070e1507080c0607030b01080705041505040e070c060513020f040504020d080c0109030e0d12030e011b0305040b010518010b07031701030609020a0603020c0d0e060403060504050619050601 84
    0x12500003980c0030080c0740b00700c80b0003a0050000103260807101500165a41c07007000183da0400140500000440300b4001c261032000000d04140020703c1054404001d0404107162030909030b18240d0707140044003e211040b1964800303d014801401d0902c01140507661b0700019075011021900e02690000b4821103e24941900565541c3c000504548898518512403a0400c10051300c8804161846028003208507040f40020705074042a412030410004010407503500c501c1418143c0c2489000b10005c1041018030401c941d210901c10b000c4240005030500321444070f581c00306142c541400c040070072880603030110740240c00b4007100903441c042e001c00003415541000c810554600850904480e05261700c0880042c14a5940002081001e541d1000c90b0080c8241d0303e60004a640e0b1009404901070700c1098180c0e5004a0300b0510954800d40483c85d2044006180504090f100c0c0c42e5801142c0c0102c0341110254403c0092005800c2c90b1501400340c100b071143c041c803040c508a00024400e40901a00d405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 31132613 1250 31131363 31131379
    0xf0507050715110f03040c080102090d0f06090c060201020c0f07050a030b0403020705091303020d020c06180109030507151218030518030607030b27040f0203031902031c05070e 77
    0x606100b442e080201c443e07100d40400744d2503480c00c04071002a82d1055504440904c4240b2000816500c18001c1d10b415020061510002401544441e00800c000c0c00701181c03c41d031340d510480001070b80482c4403005060709070300058850701010f4240d440c000e00b04e90520895803001c0303070803c075903501c0c2d110450560307034401c1004100d51181d2a00781c0c50074426400503584010f03c07400b04100d80008001000348280654201c56400d1407804059884810301403d00350001410040080000b04000382844440810300d40303545038aa0b02c2e1a51800e142064000d24008403807582c00818280d48030a4408552000c034074204842540010400c1001c850309000900303000700840c00c095903101110400940c404003906994407031400d01d10040080118505646c851005002920103264008040b080d442c03d41c85007066058903647c0703e000074038420f2801243d142c441008201c06036403a102090443d0b842c540c0042d900d4042c040c0c10485650020100c421040d4902010045545d40c03240e003148840006440d110 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 31133863 1250 31132613 31132643
    0x3080714030c0d0f0906030c08060910090e0c010f09080a060506063a0b0a0e090109020d1208160e0d0305040506070b06180601120b0d02040606080a0f05070507 70
    0x40d00394040c41c80c01c103129001d1052a048210380002c1311000c1311000f6030759040d901c1c1d107603007084e0212030340d03403600c0000101104002851401e0007200030341c0125540c00c0f1000c4055a074403c50041d20b440824900c0d0b240c004055030400c81d6080a00c1c0d100c040d43d1402c0a0b9a2141062a519956a262500503101c240c03120003103001d039140c030002c4038001c2d0344441c910070591600c03407100c0c10f0ad0190321180011481c8501060b80340c100652040340b10b07001c8010b044d140d00c10b10341030740c44880b408054031240309e956842c0c880301c0040c3d0300d010400f00414030403010043c030101c803904080d181e584c00600400440000d2501c4246007a400804c5041401085404040c21007850400321800c1c01640c100d5a0885000200700040c000d4100d15903226000031905074482004071442c4541e00c1d41e0945055001c124004015904034000e500250303101b00000d0b00e084905034086d0001000e981081c0e000f50080703800d11050041c0e5103198096485044266003043c0322606100c00b000b030a030310941e8000707171101207082484 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 31135113 1250 31133863 31133903
    0x60209090903030118020d150306020319021e03040602040519080c0d030806040515040608010b031002040e0606180d0f0203010515011d030307060609270503070602030402030c030d080a0b0a030807 86
    0x1018500c08030f08d2004100c01d840b841c01000940c0244c0e2844011009501d0036419a11a03000f103c812110b0990300800842d00d698804607250005003080f180c25400748000b088a850f002541014102c2c0d102c9810051494139209509010b80d0701c40d2a4050650648000003194004201540041003075400141c203075500021401500504500c856006060600004802c0415000454240381c101c090343d0b031010305440302e00220f111350f10031020711080c00e000244291900d003018249543d00d83d035000f90039201d9040086c116040d4100b0071621080340800b08400d604003445502e60100041c500092140103010029140380d2900b0350450800c4a1207802c0c0065071802c1c4159001e5030307440170050107041d841d5200b42000d070070050012044240021926289030541101d100d2030709804c40040d5107403e0040d26458041d50000304242e0f094450541c0a810035182080345141c217011a581d500e016040120800c410756075000044c510030824581c050010462000807103944a620600c1140381001c00009 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 31136363 1250 31135113 31135121
    0x4170702060c060708071b02090106031805010905060106080a0b130b01030b0a090903170106090b160f03030603020906060705060a020705070f0b0406020d0801080307030c05010b040603060209090903030118020d 92
    0x30310b11030b00a2000340100b0641125415000741500d032210718900e842c0309690b130b0082061000107588102e01000400546000c0d52156150790414070308030412501ea901c655081d07800c42d01c000c0795560700ca000104000f903400305e9082d403c1000044240b21aa1602c0005080e881c803034a4000171103035442020050a81c040d9014030041500a0001441f40382c5d00e800b03807001030400a8040d00842c40382c0c080b58003010f042100e040e040c0e48080d210ba18919050081e0348020307403c11005a11504002c80c800d00200e400c99480341e0a0500c20f5801182550031803051050300940908070300d0091400b4007007080000c1001c07945c903038000d101d5040107031100941d0400394a03002c510b51002c0640c0c44010000304220303551900400544030380b03408844030007170000d5003210700200910032080140c20600032480040d10460351060f0081c003800c008507030101c904001600b16041548200c601d242e000031140e2141c18910684d41d4044d40304c0001d91b0556142c2003040510010549604030020341c0040d15000401160340 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 31137613 1250 31136363 31136377
    0x5060117092404060501140d0f02030703080c1f0e0316061104031202010b0a030b041e0c06030204050f04060305070b070f0606230a05100c0507050603040501140c030417070206 77
    0x1c0c609400b21280348039400390000341c0d002c0d0781e00c509020010402c4001300c0e54410401c0c00c060318000c40702d0071a4036000d0b01c492020804036458013481c03c000011400b60f17009450951074620181c000d1168120301a04121034030320102841c141070040340441d0440100607264241c603040c5020310300150720b2520038010804109100e0304090302003000f20901c040c4200d1002d404003241c008010a01c8140e04000c1c07100440e12004102d003100d2030000b00010031514480350802c0b10281c20101201860b90b91480402040c3c000100081d03011404120601d4a6104801c03100c00903141000b4880c19612559103c035401c5c081c00e1b400d20b00c002400410000141c1c1e903012866044042080000d0700c401051668202c60307075440800c2c8048030318000076403400c0180313031089800081000440038600c0d0015a66040c0303504081e1501e0040100001d8240c90701e1006510641c40354000061100d1070900a07440d58201410724014208240200300010301c1030488007000d0014196003036291011440000d01500c5150 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 31138863 1250 31137613 31137643
    0x207050301060906060801120b1503010207020d03270308030723040902122202040b030705120a03030e120403060908090d0303050f0603030a020c040b03070305060103030906020c040506011709 84
    0x1d10000d0f0b08000c0f94400000e9079419035074170030b2a1b642c0c1e2144032042c024000c0d010f0300c140480000f190041310940010000e16802500160411010750000340110f00c0244065001c04c425003c44480350340d8440c028030f44101d9060000d22500d085454480450200900315400c1c041c1604130b0748004504401030160040c4000c20701651603854000c490301942100c0c10136101101d2100c04502d6400d400354003a02e06810320030780c01c41e280d0072036000c210207000110381868050080c843d01003590748a14078802100c8030b8802c000c05810095250040c101e5480300d00060058000d000b011410106010071101102c0e0840c4021031413811a0920451910880500980c0700a00210440030182c25401449c0324070160030654280d5034942041c95181c0c8036201c081c00041e00042030016180c68a548001c5c0c02039006012140b85c45d444c0e6460a20740b4a080e0001d81c00b09052000401c2056030421400d4991002070320144041d00701640040c1210a00060000041000070001284904200408a1925140 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 31140113 1250 31138863 31138871
    0xa0210020109151128030b0109180b060912010e150601090e090102040e0708090d1b0602070804030506040302030705010608071212020c0604270c0e130e030a05030105040c0206010503120a0207050301 87
    0xe008140030610b1720039000030900300584001950f0003415200111180041046115909103210380018414070721030607440241404803c5041d21b0b20800030151440f041c4c000224464540030b03807490000c0c00c20b07203464000303c80010400d0300e03640044040203d990843e804d00361070f20741e41c5003580640100d410111001c0e07140c000700100f190b8003484003402001c00701d0a49140c0c0740c500300c0071111810500c02d62840030094220080002e41303198005c1c020740d80540c02c0d01c2c0c01c00c1c0c0c8070b5507003505110050f00e0540c01070780003140301d40a2180a114240040680800402a141c43d0814001c1491100c00c405820b81422401204015000b80800056220f004110581d510380700c100d07000074070380340c2c3c0c80c050a031458103940c594042d030081c807902d520b0a845449200e00d8440340300410004000300825401643d032649000d6181c0e4108102400c4624129100d60340c40358100001d21003120024109030007198044001081151030108100441d491b03003d08181e501d1040d80c40681c40e200e590347c40680c040d0700e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 31141363 1250 31140113 31140157
    0x90204050a0509130f11120105040b13030903080c010203010f0f05011e030b1909060b030c0315010908070b1803150a200708040303020c0118050103051509090a02100201091511 77
    0x1114603d54106c050454248240140f041b41c02402c03100f045400070200b40f402008640340c1c550201c0d01000b40b034820720380007043d00e03100d075038800c8580c100e22080403090b9004001489141800ca6208001d8003a1401141401d40780c0000201110581030011881030441c00c581031080d80f0071b41090030b80c0140500454200340120f815a0540034892207500f5000c0e28110b0042850b030601021070740030b4120800c80b81d007151501d44000c1c0076044024001810300c10b036018005000e00042c000540281003244174140ca0b00c80007480c01c01c1e07031030313107a502c0c0d0b442a000445540c2c1d88a030303161401030300300c0c4500e1000114910041000c407030305d407614406081c2e0300201050102c10050a10020401d032407207030f400c0d5142c11031282e00541d00c0a68541d0722542c00c410180d4240490751181e03000ea40d010b201c2d4940d00c1466540d00000c160111340a854001c0590801c1da46e640950801c2003036640350820520007005803000340e03111000003980000d101d900407515105007111200c2c0703080c00c0c3e0305040740c4440c0e11000014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 31142613 1250 31141363 31141373
    0x6020a0807020111070314090102030408060906040204270311100204030f0219050108010605130909030302070302010507050307050f1602041407031407080a0216080c0a020109090204050a0509130f 86
    0x110403074007240103600b0700c0310801403e1100402da40c080c0354540c454008211001e440445503070010248107046120038031000903200350400445000764070340005050b10b81428014003041e076144162203481e101500c1c0f00014904500b40d660280320350540f80071071043e0f580303d0501e82402580d0405d0b050b8180045000701c00c0c0202c40e04106032543c421610b8404d6202d5030010000034a0b62803082c07031301003007041004010050140c401040f815003001005035034103460315810004c0f1030140d0f4042d80069070208413801095024450365410410f281005400c61070035000040a078451812401142040415011400700507290600e1003660300400c00e203d083c128443c403582d00e107404c071400300000c0c4c1032004000c100d0110044840c0601c0281e40d0b00341840e43c503100054040e43c460310b01c640310401d1040c0c1e0440881c1480e0003038815450071001800d0090400c3c00010800c0c10980c010f021442e1040104100c01c0c2c0c1c800034080c0c21194140c1d4240903956031180308200c1121145c0003c4e012121061210007008 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 31143863 1250 31142613 31142627
    0xa0905150a09080109030507080f0c06010b1b060c030106030f0e01020a0309050d0806010c06050403170708011401021216050a0b040c05010f02010e0706030b030c060d0c020c010c0b0f06040906020a 86
    0x10700c1594585110707980e142070b20b0b800e942c01c000000c2c001c2002042140081007001c1c2c000d04d9070848400b0b25078588072469410720310f0001c09074044c503140d88002c0381c850a560b403070a0050080d0369560303000f0500740c1401001d1425a210601c640300c20705035a01a0a809445143c1010109490110085403910507010018000e01841c56003115940589250014418000d984071801000c0607542c4d221303a880c05684035401004040c100b0f4043c842c4003039020b82a441e001c10202d12540c820b135100b14031545003c1c11808050180700031181590001c400004407a9014415102e0313181041601e1250700825042c55410109130480c05408100c40c00204014401c20403413560455a00303990301200025503100c101d08031000001e1a00483d002004c00308581c80c829042845c0c7c0150050503580130441c21800030b001a408102003182c0d0a440740005542c061f01440403481016080c00e0070341c0d002c852076556911903000186090051201000419040e8540364032444580740e00401c11580d4460b4060f0151841c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 31145113 1250 31143863 31143877
    0x1b0c03030108160303020d0818010203130302060112030c20090705120a06030f02040c050409020a03060e070206090d05131203020c090a1104030b04081201031b05061c020a090515 78
    0x60301c65070030030b6000f5a4809900d4002c032500765002d0009120420022a61fa400140c00b02c0c1d8a245281c80801e6801408e20041d1300078a10141e40070380b940b07000e29020742000b505a02c081e50038030300522620040385d0880d000c2101c103a40010307200344140800d030640b014060742244482d001240c55040000300c0390040c9c01414040804130011641350344105000d01640c03060f000040800c1e038581000c10041c02d0541005114040b141022070906455004004c01c980191240d800040c3c1c81c1c5a04004411015680c150803818030f10180810345004c03145203603200c00c0802040c041040c0081c1026250108000005c05407544507510070040246041c02940c034140c00480500c00c00303a940100f940144244908c05100050b1204682894956102d806220600400903504e2090400c0300c102c00b01c40b44c00c80c8a000e9449084031001d800118001040310703810750307000b8038000c02040180303000b01c0c0300d0b03061030420031b150880008d60b644583c00d40440321032844e40c1c13001c0d400030000e140803030503400b01402030524 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 31146363 1250 31145113 31145129
    0xc070806070801092007060b0103060504050a0b04050903070206090d03020f120a02061008070605090d060501090903090902030c07110f0310021806040b0f03041406010e0105010e0321031b0c030301 86
    0x69880700805814500c104804a0410020200646c40004200e40c0210749a01e00c141030000b8071179070343c601140648501303c1d102a0140d035201c0e880a032500e001d00c10780340c10102c124021402c000e500d03400700300c151050600c400e10400c81d003403144040604c01c1000450350141e620075520503a016400c0586590880568000940154000200040d50101600048a40c488002d10400b442e021081d07449602c0620510381000c01c507a04c1c9004075072140102d50003403114180006c0e01071654100107100031225044800858010801c0c8110450404180c40040d90400102c0c1000d50407100001d80d0001100103007034050103680e103456404a07959018044007001c0d4824928175241c4417081061500c0380d405000035074141400138481120600f405154414446d82c090341020384500c903101c1c03401000741d014088080c02c000c0180129607000c0c00c07282e000e0350300307500400307840c0c90382100c11110b0b42c081c04800888a0010001a1040c6089160784400c843e000044c940e81d040200352558803036009001d0351503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 31147613 1250 31146363 31146371
    0x1e080c0604120201150608180604120f080403171302120607080903040302030304031511040e04110609100806130e0703020306090a05060a0c02070510050901030605030607050403080c07080607080109 87
    0xe0381074018060307038032914140035150300c5d42c0f41800b10030f850920000e000c4506000142c0d1071020a50820410907004900407544d221800ca05404000c1404642241540402118209000c0000d80002108003081700628510080c1d9941d40056881d20460740c602a6110003070200120550402203102c9009004980c0c80240b50360f60340d2401341d40e1344510310000f900741d03104020400214041c402807140d003104100000c90300410b4401c3d0a040c82c0c000350048420350134404203010402000800c000c0245409450042c1080344500001d511000507861000c1803090900000d0411fa07100260310701c0301c0004e8a01000114038445d2405da4804890100724041d10815011400f81980000c5c0c641c51241d208004000c0d0766594401103002d0249103a0540c10b6209512002c241507940c0400d400c4844903581c0c6058031400c0c0800010b09454055101a01075000035051280042e407060484040c3d0303400015003655500c0e00000c1610305800b035400074229000700d60500c4449079001222030704a445400d4140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 31148863 1250 31147613 31147643
    0x5030909010b031501030c1403090c0a0303080703061e090c200f0613020d020d26030609070905030c011407080c061807050a060f03140a050601030c0206060d1e080c0604 74
    0x2d011940c4d403c2c100c5d008903800c0411488450741c2d420046074000d48ac601650314008000700410144621904120040b5001e8010808201d5251281200500c1071998001d0410b206000500017440346001d1401c46507150b44481e0180390181c07035080c1d00c00965288095010399808515a11a1281441182d0501441c000b01e86489810011000803540003000f4400842941d801c00c040c440e041031040700c2c000064030301100e00c4803003907240480800f5501103107596441e00d40d08001410701c0040004080c425000414003103a100000c00358031580081c00c28001107441d84000d118a401100001883c02e000001c3c000002d88d40803c8090150907100c6c800352280300300c40da200d91a034005004c0c09400008034801006280d105c1c0020810420450500103240d41600d054250701d203c08a0746811890f480b0310902c145540e141c40381540181c1e080c400341049041c00740004030400c5040d035000c2c04000b0a0a0342e04442c0b04d400d0084a10554082a1070341e8a05900c2c10103626404204e40a8804c000040446 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 31150113 1250 31148863 31148867
    0x20d030506060f031b030708010f08031309020d060b130623090103090212060406050103020f010504031502030405030c0601060206070e0a03020d06050903041205071e0f030f05030909010b031501 85
    0x50084200030b156a00300700d100c0a00c2421508010300d030a600000035406038051546503801940181020760f10907100358104400482c0156290b4043d040941c01000010038007954004071605403401010050f03607071589803144402800d803e4000a01021000490220b41d2014000040441d90300b912040e03613020b407000000c042100d5580f40c40000715000c01004402e58820b80c05a2a02c03880104040c4404d46210402450240109c038110b510035540c10050083d46080100200c50324001d2070014076260840e42c0351002c280140c0c000c01031043d00400030604110041c400d071100c1240e0807003156925a91110b00951710f460940d00c181c0811604100301d0028180384120300c05594000e403100c040f41800d0b95881d4000c000042c84a002030006010212ba40002c3c002d103d071302140a40c00074881541400d500202e0540c04420b00c8003038075520101004142c180942c61004c0725000f8828440781d52080c1402c500707600c610740303500d90702090700d800103d040d64402001d540691b54851081c15103a94100c01 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 31151363 1250 31150113 31150121
    0x1b080f1b0301020f16060212040f021203030c0406180509100e060103020403080307081003020603010906060e0d0f1410020a0c05010b01030504030516020a0510110f0a12120b130c020d03 81
    0x400da249008209550f881c54175800c508240302e03c1500c0040c41c1518110030b20100c55402e440885040140200800641c07401c12000136001580c80051403450501030307610000c921581c8034050a02c0008070078400802550404440200009040e0a002e071030711031114403e420a0303026130100c1805180105456500c00d1081c2c2d03040d40c0c0d0201199255445001095440200c010110614548417010200c010b0716030601450080210355004984541040ba003d89003810b0076954074010b04100c0c01d1071020030303812140040c0745500703c0d0403840c05a40021560b4200040d030303c1c00444490000900e41c00403a44801c00000c000c0c080d1008111404a9000440a540c82681d026000450501402c100b05180d089036065861005294907912590340300440c1403004089d9403440401c0100c2e0164801c0300d010f01072108402091005000c0c1c1040c15566280c100c0a007499030020050403e200b24408980c541c000e11807618010a11107440e0030000001002e4140000c5170001070184803450681c860080c01 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 31152613 1250 31151363 31151377
    0x102041a0f031803090a091b080f010501030506131406010f0201021c0e030c0f03220806190902030619060f05010e0d020a0302090f010807120201020a1b080f1b030102 73
    0x410900c0c6468070f00090318111000754114000d400304104940080c0d603032121040c01000090301c04191380c064141e0410348000303180c440c1320500207104100414094078800c05419103c003401d001400751034a40215240c9000d413640030424503e480d455640212080300100c3c45205c09a0f12165240302e0a03000b24240e00842c40802c104401046a00c0c414400e99003100542c9141042101d0605030fa41401a1822030140f21140f8103810020f0101c07041d48401505040569400c0101c0c45502d2400702036650300e2600407c8044a840b171103e100103100f405800000e42d0540080c00c403000e6040004131000501b8061b184c1e140810b1030001300140e680c2000c0d002c1802c40303d050315107940310104881400300e00c4c0740b0402d007241d021900d0b80c0c0c0800181d42c0c21040038011144012001c40c00c1d81000e119922301082d9400010890f0f80110100d001030ba80003821004142c1d2182c0303c001c081c0038000d04140e00303240c542c00404450190010980305510000341e40b80400b8400703c1c811034011a0039050500702d100b005 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 31153863 1250 31152613 31152637
    0x110607050c0d050f0a03030e0106080c100309030306030b0f0906072a0f0b0c0a12020f090402070507260105011203020a02010c03180f05010305060a05011b050708010e0102041a 77
    0xd00729400515000740741d012554000c20595164a100e00c14107428402c80c02000c402003651880f41d06c0d19520244100800b8200c100c1c024030310850508005007841048690710b03410035440b032014004062182d040840116844210301240e41131080d00309030040021591200345209850004038164420420b011030044490303020070041c0d020029043c507800340c10070142c5110000301d0711440000c0144889901c66003441d00d88507226616014010103d0032040d08d040d0340c5074014803035494084410421260701050440c0e005950300002d00d086418015141c2c003902886080e9010030310319481c6800004044a80c03078000300a942c4c0c80d801088194801c4d07000150060b407100802d20700550180e0a1044824081d081404500700c040c2d441d100400c034140c00245005003194030410071543c040c0581a005841104c4003000c0c141000e0000700710114000000f2121281c4182d40000d22000344030b40307006000184001d001c02069800307494081e52141c440d00d8061f14420181740301d010b48090981d0091000c40d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 31155113 1250 31153863 31153873
    0x801050405241c0210031d010203010b030c1809010906181a010f02031204050a0212030c0606010e010c0b041a0105010f0c020105092803140304030302031210031703010311060705 78
    0x1414840d056034021500f00c00c0e070010b080308102580c0c0e2184500501603882e44c001c90385401c14602c880071181c030a41504090f03801030005100b444c515600ba681c0c49155180b066882c1c0094008404060407414816600700d034103000041610303a401d42041098580100d602d84850840b0f0201030121512826a19805428521b8070041503108001103034460f80d0510481c1c2c10b1201540300344203260020780c0c080f682d990003441a80b086040110007071200038403c0001d14140500c42d071120b5110f00c0c000f8400c60401c080035422011580c0680000c1880f1038000c640070400f86054941a80540e90001d10007a81505200c0005503541c0b00380f40c2181030150b00d64800f203040a085c1d005417407a0308000c031040c0d44041e090060110700001c011980800d80c400c4a40c1109840c50341c10710440c0103c1c11412405c540c4c00800081c00031a0300001101c0b6801c050021050041e640c1ea8150340350308486400050203010140c1d04140030010950145050305c0c06082d48507903034030320182000140d2103110710003402a084 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 31156363 1250 31155113 31155181
    0xd0203090c0a150c060903140f03010e0a0203040b07140c070e0402040b04060503030f0304050102070609060203040204060504201b0102040303050403030813020109030212010e0d02070306150f0e071b030801050405 93
    0x219806c004112442070502c005108101c0e05d25041d607801c4000300390300000f008001080881005880d058104407600411032550400d0380340c18628100050002d410321076802d2550011810280440d0a014020010755040945503509280701e00826101a44158200307a82c2d59054509403189400301d410003401980f52042c0000d20302c1b066080248261800d560034040b10b40411094018103502c0c3d81326040043c0d40307103001d00c1040101c3d01c50342c000500862801c0d10088201c502540140c03c892050010381e5202c0e010500c281c10010140e20f0010450b50002c54000b040607000381c0900156803103619108403c1d511280c2c46080c00041500c064005070400030108090b080c125041001100303c08004a8941d005808041c80c100c80f041d525401640104010420301c4031911a003140700300191803814443c0c1c50510075028482c01401030350078902102340071074032540c0641d01c9042c3d510340c42e207042121b40f4042d0401800c595403d10405008030305200000e454100410744103031040010341d083ea090044 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 31157613 1250 31156363 31156373
    0x504020a0f26070e040f14010504091e0804030309090b03030304080a0e100809010b0405040b0408030702070e0a09060c0503060d08030903090a080307051903020606010e01050d0203090c0a150c 84
    0x8000b1401160b1000d2a4600c0c40c41c1000c2e078101584240225203c40301c550201c2c034288030840344060304455002e45003000c000c41440b000f0b01c5150440d20b040701d0103d449043c40c00d1070000440314040da150352008000b0040200500030300135100300d038000d407202180e06542d045001d0503100d1511146034103030000c200240021300f0002c042d00403821f103403801d04003850781d020200c0c40581300b20040c04007241d500030400004003000d00800c0d000c00d83c141d60500241c20a0b0781c0d45090782d8000f81c00207250440103c000340070540700b001410010300c1282002e20550810015003c01044004000d440250070461140c240703078092f0040364060007000d01000c1c0c4c000c0300c984816140390006402c04c7e60900041143c1001595102030002c083c080b20320196a5070020762a04074a4400e680715110903010188040d00c0c04260041980f507444542800c112950381201c8004a84901c600c20074207008034408800d01c192418005001d90581c5010340300c1e0108242c880b00b11901c580d00c944049070015254041160005e8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 31158863 1250 31157613 31157627
    0xb090405060f040f060c0e032a090a09020a03030e030d0f0512041b0b090301140601090e0c070f051509070b0d0209030f010e030a080c040f2306030a060f0504020a0f 72
    0x1c1d0103400049900544c980c2c0341c0c020303250403c0800700050501d465003200d919080c01070000c249001c07044480f95540b60740164080b400b06034a414881d12a9030001000c0100a400004515600070004540e080c0c403449c029141c3c601504000d80079104e0030940b201e1b01c5020b80d008103030940c502d41350300d800d040c83d10300035106580c8010411075514803010718019014605860a10103000b8911419840b02951014982129000386940349080176000078098941d81160341072007034485035401e00d900c41e91028440c000c284944000203041d0b84412005405106011a00702451004403441d8260380c1c54818040355142c215000d04503088004019a11216000354018a25010050300b9248491504002c450031503801701d40844003508001021440d69900c10703a22a4420a80c0324641c2c102805c100e0700800340c50725401aa17440030708412580b1004a00c0701500c3c00815401040c103a41ca280051402002c1c1100b4881c2c01da50a018400115143c070340b50007038403203028165035030140d400b584d441c00b10703290 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 31160113 1250 31158863 31158871
    0x9150e0c090414010f030303051e1801020c07030f02042016030903020d080a080a050403050901030203091515010f17161701030c05090105010e01090306051005031e010b090405060f 79
    0x480c0e5038003c4450003400902081d80208031181030f0780c15030340c0340d420302078251400100403298215011141454001503500465000a1002180e140500100c030241e40248580003d01e50240700c0c0e0500041088081001001007900c2681c051100c100f51852a49000310001040c80210b0000c2c030520081907014107a5202d85030192030b04c60003007030796600032652040b60000700380c50b240c000141580400350080c1c41e00f5002400e09034100301e20700e050748000b402070003140302150405800002040030300504100c540f01c0f82840d002c01003403608004c04020070b80501e02daa014040340e11203884014150240d0b10743c44081c10410100480d9030354921b0400440e4010366150020300ca00321010b1564400c10041c0180a1032081c018074811900388410440040816440141001001c400c0980130780d0348401601c0c21030354013203004149500ca520b15280c0110071034101c02d40600c0345442008000b059080e560082150b00340082080c0d5035400c080c04a0840c0c220380c054900da2111000c500d510705190201584 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 31161363 1250 31160113 31160119
    0x501050c03120c0a0906080903120a0608010e0717010b130c1103030a02040e010b09031b010207080f070306060b190c0303020d050708040b0c0c0c010e04020904090c09150e0c09 77
    0x280001a407415103403030388180c0b00409070f5800880c2c0f52002d0b90b0841441006000c032401d0601480c0750001149aa0344500f074450640000142c02060300784c2100e8110313002070510080240941034600c0d8640d5030f6002d45114400810b01506155030b0b10410622505800c0000640705680d1500600504030141c026054281c04025082c002400c00700c00c1032003d540a00703003075017025948034a49128444034500603003140c400c0141c100a8a00d0582d0000b410f090a07500c1050243d00100942c001070781400c00f1540032182e02d010360242c07210b03001c2000c110070003501e105810030400355480350b16205045c090352600881035829a2034100400c1d0080c901d4103e603922030310f0098a0004e40f1400c0b03000341c40301a030344030010810043c180010030401400c034a500c407082840705420944041c014527030f524101540d6506201080e1f500f01e9aa8440d60100c0342e04200140041c400c140e80e80c640050b0480300f038482d40b0619072030060021444030006820300304a4072002c6060036a500c6001d48030350203a05c44001c8641c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 31162613 1250 31161363 31161367
    0x1030b03030f0f07050106050a0b19030e030d0f05010905040c0302090907090f0b120a0507091104030b0115180501050409051e0103030f02010b0102060603120304020a090f1a010e03070501050c03 85
    0x40810b280002c02ca0100f24a02054407440e4901d05035003075038103a41100b8482e10240409010480311001501c100b98100401c080e9047c24030102a8003e240e0b19907200028000081c034450340c070505421a480101040c0d0003081545c2e621107005003181d0081c0c400034003103c1c40704404c002500e8500846078008200310241c0e49466916507200040f03070340f0140c400307031200c0c2c686404200300d2030031201600e401000300d005080c2040596440e19100c94150007040e100700d070b42c1c41c4d048401140c8407095402035980004000d9455031102009058036041c001c0c800c00040306152650304020019a1210803140d068490904043c200600f01c2c0107031000400038a000d038035585419840e5103180010324000c0d03010b80c07200b1a90003900c08001342980c11024069042d544100c0501640340c42c0065202c000303000902c4503640781d07111480002c403c2d0307900340e0041e0416401c0408451824085911072669000c0c103580303e4428134440c10042d40c44480c100c0c1002d40c0354101d00c0b01008130b540a0301c0203000085041003075034 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 31163863 1250 31162613 31162627
    0x60c1506011818110d0603030e0906060901090b0d090f0605010f0b04030b0403120908070f1101030908090d031707080708060a03030818070b0a0e0406080c0a0306020a050d060e040201080a060503030901030b0303 92
    0x1170803942c07513034410341c000b40900c0c00d6488141881202160084400d440c51858204654006417809100344a1902d00d40e00010301d612044c2410b81c0311031030103580420f1800c44484a0f0414002030b05080c0180010410030080c0010503030700c1c43e0119805c60f5405004820709988a8909640c030303c440c034040300d51168803203420310002103022006001c0c40e4880c0d40014207034691400d02d58810140c8183c007030305152410344404d010039103c0c4250f0700e0340b8070b00301c0340800030705454a021107043c03c07500101280e0401000500c100341d034100110500c140c425035104030840d035480c1e040280800b002d10019011400d16400300e120408203040803800d40d1102d00480b540d190750f803c4030b03041c01c3d40b0039100d440001c0c0f0903c0d1701c0c20383d52402d40034000003021840000c003a040c001c2400260704030058030000f003603030358002030313009525010360113558400000d9001040869a185000d4107596012103089000505d8280040c0c0c072070850344203100a0b180007070000c50801c44090019401400341c2007a41d81e1500c0284000 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 31165113 1250 31163863 31163887
    0xb0406030c0e16080603120c070b040b030106030b060906120403091815081501050d0c0803030109090b0717151203030a0603030f020105060d020609060c150601181811 73
    0x74000a06841041110078070784044080c10b4010250300e2841040701500500c16190342c002030341c082062111407004da9034040c41541e10b1400c03019500014250101007000924180d0100c0610b0486155440034011902c0510800040d031081d081e034298841d2080c8500f42d910208000c8880d03020f4401e042952001b61601000c920300c0b0a0300180061103615603610fa55510ba14046400c014540400101040701045a065104500c14021a40607070441030100c0184030070554100c00030071014040e070b540d030358540c110304001d4481000c00b2b50b02400d00718081039180e0f1040001c202d0580800c445c50585032550520b94400300140e0741d005500103040000c0503443d0100f440158041d10724028001001c0d0310b1454060b044003840748080c425645403c0c1004425110403003405021a81200c1c1140e4508030301d80010810700a00c0d000c00c045110300c41e40d8120645a00a0303060150710240c0300c441221040211281851086c0e000300500b4503184503028204c4c00c0160001f2900302c440030201414002c04010b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 31166363 1250 31165113 31165133
    0x14010207060908040f05030606031c020a06060e06042d0506210d0206011e0e060a1d0403141c0c0c051f0c080114120304090c08040c0504050106020a060b040603 70
    0x2c180c48500002400300003c1d0a8410741d14010315054025011515065000075140d501010400002001d0111110503903403090100610f8542d008000700240d946400156009080172555103020f1882e00c1c81d0303a80003000f000001480107028001071008525150140005000003500c03198005444546603c0101c038441a585c9a04c1c6054005140301070141c00003d14105c0b06900107816040342115420503034030400d50510681f4514813418a8949612022410007503080c1c0c010b4811b0410317020396000786130a0600c624041d5000c1c1d620100d004120060005080c85030000328080500001d070300f00c0204066400c000c00c0c00e012801c100c1e840400f6074883c1c509041c1020110307001d680004100c0300d07051403644105000f0400c00d2500c61815810114030046c0c1c0b0106101d850321490100707023040d500e10800c0048a0190219032824440106040710117444400292011285441c080c0000f2519040071b1250798100e9200b940140100e8801d0340ba42401807a1541169801030b03101c0002001007201005 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 31167613 1250 31166363 31166381
    0xc040f020702030c010f0f0c05070b04080c0406050a050307121103060c220e130c03080d02070303060e0c03010b0c0a171c06142710081908071401020706 67
    0x501603919041403042501300104480c41d24184644103040204050780312581c000e4101003403c0c56219000d09040844c60a01540c0c0440114000000e02240003100407444410703004050700c0a00c00280c0710000c1007042d5010b40a1260142e01c00d90040010340c1242001d1900207008200144a424422020a08040f4110f031004210800004d02112075107000750201504654011140d51440c28004844107819016003080c0d1150700440b541d0060041040304400110786c02001107a5070001c0f40e211030041c0d0007080003500401d1a0100c0091040845000603104041181e2450700c0c603805c5c4080c120581e000081801c0c401e00c95040d00c14001280201c1800060b00d18807107030b60715010426000131106402c0321100c45003d040c00c004008035940703070411884240f07040b1900703161003d0001e48a002d0301030039240c40541c080d40c4010700900503074108452040d0313240300007070710b030000d0416039170301000010070000400542040108002103404e42d20740d0309030a007108002525094013501e4070000d80306180 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 31168863 1250 31167613 31167641
    0x2a090a0e010608010603020c030d021b0105160908030403050705060c0f010203010803071e02100e010c0515070809070b030c1308100b040b040c050f03090a0209010603051504090f03030e0c04 83
    0x4010b0004580100c183c034010441403405602c0c110000807005d44030b015a1800d640110740100754401040b034189507080802203410000c02c04c0c0d1500c110781800d101210314480b00441c2031814046242180407040710203494202c030040109074642814403d840c0c0c850f0b80c00e0042806142d412000c0c080084c0003c6008110110045886410314180380340f944c02c1310035404030501010785803100107884001c19001da640039810148440d190323160060300d407000c202c1d90007065400359840b41612000321015241c000d02259030303004010303560500031640e907040034002c1c0c040074a418400501da03501c80034000c01041034082c0c04000d03503594135001903107080c1c02c1c510440b0146880724407039000d500b820301c580d10404404031824002c1440641015110b441680700040c024035000000800c0c0010400121808a501502c083d26641e51054020014181946c80300049000d80101c41c80f6481c10b400313922541604807a849000040a5405400501b807104002410340240c400b01c160079a07462040d05000583c178 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 31170113 1250 31168863 31168889
    0xf0d1a070305100303020a060c030e0111041d04020307030b0402030a060608031e0a0c02060d0603050303250c030906050a11030a020a0501060803040f120312090804060f082a090a 78
    0x554001d002e9460080143c082203190f90400c00c0440c4d400140c000031560040302c0020200f0385011b046002c0c007102c00764802d20b5030030b143d141141d80c0031410007007089800d00c00c007030710201030f0001c0e031554140c2c1d081e20040d41c940c6c00140d050001c03c0185500d160082c2c4000d0842d41c6001c015604d030300c00e58040f035200d40b0860300302140030070071010301c0740c64807030f500e01c1c8440b1203442c06000a2014114600105002e0301484020507400b4032031165a00c10700c042d42e089802c59480740741900c0c1c4000710398031000030f01c080b004c1180c10304810503000d001c0308901d0b40d900d6100e0341390107800c0000171a501d4000c4030b10700c000c100c3c500d6141d41c500d450a00c01812044e10541c0600800151400d16500303483d2180d0200c403e03603008205c104104030500489400b92940075006460894a500317007120380141080d40802014a010707001002c024101c4006c00031180b55417030381c040d8a50710003815074184404851401e4000e04e840f80d02e490b800d41c0480740300411041280c0941c14104148003148004c5110780000410001c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 31171363 1250 31170113 31170121
    0xd0f0203060901110412050a08130512010911010c061407121409060402010507030c060c0504051c030e01050a14041805090601030c03020603060f090a0f0506100903020f0d1a 76
    0x41030109aa00c180b10500921044800c13080180c000d04c01c2c0d04ca05004515003010000411405000b04107025812101250f29510004140e5004031118480e080c86aa4204141c0c5c500380340c1801030241d550b42090001d240c0c11801401554903240c00072085804030707510f40d4107401d0118002d9030741e40900c06c2e642e640200c54580b1058a008c0701d500000742c00311204014100811a00001940ca50050b070a1801c161601c0303407071400780c3e052140100c00408840c1070001010101d40d025026004840d411186500e048145900c50b441d015844007014002903080d0b0085001940112700030800300741545001c04404078900e85081041c1c010341c01c451207a480d8409000e0804206010b9140c01c00240380c0134007083d5145903590700545c1410711000b4020304000c800501c0c0e41c0d42d02d41080c0e244200c05419210a898400155001803054802141c0e01d1498080030842900b040d0a800582c15143d845650300340c0c0c1113408016801d801c85032a140e010102520100001d2500c240c0e030b00144459103154203180c20 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 31172613 1250 31171363 31171369
    0x9030c0516030b1b040b030106050309010f0c17060609030a1104050a0b06030414030405090117010606020c01090e0924180a080a0305130c0f0602100b101103090d0f02 73
    0x101011416100c03481031500b800851002000c81d604490141410305082101e40152003190045511254054401200006a03da0007000851042801c45c0c02004030855041001c401c8440820010000400f082d80da042030f4107a050025410400081005090900e1140064903000119200301ca82e04560340d18151a070400c0e010b016040055000d09100c0981010042441408020405020340d5005d10000c50601c800307008a0b400350070042d100d50a550b031510780440034140d24480e440741c158030b04400001d00c50301c0072903403600d0030708140d4800040a15000041c0c82c1c4190241c103c4085024404014040c600c02c8280240d10089848a03d965450a0501005010320001c90300c0a140c0011400c0c500207001902114941d44882c140061603499614044158401c1e5000007400c411a801c0041184310300c248030325040b5030280e400c6803406c0c1c0a94400005580d45468080d410040a0708080981801104003560325144102128149000d4600150003149104001e0350301c22805000074081d42 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 31173863 1250 31172613 31172623
    0xc07060e0604050d080a0605041103010513060602030306100306120b0610090305030a0332090709020c032b021c050708060d021002070302130209040b0a03030206150604030609030c05 80
    0xc0c420001c0d140500c2c06440b00340d161038074102039508100304500080c901c4041c6078403500c0904005041000380e131034a0b00078103006a0080c0a0244035404011402640404038002c5006451060b0701540c00c0d516020248684031040c600c10405254840a0100c6c82c4003680911111890080a1217142414000113004020030384c3c101d0071040002910042c008070380300004448039a90076103000915007441c01c0101014140e088110030556200982d0391440d548400345c0c0d00c0c055070002044c2c603034141e65102a00e04130310940e40b0a200e03c2c0c10a018034240304c09010740920303080b000c04c84103001d101c04010340a07080703a101d0924a20519111000071a200c40a0700c1890303886107180c20324500782d0500ca000a5181da020500007403107403520b881e6060740e15100344406001968060300031480f03500707500d0b4100040d420101364140610320300080d410151401844500071240c060b0080d040039100c3c541d020003c07502807201c442d0444010040000001c1642c4200307240e583c060742d29a0500610307031528900340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 31175113 1250 31173863 31173881
    0x11030708031515210a0207050a060b040b180406020d0209030304150909090206070209070905040e01020403050105100f15020a020a0611060f0105060d18051e0c0109060e0402030403090e0c0706 84
    0x10f15428010118006621250103488112081241219588100303052019101d5280010141d000d004a110304118184c0c021210483c01140d09000c0092154148191104600a181c03c080c2034040418003080f4190300402004103c11030142c0741c00b0941300828030316400383c0e1260b1142d001c000410201c10f0b0b1309c2a8100003401c065a4140110003150300010350300e020320b402c06031103012034101003100c481c014400742009160180080c01950440e5803200c0c001d4001d4402650203509143c001008400d17040070b414180c50103685800ea03800e0404c00300b05a90071654582000b036128000c10b00016a40d0701240e800140741595448400302503e420260a026016114804080780c01c001130145940e0003050703c0ca0000f041c0000a0410340000d0764500a01081c40068014003807407454040038100108081c00d10701c4408201c0d43c1c1104040011a81541c89102e08000140d01e800460394500c5d144d001590402e000e49001440305490b841101c5004909446a0b0000600090041c00b0001940242000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 31176363 1250 31175113 31175149
    0x130b09180601090c0806100e03060703020d140603060c16240f060302010203160f02120606090106020a08030103020409030e10081b0c1b15130501030b0904020a030201110307080315 79
    0x220007813030400544080b101800003886070007142003050409100d142224201807005084856505100201400941c05045110f03216420070607008858103915042078001e1001a00401c500da6510264202a800880740d85003203902c0b01c01880d021542d00c40c00100418a40300306074602500740c1c24620102c82140c141c8a1040b401c290003040541c0e004400c2e0750010310002ca041c510b041e107a180c282910840e440c4001c2d840300c0e090072103680070307080000c2c07842c4501c0341076a84408a0345c031340d041030340e40d41c10741c81008048074810401030006080a811111580d4401d0901d00b0000c0b031080002140d41050407a5600090000700c100000f90340000c640b0782c8040780b5030310705900c0e0881450090740c0340c0900ca54040c6298982000c1e030701041d11a5000702803000060501c0d10340300c110403140b05803003000a12440340004d00b0700c600d4109502d44164100c4c0903030750003410fa01c0d120740713554010b48024048500507115400240100404a50460300542c4202100320010240c802a081040099030380e6140d1303800 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 31177613 1250 31176363 31176371
    0x9080306011119031d030a050309030d080f0a11040b1803011a13020901020f0d0504060905011d0103050408090604030b091002040b030106110a060606020c09011e05130b0918060109 79
    0x4615091900076540c40ca07098a420a001041805c0305203409018040c0c458042c0b107414103582c184000170026251044e8110213483c6240b0b49e00608a804100540e08469444517580c0803401081d9154407001c480e21400a01d0707814550740c0e44156055402c07082a00034400510b1210810a1400703100310002050000f400070400c007400d50118403000c00c16072000001c16800501c0461030f038020024884403044000498a001c0b40980d0000c20b140c0161281c4008034802000110301036018070344e901c2032190100e0803090003424000c011000780c54050070581c0d0039881081600d8154841761f00901c0594000c0800d000d941c20032a40c1185041c0c400310214031024410b010a110483c2c140e41280d04407010384c54084214038141d48000d0a180956500a240914001000504580100c0e0140c030841040300c4c0081d0a81e030300c22900d0f05071082640205c0059107128000c1c0302c103140000705485c1404c0c140c4000203013101305e680405d082034400e81c0c240380c001c4078294200895280c100450740c0945034682041c0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 31178863 1250 31177613 31177633
    0xa09170f0c010b0103020c100b0a0b03010f060306050a050105070f1703090a0c0e0708071d0301020714010b030d0f050f0c0106030c0302030d0504050306130212070f1d01030209070c02060d090803060111 88
    0x83d10b49a88e501c00866581d182c038401042c543c3c1d818007400280030040b50441d502d50395a040340205002600c940e802090600d500000c0524002008104540381a1030b094548502981d4150b6405541041100c0c03030313940f00030b44071004a21140514801d100c483d0060900d002c0c00e050081200400ea408981861a05010802500c0d817007500c050f005042420101180301c50400460448641c00c2c1c00c080d01580701159520031700154108019180714641c00800418034660207041e00c80c80280208404241c9050b0003a419a100d48020031041c0b090b0701400e81090015001d075425510241d0049c0d0700d145e01031a007842075140600520062940c00d0811030b242c00e2809007c0b9880d49002003040361a507003540b00c4081591210f40301854541d20580c01e40d144140c944c80c03000200841402032403030341d17044030040e4494041e05100031410307203400401c0720140c1d81d29042e0445880300c185404980003c018048c0c242d114180f80034115096105030207807900c91a001c80014008650710706600c5a5a204074510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 31180113 1250 31178863 31178887
    0x70b0408071e0b0a1106091506010c0203070b2d0c0706091505030411181006170609090c0306100e0c0901050d0f021b03031006080601080a09170f0c010b010302 70
    0xe20122050180f9a540780c0300e03000c00a454181760600c00d107200380520710822000c101d010405516503041e074103800f1140d07240e2000460300f030903041500a40540c0f1903141404040c028074064500d2a08902c40e90030f4096074040a104028543c801c0548400c8010440078140401030110b00c0242a80c1d28088480900c1c2c4041c01008070011851a002d01800102141c24400b0900e0810b900070740290041c010440c1080382d080d800c900031030b8448126100d08001003001c0f0b00c100462069200032444021040c0c8484040003c00703c0090154a00d0703210309101107009403002d0052a00c01d00383c40081c140300740c2c80c10791409200c2c000140300c114164000c0222101c0d41c0c1e0001c0a4880b40040b242000a0900c1941000002441a050555100450200903110041002004610902034090740809040d51943c080c3e500d00d4094504501042000d03000609411255201d10b406c1ca0007460742da284020440000009640682a00e10b1024000101d024440d20240200f0407031313800c00c1c40c04500d084000701c05 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 31181363 1250 31180113 31180169
    0x8150d02240d140403030608010e07170c030d08070807020102130902030604060e0c090112150b0a09030b13020120030d020f13091b0c030c06020304080c070b040807 72
    0xa104034005540305640052403020040c2c0304a850002e00030000403401061066543d20201c80443c00242407034000700c0c1c400c81c10b00030f6110703050303580d001014072606103560340c000800d200a541100e4401c002e1000c5e6580e0342046001607650f8145c5455425062411000300541c500038085015603004000000443e03070790308503040485014a200513240d03290440050003905080d80305000c0688003a013030116000a0400a0041c04801d032542c0f04111164207405040e0f0360442002c0c807440c2c44802d010003015000c00000d1508845c00e00d01503212684036035500410100940da041c8200d201031326030104650300700c11076080c1e8040c0c1c015465810f140380c801c540d5603440b07281d0328101c0b241e8010035203500c0007100310240c8001d408040c046055841c2c03503803401d000030960f20b03200380c0901b0190f840703130040b05000f08604040709415544410345106152551000380d8030103002102c01700d1041100c080501d03824012a000b6240c0d52401c1ca54442c5001c8089203031840542140c034140180c03070060760701e0001080b1 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 31182613 1250 31181363 31181389
    0x103020907140d0905010f0c230703050c06070c1101030e101d0a060b01030b150a05030402130c080108120405030c24030708011509080a0209090f03070308150d02 71
    0x141c0801003000c07651240c10507018800d601450305041104c0902000019049540d052444903401c000180c49844101e4180240123107203903e444083c403050100640d00350051403500d01134240341d4980354000c5803091070f00708101c9200b07000a90515049042000d100c1c00804040400d00c4c5c2072152141320011182c40d403400952040c00d0310f555418103400319090100425501e2086400d44400d01000d04250002d00094007a090000e490318070040c09038a4040300d20100504607418a60a1455090050b100c5a1000d002641e0001c0d101d19062404401390064201c0c1d408a581c81580c5035242c01d0030145011494003102c00b40810a0105014039107002661f4403044000300c40c00d00d0701c4c406504030103800703841d42c4040c40083d08000007000084d40e00115801e040320f90a80d01400301400c105811541c0091703a009192503a0040d03038a01000d441c1c03580b20349801004000a80d60005a10448246954000d240413170105955604110092582881800850001741c41003100144c072070340000e07405030f5140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 31183863 1250 31182613 31182617
    0x10309110d1e080d0c02030708040311040609020c0c0102060a05240d05120c07050108040309051e12240105010e09040302030405151b0a0c0909030302120709031a0103020907 76
    0x76030a0200484000d4641c0d07011541d00150480c1c00d0a048006a0200c410ba00846081544407440741d03100004544000b608051420704040c00c5d9602d4032020301614800300e0b4041d881d14800b04d4070600602c001c02d40c000000000b01b480c0d0800f100068108400100f000003581e02d01410000040d4142c0b425411031010300340411400b00740600002d444c20704200c80623209100310b06c00840399141c2c0c01d0007810b0040102003103801460b81c82004603644001200c4c001c2c0054801d100820240c10a00c2142e8164540e036600c55015404501c0419180b00030340d0046036965224000c58514000c440082001d04d84070742110380701960403c4000791400ba00a402c181c0207041c100d000030241403080c000e886c050f1800400c0840100d01c2ca41c80603240e50032038801c01801c0320042c80d46108503030300010b0f03001e4840e90041040d8001440c1c0080c201c0100003070340081d024140c0800010295908045242c2d01c41d500d261507043d121420b505250190080c0303101c1c0b01070709462010044c000342c0d81c0c00000d81d41c00032040c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 31185113 1250 31183863 31183879
    0x190207031101060303090f0806070e100201091b1404020c030307080702070305070e0106030e0102030f0103030e0604050603040c0e09030a05030c090103061502010501030b07030b0607020d030306031506050306010501030911 97
    0x191a04031501d50611202160365441d0650101c101035000701e103081103070384080d02d40a069444851450716010140c1d5903102080003500b100362142403c0c01c0c0d0405800c0c09000016650380b0581303c0b064603c200c23040300d42c54508a40380c24044142a0030800c100d621080d01d01f1803c1090742c950290b92844050040c0007405402000102c4441c8200a81805141c0c030400b61009079030350b954680710612081c025240843c5c241a80401c0288051007030364420045001054196443d64400b95480c0d403000001c190850002c01002c079503515014015406144140c0f1004d408030700d000344a804c4044040c010301046d800070016124243d902c101969004001000440e5171654845c0045e4002e00b0181d100c038202004070807c102a0540641c8210704032809012803980b10b6960a401720110b51140030b2860b0b000c00280200c10148c200404946034091080c140004c0305522030300d401c03102d81c1a007001c60b080540c4920003840719003018804280145820300782030102c050107640c1c02030426240190f032401000a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 31186363 1250 31185113 31185127
    0x30c3302040e0c0d0213080312060f1018150e030c06070c0314070302040905030d0b09010501050d0905010608191401150308070f0b130506060a1a030702030c011802040b01081902 78
    0x8241d04840001b00c00c07028003001e1561f2008250f40742d8000700449140c00a00600050160500f0405400a0f80005240c5c1d00c0ca844000c405070740e06ea465a10700d145804501300c1c08902c102000306d40c2040c0b1180390b00c42682c40c0f40b03141c041600d00790b415104036010344024402000002c00742080300d0140d07079000c110740c00100c900c0e032900303883c0c5800b41e40065400350030494283c0503c2030220043c014031a52440c05d0044811080c14804446003e1281340e00081c8104000400c08155501156403c0d00c10000407441950b504c0c0d00c0e914003554030881c0d200201148400b0030410072002c680c1418038000c0c01c001e10440300303600c003d10074107121484060903548002541004100d005500301840950151254156060100c002c943e01d04801c103040740e10780300e1000403801c03500d03004544e00c003101c1c007a030510242ea81c0c4107180e142d040e40003c0c1141040d48002d100d281400e640c207008400d51128820400e01d4200c21500420041c0c03445590842c1c14020b0341400c0c054041e0034030315090249640e2120160303803900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 31187613 1250 31186363 31186387
    0x105010f030207080d0902090a0504080f0903070306050103051501140603060111010e01060b03100f0506070602130b0c03070303060506071703070c0206030f04020126070804030c3302040e0c 83
    0x819a18010b007900030000d0700b850171100a61001c0c00f0240280c541c100b4580d6811145400c45070180c0300501800e00c180050100d510045c802020b00e2503014059900465030307540c440301545c43c01c1c0c2003101c9640041171082d004203803244030580104100704404290340a1031000c01c50700c0c840607000781c2c1003000c958205400c00d8401d4100714180c28014000700003155030369078000c14540060b10003101c40c0321403117000640384050006440030b98100401203480e10006a60301d034002d5000b07d40c1e5262075002d1340d0f0b000030843c150902415061000d40090f503035400c540d1400800300c03446074002c1d41c4983c1081c811203002c40c07007013a51460034044410105a690311240c43c02c1c0d0b03403c4000413009602c86000410440d0400301000382d140a6031003038884c2600b6905029003030142402d03007401d0000300001d142c002a01c0074400c004080d005070090901d010310200395203803c40000200c1941c0c0141e101d01c0410545005680b008844034815030342c1c411802d090a05004a4220501510100010b00301285008181c6 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 31188863 1250 31187613 31187617
    0x11202040b031501020d02150f1b190801050907050d09050c0415090507020316080f090d052b05040306020d020f120a0501060e0901090518010507020a1511030105010f0302 75
    0x121104111580343c2c5484104400c08400c45032819005014502c5a1004607000203021940300c06043c0640083d40d440c103505016140000b4520440c0002c0118002018900080140f1a01005400080007400b0308130000d081908103a10442c01010341c5003c003c0030652110039281d0500b000307540429010722a00341549484582c0b442298454507090b0001070035000c1e0007009040fa14030010910940d0380d4110281d03103900604142500c1000442d207100000351060f0000c24000e0782d40c100c01c600300f841c400013191090120100441e4a40e01a000c0d03e0540340340f02a02c03000b00710000240740300c3c1026006008201d4060340c44002e1a144e008036031050713310304540554a8940303040411071344a00b0941d115400d40e80003900c4110f82145410004a01c1c9486840410491640174007122200c0e440c0481000041c40000c04103408100800c04455180c00280501802000640c0c01403000c482c2e01d0500403040c00c80d5a800194280c40c0002444000c0c0300d5105807811a10309084c059003192409c00300b07a0281c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 31190113 1250 31188863 31188869
    0x512150406121703010e060616050102030f0108011406010e01121404230601050604060c111201060518090601060809160312030b0319020f01030908040e010e060108040309030201120204 81
    0x781022400714450001c0440244500d0150001c480107040e41c101c0756505210078015000e80e0399102001034603a0a010009019550384610904284051a201d060880c0c1050f1070b0350360a600c5a800411114500340181045081c581704442850b092071000038040e420020701540c1800155602200400c1c09507007c1c04062030030989001b81407038649881e003817901c003400c11200818120342d00740900c2600001c20505844014028501e00390030410b090314600d801d041c0448040900203007128103501c0352410801caa01a440000c544503040c00d0030003005464036109003030040704c22000c00a40341000074040f411541c1a08120b00035885000030107081c0004086c02c45072010307030308130300200701300b1151054070400101c0d54042081540c09410180ca40c1c22030702c1903e0504c6c060402d0305000d441c01c542c50600d60141410001a4183d4940c0e4108058120381d0240e00180401001041104540d0071010360114007407800080c0d91401d668060580039080c003029040007124032007070654911703d604503009 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 31191363 1250 31190113 31190119
    0x501031d010e03280f0c150e010f06150c1203180803010504060b040b190201061716090605030a060209011205090a050c0901060e010507050304030f080d0506090106051215 75
    0x14114440c40b459803507100c6410800c1c101c10301031120905100d54030600e03506407800d41e510b603030a901a0100720f4041c1c0c5c4000c01034460b040c99655058507a06548500c5008030007400000c10321085e0306680004941040c1e200282c1c0b418410b4031510103e510100c07a503083c680c07010329514100707040d540842c024030b41d500050b41c03190803148504062241d200c01450480300c08990501c030341500d5502c40c0003039000b01d20840242d01c0003400070b5094400c0756400c1d02c10070803c51000281155a41d40004c12215491040c043c054204ac0b12070290602183c8007880a00340d0154148116451702d0042560350740c854202410207940445c4c032010603031084100c2030701c050030440c081c0024105802160349851071408110744520541003180300d14100285141e040f034641d0f031500101c40381e000c4c006503140d9200302c5044071300340410007000c80010317914003145130464042c28659032200c500030b0000f011260050a02c606c070710208001040090390003411191204030504001580d034440405a0744500d80380c1010680c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 31192613 1250 31191363 31191371
    0x3040b04120b01051509040207020111190512030702150705090603010e0603010515061803030702060409021b1204150c0b0a0f15031a04020a0b03010b0301141008010501031d01 77
    0x81d5540040240880c003400340801d10752030303640c80c0b0130001d1141c1000e039041000d113814400102d452a01d039001c2c08c1285d0043c1002030100b80750703008550800b40180c042d0114281c00750800320078401c040003107800e4083d00b0f0201501c1c40c00c1a0002940c6c45003070701c10f00d801e035181107000140001c1c403e10591b0303140d400180016440c6e5845280e00309000500b05c0c0c4140c0250301e0b2600091050401ca24210356500b07014204a10b004400c500c94500c0d40701c161251a090b1004020620040e15500010401401480c5006850702d54140840030580528044918164402c0607030302c0114010340201d07000c683c00050303170300c0064800002c15904640c40140c098586548a000c0024802480d0440c00d0f044180746020403200c0002d640c0c003441101c060201504424148a01510145140c241c1d079800c0350005128032401d50fa034200c010320551098110041c840320100040014482071035400c50240c10407140c00d070b0b24203401d1400803c10181441403504060b103589031056545a0440480c41c3c40d650000240 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 31193863 1250 31192613 31192619
    0x15010e060d1502030c0a140a080c0a030b06070609020406050303031015090b0c060403020709090c0504090303020c0a0309030b0a020f0313060b120c0909030405010206010603020702030c10080f07080907061103040b04 94
    0x2142600081e031b0740d40104e43c01014500d901c00609080754016040b1751100d03c030503100d0f2001650642c00c24404007042c036030380d200143c00341d580312006007082601c5a440414404594070500055403160703804140682d1040c824040d0280c00100c0034000daa104030701000c451103254008581020442d400f40101c00700c00103040004041c04200c1300c2c0714a0094003120700395130380d50f6502c904860600c0006002d5807241e017404d00103480c0607040181c42600a1602500b0303e18400051400c0c443c003800228003152002c0e40410030049806500781d44580003000031400c2440059043e41a1311000300011003100c43c2c90020410402c0d13950110654283c0980011890f060000d412076544010b6801c00e0300c15a003174000914040c0002081310103498040e400342c2101d03468034500741c010350001c580803a49802000011400341e240c15640c1401c0601c1e9030303900d000b1403c12810094600744082e042104200e144c80411243c400c3c001801d408903650713841c106a0101c00d4498a5045008039000325484803000a000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 31195113 1250 31193863 31193881
    0x40609020f09010b2d0706050a110408031306020a02130b0d050706030209040f0c0c1707020d030e010f090608060f041d0f070b0301030c091109030106080f15010e060d150203 76
    0x905140380c0c51000030345034810a60305200200254040f174500306030040051100240031900080c0d004603441d080030031100e0352000c6500b0b543d002500001752517400071455510180342c500500c0010031075400941003144140c1c02180070302c08624240540e0588903040800b16031180403999072990b41100a55440b03d44a40d0010041c1d0b029003c40c500c00c50811504207900c0160303101c0c4a44041407902c64460840c0c442c1d07203000d181d103020707103075054080f80c00c3c440d01c009a102c407841809518070030b5503a5480740100314005852800469200400c000b000035041c002a60880c80d031a0b00050219442602a1080070009002d4946900210080c1c400e01142e07030000b00c0b0010b4902c1030030099009950140d034544a007450180800d01c0050080c1d50030650401005400398008814506a031004134942100c030070110f420746030143d200d1501035200d0175040604903824014640e85c0b20f440c4850b503400c3e502d0706003c402003078000341541d80304080500c200010065403055201c000b80c03080c90f05646a28103a140 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 31196363 1250 31195113 31195117
    0x209010b0f0304080714100b01021509061b0d020a0503010f09091709040b040603051c050703120504021201140703110a090b030702070807120203060106080108030a031d0a0c0815010b03040609020f09010b 89
    0x6182d0240c80758800300c0012f020400d0b4034602c02c0c5510001001c3c41d550741083ca940d82071701c1c448801d09500c4d040000004810090004140380c10980c6c5940760342c0c2d4074100c0c03c010195981e0380420880303407a0401078000142c000101414116424107026290140071000400600d00344110507801481d14000004000c0c004c01c2810f685c40807007010b0f00c062000f144050700d1754481d6940c0180021a682c9031122191000d41c40290014005010101c601e0030050250b82101da0500c08152040142002c2110305030307050140031040544020024180301031007501410106d0540140342c003054011000450082c802c1007440000d00040088403a1ba940d40c400340d145007007031220f0030381c00f0b4010580080380d03d80c051a22a4120b4010f14011403030003290342021801441001550b1450010140c044003403444100108500d150162031203000c464a40422146810f030000704002500c0c2c1c5ea500100090002a0f050303a90107500801d0210350300710350740700086030400310f080d217aa0300032a0040041011a54980 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 31197613 1250 31196363 31196381
    0xa0f090501090605040506030304060f0207050612240f060d0f020412120201020909040206070201230a1b02030d0c08070204020318010c0801050a170304090e01090209010b0f030408071410 82
    0x110400c107180c0c45078103002c186c030422500144c041c0d1003040100310307040c450400c035904091a4410740752036a4a690000d03119620404001f120040000103001c241c1c1d150354003200001d2003508d0050f01d0340700c016010520704400003950038403841c000f060901c0d4040c40342d0030106030380c01903d104540e2103448842032800c0c0c00080d0002d55441507a0190f51006c2401407013103810703002c002054000c20303503116400c01c0115400030030100e042190300718412070f125040302e142d9085030118200d890b40721012020020b02c0202600c01000040c413940442c0d001513100847d65124484491400308044142420000b4070b9105070305000350010b1000041010030100003c025040c403000070000c1c05400910a0300b25280d0000b1300820344d0007401140c0030004050b0846680815007140300603242820756401d154011200810031181c05a5141d011201c1107103050400c0502500c40f00046500b4030b443c88020912078000103000808200ac00120074041c003038070780812a00c00e00c0a9040b110b0407408480c00c000030701940c1c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 31198863 1250 31197613 31197629
    0x100b04050601171803070f05031903020306090a0207050c0406230109030b060f0303040312030c0e1f0e0103061e240e0402130506070606080f0a030507021309020604030303051005100e0904020a0f090501 88
    0x12b00e1722203180d4401d0088074000e94000b460a0040d856103100a0020f600016045500303209142440e04503864902462001380042c459a1916051400e00d40f403080301906009410480ca00e4801d000049101e06050341044040e20001944403210b40440e18511650304003801944600b40c0c0350340c01e81d90540240301e040c0c1140e41e56905103541b100610242c0c00d184645051401d04810080001e1441014380100c0b0450514000c502d5a55410101c000d4180582d0340409500451009018811131500e44016013071580d40d02c01902240d202005040920740e602c2c451003181c0000c0c1e01a850740c0c150800402400c40280300c0e55449549141c5040180b041d442809201d0203102c9c1260030681c40400c0c441c80081e00350302c6091401d0120750030040076103071041210038190342d00d400d4403003d07032140000340c0040c40c440d0b200019541003104507045140140c3e40668401c4012402e0442003a40c00000c1c03201640081c0e6045d58180c50301d100040110625422001ea54921520002070f9195940c010030b040300c0d981 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 31200113 1250 31198863 31198897
    0x30c03070f0c0f151806081b041d01140607030206070807090e0a0b0111030a0c020904020301061517060d020a092c010603030e0303040b04030b04050f100b04050601171803070f0503 79
    0xa00017801041c480b845008080f48180700019075803907043c15545421100c40c09401e20302070311140e1164008402c0244082c45062600042c08a0752800090b089154412202f0300d041c81800d581c000c1d07a0740307802852881000010310100341c6041c081c98410000d0301d40401c03818920b14117400c0e44002401d400b1902c90004102c1d1106280c4404048215200300006503103844000d0344680038803401c0407000c1e004a80565858000003200c242840c3d2080051003903681e80d41c01103270000c4407500700c40c202070540c1d407040c3c91600d0b002c00140c0d1a440644100e50089001240c1d0070b1006d00c0d82d0300c1c01210b03882c2400d0450a0784440c05244641940701c0300a81c2d04c40d413941c41c040701c50f002c141542d034041d0b4007684907048420481440842e04417400d0580c018800c9044503100034010106909150340c3e15104940c180e05c819503000e0310719140c010107038848070a18014012100000c1184d08040010300201c0f01000e028054402208042c0210f4100d160042041c1c0382c0340d0070318900345940f94080c12076038824101c8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 31201363 1250 31200113 31200137
    0x30d08010303050306150c010203010b0304020a0f0f0510020c100801060f0203030609040201030b060c032d1608090102210409050f1312030b120c030f030c03070f0c0f15 74
    0x604216410389400d95125030841ea20002400640100c003c81102c104201303005032611140d090000714040e1807010134854890500340705012001c00030340c0011005400c46030041c49008082d070700c2d8204680741154a904120f48100061b824004810210b82c0c100520410907103029400c0041103040b11665540c024000d8000c02040743c0328001540c15903400302c05040400e01641c42500810405200100b24500d403112481042d0700e190b000c1421329901e40c80ca060341800d402d8020100b0300d040706a803918507161203481201ca1550b509245001070040d034000c28003443c1c5034803c0103041030100d80400d0510a0711210b100da408680c2003803140384c00702c80c24a4001005400fa130489903006807103c0b10300b007500702103e03620900100326092800c010190f071600e03031801c180d403111408460b02c14000042c20b000040c03413040c50304142140d44891010340c002c00c1500744a1900008992945805c42c4801d81500d45c5403408203800303045c641c4440d01c2001d00d03010200e207901545450711203600305605c0d80510216 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 31202613 1250 31201363 31201367
    0x203010c020f0609010c020a080705030417011a0405130b19020406020114090a030903030305190f1e0501050f040504020411070311010c0903020109061206080706020d03110903030403020d050a050a0b06030d 90
    0x10106c2e15006800403052030000030b8a8102503c081e0b445007040d00c0c18a619049618410b040c111140c1c00260b44820030410100080350b480301e00030b001a60140304502c0c10b040713284001c1e488924000c03c540c190302c001a03100d0010740c0058020401440c1d0655869a4032034000b13010b000a010501d45081121020401c2000001040f0f04003c0d81912007500b19851603d05800416009000b4242c05040010744420711440c3d20803001c00c40004240080c0031001380141842e11002c108402c80074a00d40b0b0018030560380c4d68502e0000c45282180e01142e03603a20780c404500580a0785010010314003010941104158001c1000840144240c0003000380c0245103200b2514901d0301e101c003a0100c1e480302c00c00e01a00b84a2094449803516121000c107285941d03180292800d146507001c0f43c01a08140c03450099180c1c10b000d200d10042400d0015420700c101c00000035102d200d240700082c420900042d0030004c01505019520700a600102901c0300080c141c1005121801c0840304c00384607000c2d641441e04158 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 31203863 1250 31202613 31202621
    0x40509060303041d1009050c0c0d020c1315080a03110d02010908090103020c0f0604030f0e090603070501030b0315040c0f0509040c05040e03070209010b120c04031109060103090203010c020f060901 86
    0x9141c103c131201540c0d9060b50300724800c00b0280c40300600060401002c2003c03030160081c98050032194841e150794000c40c0c105541400c100010000c2150032009500c102070703031494115201410400c00c00510800004807410081020764080d000900460030304006154004500c1170038151000141c40501c1102d203030882c01c0302e1160500500142c0c040c0800c40455102c6d03030241c028170b1158421118000a45c0700c21515102003201c081b000203405201500449134441008024150103585560060401e80f0000342ca4031100e00a0904042c3d0300d0104131440d5900b00710030000200c8044540c0350302d042c242403010b00302c0c500d8003405103031701045100056103003001c240d60b6208641090512082c1806d10702084083c000808818446110070b20464002d40d5491748c100d4000c081081c085650386000300038102807400014055900d000c0d0511081000c1040c030440400c10403011100031034103907107004c0160001c0c90b151401a41640c41d207400042d08580015440300e031000d1100c11200a03584552081b42a1 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 31205113 1250 31203863 31203869
    0x10e0d02160803030c181206090c01020106060207090213150e04060506030403080a090302100c080609060a060804030f020111070f2003030f0d0b1c030908010c0e010804020109030b0a0204050906030304 88
    0x281c0e10420005e41103507210000f604401510b00200c90000121500040e60282c0d040b02c03100558102109010803075a0801c490540403c00780000d000d254548000652121f03024032850314019000208520000000108000905206181c00886041d1024028510782001260340d014510304003000c62140f030210140c0b03109681c5640e1700c40c41560344104050251106601c1102544941001ea2841c08003d001d21451080329540b10b038400c7c83c00d40208048100701801080c081c0d600b0030003e009a5a010310850b600907018101075052440031201280142011800c0c40c41d0b941c00460b8034005c08c2507443c664030f0060300039450030400d100c0e28070101b2150710200d40c42941c5540200200c0516904410162624000204001a076004250041000400721015480071741c054181b0140c10103802400343e4014101c188003c009990003510040e00c0c120303c104009040c010508006811a0321035082d010265134009a038124905100920401a4010303001d520311820301007001038064240041583e0407 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 31206363 1250 31205113 31205129
    0xa0e07110118121103040b0c0601050409080702011b021305040614060109050f1503040c03170c06010608090307060f0501060e18010b0318010507090905060409020102060103120c05010e0d0216 84
    0x800d2a03a10910b250642e100e20b0b1090010181c0641e018080900c06440200b000c403591f1503035407a080b0303130302414800140c00186c4980d01d0f00860401082d5903a00359040c1c10f5080c00d003078003250079584102c4948100400c0003903100e101300e42d142101511541107a805544104028450a402c03640e4124184c54212216030014106880400481c5895120000e4900d006040310781041088500048980d1045800780c64102800c1001c000b0440445200c4418040402641c0c0c00c0c4461611a0744c1c40b5070040c42102c00b01301503900440c2c1e04d07040501c01c55040d10360100017008210304031a10340c3c020b40424850040440d8002400080381e00340103008643d1100c82e181202903982c2045010006d50300702600e03594400b041c600c010007c1c1c0000340300e041d0045545440365200f00b482c01641c40d0981d003001301032134029400c191103180141d0b0000307102410340390300007400d411000942d842201c0461307080c00041d103650b00700144008001c50108440c500040b03603609807045001d01d140e40b070505a94500c03402403 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 31207613 1250 31206363 31206401
    0xa0305070b1306170f10090213051206010f0b03060604080a05150705040f090c02010209130603060c0e03060a240906080607020a12030c230901030605030d140306040b0a0e071101 78
    0x40581c213035921b03500c00a82c3c41c0c0341d43e055444100703201c200e03000740142994840d0006ca0503c41441d00b480c644840100c1d80f4000c050b598180015400010610311491086441c0440840d0721035031600c0a4030301034075881c002c8520383d04403800e1031aa54001203030180d1102e0403500214400c98403403801c850568103001429140c06161108080040405181850031558240f006c010300e955200c1030311880e40a0810b0200b45941513081c42d03000c444d00014500d090080558044814bc0c41c0420b25a5008030322050004104043d811014401c0798071001590242e00448804508600242e00c1340065640d07000444205d9958000280c0c3d4030001004050250009601c0c0d64120f5403194120001000d031a02d8071114403a061031a14038040c1142c2d448000c0040d01085040f400d503413510036200101000c4001380001201d203030f030150501c81103000c11480741000000007415074559030010040c0c684c014001c01c081950320004102060300c2038a145001508000c82440c14510502032000e0002c44011829 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 31208863 1250 31207613 31207621
    0x91802010810030203070308030f010b0304030c0305070507180f05010e040b16050c0604030503090d0f0f0309030c05060c091005041406070510060e0114010c0c0b090a0305070b130617 80
    0x507484150060109600c5248000007000588050102c10002c500c90031150341c40f0306108043d0a41504160001140b1010074800c20001c02d90101d8918032194140c207007103607905a1402d1240c00c0c020300d0307001203007040010712881c11802e80c9548446040ca4418404000d80d0743c07101001e450b61007081c2c07030207400f04824001042c503480140f0280b2501c110b1707070700302140f070107444803542800c00c0411035069010900100030045414404d01c0044200821440c7c1403010030340407000030303062001e4086d514040560720300300348040602980f0880c950701d8000007100c201e85070031640c90840c1d03480112110300800c1d03401140001540103405603002d071228160749100e101d030500180201d80e0050707401500e85104000310034209030701a2041e90302600900d1380403c103030341c100300803441d0003014002818100401d00340c0b1403010030000e0b03c41034181c52408095569850040000039070380300c0c10340c2001d041d41c0181c07000000c050b40280010146040c212412461643c0d40700c400750385100880c4030414142c51880005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 31210113 1250 31208863 31208867
    0x70f0519091d06040302070509130b0103060b03010207060f05040c0506030c090906010512040c03030f02150105190b19090510211b0206060316051509031f020d0609180201 75
    0x61078007007040050b82a02c505240c4141c5140850644040d009078004100a1240e400c11003546c0b42d02c29100c04601802c00f40c07036500ca440c203c034144400b0388000e130342c2c209a0a240c2e41c00e404031030072680c010a05108213a09561810010a000d540480744442c820600141600700384094a108074811504a410a401e40d03041c050a10780081020341046810040c0110700320301c5240d00c6010340c2c002c1c00e000c0e1f401c0d411494081d0201051140078025544060303a4444000742d4040d03224107480301130720941c031420070b100c0f108140381620750410305101c0404100540c0c6565282d46d175080c0707094680d41c0c45050035039401c148180480c6c0801c8160004005500d801804441403140c56000c50041c0740000c0d03040300420007160001d080c0014a40160014010b0010f60b1030108864143c1d81c0c00c1c07807807404100380381c00c002880340c41a010b100c0c81c0a010102f2140019607050142528140c000110744210420080c103031002540051589000a0310f014008203442c40207206d4503808600106151500f40c2540e001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 31211363 1250 31210113 31210121
    0x30305160501150b1c020f0403170f0a17010f03080322050d0306050102010e030c0a12090b03071e0206060609010509040b060f07150e070b0d150602070f051909 70
    0x1054a4030b40d22482c2c04004070b0000701d111001005281c00c180d46a0903100010911031140ca480714000038010b01ca8150100454000c803021a9480002088651024502c050703c0f800384450114001501248040c2d881d504800b00f80100d640c0b004a014490b0b0700d81400b611a40d070140000b510040d814000149102020051024811101400c0e2010202195191490070304200c4040c00000c0c2c503040100039a5070240501e081c171200300805141408854100281c0c0c03034400c00809442650fa41d14014099800b03040054041c2820440342c3e070740c914162101900c0c204003010104500d108044c0c04048080c40810060301600c002040c442c504006400119035a80001e440c1c107074059030354007006100d1307641c08004145024071500700944500003420031a442041200c417018010b41004a00d800301e0070041004401c0c1c510450384070b0b4449035a030314440018a00c0004540c41c40304070003004550280c0000d60301c8115824403a030002141d448109000d5003403003e9281907040403454000740000085508 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 31212613 1250 31211363 31211407
    0xb030f0601050d06061d0406030203030a030207081201080114070c050606010f0e0301090f1a01080312040807020d05060103060f02040b0f0a1e0509040b010305060d03080702010e070e011509030305 86
    0xd0103d041c41601c09010046401d190b12074004101b100500e030901603010742000580070421a0104185c91540e0042a240e101d507441000815074005007402c1044852025654000c030350440d020751541c0c5602e1524000c0050440c02002c220742540010440d40c410320600d0320456201010307002d1500d480c401540c401d40c0c030705001c10900c03906c985861416142407003014241030041102440c480302600700303a000c80f200352841c200304406a20051050000020803034680405007080090107a543c2c1c10070f40864021827030001d40c0882c03207a01c088103101c0f0000341c550580b40a0303082044070412140300da400b01d200d1489420100c11080c80715031486060308014103400070850a1081042c1039180306003440011641d0b01402043c00402c0c2000241801c2c840c03451120b20030300302004282002c1d40007a042400100c0d0007000c0044485c00109658400c2d0840003500821504903407a1540f21501081600c1c0709011b81e208130b074941c00c004680540300b94000c0d4100c9405895062a0904258800c0e0707440d15010 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 31213863 1250 31212613 31212617
    0xd060b06040803070c170703020a030f030c080403050c030c0306160516080a020f15100e090f010515010e0a050f090408093705011e02070306050f040b09070b030f0601 73
    0x40800146960b0600082814030b108003440c40c1c180d404e0003d5582c1c08030354600084002e074050b0b201480117840e48018181581d8010585201002c49468212940700301440014844c0030f01050000030807400280c0440401d608030180d03502c8410517070515560303400071038500700c0f8017180d41170401545024000170494095002400c2c01100402d86600380c0d41c0d03003e40300d002c00592101e6105d005200c020f11200070000000032440583c0c3c24400141050314926018849810070b003140030a032819001c1041d010300550090081c003540c41c0030440c4005c41c0301d40d02d03201d07070105080c500064214030345240310300c0903030384001c0198444a00540902c0b5400400600440301540100301079644c642d03944460000b64081c0d40d80b6680c0c02803007a0008804054561040303e0015044003090100d071389c1100080301030540e01400341290352400d200492800b80180d201a002511344018080042115030510307200340d0241080540030344500c5a101c0c1c0d00d00b031038842d12001d540107001040040c20b12104c1340340c000c8014 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 31215113 1250 31213863 31213867
    0x6200d1101020d091a0f010803030106120912080114030307020d060e070305150115031e0c0302070b0c07020a08030a080403050d06080f010603060606030207020d02090a060e04060b090a02090d060b06 87
    0x84000f5400f190480307113003900d9068501941030703004c021580c002c1e40d02c05107140c403007181075141042c180e81e03070300060040314248003004241042c600c113152300080038190041c109103010502c14202400da05028094100f259128407410fa1072403c002049130304a03070740a00007422450290300c50710001e00400c01203c0e080e001d48200040418802c0100180d000361044c83c01c005545440c000c41c10400654044400b410b040c0200c13502c84550010000c100c088904001107252171400c5400c600a110307034500200b68001e100f0901c444620554042c06030740707200751071807003020781c403040010f94901892601c400007a01150000300003034400c801420ba80d0800100101c1c0c078031f4440309000d04092001101c0c036600d0f995140c00b0418407590740105001850700303040c11450542e180c4c0104030300e90403102029014002c2c0401096020b151980000010300c030b503403c1c0c0304090419142c82005441c41188052003200700f5804100705d0b001c28803c40340d1820f4000e01c1204070380380b141d0720b0001074611304013225401001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 31216363 1250 31215113 31215127
    0x1104030203031903180305090306130302190602041d01031502070b0109091704080309130b060a051804111b1b04090c08030a0201020406090b03040c0e090307020d03050406200d110102 80
    0x4034040d288805c51090316102c3c2c0f01e01c521014146000f02c02011000784032909a000c6000c280c001c14600c0c01401920744032400e880c200e06004002c2d104e1075110008800102c0c036070b0f80b030307003881240500d050b41d1054803420041e4801210b8101a03004441c406003454071180e0040184040990051001900c1240705614210580c44180020342090b40052031903040007420381c0440c0750070f417184042155000020805140e0060110700c003801060490400d0040c00203041c1c18003d0000d0500e1188200200103110511503004000c0e5180c000142d010105101c4580304590a640814640e52125422160042d40d18504c000c000c0541040302058914010715100072641c05001d0000307048031030181c0c00169856241c000d0081148045500c0581065400d00c1480b0008081e0f007a020116405804401030f2501c420640d603085100d0000025800307125041000b0406401802910880b01c090325203601040d10000e40c80f090440b949081c00403034100c0340e40c0407174843c05a41004d030b50300300f050001424000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 31217613 1250 31216363 31216391
    0xe0603010902030105010e090702030d020c070504090f0c0f0602060a1d01060b09130b0f0d02010207080d03050f0a02030702071a070f0602030f0702030c0304090b0d02100807031104030203031903 85
    0x802a0000c49449400100600080d6040000508249019910f0510740e1400d000005d40700d018050b030340c11031a5000120181961001c01c1010003801004108004607612840e00500307203a040d42040f030301d0301144e140026000d50303681c4501e42199804e401510095481100e01001050314a030701c1c008200340001c42e1178200c0001d103d4040540400c1280a54812a52003003180404401c04e00c0d03040e050404038184a542c0722401e020404280503161a00c031030b02c492006074141000707900710b14213511a810030b0b2104680d15800990040400c510004080c0d05e40a891005a03c0110342800c0540c6c0201402c010302803406049029041284c40c507542008417541c0d0300b40240e091100252482ca40210a220000c40d07601005a00f04115000a503d40841a600b15449000d10f1082c09006955195242c1da00d03121420403a1b00c00d0341c0140f550025201e40a4003034000f21068890b03200082c0ba05003841e00c0b00c02d0003401c403001c0d01e4005000354180b105070b09986401401c034000b0300040589504414100350 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 31218863 1250 31217613 31217617
    0xc0c0d0602070b1807080a02060702060306060705061f0e0403022a041d0105010902030103030c11010e0904060518030309070e0603030405040c0f020c1807050c010b09070903050705090c16030e06 85
    0x2229071301c2540c104441e0480d01500c1c2c00c019411080c00b58220850740701c0141e881c80300300c418460303050341c181d9120754a0310009030060250703110103482802a0000c1041d000c034841021019241000c850542e0562110381c0c5600a82c0122401070150b4841c05051000300314000030981003a2034040d503a5801e1003440c003c80c050790003a132404078118200d006a502c15030020b0140307030301500050741c0c2103046600d10f0320300400010701004080c0c40700701c08611204060340325940f20125404007916000450806180c004001c080c200d514140e2007801081c4148103c00c040101d0303006000c00700051641d141085101c081a000180110b90b240c40100300008441d291070142e00b44001851301e842410140b0000040d09003640704003110712600e041c09401d078660002c0c04030713a40c10800c80e282c12034851949000c504e004100b00d002c036561001c3c0c400104141c1c41c0d405484c41094a1183d41580c140315503d009000c0b10501c02d441d00c84001d6018000940044c8072026a60002406442d082d42d02d0078200000c61400d03 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 31220113 1250 31218863 31218871
    0x2010e04062105010e0f06040212010216230f06160e030f060906010608010315020903011404052d15130803090c04060501050a0918110c03040306110c0c0d0602070b 72
    0x400365080c00c034180b00f803c3c03143d01c508645150140089004198140b9254200104000d200b00e104100308150540254186d512810700550040c41c2d184aa0410b414440c61420320403078aa58074490075003000d000482d5801d10400c00350024502038840c4041900c05600d9040c42c4010086120380712540341e5420410540000c00b1640903200608081c0c0805040940c141c02010a102c104001080001c1c00307120380030083c0c49075120040c2c0b43c0c4e4403140020301500c1810820840c4005490501c003d02c0808120109000c0345c50080310210031001d440311040108040010001c1e13000b2980500001b180341d10100d9102c0014844481c500d61540e841440c40d0b001070700c02c0141c1d540090100b2016042901c9107034007600017424031a051417034280b40200001018003900711540c19a0030103181ca981241c0210001c0041090b0150710348011800244d9660800c1c4002e64149080c801c0284ce2a140b00045503c010a54000340c001c0c010840d041c0140c001305c080049550b10ba00704504004070311402c5041e030003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 31221363 1250 31220113 31220159
    0x20d09050a1202070611030405040c11061015021f0c0e060705060702070605070b1603020903030703080402090a0504020904060908070614071e090512032803050a09020a0302010e0406 80
    0x100c0c00b8541e8028544030180e00300e1028000c01c9264600c8190000003038408440007120086030300e1150050440d22264019020307000c0740304107418090000301060a04065481840d1702c0c00351200240e408036980c6014803c0350301803480440c000301000d40d294001c0c11081125090400d8011019408112540d10044050701e5903001141400a056414000785000b031045152030340c105900c54840c0000c2c11030140480e0ba00456012000701c0b4903001c0d4046d20507141004042c2e94840343c2c5802d01400b110030440d4102e2103284c41400107400d002e801c0c440c03640256006020b0762803650329680d0f02e100a080c001d1b4299407e00701440030b040010901e006090518954141c0c3d803000d41070082002e006200181c0c10300d6800d2103001c5440e040c0992080f109000c0710021104510100c0e500e045480c218400e002c003496020040f400034107400031140d80b0021400800d5030b8100a140e44500e2418100e40030804c1c02540002441d4040015610802400c00324640007040006d00340c0d56034500d00d40020345c15010000d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 31222613 1250 31221363 31221383
    0x50307060903140703080901050d11040611010605090106051c020702131b0c0201020c042316080c13060c020622090b03030c1207170a0309020a0602030901020a06020d09050a 76
    0x800c1021040f65100040042c0c0300a00f07006040d42e4800f441170007091021810070034046201c0203410403d0b04044c80426604180740d0341c5684482d00108101c0d07802c03124100c00e42c200b03c0d001803030342010818130b41220100e944403070410f40722004020b000a40320740300c42c000070b03003d1011501590701c1ca001070b803e102d940b120016040c1003101034203c00030804a020021300c1800811040942d8010881e0a03002c6000c850026000155810707010540b0f402041c4000011032003010012006c4400d501927002c00c0b9507840b0000c0030780c0d5926180030381e80b095070381c044e40300c10403100e003044250b001e0600f14891601c01010301d130401a08511018040f8401010000c80740e250b46030400444056100d015410302013907000e1440d1041030101d6696640e032007401650310302d10004002092050881144d4410320590100356a261607060340140a85030a03603059200392820f0100103030b05800001140c04405060b00580642e008603200c810003134000001d440b40c001d446200c0400041e505005120b227451040020306 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 31223863 1250 31222613 31222619
    0x305041e030201141c0509030d090501090209010b040f0e06040905030703031505040b030604020d0f120309020a0509040b0a0504051c0302030a0f020304080301030807031707020d0f030b15130503070609 88
    0x1400104e81150792035101d4410081c40c4590f6050107145440600210008030381c079110200c0345851403040400d2080420316002506041110640016544070300032540c90300280d8030781717102d41101d1042c2d11400003a9400410104040762084c16030b181d01643c010000070308843c0300c3e00d81600b594084a0101e00003640c401004d0802c2d044040e07044080e1071700b9142004071440f860701096071440c0103400a4811508400b001c42008070411030550a290320000b402500414404003401506c48101c040713100780c0702c2500110702c0e4207010244502c9a42c0041c04654141c0742c144a00c1c000345400f40c01941c0304c0c05242044030840c0b026049501ba201036583d001030782e9140841440c411141c0318040681d60600402c2480086910081a2030640c3e07000b0514035070b10a03d900e020f42e00c080e0010341c0898580087c42c100010f85402040d401c8030001c4944848000150750b08044040340d461a44480c1e1100051540100380820170006d0f0072542c0c41c1450824a00b503c480000703140030341551200000408021041c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 31225113 1250 31223863 31223867
    0x3030507050d05030c04091104121505010816030b1305010204060e030106050a0302010c12120501060314090d0219050f010e06040c140a052b0b1f03080909040305041e030201 76
    0x8100b103041c491a2090450420b0501d19081d40300710303c50300d1f9200341c6800714559034080f20012a0001c2c2400344072251440103600e8a01e5000340544480038400b80341c000001146580484c145c24420b40c0c501a81d104241180e41c1c2c2d44210b00c000d03042c4c0a910896025441c0084c20901c005c1028000a4480d05a0358480000f0503094907510f42140d4018049401e007000142d81120728a9061944240302c0e042c5002c00c2c480071194600c0c0c8035004e204c00d40c2884000202c0035059800107501081145000b002940d4150080c0c2d5622040c01c807580041e0300411000c0c115140545000e001203104e0380039200c0e41c011481e0001c0c25146140e98006098001c081448100402d210070f0f80014990048401d10300051308001550101682c8986c1e801110000c07107190040f110003054100e04d40903003451507500f9155003012070301200102c5940350001911501c000e0076101103003c0f002203942c801781803490244158203008540b00b002c0d10480520005200120f001d1202401c080f0888003068500a0307154914000 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 31226363 1250 31225113 31225123
    0x1e0b0901050907060c0503030103080a1103040e10060507020f10020c030a12020610030515040201030f05040c03061505030604060207050a05120d110301060806010e0f03010f0204090605010e030d11160303050705 92
    0x702070003410382441780014400b0050300c0c1103d4001d05404e03141c0c60242c4003a1100b152240400c0468000024003017242003240d030580b80103010011a035510a51180f105903098810440f0103035010170310b0041400b00380340440300340e41110340b5803066502c25000c29011034505040550111034030084540d98081c0c99a04220080c1d0001c441881c05040924646800d03417504400606030b000744d0f21800000702503900076081540c0c8010b841b0001c0005143c80c0c1030407030400800c1c1c00115001d030304281c00600219070840350720080c0c50307008000e0907064450790745040080d4051101190140140e040000204809008014020089c41c500c180d980c0b4147d211a41141e0350b0340c3d03402201d2030701403006000340d41c0c0c403440ea994080e4081c00c001d4907514403a00040c1c1c4129115803159859030a05103031122464039900078104a82d14a1002d11005845100640340940344081443c0c042c0d02494500f01c1e00352145044000300c02c0403400f42c85d01117050000d01e44550b07140b0341060300494800900441001400c100c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 31227613 1250 31226363 31226369
    0x60f06180b0102030a0c03030e03120106021b010504050f0105090411070804031202010606082a0a02070f080705010c081303020603070e03100b060307030f020c010f0606110106050108041e0b0901050907 88
    0x8051842c10914060203080f01289480203010141d4800c0320101000d820821901d001810be0801d50107580e40b03290003903443d52240348400c40542e0002c04034902d54044c2c020743d0281d4900800007107140d8001001112a034004010b881d91240d00c030420000b099450340d00900c3c1860145051590b00c5045050803001420b000815108681c0b42444c00c0001940c04503065402c10003a02107000c07a20381c09a4801728032a60a0314800d4500d000050201c41036400040f00c8080fa5607402c0780c4080541d6403103009444552034403815011031903902c0300380000744240d4000c2841032109813404062030385036000308400b90800c482003001f14040b5a000c1b8524074042220981441d40314009101c074000b9207010503034a00024050205043e201c0341c0344c11003002150151414219114000c006004450802c000513161510480000c2240d40b4400c080c040418052074083c0c0d41e045e12a00070759151540c41f14488500c440e400400801001501c400052000003214010b0341400d001080030b007042c2603030604120040d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 31228863 1250 31227613 31227617
    0x102120c07030308060103140a06080c0303040f0e04020102122205032109041808072109030206130b12040501061514070215040e040507151b060f06180b01 68
    0x4404001004400207003801920b0b454034240b04261100300c0140c01a189461041048510082c20040c104010b0790103181184d0003c001c4908607060314060549900c5540104607100d0071000b000c1c031403c040040115040351061049800c00c1071548282d040c00d402511852080d404030b500d01455283c4404041e1000d0001140508823544920103100b2a114002002c446041e001103100610359589a00507056050a00c0000c52442100d20b801203495102c603804541d442c0005d030580c1e2015805110705c2142d80483d4841c01421401c1d90208000e603007000c420b40c40503040fa214003041490740100a0b2210012101d003030300c5641820324005003956a40d420003900c04255810314407030190700040028141c4080f02c02699100868004102c00401c02e1000c140c4a00d00024006411441c42c1e14140c800c6006109441945850710002c001503241c1807040d000081500000640701061300c500038a005116010010710880748200c80010380d40154422052281e81032000c0d03201514a0080e140501424 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 31230113 1250 31228863 31228867
    0x10906082a0108060a0f03060b091305120304060f020409020a0905010203030c0d0203040507050603011502010b0a0e06012609030409050f07081305071e03030e01020a030801170703080c010b010212 86
    0x1400708007040003088249141000200408680383d900c81c00711040240201550300e164880d103d040c064080d09090542a000d03480d00000106240019000e840303202d540440602400221060502c406401c050700a50304c01b41d5549821000500f90310042006000411015840c0c1e807c40e0000303041c800e0254003290540d00b04004020303032818601c04880761000c2d2064016220380300c038200760340340c82c0c45d03600460b82040c1c0c004008640140c05180c03131044541e443d40284141a00b5406020f4030383d8152140120303d006000118a00b90f01500401814021010080c1c0e0000318200c0004c0760884252150310454100050070f001c110898015070344d00c81d00040c005070280c03c00510041102e40024501c3c0031803200c9410180030007000340a0f0b0001060b10104500410140c2d51810000c0400b42c44210089000c46c03801c04441c0d40045004c0e14600e4054a07038100f540c3c44c0c20200d1081d0b045001c0085664024080701000056808010b0159424901c0000854180a01c0060f00c0d1404016820000303142c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 31231363 1250 31230113 31230163
    0x3020f01060f05060c03070501090501092a03060902010c020306010b0910020303010f3602030f01052e020a0c090c0e090411040902060405040504050105060301110705150603030405030601090608 85
    0x100b409100b00c40d02030f80c039a81c0e40c10b41c400003e07040d80680f090003400d950a002c03141d020b01105401041c01203002d1224204981d0384240214a06490700180302e0300783c0349040d800c1022404a85c03118060600604225400800079800a0f08024098102c80035143c8085940c2da468184040c000280300b800780001c61843d4123090002c0c0694195204010b201103170448c0d14074000424034002d55a1660802e840c0e065484914000006500100d44440080340c1d108000280f501e0003850241c80b446e07841c0440341900032440b501c25440c0f400c003040002580304592141c2d00045500318401c0080c040c0e0b441c005400681654024048a030110095100314292010300010070300800400003410000c4800080319155071010480901a0764003e03644203142034200414041d042d006144178140c124000c100c4a5800160f81c0000c1c0900b0102a01c990f00440c10140c0120300c5640003074000100500b12030915a42c0e80011780307050400d81005811035141e0a04203c0c440b03040100400e410404030f4542c0314241 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 31232613 1250 31231363 31231379
    0x110312150d020a14030a08030c040305100b090612031b0102070203100c020706030f1b031d06190509070803070c0806132001030b040c0e0a050d0b0c0d020c06070c03020f0106 76
    0x120f0b83c0220789200380031014284450344c040003c3c5100070f034080301850b182d1410501d0024960460701c800e654038042c00c5c00e20b5480080c42e00c01c0c0184114000e144039100e88031682030110030459401514550700c0b08001d072031282c01c00b070501d0311380c4504010f00269480300d00e07106043c201a242d41703c143c2214100303c1c0010142c0d401240b104107452179454001031070700017a0211005001c03044a004150300c1c1d00b18007504525415000054900c40d2202c400040c07041410440b552540210760400140c04681e00032000d0200e40d420458000404404940355152545011401e40c1e111340344c221403082c441d0030100b140e088203100d460b0f0f00c00410025041303440103580300e0148140c4655000044078808000b0580c050f030083e84800141080500200455200220090300702c00222070105e218030803601000444c1d190407084285a140c1c0400701c5043da4032410307880400e6400400141d00c41680070f008813400340c03a01708100f91280c030080d035800c000c40b01360b07090213800c0900c03010030608240d0500c60144400c00c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 31233863 1250 31232613 31232629
    0x903050307050d0b04060b030a050f060a0b09030f121e0909040b06040e0a0c0906050d050c01033201090b03010902010804110f060c03090405070c0309060f110312150d02 74
    0x208480c00c1c01642c0b03c0392902008000d004888846603c41e02d814008a600407a00b80a184205132074442040285c07601e900381004030030101c8846500c90b900a40501c80e10a41102401442c4006002c0f2021102011811410240599640306440d0740214140c06514510407031078021208a526051405000a01040302810010806030000d9a0600480c01039180ea5021030800040613040d104aa029403a1096604070075204480025040c0440864103140c0217a045051a40c0328005002001c10f1500660140c011048041e401d0200369074400411a600700c1d03a280c810b4201c0004c0061740d818440060200c41c14480e00e05d001e0782c541104000140d03040440b1540103504005840030480c840e00002d0030f2101c89070705031908010081a000e0b0007120000142c05401b904580900403565110310407682ca5a4400014000613000030003044164040c1c84a503407004018507208d90088aa040d40c945154001c1850400307541060041080d04166509204403010048421640071031654000646203 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 31235113 1250 31233863 31233871
    0x30f06180d0f020a1e06020703020c01030501050f0f0d030306050d06020702040c030204030f020d080c0d0503010806130302100f0603080403050604020f0109080705130212091510181a030106080106090b0409030503 93
    0x10b5009046217100e40042c0780c082c3c04980d070003a0700703560b40e0b826072600940f81c081a1600c54003103814000081403514203010139000038000035040c508810401801c2085942100030240c01389650b6400208664403240764044110740503110159944401d407040c04201e5600003080c8040610601c018030000d0002c400c11948541c044811429070a02414030f20301510902c2098111031090442c2900525000400346040f1140038050342c142e40e6801c409141e005a28030360050068001d00003007a0080c01a50000805a69103940010919101e5407621700d01d03801900242d651b07910030780c1048114076000350011050740080c603100070944d107000000e6943d16007a002d5035104200c0f00c80c07110b800400c00e41c1a50b002c985d401880b5075941c2412148103407580e1000c04500c0c1c4220a00c0005405000c0d40f402c1d1404a8905940c01c1210f00f03054594080100410109008030104c210440312103560240244000b4040800001403442c0c50b18181c00d0450f5508100c840c05941401d040c1c0300441d4001090320381c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 31236363 1250 31235113 31235123
    0x20f030c070201140d09150207021804060603080703030203180705030705040903050f070615091e0b0f10020c0307080111030103020405131208010302010e060c07060e030f06180d0f020a 81
    0x44058a20041e5115018003134403810a4070041110800704425800c0038440e0341c00780c0d02825041505d400309106910411002a4219802d0b4032503001d405922140c5070b600038021070f400505184c996840388481e40c0407600030783c0002e03004020300040c4840c201e14441c0c9421400006c0403030b145060046921225588900361140382d4070103515050500800c111202d001c500800b26941c0c0c415881c5c100001c0004007a5038240c02c003c03d0300400c40329054410f000c000c11100652000080420b1041405494080c00301900710a2921034180340e500ca240100010156940161801e4101c04080c07502d0102c2980c0402c0260303040201d085200c02d0880d080b28196501640c020030310341d907080d803954005021584002d01e0000045401242e8960022900e81680d100341e80d19255410003c00300142c03409011110a0140c0000e882004524040c032385072136403480d028041e92000c82001c2865400d044003201e01c105100c0b804040000d01c0f41c400c1c4800f409080c5e040c20404030368102100000d42e00c0c4500040144 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 31237613 1250 31236363 31236367
    0x90a020111010e01110c0c090f0406020307170702070806070507080708090a2102040605010c0b1302041811120105090d1103040306020301180506060f0d0209120a05031309020f030c 79
    0x100785800c0d0400a01200e440c8024030815911000c103c646038403080d07880a41340100b098049043c42c101c141c29019103011070700401075450307980b0b1743e00c000d42c400380c9040e09104c01c0701007004401c40741d100928890283c54008e00761541c074010300b03103090050080010342084000c1001000040c030550030307078079080c1c1c0003040151a20300890224400070700b590840a00e0104441d00300c100950034013292080c1510a4806100540c2c0d1003005603111066204020204a030000005a00007990076101c0005800200042403000614400c854003100c0d00d90161a07881e40040351510038145a5244500394900400070842480c0c45150030340c583d004e0b4542c1c042005051035901243c250200140c5002c2c50704400110f642e96564803080103c0c07550b441e6200302c0142054001901d519081c02514052003084151618181002251000961020307040300d50004e00d0744214101d000301000b9041c44180309400842d5142003141c03102401e001c0543c000072b2840d004200161003000288141d80d00a000602d5480e = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 31238863 1250 31237613 31237637
    0x606060e01020a150e030403050303070207050d020a06030b010c080f07020306090604080a0c15060f0602060a060305030f0702010504030f0c08160f061b061407030c02030408060601050c0a0b010303020303100806090a0201 96
    0x14043d217006010080244804940407080c008040019409120140c00b1590855038a03414002c03102c254020103503018012a80402c440c6010303400c40d00c48590140350050004449544401aa40041d07102c020219404144c2804508007001076a41051994004202c030346030940c3c441115104071051030040002045101d000c01210030280b42d07420008a00038004070743c84110310004e0341e034036200300c90062184e1000f08825850b1032003510107480c2c000011b5864896014503090311035010510803410807800700170010100d0304402c16010800d1069003c82c1115107418001e518140a09033b005007111a0040300b0032a40b00102003000840300c203400c0c18038004440c40e240030815111a04040c0106041500e0f03500d0300c10400301494400c0c841d0752002c014100301300c08126501d020714010140e503a48003c2c0460b4856006034040c001c411031f528201d8040319001c1d550307040c58100a07030048001d40c2c4003005002609900403010741c0035040400c014a201e10340406004d50782c20341448041d061200c4c2074900 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 31240113 1250 31238863 31238903
    0x60f0105041809060501150801060e0a0305010e0f07050a08070e0601050705010e0c15040e010b03131203141b0703080a18050a050f030f0a1b0c120606060e01020a 71
    0x1075030082000c04003038080981c9200c070101c0a0030400400b110304c145000c0011400d01d142e112141002c81c5103680e0301136560b0801009907100c0c060000c40c1503221791081e1002000410034003580000c000700001501c0303c43c60501e4010300d0a20070385c100a103e9448144244100392002944100701e51091143c1400b40d191140141c82510802c4400b0708a9402c1c0607207540318420000d1002040c840580b10040301c03440313258020180d4011400307032182c1803010000400003001240080c50308803000c5003048101007002d60720815079020b4111040c001c282c03954009200c0414040c0d40a501003a48501054800c903903004034500c9105181c001418410f428011500c1410564801c481d214903010384010116030a042241d994610f554003140d4500c2040e90111240d20b000c02514005500c200b030f0310b400c0c82c48e60142a10b200b4483e03840342c41e44541c1c0f1442d24000c5030f0280c4d0480000c20458000c150042040d0401e40f007569040e1308954140300310040d156403582d03400103030b10f03040d15000f001d0110b0400c100128 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 31241363 1250 31240113 31240117
    0x50601090911120f0903180303041707081006050d0204090c0302030115051302040302030703020d050a0605070c021003110f070206090d0615140102030405011d0409050c030106090212060f0105 84
    0x10031035026203486014101945840000c00f8803000340d0405003601c0d0368451202804200440d4000c10a420078080040c4080000d200c0d20b0404000500b680d090540f15550740c1d010485400d1081040c0d84218410040382070709004911301202c010100b8081b10341090007050510001043c0280a20303605c6185000340701510822402455004000f071020b1240e6015205d08415180643c51282d005010524000c0c601c5100702d504a0340d003e409001168519020050180300055041d1524018158140b0000303040d0302c02d407445042c450312401c08100072801402192620114500141031170050600c00c3c141d0b12409560f102001b0a02c159501e07080382c40400c50078060001d25a42040b411b02c1d4403010000c2c9508582c54020307600d403010484a581c0c006d80c0fa0a041c016413400e000d600100002d005551040f184030b65452401a0000c950b0301d2180041400c4540c454029980c60300f042c40910021325003801181c004000e5410191304080002d40000000302c8050f0210344614100e100f02a044c1c0d026000b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 31242613 1250 31241363 31241369
    0x11425080901090210050a03060f030213020c1207030f0807051e0c030d0603080403020f0306010b091507050d08010602011508070b070201020708060a0504170a08072307061d0f1005060109 82
    0x201c0c8058006401700034107642c00c203000d0000441c0c1840700200e0b01030700f25120201241d0300180380c8480b142210b60b8003c000e40c030900d0780c49614040c6903181d41301400040010302c50548256102844000c0031035004083d40f502030020740400c5070070045000003107980d0041070100c291000ea00740e1341c0d810051100d0721b10b200d084820782d929410403100001b402241000703002200e00070f482410a10741d03054200b548a032802d0003401c0b0306c100140982d407940e0520703802c4000d900c0b589443d491301d060701a1722880c0c80c248445008030001707030058006205083c1d080c05140e007001c908420708540c030350070544a6a02c41c01240920702440c0b1012540300250782c0b00f0040c4000612002060314803074102a00c06901600c011502a41d0f40c081090820404144403011903d0500142e170307880c1e005840d030820446508204001080d05030141d2a20030a401140100030080b480c40741d640003906080203821051200641255448103400c40702d200c00c03000101150f0307507080c11031224001801d96140d40040e5501d05c2590 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 31243863 1250 31242613 31242619
    0x7020304051806100203120a2c100f18020d0f0c0602030c0706090e06010309020d02090702010903030f0501080606010c03031803030b0906090c040902070609140114250809010902 78
    0xc26455002c1100095950040005644199160104070010385c1c0d244107501034015800700700000a0500d01456119020344030910100e20748007038401c01c0b07251010700034240e5079905030404903148403444c100e48640510002c40040c18042d035a400c0c01e4587c1c1900c12802c1c0030740103003001a04030007003280412800c0d0901d9403000c031200c4a16202c03c40203641b904001b84803c41c51040300d4020840d1801007d4400c1142d0a80301950415a02e00380110f0203043e25510482c1c22103d91108600141d84144c4040e121301d007541c0c0001808255410014142c9400b00941000245010300601030764201144050388501e00b0308100e0b40c807a07014a0220300511201c0070241000c101030020300c04240d4590400301240c88200d81c80e00c000d40316502048841002614071307540884081204000038019600030b440c001d809040c3c00111284035445101440c003908180c100265900c0c2c1145106503d9400916003000d504800080203081c000002114410800300040510680000241080c1800d400c120403843e805 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 31245113 1250 31243863 31243879
    0xd0b0315010303020f0601120506011502010912021f0501030f0204150306050103080d060e0702100e032703010510210c0503030a110606030a0807060b01143705030703050702030405 79
    0xb90800a40301d5948100e400850300910340001006416202940c85054000010702080d920f0440040303102004001810103554032412602c2c0440c140740120b1003000c159801400602c0d00800e02c0442e989281d20b80f250f03960385041c0040c4041032417000141211541078500182c81c20203102c407076800542c04d900041c00c550030040040200010034001e0300d101009031006000c495150124403c420b00101c0e0040c005038054038520216a07480d8100c0c511000707440b426a49490071400b280882c03980c040308101d1220168141314445d50809200d10b0f40e1064041d4081751255042c10040703c0c1c40001341d0b180a1400c08400c07030101c2403000c0c480044004080041c2101c0c2c0c0c4501c10480903004204c40c000c040704501400c40024205c2c240892010704c11680103441528061060361010020118040100e0410088680c15520700003154001c1080140940764031804006a10824940900707801c3c100158180403903446284a81000903260000107505003c81d040da24024200e14501a5500142c0d00070a0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 31246363 1250 31245113 31245119
    0x2100203040f0b01090e0d0305070e090601120c030209030c09090307030e0303090603040302010c030506011b0201051806040f0906120b040803041113060306060506030f041211010c080a0c03110d0b031501 89
    0x109030f11002c00c1c00703401001d444002490705002e9044440882b03808011074030403441c1c0009854110f14541c1d004805041401c0070b04040c00d51700d0f007128000c4007400040381d4002403a03811407508102400c0368603404c079881901861700d540c040d42c59018107840102800b031ba15560440c00d50f01482035844000003d0700c1240c5916160800138003030941c4c6201603010916041c041002544110000e9002c003640e09800f81d0109225401103a03598000c0d1030401511300842c1d1480503076039640e00100002e044202c81880003905004ea4042107403110384c05008844841c4910a000410a40300d0640c082d42000e0303425180d503078904000300d90b440006002039200c004400c01d100f54071201e5010105480c02500100032080d01d550074800e003803106450000c00340c0d01084c0020001003070b4120b0f812200426203404601d03003c480350700600751800c059111010801f69820454140001c4c03040152000c082e260512038280303030b1a4030302400e00c82c01003d00c1180d07850b4454660143c40c1000001601d114211021890703680d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 31247613 1250 31246363 31246379
    0x29041a13081504020f031b010f0905030d08010501020f0303090a06090204151e050108060f2112070308090c130e070b070c06020d11030904050402010c02190608010504060602100203040f0b01 83
    0x2c0e04842c105d20031492031240320f805080c001628503000049100102c2d03822007110040da80c0301300c1078130a0700811464280200d282e8500b0b101d242d03607110380354507911195410800060f00346044804e4035a040c0d0b000348108a45440005640031400f60014000200d500d030354004a130203480c80c40320f81c0c0810956410000386860000c0d464040040541c2d6001400c951600011a92088141c0c0c10950200c0b0b0900d9051030340c0340a40c4000c0500003509200060f010b0031012075418101c508400008080c0c011904000b071540010145a2110303158014008112400300010304d048000290210001e076601d0f540c250b4034100b003003124043c20b00d00da520303521500c5628190174074080701d000b074030014002d40d4865564640201f10190b8885454405181054410310603c4001c0030014410b03410403c9100b0340b000075807144050741c078003600f0f58030a071109141016005845444181c0c49240128078108003080700c294040b642d24070b044012640540d0b60f0311241802003000e00400006001c108031000005141ca03 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 31248863 1250 31247613 31247653
    0x32c01030b0f0108061e090703020c0d03140403080c040807030f0203071401082802030a09060b060c070b030a020c030a170106140a08090a060629041a1308 68
    0x1509036424080c2800100501c040540703042d01d141e002c01d0303101c2c010460a1a0007841c10340605210a4103150711a4050006074840005840d0301001c65800130310703e003e1a90034094142050914182480301000c03d07031080703025a02c0104054100985800401c02020455003220004d025803000c5446043d200d0416001d0030b480d481e01240b02c1d202e110000501640c0c42c8c541e490310040b05071145a030507519a2442d414081000601d42c0521001c5005400840324a10140d0b004079101180081c0909081c54201d007107036a045030a5200d10300a210810150400090690581b40c41e10748661b102e44600c0d9016000e030181700e407400340d940001305000c04001c0d8001c10b02c01c120100083d007080d01e6684c458040d108200c2625610754021410018070001034081e512154110002c00103c0c1d000e084580c03540d0040742d9031900682104025840700200107814501170a2440c462003106500c0e0078a4074440c40100c07200c0c100b400d0340a4902283d505609008101044020324000f02039521007944042019104 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 31250113 1250 31248863 31248947
    0x20304081c05040b0a0201060b0703030b041d0c010f030e060f0f01150504050f01170a0606020c06090906100c060c0509150a0c0201180f03080301030b09030310030f03 73
    0x9441400311100754008142001d41c010380c690344809241c60706105a0745003c0d40884d560000795902c0d12070024040103210010140c0360b0080ea0000b1b0000c2c0707454104801e640c120400c04050b100b8500541c40b00d00f0001c01c0d41d5060300001d003804514180e400344141e01418030802200c0046c042d28080004074404820100e12034032200c6611200b6a0300c98440350100e04a03810b061002400900003804942040302c0901c41c40342c01414000c0c51815200000004c5c3c0c2d0382140d002d0110ba445250400000b60104038040c4c0780802116202c6c00c0030203203004281940401403489115031040084101c0b594068141040c245800410902c6810003000001c0c286910620809025540c0c40341401c02d50740952007518840318244d0f480103030b1419650011a00c08025501c001c21180902d500090403400312800400158400c01c9050303200c0d891414562400394000b011009580c104008200900050f1101c540036241c0c040e03d00704c41c1107014141260b4402018504009440b140d0640208142000000d4408 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 31251363 1250 31250113 31250129
    0x71707080c09040b030f0d090e22080f0a030e011503020105031b070506100302010e270a0e030705010b1009050306010314031b01141b0a0804060f1503030e060301030b0103080c0705040507020304 85
    0x25031689c4448464525004994440c641079185405100180881c01d0780802d05005491050070b200140c0c8485c0d1187d44281c1c24040401e070360b030007a02100f102c03e0044c11081d000c81a1100300f01031035a00042d0041c4001840d00c2003450303480f210030071940c520109a68100b43c0181c00c4481d18a0540070703c85008401c1d00090740455411110340e40186001c1021000079417038450442402c0c521100200c54284c4080d05030404192505410f82c40314000308060000c207400307440081001c80d01d42040c00000c881c0498200704100c01c014050040d81c40009072141100d0b03000004403045022074600f54194000c0395003a00740c0d810100303c660010700054126032000802608526041c0d250165074101d10a440c00c00103d4104042c00701550550040041c2980310707016802c0030130000079080740d0404a40783c101800400745405207051061690007100145200e000f5600c491955045460701c0c0400c000510000304903120000702c9031404041401b00800030070010f8018003c074102014007a4403074010703015101c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 31252613 1250 31251363 31251377
    0x1a16080d1404230a170d0b0301050106090506130b070b010306050603010b130c1b1209170a02090c0c07030804080d09031127010e071707080c09040b030f0d 68
    0x6403404150079058081e552020072810803103001e1400c52100c441032043c101003405210840008524440c0ca140480002041c01030f070785020401d6800d003140c60000090380039a15100050048603000881d80c8180d9008a0706a45c9030296644038860344a0140c001038038180c00400c400042201901065050341e2183d0b01c04e1041769600e46c2494202c56100600b03075802040703015040803c2151381c0c040c110100d850701c0d00040c0007213101d0b0340c1c1102c11034444c000c03030305400c607040141801c130b9102101d00060000d05000f041d0fa440d16440c0da83e61007844c048041e1141600305c0c0880d00c3c01540004031b490003007100c030640340000d43e03c2c20149080d400a108210360350240c00e000069842c46441000203803a400b2100300790342c003a25418450f00f10480c4050140905139070440d616122984ca00003130091212010640091414020092815501c0e07208006441441d005110107160483e540c40d511500c0f000c12951110500c00008000d4000d0700340d02030301070003900240844d42c4404140801d1800d01512648 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 31253863 1250 31252613 31252631
    0x27050604020702090a0b0a120507060201060f06090603050622060503010f020c12090d08030a05010618080c04050405011d03091203030118020901020102070c0608070908010b0a1a16080d 81
    0x80309911840100a51114103600018010b0035143d11000c00100058003c0c1e811503180c5031000c1144ca8842004d45042d48804c0003042010703824052440640b000c6e6490b486440d14040004d0300e01c00300390145009050701d40000842c0c641f1440c1000481850b06483c146018402030802c0c0014603060044c0d501950900041036400940c3d8000c8801d0302c444080209440c0c0c1c4000054086034002c0361000340d028443c8030900001c04d0485004c0d502503040104001625450070354040c0151042c1100c035042d4038440c030800c02c22041c0c04200310701c04c44800d48002c61079944500e800380c01022249480341600d5280d0380f06a10604c0004041e1441c00001da0f802c2c03a4900d004240380d0703541d000034856040031400d180030912100e4200d80180c403034081c06000140c102030700d0390b031944404001c1d50440d000045514040003c07044c0e108900200600f1948000c200c190440004904c84c80300d18001c0304d40e03001040382c51100c1c01c880705040b942c07586480107610191045a1030300070314540c405062890840c0c1085460 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 31255113 1250 31253863 31253869
    0x607270603020d110307020d08060d0b010b18010c0209010329070509030f070807060c03030609050117010b0405060306070509032506090602011401050d05010f0507020609010e0109020604051504270506 88
    0x482c002c2071b058004140c1d95a100d101240c1d54400104429082900301d217080d0002100059824064442c06980c6600e0300d01c07007211a0701840c4502a82030400c8810852072026071642d80215042d217400c005800b40c0800e024841d80070f10640c0c46054840f8040748000c0180450b4003030702808081e0741c2241a00c000f801c3d02198284d454a0314021a5402d800c6130508012803801407610f20210307071181c100401d50355561100c000860b0804d1b40401035400050030100660729080c850907540003803c84080000e42446c0c00400ea681d8030080180d0300307000c4000f40078000c55400708080e036481c03c0040900c01085503450f071007007020b60312803158401241e1250b01c00318000340180035400c401c420895041000da80f8010030442c2130302c2c41c0801a1459585d8100c44014052130b070013030750301c40c2c52683c00170308040c104001d10508556130510b1000259160200c1d10005907184000c94040703c80c21580c0c0700c556a140b14101401d44544e83c0089000a400d081407044686904603815440d005640c042241e0b90703444040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 31256363 1250 31255113 31255117
    0x9111903050a11270a0f030510230402040203071101050103061d060705030601051c02180f060c0c0f01030e0a0f050d090e040f0606150c0b0c0703020607270603020d11 73
    0x3e03000240c4410f82d184c0c003c8000035943c0c40c642200200002116552a8922103e520250b00300761000e4100c002424455092801903c1203841455803040005038094100f0b01c24800c00381009100d80d03000004078420300d1042818880300480d50000304030950b900e2400780000e200c01c00c80102012a20f4110b0410382c170000c01c9940c418181ca48506145a407001c0c011101a030214084c00d40a1101070071804182d909032016048020b072140000303019042940030400c82075511605248648000c200600307580c0004560030340e01c400c05032031760308004980c840107134050f06030403e0540c2240b00d213400c02000d01c0503c2d007003501010301583c1510107645007a0b00803a1110340d14020700c04400344041c0400c0014002c1010001c8050042c900002c9840d10784030441d03204118075002d00c00180a107070000c0b060203c020041904110307000c0029140c181180d81c069142c4000402c1c2c002844004162064085600614850440030b090b45146e200ba460f100302034000d41000410241052902031400030405040003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 31257613 1250 31256363 31256377
    0xf010608060303040611100e0c031204210213050c0d0b0f0a1202030f07060207050f102c04060e07030c0c1502070c0801050103060903020f0601030c09111903050a11 72
    0x1000c3c529140c200380080d900d001c44051042002d01c40c100d03400050b2021445810381c440341c1d100203080c0d03040c104000c00d0300e082c080003c9045101d40801040101416140211070180140c591001a0b41500c0c0001549401180d01d5421028109010400d2207403a4000034040401c8031102048401c4000042c012403c02c465100b85d00100c0100b014405100f060403000c0c06584010220390802c4214038040342403815541c852400b42e07200110501c00c0d807510501c0c0303c614880507151841d034003185807801018030b4848164042c1505810201d140413101540204c2d0302c6071b0b4090030501c00e1541e680c400b000c82c200700300e0724007001925007200300d08030500c10090b90803c15041040c2e21012003001100b04000e601c041d20485a8640c040ba00040505081c01094000c5019080c001080c03500313414040e080020709902c610285e00018014000590f5a0b00700d94203a0700b00c1c040004046000100d90a420f1140e45c801c04105006407511546040e41600002d104820f006d00034881c0d40101556100e150007400 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 31258863 1250 31257613 31257619
    0x2180a06140d0e010b0d060501061205090606060306030f1c080a05190507030605040e0601050103060b0f0a05070f08120105040606030c12020307020111030906040303140103020303090f03070506120f01060806 91
    0x3440d501c03100190000c50b11885684000640d4504031703000150902d40c3c610b422154541c0300d4004002c8141c000d03031481001e01c8600003c1c041c80c42e002010980320f403c010803051160b58003002151241e141080800ba1154208044969207002c104150750103400b2083c0107000a00b80600080c03071362056015003800b0360794412000f400c01142182000c05004001c1861382056a242e00004a590300c80c00341d8118002000c1c0175000700d506100006040e00c0c0c140d00000c650304030030031500b000346080c1421542064024501113865420301d1501c41507100304240090004007010800c0001494088401d504072031084404115044d61048203a007501c284400c02d034086107222805051807078168004550004e103a200000d00c40044007250001030b0801d444503d03880e400b000c200010141c00d07102e443c49050000c000070085600d5540003c3e030720301c620005503002d1011072000d0450b90303c0812038007000d4500100495240d0811910400e41540300711014890340e504071000240da1400746040502404002e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 31260113 1250 31258863 31258867
    0x60d1104050a0209060f071407030f0803130602040b0a11010c0203040506090f040501032102011103041401060e13020915010509120703060c0f08251209050102180a0614 74
    0x1804000003094020001040340d6003c110410700381d80c40c07000070524166a04113894440303049081103114210070403505a815071007040140b0229400d92001104140e02076055503680d9541400e1081040c0f080740b0007001c950021501255200c05c113070190500d61550350354040800c09a0044074280ca0700b03038807401c025070420002400707281040030080218110140100040c41c8014010030200e0f04242d005031900782c0580022401c44217203070610100782e8000c2c402442440c00c0d845098032180b0016000405444507c107900300d1104003034000c000180700c0515250340c6c03807414400b400408500104c040340324a26000004000d003a0841c45280031b9030040c0c4d40c440c1002035072020711140100d6070401c000036208000b00040050000d01581c800800c180d5101d081d02440d19001610107980940a0360070304c0d1200c03044100038008982d120000882c64503112004101d11904c0a00608044101400340e5000003200d510490502c91490448581990100fa1156942c0301c00c941d1030040e648546040401 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 31261363 1250 31260113 31260143
    0x51314070c060905060727060210050405010e0604030e100302031302040b0105040b0a0504180b030a0b071b0605100501050a0203070813090510030611070f021e0303030f0906060d 78
    0x12403102004102d1040c00c00245022041d00c80c9071414200f04c81080c0007400482d0000001d01891080c01d0804541380192000503081010203520798030124841d961040d0b0340c0e000201400f40035000801c40038041020b0f120b0340c0c1028100109800054034000340942810320039400902d110384201ca2003400e0076081a50120f04560801019054040147d41042001d201c081104801400202400400c0ba114285e17250302d803000d05036000d000e0303640c1998000d103071486180c81a180461081c01407a031140141c151039552440640c0c070000d00d02c00800c0e10320300c1d40b806941040813036031149005690340000c00c030b02c0960752001140d0741d1107000c05240c0180c0040c0180c600158810012301110312040360003245036a280c1202c9011510121200140307101c03040c0041080c04030070300c02c9014907400750340d00924200b07450f21040c11014221000a0141c130100342d21415161640c040990710b85d81c0201500c2e42c078200004442c00e20442a100410389003e00004104c0e03920348122000d0b00d080c1e02c00e44090651f14 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 31262613 1250 31261363 31261367
    0x6021b18060a08030406020703020a120203060403030e070f0611061f06180504090602090906010203030714130e070903110906100809011d030703020712050a021e040603060605131407 80
    0x14001e02119040084101e002c039038010188050000b80000380e0041a926241d4010840c62510b9076028084406a01d40c0c00b001580700803425550068041c28049181900881254681400f952104c0d480c0400018080b800c070380c1c016030f00540b000b0b40c0360841c1c0345a00c80c1d04080c42d002400c020300d122005d035001e000308503560203418072200b088060380f0000c4440f1740d205c0100d800d952141408551092303000800040518002040d00e400c00c000b80700450542c9404403024145694806070005000700110b18807400c4010032542c0405401c0d42000e0182e2818000d0b0058400980d5010450302d03403241260b20380c2d08d0300303180e0140da2140c0e80041103040005295441034400c480c0103081e91000307540700d03295441e50b030120904402c0c0b81018500103580d100b034641402410a00d0340d0300b0501c8024084070103400803400004600302111f40454500410035040c469119102c0c40041040782c000e07040c0400001880f07031641c0700d007044800640f2a41e8400030303070300c2d842011900303110f010a000301c500307001081c01c5038 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 31263863 1250 31262613 31262659
    0x20d08040312060b07050607021506010e13110318010506150c01150620030f0a0e190320030105040c0603110706020301030813061e120615030606021b 66
    0x80d01030300b48940256555142030099400c10f4010014007400010b8260400c00d0030041c00e40d2080c9a480500340b1034014501c008030a160203822035042060790818910544d55101c900250800820020810704c11100a40d11058104488800384900800345032460030006005062050800a107504801030b0191200303e4030750001003200038950340c1c031880c2c585012907460010010702a0740c1c076000c4044038505040d115040345020140e450303400c28800d506100c0c1c1c43c1001d0ba81d4a07581420031f04204840f840220b1103103400103044100c9140d28010000c28050b102c100482c480c03800e03502002d0703440b200310145400d0702c9040d00d009106030303980c1c4001c21565110b58000c815004c01d02c20f9143c0760940740e0310f42d02c080e42c100307803c02c0c1d80b40d00780040c40252140352210900c0081c907aa0401003a1422010701000549007502e00701010300c106d01c1d0040b03116880e580c0c4120080c00c048414201d01d0b522500000303008090b03034080e01016200d80d4030304a480000e07840700300d594404010f1031190748034020304441d5126 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 31265113 1250 31263863 31263871
    0x10809030a1404031a04021207050a05060d021c06060801050604031a060303090301110408010c0804150209060d090501090c0e060d0f0204020c0601120515040308010902070f020301050c0403150c020d08 88
    0x907403403d00c804000079106a11101010311440c6036100039050900401940045071041d04105512440b0200103903111402d0910840c0c50844005403130b00e1501110700068814045042c003e840d000501e412070381a194000015107070031f0754a10450742c0c1c0701c0092040e584282e0001a00707509864228181c44207004414a80c04174024003038034202842d8401107400d5810070f649404c00101c000c034091041c407400348503448403113002e441c0401c80307401c00f905d54a80e40b04519a1010b40705400048208150f101d54048036520031005404001d400c00c0c608016000b0f20340608200c1e1040c024000000d1918040b4090318024000105401d4042180d03075103646a24600c3c00c0f040780c000c0e03002d01a035210050140f141c0d40c000c15000d00200e041c10454036000f0300b84144009801a0a94205c00b44804a94090902810b4801407000184d6944a41c104034240c04142c400c001d50641c201004c0082500032200070b4411244259840000c517074808400c02d0a440c08041da00d00103034480300380601124402e4460a401c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 31266363 1250 31265113 31265147
    0x2060c1204090212161704140a06050a0f060b0a0f02070902030f0105010f1403040b090a241808030f040201050c010203070201020306100809060105010f02010609051006030b010809030a 81
    0x40c41410469889450300030758054604141d01161510a004240402c590310071600d00901c07034a1105c40300003a24007070409403007110700460240000c0400c04e9000c500783c00510b030002100c0d00c5c0713800e03480d210b00a008101e4a8583c1c031400c0c1a40c41c0a04079540c05440c0640790500ca00310b0030800d11340f800b1180411001c21003011445400000103041005200550061017500010010b81d070505001411039051700c200c00080019500c003034040858601c090f80d4100f030b401000300e609070700c4585c2c1035458004c0d910800746c1184a0042e42c00e00c2612041d08800d60240711403018480720121003010158181d00040c090050b600800020f20307900800d4600da54054814108141070451900307082d803c90f002181c0820150790700001348801c40c54440c02c1c44044151310b2901000d645030106100ea1101c0061142c1c905001c405411551801d000b034211201130481440100094609005000b0010794140715180100b031130b01c91501260351103121441e2040240400840c074103402050102d032180304038be00c07241d0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 31267613 1250 31266363 31266373
    0x706081905010308120105060a0e06090402040b0a09080c030c090a02031f0303230304020f040f110a020a020a0906030c06080405150702010504060509070807030b090109121205150d02060c 82
    0x2064000d80d01c6803a001c0c50060010070744480c00102d059aa000703043c3c0000d03109540501c02c1c085d10b0790f4441c008600c03508007030ba041c81d103454003440410064042c94100070000c0c00e000c503100300355503031011010b8100e94825041320056580741062640b5050309d1801c558002542000281c21034205400031070300501070785241d00710041d000765a1401c8800907013049000440034140400706e040c0124000c021040c5520002c5e15604190b030004400803001450f6500880c4c550b04012201c143e81d9111010030003820107025911280d54000944480018002300c0c840c03c01180007044401c0c2911450702030f664041d0304691f00c50308022041d2440107000700111040d1203010131810f040241c0c607803071a0041d920b40d0000303d094105450180c05482008024008540c40f004040000c010000f031150202d83e00300c1405141c035165200203e001d4401c1000142203640c40d00c400102d0503501c00110000010000404c2140d501c4125025404903030622000c1c0d80144050030560140c03070200010702160410504941d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 31268863 1250 31267613 31267651
    0x203010612320708010f050f040b01090902041203080a05070219050c031509060610022d01050903071202010213030201050918100501031109060f250f020a06020a05070608 75
    0x4450840c00c40d00501d080b0300c1070042c00003060300301d80844c0c050489104c000303003442e003090f020511480c00c0000440c800d80d11002e1404084e40500c5c8000c0280c800780b07030195561512801c0d001c040d00341130349003280000c10000005141c1c6240c1d108080c007850a83e400742c00e00c041d210106040310317501c442041d01c190203021000c1580380c0e410008503406030001c40084025190440142d8100000106142e01544616026040c0103501140c0160f40b42c00d00009181d00005d1b00615082112090311340d42110340c6484207010101ca4004050040d45218075110016100815001c074242d01680c201c511442c22010300600043d8021005483d980703e018100c5100358004081d5030400000a0b42e4407a4031f942070840030700183d40d050050150f101d0382040d0b07040c9020310140100e0300c01d100b41c000f0f100c0110030200345140c00c0000035684050a000311048000ca03002d03d41003036102c90500c103c0c03ca1281d6001940001c1003800800d044400315000000340121a181584c00d40d8000c6008100610081445d0222 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 31270113 1250 31268863 31268921
    0x4080409050708100b091302130b1611010c0b0106030506010c0506040303060311180c0306060f04080303010501120c4a030709020412111302040e190203010612 70
    0x10b229401e55070b5000014142410407009881c440e800c0400008010081e41e50b56846142d14002c064401d44001a038811280301c62441882c01d980148010090000750b15004007000e40d102c1140a000f4071000c0700c14000d00d00150761300c00010b040100b1703200300580108245e0303000c3c3e440a0341c0000181000c0303507440441e503111820818226801c9020070703034031081482406540c020300d50580209403014140b44030690810442100c0040225100b580c000000580a40b102d01c10b0780c610394414110203454684941c00c16840303400900580d0300103407400341c0860103500b660244891041041d00d4428001c00e09980a613256110190b120b00c44d0b01c0c1010b60b0810038400902195180704490309078104401158003010308040d5a0351000c14080d0041c8410700055143c072416040042d40201000b500c2c28581000c5034403641410080d0b00c40038808100020300d5801c02c0220380c0301d00414000d060f2203000e0020000120302081c00b411000540c069010f84826005500441604407440700386003118000b0111 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 31271363 1250 31270113 31270121
    0x5190b0a0b03091c030b01020307141005070519030c05040513150f061103030105100c060e12070212120901051602040c030207030206090a050c01030c0e0d060e12070b01030b04080409 80
    0x140c180b184c3c0404c2c0a11130000b02d120340d000805901d440c00303000d1204940300003540ea0141c6000608440b0a01d054404100c0c0c04100340002c03040c020030103101074503007a40301404a0300400980140380030b00030b2010715010702c43d119803035400c3c0158803280d01f058140f6040c1b0404000900c02c112207a41c0d01c050800c14a0354a01e450b100800d240140c4065030303820b141c3c0c010960014440204001d9000740018091582c42c00c131040d1109201c1c5c64440c82e00380380f07410010080c1005400041003401001d22040070700600c1c40060030890300a540c005046d200d210031180d503600104c001c05410910500524015601c604010310000703004211104000703503250005421516611a8840400d50006590007010340511110f54817403060f0300a03084400040d20303000d032101c880320310310ba04141d5201c082806890145e90103600504000d010008460418903295008100181c0003403601d2041d080100380207d40c10048581c0d1550000e000d40c0580d195a03502c5650003800360084480400c144000301d2207400340d03c2 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 31272613 1250 31271363 31271371
    0x20d060905011505040305030a051c05040302070302090c03090d050901050d0e0102090405090d0203041806030b100801060906050f0d0c051804060b010e030c0904031803050a050c0405190b0a0b03 85
    0x4001445501d00f0032040b00f40c80301240300070140f11052200b04045980402520103550690403d959240341c80850040344480001d840520140303000240024103078009410420303a1310941d11030245450b001000c0a144c00212848180c65101480c040c4ad00c80c0b069024203020b58041c1232090130321040b00ea00400740e40c030b00200c10703040360b5000c40c0360040c600d454011990401c072003c0c060040f442c40a00002c0d1248110b000d8980c4c62949205400135010b6590b000c440159001343d5419128200a2044207102800f842206465070800902013142d0302140b00d03160403140e0040403001c01e801424240040c24400600540380d0041d40c145c0081d00d41c89040d5039950402511592201c1880d041c6400401c41d100050b5060400540b110510590307280003450018042088902d12800c0d9900e2404940000e5860500544203d503003000004101d070019110002e18810425a140500103005110444500300c418201c1d2088480075031050801560040c20503003006481110101c0e00ca51107859550300c159 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 31273863 1250 31272613 31272629
    0x60e030c0a150c03020702060a03090c03060c0c050c01020309031506040219020a1a010b0d1505060c010b03100e03040b0c0f0616110a02010518010912030807090807030308150103020d06 81
    0x228030408250240e100c1c00344010310703130300707045041c80c0c00c2e60013040085c0070700c00f040010b15581d040303443c0c24480f14040d100000c40c0d0040c818808216005002003019280207001c0702c682c0b007001020201980040150389294401038008c01c520100c904031088200d101511051308140c2c200802c5555800450071101200280d0300102060300030380c5403407044c2c1d0302d030004200692101140140300f44034600040702d840600c865004a001c4000d40c02e0900c2c0303403019620095000500240308140a1819044528611003c03415031319241e182d241c40c41c2c2919030a0079101d000380c00400c014040c0b4143d60b0064141c1c514501c0459000303008081581d450a2030075034801d4152980a000100320f542d0004840420740c0c1002c01500c4c0d620460350010740113004403c4503a00910218a1103026644180c800740d0040041030801040c03854141409007800c1e100307403200000900074410101c0c00100010703401e01100c0c0c1c159a0402d89a940c0d044481c00da0329103449013810184c0820036240e142d225405190080e203818 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 31275113 1250 31273863 31273883
    0x9060501030c080601150504140f0907030b0f06070203060c07140a080d0f0e07060e0f0306010e06031903020604030503060103140403090828020603040303090c17061b07060e030c0a 79
    0x400f00480c60000140d1025007814400283e0044455014041ea001c035400c58a0000e400140c8200249140a24800c0c25403c8061441000394070f5078150401c144041c820f5412a0b5410404012700c20307203204001001e07405a0203500804c04202401b00100603140c001d5000ca541c1d940079803445803d00c0d0303000740162410701000c90f100b40c3d01c8034540300c0c2c503181c180045410401c070000701c40303203c0d01d4141500c00c400621001038050401c645400668883c20310008065030700c03641e160725503071001c4201503d406010341b082e10008903c0b00b900d1040c0c8200c140d090307002040303d81c0d942d40d0200c4150303100400030760406480f100807002d010304d00c0304554040d41c800c2e03c03500051030130704011518054491080e0220091000c4950007000c4e40e03075080090032078054a2680e96651142019000b44c00002c00003030008180d2030b00080c41c0104039500304c40035040a400c2e030b217141e102da4400085444280e0f0818120020401c119000a04141e0102c003003070303400302c0c1500e0400d09441d50700c6052040107101640e1940d96 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 31276363 1250 31275113 31275119
    0x40305070203100513020f011e0207180b0105040905040c03170705010e010c0527062206020106051f030605030d02010f0501120c030b07140d0204140406180b0409060501030c 76
    0x400e004203000200d00f844204400c0c507101c1d4000c0c2520103c544082d00030301d000d0002c41f040b64801d1091403e0b041c11604178052404004200a40c0c42c1c51510a5503410302d00c00c2d10552881d00c2900031b0a000c3d0348140c4d6150304240c104a80c51006110180048400c0110054004001030784030000700c141101081c01185c5440850502c0b50a5940c030700e08820045e490080c4c5008460b40000035100340040c0040381c10480060034070000a0742d41c540002070f03070081c00440c00b800c0010403985000d107041601c680c42ca50071a6504010303426200c45014a5500280302d52403000f0600e8495944c1c144e00342289004141d69a07603c01007401d0585000850740180d44515a58420300c0e518012540107115071682555107040305e44079401e0000003030000402500303040c0041005030340308200200081400160703150355140c0e022600802035105200b80d040c6071040c0d0b404c0525615047c8120001c45241142c0380300410300742e00041008140085c50654010380d644841c0e000b003140c0d0710565003e544a9941601c2d0f50742 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 31277613 1250 31276363 31276369
    0x20406030e0f0304090b030307020a030f051005010b0405010c0204090209041103160509040204020306120d020601060f030b010207050f1908060603070506180f18070905010807020f060103080702010e090403050702 93
    0x2448204080780c0e000c0c40146400001c000200c034100c440100000a80c48400e10029003140300e01030300654001d203224070100600003003003c80140c40388200220750041c5e0000781f002007594400d220f60380d01d45000344820025540a002147e10070740c8000c0000070390940d1a4005005032070180c03001c0e55071058006100041d42010040c9500d10210342c40305006061501d0002060b15034001c00007409142c020000c103980c1e0302c40d510240501c9940500b903520002544200964032902482050000360645445440d80f900a22420783d405106030b0241150505100c2409880312414450b01c2d001640c1c0c00a59040301c40c1c5c0078144014001c2c440103070525007007803010549440c02a80042d0300c20741c410092001d44622805002000000591b0000080050480042e01d4200c0c1503444096101d840400c1045099115207040141c500036290070701152034010049070344981c6804082000d90000006101151484020300500c501c145000d054065a8101150b20210191070480c045a00403c411045103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 31278863 1250 31277613 31277621
    0x230703020a060504030f140313030602070204140f0f100b0c1e0c0112050a020f0708070501050117030406080604060b0412060501050108041104020a1e09080606060708030c0307020703060603030302040603 89
    0x298500d0004d0800b81142c41e4080900341410008220b02e44400056910310003e0040c1c640b000e4407000d1014140307a803410110065402400c0480c40b841c43c01021043c21118004d0081c06120384c0c40e1141090f1340c0310302110601000c082c007140002d030301a03400083d40c0f0751078100a0858841e15005040034481801d850340260a25202ca6807803500318a100102e507076405890300707401e000c6180020640d070b221041040000e124120b40340b0030700b41000400310244031241000f012a684074500800c441c2e0f0740d440703001300c54442402c2c6180e050b410402c801c028a80c424840c00380c100c500181300207080380c1e03124000a40350303119511006d0950000712152091201922440740103100a0a10003403504d86580c0e81e07008992881d00d680d10580e4045a050020340c4640600c000704541403820f880943d20181002d030580b15584506c1e00a4480c400005802d801d2180586540f168010f030b2072420340e114698500c2082d00000c1131202148901c003000004541c19000381d40040d400b81e107005944d941000c0e0010152 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 31280113 1250 31278863 31278869
    0x9040f0507020a080711090114030d0207080309041a090a050103050f0c03030f070f0204060e090c0301021207080c07080706020a080109090302060103021c02191509080a02010c230703020a 82
    0x52440c10003003140694000c281104680d03030041445035101d07441d262068030b015090020b0b6401c50001d10005c079407141d40001d0581084000c504075081400744e24004ca03501c3c07106000360705450b0800e1118034400e003816044803074200f1f055401e9000e8085403001107000b902040390495402c030b88800040092240c14012100b807021018060204810a00c001c03a03a04e20500f46454030780303800000e484c1c0034415440f547c0c0510660040003400559a141c444041d5080e0503108881107009490310340c14140343c140b08560390b450b9004490354656070b4594040e00e400000414a0b08440400c004404c0064841001051a1072142d0302c010f88074241480006e10001058011074100361070300380a40e002c03e800250351070440307904031050491b1054030664442001c0c0010380c02034100c0800007160304448100c0c009607043d9510b00098105014261004440010030380c484e012043c1c01c1002c0500244d4407590403000024080c2105000c0c0310218407540e00c0c4e451b4131a50240c0702c0e40000b0024011454801140310007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 31281363 1250 31280113 31280141
    0x2060d02070c05150301030b071b050d030510180504021c030f030b0d0305070b060310060f092706181218080d0909020304020d02030610090501051f1206080607050904 73
    0x105400a4070407101c4ca01c0306000c080c000c960140001111284039000500c40c480051107801c45100041c0341c001d84c3c170f01c140f01c8000086410000040d201c5515460388204031401e811608018181e0800c038100200310142042e60484045004a5440c081500000c1c420600c40c0c0c2d1018a44404814020116040c0b02c101c0c91091030145c0c11800883d41c40070645016580001d0250256220b03030f00001c2c44d0510082520351107a00381303540015400d2100e1100f80c03c0300c1c00651f060050540c07070b03020001e00241950003000c030030503030481702030120702d09034442028041d03c060900b0030b080907519415010040804080d0001d072009a190560311840a02c500060620344000d14901c95400e0b40036010394414000c04035420b034017100140540d581d02d08002019900a02652040d0400648440404032507002d1000300e50b08080000405080c12152031130300540ac1a40907001d0b004060301119034184000c82c02803401d8940314007084400c400e2041c20300803036107900c2d055980c0d229681803106440c8c0b2100c030b02003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 31282613 1250 31281363 31281379
    0x1090c080f0402040c031b0201020414030c1f05040306060308070201120507050a0c0302031b01051b0c0309010509040209090106091401020105041a07090905090d0306051f030b04020702060d02070c05 87
    0x703210000480d101e41c005a04550100d006020b82c0811402421035180d64054049002c0005408035010350081065901003420012005070007014540c1d103a2101c5185500003407004504400c0301010510644d00c80c08a1078010715041d0380c1c0d2222002c1c2c0c1c016401c1070341e62500020740e903c215a000b404164442418440034007070b9203884c49014025000e080240c105011400c100380301014400d200310390500908003840c0480c0c403c50030056008280c200c1310200c912458085a080d01400300098034040d04a5000039441d11481c2001111140c00c0300c2182c94205400b40b04642d141c0d914990303264048e0441d580c071024035619103009600f0300400d000c145410342e4585024403020805040050400c0c00120400440170f07100c1943c00c54844120341c0c461190b15180c0301c140311810401040311403200c0310580c3c00307002c42074507801044100416020342c003440c2c0b000d018001c0f00a0740280c00003d00c10900400c01824400c80b40c0106095601803003101d0000c56001840303c081040080c550009000c060714050 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 31283863 1250 31282613 31282621
    0x13060e090103060203061201090602030603120c030f0a030b040f0c02010510031703070c020a030605070f030606051210080708030409061703120603010207020a1d010605090f01140403020907050301090c08 89
    0x180100340600028008940003c0020000d8441d00e480c000c0c8040c01400800441d400b904100000f500f0a0396038a200b400341c0c03034017018550300790800d80d440410048050b5190010303e80e031012882d030158500d2428903171100709501059860740324180513901a580c0105551031014002421158000c2510545040c1d900c802d001042082052948051030340003160307601d0321070b000300381d82e90249210020742c446040c440c040b080251942040c0c0c044e850341d0701c031015000d0603490705900782d880c00e00440001030400d1004d049100c403442145a040300b00320300c50071205030300c0d0b100ca07500305021a0000212944002030800488620740b0803003000303016450300c84150346803c00182e07850317129520210b0106000c06004c5455550207504944c0300660050401d14032543d544890301071540c2a480c0c800910110340000503240b4019401c03151941001081c0c0200910300000550f00380804520340c4d05903007000d00003c40140c491303161890113444240c035a03d49942c5052252815104407179101010820400240 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 31285113 1250 31283863 31283869
    0xe01090f0b0304020301090605090d030501050d0305090913061a0a050316050d08090904030906030b01020706020d1809020d15090204050109050f1906030209030717060105040507170403030213060e 86
    0x3000d552030840082c0d41d940b540d000003405800e01460243c06589054180041054001203070340010f00309031418040341c1e036520104105203402d40e00150215000b0803104003103141c0210038917440703110310f0340481c00c000c4513881d010b040f5948400100310289480e050b000144c546004100001c00c012402086141c3d11420030042c1c070f4041d0700c40c9600072a4425088010050381c17005690344400c028010100da0b1605003401082e04031144076200109140c24209480d95201003010070a603170190300100504500500116a24900d00301c000c03582d0300d109000410140d141c1e000030310914041400c041000c140b0b1096403040c80b042750303000403106441084100540d03600901c05100301c88003160010500304c10b441c003081d0000b403070b8000051441c0310880081600d03501640036204000080e800c4a0840e40c941041025045d40811007608a40c0300030010030907850207400c1140e02c02254a800b41c61610180d13424051030005841c11804072b50046000c00400d01c8403100e80008107102e15102000704c044a005c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 31286363 1250 31285113 31285139
    0xd1509060e01230a03080c0106031208090703020909010e0316050706050c070504020307030612050a0b090313030605060d05060405060a1116120203040503030d0518030c15040309051002030304030e0109 88
    0x200c0c641400303040e0080003642c0d04102800115004244d1980c0c030719241f07408900800e0310740004c480c900b00c40507800d1002445050b249100d04112001041a02e0031502044000314005290859a40d2035014420340305d07409201500c881100e02d06104c00d4042d561828504001158200004004052140321103031007002231a41d080710400da81c0140d03a40c50b0a03004a0141c00103400c1440031510902c1c2980c100880010001c4402d0b00402d1a03641a03140c0c1150f1940300c2c4500100d180c44550500d509101003140fa6010302c0d00840c0c01484406207507030582d50f40781410400c5500b9900b0f504160100003240e5401d024080503101d11080b0306140440e82c2401081d25111a48041c2800c8000b50202c0c1489008000315800f412004003125100c41d40241047c0141c4411100d4891045121192503820a0000242d500b940ba001c4085c1c500110845000c031034425008105508000302d05c1c4001a141d00ea10741c40da000d545055025568924080c10042d261603c480801c40c10000c00c000304108510300b4000c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 31287613 1250 31286363 31286399
    0x10602010e070911070209010b0c06150d0b060d020406030503040e070c0f0b0a111801030f050601081306020f0703031b0e010503070309060e0318090c0403080f0702060d1509060e01 79
    0x1c0d000130f041d4a050310504141c05240341c003d4000d6034000c00860024101c00c080c0100b10750003c01c4800942d03408400841c8842e000071032581040345404860001010010142d501c4003000e428010300d000ca0f070700042c080c0e922690080e00c242d000000c003030220500041c1801e51180d0242842080105a681da00590105074040603152010000109025801e07503006100340a907081032050310788800507402071083c00d00c2d07a07030940864507140222813544110300525104140503122110503036030701003a0807102c40080004940d0315070b080090b10703102e40c040d10180454900a50300000c28408158070840101c01c51101041841410360506600e607030711100300e90b400846403402181101d00740c50600064600400a03064500003c1850403ca10000003040c134442c008890343c8199450b0a01d82030803500c5980000741c030f40d140402c0103040e20208800242241440a49071514050f50040340804480b075805020854600c04030082044080a0003101d01401e1020007002e403075403505100c0317101110202 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 31288863 1250 31287613 31287629
    0x50706030e19060e0d020601080d11060106050a120204060c02040e06060a0311030703020a080d090b1303020103021b0a0c090506030c060d1503020d060507030c0e0d03080c1606060509010602010e07 86
    0x1040d91040100a410080c1e003120700100300c4412185d01d0030003a407a0300b8240142001c1d8400d41d99201c0c821449020740c48414140400548041d07420a6400c0320581d0200250405000840600c002c0d0542d0920042c0000d11240e074640340015040d104002c141c5599541c10101036200a00740041c564600c4010400ca03640444001a20301415001c00c0c01c00d50b0325403011b5403000d115200000c005001003150030107811a030b51883e00c500e4032404c4c528100d005100303003120701e5000340800b813005501039030080c121408141c02e1202c84195a120480c50410544811158008001c0c000c010260141c080e0a0300039004902602030202e10001103192400340310891100380383c4809a000080300d502070101d0186030086c0c040d02e00111030f030402c0e00240200341c81d003200280c07a00c520080c0480c4101100c101e00c0c003005003a5034608426440407160b0324006008070402c1c89040040c0300c070000802d0380020b03c8601c2404086403080c9044100000001e05900040c1564140015416040d00204100ac140c41c3c07d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 31290113 1250 31288863 31288903
    0x30b0d0327050301060f031101050c0a1401020f0a1d010e0d0204050c041502030307020c030a0206070b04030e040c020a0606090501060c0b07090305030307090302100c05061909080403030507050706030e 88
    0x20307103100001c0d00607a0100e601035181c0301000c00c0070528480402c0031350b40a0010191a0f2981c800112101e04c115141404541c1182d01580002545621107441810881001604005199000d04900d5009024990100c2d0f50714259440c080e200001038001ca86003400d101c4620900480420120001048000e2089a64000240300641400142d401034000d003400c410566a04900180d83d030760080e2a1200944211803004103a460000340f82c80c0f1040c0d010303262908094096940f2500f01030042c004070140026800c0361401034580388112000d0302d001d94018030320718150b410305804441103504000b8a05091a0041c842540c100404a060740e9106100e418680d682d040d04850701e0106810007072603404008144004076500c80b0715142a00d00071500248000041d00302900c1c1201c04810003481c43e0024400a00d40c0103068004400c04803404101251040081e070700c0409079801900200c0c0030410100312230050201c10840c010261200e0f040801801e08980b03c003c6d80d81e400c0039074000182d414 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 31291363 1250 31290113 31290167
    0xe01090c0318050106051e0102030f03150306070210140105030712021c06020909010902070b0612010608030d05040b01080609030906070c0b1204030e03120d090302030f0f0406030b0d03 81
    0x30a6200050402c072420011001a4083c600503011301810301c02c00d4840e10584d208071000250304050b0f000078100580085117010f07413190741d0394566040240040110020100c2210680c4c6091101d5846005207901621404181440210465040100c0380b012a2041001403225440005400d0103845008862604c110003510000700c00d00b04c000c070003403d6403841ca280c00701000311540150030717a100220350112050fa01c402d40d00c022405543d00291030b41002a012032101d04004418964541e8410000301d030349c0d80c40780c08003440c5504c56100e400322582d40d0070410040c4080001c6103800b40c20110044c1220b410006002c40e5039000340c034000343c490240000d004003000840001e4100504003106696140c1c030a03c4003585221104032030a0f004a8815840001ca034030b400320304040c1c1e10176001c0c1402e042c40c001158541c01809040b00803401d5110801440e01540c0c1800040c14802c220b003094281c0e00c074101175004050350b082840403400ba485244140d0002078104548500291120500800c1040c07 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 31292613 1250 31291363 31291367
    0xc14030c030406030902040c050f1219020a02060a060e010315020d0209041e110a090e06040b0d140f060408180a030c0b0903160b0406080c210f060a0e01090c 69
    0x4a0100d65505600c40000d00040e0f0031342541011244500883d400c1104081100d025501445900109031aa0104114000c401c2c164403044c40d402498a042c03418441c000c0c4a12507003284e00914850000d42e000204004a58649018101c00f8000355952002c0f1075146d030b03969140c11070803c002d540c02250003084a02d101a83d80c0c4c10340c0c9c81c5a0300108148910303000c0d05d1200c40c070f002490b40072202441c00c1680c0e46003c04907410841e10726200540e500c60031a45403d000028101e405040030707500684610f10142c29517522030142c2c0c903941c01041c60f580d400700340084480c5041d60b8180c01a000307401150400000c500e00308107070f500c240941c1010202c2c402220000171206012074000800c003c510a6000c00c1002100c0040c00e4541400e4040f13401e0741c0782e14804251049564442c490b0740c403004100034040948a521595080410380d08103604007090480304800c800030a0320081c4100044108001c0502422000d06821032015541d0300401802d007040203100c0b40741405940f0100e40c03950410201c1c1c074 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 31293863 1250 31292613 31292617
    0x603070c060501030b061002060705090f0609131401080a020d060c0e19060314010503030406030b01090b0d29031b0109080313240c0b13080c0105071409010c1403 71
    0xa070300c4402041690303100d15010740700c0b0340c017030b6800e90152001c854208074281c000038105000e01c520341c850a007062005800c105240088090b00d0780c000205220552041d11005644040c445800d40c01140d0345406104001207010143c4c01014141c0c45203031000c025880702c510706d44200b50005c00104200a02c0035058644880704031000303800c0400040c8ad01001c501c055621400d8580e90380e405d004205644100f120701c00020300840741d1541081100b08005070103540300c0d03411603806061058411ba41d91401c41d284d500007850350714401e0303242e6515005d090041c0200000340b841c000b001c1d001100940c00441e030b0b1200441e5034598140401183c6400c6603001d00840e0300100b080c001140d03034440381d545040d40002101d11481920350000c0ca0b8804a034403000c0e08801d42102180d41e00c60641101b5116907a042e032000c1d111290215a00210801107640840146035a44490001054a0070b08000003000d406000310300c1918000144420700c002c0e82d00040aa9100343c0101c2c41070315490b0840e500c80e0540c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 31294969 1106 31293863 31293887
    0x20c030c030a02130c140c1f0504030804020d030207080307030903021005090d0809010309083001080a030e030118050a03020705060f0405061305040510140604050609060307 76
    0xc04c013591008240e0f1380e161030700540c25003e2001c40104e40d400307444c204190350440ca203003d026400d40e030407032010841450001c0040e458030740c500901703442020304000c0c480d01c4568103d0b814540b0800c504030203403825005984e9140c04038603000d03144080b680b10481c0656013201010300e07014020001e07160f00e210080c0150740728103001e580f06180317540201c000764181652001010003090b0380d440600708007408403a02d0020500000e411400206038810704003500c070142c0006112703000e004100c652400d40d2504040d080903464000081c02340100c90100c03500c1204001500b02444800110795903581d0003902601c0b01d154440c0c00f48030a51241a4108004840811081000d810305200401d0f1580c110008016820344400008007036600645260451784002d10003401101c001000c8266030b4101266554076080c50040401c1d107900030b0403030340c500c1a0808030002e1466070050b002c0e4511 = true := by decide +kernel

theorem cover : BRFrame.Cov 31115113 31294969 := by
  have h0 := BRFrame.cov_init 31115113
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 31115113 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 31115113 ≤ n) (h2 : n < 31294969) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
