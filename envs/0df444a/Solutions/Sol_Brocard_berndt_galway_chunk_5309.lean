-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5309
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:26:30.85821+00:00
-- url     : https://prove2.me/submissions/fe66afd8-00b8-4104-95fc-42e8cfe7a669

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 954676258 ≤ n < 954856115 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 954677508 1250 954676258 954676297
    0x90609010c020f041b1e090e070909051e0903070807120507020a090207021f660b0601080c070c0e0a1413080c03040b031609121502 58
    0x14111403400404919205e09259820203585d041500003150b5440f0900c0d80ca0700d0740000741d00402c1401e01c0d0141003030110164002c00c0c81548648082c0f4027604034518104940d0611036020b00400f8000a0344261181c02d0f000059040c0784040306840680d54010f00f401d04284490351480c804102c500d0110081102c1440f810380541c0c0c5400292005144442d401a036481503030040c440300805040b00a00d1418105a900300c80603802490100001049898401c08039a0070b8000130398000c520701c03081c1c10042c103020f44007044c9014007011410f0340c440c26040716032400848911031091000c11b0000d001c200f400c0300041c119501484505500942c819a141d103050082d64481d41740c0001c0b80c201c00d400c2c000c0ad108000000025124800802c0705602c1d49204a103003880f4244100e01450200900030500030070f00d13039030a00041003a00c01800d2590074440c1c403403038030180e0364142c90a04407400000400300f11340064804d5105641015150300310540a03a02001c0b4249040690300410050800c0400300c2c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 954678758 1250 954677508 954677539
    0x1401020f0102040608010f050607020f060c2b201207060e01050f070e06040e01030813080703050c150306090a110405040903051b0105061c0204090f1a0c090609010c02 73
    0x10061014003c50380345d0f8182ca504003482c44840c0c5d00f080c4c11450140900700a1b10026a0345d03900040e00c107540494406540e080c0300e511040c05c220b2181e00c2142071424031003885c0c5108012128140f424921540c4540c3c15140d28000d200d902d411021054106da08503401528502c1c01d00341c01007010901a00c804921030110f5101c16003101d40896941d4205000402031140c0d0a9014044403400b0300d0445010303003402e04000c0300101e010418071001b05003140000b004413010380c00c402480028003c1d1825644410307075a040c11612030b440301c41c1051041c2030b01c01e0162802001c000c05c4d24080c91001d007a6030318541e600380c590001070060003400d07406104140400034281c0e60784e015458142d0321a9840a0300d55050720420081e0f5030044031054010b03410001013044c40d0b110003002485010480041185017800d90002ca070085c112284081c110049500702c50061140b01c05c1e1116000a1180e006c0c20941e903600002d1b0998040d030148507a10090400800c01158404d9038841103481c0000c151100648a40 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 954680008 1250 954678758 954678761
    0x9080f0406030b0102011b020d0516020405130b06100f050901020111040603060305010f051519030f0605040b06030703050601060315051201090201021c0801050603190e03091c0b011401020f01 84
    0x740d1000c00081e03142c940034205540c4c28041c00c03003000d1040002d80030034100c9107006500c0c0c00d002e03400c00080280c0490701203145126400308031042500640f0804c8141051603502c0c2942e00416000d640780700d00b1601150075410580c0c80400b0f0580ca030364480320454400c00b42101c080d8840b00049045648503c02007072411410700c020402040c0544001610300d1940c5005030035243d1204102038018681010030078005007031001c041040000b10303800c0300005042081d000f100c442c1500080c049400a01d458010080301e0b030300203402240504958805995404101039591919000080407034001d88010080c490083d00803100420503d03500d10341c4240c60303502142c40b00c4034000a00c10f040e91144188029541c0520034064040c0e44004040ca00068400c0054a10803040c8641801400002b0016a0324214094592400c1614030710600aa5100604c1182d5039000321655500c5554070300d491551030038181e812000308591000503115560f1a000340d11907041e440007082410341c00ba00d01d024900c0d110a = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 954681258 1250 954680008 954680017
    0x60a0302090111014205280e01141207260115030b0c1303020f060c010f09020a06020d0c06050907120318120f0f050709020409020c0f01050c070609080f 67
    0x440301002e400c07144d0400d01e0640841c0001c0d0140f14175040d00d4142003a0404d10381c032006482d41503074000503011400185106d80903040030f04ca103065120080208035030480450740c0741210a440c2c03000c01d882111074200030b452603680308020f0781680503032820064490002c10080101041040030013140d0040a1810700752510f4020103030602c0181c2c5030520800044482554001d0384440300981080003420220345681c42c00e0002a01c00c007074917085132450b1f9441c1e42c01c40d410310360900c000340951645040100050640900201e103e500d0102020070200d10000309015044020750352102c410b0340a0300c50074014803024010b030321103000300034004c00c1702c031084103102d00281d01c02d584000800c40c0c03003421180110b17043e403c000c2c099507560b0743c201c01040c2a85914200030303800c45003203e524255443d0680c0b0b002010782c00106803a001050018460b0f01660181860a0381101a0381e8a5101c0e42d455608881c0300710340f4042c440d081440b68002051290b4013050041c1d200c0c4036200d01e0242003260420301c50b0403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 954682508 1250 954681258 954681281
    0xb04090219020a0b01030b060607080406030b0301110c100e0a05010e0f010609050f0718051005130b03040206040e180111030601180501051b100e0309150405060a030209011101 77
    0xc0000d40c1c401000c000300e914088103500c5101814a125095642224840041c030014181d20000d9012410310b0b40d0340b10841d200194046c1c007099840b581c0707020140c0600004040343c2d1107540f03032a0107680800000002c9600180d040000340000c280180d5410340240746440445026215031f550340d03070014000b4454628901d12450080003d0351a0b00b000c02c0c290b0342e841d040030b0400790802c400e0289c6080703404d40781a040344075400c01400000000813030f00350a40303840e03205aa100c014040c69541103900140100200c10010310036440703082c1c03940a070b0511403105030343c029006001040100008103070149a16040340034919001c84604600c400319094440e81c02000085246c0002841510343e0407072012014400c03a01e50708110a454600042c1c214024401c168906405d800c1c1c280c18210340600403032900c20b00b40181000001558503440d5941d401019401340a0710700c0060031409034400f1000e903000c68070018131040c90207240050031000ba402c060180350510003e05002d070f034600d20071b0080649550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 954683758 1250 954682508 954682511
    0x141b091903021503181b0907020114190e0312010603090218010617220206031305120c0c0303041a090a030b0f090607051305040513080c0610050103020a05070b0601090b0409 76
    0x1026066403c981c46001724680a0fa40141516030780300103806071102c40303204101e40c807850313a586a000a034051720f01134040703d0305400700c1c1d002c014180905118205c1c2c1003000e00001c002000300c003a00300c4ea1343d11948501c501c54000350b200400c00d05229800c10000284050280032000c4041e11004c1c0400340c1c01c0c3c0044011845420b51084890181501c10380e00600464040d11400900c010381a51000c1003800a4015031002001402060303a41c2c19520380d01d9031040440b040341030005000001c1d0307040076040003454055643c604001d441c000090740c00352580c5840220301e50785040d078000c01c1a48240b4501e40c200c10303080000004200c00404581c03203403210490b18495454400c110740e0030b029004081d4000d2003000e0009032840000c401d140c00c00d450b815070300012a80c45050b03114205c805030840c0213100d0040011480c43d07524004c03c01c98028100310709074a66044d1941d0054059009040030400000e509002400110360402501030f00700b4018144642d41544884c018000c40d449508a84800c6 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 954685008 1250 954683758 954683761
    0x2040b0324010f1d040b031207020a0f0e190f0e03190302181327050111031e130507091e05090a171c141b091903021503 53
    0xc40c0009507000180e0002d1814006a1030321600c040c0101032042c1c1c40c030003111820103810746107488903400507450800041c2102d15061001404000130307803201c3c90890244034200ca0006803400c0c01084003040d6812240c00054995844001440c3e4041c09011150096150501d0010446c5103218101302980e03500041c43e41c6e840000b0980903049800c10030b82e07081510400900e840118000c0b10103101400c111050b12150f81c959a18201802d0600c022079240010200340c11703034940c85003515400d064400c2d402807216a11031111095540011a0883c03800c1003a246e070b100c90500c04400780d6501c04240f03481c0c00040d42140c1c5842e071415285c0c1e04400111030340c88007024903c0308803403242511443c400d01e0502181c6000444030792682e410703140013001e090782008010341000310007003600c0074140b101c142000c024080301e80d0200a00112601100181c800b9004103034103c4040c044484031480c1c00e001d1902d071102a00c14860001a030000c14501c101e000e0324040016590700310b98130b5595116102d00b6450b0b = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 954686258 1250 954685008 954685051
    0xf040c0e010f0509090c03030f0c0f06070903020901080601060807030c3b270c160507050109080a0308010e090c03030c03090132030c07060903021f0606091802040b03 73
    0x145200901407042c00c1d0b1201c00d1240c03850b1750010880c0c0b03010030041607103a19200c00c807072210310340f242180c904a0507003310380c2080f0450340d01100d500c045900880311401280d90f58604140c80320828080c0c50b0008a041c40001c50882c080c0e04240782400c500c0c81c00e40051500c6810719040452103400940301225034003000c1c6038502c0c2016255801e440c046030415100103600700880042800746a50010880d401c0c0c00040103103010b4000e658911500846960030000245401900c1e00d515019050120f0780325007002c10341c2800041d100041543c90340701d200341642440d00c20210144000c1c091a038078030400d9144204c40d10203001900450f801c402c015a102c1d001c13400003512025907185802c450111990f023884184440034200c02000c001050f046a5039110580f001841c0c3c0f141d0702c800f038403003800c1070000e1040507400150081c0012034512a81c240040c011380030802d641c40c0c0e1003107400180c0c84810511007809940d02d4000f0b420b08000b40140b42c1541e480c0654110b800480d015004440b480740141c10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 954687508 1250 954686258 954686269
    0xb0406260906060f1512090705030604030c05190f260c01060906050f0a0b0315060c0c0102070506210a0905010914063402101e0e0a0b0f040c0e010f05 66
    0x44800c421289040c0d4150200e00a0799903015911041003c1054540807e903d860b060000201510001c1c00750307103440c509418094150303070740041c1c02c90320b9100e01c541c00c0401c00503e000c110384095202c0100030724a040c2e6280d284c030b040640600802c80440801d01e00d6444081d4100610200e101000085001841d0400380002c5803113540c00340303008443e255585007069032a4144074040d00c500c210003680769101d0b52a214a101903460710707160498000584900c4100c000200c21100c1c0009900701c3c2c20481e214410711140e400740c0300740110051040b100e07480c56004a6407520341c1c02038154100082e106071a8556601303480500710305440c0c02035600050f60407070b41e05100e815407244160211801034000186060500d42081915100e2442009022402c0a04c00c0c07041040d9008602d000f4040028026000881403500032040d0700307036518004c1d05011450011030a81091900100840b0761641ca062408100d403000a1003183e0803c207901d40810002742c0c2c00000b40c0030300107042051400c1d5081205100 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 954688758 1250 954687508 954687529
    0x1e010b030106080309130905030f18011d280909030801080f060703110c010c050408070f03110d03090e270303090703080c07081e0d090b040626090606 66
    0x1030107a41800401c1c031000400004031241c6420070749091b015040030080a4005060b8100d000740140000981c8600403044003000d0a0f83d030b10022416009007074500300545050350802442641d2081d01b14400c641c92900d08000f204852a680e2440300c0c03440048003d42801880e0781212694542d104035403024554400200c5015051680051007049071000c0e01a40d9600020009000c02d03456580301802070b000780060307d240b02d10290003441607104201d00500140c0250061100510400800140111206040e13104803a040b010f408082c005040a22070310503243c05082e810f2000038000007802604c0920384912682000000006840d011107181404044011a0b5a000e03401070080c4205d440c00401c280c1e084a9100400e95991404400b407982015280d5024082c54010051440900050304040100d4840360000b5102d040341814400d03070ba0310459010700440010700744824841e00f8082e05030034820780f120422000040c00e07259500040e18004440202d030b03680002c0305110041c00c0c00140d00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 954690008 1250 954688758 954688781
    0x3080906040804050d1a09061617010312050c030f0405090709030809040b0f0a03060506130c23040f1e080c0105091306030c0e04200d0609020a081e01 66
    0x100160300781519441c40a0089001e01403044000c1d0350ba01040188140004669503c98480010140f034000711181e19004100c0e4601501c0c16800f5180d5081840740c1c11804c1e05810a03020440c081c0d003162034000044104c1046001131000400000c01d900e08204082c00005501c10301d030f240ea072070404090180e601000ba0102c0140111854148005070001d02075030300040054030700141c002d02110000e01042d0344082d080c7c0e0000005100802803003201c0c0c10862007403a09881d030481507440100b04000300c644001d059000589840300c031101e0303903a00c402d8a014140b0460b240c6c41c10207480340360785208583c2c1c1da4018903038102084072004061440b101c100f00107000f848081c2c202d00480c0c80018000b485202140c9109400c040e84c0b038171010560303502c944081d503046445506499128010125084001c1d502550042d00010f020344500e0742d9401e07003100115014041a45800c071135991100500a448012644045040d0b0045500c4104109100b0500c07800412809a0b5025010b01801c40d0911000c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 954691258 1250 954690008 954690013
    0x5030105060a03020703031103090109020406050906030a240c0503010e0a1e110c030f0301081b150705100c180503030306240408030d050609090109050a06020a05090d0807030809 78
    0x4015039601c441c203a694103071075410f0259407220740b850100d00a00070003078500480000030051145141d015444210802d1095a0170001c0b0b90700c540c10045561002c03943c40f54568040c000020010310f003901c2c0c8003089045141000300c000c0204a1402c281c900c407002c030750001035000c001040300800320b02c940b03a0083c05c00c0004201201400b5580105240080200c0c2509a02c90380058500d4003a00111034080101401350703625201041c40f005040ea01c00c3c440c048181c4070f0101e1003191403040c0b080d154111130006044a0344074803085040401d44e040594156854022000c4019a0703821074001c111514580c0d944048500c0c4021901c80301700b10301d980080e4042ea2080c4104051510745181409031b01c050003060320710f41c0c0160f03080200c0c2c511541e001000e00b40004180c01c580c0345502c0d04401d000740c03801c551006040c0e0311180a2403c0303421500c0007614541c003400b01032010400c9540144010740b01031818a02d070244070808100990f0040404480918000407c1e4045c15030201c02c0c113070800000d101 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 954692508 1250 954691258 954691261
    0x901212f0d02012c1c26041214010c020f07092013051906231909050301061206050a0b061801020c0913061a1503090a0803010807150503 60
    0x8110044903034480f0100758180650030041500d80c612000340384d5004042107490b400303c946050074180050300444841e00c10051001c01d40b4150f0940040c0c84110328141410030b450941c1c0c02d41c401a1010065a00710010600a81446020701500318102103e800420307003407814085207171902d0169840f900c080c42c6854017440b0070480c02c0000084101c42201c00d03a440d6820307107007000194461ba038403c6a1050706c810740c078124802c140c000031003110166190203510304080446460040386401809128030000c01c80c120b0703101e2891081e0700e60107405103440000141c072032001c02d007124010b800900d0510b0480c00c8001c10485c5500035658822001c00091103980058804104140240021803400050007007860040b07910800249058400c003d001a90b9802c000e2044666001000c0c415078003c2d04005a40d60103504060901103204405461100c140300650300c81c403500e81002c2d00d20900750003840d1041c00462540c1000c0c40c080c2c480c03a000341014031b00c0c040c64078201e003440380600004d1103801d10 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 954693758 1250 954692508 954692513
    0x1b05060610022a0a0e0f0106110114060103020d0609050109090516060e2e050306130501052202040b0309160e0103030f2f030901110c0901212f0d 64
    0xe00301c03000c22004004000003d021080001c0c02c11340c558001c5584002d5100c1080f1440990000d03d5048413032540301ca03008070802420301401c0e592a511200c00c0b21488070041038140d403180c0e009040c4410341d10400074549442d00c4481d02601e800ba0f1010f8040c40d1a84a01000d000c814002d1802c1021882094148075203094006007003194224030951156408000c3c544800e0750080c8105003c1d2035500b0800c0303c0e802e90142c0508140c105480031401848501b200d9850150300c0d104140c141c8200400c03846401410040d075188056001010b201681c1d003e000016000d89050059070007041050050948100c1e91502040316014540c885100c03200d9100041000c0380d0030003004121003e10b4a8070345103501215400a6151022030051000c094904400041e4900e01102802110038241c2c0c404d450084105840d940c6c074850091002c0c1d1080c01c200040040134000010b002d51183c50392004d201c030b0b4543d03031544903a41d032420310f015000e034042c22000d039400510031450702d01e240c004480b10903500d0841d8 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 954695008 1250 954693758 954693793
    0x10f08090601290a1e3029010e030d12020a031b120501150e04020a260a0c09180b2428120207031b0506061002 49
    0x180b195080040a00040f80c0e60326401000f10480046886800c9695000d070300d200038140b000e603280150f0303d01091201da42a103031042d04201c00074000c2d03402d06207140795440a01d8082915401450400c136507108115681110141c2555564075128100000301d0801100050031802d8035665036440303500400ea0f40c400c608c1e00411b640200e0706110100688036008114290020803a600d05510a000580c00745c83c000c0b544001518201501c0120501207640c1e560788100e81d40c0d0082225502183c0f02d40c00806550030981e0181600301c1d46494590310741c1002e09002484075070940000600d01200204210360300c4200d02801b0403113005071038805145c42c64802038020000d0701039060082c0700d499020248441c0e0b40c40da1031710f80b0007449200340512030414a040640c035600020a400540141c07100c003d080302c0e46107140c0501140140c0720a1180d000601e400402984550421014840000d21292a542c005012110400d1140740205081d0425000304000310080c030300807804640c084c03c5100a1031416 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 954696258 1250 954695008 954695011
    0xc150126060c031003150902030f0c011704170c160605030c031911041214070503030a050c0f03032404060614090303070203100606080106020f0604140a02120606010f080906 76
    0xe40b2800b030303c0307403203160301000e81403000da00c05001d21160700c9140d12281c2e035980c0300442c4680f08030101c961100744904a01d4403600505241c6000c07400410b04102402e032290f1940e907100780b2030303001c80c11030003594180181541c0180e09180d0403907106e07001843c481507a14403070402401d21410101d0840c50300d00d04100c90751100410204008402340d00c0f1452204007a080b00c0c1a540103048507039184d03034682d0200000010b45000c142d40d060903100301c4c600000008951002a40d5006e40914070f407044690090f01c440d17011404820151090740740c1e500032280d060014501035028860b149484444a03401d01a0b840c1407065400c1c403651400100308915500084402e427010303003d4580c0c1da00c40d140035000038110302030300a0103505805180035039200403009910007019251142c80c0c0208590326144101c1e030341c070a0300c2c00792010344d4080030105001c94501881401420f07899000c42c0d0f070492595010641c1c05610501c01d10881e484081070003910341c2c112903000d2010f86d00d4a4600b40e1842c2c6a21900c4e0749640 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 954697508 1250 954696258 954696271
    0x1030b0906040b0705090d02220605040905030a0f05071a04061a0f0103180b0a0203180a050606011815090312030b134205010503071707050c15012606 66
    0x30001034520b1b0b50348407442410303c0180c00400d00b242c07000301d01d1684800c03901d040e94145411445d10074046600d151510441e00f00d80c3d00b00c8010740c01c0c801004410f4642e550390645990510606002d0800042c003107130780d01034015a10050b0000c181c1843d1a19005840050310300081201d0541410352907612018642c1c030031041309281c082040c201180d140d410700c0800100240080e000c0c5000c0241c2c040040d0021802403100414104004025000700303601c80c0e4214500404c1c0d6042600410100c2d80f00d51016111500412481c446065035840d0850842240c2100c3c0400b00e20020010400e0000045460394500d50301c0c1401e010398003041d0000786a00e0807000602210340e50b2603040701034803000070500b501008a00c03e540980e00204056080841012941c60103c000c00844045210352150043d64003414460b02c0d502a00360032401d83e880241e00c000c0c0f500302040010b00608035192010400044101e85052030204954109140c84108207880303015184560b2400743c7c802e0300080c0019180b82c5c042c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 954698758 1250 954697508 954697517
    0x9010c1719090501020627030a0203041404090804171f1401060801050109030f051c0908070b0a1706010e060313170a020a150e010f020901020d080f07030c03021306030501030b0906040b07 82
    0x2881020304401001f8200b1000c5021f2001295107801ca5400000420944c0c1d0012130038008102c4500c104010b441034080d0017040650181300800c400e10b0034108070300e000e462500a40d07910314150b50381918501002c0c501500e40a0701e4105082d00f00840e40745541c0035041c20310f003d204641c14107001078000e040d00e1200820100c1d00c115050144241030142c8040140c0307200c0d1084002504000040c489000d40c0a40300503401803120004a10f04200c007111481c40d02c1d61110f4901d01c2c400d0b44960040c4c800207103641d041c4148c0030410700680d0344100007075100e44101005450b01030030904058454409904515a030500c0801010b18002c1d000614961003590203070606d4460305201401c07a001d4000c14801d0f200960070807440a01020940d006041406000ea00b2620303070f01d182200c210703820310b4152001034035496544041440390303100c0d810500c802890350070094544488000d448880c46016800400000c2e510f0006008100480081ca9084a01003004006600703040e101c20384039141c09400d000c00d10 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 954700008 1250 954698758 954698791
    0x10031e170a02070e04050718020406021c0210050403120b0f031209010c050601060932010f0c2a060206090322080a05010b13150b09010c17190905010206 67
    0x90344200003510113082c1692480c04c1e1401d01e1714200380e840301e45002e55001d0481d695510102c00003076200b680d08860031640200407000510340d650f0210b01902e2103001c1140030b10005000000c9481c02090701552180e0f42d40c80c42040c40481c6001121165504180320700300201294005e581d000500001860070300c052151395441c18001031b1042e0782805002400741c0501d01c000205160081c0c624070846a54102c4180040480051a500780022181795440004d6100b100400c55110310152500c05542c4d0070140300e40030780c94545000c0c03401c5080c4040305031241180703400c1c201e181910800700100303072500082c6418282040b149449006080c4030549404041c0704a48641c204092542d008040328401d444040800c2d00300107000e4003501e45100c5c09072000c1c406000e004105407241c05d0000020400002c03401d400c00c40d95441c00d6201242c8981003060000d0410080f89030000c1d4075000d404100c002543c0c030100300581202d0455680540780900c50300c244108001e0b6000300f6059802101001c0c0c0c501d40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 954701258 1250 954700008 954700027
    0x906090901150308030405061312080907090609020903160b1602030a121709060702070e0621030706050c040b0304300306170a0816081210031e17 64
    0x100b9980384911920350b548480081072002d01c1005500490048080d2180303540c6013050319134001d00004001340245109000800124403500b50720340c000752124103480e04943d40e04450810788600340c01c01c0480d00d60004a00055181c104034514940002c0e45aa03003d45180a407803001d02d001d440c0c8072000241850440c0c0c002c40d5000d00c840d40304d09510800440c00714110030802800381c1d440e54414070100081c0408100e040000243e058816030a80d402010481e0030503600302c1903607034040c0c40f0300d80100c20001600201101c400d00640000f031688011901c1e040e4034200482950b401412810006c01c00304003c0c030188001c0000c4984c00754125090f6070321228a200f10000904801c180b010385521481030501d50164140c005008132030700303000d02c0c174030707000c081485207889070380c00c1000804860701000440c9142c00d54808449055004940b894100a20000c4101600904613450280822024030900401c03418000c0b141c00000800c03420200c0c40065035030700c03020342051807507910f0010000c62000719 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 954702508 1250 954701258 954701261
    0x613030206040612140114041a03150405100b0307030609020121020405010e040203060907141c2009030604150209030a111008151003240906060e0906090901 69
    0x1580d001d880a992142d8404000300080104031800c5015410700030f107151424000ca54440c117896081c1050380d11035012404100061410f003000018482600c40045c101c1d503402c1c449601d01507140e00250f8403503c1c00d072800c1c90509005590241c2d03614949280d142075a10009034100a0b87d41c050800260440c86000685580401014105480603245480300c54460660090300c210b400a0701c4103002000520100300682c0011601c90350040301400c009464a4400d4144040780c402c0c8103401464400da06001c1c41c00318404803111200c880d241c0c2c1594050340f8207002c0c4c84c00300c85411420f55080c07a040300002911480064070140c80c0c80795908200780034005d03542c112803120310000c085407800e2000340f805d041d01a4005ca0010f01c00e441c000c0c44081d146009035840d070b100d90b0300311011404042a90007086200c003426101c0708205690b40e01c1c400c031100c00000f403080c000216804402c1c00f4514159040054440c5608402d0410102003040344080d00c1e00004241c004208a8002a059440d070300c0890 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 954703758 1250 954702508 954702547
    0xa05191a040b0a2304140913020916020d0f0827070303020a050d0507020a1a09040204030609110406060f05030406090f15050c0a0507080901031508030a120e0a0206 72
    0x6540c180000e8100c4400d9040350a540d4402e00c513132080700001500c01d102e003455016074807545076070950303100d500012441d104080b103a02c01d4030342007441c01c0822590049104140300f11018039410240c0201144081c0d010006106003c0c1c040c680741072600102d080c000e020305006041c00035020809030440c03030050390040b01a03401c0011001140e000329902d080081d40d40c619848151402e003c1d40f044226880c0c8103804591300e254020b8450008646400c1d141101c030b024541e254019544244424a07103983d841c00184025801550089403415042c00d140f084142c104400f50b00ca185048010441c403908900315489170342c2c0c0d40c2003c1ea12039032542001c2d400783c414402e0007809030b50403030888400c22003241541041c1c40001201080b6540d507410141d10720b48500341949000c14820300030741001940c05001004d5501044c075000c1508509000441d2001200c4d4012008540004c6501024154004401240c0070356040742400341410020080ea00d8144a00c0041e018000001c1c0442d000b00c0c9240442 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 954705008 1250 954703758 954703769
    0x311010305040c170d09050d0c03080309031c020c0c040c081303050f0a090e0115090302062203120e0612130218010e061c02180a14010308090a05191a04 67
    0x1504680d0f03540d10494031036580700d1700c0c400481c140720710215250502030a0f90300c1769544606605901e03800c0d40c0390948a9000180322814504c010810161030501041d41070000d00b240700000341e02e80481901c0141891704200c1c8072400b46141c40e41b5242c078680e0054400780c0280421791005101c42e000e003802c5444e840b5060540c04002000180442225848200300c4100c1d0034480321002503903210500075120101404081c00041e0044105002501c3c14200600b0034181240807924880c4040b443c100320b0070070940c070544050500c088903100f901e41000c840c0c0c50004040b107101d86050541e040c0041121405885c41d0750f165818140203045443c1c00705407500e14030644020940540c7d51720781c40c062407001107c905010f40c4010081d803503400b4103507145481d01ca900600044a07081c80b458101901c0400030300130200183c6940041c0c90303002491490501079402064000c0d030300c400e01018030500d2411944818000d9401d02803442c8001c40c0c081180050311800d2258642515940d600c41809003d5138010 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 954706258 1250 954705008 954705029
    0x4080f0d15030b09030f0406030b0609040c0f08060d0203100903170f04020a0509091519020c1e0c030601060e06090913200f060d062d0506040311010305040c 69
    0x80c1010a0907045141003281d2240d64030300c03116a40c40107142d4607402080511901c200c070030300003441054002e40180e04503190240115007440c83c24800030b002c2d604029031820205601440c1030590603800f01c1101c2e4048000e80e6415542c01082e40426034403145000d81c0703c05283c0e110208000c05204540600100c045171038946036500308000407900c4a00d00b6a400c92040f00e440d1000155410000d007014400d00048018001c0c1c0c2e00c05a003040003072200140b1520703c20003a152400d50920f26171001e00f8820310480000d00e424034220000c43c031f0321803d040c511040c07588005440b104640d0002042d50645902e8540741c40e00421040c0855041e000781425168021140000c001c2050000c6481c8281d150191401c0c5940e6410884265601150400156003000c80e00c18401c2c0c0350304006004180a06d140003000034220741c1d904e514001070b14584a0112500c0d440703850541000d141d102c0d01c10150600303c1d07409190910f107640e117880c2c02c40000300e4117043c95200c2e030003e010321004408e000020100580d1 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 954707508 1250 954706258 954706271
    0x20d050c030d0912020d2d0c082d1216030902040203070e1809122115180705090904021f020d03061205060f09070f06021c020109030804080f0d 63
    0x1d0240c103134200c840e0b180005110b1008104038061080400c130303812070400100180381c0c1ca120041c4141d40032105201a0902c60600000340c00508101c00924924614403c004000c81040245179030200090340d010308184403e22001c00a64a03404005800c0a0891030780d00481c1e1316032403754090050b0f640c019600610100801103501c0d0081c03801981040e04940840e56161581410b400308141030703c8204160b80300350000c17208005200000c0110f1140c83c940141c4a100c080c604601d1104103d4044005855034101503549082041c03101d40c8040e4454500c040310300d0244001041c0380078542d07540344a852030401141c155280c0301c0f0b0320780d1049030300e004030307000f46180d8400070750384d4800064030000103858401c0009290310421640c0080c994008064005621807075400f1800c214003a16840c081d00800324001440e00c005001e40c07005140359009800708180d0400b6001c2c082d00c2100152040d641040b0700040060341c84594a17a105500c008030b191201c1c088002c400380c500440f490804160324002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 954708758 1250 954707508 954707513
    0x2150417031b040b120f190b0312040807031205040303140f0712031e091e0201052101061205220510150801050a09080a0e031501090f0c050a020d050c030d09 69
    0x20050044c22949a44c2505503107a143d46c4229019085820f500c884002142485080d94980c10600c1c1446d002411164a4043c0c0d000318901e80e4080c1d070080b0348940c400031702041007041002018001e10318a0508606180c5152805071043c1c0701e40c00d0680c94403030002100005a542c001c04e441149801110650b210200010b010307000b40581e0002401d1504840000c00072054075000c0c0c44400e80c0d118000b186a100c1011440d844410500d10803070510030107000d80001c01442044400340c140c810380003412a545003017005080070251241041c001c1c2d040c00100f085000c855070700b4a00800c00510715526404550a2590030b0104203603007100410304056400c0840e48500c030004066542c1c2c1d000030482901c07120001021550307c1d1200410745141803085030700050040c400aa108030001d01070300c07060710b0380382001c1584082c241c11160800d551445020142030340d1344220118071400d414510700d013030441d40c4007130355070000d00620804103c8001810141d00b2024000c2d40c1c0c00451540060141c01042d1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 954710008 1250 954708758 954708779
    0x90503040e07020a2001030516141803030304050d11010c08010326042c06030717030409020318010506011823030f0c030f01020913020703020307020306150102150417031b04 76
    0x421200b4002800e08011610304054101000340d003050944403800d402d200301c104c051032500715000b65008011401c2d2f51844030f880900095100310320030741c041d040c25800210302419090082800074010303850070a1404110380c01c03c5440b810740340c00c5405007407010380103030482c1c002082a0240d4010070324085800941c001000300c22080410f65020031030f00381100190808900e0b002115107070b6040d484050100035000f0213200705020449401c060340e1826458020880607a0300523110504020b03400120000d84120a00c9400c2d0044003d10f4000c00d4407851051009025005009401c000e0070524071545540c003081d50740459001010701500ea50740c83c00481c1c0740d03c91050300c2c0d01c80e000340559804508600d00c18130856070802c0c001001920308a101d01c028800a40115000702c096200c100800300250360100001849a151600303000e100760b400c02e000900b000c000341c950070001540342050000050350650040c03c0f0300d4070305503001d481c3d94500916401014503500b0140400f1800603010880c2810b4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 954711258 1250 954710008 954710063
    0x11070b03090c0d200612180f06011e050415050f0a08011103010305010c08090d0e300706050a050f03040219031a16020a0b0a110d020c0c04090503040e07020a 69
    0x52110780d904c226441c4041c80f40f00c2c07060300311040081c060317a00000e24000c0d0040800108074900422502400c5400c00f600c0e03d001c0c0c0030f81107005032003070001c4524169444c000420000c1e10f4140c4d81400341c1131081c503903003e81d08000d0140a00c40c420210f00081c0544509030070340010f1102a000b032040d0480f5a5440685520a001c01d0b40d00d542402c20310302b585030095403a9030043d60b102c0020b0400c4042c404048a01e40303060941540d10030b528a0a107568140743c00000700850080700310b0a50000040e40800789050000c0d8483d400f4000c0500c40784403425080000d6440000118030160741d00d540c0d034800980904449034000c0081040c2e442d01200b0b1140c110303001c40740505c2c400c0d0402d00c1c07a00d400b101c05a0003022407a501d00140d0144440d03100207205103504a400070800a00810301c105040e103008425044035081c028241d5021407001840d15082040241c442c0b01031360304011010080d01c0c0d003500c0c0e00c01c50090703800c003000c2840850b10181c400c0003c4400f040d00320000c0314030045005200c2d0800f00c003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 954712508 1250 954711258 954711293
    0x6090206270f0402120103080d0615050309070e0912091906110c09040209070c05012d0b150f0a141612020f030406110307060f0603050d11070b03090c0d 67
    0x1c2c02040c10384a0a06101704da0701d00030000110711103a8070b11390302c00b0455030207910100841c80e1247d400040c0031801f40c5244001d80a56103401703441c0d10304150024500080e44d44030030308041c43d450a10094140c0400c0f810080704240c100140c0d03400725140800c80c1ca0503640072524692003803001c005480341d84405513002c43c04900023a1090062802c0800090348002d8034040e5000c0f821401068069002d01c0380e51401034480c10000c50741661604448c405842c4403e22030982030328584841030b8030705940c071030101d0000c41110f900707141c1a2505285610388c001d044864040450009280013030b580103c5c02d1030300000003801001e0341c400503020302c458104a254806c446d90141025000c1c210344c000300e588a29001140011404c20f844c09070102c0e0400079034902454240800c20103100420aa4001c0e022400c103030120204103186546405403400c0381c02c6928500b041045145404a244040788400c1240e0b6100f000584030307210050030609151001142c551301100c4000408100b00144030310801090 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 954713758 1250 954712508 954712519
    0x5090d060e0f0c1c02010e0105030406200418020c12070309090501090603020f03030a0f030b0d0b09150609040c090504030509040513020102100e06040b0417030c0c0607050a08040609020627 83
    0x1c4201190a00c24882200901103208131487d500f10754800c8020b1540315016081c04551403800c1c6282d52412844c1c101a030039103680001d020700103560042d02c1304c104900f040c20708502d40524018001d8840c0c114420900c500d250008000092510440081000e4165400e0030802c179699a00700f10024580e40c4401c074041e040700d201d076a001d4600802682e4401c0003d80b250040c0c2071401c40b00b10010503403118180e80c8050440402c2000c19102c3d4103092141e21010024170f6000e101e8a50b80804400c000c0c415031040d44803d0420000400b902103100403114103aa01054540312483e061300c05000e000c16091304189481d040102150f189103901030001c1c001c0c4c0a588a6160084460090306d5000c07255528640c0004042070000c3d030180499a80580982030408080850703950204082c2d206441c244000d94010a0544c00d0003401d0101d04d40025a605141d0b181448240d005820840010006003001d41d40d900c881043d5100e15086542f11014404400c5650000c40001c00401521420f801d00a9 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 954715008 1250 954713758 954713779
    0xe06070f12020a151b11011803030e01060f0b071202010f020316113c01021c05070801050a091a03030f0a0206130b0103080318240a0c05090d060e0f0c 66
    0x101e00340d00c180544100401702c2d60300a540003900c141d82400a480361610259a254504840810b440e07000041c403512a80d00818070f44a40441a42035680c941c101d02185400302c001082640c1600c4200c840e5568040003103c0521168034059005024030146491000d00020030408070038401080c200d000700140d1500408100750300c0c021542d440e021103065140c2c00345070015114203058803210540098000d000003d0042602d40010700313a03008000406124074138000701010300500d13800b0381d5622542602c0c00000540c0b40c0310000b144601903114113100795940300c403420122400340c0040e108500b805003c032070f0740d044500d5220103035034441030303081005010b8600820202040c00c0b00226031b16400c00c00c00c1c40240d08684640300a030f40090151181c4418405501035200403d10404001d0481404540c201600c800025186400b00600040486141000c59400300307810009a4031342c9201541c5010290f0020b00d4800024100715048515910924101400b004000150180504010366407202c07603 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 954716258 1250 954715008 954715043
    0x4142503050f070b04140d122001050411040203070c12080106110601140609130f02070209090f070905090f0a05010515031c050a09090213060305090d0e06070f12020a 73
    0x1242100d0107003000c8802c04010800080380b003240c50456500000340003940b22249541c0f081140200308c14030a000c5680a121811185130b0b850000d0601486c0704000d000600c0c141c0e68000d0a8005048501d22031940440401d20662042303d08803c1d450f0701065a11240d101c110b005000b4000900c80c0d0400a02c10091042c5604800700c0e10700d040700d090700404182005c6000c01c0003000d8202c407480c1900f02e140040e214140000900401b801180710a4005070349400c0d0740148180040003d0100e1055401384814466100300094940211000c0c02000111030715070389501418407948420500e024843d0552501c1032003010f52003240200848034001402112050034140c1f612a00910158440030032001c81b4071580c003d000405e0310405610385119200c0d2915807a0f030407a0071031842d20f503107080980707800c1c45096058419a50000215401454141000c0100a06085200c0c901c3c0d400341c0c4005c00c0d20010454812040301d078880c0c0c4072014806100c828540255aa4400100cc0d5020301909000039030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 954717508 1250 954716258 954716263
    0x1005040f0b041d060130210905091602030417100516051801050702040e031207030203090d0c0503090901120c05090709091e0e030405090105030102030108030304142503050f 76
    0x1855580b40c05401c05070706c0c0c82140b040c85100320480340d071025141c244600c2000d060360908905a44100404a154209030103402000c81d0440406c50601c6000007081c0140c3d070314007000550150007040704000354903095100300d041d40141d81c0320034603142444420403032158000c9038403804040e100754104540da8440840300f01d50303291040580c02051041100c005032105002007000d801c001818450300d04000f0b6404502103491010b40f59807507400c00300f07015100c1070001f210207410602c585419410f40c01d05140290710707075014043c107005001544410f18100300b414030a690010500074042030301981c1d255600c3c0307070513410780c0000c54104012640200d890300c0c2c00c00103280a490941d8403070b0101410705421030300800344605004002d070026056084210200e000d5130b181240c0a6000d07648407840c1c00280045042c043e042503210fa401880148040d01000013038030f6226401c69210384045088000e154104504400404480b5040460300c0d2000c0440c1c0c0445d008407440382044907181d14004001c03a4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 954718758 1250 954717508 954717551
    0x15120604050114120a0b010e07081b0f1c11031909031d010203130303110d020106180902060c01020a09031a0709060f03020f0c060703060b0a090b031005040f0b04 71
    0x400404851aa65824101340d85190042c41104803804412962645280c0100903405400b05881c4201000320315a44032900c00e030440050526000030b003c5100000c0503a0145540c600312708400415103001c103091302030010303080c1c42203090104001c1900b075800001c1d42d0310448181c0300d1054180c07000c0c3e04030b5046104400c0581c1d00b6982e0f050281c5c0e188c1154980c0044244800c5046120034420000b00c065a4a065002148261940301004c0c0c203082d40700c1c0c03d101c1881c07465425a49000410401c2001c50201022801c8030f44000044910007440082c10500441c2e009005641c408900000d00c150040030880c16640100d0242c850384030259001143c882c03044a81c1c03000603c5041c020840c242c09100c0741495040a030074050f01740240040c0203200c3c0e400c01d11008150b68880020b02401d0340e014812600030b480c00c04034147c5445804240a80040c2062162105200b0000001103116400102d000301400e002402400781c160a0905030024021003040c06126510f44031020311500400c20600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 954720008 1250 954718758 954718769
    0x91b09080a0b04060906020d0c0903020a050114180a08030c0a0b01050d12030b011b2909150910050106030f05060a14010309080d060b0d060b09060f0711151206040501 73
    0x2e041a5490740c0d600781c003500480e041105c0c01078003071060310304a940c10700a039030282816030744800120740780d07004000380c0440980c4503c0c140020b00903481c0d9041d850408a1701440d1004110f4405005190041450810140d0041c1c180340004661a2407044021440b000b829001c1c61010440b0390300c80042289021024000074100d40a405090072018045e400c86000f00f03105042032409448130716900b214408008004981080080800740c4508414509082c80c00b0910090100e0754a01907005a5441c008151481c3d4103490282c000740661340100b014030001180c00000740102e594400d0040d002d44582025948031030700303000024445080801204085800481520705480000c00065005212484055407544400c024071440300c030807070007200010040d1941803551140148411400c032442900041e9507440200901d04c0a661a00b0036501e2070042101d4490350741c4440d2400c102000c60241425400003c1c0c41c0061740d100207004043e2100b00c0100a042c2c84566890007040300701c440034000d2 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 954721258 1250 954720008 954720023
    0xd0513080f1f0626280c09090c0e0c0f0d0524060a18080703030e100e01080609130c09050a0b010e0307030311031b1e0c0d060c09091b09080a 62
    0x100c103060050304d058100c0411501d01907900c0003c0b05161403d040b0b1808400c007a8240801e2400c0382000801c6a00700c0091020000c104513091207943c88000140452080046a01d00600416403c640301c204546a031120002840c1e5940365140c0814040c1004030313481e10355040d050b00314a1020b5803181c01501d5410300180010718081d03c1d1201034640c803110b410702c452182820200420b4100301080403030080c40c000d8845031b40c10b0505908011000320034045030810000405c1e90880c03280d07004400c5035003040040710706003910740c0c506020962600c25580007a041c0c4060b084005401e00c000d0788103500503089068248041610740f00103581c60f11144101c607425922102040010910500c00456095130300005d41c0d142c50324103034000c0c5070001a4804a010358101d032000c00c03440b4850486060150b0700100c041d00d904d20401c1c0001300503c1074040d0252400ba20348014000941c8030310658005048a89400c0000c04100c0b040030402c40c5009401ca00819129180417600904c0004c00344039040c0c1c80000e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 954722508 1250 954721258 954721289
    0x160509060d061e02040801050109181a0408070f110f0d03050d11090a0e010906090b0108060415170c1002120301091a060304030302090a090e0d0513080f1f06 69
    0x4404004100a490041024000141e08140c0143d540010402050401d001042550410340c000c8211140c0b5200c0508010803c00d02c000013508045440020608541502c0815992400c00d01c1007440758540040c40001400d940d082003059420031005d0301c200a44110315a445200140b0144011101000d40401c900380404103d010054010001e156030201c00700e800d080a62011442d180d81a4102c0707010301d440c8000501c9060800c2c81828024888001c01340310400385040040e003500b5010f09418001e645070702428501c00c0b4101d480c08000c1c00e10100c5800015145481e00f500c6a080b40485071244140140300b07140a840026403401800d90020301034a9a46041890301c0200386418003003807500540703030460603a07a40b41d10103140306601945016075604881c1d420010800b80700e40182c6261454980410802e4fe00081c555440704054100075641f88072440480d1040d00303451303115034580d2250034420391207190081a071400c1c8010508104205000411650040d43e08078060b01c41603240040 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 954723758 1250 954722508 954722513
    0x6060f070f02030717030d0e0304050a03032607090e091c110f03042303300f030106030227010507060c2304060906050715090302031605160509060d 65
    0x4004252240c4018104c46030359686580007a94410000c10841291b000855001390124141c05595450039038031000d1882c1a0400c80010b4a01d0341d00c5c0006010041900409030012230140a0100e21415a881c1c0f034609141c1128014003950143c065000d89803c08000f0030070b40507000038881210b1100002c0240d96170702e0f030141205c40b01c06144944003e4458600b080c000c05e80240000c00142054903910b2080c06d50850380300340c6458481d03404c0d0f4043e0380045100c8007040450794203209201340350b40500d0007810300661000024003500b035050494880c0000005410794050340205007280180d8100e104000c240e8000040d59200c0c00c00c1300340070500401030040040c485911443c4580901d0822210000c001400c146881c502c074041312801402c0000d09016a82e0090004130080080b450903600d04003455680c82080b011007826800390175203449440080500034019034141d03031007285003100d0210381410456961074662020300c80048103440082618203080d04d08070b2040102410501e5a0402603 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 954725008 1250 954723758 954723773
    0x408030a020a0c080703020d08013203010b130b04230f13060c09031704050a1205120307052214010818030f1305040519090c090f1406060f07 62
    0x181814003c0014401a040008610a001d0302d01107029600806242e4a03e40000e0400b000682081c010503491464072152410010740c2c04451a0f483e10052242c0212180402e026000c03400302c09500401c00c2c1c0c9112040c81c1c5a5015500c0319404403001e000d00203800c2050082580d80300b2103080b10319401c0c40015044042c640d24aa0080c5030398807900c10307840e210784900b401caa06401525000900c0e0010401c140501c041d0315002c0d60303411103480d03445c146c5048000b070001e101c40c4c4550700301c405502d0201d400741f010a000c40c51007400000f40c427643d41c1c81c0880d00205a5405440f022134051800300300005a070b810284180203403600c1a28100301240d13201c0c010741d80a84010030036207400c1c4c01c1c2c3d01c13081b580391f0060000e000301c100f0011826840346814014034122840f11303007000d4051450042088081341e02c91042c100c0110102c0c500060880700d03030401007130020158100d204040d04002e103109031030b51640d00c11000c0d1910044803550075128901000114031401d0000c03807082100340a4034000c505030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 954726258 1250 954725008 954725017
    0x40302090103120513090b01080a1b0804020a1e0602100c050a0e0a0f060507020405250503041109040f021903021e010504120501050603071d1504150b030910050408030a02 75
    0x21401d00034105903001491303000841003500a506c505403503c020042c3c5503000b0307a9680c0c100c40448020300400c942c85a156038102030308c091100030044480c0c046025500c1d4690031001500f00e1036040308046000c8844d412030140148107020040c403a84040c403401a005100c0c0402c203402c16600c181c0740400191089550150a142103948031140c40d40001d181c10840960100400941c2c8820340c85981c02c0c0100412200000c0c18001d48040c49000701c2e8580241d401038401240050604640360784640c1018981e0008601c0300c250405c50000034003040c440c8021500d169076100701d45210f0b0b0a130f050b0185c00c13100700ca6448000d40180300c2c0f0b060341d000e0250b81c01d1201d19145041c9000c07400c0903a9140d62050800521805032003070b954841c141720b510708051249402400c07603c1c584248a107014480304a441e40c1c0206500c40007420b40806640558850704041d40000540715441d9070140c8881c80d0903002d0744156a1102240f00302441c08500c0030540c01842e1241e90000301081c1140c0d10702d14030b080039601 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 954727508 1250 954726258 954726293
    0x80d141c021b2d0d110c040501090c0e060705060402100c0b1e0c090f01050c01090507090e150c27030f0f01051506090411041a0705010609050c1e160605060312040302090103 76
    0x30f0b03406c02c90540c2c0c0300c5210300e07402892100c1c00896240d40c903039405030848034010841401040c0822480011640004400790000c4c2c2c140d5021541c80401681151810b00348003006214072448414010104030030302c140c0c01d16840050b40e5010a840c0c01900100b240300b0a40e000d600301c120f400c00155250700400c05048401c0141c000811244080d83c2c0e5141445c0300781d00117102c901e41d10704190b020590204541000b5000341c4041d080b044c10510301001310341c001c0c01c0b02000165035248804803031000071703184403502e0700c000350488100903540c0c44d17155116080b510407401c4c0da41c41c1100086460085011170f454600e4041c180d180b13130502c01c81c18003014005103114030b0451081084005044bd0070215001a014001c5070038980b5010b0301c0c40d05600350340340e075030200c80205d081000784900c0002440440f000c034800e81c04041c00490200701e864659000320b41d2018111102d000b012000c0c444c440d00100d208070411010354000c6464100d00d100d149c0110700002e90020300b841c005200140080701c549140c9607 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 954728758 1250 954727508 954727513
    0x1021b030f0d11011508070e0a0b090108060a1401211403040305030d0e010605090f060d0803090a020a080d021e01090f0c080d141c021b2d0d11 63
    0x3205400c0311880d10310031401040005038001d0104031509401c3c490043c03174403450105150316078034050486540f018540a0700003060030030004549040300d59801043c0c14030000c1c01c0c4100d1580d640c42100d13255442111070242c0750781066400c0350180501e01070a0b050324074519009a100803204120610361081c05400c6403210150004040302100c00c1000e0700045100d1402140c0c1c07501c01071200c90039200428040b051a80c1080300502c229941c0c645403640c401c00404506d400d03940e400000a080490840016091407030010a000c841c0c00085680881c850091b07030480e0700076944440d416130f11104400078000580004400d1505070302a550280b60a8080800200b03200400707032140c46604d10380d044121035075403444000300b001e1002403242c00300b2800c0c02d08064901d0501002190309910940e121043c08135241c100d1500c0ca0543c42d03043c1d811280314050041d40c02c001c2c4940745988d810081c6560101507003004a0703205d03030010820300c02c1c41e59040e1354090407400d0b10100082c3d41072108256503070f0150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 954730008 1250 954728758 954728773
    0x1050c0105040b01081605010906120f060611190f0303021608160308010b1603050f0d0608010f180818130f0c031a010519090b0304030c050c0a030201021b03 69
    0x1048240145400746015502030b0445500d8600054a091000801401802800031042007145e800124520455003d804d04c4410308400001520040206040c0300d60340c40d107030040106030a9409901c28601915103004c6a500407004421603040f0840203400a003a480c04d4204c16001078840d402800064280e881c204041c1d00c01596000c0840e04840e102c401801641100c06003419800120f85006117410300f03902d4606040d400326048011001c643c05401d02c00000380e00c400d8603003000100c030400f20480b0002c1018540f9041024003800031442c04c005000c0c1000040b2a039461000c1680d101c107540f05000a25041050449e07805c8082e5002d04180d0107a103240c400d045502d00c5010f540c92030003135004000f07590010110041d0456055040c80081d5802818058209982000c112400c070800103440030000c18042104881c00d06403500448210940801400700300350b00a00002907541c4140d0560f03550b10f1210062100d03500c958070010f07005a01c44880b2425040c82c2e58400440ea500140644125 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 954731258 1250 954730008 954730027
    0x606090f090906160801030503090103110c0d0c05010b01080c0301030f2405060307060809030406030216060c020703030e060313231c090b07030207181b0503010915060504060c020105 80
    0x24030201c80149407500301c2d80030418440d2003512015603084d8542890100d55055881c1d0580c0e9000d01c4058905059071000b02401c403203040f40c10356031414680401c0303e03140340d00440024048024400d00707d8040d820460b603220198012815103100d602d0490701542141c1c0385031580b000403450800d098424110b49040818410000c086907043c1c4401c0480114090a00f00245407620860350300c15002c10010b1010320482080c04000c8a04071422440c5c0540c4400040021810761130400ea0300030603280c40c104031032a6083d00410604e044901948900201c01d11070700501401d8032080381c0c507900c2c00c03a951000b0b03000a0341440b200c12044011502943c42c1c542040e400741c0ca801206c24074600c030741003802580408150310171400030141c000056140d04203d2582c2d0043c0d42e82c00c19008245032038426200c000240303140d0b94807003541d4041e034400324000c3d01c20040014209500c207005207614242001c034444d09026640c1d00140407200310365111482d1514141d42116002d0700c50707008904020042100426 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 954732508 1250 954731258 954731269
    0x15081c050d0603200a03120f03110c0f1e0c060a02150c0c100902182203031b1106010b090418060b120a0c15050408010e0705030c06120606090f 63
    0xe94132400b980381281302e104039451001c60040d0300380e51245403208028000110b8610b40d0301080051400d00403800802e00500741e0240405245210201101180041c511140083d5000d4001e03a10b40a42d0b0340103c80d449800c01811508000c0500c551250304a0006420540000c1040c0030300c503c10303120107440703903825640004d0040d00e03054084200071a510300e0001041c0400142038021007001c201404840d40400c0209000708000d41c03000080c1d41c0000d1091645904500350080081a000600d6951307240c040c00500c581d030080540251308045149295000304142d102201021004141d142c0c60f10310707000081d500940c0c41c00c4d001030b1550b042440011410a449034110b00c900c0c00030541c2d1460740c041c8084c20024880741140345d40030a19110101d90012030300c0d000e0b504212110400c100420342c003a0743e18403030340d4840030707482d0302c0c1c07000c545d10741100841d015080d100214140d94070000c40604105460080100441c500548071005c944503140c140d0080400c0c03403010700510302091074400081d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 954733758 1250 954732508 954732521
    0xf0307090302040c1b17190305160c0b180c03030f0c061f090f0213081c0203030c0a0302131a0703080f13030e0d0209070e0415081c050d 60
    0x408140d40d02024000c501d403601802c41c0d11801e0b03103002e009800b10780341070701e269014641000e00392840d00c9251056540c030342400c807203c120380c88802c124554a00e50006008060403a40c10b80d9020050040d0000340b4410000c0800540e045a442203103500c821840c05601605030311068064451a0580c2d0610b840510251000c03a10030030703000d51580002c1541d035051500c01032862524003a80310014107402101c0000350141d032190000010642c0680044900a105d0801c62900c09010b4640005400340002540300c03045809041481c0c400d04029010380e80c03400280c40c80950f0050500c11502e40f02d1082e8050703d00c5840da00710031400d1550b1680c40c0000340c188803084007a0404002149401d240c2c0211842e900507a0880110410703240c41e0f44c034111914a000001404c00c00c0355650a100c0f9a10f161446404680051064209007070a0b4000380c07002d10181032050086040c508044c004500282d401c00c212202080908902d8520070704015860556040c641d09003e418810369202c00d01c40e20804 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 954735008 1250 954733758 954733771
    0x50a050a032f27060f030a09080d0603060b01110c0f06040e09030a02250302040b040905010c08220b0f09071a070309090203071d0a030212062a03070f050f03 69
    0x9035030f000d0101e000b030784000c0c8a031510703100303044404804110341c1c481100300e0301800b026108040c0c4944420360207101800032441c01900144000c182c50380504415844041107078403929003000540440340056400003200009001660841141000c070744c2130004106180c140003c001c01d280030307280c0807107188010742540c2c440410345c00030840c00b24054040180c20080d82c20b0114560000e080140c800b036000360719000c000d00884d291404071400c0c0c3c8480e0802d5400d29400070082c045010a4140200000b00484490609600810019400c6da800000d200e81d4580c02c00700140300c0f0340d5152448150504007411165081c881c0c5d840000f000700c00e8003141d003003020081404039610300c0c035800c0c014002d20080c0c010b240c61502c10420b122281c0d811220345c43da0845918085202c3c0780421000800c142030962002e03410420401d5141407070003010542c9417007801010016121240303a410407600b141c07880540407001c0d503410030200e000103000d00e5030034100b81135030303e0050b29000001c4141e0300180c0003510301 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 954736258 1250 954735008 954735101
    0x702240f0f1005120705040c020f0d1b230618060408090d0803070306031a090c0904170c160e010501050f2505060628030f060908040f15050a050a03 65
    0x50282e4031f000e010303251042c0c0c1c043c8018102c0300e000c60f20a6490704c0c2034044220a104145081169800501d08088034103a0005840c006030307084202810b1842440c2c0904058034010308002868400030314650320758208890006000d140d0700c66507074000340c0e4040301500b43e00c180440c2c11500080c0000c8000d61040200c2c1d034021500320300d145449010004028419854003440104002110500042e0800b0301c40c000c41d90041603480340d0410030041c410601840380080300000e0194614400041c0d15881d02e20301c1d4031141b105907070300d040201150001303010301c0c1d000550401000b640040044040d240c111f61001941c8803a24030580d009401d01e40081048801e50080700400c50700303140040c100070310310680f002106146c03070551881d030112020a0000800740705214041030244a4144c1c041c0c283c45502541d8a95035580b0b440031906a405144a400d0310801003041c43da80e05440384098034120320140c0c50322402e20300910010340251294004a41c801034440071140c00108101c506c45d44080ba074040b4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 954737508 1250 954736258 954736273
    0x813111804140706050a0c12090b0d060806010503010605011b08090d031101181110030207060f05091207020d0605040602070f08090a0e0906012c0702240f0f100512 72
    0x269600307103c0d2039440304041c4002403100340080ca8000d41034040150b0721454242d00e00c0c00c9100d080e034901c1525040b440c3d04c101c0c08100c0306550000c1d54041c44c01c0d0741e5101e0480d1200c3e80c0c1c901c209400d0381c01c140146400101500d030b80410b8600300c030800c104124032859505081c00f24000101329801c003568415030000340c040818090554081c4545000e6014a80ca5042d0f0300160b41c40d0b03050b15011242c02c942c06248007201a0700294402c2d41640c001c40d500010500000040807520303805010140c07510a030314000c05401e0102650500200c400407680030342080c4404406446000c010a0020310540c3d98a40030484640011140b800c1220864800c2440944516583e814803031035861f1034000070340294064091120a00000031f0090450f80800d00310380041ca010641524943c50030303100040c042c881c800601c40c005801013070101040041004402c4507075501084029551410b55086844020003400315446d44200800c076a030003110995000721103a0b594020581110b0142c078500040d0b040201c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 954738758 1250 954737508 954737543
    0xb01120e1c0302181c0503070b040209011d0f040204241e05030a08070302010b092e050d1b120309030213060b030c2b14070813111804 59
    0x40031a06010307040c5411810155581c10750303000342d2044028030344180300100c400b0100d40c40d40d41010381001da12400b03403501c0381c80524280400e04025a01244143c1d250800414032050041016001d041c50400340e201c26102c101d1441183d020140060360440c3c0c407080c07120003141c1c40c0e07075204101010384508545010b240150040e980300d1050881c401d50350f0100c00800080d500090300e07550b00d41c1c105074126034554107440c06138010520070f0410b5411040034002c11450003510ba00e120101442c250304808010703031054181066404030300a140d48509030070502e5000c140e4611000c41e100751000c80c00c1039081d454241000d1102e0850300105c002881e040800d0003141865800400000030548040c0842d07801c2c444155980c1c0801000460041c0c00454000c0c200b030610f07401c1c4440421103076034920f40c0c0d101c10041c0c040500124400102c210b414540032810032441a0101c03485504803284241c4103144654659441e44017020322560301104044c000c04c070603000c400c81540030b1446400b44010100402 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 954740008 1250 954738758 954738793
    0x40812190f0e030913060e0711060a02121503010905010e01060f0f05101803020a031a07080105010f0c080d020406090e10030201080115030f050a0c02010608070b0d0b01120e 76
    0x4052204441c1800b445103400040001503d90f052411a0400325040f03140301c404000380383c903130f1048807200102414010320b9900458100e41560440050342d106940b0140e241c000e0744920482c58a05800381d1000402201344850009001080200045145003a946445007540d161400007112079544038420003841042c3d40300240104005148800d040b4606400a500e0720321a040d400244100300d2061440c0f26810444000030b141c1c0108241c24040e180d05040742d91072055014082680c1008003c20442c6000d03c1c1124100c5e10140d54520702180120422942c00c00d54410803140c0180502c0500302e14006030020b0310140400d590703007103009441e04003901c4c00e6900181c400144031030f01d01014005030742d000106d2815110603500ba0300058100c95800c40060861444140c1018506410b101030001180c002c80e540340c04a034000d002c49500e0b204010f459030071038400e01300f03420f0081014082850030342e041a1000715050500e290300002c1c0d20241b0051314043ca080c10001d03000568030340c1803201230 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 954741258 1250 954740008 954740021
    0x30e060c0c0c0a032102070b04060c030c12080f010e04020906101107120b011a040b0906160c0302040507020c03330a06031505010b0714010b0a09021e030c0a030504081219 75
    0x1b80b00801c0c00030f161600c620703840c0c441e5014a10070441c858003420103050280c443e0701e20f010790148102e4100d0bd41041e0003400008280d43d6000880d15480000070400c50303aa283d0740c050f030340040207101d40c1d480301e1041000c02c00119803180280818400d2001303a110040c4525001030040b4110f042c200300d40e5180070115083c050300700404503c038040c4500300c464500702c00d59064800d003c800d981c1d40c40c04040003401c0c034000c202c4900c002000d0502d80004001448500e24203c9200f0341c2d042c401130300d0b42c0c84280d84500b4640b1f0200e8040d800042c04d0700180034680110b00070100107410454003001c0d25082026101e10840d441c118a07600e031f4030308000704002e48041b01480070046c60200200d50503d95608040d103c0e4070f401401a40c119010340c41412020f502180d091400101524a6140e0305c02071040690049000080303004240c6401c14a10702e07000e0b0840c0d100d100744036441d0f03180040340b92054004120180013507400000501858802c0030447c01d03104d00443d0300040011135070903180080002d440c2d0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 954742508 1250 954741258 954741323
    0x14240604140c0d020f0a03020d0e0105091009081303030804030e04060b120411190302090603010515120c031009060b1002060a0b0f060f031006030e060c0c0c0a03 71
    0x40d000c0c0c90418030442001442c0c1000510740724a5490240e005039801a003d124008000c0300300000b9404c20183c0c241d40100800e01c02e10b141800340312075088900b803c841703044500b05001d8000f5003481005c0d003010792010404a02c0349031070790708200c100c1c501504614104d070001c80105501c0028801070607003184a96084400c115800d01840f82083c400c41013500400d031805002d4000080402c081040134a0740030400c000180582101c0181c10310032014500c2c19100681c0500081c80108181e0308040c01568810303212004900c0205c40d1420502032820664a10040740340601e0080024a50781404401d140300c10903800820b1019460038020100c0d002c00122510642c80c541c0f070585041d8000c04c229030302020208001410488280c0441c000d00501e04c0c081d54401c0b0001454903070b00c1452400345001b220903801900103192684e005508803070b88085400361a9001000144030144030a000342002d017100000d0310101c4002201241d0040d005800c12103526183c42012511103503200a01d561502 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 954743758 1250 954742508 954742511
    0xf06060309170f04051e0409080915032e151211070210110a0f080711030a0f0204020906070609050604110105120a0c09150807120b180414240604 64
    0x30694050700030503200381c0c0300c0c550056500d48800482c9051a180240110002410910000440f80327001766555000502003841515400300d00c8884c91134103000d030b030301c40c030207410722400503070610b5455840ca03c403441000c8605032500c8001160200418041e16410a09034031000c40b8910500c0740201500e07251030111400e450140040030150b030300d40503489406005402c003100d84810b051402c50811010143c080c00715540c4401580070480c00c8802404481e000d00c002c501c9201c0d01d0810944c031441645000303446605800c00000251038030798001e0a0031300c4001e01c0f082c540556940c0320015603865800644040d00240100700034405a5641407014207000d01e007a51900c0070101c1c90302110340015000f1a1b46503503c00022070740601800749400508040541c05220744225040140480c100303c942c840050b1443c20103400140b540c2c041c0810080b00146402c1d50365030240c0701c13141c11b004020400c4d92040031074200111516410301141040c02010a1100600c1005100b00d0003550340181a07240500d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 954745008 1250 954743758 954743767
    0x10207031b0818210a02030c03060606041806050909010c0e15180609030a0b010f080303070903060f1113030302280201050f130e19141501030f0606030917 68
    0x140060100d542400707100708440700003c0320401091040c69400340b03500c0c00c118010315402000c0c0c40000e11401c1c8030b20031011a90100030076400d1640f83c0d1000e8074680e4020304140018406002c40411222030390020038000920b0954500010f400c07528260f40b10a0141d54950f032025046601510000c09160140e55011846030300042c080400c2c42130142030040030f441107802e08803642d01c600031514012001003c07107a0210103030030517034900202071199a0340564140b4000507240408425644034a4640e1500b505207031a54592a000e400c03000a0b181d00d99903203041040742145084068200c03aa0503800720b81c4514214940a8501807184080d0944020300b900c20b60300711800d0300710001001e036081c68200d072144a030500381081400703081080180928450702c003003540c44201428520619800d4400f16080f411151850120350510105c4001c000d448030003c1c901d01c50307410030340d03d419206140020345004003050720b200b1541c40760000d10000740c40c0e42d4001d041c04906015a00030704c0d00c802c120b605c4c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 954746258 1250 954745008 954745013
    0x20307230d050a200607051c0f0213060f080a09030c0203070303120b04050c09060a0504170a0c060c050604020f010504030b010b191b110a0e0a060e0703020a0e0906030f0f010207031b 80
    0x15105d00800000400200107109428001d240c04c511030700601441090280840c1c580500020b50032000000e944d10043c0d4000080c070611400e54414000d885807690041516010f9591b030280007604010707818020f428103104016103082001d00011030081e5140741c001400b1100203c103540550807001d00c42d0f41042c0901504e00307180e804843c600201154180e540e070400031030680700c40c0543e910a01200c411103664010400c00840c102e15240d22918015215a4451030156880004c81201078055131002002034018100a031002c909010141011401e080d0f8030359400d01e811400760000f4058403004924002071118103d0100f40c0b4807011b051003c0800c40803e110701230342e80701c2c841c003401c803a8400790107a03a140c4420391000c0203400394a810701c06c6854004060400303840644076482c03400c9410780c00502154401d20a8038005903480c2c1e1501d01c400058000c024080d0000762079540d02d800b42481199450742d00308042d410803000c10002588510450030060060007000d4814641c0300300000c40c8100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 954747508 1250 954746258 954746263
    0x601080c1f02010b030703051c05041805190f020d0b03060408121b0d0c120b03070b0c19140606090709060315030605191b020307230d050a20 62
    0x240c190300d0420201922103500d00303e02410916440d5a0103025075007010040c80804580c00d610000d03034088040b00302c01f00a0381181c07903114901c1031440e140e6446031a01d07412071298000300c1d002011031401c08a2106031501c000101d0302500c54840800b0341c00034060810120902032586500401c4029084030710b000c0c1c45d0000a48a08940c43e011141903200140b08840d01a8170320148564501c0169102c0c0c580040800040180d81c4659010071500584d80c1d214900501817540d002c2805800742060525015145030b194020071070b04071060285407008540103401c03642c0707240b64500608a48803040c01100c40c803410541c000d4201130084480f031b800c000b0119080000c03001115194070b80003031003015856240400700f0990f00020010f41c02e100c240004424020103200d1110a45442081120426021b40460352007030354001000d0f802c284134003008144c1c0f13100324006460110245c91006030f003d18505081010000600005c00c2000c40c1202080b03901881c07503904d04007040501035051141c85e0f00d207503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 954748758 1250 954747508 954747529
    0x9030403051e010e24090c0a0611030f03040c0312030509060f1510031a0f09130f1a0a052a03270706140406090302060304020f03060a0e0601080c 64
    0x854441008105403242c00d500c01e00c0c0e9100d4040595a007442403250f8650644210340c81040007028010100d045000d01241039181d032000200001601440c3c024142c0344541c0140d035440c240d020a00c02c040521020350000c5101d688070b8200c45c00000d0451503c00d860000c1c2c00e800030101480c1204118000c000007544035003002c11401c00041d207070768600e500310802090f03103441500700b50007402ea0003043da05504040900c0e44c0ad0aa80030b440c0040d0380c01c1c441c500181020f116880541d03440419080a16001d030040f80d68055035501c407610145445104010280821a00f076401441c0b04101014003544a60340d0410403206030112141c04207145106082c0d554401d07203255905c00408902d03442ea03460b8800c8107103c910481804a0001d1940041c2c4030041c6118503070101e01c1180003031200c03000341011903098414646440c0310721411602404490b820050040380c005401c580301655603682005068818000744001084103020b25440900f000750613445041207520806644100303a44045021 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 954750008 1250 954748758 954748783
    0xc0b0406020306120d0905091b040b0904060b040305030909010504020708032e06090312050703120f0212040818060405100c02030309090118061a07060f090c1d0903040305 75
    0x7503201d441d00740000b00000d240c4508100a44135503500307405907940220a2a040303c204079012100c540ea140c401c2c182c840c41310302e82250107000810060000c0c8040c6000b801141350040c20028010342c840f998003105030301540058440d9072003c50f20b00190b00d4140402c6025040554080d4282142c5a5485a0780c0c00041c1401800c941322141d110002621052409208407410700700f02200340c1d9402c400760903008940802d81d40301c4800070100110318002d02c05c4039495a80b643e41d0300105034910680c00010880705404009a91f020440301810b5800410894003450044054581e103240b00e000c183c000d4182c0500040c0180420700c01003084c1d540c0d100c10303030070008440d0422341c06c2000035100007410b610400200c254420404000480c0d040301565007080d03038a00303000d020003041c0c0c2c4a41c082525603a076100c03100308200c0200324110004078190002d010510b2003030000b1071203050075529075410104a8101690258400d41440c42001540b030616800c0310301031011b14585411500d9280e10b50f1400d1111 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 954751258 1250 954750008 954750011
    0x1c05100f170c011e0e01021203130b0928110301090b0105101107051e040507020f16030f080c01090b0c030a1112060f1504080102120703050906010510050c011d06070c0b0406 76
    0x1c07218287d0007480415042285ca9080d5a80da04d4101c01c5034441c0c401004060b10880c5244000840c079000c00561400306007101c842e221505c00592450400020700380c00100c2e03a10309801c0c94a80c039074134240aa9081c440c81100308104560405040c07103511071709210020304205020541c1c1201e1390700071801001303540c015911407018104809614030300055032307044c1c0c03900300345448208010581c1c007243d00003009101405071703880c074400590344440c0e40764140005040482283c8030000060300303070070050045040840c00820542280c0d140d42000d00e0003242c015180c148000100300b0340c61071510403080303410000a81c05082c201101c841c1440850000d10440c02030101403900007080d03a8040c10441c85102c06d50300c5c5a036031600c03800700502075081001140c00601458002c12034550113801040e00c549025001840180e181c40208400341c0040c41d0b0740018040100410b500103402070044000014540003641c04210800c44424500a030080c00c8404101c145500c550000d44c0350505185c200d82c100b0030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 954752508 1250 954751258 954751277
    0x51522050a090b0906131412040b0301060e0108100e0411090a0507021608060a09030309080c010603020a170604030f0e10020a0506010806220206090d03180b1c05100f170c011e 77
    0x7c51615081c807100e8900310422000c1000030300c842504009505882d481c0e524402d425180e4001513491810544803011300d4a44e154041c00f142d140700000540c0030380504440b00d84407184101250320b203034064030f099203903548410411802c41d40404c1441c1c030804411f041d0240861900b1200da88501c00036100203101c036141d0442c0c8042c9442604078035050303900218181c0c0d0b1070401c0c941090090074203100407070182081c2c4078001001c4050b030a00034a11122000508420394541c1e070103d030002c040c0340d840010700440c8070346004c95442d001086010801250014000c4002d1420120700e0300c07005a0111441c1d5002d44100580d0010010301d000104044e4802550032040d030b44002040c90043d83d48107a00040600954410b1661000b000700c0110184050b00820688450109d0351500c20303640c1d420310450060040c003454101c6544150342c80b01e0b51840c00c02400b521080411400e507541d50041007009000d0b54440301c2d8050620aa12790b428003400d20010703a02c04142601d81c07003501105a00140700c481c41c07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 954753758 1250 954752508 954752543
    0x11031b040b2103030901180215090a0305070803120c0711010c0c0305060f07030b1801050f04090b0f24010e01050319090321051522050a090b090613 65
    0x109030450181c040003611082c29031603a4841c0e0f41d03041110501031541c01c21042d071070001c01c51700103014515009031031910190011221301c000d40e44515107154100b0500ca00001c086401071000070050800600510390340d1020746e80700081c0c040044c14044400f6020801000041d40e24130110000c0d070030a0911401c4892103042015507000e5990000e4218010182080008103017500281d00c00e95407514100b00000f01c00080c0032042d03080d01000c0c0403400d00340c00140300c98949050004c50112005002148202982d034a1810b0350806880c0c03400c42d80050320130f100341d41940b4000020f170a50303489030600e100c03c0f0047c0000c00b807030811180346052103c00804138801002c42000040000f8071194240944c219901d030050240c1017042e054990b081d80041e446400e82c54a025090003080014030324842e08910358104118180f440d29001c1d16141c141031522000841409075500c00e001220001401c1302042c00d1503000c0043c01050b11000303401c8101080004103070074404010082d00a4880c030702c0e0740d141c0c4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 954755008 1250 954753758 954753769
    0xc201b0112150501260a0b030109140102121b0306010503060a08161802040806040206161b14061615060b0f04151b060c02030f0f0711031b040b 63
    0xd2280312600750400502a82019040750310700c040322800e0b0b80d40c0f14010203914542802c020301424250248604501084a540e07941d00807510402c0c0060002403890600e0380e5526a000006118841907500400c4080c44c0400e040f40080e8082d0401d10680380a48182224114a200042c84030f13040c04404800704d02544c5965143c0409820320004448a0034072869600f10116aa4498003280c0c404e249041c408003c0c440c000e0341d04540c0c0038002000c1c01c3d141d075030030800700381c20500c192480d8074055041130380030507020b0f14400d82c00c48112402c001c0f05400e080e010500c05107981000d50040c0c40401001c1211114141c0d819011078014002140081040e120780707010b0851503102e104452008035103010380c0b80c86003004001319018104101c608420300070054035039121046046020301c020544103000305110b40c104410322401c61065a15244001e45402015086200100c0c686480800d01d6020400200400102c0240031402006480419038800e0355080e42d40300c1841c060340e11805100102d0b20745d03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 954756258 1250 954755008 954755027
    0xa0212030408160f020405061e0d150c090303020c031b010309060605060309010212101208070311060106050705060f010b1801030905030a0f02120306090a0b01120f0c201b01 76
    0x30f82c40243c031905400c044a200460440030b9100380c1c03802001c20200d141000c20090b800009034008802100304d4030800c030440c40b08a81c19100e4a5034072107015110045403081c50100d0141e44c9400b10f40c1415400e00034508a014201c40c0d02940c00409c0660040c0d00d0307061000d81640007443c020503501c401d480c120000d0300c565845650400804001d100c40303560190043d2015140501040310982e85000800543c25482c0c03290b01000b100a201c0a0040f82d240300081260a02a003000a812419458074924103542680501e00150380450b041007001014811250000d62058011400d0350401715218040c0c80b58005149483e8000249407185900a41001508030340060640e1f444040410026140d010081c4600005000d40700700042c0e00d51119050301d004120241100e009596982c0c281001001e0500317401d41803100800110b03168121034010450100720040c00800c00145142001c1d110804c22030522900c0e40c035025920701c4c00c280c0007600200c6042c0001d49030360103101e1480103841c01c085 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 954757508 1250 954756258 954756277
    0x70c050309060a030e123417040f08210a0f1209020d140105010609032a0e250221180901030f0c06030b0f01080405031605060a0c050a0212030408 64
    0x45082051840c0f400d400a00150a62000c901803c1d02c49500e1080c0415100002000c0f03101c1d161f0982404111280101c01041c142000e00b41d103481d03141c483c3c82c40e110415603c44a015400000e0080d00200361020000790680740a04a0b4203004101c8030140907000401108401c01110145032241010300741c01100110782c002d85113031800032490610f1034a41c10710392503589030f5600300b00c000280c030703482207000c4001c07a500a00324a10700f00c8920141e556118030030848080400504d1000301e24440389003081c1d03006a0001070111542000c04000800040082140310b0564000c600d602c0c91b440c1c144800300440320b8500d0005996038109185c001e000ba070559004e9a00002c0c240008400c0114009408816501840c0c2c111500f0b07556010480076145814070740ea40044210241508550050a0721078003c1c0c410000d907410550701c0d6403044911b00000b5001e4600341e1142080c01041030081c4120306600c110b41c80d20070300d401110000a0744c5c4002850642c1c1d541c90001001070700b8081c400c1c054804500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 954758758 1250 954757508 954757513
    0x913020108040323030103020a050f0a0306230f07031a0319060f02130e010803090f0d02030129041d030318100f0606170402030709021c06030f0b070c050309060a030e 73
    0x82c004c25500708a4000740001c0703002c0d0000c4035001c00c04c1d140c81c000c0f6803142d0300028110ba461030f003142c2c0e4140103030141a00d602611001080c0d80042e156049482c00d1103a00d003408085290710340b0600c0201641e8030203900100010718903100843d503450100d590f490010745c40c59108566005803400600414a954121102c54030206820401d0240f032032880d400c9448044c3c00001c2c41e601c460304d107900d034460304840c10b80c019040600c400060414800503010940010000030f840c450043c1001a02650741e810303c24601c1a5184919140c50580708603a04100012440001800603e040383d99901c005484481c6c400b410311140c1e074112600300b0841100d007030344680a02c5940c0303800c2c0c0080c02070812030081d0804208504010f824080d0710503881c6100c1c0c0c0e00103005080042c070703000c0341c2c4001751f120b0034034855030490091440c000030303400780103440c000c43c4150100340d4801d8990502d0034291901402c1c48040000d0308400344041007001043d03d200c00700c11641e443d99014161010780c02410f10400501150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 954760008 1250 954758758 954758807
    0x607050f1e0c070602011e0c03020d1e060b0c030306011815021c020303060d0318030206070b040203010c0809031e19021b0a0501020703060207030c050a0f0201030b09130201080403 79
    0x101510340648001801402120f40c510740b122070507801ea03614481c25848400750a08a42c04100f00b6070484240c0c550a428010300d000c0c1032000d400b098400d070f0641440e5004103211041120205481500001c2400080131404c00b080300604a449100c0504810704000b4500c04025680304007580d641c00500301c1f421150204e00c50010042c2d1149514035440c8004900245404c954a00100403a4402c92000f050403000d44030503541500d6200203480802c4000b003c4200100c0142c40d01d000420303805014082503041842c0a10405003900c1400241c00c00f0807003204140042c0e807000005039903400c0015041107201d02d102481c600088c0c0220303024401044800c1a052802d1600841c12540515046070203d80158151080c0304400300140701d683d00580c000c1100b0004142990b0140421511910384840c0c000182d8480515140c81a00151a9800c0880d420401c6680500c6550101c40301031340c010f05c040c6000d106001264041040280c140810100003c040500c6081110444803050300209600c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 954761258 1250 954760008 954760057
    0x4030f0206040f150318050607032c010b030c03011107061a040504060e07050f030709050606190f092420030c1612050304050607030903020a0b09011b050607050f 71
    0x6042c10720005202080c078000407000c01800c80d52046d030300150804010007480e11035200440040551940110407501140701c03c60303610720071110400812000e007001048220b41e40341003500300031031b41d80282e100303a1502d02281c1135904210300791341e0090f81208000070100d48485581d02c850312180c01c0564017a01d00010441080707880e90140b4038031a0404201e03071040391035030140490442a0001140d240e80140380822440300e01d900141e07440a40680814148001e04902c603800504a449200118602c1a40ca00940b42c1c032000a00003450070282880b488141d108032a6281040502840204500c082d0703000440c08800240c02c5c081b6080d202260303038400c008448951034000c1c2e4072401c5811507400710001010603d080e41d003110203030404095403a007847d100821895a200311b43c12814043c103240c0010240c2d40e120404002065201d00781c0e5550001400014007a0074040c442c0322441e05800d801e180407420000301c03035920617207074140540e40350008021102e050040f010f1400c101c8504142c520f29 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 954762508 1250 954761258 954761279
    0x804120c090f0c08151507080a1b170307030b0a09052e060806030f03040602010506270a020f0405131b020607020a030e06070501050a0605030f030a0504030f0206040f 73
    0x407990010703030800164441003030303210603103407040f4010f0300081005002c14440c80c0c030710708100701c1c2d103900030140c80c40c0d00b2081c40d42c08003507005803030705032001c50011a64400c020381100c0781017030b0f03010356044510380c1041a40d40d02045101010200c100c1c4580800081c0c00580245e00a104842009050068060303440041401811003185c3c601c03a03141240612003030606d440748020f60350300d03d07848a60705854100a07040310b10040041004c0e900d8030074040c1281200b1410b000800c050000c031b81c0086104d00c0c0c401e0a1001140120700190700b10300ca00c0e160b150301d0300d03034042519800925005016a131040041ea19510310f010f5604080d034081d06003050549400b001c0e40c0106c26256221040d05060402d6010a9840311411035850015030448060303c4002407150211800c8520f004003918181103403919203900711042107d07420002c0b80d0f00d02060120f03140c200720802085001900940c94070000550080060003140300041208107446c04c0c1d0411541c8038015240580102641414407640d911040c01 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 954763758 1250 954762508 954762533
    0x5010c150f0605042a0504060818210301080c0d12081017010911040203011a09150a0315170c01030b030304050405070f09050901120803060307171f0e0712080412 71
    0x10111114145c414021030143c0140d0702203900680310442690b0b1504252000840c8020b01c1003c180603600e1900f29a60310f400500c00a401d007c1e802d940c882d810200c200340390000d01c04202e481031a03580303185400140140010628945c042c0f0704024a07403503103242200f560026800c035070395180f003850144042640550200b5080e0380a030081c1c840703265100081c4801c03840280109810100112151421103031503400405001c02d000d01003640034180d1603100d4850750885507001c0c00098481c854015208000307581c003c0a003800000c3d0b43e821380214840d180d0f6a0b80c451810701d0506403501ea60351402c1c0d4017407080c1c80090002800c180700c64500b01034010110070605030b11002244003120301090604207602402e0689045013400c00c0300c460580c44100060300004c204030742c5031140c1400800d51401540c10400011521002440e04501032410040d020355107501300581d59251101c51200501c00003112401c90720095014450314546007040c040c02c0c030580c0c00c1440c480007035030426000c1001104484 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 954765008 1250 954763758 954763811
    0x513021c020406050702060c03070218090d02010b090601030b2202090109120c060c0213090605011401030b0a1205070b0c0303060109060309020a1707031a040c05010c150f060504 78
    0x490245200c1502842280500e01401c000260140004c80040c28030034010309910800344c086a007032201680c00030302e007586182000309008403420107001c0160410840c2048100d050b0000384620015040420001d94008168a04260f150001c0005a4071605207071009400705071030a0400021a141e05006580001000e50000342074440010300c882c540310710b500e070860b402901440014601941156aa0300040e41a640440c203d40d007511204483d00c40c00640b24880c02002c0307031540c50b10030010100038030404050305042c1031513107000d5140d0b990310300101600e415903103049024146041003407800a054200d00030801000503540301c6a40300001070341c401d050036612104050f4481c0c00c11400d0710070000000390401c2c0414010302c4210800303850007495182000441c0c11443c1d59844481081e0b5121816050511800080c00180f100000005000e004282043c400c9000d10b42c1d60340d0802050010723040122966100b42150390a41a00003000800c4010800e000408800000c40c51141598441 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 954766258 1250 954765008 954765037
    0x30a020904240b040e04080d18030801050307090e0a0f0318090e211b0c0a06120b1009060c02010c1a060123040b16050109082d03060d020a051302 64
    0xc3c043e0303c00d0049905944003429104429216070390340703007065000071480282550310380c0c0b0142e070140b4003c106506514003d58848040e54506401d250034003803d038000791145420300328242000f0900243c0c411815901020084c0d200003507040c1100c04d00110080107104000150001840600513040030f41c5c507200c8001134608036908008040e0440006440c525400c840c113002d6400100c5101018071408280e445c03d0311210001070001500110081d0003040c0881c40000307110f403005640384110703c064401615104000d00e000f0f80c0140c60b0f0a030510900082080501c0707844116441400d00318003071780e07200d80110140c032800ca03840d10a07a402150b1141c00030301d0b11608840c2d42a40c45811485400200d595549441d0804540540991140b0b4070050b03c3c0c0303010380f60440001c8092244c40b101d980901c0c8540d488001c040314030500c8150b010300704029041c14040300005000c100007200d800540488000020000d2440800c0ea01d0115502c0380e80d00c080a000c3c2045200c51540092002c003506d2940e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 954767508 1250 954766258 954766331
    0xd0b250302090f1c06052404060302010206011509050a03300f14040f080105190225050a0b16030c080903040e0907080a030f030f1a06030a020904 64
    0x1085040380030316070790355034044030001c9102e50394102900060502c1d91100c1d104044013100d84c4501040d50001c1d1190591a145e039149100030701c1514554a85507101200d00703005007451500005e540381c1049c0650030024581000006810f4020300c00140280006800811210ba880c207042514010001100003543c003423801d0b40c0440250940c1c04ca42c110039603100c00e0b000e018040800c440403101001188030000b01040080b1300c016214490100a285002c004203031490300da12920042120390394240b4285005118101c0c0b020501c008203800346009203401c030702e10541810003524010394680302900e91410507007401200d0000390040164403520780c40a001c00030008030200d40c2040c04462104c10b41d0000e101c18014804401d0300c0c942c000f0a100c00f01c8854640303501c0200d00700403040400702c004c640d803900e11100e041c0d014000c081003410038030400c101c0350440c50bc140354801c6074500c04078401c5c000040040d00c01d100319170556070031b82c2c4094001c01c4000c105900c804001c000001e521071039808501c8 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 954768758 1250 954767508 954767581
    0x70b040303080112050717031b0c010f051201061b0206070308011a04030809040e0a0506010602060f0f0105221b09081507022a100f0807050301120b04020d0b 69
    0x10003114070680e10000070020303070380361400000c4855216a41c1c41941d00003004050b50051502714000784030f1090401412942010074000341c02c400380391185200b400018006800d10142900025045900600301800100800c1c9510b0140705151800203601c003102140790428903600101160584030501c400321b03075160910940c4080c90140d8403008010440820415519082c5030300400408000b00bc12205881e940da5115828a0401d0b0480707001a4030038010001c00c041000c003d02d8220300b40025000c002d50501000c50401ea00740241d5400c1c008000041c07001d0010258030016500c46a4620610360009160300203040d40994810043d070791203031512010010325482c008901503402130300284020350200388094003a00404c0c5400c0300e40d101d010700c0d04156403141020004c690b4280c0d40c5c2d00400c083c2088000d44031100203041e1404000c1c0c180010f02c4107222541513184c4079504041c00310b01695a034030018a441d040e641004000c00300081c180000030303c4402111000a0711100251004040704 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 954770008 1250 954768758 954768779
    0x60203070f0e011b0305090613180b040c0f11070b041205120c03071e0c0914070206070e0409240e07080c0906040902060c011b0912120807020708070b0403030801 71
    0x307550304104c21012a00000009000da4014520000060701c2c2d64140103040b40001c0e0741c81d00c103a01521800071034203040d03201096244125041c021088074100031110366003800130000001c03010b10b0320a001030740103605404201004040001c044141c810f56660b0344842601d410340a040c1d104607028800e680400c6c00030210754007500d0761890345400850500007103031544c140d86603a84802d00320803e000a017520200e00e504d0b814101070030000401040c003000c4041c2c610801c8000512000440d085036052196a5a0104032070740400c1c0e0499001c03904405078200006660400450740390030074411076a400a540480d00080e40694140081d955400d0782e43c8203c94543c085c2c0a02d05910628150001c4d1a9180c242e01610405001500c07141c200720340c0803200b42c02c69074040f1184450030700c80d0a4071007c45610007070503405030116401100411149540741d111200841c0544010b01a0b080001041c0c00c0c42086124000c1104001b201c0b0b1443d600c15900406034841e02040d40058009400481e242c1200d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 954771258 1250 954770008 954770027
    0x809220b0117090309010f09030503040602061803070203070e060120071e08060a020a1e08011802120606210f010303030c0504050303090d080405060d020325120b0607060203070f0e01 80
    0x5102540c036084145c4011268150300c20700b068240009158040081181000a8800b410740c030703001050b082c2400b407030b0f280f00800d1014281015030703c108903080058030042545c00441e0140b0807414950b0701d507800180c60365210020001000e40c02c04103841e94240c4001080c2d0115442c011054983d03583d0440310303900c1000300740150801c40d403000f0041022404154001c00e00c16516190031074030b40c2065820304115100e015246800034007520018850100c220b00040d040c81c3d500300c800c40c03900d00015602103d0901c0141590b10803040400c1100003000d44030a208441d242c222000aa28600035091030502402030205074002860858088400303400380c0c080b9000d070b4400400541c148032400f01008012048504102c552510a03c00043c8a4542c1409020303034510382c7c0d001580780c2c50280d501138618801011b0301003000704d2001c0607807000c0750004052844000c1103440806c60018080114040303100d01d603002031045100004007c02c031584200a880510481c0e0340342891038205100440d5003100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 954772508 1250 954771258 954771271
    0x5011e0212010e0604020f0c0105151f05070507030b0f040b0a050112080c120406020109060506030c0d1407030b07080103120c08270d0c0807060503130809220b0117 72
    0x800401440a2000082d4060740400c00501c054035080007c0720f80700c1030790421101c0c100d01c0da4699042c4186030f01d0003120804040701c2500c040c6d00d280d400d5140c80e08182d451903d00c0d000e01400080b46800c2c842c0c2030000030080c0da0025010343e43d90402520004502c20112000d4070341d802c03c2c00104201f54694041e250484030b55120300a4006429190303940315500480c0030358218499602c0042d41d1100f100c0c043e01c01015207030000154540313a81400e0080e100300900961003600540e050b01659a16040303500c400681214000548a0101000528240c550340014140313421030020810010f610000c0d440c140d0744204440c0300a0240d241d800d503030340c9101c0c2c400200028801d102c0c1071488800700006085681042400d569410184004101100c14080040c0d841d60400038080c4882101000090010301c1c0174545107145191803181e07511540a2810014051400001c080000f6038520345220a0a40005080442c100c80e040d5400001c040315a0800d010503611418440e802081c1001d0912860 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 954773758 1250 954772508 954772537
    0x50606040512010b09070f0f0513060f12050a2c0d0e0a0b0705161a04060507060f0f15050103020708120405070e04060203060a2103032705011e02 64
    0x40c1804100600900c0c444602c0300c05669890011041c0c2e5141109503014468036240c0f8080046d047c8030040c4012000b111142c00d00200b0000d041e900c481200004c4d040ba0704620341a040c89250341c0003180c00d8040c070313480c40c05e0700303030502003070190518103640018820b44c10090036009090608622140051100d00da00d021500481181c3c43c045005048040f201030004011b42d2900e0340391510304031590840b08043d2102d42c003080c03c3c06003c01c079240118000d8194550420341c04c0348000080c04882c46540a00317802c002c0080784030802c12455420814550500b10014010983e086400b0401001003895203e081106410000f0f80c650007072007101c0300b241d003105c079240c6409110041c008110300003600407903980c881c0710300c0094082c004a1b507450185218030302c0075a0341d0400100300120501141c0001ca900742c2c00864900c4400e40c900c8115004940c1030401180c000c0a68400700e401c00d590003012003408031b0070003940c4100001903000c40404e415400b1800f071040041006003049009804000c1d0926 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 954775008 1250 954773758 954773767
    0xa030206090112111206030708010506060f0705120304030c150c051608040b2d0406090e070309050706022401030f0b13050304091a0904120f0e03031615050606 70
    0x7540300f03681c05201d1403007008002c110103016009101c69603004451000c00c513440c410501400d8502449818010b0461100920140c180780000580c144504402000c1c4001d00081c0c000400005110046520118009071500c9140c0340c01d008d03000a003c1032003180c4440c000b8004004010b214400c801b641c9800c1da40381400c113040854007800709010002c0c2961400820b000000389580001c0c0100f01a6000614601900048101b211862070a6100c02055004140b1062026641c8116080102c401c0400c0c0c4a1080e162000d095006200786080a4001d01400b400880c1c103030b4001032039900d0311a0a1201c028248804180c05486100070b02008003a40107002c110804104004034403070f004030380f040001c242d12006540e414030310348c000d07805210308648800b010456801f6550b0042d0004406a4100321180b500d9510440000706124000c001e00480011400c139080c0b14800c0350340000d501034100c0e6990802000e95007402902514100c940e0444909440b1403180c1e42d000c0d0714004e0714050a9603050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 954776258 1250 954775008 954775027
    0xf0f020c040908070b040305040509240402032d0118061206051e100e07180e151e0f120a03030b0625110d1a0603030f030c040807050a030206 62
    0x60300401e0b41c00e80d048081803004c14082441410214026403003501c4455a591404090040c8444020b0180c100c2110504c0e55403104010101c251410300400c40d00103a40780e41f0403400024803140181c0010195050802c9251540e00c20b0100c507069a80c410104000d0b105c1e924442c40503030b005401209030b8003090780884000030707046420594200019581c4010803201c1200c2817100c044085035150004d40d1b5410b0100680004402c101d5000242c41c070f009108041010100039488250780702d50440204040009203d4003040080280180801400e48402c207000da03c4004031014038050603842007080c00c0803420203107031114070070300d02d11030540244c9040d80580d1019002400c503880280d070001800c0000d44000ba0120040d202900c103005403010346c6400d80e052003070b803100f2000d040740c0c02804000200c4010400003004007107090090601c00e01c0c0c0e0b81d40c5601090460065960802c40c0b1407010043c00502d10690018000b520005412100da003030b65030040013541d4220344006504210108119200e = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 954777508 1250 954776258 954776261
    0x7080a0b0d02040c170a06030c151709010f0207060506040c111e030d0c050a03060f120f060e0a0506010e070201110f0d0905060a0b01031505220b030a0b06010f0f020c04 74
    0x4103000c940c01d141c0649140c101c0110b844480850300032140c2d6a487e0000d00410003002a00d4000d0224040030401140c61b0f040040c05000300b840031a465000080000740d040385003500440041001c0030400c3d91034141a1401002415060317a09a1050341001f0506d01354900c11200d0181e801107103002041c1c801300e940801c09189030041011503003400b0400100300349080d5030080d44041070845e56507a5a8050802c002401c45100b9003000b964089903402c20040720400d90800350510790000320022504441c0d24210009000c148441413040c014021048144040440c0603030480314080408800c0341c0d0f030101c0c224201e42c41d2080b40d542111080c44981e2118801742c003d00003550b41d141d070000721003415031a45490102e007140e82680d01500c43d1000566940e05005d2082c2c1d0800c440604083e6900b0705000032250458060844440041e203040001d820006e60060702c88058080c083c1c1d050303080141403a100301581220314601180b11110180f0354184195404000320105038040c180c443c8240b0704100 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 954778758 1250 954777508 954777521
    0x20a020105210f15191701020409110a140909040f03020c040e0609010b01020f100b0d0c0b0703030b03150f1f1814090606010c1a0f07080a0b0d0204 65
    0x4a10003410481140d29000c00b41c46001c0c1c0c540d1500c035481883c04034000300510070034054070b07805141030080c581c22038042101d0034030607691400001652513281000c602c2c02405203601c089002e9080c5000d2240c184d01c0a0024248444290b4900600d000794840001991140b800201d030040c8070702c400100400c0e62035450040f030b41d1091050303031094046000050140c0d0140e18001c1000d0b04200c0600c40418024840cbd0608801d003030000d81030450700306408649402200c40300d1900c15855002898817070b544c0708004014540c0c07000f00390400c1911400211110b8104100803000b091030005c0c00d5005180c0000d400e41e41c202001035604d02540d481c1c005c2c8041032000350501c4c9200180c0c26940d4510144400a90041c010721000811a0b0840382112801c0c0d0341440d50480c4030308142ca09000e541080415421752041c801c3c2808003240f11070f0300e804a4603514483c0040121500f25041c8441500d8801e1500d01034145a0780360003154035418190811541807842c0254003444148844005040607000302 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 954780008 1250 954778758 954778777
    0xb010503211308010f1b020f1e011104140f060f1803160905100f08070603020310030f0b040b0903040501020a15140906070315120206360307080d020a020105 69
    0x90341d15503d4102c1130960340304031040c0c0241e540f40c040048100d110b82641d420280c10a02c000e1400c50b1038117003059140d411120802d5803208000c1e03100900b10740c2c00d4100d64014031600c210305580356698110101c4208040200510a00070505180b00030b24114080e900200c100d45042e43c0b41041180427624040c1c0c00a8000340c1600985490003460244a03400d0b0300244401900030949143c42698000308031041e40010020002c0c1d064284500d020009005064a03124140141e036500c0707520400889450b16800100300c1c00b0b00e4090401040050340d6543d000305e20917000b0740d500d034440940544c0c403406507001d801d00503413004884030007242c2d40c400840040c0e044014001102000c0c05000340c44207400310f880e03560f20b40c401c5050041d080d44c0b501c01d002021180c0d00c4a050300c41d00b040140c020f15598000080c0c4a0600810382e00c1c0d0000d0034030350000a01c6400e00742d00e01414409619800c01102c0412203d200e8086c10f81c0001b070041c004980700e1016a21540a803000d07045136030054480d90060303c10b0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 954781258 1250 954780008 954780037
    0x81602010309080f04030c08010c050901180302221505130c05090d080304030206090601030203060408280e040b091306180b090a0c1401021005090f06040804030b01050321 75
    0xc0c1d00108110100501301d518001a01c5a0350750b0440c20800d82c05000d950212070540e01d081000401c040e802000e440c2140400d1034420f1880c101d9043c0401c2c0e0018075040a5031108110f00b40c100e102c1c11644d008480c005008405010410200029548064461150701e410407004600192070004070f5000740341d460085c4c1005401c2250f9940422103064120f079080300c41540c0041032106050701003005a034810085401080c6543c1941d01094071420003600050018001250f02e500c0841e2a001c500c0c003850382e2006100d0850300840000301181039001000b805185448600c9030341c2d08044160314415298400e00500102050f0703145802000800d4542952000c0124020001929021128040d8582e0b40003418008000c1c1007032003805243c1e42c0030364440d04c1002000b405691f0003081030258024403440c0050150340d00314441d410007130001c000701101d014407000c103c02c11140710007900589024200d81d480580c0ca4205155580c1031010300b51202500307410f480f45100d604140140a4050880ca1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 954782508 1250 954781258 954781271
    0x309090e010e01060b04140909030d020a0309060c020106051003020c0c0603060f030d0e010305010e0610081801090b0406060e010602070308180d0605040215030618130f0f03020d0c0816020103 84
    0x8030900b10380440d0488850020700150401000c0002c0b60010b513856801c072803252403800c9c00c44c407050742c80c482c40b49a43c0c0b0042d000f040c0a13610368001d078030100419422000030b10070002d021100074000c10701d41c01001c0c0f2540c03003203501d205454820300c01e41d150049140d006003100d607045d00400810b500700404d03040d8415032003010f488081e102844601d400700c00b96161040341c0b13040c0000140039a00140c00c1448042c40d40c3c400c102036a91940c20440180d45c09040c60741c4141c84140d078a440d9402d4044080005609000e40300e0100140c866000c0e00c80c07802841c04100340e64a40401d1502e440086c0308a0300140e00104061010580346001070004401c10501c0071040d802d2070010034a100d41a1206440103503a4004000a50400d510010780511018030041d1840c60703ca400180030740c81c01d0040400515002d8001000102c1901d00c0c519081d800c0a51103a48104900c0c0080704880e031060128018040d40a0300590300f80504020359801d07603c00b044504241c9000c110315a40502c036001681010f44444 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 954783758 1250 954782508 954782531
    0x10c0212120403031d0411070f0611030c071a011d1806070305040218041509020609040f0e070f031a04110a0329100506090d06050c1e070309090e01 65
    0x5200840c405e03142d050150820800c101d1055035543c1a05014900b1302c3c00c2c06014001c030800b12507010341d2048091018041a040c008018001000e000305030042c0001446411490b803c0580155881030451600d520300814002100c00d00070310070072640c42481e100c82601d0303a030a100b200b41d000b411481c1c5410b9404130641024070300981941c0a0300826078800500065080c80103400410b10f11044200003542025500c000c50501c0c0c030001c6100e826501c80e044400c551740c0404480342c1541c0108103104590354504101e004091090a82889102d850300c00560324001c040e240085a810072041032204660701104040248000c1c42114131f00340c215010005075507410501b90186d4041d4201800c0790020782262018143e00c2c49809031480010000c1200c026a2803185200340d550540740c00742c5502e61800869440d100c0e01c003006120310709020800c10140e001c50080c043c0402c110250160340140480036481612072807001034001003076954184900980380e00600c04e001044000040c5201c02e15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 954785008 1250 954783758 954783793
    0x30f030c07061803093309030203010504061a0907090b070c1518090b06030414010e1f0605011b12110f0a0506180312040507032a0602010506010c0212 66
    0x10720040700b9441443c150605030300800c2d41e070150181114403c40294040540343c100b2641c0f2032041030b0019210901e844252013500e5032401564060028440c9080515020000e00000d111003102c2c100e0500c101c402e00d20303190742e090303021301c00a40f2481c4200b03040c1588a89103902000e0261490810764500140c4414825080302c0001500e603220003184000e064012242c02080c1c0c441400b241c00d101d0715514981da5030003200e0304031341e010a6960241c44031150039070240101d1a0988840d0040c16510740c80925800203200b10801028820000329071600019a001d5041641800f1349200401c000d000144440c1c0f42400c64980c5130822002c811a8081e141c3d107016111001e0f0106a000f0300c286400b040020807240f508000184400281681d42611880d50b90152821300121074001d017020500307001d0280807010155070411030000c1040c148000b4002c01d48140440403e0501041000090b82ca2040c86074034064030f0140d40f00c4004842540812081e004525510319642c0201074400490700c644 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 954786258 1250 954785008 954785021
    0xd0f17040608090d05180f0a09142a030c181c020f100c08070c080703080a08090c061c0f230108060f0f070c2004060f0305030f030c0706 60
    0x90ba501c4034507601d421146642041005459001440014441d1340031050a03007058030640344050310410203802d08074001401140d010340c422804a8502280b0b240e91444140e6400c1c0300d0911860441004020900711084843c40700002403820391060011541c003201180082904c08810303403101c00203141c00000620007280540189840c018071001800031401c100114905000d003c4880811014042c680a8090b00c0a02c0700204443e2000414600300144030700b2007005060701c1000c0351482c40d202e20740742505a1151843c03c001c00c001d00d0000f151480c0000c1c00103900003002c0c190908000107022045844510000c00342c1e40e1540b12011180c4941d031520401e01c0000c40742080b482c010710504a04807508206800c0460701c0d4101c60100102c00000480c0c20b03030460810407090086990345041160364024000c070050038115100045080040011030b100a40041110704000c4150b031420707001d0a482c0380d40320084c055001072000041c19014000610f03030182d00c840205190841660782c403000c8890 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 954787508 1250 954786258 954786269
    0x9073b06010e10231303060b063a0b012012130914040f022403040501060303020c040c0c0803070c02060c0105010603050f090c090405070f0e010e060f0d0f1704 70
    0x4c40a0090603840b00e03001c1d410914801d03c209035450700f8040000444e041603103000260596494540003041c07030b1600d0085400f210f90804940802d003259030a4004001c00303d60f030882142803000760458242c0c1040c03050a5a050703058441621000d4a040b50010703c160442c501020b50050303603000001400d109000b400c4c8038800307040800229040c10300c0d81e001c80b941e0568101a405130181000300043c0c22800082c1042c0e01190520540c0c1c140d80316609130480c0c1c80c000109144404028042040b405400100503a44030b9000c1d1409000d041c02440100e800900400c00050b160703040d20000b050b03a01004540103a0f40385130a000107941c540215807168840321440305660365440040221507410320900350804008450280c4500342442010764441741034828512541120010404002c803c0020100604640810500a07590760081d4000b1800034854001101d01c13140010b1038a01d0990111502c006005010389440481a2904014004405012581c1d442c8048180380d4190459024000418 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 954788758 1250 954787508 954787517
    0xb04020a0f0602061603051b13030c1202030d0806010c020d1a0108031804051b0a0c02090c2205030d110304091503051e0606041107080309073b06010e10 67
    0x178a030340b0400400c515115403008041c41d26003403241c50070b61000d130b802c42e001c034661031551074a15003420500c0c0c5841540c030040550b102c0e010009154140c40d15141d04080c0218180c0b40034020015043d6144a0b04032101c0780018000d01c905030051815044030010b41d4001c8260245101265811641111080e000303068507a02c0803856800e41d1003040402c100080c415a4140458107000e0b2061007546000119100300800105000c108980308100412025400500d02d8003141482d419104059101c071002540740320510850390420660005070000322000a00104140c0c04a01e1046030005800c0300488803030b0100f0072001031240307032600031070311105043d1070602203562551404505c0c0c801840c414890b0080c100740c241d5846600816850341c4008207860100f86450f03c81e5218800d8496114000c0400e003011090012640000032010f094030350102034040c00311542e80c5800c52020000740400b160300c610003000e41d0080c0c2400100c1d40c00800604140c0c1310303801c025000132041041410303c00d0018 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 954790008 1250 954788758 954788761
    0x1006022e1812050406092d0306020405041d030f09150a090e150f0603220b090d0503160f0905062b420306021809010e040b04020a0f060206 61
    0x3400700000d40b5024142480780c5018580380c40500380742002d115074508041d0401c000401c01110808065543c0350541c110302d000b9840b49850b100a4205000b00380c055032a1016078100300110500c04104450814010350030f00400801c9091603600060a650b00440342c001e07400c03a18403030100a0000e403821615144d5107070b82015011000d03400000e2840851107040500c007412922009500c048070341c4255011985c1e40c2e22814848090f0384503030610380202030802c1072501407085a2501c81d005410007015030300d4103150400211544d000c01d5550103100f8110b40008882140070740c1d1340300003500446c1001c01003103a4510001b18280c100541d254028104101c62500c29620071000350901fa0707140f034041000c04a000405100203502010610a40c0d41c0600707003140c600e840b61070ba2400c203201d1105a000940d1649800300117900414070149012980c0c1d810000300d03280005020703042e80c5007000140e00940c2c0e030b622400401d10380940180e810901e01a40030605144030001b13400940302a40090585 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 954791258 1250 954790008 954790013
    0x6030405010e061513091103030a020708010c0e130506040b0603161404080d2f101103010e04240c1d030102040b03060d14010f050f1006022e18 63
    0x10484020040ca5003e580002550380b00e558614500701041452000003480300c009141c47c0f5a4062488412031f8584000b01d0091800c5900085003819588000024410216880020341e0f90583d00c00400e03610107603800558078001e000760301456010b1001800400d00c406080702003840796100341c1c1d280021300c81d8070b0b5070005102d4100e030b00c0f0b00350018072002152400345003c13203654032804400b4240e010070050050f0042c00c01c07003404114184003914454440400040d22600d030741c804c030b201a01ea80c03407800c02d03074104405008002035038104c5000150102060b982c50f940d0b602c0003500b1900c0f81030100030142e45000309209038454460100e005494458542029400f102801800d03645040c2c86a801000280424049041a00e420210944e030f0450034102518101c0945000141490303003a601e84040d0107170642868208900400c006000c100c0d6075164094851300c004150b029500150348408290544000610b58400781071110510f2103540900066103002540e0b00c4070b111181d0420804214400d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 954792508 1250 954791258 954791263
    0x61e030112060e0f19031107060c0c0f0b04050111031210050f0d11040c020a051f0f0b010e0f010c1502180102150712090605070306031709131a06030405010e 69
    0x3a01e607007400003400341c4030614040b03070b503951805c1c1c40d1840020345509110042500a01d4203900041c0c0da14142c402c141c1c1c075901e0040440456000c255000d099240002840d40c3d038410702281510800059a407410307003400d005596081001c2040c092031704c0208004030301d07041c10710f4a0309d000b07040c6105052001440e1030108119003691500041c401e413209000207000071141c00b075951800c11305880200c0d0490418a0030b0b410081d211902911a0003803078282c00c12201a208404c0b8440e456030b000f0094103450f040c0541c206e5507880c003160b01142d102e0700c00701524034120a0a4014204c1498074211401080e95a1000e02e4901c125610803a0780204980329400100402c000c0142001e10007842421301c002d046210680b0064541010701060001070a41030100d50040c851b600d820101c140418140000024010701440c48151000780c6004001c4c440d0200d00b408480170444024032a1400e29905041c0d00000e02140c0e40603500c0c4104c2e0587e04400761915000345101314014400011340003100b604e01d50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 954793758 1250 954792508 954792521
    0x307050415020c030c0307061d12120c1203070f27030506010315020712030209030a140a020a08011505010809010e07030308191509021b010e07050118080606061e03011206 75
    0x51007030301f20000901000ba400408842c0360718a820b4800c210780c840c403010404c1000ea041103034009000e0440f05903200d146002c0284100402c040840d0700e90100455584881d000641c3d80c0000140d50301c60301c804283c4150781c407041900050312081c0d120188105c00e0010b0b6841503000703c8460300f220004100f44005a1040d011030000031000350b00e003040c20350340c43c6088266144c0c513206043c1d002c60411080c0c0c500300102c4040f19440300348000c010381240d10142d0354207408c6108a00c9a88100d5000c90b16260602903800c800d00022416039183e07007001e00540300744500401840d159962066000c134411800c10100000314002e4880c508c0c030b03013440380300c002c411207549441d0281d00d0709215105005000c1d084185040320020540103855480d0020111180d1101c55443c074000e40c2010b080301d0541c80003085600454409803500309400002600c0e000300894a44541417658120380009800350400000400300e40742c0341031401d10080e10201c11406d868000b83c00035090440e101910741c08001b003510815 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 954795008 1250 954793758 954793783
    0xf061c0e060c071704030605040f26180d0803040b10060c050d0f050705010908091216031b08150610080631061e1a0f0307050415020c03 60
    0x208080e1502e8450800103202e0300e0b6009080d0852884404e40c2d0324044000d44000e190300580c140071900309806c015442401c840743c02c1e110030700038600040307464925450359440d240900b800103043c0148079a40807a1091014011500900c400c0011000108010000c6104070300c00c1c542403285060007a60b41001461f541c000200740b1821040407400300d0700c0001d102c481450185072404440b52400380c00c0300e4034001d10f08024039940c01c00c103100b4200100c60327001c0d0881d01401e0b160010707100320b200d2089030703070300c0f0702504848030040d0b440360920224117407568201c07024680030030101c0259540c007120b0346480c1d50305600c18203500308001030000c1803820080d00740c40c1345490325007103146040410025013118103001210740c444640c681040f211203840c00c8148011500c1c2c031001c12103190307035607041c544066454000d401101c1d0408000f160384003156100d81c005200c20000d650170840a845015840da0001d480c42082c42018000000d030010054551030150300242c0c050701140d490002414645498010703503 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 954796258 1250 954795008 954795013
    0x1e1a09120313150203030408180303120702010c050f04030b060d0b070306150c1515090c02150f071707030603020a031505070e030a020112020c030406110c040b1c020f061c0e 76
    0x41d20320313400000d0700d4000703800026495480f01d42e0080c260022260401031a0503000104054030281d5090b018244103008640003803054090801c01121148192180f80b461100140b20610101c0d4850b584941e200c107001d0203a58051029032100c05448900301c900303100003a11190b080c84064410094200303800014104600c0c0c4083da03640e10102000c0c0d000c40f01000960f0740481013540404486024028000c44c03804014410220358025181d1785004110345a1a602e040410441d0480c01d0140d8400c0303506079640018400208483d1248c16400b0300084201a19107802001603501d83d0300040045108980104440c2d17a40c070720550550780001c00480511410300c85c024607a03140494a54004d640c2440d0140f80750740c01142e42c00007801003420342c603020f202c0400e0101e0440e82010300344401d44000ca00310f03104e0781c04640c00c100544d142c0100858003c00302d481c100e03401c241688000420580300900198180700f20201040640e0410341c4e1018012034105080c8900080700d104824110380800702 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 954797508 1250 954796258 954796289
    0x5071409060d060b0112020a0e0118081207030c020301050c04090f0b1507150501121416050f130c0201051603091e050f0d0207030209011e1a09120313 66
    0x1d40700b00031412000c0c2034140c13100c1505138070740c0c440d00b80302c4400325201c042151184280340b0000e12006a810207180401d8203450344040a80d100e5007800101da2a40300240618074110402c8541134010230401c4050040c10b416100050b502805810b10407008407510548903031400d1035550580d900c0b406010351880c5401d11096aa0b29051402032000200c600040da41381202e2601135040c050744280301105600e083d00108024414031200030001c2e028280380502c212a40c015952111011700101d9000d94243c036080155060406203442d160000400004818500c295003074180d03078800c0404c00044c0d40d62801c001480002001a240300111031031304105082c020b1703540d1180401050030605035440ac960142c1c04101c01000344014040d205020740e05000c486543c065510442c40c0022032292174040000304e42c0d8078020040004040c40c1c18804003005180582c0240c94403142c2c1a041c50510080017000381070707110340c684c2500c20701c42080115a03031403d116442c0705601880c4c008900303c0e0070810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 954798758 1250 954797508 954797521
    0x18090c050f1305070c0203010e01060806060108010e0106080a0204090903180911071106091e0301050c09100e04020c01091401050903071a1f0308071b050109030809040b0a0305071409 80
    0x151030b004204400a0001c0c00344c070385000c00d56448090040007581176081030043e10420006401c44000c80c0c01200440700aa1105001900c002c4801d004d9000d24506103001002050300c070720001600300e22401001840e081e15944041c0a0b00ca90200a5021404210310054040845440a0000d011642041041c2d1000c8400340c00d10b441208009401101c8941c111191075803030004071a03108030000c000540e04400303c041d1101c4e464820144c64440c1d40781c80002098424100c0840e28145001007440c414000702c40343c10780b0180310b540030040c3c1140d82408002022802481500c1056010703008a1425088104032182501c3d03000703254415a400070b015000011b45a0703c131705140c452650840c034069645901b085d1103040700c01d0034030030220f0110302000000d01072002d0040070b62601401000c036110a1440301901c03a9200c5128040c000b8007120710800200c1e0240f00500082c16000b40301042c2c01540c000000c21040e02a0403d0300d03a500030341030401805129900d41d50750314206948003412440c186 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 954800008 1250 954798758 954798769
    0x30302060f100b1c0204052101050f01051809011b03090501270f0f08070b0402120a1101050d021b0c01020d020c0f060306061c022124010918090c050f 66
    0x410401d402e004044c014807480440b150141c17409041d000e04524012500103010140002c44039004c240705504e00008581e0010105103158143c0344050803440e58000303800c030440c1c07031004010203420aa55071340003080481c040400c021440c0300e04503a0003154406850428608684078402c46040041540003010000214043c40c1e040e03040c2c00217040000d610704da0400c0c80b940094804003c1201c1c80029040302008078416256010354000d990f1240818100e101460f5100e000100103040c241c6206156141588a00014a040d440280d009428000303004140c6481e8000c036900001a50032065280146507810460355070300c00003a1000313002400d40c1d41c001c940c2416081d805940601c100000003661925000200c0360f1091072445603280c854030959000000390407800b046400503560b00c2d54000e0380f00b412640070340240d40c0c4c104142046403562404101107a0350103109418400702500000d0a44001400c00d90403c40000021a2083c000e10780f10031405500c0d0081c910642c80516802081d8546 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 954801258 1250 954800008 954800017
    0x3071e12030203070b09030703030e010b010806132304050d02071406090616380c0c0a020a0609180219030c02011512021f08040b070c020901030302060f100b 69
    0xe0392a410048503080803070961192101c054001190750061040401d000401040c581e806580c00700114401075076103500303940003e1352050015070010017148039803030b091900f0450b075524545e00261700c919000910b00108108a203044030b4040c0c0500308402d01c40c0a020300040c2c040540b0103011017070704068400600c250300708281e5002c0c0d040402c8052040d2142000c072410340b0048817041c2040c034894500b0441140c82841c82420031802142442c802c07040c100e541703001281d00c5586140d80e5698a00741c46034980c0190f041c440c150f01c41c511071080941c0324485d28501602007070340e94403082400c00d40d90340c2010089200030048144108120811000c900c0301544d10790f000c62601281c04070017104100d0140000c011420440385d060a40083c04d50034100c0d100d08118030990354420346050001805200248a81072000404c03103450000d400039901003401b560094003410305031b2003146c09402260120800341c04c1100542c0c0030106001c8501c103000c659591103541d00e2004000b0300d09103583c0031020b004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 954802508 1250 954801258 954801269
    0x1003020403020a03030c08070605090307050f011a0909030d23010e100902031b0301090c08060f06030c0a02030f070f020f0910090f0b040908030601120b030304060e04020d0c0e03071e 80
    0x1b48107120108211000048a28264002c2005d20040c106a0340c03a98890388144001c4401d44902c00038500210018000c1e400280500000d044e2059946401d10410000080021a013408104940402056140305030301107686102c90190038803400700b451001c3c0000603080540c84003000700c10840c01111110015054a40c00e02c80542c40380c0b40d8441800801d0800c81c43c46952540101c00416400c5586d400600110801d903100480ea4407582e081c4820000520825900840204001030070300d01c01600404603540d603031045074585644c035031040c0c003540c000306002c550292500a101d01580303400c100541c40d8090444d03041481d41004000103555407028401c4000b210748410360494827030603d600c5600c0d0b00001600500c60032001d441e243c42030798412114580032491500034000280c801e84182e41ca0810080c00a600d0142491300650b408420004060352181d000c0003803e00b0343c441d07801800380d100f09540f202d8502c2c011b11000c040c1898140d40206500b54954480c81500d1907480310010120750 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 954803758 1250 954802508 954802517
    0x130605150a03020706060b0d2301140d0b0408040f080d020d180518090d0804030c0204020702300c0303070201091e0e010303090503010c03021204060f0605040f06051003020403020a0303 81
    0x540c007000c150301a000d8240081c0520703191410000e190480e0a00401184516503401c0107030b425204454000c403038800d6182403011a840300140802c02d20b01c400d644208500600d0800c20108076a146c1e4400f40003250b00301d69001d4049001c2002801901a02c03001d84620b0015244c0c003420800f0017035451100d41903860030007811100f0b9442a407104140034014010141068520f0414a010606041c10680c1d41407554031401003400813103440b03080e00c14041e5901d55a050003a401707079000c0002039007051030181d91210805185058104101c1c2d014480c5400b011003042c032460700c42c117030710341012030030703000135003c0d40040000b00d00507a17010406c1c1d41517610000c000031b010360100c1c02604400001d9000580d8643d0108004014150400300a200300c841c02c0300280059940300c107044090380203894051058042c070402040001c3c10941200080103020003001506a40d600000b40076035408042040c0030715a03940050040341003213002020008441d0409524042c99540440c011200c10b120150420 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 954805008 1250 954803758 954803767
    0x2070c06050f0a030515042301050d0b01090203070e0a0801090302071e180905030f12010506120403030c0c05010f0209011b08040509131b080c041109060d02130803070213060515 78
    0x341b0303070210300e080c03401c00350080140000c4041c0c0c11000d42c202a407113070880010030000144501d8200144d62440c0d910000303035076507039280c141710038080d42004e440c000034400411206545c40c3c5032051200c000300405030001c901c118003810060700741840d54004a00e9050007a03002250780b0250f80d20181115a42d070308000580a8411000000342414840141a40030001c1d121443c0400c03035000e055010204201102242d0b030310010041c0501c1034200c101c02e84210f80000a02080c0aa80200f00110a030308142040004565415086811880ba24401c103940442c59400d5540d01800d01e155140469200900e0070341d084c0c0312090035021b07500c61284150812000610242001c1c0409409650302110791040009112410403029103640034140d40742c40f5034801c0c90b10704e00c1e00d802580c18090580317105501d400c180c2d1080c40191b60000c80c900c0d03880e540802007044056000d4281d000101240030203140c03100d036588100100d8405507280c1804003030a00e007082c4015034840020800d00700040410303a41d00e = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 954806258 1250 954805008 954805021
    0x606060f070203120310060305010501022a310e10050601090e040c090506030c100e060c030f180316090b0d0203060a060510181208041802070c06050f0a0305 69
    0x258841c810000b5090300405140c0f4112082c03032405103005803a030210640980791603072412421a0744c00d11984e40141d12a0550081241d03080744131495065946a4450300043d803035000c20b44000260082c0d94421005110100501e071181040d40c2c1e00d80e00301c20701842100180c0600556815810a400d15207175599004500c0c00ea020f8a440e100902c0c000141000c50318003402e088061050b0341c498001035500301400224a45400f1405645032000106611440785580380c00301d901480002c7e5003038009a080140d0340e00c80a0800c0a0069903104072055691400c0d04001e158522070381180c018002d42c08104100c800d010040c0a0b00199a0004400242d20200350006541d45d91740440c0a03405028200a01181d20505d4001e4010340f5001c0d03a0040e90304800c10704c101c03100300110f28122183c1d560b1f00d0040c00303407100940040da00310b4002d01c0313a18242911480340ca070102c4006000700d40010350005004040001c040801d5004003078a00341340742041c0342c2e110150600d1050910078400c25a650300003492 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 954807508 1250 954806258 954806287
    0x9080f0a0201180804080d0804020105071407170106140a0506120a090204020c3f0d2319020a0519030905100f0635070e0c041e0602060606 61
    0x400112100140010307040da418202113960081c010803805001e55050b100710240118412405941c1c10fa5440d441c00b20b00c3c3d2120031040711149240512030103080c0d80000d440042c1701e13402c9080709002000056252038051004a081d003400c0100c0d0080054220410081d80e032035083c3d6040008080302084e07075075200c4944070020030100100030b600510118460340c80c54030028240b01c2c417440d1440e9181da002d00541030701d8002c00d141080c2110042c1ca8901c0c1d48031281d4140040d10303840c240300401007040c0714480e4a0000d00305c0207050a808203218002001101c0381c60304840d40301400014002c601d842e8440000506521803000d1032358142401f0098444294803d612024000b6040b0741035440102a000448001d0159a04134418032070603c00045101c0c0c00040040b2a0641e800049099012a107440d105214040321740d0a2214043d103480000c20340d803082072041c4240540b600c401e54441c10049240b0441c4400c034071034080c94100e00c0040c40001d4000503401d070001c204450300340d00c8200b042101075 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 954808758 1250 954807508 954807521
    0x61e0d14030d060806091c1206090e0a0302070b090906090403021504060623060304120c0f210305090c0f0d05010e0705010f110c0f04110307020a140109080f0a0201 72
    0xa00078070000914441c0608541c1c8120140c81c400300640b8140c0e12100302d440e0b43d452402400100d259448542800c00c94082c1c0c08000040d00c5013640421803584c4c3c0c00e922411202c4c4041e40070210307000040e0040800d58107208800c05862000c01403414a000c08000c03503000321000345014028090140803809050081004d14040b0a001005030030520707007440c00c00042d200d18071581d1502c440c007408920303100318a034022040c901e401910300c6081d940c071501e5034034401401d80c6003101440b074030f40b50410221b10400180d0308039178090310031030f203002d43c98401c41e10f424101560640105031901060050020010400e401d07082c0045a9500b000c0f111540014203610700c508004011350321740148031039082d001090b414202e030801d03281c0480e10303640c0c5003095a09000d0788a9900481c0c202181160207460643d00c003211000e00078000050314030801c814203001d5032007602e0940140c1e108100200c2048140c82e42002c0c8482d036a0000d200d2145207588107221405800c0c0c2d01c0503103c01c042045801d0318030035440903 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 954810008 1250 954808758 954808793
    0x20111130e0703270507052e0c020d081305090610030b01030e10060e01120b0a0f111c0e031603030509010e0118050105011a031306141806061e0d 64
    0x102900030b101310811806486040110340701d00540f03100140e10300d001c15a51051441c01c1e102e450541100c000008802c030180032002043c0400c458105000d0b031540d00090034218850203c00e59510348213208600e040c01658030143c8102d600c1002c0141c00d407a0a100c000080c4424207011800409a40c010b0700604135034086000984941851040030824a070007223011103000d010210802e9880d0b51404102c500068001b80c611400380000c1400206543e0000c0c152004480d000542001042c0c140401d503403001c242819090f0402c1500d0040980c0e0b03100300c050094005005510b031404410900400303000c4500c0240a069566000a440b0742c0c1c00e41002400c441d4520081018038003556102c100c041c141c480945031907180c0000419040c4440d03100580000382100250308599805d4180e02480c40c0301c03841100c03520b40b9107211220503280d030a44a4001c8902c40c6645445403003881c54607180c03e100800c02d9120303200800036515200c1980054420900040e10746440340303952401c00d50102d5540e0301c1c42 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 954811258 1250 954810008 954810041
    0x90b0903121903050604020f0301060809071d1f0f051e030106030507080d09120206070f0b07210207170318060c030604050601080f0c0d0b03120901020111130e0703 72
    0x2550250003010000350030b15070b0b40c1d46003002241ca40105220487c0107485a4104c0044100014400d44e07014203e044d9004620070704585100313440d2000c403480400c42d808541010781c50603080c000b89044d03000300c2103001d2800c1d0603407000300d902e0509903003c1e50319540300c0c56000b4070b00c059240390615080c0c004403001c0070001d4028800300f5568500550b8a214912030b401035030044601e514100e510450055088070019031045004c021113800f00700080c1e2101208035915803401d542c110002d2085039260744540c01a0311801c1401314861401c9400341d80d5009500c003d284108070140c00241c1a18210100c0c490320004180c89a4a16000845113001070703515400da407081000b0001c1461640000b144940350a4030240701c60b85404005440403402601c80000c04809070300003900c800c4c0b00b0340180042e01c45011010071040d8250011a00388610105180449000010b42e0815560240501a181040465810716015600c0040c189610003030150410703c00542d80850034542c0300e5001505e505224450 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 954812508 1250 954811258 954811267
    0x1430010b06070f030305331c0c030b06010906200f0307060606141801030506191205071a0a0e190b03060a0e1303080916031401050c0406090b090312 65
    0x600c19000c2c0c48054040f00001d05002c0000c1403c0d0a0150143c10030184412480c01203409468081c81e10501d80e40198008904000c0c000c405802342d000484814003949403108800d08504120a5a074030052001e418401e0848040100c180c1c4000c0c0440c1681c8001e0310400041c41da03641580c1008210b51050030940700100308281070103020380c00a4222841c58403030801c404010144141c550092003405201540c0e03803014a8060b5000b6081181d001e500245071240001c0c1e020006840c84d080da401c8021074440e90b205000800c40100840c030090040f141c031200310300c20340e680c5041d060702c0341c3d2000740700b0030224007a24980340d02da0b09040720303415101c2c0c0c2505c503501c0d0300d5480040c5560030403900f00b0303c00c580715440081c1a1940c40c2443d07002e2414005403064990083e14241c80a44024014850a1060a040c1d030b5002440d81c800728043d62059404070220000c4000003400c2d10805442030b5020182000104503844d00100b040e411a6850694582c44550f0b000019007040d01a20075055140d80024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 954813758 1250 954812508 954812513
    0x61204080d0606200703020a0902071106030106350412050f0409050a1505060f090f15220e18100905011d0a1e0c1a041430010b0607 58
    0xf010320410965079040e00b1000344000c05155954242da10000c0c1d004528414242701035004c41c0c008111450103000a840910704c0d03070022072a0303075200340e01c030740300160542880ca2115000000d6200014012201102c0d034800545078a46807500007410007030081c0d4020800c2d042c00360049003501c039103220890259403590343c2e44100a0113030600302c6404a0042ca000d600c840ea0106c8549480d064560103000f00c0c0c02c0103010704102c61a503010b10007a40c2d2200154507202c1c6140c0d102c410091001407599062600d078881d40d10b001401401607405040c00200721030040c0190340c0b4102c6100c2c1e015440340c0c0c8400d441c22480e95547e0030103045d45072214050781002000c3e0300307205054208032054141d9020043d0001080d52490f40c44048540d001803400103104403000000d03800c120007039801ca010301d400304c0030381d03a82c0c010841174058580400300c030101e0046000c0200820080703c0c11100c440c162250380c2012034000780190110030b0120000006180c05c0903010015209501160341104041c1c0300c16919030490 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 954815008 1250 954813758 954813767
    0xb07030603030f020a0c063222060c0308070c05190c0f180902030f0601030c05030105070302071104050702160617070318080a030917030702060702010b061204080d0606 74
    0x1d00003a4082403d04406480d203e10000310b81c010386070080000000c0700d0809008030b980b800702400881501040115001041d55040c00d04c6ca02c807000c40f007180399603032007043e03141c0c0c995210000030b10309109022400708110340d0131200e000041503161410030703c541d031a00403d039171058060038064071501c550400b80794440c48101c252403506018000d0807502d595584100808090309000d0b015480c0c515448a4330320580c1a0040e00e441072008080c1c6100f00b01c4032024528118007680306542c0b20000010030011402c080c8a0142c012a43e8a002e44ca81907081c3c0f16071041100c544512400f940e40d800014568501c00c1c000d810440500c501618152961014014403403030480820710f10b40c81c206000314134002d0081c8605050006082d103424404419603c60242c560012070000c4141600c5903009000565180c2c80c2d405881c20710f80c83d00341c480c100b10000900d0300b08010070000541e0301d0996501410350b074034016030709a0701d1502042041655a40b50080c1c035405042d18a0640f13038140100426442d410 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 954816258 1250 954815008 954815021
    0x15180c0901171018141303090501080f061e0a060c0c050a083a030e160e01120303021603020703140c01120f020910020d030b0d0803061c0b0703 63
    0x2da840b00341240b0207822403119070300140c40c00c00d03880200100800c04402910503048a000c102900020251072918480341d43c14011643c0e0301030b9a500d24030f1030003019005112071029090a203020446c0c0e14044043d0500c00d5009844984100c46924800e4185207190703191455600d0040e011040d9142d4481c1c003c2c2900e0b103043c104444003181c03000007144ca400c080612204503421900100b80640f100c0c501421088070303480c5038203170b01c842c4d022020f07021500c01c42009451040b00d560018050940500c00c0b4103010701c401c106040c0401540301000b0b81118418160306442480c3c0c0b4440200c0080d10f0190001d2145440c40201118070811072802e2540105942080ba4025110f8400394851a2081c07a110700714003402c903003c22009011590303c0c0d100d3780d20190000000020051a18000030006044000717010502001a8040103000089170341c1400f07003a41c642400e441000030f003405540c0e00c3c400e0303010050a190003080803070012040c0d005114040507000e5004140c0c0341d00d908010340002e0207400b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 954817508 1250 954816258 954816277
    0x90c0b0715140a0e0102130902070201110f0715020c010801061b0c0e06041107080a0c1e051608032d070b010902031b07150e03190320090915180c 64
    0x41c00139003600d42032040c001c85954220305918544410f05100a110080d007001d44164100140301005488030740d020002c5d03001006a0500400920389050070b0000d030710601c4000b01c0c04640014511007800d907005592b0b1819141e660520f40055034422030180c1003c400344001801c1d0403003a01001038044d0700700810354000c0c401590184840301e81002001d00380d10070745000030104142040800c4001e03104180e027a071114400c14803007020500da22841c400003c10a6800e4a082d0080b5600a100a0102c20084000c0803e4005581091149034002c112480b80c0310400320301840c4e0388000c00360802d4131070443c1d09840d8840004140755850708103a1000b50003c9402800e0030b0340c1050440c1458245a0584610551200403201d0310700e800b0f00d0708006003101200c208038522003404030111410000900e941c10f0726036540c000461031030140e1680088110010707407000b00603042000411a8695130401c580c01031a040407049010310700000b10f44000c080c2c1881c1c42030008007405004084441360001d000d20701 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 954818758 1250 954817508 954817511
    0x1e190e15090c0a211e080a0806150f07050106150504030620040519091b0219020102210c07090b0f0108010b04090e0a02030105010602070513090c0b0715140a 69
    0x80e0142e0600140c115079003d211030000c5250b240c034041c07000703000000e84628032030080c004524250091403080644c0481d01200e4404000c503409600b5540150380a5120f10102c644030701c2c0e0315500c5484125403103070000712900a903002402c402444800d4000c07000504101e00e4200d16a24001d50050032508039020445d10682050081d4510400100000326402ea94042e1036140919100401112441c02d84000e5001c070480800090310101d2480b40c03140c40e4900b040c2545010120810003402c0130404250b44c001c0d19612625000943d0340000c030030304d040f1072081524425030160000000d6900031411300d8409442200400b154000c119008164080030a5a903001041914001902c00600c00d00031600b8103202030104124500c5140c011484c901000c03000e5624080080d0046429148244c1202d00542d200f0b813010030442c00c01503d10403080074208020400a0425035444012421030701ca80302c4054004500d001c28441c144850201c5440f1120041042510036507400110180440740c4500b142d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 954820008 1250 954818758 954818773
    0x6041e0c0c0b09070f0812190c0203120417061611070b0a1206050306070f0f0e090f100b0a0e19081b040e070311060327010f051e190e1509 61
    0x6c42001802c40d6002c1d0410543c241003040d0000070700901c451000c00302c010005080c1104015840c180402c0e0b40340d00403215038940c0e603030403c0c001c0e1020240130a01011554040c0e4200b0401d080c550801e0041c01c03809140c61054102e038011180c1c500310311030b00b20448040300041d40d25003143d0004505500e0194008040c442c15584604260710340c0800c90b07110700410300385a40300d40c0c054400d10350f00d407007012641408070341810b254012070484481240d0018a403075a203018480f400980900300300040c054050305610380540c040006082440c0c0d0b00100703004880102045040024214079240507120001c2100d03900344e40c00c0c5586090610404c041d5029625180221003032040120310a41940c0c2c00a5121410100050500030340f54001800180013406030088000f43e0002140d001850403454000800d42e4584800034000300d940207402000344c0d0f0900e100d080c00d00003a81e0101c5622404040a00c1c0e42d000030954000d0180c0110488003400d40070740c0b001c030f20b00c0307003035480c481401100410201c4090 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 954821258 1250 954820008 954820019
    0xf061206170a0b07090b0c0f0601080102040506040905070504030f0609060b0108270f0d050304170711011b0510060f091512030c050d120506041e0c0c0b09070f 70
    0x5915001c402000d103a00269804030103e15002203643d04040e09141850203103559021402c00c5810900c1000300d160081c4050b551044030805c03d031409414508000c520b0a8504000186103100364810111031076281c4000401c01801402614019a040039031040120070300e00d400001840490401c444c41d81c50440d070b426042d440740203450f201d10009004001400340c241da00b10384004450342d5400c0d2510a00e031190084440500c18103401102d0780e282c494580c103240c40c02007074105c0c603804603a120880c28024540030520203003078107020100a0810208401800e03084002811043c0006411846142c021061440b03071031340524111550b4814000580e034850204105464005121342080c1416034024804047d2107030311004160b12a0800e1513205016a071307139500b03110940c02d80c20042020031408030b83c2c6404602400707a0184040b41d04000ca00e9401014040403031800d03042c0d4502c60f54800d0303407840c0303107012f42c11840140707400c4040580d29103080502c155850307030f4a00500c1b00708650581d00051 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 954822508 1250 954821258 954821279
    0x30406140105060a030e01180503040e07080c04090e10110a020c010305060307051531080c09010b1312050f0c09070e010e01200604051b0603040b060a0f061206 70
    0x503150001c014624101d1190022000742414181b040c5040d541d9030f03844242002d00038024a9010320071b202640c3c503140340c00128150743d40d000f0000e4041c800c0e01c40800c01000503120031182070710400700000458600c2075032b00916100740000c04501c002e03c2c00002c2d5914804140103400234801d254201d92101d6440d0004400340d900540c0c206030182d102240c1801180303061140d101c510419004000e040100c20084103181911154040901c2030500062402c9018401105005000044010000a407581003c1851030f041485290701d041c5010410b003050301d104d06c4001000300400711207a0382a200d98144140c4507c0c41052140c002c0c810260302c0c0d00b050030881842445504283c03940341c090f0ba240801586c2031001c1407551342c100001d0b030103500480324805043c0c0c500540b081d401400c2d0780c070700303860000d2a00c0449000b0a01c02a034440c050780c040c0c0d0760617040301d80c0a50710600700310706034079001c0101d05105003a800400c54107102c54004104540c0c85102c038210180c00c64420320409603124107040 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 954823758 1250 954822508 954822511
    0x5090a150c0c0b0702030f0d020a090e09060412020106050d0606050307090501050d030e0105070f0b0702060603120f090d061b0912150203040516060909060b03070c14011b030203040614 81
    0x20100c2e030350b02c903928003043d00320190f554004024010380345400d405801030072055110b8411801c102d40c0c0400c001d101281d010440902902c1c0d040c8484045050841311183e407400014401444001c980c2d02c00c0c210107100b034009000070400078003141392101451800c0000b03804a4081d40d8000d01c00c0c81c100042490160159604075040070300055440c01580d181102da0307010000d44e071030600108010540005900610300703000140195000340030342c00c0c480002420503201400f020300c00d9002c0c50000d111500ca43c0211892001c00e103003c03e0341c0d01c0c1030001140105851101c0948410310305282443c2141c5004050341e04004940d0b2051621610740c0b241b455901d61901016003550404045000b00901c25802181c00c240510300b11410044128004102c00d1001c1d0400000203c1116003004541c0e01c5002d140d015004e400012410340c900401c00500c03110080341d02a0040d90f0211142039052403c2d4011000c806c01e1114096071168090710113800f96005440480b45240740072045034801c1c07000c000c1103 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 954825008 1250 954823758 954823781
    0x80a1104021312030302040e01032922030e0307080c0112020705060121020406030302030c0c55050f01050307020607050f0f03091506031b04090c05030105090a15 71
    0x400c140c5040001c4143c1501031034504030241075082002140194240c80c4480c0210711604000300d03030181e141c100b607201807a0071061040c03000358901400021818043ca08113250419071040704c6544940c101200e0280c1c2100b00356415005003800031170003440114100e20340d41401e880342e8401e0094100008100d1040c0880541660858401070013136258000740081101401060a10080310076000901224181c0d40100d0242c2e0000400c2035846a080c049860240c00417500920790441c048034241d2200041c0380040c05039103010300e90100d410110803d4061189483c0d40070b200c440031814031104d1406060054601c10454845d0305a01c2d5803180049070700c240e04582c05442a9190144181c1d600d4102034a40540810f061003c540201903160142d840f592801e00102003080e6182408040e00401600e4a4000c0e048854440d01440d0128002c04840071700382c80003e00e002690801c4500c1030180e030880387c0c0c10b50811092011044000409000d0180a1411401c80389500000c00d01118043d0111 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 954826258 1250 954825008 954825037
    0x3020d0c0f0b0a0e030d05090c0415051203070816260a0e012705041a010804080c03040e09030d1d0a0204150b12010f091103160e0a080a110402 63
    0x2250300080d038901e0b9007500100c500001183c80d020080c00981140c0207000c0603a501507031402008802513040201889800c810f0303804003c80c040500c0c0c0358281c05900d000c3c0d01d015214219881d040142c04000f1100d03080d0f040407860740c032074030100240d030520300e09a01706032600c0032403a420910395001284d56802901c104002c2a1401c82d01d010166810071500c6a4541407103a00d120043c03c04890301e4410801ca00082044281141403d04100071202d100341b40c001d801c11f0300d0fa003100301c0380d070407400c02904107170000c9402d42c64182e032200c414907600c20fa0b0880c140003044d101c02d00c410300e81700001078461400c801109002c0d04009080d0381c7c1804034080304060041c3d1103940504050704180d4007100f4008030620f4840e4101c0e4440300e508031071780d2091205070600c2c5100c80040092400c0440d01c01c010b0210400c1c140400c180e400c01c080001c1c040500a150070301407107241c0e42d09540c0188071341d991b010b030081d2400c8007c60391000e61645590103c1d10540d00b598049a00e004149054421144840c002000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 954827508 1250 954826258 954826283
    0x20f0a2d0c03090305010e01150807050d0b150d0b0403021902030d12060e0c1e0f030406020322060b040c14040e070908031c0b010c23190f03020d0c 65
    0x82203500c070146076002c1c2c00348050524007201007502802034500f000198000030402c1c880c0f029003c100c00084d640103200503080318105000c580d135400621403980390072000c01c1c2015220702d124030722426038034840b541c3e00c2401b080404081100c4030000900c1540170f6003c0d2030078465a418550703002c00d810f50001307615401c0032031030842d810301811446a03407090b04180000d515880305111281c0400950b881540b25601288012201410401c040b11002256500604113a5014074240250102405c010201078010001509031100941003400f080b1625442885090280c20300d00010514a140c00d40a6814021000f000a0080040900ca00e0110b80ba0904d081d2500b168840c000e60b000d0064000c0000c00304c1c00140562040010748189010081c0468500c00080e1038601285e541242c0c0c581880800c00c40640814502c0d03480708400c050000c482c400c45001501810305000c000c80c940791165405d03035403217414001050b6050100794420b400b00d582040d07854a050b0794166902000505021a4a9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 954828758 1250 954827508 954827597
    0x40b0a0515011d030115030c06050a0e0f1309110a080309060315010c020307060e010306234f0203040803221202030310050901050102030d1509020f0a 66
    0x1040301c0e0045a52070b403c0b40d030303100030b00000d0a545460300d11525004141c0c000b44180030048541d24001d00850900e14a041846074000d440314005a001d580300d01c40c104040c000c1616000c10050300751211401c104409111403138903800c595120b030105400b9459110000c1013254000080742c05841c0024003050540c1d641c216200b4140c1e510130a614100004003080390700603201005900050700f800c0e02e425400810501c00181280e00f07547c0081411341a0700455003c02d14070452001c1d482070241c035074444520b0050948520300c0c101d103107040d81d02c0d40e018070640748100000401000241c0c61810103855011841c90200aa010594001d03242990420100303020299201920002411411034580011b07080c0c0c4a480019403614680c5025800000030455083d000803d042d01501c801c40f1961059410b20300001e54038080c01007036956140e0340b02e100404050054280c0070090a2186066588210a591010b2641c020b4a0b040c408200c140280100d18000c10820b190307204202840c1001007002c09 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 954830008 1250 954828758 954828767
    0x21b0d121104050406030c030539030f0709020c0111030402012705210f0f2a030f0a1712061309150e1204050a0b03190c08040b0a051501 60
    0x510442904000c101c0055144c58a000d0040118080c944003010545541081800d1810031041d03944050213022800c042080c41207900b80c25800d80d040b4005000100320301003440c1080522807800a4440c04200260310131300368000780f1029059000a00464503a02008500343c0801da40090114080301700c500a0305c4032002074011071041d00000d04080300ea86030081103502d54142c4010760701080e918444035005104000c024000490380e0f0041c00f281d0101199280c88400c2c02d4000055420219050501e102c404011121030000041c00d441e0402c0402c21060f940b200c030400101c40b14684640ea10815036030302c13010384400485170030752a0525178a100410010f00510b0500c461507079520030400010030a950680204140b01c1040020702003c41d8039414074000758010400d070714460810052005841c0c0c01c105504440c20402c0d0591a901c459013151039140000440e030304142e241449c528261350b481031407180980c1c01080d40b0310094031900304213826600c04861103184040a00803803421540314 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 954831258 1250 954830008 954830021
    0x60f0904081801090315090b0903030403021b0406050307080d030c022a06070602182b06050402030a02090a06030c0e01061e0513030506010f060804020d061e0609021b0d12 75
    0x1451301003c040c1c4c41c0d6950600c0b00204102d03144416a58491110810001c50f503030070b801c181e1050043d0305514207035500956030101044050080c2c00c02c0b000c50400c50700c85030000b8018000003001d8030641034480f000c25a0300c0d45168000000641044002081140080390340004403528104c222888808501856100082c3d0310000341c000302c040040402140f450b1002c1c0c91601600381401841d41140401c200c040c2c2100782c0429950400441880c20441504000800345179002c04013240c3e540d240d00000b41403541d4075034081d40211a00013002290f10b92a03003e801a244a000070a6805803180c40f5041c2e40c1d20b09000c0c1d200070a00341c0d003000444450100d080c0030441410329103c0d24180b065484024070401541c41241ea40d48448010700400b10b10842d00d81c050001031401c181e040c9019000101d152901030400342c515566040a00c030000e442c40c1c030002c42c03c00011000d10840b0341d50701ea8040290701621349450800d14104c5444400e800203e0507045421082c1e4502010049030902c034002000c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 954832508 1250 954831258 954831307
    0xe0c100e180c131202010207080105070e150c030a170106170402212e020906040e190c0c020301051006080c130f0f0f0605030f1b07020306040b060f090408 68
    0x1080c0300c140d000360340803c007030701c084c00a04500120301e003402d00c006807814455400445050741008200401c0702e51000c446c2c5c144071801c481442454040308a59502403280039442c002500000840c0141c07950000b2a2042d01c035802c04019101d80c0c1d95000071600720606440100c849140700e40030601602c0c010a1600600c11803070704e14103003c10200700f054540410600c000c000d0811082c0501041414900000340900a1034001d40c0340c0444000080c90921a5000e55100030390140049100710400d0702450013001c0f15400104500b2584400c00f80c407010480d28101c0c801d60074034001421300b0402070b09070000c60b4050785440229407207031000b116080d000714020301c002c06044100011800d0084920a005003020280b5040081c2411824000103a19420036402d20504000344442160203150040d44501802c0c3c2522002e4240e0f926519070740314158011f985480382105100511240c0351046010b02811140182028404000d002016200301c40240c4004818070801c0c00c80c40040d5003038180c841 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 954833758 1250 954832508 954832531
    0x105040b180d0b071d0d02280e0a11070b042a0306020d050924100504140f070c0305040e04081e030603060604091509150e0c100e18 58
    0x40d10001280707003004410010f45010fa104030600c5080342d0840c0c05c030001a04002c000c48110281000403035150f1401d0207000b400340418456030704025020140d018074040703000c015012800e5441900c1c1e613160409503910541d0b18540340050700e50700c40b984100c0c0c0c1a2540200524841e43e20707601d03070040340b0540001d000050609407000b80c940c0c190400000c07010303502c156401078072020515002d3b0200c0303600074407031f41e034617400070020100e45820031070b012a001003110760654847d0340300d507400018121164080c540282c00c100e5100d0300c41c4900245240b01c2e5801e1408240c003a41c07100d200701c6040400040140100d2000c0000b030090360f002451896015001d42000c500d82300201040c1140c801ea8120649611710000c07050100a00c0e0a101c0076030040303803c8030184003112030b580710b08841000460550079015234a01d2298100040d507280c44651454032002044010414920b1640303d9144000080c40307111200c620000040c010600302140b000c0c0075090348030340311005401440054000e04500c0141c0c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 954835008 1250 954833758 954833797
    0x4050c24040611010b09010303080a0203071205010b270105071103120f0c0105130b010905060424030203070f08070b0a0e0406060e01080603010e0d0e060f040e07080906060105040b 79
    0x1880c00c0300c0204028052a83d03070307590711038818050900b140c000001032480342030448010070104e6030219000b6084155240010303074075100e10801b51042c41c0000b00051410f410000002895181d4401400701c1c2a0f281c078400407020103048200c031035640c50210040c0400c1c800c2c0800408103281d01c1070400d00080240c21035403d00c5510040b00115000354031010158040090322030b82c5042c0c01e001d00e9400a400b61844186800e8580c0c5d91001c861050081c00381442c0e0300c90004603169655088265030800c110120b42c500d85000000d44079007150350005a00a00c2107050014080b81d05090180840c0c3d0024081c20489047c0b2044984035809105d20000b0000c00d0070128407170750341e14490307400100b5968036004175440800b8005002c203000200080e110381d00d0188018120200480e9a0081c0503240c0780c0b10540d0507407200010303440d016010701e01040c5072001c20f000c00ca0201310440903009181c0da40750f6014650381c000c40180d84003c03c881142c006041840100300c20745629001d840c10b03030f100940c10f9490 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 954836258 1250 954835008 954835069
    0x18010906020f04170a05340906080f0a0206070f0c1802041809050a260d0606030510150e150a02061b04061706040905030a0306080c0904050c 62
    0xaa802500201404400000b0200244c1100c00c1240d004100c949028103074001c160380310961619040c07842400c0440481c4104808007813034100f002e9885004982e9164481c0c0c1301c9501d900208014011804607110740014200c507045c0c0011303042601c3e0b5005101500d031034880d50742c0340204103164000300c0d003a10000d0300128401e140c14212051201c20044016111490b000105582d1003030000510801e030314000380b00d008500003148026080c4d41185048039009255405081c00c01d60403241d13004901c5003c81c0200103402e03d41c02c80304c222a01c550f81440a600c1e6030301c1070b0082c0e203401e2152104451038020ba510a0030b0080f52090204040100000503900508003441900c2d4000300e110001600400c4c200a0032002c40816010900440255141800c0c10218007400e942e4540c0460a55070a07503400082c4d060740d440c0c018110f101d078000266030310307061b40b100d0150140c80316000c0c540203030040346250134441c18004862403180350400700402408145100b0b012010003420400c4003000c0b81c0c2c621a000303 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 954837508 1250 954836258 954836261
    0xa090e0129040501060c03080f0c0408030f0316210f0b13020703020105151c0f060606081518010b0705071a040f1a12090703050d1e0207060818010906 66
    0x455481c2201c000100d40d661401c02003140c50582100c5e007880700641c103810200c1d610410007a4400e0007074021120640329819807220501440c3c5c03042180780300020352098185404001f450140415007250001c0145101c0c05803101c00c03c3d800d94542842001100c988925507079042a0092016040c00003800448080400c0010506061201c0d80a0b0002240c004042d030900c42d142e48188114808126403021000142c1841c51500040d06d010071101e4007a02440011541c6030011940403108004482e034641004e00b000d041280c400d440a55910351405650810202e40510f148182002221036801e0076041ea005421090f01518548034074800862030107020300307844180d103805900300d0b0749892409024104a17155a041200200e0001e03080000d20140c1c10144c61506042541440f501d03070b1641c101ca854034003030358400340c400e125840301104100c0d000b290001c4910a10312000c00704d140c6100050341e48503500e208910024090100254019016240440c0c40b2070160740081007051041d1241d50 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 954838758 1250 954837508 954837551
    0x611030703020316110705040e0705041506120e100507020f0f0c0a0504060b09061c06060807170411090903040308030c0409060501170106050304081216030b0f0a090e01 74
    0x4000c682d000080c4540780080d030500402c1450b0340e1810740801030640600645503042407045a00498880e000ca002d216002d011a0b000b5002c05001004002140210482014502d03c40c41001c0b54144a514101900300d01031441030651500c024041545d41c2140c000041a00620780021800350002c1e514200c0c00a020542004003d1001001d41c0210001000291b8485501041c4501e152a604002d81d1240c00c050781e22440c011030707a031034507010201b40c841040a80c82a0703900c041c0c0d01d4040086a01608011858041c4c500d55540049400d64280c40990751300742664060a0503100700c3d400703016407a19125040d4440c6100d420341c0e04191780da56503220710b0b07001644d1039911140d0101d41404581401d2040400600302440c0185000c40320351489001004180214010060300100150600204504495907401c042888020500e0502c0104c540c10352004010700029090a24614042ca065001880341c018001c0213071100c030b032070100710b60014028002c1006941d501c440303456500210181401 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 954840008 1250 954838758 954838771
    0x70905030a03020c120c0904080306030703141b151206031006030b0906070f20070f08030715020418270c080f031206060d060f18110a0804020d061103 66
    0x13080c690306024200706000301c0000380032849501c1000c2030952595140c00c0c90350015000041c150341d0b41c8401c00801d00346000c40d0005441300c008107a42403981c680010b111402101c92001ca619820f910004010b031a490030f0b52078400003c0113201005280004404554001400030308507040351083c81c903500c00741c48040c1d00640c0e00c280b0403400c100319a50305200301a401a202d01e45012003c052070000b508800c86c80c040c50005032440c8409403881a010804480500860740500c100a551a41c2c03030703a903d83c003658084a036010880d280c0401c4800e640255001d8034541041540d600030b01c50740c3da00c0209050003145c40032007141c1182450135603242c103440c151719008100032203500d414201000e160003030f91400c15135240d00402a125807910546c0c41144c005904480f0740740d5400c04437002501030441c0f5001920003403020403001030b6901d0440031b0081e41c1d08002c0818400c01c0031180380e4001d0b50203040180700100350030f523002400515080701ea000050b481100c1c0061103906440703413445540c00c00c4480 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 954841258 1250 954840008 954840013
    0xc120510030b0f1e07050403020306191d031c092009090601031a06040222051801030b0406111303080d0b0405040f0201031116050d080c03100e070905030a0302 70
    0x28000c0c0603a0b602c440e03034815800c4212110a09110003109074030301110034464200f03400b18020402852203802114010354005080322151309081b1100329040c03020b101e00c140c0d5036140841040300d800101c20700c103591701c003010095401d29042d4403642c2010f524410020f890701b5500c0620030006208985040080d070750210f1000414540035003801361910018001507095880103004000080c14134009c0203070662030000e881c0e070f03030f4503a540480c02901a0111386000500400d15148007042038907640000c40d0800c40d82081c0d40e80411510f816a440b084c00007402100802e40024042080360300000c1c10b80040100c19880d1000b4040d144e80501c0003500300b101e42100018020000b9203d0340150300880008a404102c0e6041c50307030b02c2c009040d035400002410315855111a0381c2083c4150181d03400070002540b010340047c0d0380e00d001c5844500414071400810396001c0401e1102e0307403800549105540318580102c26900300010074045041c002c010800b0010b02210205490700e00b40148542103100f03800 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 954842508 1250 954841258 954841291
    0x3e07090f0e060c071104020904140906040c060f0206180304170706120513030c0227010f08030a0c0305131d040b0a0e19020301180b040c2103030c1205 66
    0x501c039061550103804402e140b9414448400865103a0340084004e000468006035154820004a400f50280340c40c0c130000709104100300401c406000c035100344280c2c400c44030489141d4a42105840d0050040704030401a40804000f4440c26000030540003d4540101100c4c1015510030340d14403944000185111075810260342048491b4210100080b0112100828400c80c609039840c51104580c80c3c001408000c880f030905401c0d03440d40c00c07100e041c5d50b90014182d28400c2c0780500c07440440c2d00a200324501c0040300100022601345c00300c1506c0402d80140e690140350340581d142120541c200040f03000c551091000001040c1ba01d40c0d504000c50356250300454202ccc03030320f401c006445078402400c803030b40c00e030524504568032280891400c84107942a56220f142940c0d500100740100070000d844000030100352011402d10880c4045e8510440c0311340c3c850b00c07209840e80000c000f4850804070810701c400c200006c002c0002d0182c1c100b502c00d0b1402e494012884072000f0041400d6a1050f690814007805040 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 954843758 1250 954842508 954842531
    0x20070609020d0516141c03300618090b0615041d150409240f0507020a0516061403070512010b0d0614090c07080c030a050a3e07090f 58
    0x50148582980898021308086d130300038800544e608100600408224070005101200060446540d4030140c0780001810b0391710310b02e86000010034190240ea400000d44600e00d83d031490150081e40a026030240803650140c40c1e103028000e9400d10320036000c038190814070000c02d09104503040e034403c00d10000c1403d52030342450040d0b0005040f0300c100c0d150241e4100300310f02c004948041113054000c0b0760f50340d09005a1103641c4410300101019440c40034128108018000203903400034120828074020b100340c481301120a060f00c1600000c0e0b1041c02c0202e0600d0a8200c004111345001e1a445100390402620307001e1512480f400340340098000c03920810380403031481d010004070310038034029080003000071544500c0c400003d590311100a1014000750380001c0c1140401015800740c40000140804594480a40043c064100d404c00e03c00600014201c1400c58034078080a414681c044000c608460304220310841c00e000d409800010594a501c03801c000041e0301103861080c2041080034050000b066030426 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 954845008 1250 954843758 954843779
    0x118020a080a051f020d05090318030706082202031e060106020c030c040b03031905040503150112060b040b10020a0b070e0109060c03140c0604020420070609020d0516 73
    0x19004118194400c02d850030000380d001030601c1c000410646195641e81c00c0200000c0a07116040d11882e12500300030a004018030004054100e03250101d1072000c441d0368403c249a0382d591580300e4540040e00540210354603003588025071010b24038039481c40c45880c1154000c01d2400e5030300f607402c3c0701c540507074404054442d0341400228003520300b40c03020300540e00c1c0e9140040e5560080c412040d02c202d13624110400c442e40c04200315241c040006030070119407241218043c203290418807980d0f0190185c1d4201240512000401c103050340c1041c1d070304d00c410b01d080b601c0300c600521550f00080c0e002940c03066581490781d540028540101c603d94000e103442c0c0b02d01d16000514510192090050029901244250381e03000203581056a40328a81082e58564a02342201c4d419420940390128050005030b66603068008590140b25600a40c2c081c8203860b0101965456032528003100c26070000e007407281c00f0004800f074121a03042c03030005260f45075165450b181c01d81007880305590f21b542040101c0c1c0411510028 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 954846258 1250 954845008 954845029
    0x90c14030f0c070b012c01050a14300c040b09010b0d0f0f0207030e0306061c08040f030c090b0d1e0302100213030209090a120f050c0d080901060f080a0b0c0705011802 73
    0x1041d20082c0c01f9407408010564002c0b06002d50000d0700140164400180c480c02c107000c10300d243e56041032856040c003000412100c131240700a011a0b0003800e21a519600305401101c174035910141c00721070144c0c41c10981d505940c07c1314201180c03040d1100c014080c110302038007070890300107030417880103075681118640a4011070b01e1a004074082d801c504d0070400580d1390903a51807044450384940a81c60101071034003640781c0c4984c0d000003050200c4518040f00340404d02a014050303a41d10034042000400076810003a049007408802010824400c081104004d02e911800e20f0807813003801242c8120140404120998009001e03030422100005410002d41c5800719a003070300915440003610707680c48a61154030500080d001040b003800030401ca801540b510440480b0343c8e0010410640303480d0b8181020061281c24180c0b032240c40c9600304a1f010404040b00100001200c101a006003003070a40740d03440c900629070003041005008802c3c024040410030a00840020714070305080484402190310401c07100030103 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 954847508 1250 954846258 954846329
    0xc0f080610051009031403120705130915030605011d07110a0f0c0b03070903061523010c0b0901020c150c0a08150409060204090c14030f0c070b01 64
    0x10480a0141c41410a4500d4041c0d81c010340301c00c2a0000780c11015140000e00b513200800303680200340d020f0003031030003c00030707000c8040320002c600c140b41c0b40c00c0302c1181c19002d8004842440e81e0303250420003880c5020f03030254000403020a074400595940380c0f941400c498090740704802c1d0b42c580b8008200c03042081c0340c1c120b0340400381e82441200c40002d0844141c0e10780c00194020801e42401380c00d28140010542c80c0c600500c129115a5030360f1901402c0107096035101d203c215181410030141050714012140e40c0c00555514070404d85040400f01900340014610342c1c0c1c2d140c1032110101082e400729094181140c455010b010025a4403100c610005107401d800303480603801c950200c0244440c080c1c9403021202213003030600d0b02c1c03191034444000b03071040300c4013041e003260388245440d5218081104a4000d0800c8404003d020056030240ca08240d401e5041402c480e5450201000000c9160303c1110206070800c6c0484c4400d03003081070503541d459042c80203811118407860500010658071800340741c0301c0320748103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 954848758 1250 954847508 954847513
    0x110d080907361415030601090e030d0911030f160e0c18220b0108060f01080403051305061b011503050705040e0c1c0231051306090c0f08 60
    0x105042e000030a07180d038516100d400e0600400c80096200007581051040c5200c0100070212070605808645a00841c4444030703000780100c0703000045490741407250702480c000100c080e510b0041403001e0b05000f000e000d60111064154811380700c20685041200903419582d05000384072045101d088079500000e10b038050300070405c600c0100001e020110041d01c00d0761203102c9070040b10005000010b441c806401c01385090f400b0008241004640d10750700804070a800c01e890f2a00c80e5160f4009212b98007915040e500d021031144000702d400a44120020000f004902c900600515150b00001e08030303900c203082880500b8602900daa00b001401c6c0b054204018172194684003040c03035a0f650030307125032062050074811740e5038881854603144280300d66000e10100800d440400d202c8a007840440840c4420141e01a040c2d50100d02140107100e440441804400b192034200e28001e030291001074100180000e03018003205040c000001d03039600a00100501c030725502500a402e0091102d40803c09a00030805503 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 954850008 1250 954848758 954848789
    0x71205010e12121f0303031d16090e0a1e02030717012007020123090901170d0f1209080904021305130605010804080d06050a15080c042103110d080907 66
    0x3482c1301c000038800c980e854100031a118204209418040d00c0148038101280a1514030b0301107841ca04071035000703640d40d0300801c00c41d568000c04500e646d084014002400b2294105a004110000c1c030014100c003440241103400c0f541d241d2a16602c5401d22030200b05003691200c1c81c10745440d00b406240620340c012951005e05002c26074000900c00340207101c0c04011496507520701a4031110100880f96040d401030901d0001e560b583c1c3c0254900e10040e2205210b6004002c0091106449500e02d09100151a500d0700c107045100c00000d0000c14a04a0403144a1010000d05540c0e440394005024181b500c00401840b01c0d240030103001031400704107001c402c401d1515900b030003240e800c5810701e80c1240c1c003c00d54a89030481116072000800294004584c811440c40c0300042040010603500400780b6560345515080d2560000c1c02d1213070240340a01801d41112621010b210091501c2d14034501d4040d2400d0300c0d040100c00f1426082c0703002c407038820000400182c20040480c601f0082880145003000080d1600e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 954851258 1250 954850008 954850051
    0x306010e0603100e031306170a090b011401020a1515050a08120c0304240e040b180a0f050a0902010206010510080106180801060b1c060503071205010e1212 68
    0xb180a030410701200c2d2a0354200701c1130010310400a0b07a070000f8000c18060000f0f0744440011386100b000c800c1107800d03040d0346400240c94000d1741c02842400b1354001c3d185250369081c4100c00c100d500c1b0b0712055604600c600e0b0b180700d0208814550140003040071031070024858000a00f420080d840720381083d4018000c8980800c00300c0000030f0488400c888042c20141ca03065411421030446c411980b15028106602038900b0380d1081c3c42281c26840d01e10b40d211404202e11010030b000c1503501d940b044035804a0428034542100703040982c2154841d03201100002d219807449081400c550040d9181003e0f41d560b4408107085503010041c07a07014020484100c400fa40c1c10280060000405010708d41c00c000ea00340d48a0204070003220a400030703080c500001c0c070015854000c5500f45030403062b079070b400881c0014691850042144211810380304083c0250a4007030421110b108000aa07000031280c0c2e66030740b10945040c60052208100c0520701d1545203a40c0e000600e10000126800781c40c00c100c040d5219000d410 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 954852508 1250 954851258 954851263
    0x3030f1a0906040e2a03030426012901051b06010f060804050304060c0507080f0c0103110c100b06040803040e010e0906091504030302070b16140c03120406020c0d0507020306010e0603 80
    0x804504c40303410034048960f441741e0f40c2c00d0b40c080c1c814260507100c04540032484501c4002100785c010502e120840260070140e00d4a4283c1e60244035624a00c451032440400419800684540d51001070405524142840040036510450300042c041c09402090040c0300750050080c100c0300800b00752410152034146a04c9490312403140d88525001d002c2400d01ca182002410b2040c00f000704034220540341680310040c603c503103e0441000b0740d070000c0d20b400325031a903007034112080c3c503d240e003944020880290984100e00003860715485280e880342c414040000e0011301080100047c1600c84040c1d411540743c07110346509200083d02545ea140c004004204820000182481c0c031103107024482101900c8509056000384512030014001a204008202c00d01240c0071204455189070340c1c8003181108403908011090007840e1151905400401c911180704455030445030700180602d00042c07400510366005490007131004c8600000c0394002c503019040d0300d02400000e00400b09840e103600707039141c6040001d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 954853758 1250 954852508 954852523
    0xa030617071841010b0301060203072006130807211509020402120f0705040807140a0803040806071107050f090a0917070b160e010c03030f1a0906040e 66
    0x400301c40d40c4607030740c0e280d10015446070040038411040083c0200c50b03007103100c03030103036004a010840c000703442d0300000764100e0304012241201c0855018600301100c41d51001d00e0740134801c031052105040c4ca015070103c0c2d0780781d00c014502d011885081ca0216803401c0c14241c10007080790b103c421554020119480000050000e49980aa0008209000000920801e001031040300e1002c0e401501c007140c2046a842d00c1c00c03e0502800a59100c10051350341c0100454151081c1d004800f1650019002001520704250300c00454050041050328102d0325400c58910b1500558081c1c0d10990003402400302e120303007000700e403413a21403050081c080c1c640c1064080b0b0512003981172000d0190041e20000368030304d55154400180c0945c0700c0040c0d4040700d80f40042c403800c0e8020510945002c116180421004225894813010440e059120101e0030b140c0d041c011b44018026032000d8041c9619042c4000c41995244200303440800300a40301c201816000c018480c50050060031140124030742000380900b4400041c400 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 954855008 1250 954853758 954853799
    0x61f022805060f100e09011e0c030506120c1e0409050610090c0813060902130f180c170709050c0711010201090b18190b0f07020a03090b1308030a03061707 68
    0x40388151140c2400034010a03150030050040b000d441c0b010640380310150040c9d50000340300d0b581444a03860301c00c2003140291905c00c000b501d41e80b260302121082d0516105004200c002540c00d00d4826802c0b401080543d103440c1704c11600ca41280c0100701d01c00d00c141603020081c002d012420021500000e00103445444060302d8103400e0341c40c42040c24104281d5070098100a80c4c0900806e00907803409007840d02400881c40c4840420381084030291030b540c4800d80181115400200c03041c4818584401180800801e4099119500400384042400d01ca01c0c080c05018181102443d80e407541242400c841d1512140c0625046906124105001c1501151055017212550003541d128821141400d40303800703039a85005c030b8200151000c1c0024070001614183c03041030203804100c035aa884d03030800c0381c555100384401800705900042c05c2c407a8520a5001e8200c031510308442c2190180c95080607860b5410811107840081e40340e90041c0040300200081c0d0070440140c10080415a040c04900005050b940c00c10 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 954856115 1107 954855008 954855029
    0x181005060f0d02150a0c1b150314060411040510030204030204140603030f0a0504120809012a110a050a030b15030303061f022805060f10 60
    0x10110700e01e60042001540300f0056001a00641102030340604005a844508002403541c0d8280103002c0c7c2c04000000c099031030600d000310034540045050b82013500b40725000f030b0340c003030140c80e05a0004004ca03004145840b05a040099a0007694040e0750b000000c0250b0b1540181c142e8010001e49000351070034000481c030384a034142841e405561080e050380c070800104400d80204406880440101e203001450290340c0c02c083d0390b807080803400c150b4040b080000c4c0c0610a41e0000d22121540300c40c0582c0c070f0080007460b02400f0b6400707400ca40252008411024640440c2d90b0301d030389a0081c08000703009480c181c0d12030610711450301c8103c4080825049030f00e0111000d00d400016a882003130f0086c01c0c00c00254491003940c1c0f07440c1c9d8050900040d441503d00d0004030401030103403a02c580b90455031803d240f444070b080044c504513000e05a91408412780f0180403c04e5403001e1072a090742c045450 = true := by decide +kernel

theorem cover : BRFrame.Cov 954676258 954856115 := by
  have h0 := BRFrame.cov_init 954676258
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 954676258 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 954676258 ≤ n) (h2 : n < 954856115) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
