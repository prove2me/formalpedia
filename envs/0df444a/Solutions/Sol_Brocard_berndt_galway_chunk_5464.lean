-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5464
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:57:08.490727+00:00
-- url     : https://prove2.me/submissions/ef0749fd-1e30-4d8f-b8aa-44563c546d94

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 982553956 ≤ n < 982733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 982555206 1250 982553956 982553969
    0xe130c050906180a06090608131e060902041812030e0307150903031401120f061b0807090f030b070302070302010e0102040f09050609150913120e01030c0201151707 72
    0x3d07154142c105041100c40311608420b841142c820500203000303802408441c083d240350356a03044481d13807214640b5098001c2c044045078910501060b482040c0384801c004818030348501c1c0007085001c070b640100416164500d07e41c105030480c184030356001540c0c0310640c0d106a0344a04000c40c2010b9071410540c00c500444902510900c2c5a140c0403c41d0b5840c1d5009094191281e1400c011703004002c110120344000034050318004e80c6c03486103154046000203c040008034460600400d00090050000b51101201e550640200380c0c484180b04069400001080150004010030070b002031035070b20303400c0485c82c01905543c1410360004610080c54400e4101211584600009654941c4d40d01003601c4e008841d407149440c481d1401010806501e407070504140105240844811030306c80520822201d040080c00f482c40015030f44d103641c00040c00c280840040500142c844140600350350300054283c4900b642c1c80e80869150407411740700d01c50300d5094141511102c1800034020340429000500d050610380201 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 982556456 1250 982555206 982555219
    0x1710140402010813081b060906093415021002030408090d080d110306010f03110d0209060c0a05060105011403061e0102010212010e0117030a0e1c210f0e130c0509 71
    0x11008044040110007803044400110b1f01e040e40c0d820302036600c410080d10b140b10280c028074800000246403030413581510b404141800e00001c1c50080204044c0b5480d0b000003910415401c840e908617030140034074100b10705ca100c0107500d146440d5880d40383c24801c0c0c200d0350f4882d5810340c12600500c0100300c152074840c1c403012810015040145030b4107001d0b400071201d95002961405134452214400d010f80080a0300d01e40105040c040c9102c10032000e5040089143c0d00328505000c400b280200400010418074000d10280c91154142400103208803032110103030a452008006014036512017284080b8002d900240e00c804003915440101e02900c100390000b0030b500a40d2001240c003081d00d040050484402402c0c02901c0d22500690356200e02070140140c0c04101c01c940002c190b420081c1119071102080e038902c0c1e030107200550b50701050200104899411004941581e01300e281c02030f49000341c00410742009000000c05070005408000a1105c21000c29140c1d00c1c11203a15001c0e03000e403090130800900c1c5 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 982557706 1250 982556456 982556467
    0x801020a081506070b1501020c180f070c02100324030b010f17030f0d111603180f0605070204090b010b030405010c05160624171014040201081308 64
    0x41c80110207498024580107041080501490328000319401e4650019140c110703540d424043c0e0862400081c146815030160800c500115602c0039400c1262462064400d41c0c241441c2040304c4520b4401400001804a01b41403200543d6a0518440c4600c040740740100381412988a100e0303d89480d114107161801c6000f0011040200580c03000e8140c800c03a41b08204840c2e50b5581050f002078407169441ca07290400c110360710080004400400c0302d03240615010680d6094000701001d02d500042030b84a000c3d003006d458808050b0701000b000000141010301001640c1840d90303400c489603051040b1024054001547c000315103a0342c1110400a0300310410280e2503a42e0a00f41c085d0340d008803021607640d4a04401c400125000d403059606401c000e09081014200e550f0b02c0c03100801c0760080b25001d0900c03403004c003c00f25550403035110203440791581c07008480b1b254804003881e05d03603c42d000e10981c40c1807050701c40600040a400550294091900070816165050700f0440504440e1010b805001c00203074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 982558956 1250 982557706 982557727
    0x60f0204061b020607140307020604031a150102060109020d110408070302090c070b0126120a090f080a0201050906040b030903030421081810051305060f040804150504080102 76
    0x140044a10580b148488448481c0c460740c03600c2003000d0300961022041c401e15001c1015044120012240001202d01e851103980005005420560040703946a003240400d10f02141498501a005030100c3c6a940c0e19440400010351610014014400314070743c0480c41c07500786542d40e00000702c5807000c2d0111a607039684401103a41c541504e40402d1f4010580d45000c1000e0544520860344519004040b1074040d908003030400b1030081c210300308520784505a141c0341c102c02d6428000c900c074640c0c41d104915566074a002d400380509045a210155480010000b00500302c00414001c0b8400e50903e0318550f18078a03800040c0690240342c00c544040c800100400c159000c001000f18095070240a080b030340252a601c680b80a40001007912000138140b00101c0c1c1d4800000840e41a0300c80740c00142e03400d500117000325030201c4808030752803000c3c46c0300513140030b092007001c2c00300940002c614080120580750546900d4103921541c8a03800c440c100c442c0c82c0302d0034540700340286e1300a8103401009550b141003030103 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 982560206 1250 982558956 982558961
    0x305160227010e013501020c1b190e18060403050703031103090c0118092408281a0114040606020303071d03161e050303030c0d18060f 59
    0x2004040707214000c9001140c40d0040c0f401c03030303412138000392856a0352a03031030300b4403112428100c0401c039110302c0d409002448000e82030028248034801400180000f0050354461024071b82458203450007030701c0c088100084a07080d10410b10a4580c01c081200c803a44581854130182c076409640b550b072500480d02480100b5a000000300750644c002c0d0740034444403541c0043e40c0c07040e110a81c0c41c0d0b5607aa21801c1c10300ba095008510654640300e9009403441c103160750310000b4040d6082910082c18141d8940f0382c6411720300c08800280003400c4094000d00351054041c80c0c240302c9030801d40000c4043e80e00d01895104100180400c1011900201841c4045580d5517401500081040340554030890070800045011480041600d100b24103590312201c18200ba400c82c0e084c2103011400c80c030b070035004d820324040c40c41000150740700052280400d03410440c0160b1102c138160f01010341040d0300c0383c1c00c01c00c140210175191806850300c03c2b5030103000191011009003441101800080010b05150511b92400c02c844000c0e03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 982561456 1250 982560206 982560259
    0x5030a020111043006060f050103150e040b04150f06060f17011205100606050c1e030904110d0e031818010b09060c010207150b010f02070303051602 65
    0x90300244680300c1c103007009074214051409140454400b0090000c5084181c0300f0300d00d861200c1e5071000c00030740880e45840082d240c0c2600039500e02d003407007030003000070356071504c2199001c01b5407441d5280054104100160294000381003e81240740020102c0d0610124401400982c600c0e0241002685442c00860b0003a0a40f0310685002c1110300d140c6018a40c020101034080c000b05510000c807585c05c00c0d034101031640e0b00020a440c9442400c0b00b142c80d62019214901c042c0c071081d21529200c1c128403846525000c1c091120720607124580900d03290100b400021744901c1c407011200030030b20508881c070300e4449001d59103111158609201360141c5048000c001031105850450700d0341001003114061000c0f4100224a10501c400128010810904000e0261440c0d09005051034549440c04030320b0703426038000d0341c01a42c2101c81c0c45081003061400c0d1140b80c4100c2400e00f443c84502ca03007008042c0d15017440344006024404009503810001d1000e50302c40c894075038001c201940c20303901c0ea0559141c62490 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 982562706 1250 982561456 982561477
    0x10614190801031a160305090109080d02030604111201050409060b03011505041518091a07030501141005120a0e0d0c060b0415270203090f0c0108070909050603030f070503 75
    0x10203400c0c0710009119901c40c820004101c003002c101880d280110000c00006016a088e950307a00d51920004641d1002808101402040503880c1e040110410084403071890007000c05690803ca1054000100510740381154400c8800152035400c1d401c000c005804003070051581940b0704a001200c042240c0780110a84005980c00c0000c01121000d40300148154040c0781c2d55004403035002000360000e50003040c0c0701417052000d812005841f031a919403d000950364070010945850040c848101c100c040c80e02c085034100d40e65502c2d000c3d003400152092240300f000120f0000740b000001e19a0006400c141c4040c01ca00701112540e6220000c0207000042c1c241d011998a070030701455800a1400d800352080c00c00004401200e80c82c5003414030315050000305801021001c6006400309059040d1010358481c207413a01c060100d4007400b0950710304050010b03039082e0501c50708809000d20760740c3c800d01e0182910758490000440e80c44070800240346006000303000128003000220482086804805410366108 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 982563956 1250 982562706 982562723
    0x1101090e1311060307171314031b0307020906240c010c111b060703031506050a1205010b0301090906020f0c0a0b0907051815030106030c140d020901061419080103 71
    0x14101000003620050303680c44002000c103030001c400e10046c122125003082800074003000000301a501c00020040729506c1c0445a04080340ba07490320b49095074641d00850340c5078051840c00c3c020b079000904051000d050309018040b040750702c0c003021030301c0c0b1009001e60590b404a59290007800c0480c03030280813400c2507040003481c042a0006000f41c0091b901270380e05030303070700c01c0005400408090248941044000340d0405031201020171281d152801c055001e080b26541d4a903581d4240305003d0318001c034244c810100380e40b41000403c514003410302624152010042c020503040c101c0c0c20405c01034007402611074a8184001040316030140000781940781203119103910f148035039850b00510b480b100d0500c0b40fa078103c0c140b44109241c0801e12032806901c82c03000c0414a10301d180600c003090031100c19420484803401a40c4050054024031103c4292004080700c40c405a01c409601040c06000c0c107200d99814403581d111000e07141c2c0c2844003034640c0080b64004510001d020140020200c12080c40299051203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 982565206 1250 982563956 982563983
    0xb03070906090e1605330d11090d0602090102121308070602030304030225031b091104080c092a04090605010507080a1110020705031201170a1101090e13 67
    0x71010650040801c0d04d411100e4a591402061001c4801c02c030780145402180c0128184003e9501c519242d10310080020302600c3e071851401d110f00301e070300c0040c00005d20780b000e000803060b951b03841540b0070306c4603800230025031958440340040c1d2a00b0004100d21501280c0420640c40d0705900074a040110360960003242e408641d21602640c607444191400f0780146c100d03150440740c041070b074001f0041c1c0358a030f200b100c03110650300d80302c0711030051035441c0c030002032541d0000402031001a8040e00701c110311a003415500d4140b412820076034441c2e4000303085010340007650000700c464460754001e00002140d424884140c0d030111120010690080c01a59051850071101050343c0d4401c0095404982e07004181a00e0540008002d171119010007040020a204107910f00b2140390160026084103403040380155194640340781d604042500c141c20580709406642c1014041c1c03200050400201c42e042401941e40b13901400040301c0300040c80d002480016040c0e814803a00940900091446500a484401122 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 982566456 1250 982565206 982565231
    0x8240d02010c03020304080316150608100b2b03090501030b0f271305010f02041d061210090b06060a02150c041e05010e09040831030b04120207030302120306040b0307090609 76
    0x11804e0740200e071200d520120085002501c1c9174048074100b00000c041e42d240385d0103104800fc22100240142007100c0c40050900f0415800c20305c1400a00400d08003481154104008602c1000081760782a22421413510340307007041c1d201c01d400743c088034403104258100307031030059500c10384160400c008030342e250300e01008002c910015200ba00e059401c040361001007105000c2000b444942c0103806203500c05814200d5440440080119448480c0c4910001ca207a02107403c0500100d400208054040c6400700600702c0121f90202e4410242c0b08850720100c0217803141c0101d2102400780c1c1c0c00c01400510740f9960002c0381d01a80c007901046a501366210084108040244107004a060710001c01c03002d8240424490320f421310120b841049203421000002ca0a030091074081e010041d8019207014007640c0c20b00081c041c41c81c04128924015000800390f40c1c0c0743d0703a0000d603150550404682d0140010010965a60f07503900400e40c0880c0040440f9055601d41d00c1c0d0318010100e5218100d80c003440d04500c1c0101 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 982567706 1250 982566456 982566461
    0xc030f010e1005010f02030904050f06040b0402040806060405181f0c18030809010c0204060b070b01050909030304020d08121021080910030908030708240d02010c0302030408031615 79
    0x180c0400d0303038003050701c2d8036040040d42c0701c41d100110700c0c00358001030050610603116881118400c00043d030b5402824100502888129140110064051401004107005084001a030590403940c103940000b819035514078119002090207005004134007038400800c00c4281c4a02480c5071064072480200000c03100600c0035182e40809246500f52400020381c2013000c24800409022980410b05000180301031030b600040480700f254000c2200d41c2008551101400b0040c2c4074107015100603a05140c0301c0c207080d20704907528000103000920611480c1107900402c40300300141d425a00140c81c080d106401c24030300b500c02d420513034010404060085202d0040d00707042c684044034025004403945141050b01c0c0103020038140c00c190000c2c107054507030464000182030080103620500c925501d103181802e00e9020900b0455a51114030300b40b0161885e410307942c1d0f81c0e205201403030301c0d82400c080104011a140c280c7c298000c80e0300586060001140c6900d480710302c017405a50a0340b0441c3d075102100d210b54103c0c800c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 982568956 1250 982567706 982567711
    0x905060a23060d0b040501060f08100b031912050904110306030c0604151b02030a140709020f0409020912010507020d02060c04140d060f0507031a0d15020904020c060c030f010e 77
    0x601031103940b41400400c58911308590002e000d01e0010807265110100c0c280803003840d50005220340c4c271003111f1689001d0544103152003034900714054000c0c062022001c412685110380090000e030381148001401c103000d43d00b02e4450713600140050110b2a00c00c2401c50450b0004c6070414001d0250035a1a07000b85011750444045d1f03500e6a0750406c0741507039044100c1c0c21103c2c52060100c06107441d0390a10159900300040c40e9503a126003845607000502202c4a4200f410640c400103001d0300621004882d80c044100356000e0320740c4038400503120700c11000003a140750021000b0b010203503c4c1401313006801c2e078049119505040b00b6022204aa21403a030102c3d1648aa80708900c05003022081c00074203450710454889103a8020300011400c803000e1504801140c0f425282c800110f9900d41c00c40c1c482203a44c07041803607500c1d000c4441e046d0b8018a5121001c0c9030000341c01d000d806030b50001712980c846d070f240da06454030700e1030b411308607911407800000b004130551090b035003140c4c3d04072010000a8a010101e5682e031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 982570206 1250 982568956 982568959
    0x3011803140903070e091e030c0304030f050309132306181b0d0b090c070c260307060204060315120b040f05030a020115050328060905060a2306 63
    0x15184281c146489500d810500c419581400754480014452041000d20390080d08803402509001c00b500e80f8620038840740f1410310341d881e00240000c203905140401a00c04403604031100d2012050b6615080d420f40c8507001001d03602c05400a861059490fa030f6010050020181d400303414441c1400266000d20340b022a40c180e13001d50021038a10b90380c1c5014682d65004100c13550440164044508114115003103a00d901c200ca99958140c10460b14040c910707241c0001011500310302d44000b60700c1d81c03140c2c0d804234001c81d290981584400c0000103100c0103980380c0700d85000c0039207403a80403502d0200080d600c503200c0c0d0350000e401c1c0200384900c41c030940e00c940f01f29400020701001c94082580c40c80b8505400030010b440001c000e4100c14085001403000380030404042d4000a61380d94003903404072881d4901e0300240d0007948043c00388180b0000340070244041002c290740d40d8956074540d10300f00c005001c4800e070040050062100f07028415816070080c1d4142c2022411000004685240030290100d00f119101e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 982571456 1250 982570206 982570217
    0x61a04090b181c0c03020610241101060e0105090718181401061709030a020706110f03040e0403270312030b0306100603110c032b1a03011803 62
    0x5500400d400c600340351820945400c0d40d403030002914164042c080100343e010046150003034410105a0f05000c5168451a44102c0c10750850405c071035010703a444860300007040303c1d0942d01d1421519015100c0c0348600e185c11f00003800840d4a4200303207501d046e42841454007030701340f1202240c0114001c020f1000700354821075a0180e01441c1c07484a079181c40034280007441c0b0b241d90703801428074a0681c01e0480c0c040e00c9a5140c1c03c1d0b86e400078122144074004002c281c06015003040c8114508a0f50104051003100c069160190310428078070f042c98180001c02c0c209080501c0001000a00e148a603465035201e140261507100d11442d050008401c20003240038a81803000c80c001c800e01c0000c1643d451090030b10118680010401d2405004c40e2600e20155840300043c0c80b5140204850380d85801b400168a40440b025420807086125559607401149995001d00c021007030342c00d510306410201c210310036200903001c3c0110000310042c030360303180315803100742d8025400e01812040102c00d941c400a04076605a942e0b = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 982572706 1250 982571456 982571461
    0x601170c060a0c15060e07030c12150b12240901210b01230613261219031a0108180708030901081018050a060b07061a04090b 55
    0xc01007641d00c01e038504802c0c072a0030310b11540422410600f4600c0102e41c40c50001e5004d081c445488031104d00200000205410420f100d01038580c0410041c140c1d00b44114080f035400c9404d51800292540c03a00a1401381034081244420983e030488007070b0003604480750481301071400602846070343c0141c640c401d8018443e00010061200e00080350308074040c0110210030301c010540e40d04800611b003030f40882924441700c2e2007130166500d2081203500034403040301ca0a141012a40700002541ca07148a20b5079603400d01c180010300001c1c007840c030b21900141001034900a045840e1020b0a542120700b500d4201440130003c40c420b10b0080c4560300e14120b01206401c40c032900080110307800d4400402103480400000d16100301d214041118001500c608405503403601243d00c0014200c0780028191018040d601000304035590501e801c9103e04007050070042000e940381c0791103d014150b10f60081420300c00002c1e00034244406640310342d40600084448034031002d82d010802c425030341c2c0d2407405082000014003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 982573956 1250 982572706 982572709
    0x20d150602030a050a0309061505041d1b0d0206190e0604030305030a0f110429210402061b0d0215090706110f010c0c050105070f0c030324080f0601170c 67
    0x41c0145d54602c2c580410f414185941c0e04066075500ca00e11a06151244000d2080d440c0c50301444015154052400c05044968525299140c109441c403100502c84d02e05621950348428619402113500034004aa490081d01b24240c402c00ca03040c51040061070100310040b041c5440c0d0100c508503a09a40c82c141962a107504a800074900711034000c0b402030791940001c840002c100f01800003004882040381ca80b04501311450340760004190b85000f01501007000ca10501c5a044d03247d00026030b800e441024a0303655202080442c4200e140d00308031700a1501c049941d11500080e041c00e80e07411a400c0e01c00840100d00300c2d040781e002c160b030120b003a41c1280105008452003408c44508589401040744c5040c000c030f070041408c4074182d0a442002400c034002c04401d0050034050035412035140d00e8120789094207444000d194554007c8001d081644898001e8400182e002c0010642c0b18285a03610b0019640c20340e80d5a10082208102401c0c0039800000a0f000d040d02c078000c2440000d4800703400807407842c20 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 982575206 1250 982573956 982573967
    0x9030b060d060e07080c310e0102072001080708011503020d152603030f090f06090d0f08040c170f060106020a11042009010e060c01020d150602030a 65
    0x10035081c1c1012030015403002080c6540600720085040c0740142aa0b03d04200469040c0300c0010140c500955110003140142080100c841d200061035150ba1000707110036550403000303485000c0205a0a40c0045103032001c0c462707641e0444003808144505004545c1c00d000c01550854021100c0303101041d801d40041040c1a60120340441c1c442442c034005240552501140086440100111301c24148080301030247c240703088111060803007401c0102c0a0803800a8180703549c3c0c0700003403200540715500c2c4040341d40300004000d41480b401c0800181c075014503080baa01640c0751645031560000614030400e0181150040c1362141c026500000c0c403446650625541920b07201095050321113910a40c02c0d92080c541c1e040c806d00740641103035800b41601034514102000454400701350a4400c626107149011020640401300703811110400082d61140e40c1c140040e1041a100420203130440000602030081100660041a030004403140c200044800070900301c000001901410026901c2085000703440e50056 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 982576456 1250 982575206 982575211
    0x708010c031a220c0302090916080702060c1603050d020319050a0209010509040c050c0706051908060f01120b13050406110703050708030a230702060c0c0312060f121e030a09030b 78
    0x85c2405031800c08068003080d00c0d11411500024440781528503000e20740d50003555113800411607c010403050400a805139000c0c03050030782c44040c40e41072194074410180100d0954881d901043e00c11034403031138000004004090a01c2d444100341d0702c1c00c0d0004503214036a109407004040d06a55580c10000070710280710003403086c408804248201409a80f01140c010040b03e006003005949098503180306006519400e4203060910040c02500000c100070380d00d03261a001c04030642441c0c14181701d03421000c8000200440c031a2280c005010208500164440e904100e010343d200301403c0041404051807480035000b4918003c00080e0108141404610b0b490040d5410510001000500b00050042c803846031a01d10000301894440b102005440340e018840564082c000c2c20400b460110b8241450b6101d2103140300c1c45208140074800b2400a8a0300d078101550b50300c001c3c1030841810000080c8542d0340c803001d11122482c4003504900c0400f101e011043d02c000400548402c240c01b41195228200031b40700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 982577706 1250 982576456 982576481
    0x515010e0a0f0c0221090607030c03030b0123160516081207050c0d0503040504141801110405041d010f14070f090905060d0609030f0f110304090b01020708010c031a22 73
    0x203112881b481d540796030007007040610135101e0209100c0285400780950b0307528800c15052200c0781c0259000d480c2c080c02003140e4649032000003555162001030344c503808030a03141d01408034480c5500c42d880003031086c4899000d40300080204e800d06070741d5083d45e8245109685004102e6008105144c10600b010071840710090300c41c105403811300380c440000c00c046580c1300c031240062a20600034000d000410040208402a50500911100582c0f140700300d0548518400d05024690310f03007186c2e0000700303041c02d105003440070b07640240225414070031900041c5c01d90441c240d414060540116501e24098031146005407056286d46031110302c0c0800c920020100141502d400407580107c800000300c03184200d0141a02c01c1d120314010904c0c5000090101a0140461080c0300c50901100da95203000000d89080316a040001728628414800403424400340b588180210b43c02c00c00b0880704030341c2641100d4100c3d4540302e951203140400108100211584407030110802100000c800007070801e41c2c02c0740810300030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 982578956 1250 982577706 982577773
    0x3080d021b0a03020a060b0609031f1d0705040509030a09090c0c0f03080108061315050601030603140312240909030f04030b0603010e0f0312040515010e0a0f0c02 71
    0x1c450448a040c042101822001a046624207404104940c4101c0e280410203640550a113004e03900800c0d0703941300c00070420100f00c00c040b0300d0107041a059001403502c1400c424440f03a9030580d1424040d07496060740203480c490ba0030500069070850001007a1041020240d951844c4589010544002040300d0b100c0c07a010800d44455202c0425098066141080d00c82da9400b0807070f615124145007418400340807003060b0000090601c01082810b49204618584042c00103007035103400f40140e008141950009140790900c000c1400074030000b001504c4108007082c200d25041d41c2d00602030801e81450034404881d48040c0444526034288220560340c4100c40c07004407460107080340c250b90170315089540203d50040d40b071401c000a0741428000c228900002c00c0003044840c8600e0344081d228000c8020b4203081c2d4070124006070600c0020840503901070000c4040b60348a5843c0c0c4070b0300c075020302c007115542081ea05111101d000c0c203496116261440c0e00319070203407640101e50042d050541c0340d8040d080c1040c80 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 982580206 1250 982578956 982578997
    0x12010614071e02040e01020310090e1528150e1e0c04050a3015090b010e1008070b0c0307060f0c120902060405010305270c03070f03080d02 61
    0x804610b600a010109010350291402442c41084180c800c2d0141c219003590041c0144603160141c11600ca00391101c8803004204e08103d001070510340500c1d503103030140100a1000b4400c21880010025800d00e9004100c0304d108900c0100c480259008607001503002034051004009928129088a03004860b032040c04551013560984802c20310000c4c1d5010414a400080070042031a103070304114001d000d034030200c134109050a100042d4607240c0f21150043c8032601d454000402c24140d21850500103005001c0201c00d113542000b0301030850034003030940360003844804107a00c0c03009107421034200d49070707013000303100250038850603051680160340c000910384018081c184c002001e501903400f000d40380020029105039600703070092182141100082c081171a000d442c2c80540c82e804115801d0741c0c401c0c200451152100040c1960380c00c480f01468494000e0040384070030300400801c000030f8191045003243c10f084d271206400c0c0f0340c1c0401c80c0320007080d201042120118005071034010340500007914903c0d54490 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 982581456 1250 982580206 982580213
    0xc0203012c010e0c0a03020d020a080a0c0f0602030c0c04020d061d040501060510020a020405061815011d010207030f170a120c110a0b0a02190c0203060601051201061407 74
    0x21558070344180303000c5810340c1c01c1e068a01001d218511451034040003e004c088410008500ca4403003e0201074003540d65860b00c107080d03480e50180d4400030700c114012111100c280d810101801c10250080807000b00131442c00080451000003946e00a918500140c0029070700ca40400000b984440b050380001c90b1a01070002d1280c450100e107418201e9195468483d503d414a441802c450268000382e02c02c400b28400a0081a0f000840f034a5055041c2c3d40080d96858000000b0401076282e2020241080508204001c404100c035900001540a803a10001d9002c00c5507245280c0840d01d05060050344403100400100b4108004101c15030b01079840c9400700210101c01c100769500a0b0303120004900c00d4501d6442003c120f07c00c00001001c103190060a503c01d0031511070b00c030f0209000241c00644000f02081720390115604031036100b0744031b46954a01d07070002240980ae00b20751107026407107030242d000000d11f0b0354001c10483e00c41c264404240031450f800c004007030300c40f504050401c1a0b40e0400b40501e4000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 982582706 1250 982581456 982581491
    0x90615090203040b0901050705030c2a010c02060601140f0d0603020405270a030f030b011404060306030203300d02090301020328060b091002160906050117060108070c020301 76
    0x940484000942d03079240608040300e1134100130b4a2014079030300d01400c0280490307104050740c4d0800c0a00c41134694401418000012003010741c0d40c02c1807800c040f00050801c404056100004540e11a002c3d284940d444000664a0000003d40d4040c7c20008000005940c10179074000d1160017006040020010f4484c2c01241c200e4108481444074401d800a0b403200003200c0130032414004070448000d0202006a03640148000341c8620440c0c185034a4a44001d0307942e0060a442104a81c01c000d00303900c4a50300e06004001d411244030903402400b680c00707096440d602040c04c0440300e8824054007207084141c440d102c4000d512060b98407254503404d004000d0603a5081c001180174807840e80d907140e101a52514540300100c0c0152556100a2914104200241e1140203a5403070700c070f088139582960740b0b0604042c2d083c14150306806040c20a80040404d25080940c4980306944081e81c81d0301420300041da9012400c0070075070300309012035a414005041c6500c070b6024003142a00c0a0001b007180d04424815450 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 982583956 1250 982582706 982582709
    0x303021e07090c2304031505041203090f020d150c05030907060c0219140406050618010e01022d010e03130306020d06080d0201091209050a17030c0304081605060f0d090615 75
    0x801c004c00041c10001c0c41100d441c03082030851990b00c100401d00301661140684e4000e000e00c3c10034940c4030009203051040350b02000b005603070041c0c50004045070b1071034148480e103030307030380b03c0c06c0b45189007011030603526104d1810b4a204052400043c141c80e0b0900c40b083c0e440703500b500c20880e4421028003c0020701030403256120010600d07502c41d0f12076048010200000d0f10b045801840c0103410a10442410202201e01d55020080a081021242005000407070900302124040c890240340750b4550640350190300b051014003903210000700045801d403270303466071a44214011184007401c5010244040f40842d8010140609250317030010301d003542e6680d0036007021307106641c44002d81d41d200c0303a0300144898420080c0c1e42d80c406282c00c005030380c200310006410036903500900c0540219020102d0744600100212000c012501017140e0310341e41d941150341d6544403002d031040211581c001001803581403070000e0f604071641c0b003104941030070300300d0f080c1200610491205444d440d444044a20307030f00c1c2901c03d03041c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 982585206 1250 982583956 982584017
    0x503270d0c091a0d11010e0d050604120c0201080f06041b110c01090b040b1605012a0503040b0c09041509060603060f081c0c0203070e010303021e07090c 67
    0x1c90700d500e0058484220343d2000c441000110f078075000b0800035903803850f004076801c2e8800b0300b40d0701c0c41e1840d0380104c84400142c8100c1c2d0300b004190900c3c00502000044191040348610408911080e064104440e1520700d460020b000c00c000030302048409501041013644400301600000c0c69010411022540c0c0c1c180c4c0f12003074041020002613000b03c001c2800f650780045000c0c2080e0000b00e00d4260040d6261040e4481c201003900c0c04241007842c3c03694180f00000d07480d000380007448081d4044c4074041900820700850402000c152f450b00c4031850155007034920582c3c10009035801540c0300c0e401480d961748241201c80d8840c1e5030322103500c0c1001c080c2c49560064a003640c000035401d420100060200d8942e0b42003000ca45410002c208407507000060018440c44956035100a1400c199606854041e40354800a41c54040e40303101050007172800510504a0740a035085a50420b01c0300310701403040c00e00c0388048840c3c1d000f1207c2445000e882e500005a51044c0785030069054505120b801d060090703034050034 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 982586456 1250 982585206 982585223
    0x180601030c090b0a14010f09030212030a09210605130606030501021801020a080f0906070602031911090a0e06030f0303161806050702090406020706050901090b0709030503270d 77
    0x80c881c40e00b10b4401c04000020039165440708500b04100342010151040c01c0604100c00078000302e803154490104a0021503010306000241035140b00c13020740741e401c80e01c91000014035405c6c0c002201d80c800340704038a45104202104103032040c00c2d00c2d20b2002d0080205000400c000000d50031001449902c9440f0085006400058232001c2020161000f502c0525020381103501c440301000100700500110f178001107502c00c4882d03403001142e02043c9640070700710700502102d20100802c10b014444c00340704586092407610400602440050003501c80c018a81d107290490381d10b10041c003611507a10022900060000d084842c4810912005860341d80115021300b480020b44001c1c0402e10303000800d0408800d0200780d02840141800700080c00d500840c031019202d80110b41c0814103001d01541203824041c0c10080520085c034003c0c41a82c040d010741c1c2d404591101150002480040c4681c085506aa5128002e145442d0303440742443c00d0a50110301c0c01650340941849141950f841101c0d0b00764803131045c101e5 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 982587706 1250 982586456 982586459
    0x1030302070609060203030a0b0307080a05030c070914060904022b0c05090f070f031805010506121207020108150a120c0b090d0201230a051818040209180601030c 71
    0xc1c204541a400501402640102840040d4010044e26405000c030500000c0b078001400020746400d4485e0b1241415003e403210003c28810048001d1808050301e0045803281903645421380c04440000d0b001002d2104200045036091808102c032541240c0000c00700e42c0d402c8400810001d40003065002d030460700e804030345204200038284c80c41038000c01080790400d0551a00e2a015503416000822030b4081100d20100c200006000307030b11031140503016410480f0100c0c2e45203800350003408251240c1d84154041081020a0a00010103003046800620083c3c144803003580103640070f0300b002d4442544c0c2d1210b10130b1070a4039140d00c14450010003104030080800140e43c10480003904003600240804081044100c06503100e0b800080b0000341e080ca4103c0d022074000e020194643c03070180640792848000a15000b40a034008082c0807450410340030031041444207001c01040d44911141090308a40c0c0e07800003005443c5c44102c00754000c0c60b00c44804c0071407041003142418028240c1046030202e0000f5070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 982588956 1250 982587706 982587713
    0x31305010f09030c03110f0d0825210b030d17090f0a08090d0506100501030b030601301e150b0904080a090f030f0614042f06030f0103 59
    0x41c0c00801070030180100b15268a0781c400611418852401405210104001002e008401c1224502611562003a07800b54800c800c0001c00000702a926031494424100181c0010928461040f400f00450741396154909070300490101c00c46458400f134003a550740d03501e280440351428040b0011000c0c02d0b0b540e00c0120301102d07028129152020b840d003680b6500c00135240c110355200003000c0d1106604051615102c918030800290b90a02003c2c1c01010750052205100301b5840c20071001c01a2002600c00344000c0010800341aa9210244642c681121a046c180c06400d00281c01104100015161800c16210b4903180c01e08203115818415240105204c81d0380d0600070401010103003000b030020700f8807800005200181c80d4040180c07000d40901c0000501401080c050181100140030190a0401c6103960741410b00d080584004207541050801008800102c2070654036440749a0080070308540d422480f941401582201c0e000c011001c0c000d82c09901c1994464014512800c0d64001c0c0d081c1942c110328 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 982590206 1250 982588956 982588961
    0xf02040617130305030402060708070309030c12030e10090302030f070509060405271009052407050313240906061502030f090d08070c1e05011b0c030803130501 70
    0xa00d03070003000c40080240042200036036814501c0ca901454007076165100e6000080c102d02c0303164001000d42d50b0005500040541055840c001c59000e000884040380d50782c1841a440754401100500040c01c0410f41803145c0b40907406000302c0590703131030100d4000c7c0d01e990103c0d02e800414004c1114941c0300e0324040240d0700c1c0240c240c0d0352102041d1814405ca080048007410806840441c5006255000385107800e24081004000001c0003c907070103116220f8281405500c0305030034044148003a0400c00d086e902544003980b03aa000d403110b5a60301d851a503845040f21142001040101d40b200106081c4079081d000c4ad460381d8040b0318464800040840f642d1071304004481c901c0d44034402c11400f141d0301c0d100042d0040213544185810395400ea9071022440006821b0789940f80c4011f00c0f90001242c1801884041040c1800f61040101038600303084503c151601a0a00c601c2458001440d0b4a1181440c0d00c0103906c0e10440d610030440c00a145890751b5994595410072141458a90761981480041c01400d0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 982591456 1250 982590206 982590227
    0xd170c0405121b040b130903030902030106090e100b0d020d03050c1c020d0201090b150a081903120501050d060e031303060f06050d021302030417030709090b0121051503010f020406 79
    0x131030f800c205c40c8410f000441c000d648800310b0202d401c0d40d80e98103101898002d0f04100f00065004000b040619203c1c0c00d408000d00064840141a104420300189035810510401104050091800c004142140d08105200300300c07031001c40400a0034050340aa01108000c1d615500c84003c4981c2e00444804070028981141402c4a804582c10b1280c02004261034800c40c5802001041005894003070040204040128951250111f4419400400020a110410404110300c01c2d40d604202b801c2008005041e00c0080c01259030040801070b002c00095150342c096a01500c1180a8a0a04180248040750207040d03074400c1e42c0c415190040b07030305200c0e41e900ca40c40252200b100c0596102419801241000c06450b403c0002c943d40000860140940701008039150024000015540c3c540321000409000043c4509010320741805411500d41d0f0003241c0843c22502d000c0207110b10340f8011542d04000c0c0c14040c000c0780d4101c2030036500c13125544013806008100c0c00b5a11003d079031585010001082d01e04c21 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 982592706 1250 982591456 982591459
    0x12030910050c1b100206151003090c030803150603091b040e1f05010b04060507080a020f03040311040f0b1e01030b15192604030302040f14010207080d170c0405121b 72
    0x850100f222000350241c1f070a4440c0e205541141801c1c0e081c0900794010b04117060054400140400c1c00010000d144008500c40c1d40340f8034444407a580c1d9002030102034081900c0b00d0000350072521210102a050001c10300c0c07000320040010501d4400380040038240402c01c4101e20100500004c2840c0400d06070103000d0041070030306181131a10f072030300702c00400b41d01031200002c0c100000000c080c51150300c2041240f500010741d03800d49585d1072340c070301d13019059140e91031115000341d04140703403020f544459110f03894841d4405440308014090124405004444280c1024141513483c0b180c2d01c3c250300d9004424501203c1140115550708100410a000131b12102c0c0d045e00300040c0d0f5401c03000d501c0600f42004490704001000043e9511a45816006402150406400d00c0b003982d40004201540040c000011030702a02a01c2009455591480d100c1c0e600b00780540c013207036214000e10140070501031840d610140c01908907040c41d032600d002400390f85403000c505100c2c4d0300408034120ba02414000c406d0401c20b0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 982593956 1250 982592706 982592713
    0x30a02090931020a0905010608160912031b05190203011808091e1017090d0905061b01110403051c211b1d12030910050c1b1002 56
    0x4280000c060b295042000c0d888000c08000c0c003003030464540315050000340c00b42c1ea009102d10768580d44018031101007154400c20700c0f00d003c886858400d00034002502900c4521250322a01003260f00e0584400c1c907451100c4265400c04600c06011074000e10900c030340034810010254030b071120341c01094291078030041c074020203864001250b0001042c0104480380c5401c25030b50308440000440c645018080c40784500c070f4011004001003400d040d44103400b0b210790b20311043c0094494a80000e42d982d1600070642c4000801c10b0113000744070303c2c40c0110145c252012624802111a00344190417400e681c200c2030000ca131f940001c281842000001c1c442d40d0706201000c0713200c08001114440041c075001c44a540b0018a07445072200384402240c90300300b80c82d4900100c000c070103041003000f001403c00c0104031400d8904a8a507a00802c00e180c0242a16040640c20000750304041001d410400705e00110207544042c810200242036480509000301764800307840b02d500f07805921b080c0e07080c020000305110b0f01004641 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 982595206 1250 982593956 982593991
    0x516030e2e0e21041202090709031b0e18070b0c12161a0403020c01030b010e063910020c01060e151e09153f010b1503070311030a020909 60
    0x1950740e45a19500d46d0111021020342e110703c401565007002641018000c2e8004206040c030b105214081c1c2c0d000c17180c80000c5030076656a8203007000780c19240c000d100c048a41180300d007000791000d000080c0140c0f001203c12b8400000d901008914298000c5101c00304000740d880d202070030301c4201200d640c0800a0740b0707032a00c528a40342d03a0080d103840c800d424880c141947c50102816a91048000f2420b0100c0a41150307034036028840340071071003103503604074104901000004800356001c9114000c40349500c1030091800050f02c001ca400a5045122910120741d80c1d400700280d820103403080e95000b884520120144089502d0500c621501c02c61540540c000311b6440c50f61854880440a59012003034400300d0072038800c000d0002d08240680400801030610004601c0f46c410501c580c00c10045000c1c08040b1440341e0910300c030b20b01781c407404607030280c3c44070302080060701c0e04500c1c00055500030701710719000540c02c5c07900c0c0600d000b83e00281d41011095034003060310342d501d09124030300d25084180303d2112100311 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 982596456 1250 982595206 982595219
    0x507150810060f080127090305030603100606090905180601060528120209041103070e0a08060402010203030c160f06091b0509060409140106090516030e2e0e2104 71
    0x1032006204055619080000684c182c0191140c0d0b145a074414040502005500c0e0800a006400c00d52f05c4d41e11a005075443d111f03108400c1c2c85802c00302e40c030b40c2d01c0720201c140c6003079010b8005040c01010b01e03080551000b1102241281440303000d0103048907403070300d079103c0c03a80001c41d03000030001c0014044650307806083e01c611039401c174203a15981c030000c00c4050381e55000d00c004100a4010050b00800382c8001105000702c1581000410004620a8800c2a02295100449683d44205a4000c0c0c050703002040402e00c8640c4140040000301c40d40c40d0320702c40301126643c0e034034100503150740b041c3e901a646100c0f144c10020184400d41c08591030f421002c21150619001402841000c0c0030a449540d4495070303030341000070200e4600760140e248402004040e6603050b001000d4102125202001e0116150411200303020b803054440511580c030040502c0100755031310660311050340b41c8200310361441c28180294150b00e0f008203410007482e100a04101d101181900784141144102c410b51018184418000d9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 982597706 1250 982596456 982596467
    0x10603020a0c1203020d05150f060405151b03070302060406110711091506182701031b0b0c0d0f0512060402070f05070e070e0402070506130507150810060f 68
    0x1000d820000324050201d036000107800901c1b03051003114800c0d040608001c0d40380b03d480c1d040c8a124000380c980b0f1b0154200d07641001041d1041d0f01486034401c020a110030104062007001c2c00d07124051005840c01401c5010560345150840c140c21070045e0f0240040008209003070207140c1c0400ca90882d003a04200c0796950b5040b0f40707a0305008007401581540c0c0010b0200c85202601c4003400340c040c180a41d1810b020f0700c220598031988444601480e1500c401c4008045030105081100002c40d540000d26400c42d914103a0496a107403035055410040301c3d0115001c05000000c00b100c189520050040ca181a0805015204403120207000c2c04414451001c0001c0c1e403141725039000130201e800503542c4c0843e180451138241c40c0351003d812880781420102c0c0840c64620194000e46007038030b41c94001403115040005901c22b40c0c0340280786801481c017049810b03003505d403042c1c507c910900c10703141c82d5925540c08405c1c0300b100c080341c40300080b413030b0b81804400c8803590075101c0544640d1400c4800c100044402800 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 982598956 1250 982597706 982597727
    0xf180126070b090307061e2d0c0204050f01060c15020927010e09101515120605060304080a03090204090204020a09060e0d1a0c070213020901030e0610120609020d0317010603020a 78
    0x788171000504042d48840910f00c8d004204070282c498a45008090005280359840305c82203003d00d2401004c01d02511040d1a43e504940c907503030716003030b118400355243d0a44038030b080c8012507595001c0c0080318080c0d4030411001e000d45221610b40c0141030502d808500480c406078010405000c0100a0090341340c4003080264400c98a0fa00100340005822142c48803c519584030700342581c000680c54469030b42c80704221102ca81c80b00c00a1001d076442c0c404022540c40103071401480c80d0020401c54108500030707008240e15a00080000038079208a4021078166070000c012a40080c0c0f691405000c0e854000000954403882a03507202e00e4600c0070303607603a11450516040c8140b00941c080c0025086140041101e038030320780c098076a00885011510303200c0a50480a40780340820b0904003092541400001c9282c0300c2c2c0030700b4032058501841c0120218820a100205980b440c0e114540c120240e00d0761411241840d110340d9458440360901444118038a03c10380041d000c01d401003010504142c0d21141001c0b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 982600206 1250 982598956 982599017
    0x6030c01030603082706130303020708010209100e01030f1b020f0118020f131a040f09020307030204021606060b091c0b01060513030501050f04020f180126070b09030706 74
    0x4c05005103841050001110740145e213074081000a280c0c4000c40b0540b680c401120700c66002c644650303481c0c014541c280e0007030049070740d0090300360660b07007996a12560508681d4101810f0000750700400101b048261000c403142d22101c0180780c040560386071341c1048082800e20002c0000c20001d0848020324094418059001c0d11900c560109140c0350350741c1a0246c0e00d17106c8004001c1180060b0700b031590210350100c5480e90301c1103140590320260700f185800781c0c100d40c5600401514855066508000080d0840c0300c4d00070001d044034400d14001419407007840b0280c906200480d444003071403420003034101e0b56400000c0b15203a200c0c0c013410000d0301d266190b50640f4414140745448006c8103600c0e480f41c244984c009080b940c00c10003442020940b40f24080d00403070080d9400c1d10100300e0035040c800c10044100203145415a07200c01000303160904a00041001c072814404140c00e81c01021207403505820303400c1880161000174001c80103180401030359004000c0c3e810058009044926000201101495101c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 982601456 1250 982600206 982600237
    0x906180c181002010f06050d0f060f0b04060e06030d0302040f06030c0e091602070e090705150d0203040b0a140121020102070f08151e040215070203060f06030c0103060308 75
    0x40d05510541d440c1d86003041c1d025054001859280c28000c0c041d1002e461485101880e0980106450a00409080d9102d4000b1604041c00c0081d5960400401d0700c0c0103010056a500c5615040507500c41c0a40d40c002c08108540c0e0202d824460105070030a40c40658000a06104000c10009851540c0c0100d0440b1041c1c00c00140200021030203840301c0e9000110582e001031044104912300444144511001501e903003220500e5480b006841002d5100341c54001e4103500400080085151000140c0400c80a849045017050b400380c07202410790708240d604032010389804007082a40d40c01e5114405a9689140030340500d549050b242201d1290038000310484002c2c0b105200f0250390003045014001e00002031003494035075840090580b18204150034010032010080480c1c5946c086104100b2003001e440741201181d111a420001624200c00c40c407116208280026005030b41c0601c9400e104d47c82c3e070b49040c4074906c1d0010816040240054a060500d80340100a00c0400c480c20182c82c008039070351016 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 982602706 1250 982601456 982601467
    0x207050a260304060903170f0a11072118051008060103020c07090209010e1e0d03090b0a02011a011d0f030726010b150901080c0409020a030b0906180c 66
    0x842800165051841c205080000030b1004102d00c9901040c210b0340aa60b400220b80e08905844119035803d4803040c002042e04400302e0300709002070b404040070101502040f460000e5036550030200b8a040b0b03d4146501c00c10a0b031a1309526001600f480000d2901d00b501860203080400161305840c0000c407640400c01c5d007000140c22640640d040b51811500c02e001c90381c2880c4e441c003196000c1d5001d000c0460008502c0074000f041c07400e154806c0c183c0c8080045030400f82d90302d0076007405812100c024040c3c0400884a40004424882c90000c19100e021580081061010440102c8010b8000120070303040050200c0d02400c002c0903442d40c0d181002d000c46140209090980000e40b820f540b5421045010000c03005a82a103a41e5184080c6840c001d04000d1100f11440300400c10b900c005c105260707196038030400c13000030b5a42c410494140c0c018018101542000c0e2a054580d040b0781100194501003651a07035030706501d00d0701c03100f407990091048a50f426409580381002080d003601801c0305018400120740d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 982603956 1250 982602706 982602743
    0x60e100b090f030a05011a010e0f1507150605091308190203040b0c030306120106030209010e09010207061d0127020d05010605090408040e0c0304030804021e09070f11010207050a 78
    0x1407030b00540c000904071128680142415802070948026007055450f03000295510355024031400080030034020114420a030450043c0414110100d11029502c0300800c07039040040e020030742025610014000001d22a4240f40034809c6058001c3e0001c040700e10240308200011303a03140c0c2118a01c41200742c440c80900c0c903004d41a403541c0219008501001030204290740a40c0b00080030358800e40040310100e01c00c2c6042c41104c1d088414500020390001d01d040010302010f40300010140c0c03c800c04a000528080341e40d00e500d802c4482c0e01d0401c10000d4104409444e41d00303801d01986501d0742c0c507143c02039400000c111400b42000d030f81c1d180003800f0b050100e00540c00d20000394404801810050070156203460645030101030b640c058010054043c0d4003601007184031074018150b911032541503c41081503250340d02088800c89910030000c00300e00b0117040802e00c684610740e00b01d02805a07500e07580001000fa2001810f58072458914000131b80c41400781e0300c0810800074030303c100079422000b1041000e89128 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 982605206 1250 982603956 982603969
    0xf090415090e01020a02010609020c060f0421120f0e0606130e0727090c0b070204150305030c0f15070f1205041101081e04080a0504050d0803010504060e100b09 70
    0x20300000700d1500e05070502008100640050040060903402080041c2c1c641042c6012800380020110041d40501e0025691017040140b941d04240900d0310420068103131500101551280c0d0409000151519050400d0301d01740d01440720600602d0383d0501006032080c040607580d06006280c0b0f4802d8001c4d2001ca0070000031075000c04903410008065461690300e0b10090940010307440d0b00b07450506861008094800054880c0a00351603014110f5007070540b80c1030f02201b46420120050760304c036541e207102d600d1604021440b40e009520800103580c07581e058001c0f050400c0c165520400d495008861540111004d144c40241d11080038105000c80003040001240d45503002c9884850051405041c007051007400980f2460041c4260703281895039580c0c0041000c0d20040e2a40e209007a19200042070010f400840600581402481c00c00e041958503c0000c100c1c01802c1c0d01680e501d0400030041c062402c0600483c800340032688000409401c0c90401710f24820010f21a002444001094820960b0b440740c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 982606456 1250 982605206 982605209
    0x8041127090d0f080c0418060503190606080c130c17011d07110613140111040f0503060c0d0b0f1201050f090d020307020d02040f0e061008030f090415 66
    0x11400d8814508030100940c2c805003480948040740d444a034500754580702c0d03c03600d8800c071450610a410580391040d400c40700015800b56010355a11840c0105464804011691501034610401c1c02c003050103052900c200c9166070404145034102103415462912419034003c7c2c841c0e103098002442c1054400704940380d40b81040400742070340004000203400020b8100a048080700180c5510280d11911015548000c420f80b03000015003094000442c0309a000b102d07034103042e01544850120350015501a03003145c5054183d0b841d03441e804103040c800c1c1a0505d103014040d0400b54014901800c1c40c03143d01180340a6480340c20710741030700e400b000d40301525091034500701c400021708220786540504110a01a11044801d0080100a00d001030302070080010f100e1031304480ca402039485c003442c540900054291000050382c2194485104283d068020300c60a910b904048001c0c0056003070800080304400c4603580201010f60050140010f00e094017801c0324164102260000b03030603d450100c40054100c01d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 982607706 1250 982606456 982606519
    0x2092b0c06022b0c020d05100f0c030b0a0302030c12010f0903080403030f0902060409020a03060e0c0c100c173612030f18030c160f06080411 62
    0x503180001032840c0c0009204001900112020060b981403440111601c103034a075280000990320031200c40036081101030707541c1c6d03a8051410380d40c00400074041d000039500c4050911103505d540b14214002c040c1d042c0705400342030704210f5040103490300c2d44c0c000079039640005400c0c0744110000d2060f030b100010254032443e514040c18074240071000c10703410301070003886048805034046420500d221801d40281d2084021a075401044241054101000c1c04025008481c0c2c04050544d070304400314510040c0d02d4032038485c1c031111500725510b1400480721810900350b40d40454240c0c0c1055143c54509070003040039025040340a42040039942c4039600032040d5042c650942011181c41c200f900c3d620f03e02240c600300000c419008440c070124802100405920048420241505c10100407520382e1304841c00228030702500c001140d04100400400a080c404600614140c08880440401c60300e500c0300240001400a402c01e81d80300d161984a10152851014045115641d2801241d02000c5c80c0300e0050300304580c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 982608956 1250 982607706 982607723
    0x108031801091802090a090e0709050a0e07080706030e071802090604260607020a0f0b040f170304060c0e01051801021f060e09030306101d090415060902092b 69
    0x3000d0f10b4580c0254000702c0078502034034960354042400a25030103842c030103100c01c03402410050f1511070200f0007031102400145e107103a02e44089902c0c458040017088081c002c1c00018100c001e01d0554044c0480d00c00c0b01c10201ca03504042000c120180a0040600307490b418414056510080c03040064024030030f54010f05103845d210038031818049c0d01000104001344c085001c50315103440307500c4143ea80f00e0b042a00103100d103040c1101301c400104d001900f9038010f441200b51a038110f900d5074039107a000f0002225a50322800210400081c080d0714061107001d40341609048402c0100e01c40000c00c5845103c0224038a030040c560340c1c0c02c6503482002048003050803951145064903071054920080e01e00e500c600402803a50001185a803240482100e024840092107031545015220701a034004840005072440e40845d80f10000d090b45034488881d1040e44a0004850b01c002d90882c428100c40f0b06810510744a031041c000c4c5209a03d41da081481d1080b94140030068004034800c414800d0700710424020031064 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 982610206 1250 982608956 982608989
    0x5120c010b0a1410051e16120804030806100e060313170f1c020405100c021c02031b04020c0f03270f010e12010e1605030303010803180109 61
    0x2006502081c4141c000322880d40602d50750f07900312482e030074240c070900d54001ca1019900fa07aa0307000c1c0c0002d01144200c40d02044602c0f59080107108941c12840c0620450381c2243c480c0800c12140d1211420390750458108031300c09061a49006081d0000104000c0c06140141c3e000f41031180031302c2c48001034900050950341d49142000307210f511000358290845403042c07901c9026005214000c15142e0300000c2e9070034581814080c8503904c02d0704280351000c2c044103500300300100d4162a04080440c1c14001c9449000c4100711a1061005007078903406189816000c881c03510005a1340815400480191800111414128100054000e02c14036504107168071602014401e00d2401101030300c4044424003107444100202c00d0031006012402100756071002c2d016181c04019030103400d228001d4140031b400400100760f4120380e2401c564040040e02d20b0b80e8013400b01c5842504108001030b0103048182e000d141154980084199240a1102c028180d2070b000083c94650741d10070701007200140610600c015a62 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 982611456 1250 982610206 982610227
    0xf020705011a0a08030414040908040807091a0409110120070f1509030f02060d14181002090a030605282405062d040f05031608070b070512 61
    0x354100002c69005840c01d800004080c08007009032411031746201c1c0d10020201185042000400881e002180e25040074080400e1000040143d00c0141404080000300781d40040b40d00404041110035151044d424503540d4400034000031600b000c01d00c420f003070104034091841c590f030b00e02c1342e03080c4501801446560303000625062050150342c1261107001c1305040410000341d04607025109400081c1608917881072510040c24228000c2c1881680d04030b00003000c01914000c0c0384050020303905281c0001c450804a90344d18024025580280c84100d811480c01c1555404241c06441ea803001800c0b0075954400201900b070160303030714054540d490300f002011030a400b124200030b1040f142210800d01c3e62814070a840c100c800d5180c415101c00a060750f0502c001c12a001700c403000b0940c1d505c6152119030203080b0146941d5006440a41484c01015850701d0a041c00d00d07207040590080700f80740d480715040c2003021203000304112080d1418100500e5640c2c5d82401c01c00d2401a2070640480d10510000321043c01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 982612706 1250 982611456 982611491
    0x10e03011131030201051902010219030b030c030705150f070f150c090f0e18030c0a06180f030f0e0607060507080f04080d0c110706020304061106010609090f02070501 73
    0x1040414211007820301e80b80071aa00000240c00300078003088041103030303501f07807883c1485007418811944000742ca04618a0070000002e171200c0c0d00c05020030340398500c2054501d4244100d501008013580100641307840e00c3c0c001420310508800c208828400003903115107140c050001c841344c0036001200626142407514002400744010b41400c2d450915140d90481014892585030080b07800d62552059943d04054003004545c802030420086160040960b0441c010244094402e0f1001c5002405592100707003095001d03642c80910002190081b140007200041e50003041d0080281c0515003402914400d54042d105080d00e87c540a6100310041424410094a900042d20400035541c4828140d201c05494200c419030568000701401c90074002d04440c1e0b0010381c0802200309452801c644180e02000d400b5040500c0c6410800068000007424001c842d04000b0032400d00001c1001807000790324281004000c01c60b540140e901c11070325441c000c1c039031074410b806503101d2540010003040380120f03000d0345182 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 982613956 1250 982612706 982612747
    0xf08071b1a04260403030816020c0907110106090b1e03070909050138190306142d010501080c04081c031109150a21090618020f010e030111 61
    0x4420081120403c0d00600c0303c0541c1e0460342e060715007402c0d80d115000c4480304d41e40fa50003400e0442c4105140240ea0342e448405650082800d611121107900c903450340c40e420b544054200700c00c46030400c582c01c00e085c0c039981c88403d41202010900006200070f100001c2c01d012a82d03128401041c10209030b081880010341c804144a00102a96500c1056101e940082d141004031403082688880d80c40310100c0c14651406446403480040705801d00d0b0700d955401044941601c00041c0c1c0780f2004d0100080383c8128109608004549600f6500400300c0004a040c00300c01401424100461007011620018500041c2e6014001c45004d490643c0810f20300b640710129403200980000e4200400f5002c3d001e809012a01302c04d401a1010030f9001c0c088043c02400e80c09026000c0420554001803806414800840f100d0340c80d188101098500541c1002d105450419021006001d4040c0d00000107030f840a0030303000c01507001e0a1040c840300e0104002401402029000787c41200006003110601d00100c400d081c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 982615206 1250 982613956 982613993
    0x308162103020c0c220504110d0311061509010b0d06032001021501151d030604262a01060308041508091203010e091c0504060f08071b1a04 61
    0x8080f030b010b0340c04214400d002500c0d2400c600985e041103020b648450b4100541c01405501040c4584c040c1c003000c01c00f45051040d05030005041494900c0980d902488000c0d00040207031503100c035580003240042c10941040c4542c0b01d4600001408159203456a08400011500440030744031a8075400c45044500c00284036180c014000c0e00d00d42924088040d8210f4180c80450b2115445080d41410590f800d10300d440c1040c850105401e030203030300c03513504000480c407441c810760402c4030414003000743d81179011414914101c80d06090200b0f90304140320003009140540ea060740d154038420740c0c2d0101401088150800303806800d0004003c02d1100180c10070559080507581c03401900d80e03e0341441a16465850039501c3c402d0300800c0108620940c1c100655000306140b41510301d00d2400456000703c0d10101442d40c0e0104501103002c1004c1608411a100c0c8a881030401111614024000512031810303070003c0d00030880c40a003640c080c13084c3c203c9211306520100d03054400905150601c45030070440c0361030b00c1c1c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 982616456 1250 982615206 982615213
    0x70b180712061b0c170d060e310f0f030e0d03030501050a12080405010c0813030f0605060603091c1808060a060b070510050612010f1e060308162103020c 67
    0x20901e11a00001040d140c011845480c03005a01c02c032000071b540101c01400c04540c0b41c220100d104005248840d020b808005d01e0072031111003000c14440d0a42501d06400703040c48401808501143d102405554a11741c8091000444000b5240a81e1003001d20b8101940001c1c03120010001c154255000b40d0507100d003212080400e984c2c810180140301c0100b00700030300d036100600c03041180303500078104484d041e032040c0d840c0d40c20821a4140b00e100000198010f45929170307040210414072000303101e00c54219409542c910306c0d604d0300510240e59002d96040f9011440c8906102001240c400c01c004400b004802c0005429259203010b80d680e610000d0303032620381c0300c0d00e07201c8001101c00d07a00d811a42e66590000190400c506192210402400c004100d2900102250185401007400307205150150401107800502d03000140c1640b0352040e41c4101207418189007403028008500e40307009a809d1003024040ea005007203014601000ea003100826003003112600c107103491111540540280c5800074841084 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 982617706 1250 982616456 982616501
    0x2030f01050f0a0b0d150b30130b1f06021c02030a0206161803050307060e0105130803060a15020706021510051009080d0e0405010b070b18071206 64
    0x708036a00d0f810344514820f0311000c100030110607103190130203801e00c003580c4008400c40399540c4440700745074055080b142040c108038601110300703c200a040d00d4403503802c040c616910b10f0029040c00e08400302402c05000d0f0120308000031184124034410600940704209900080750fa2104007a617200c0302c140228004685c207036400c64402e40300005480c41e14001d1ba00030601c90b110389100407000030042a03034034204440e00380780000703841c5e114548100640c40f80000750341e51906070503c0c00c11600030720300a00c65030741082e0038851045141e201c81c1c2e103480e8000600a580743c46110025a00c0c5400d42d1200140c80304401c0c20118064001c14403a0807520241c00340c900010b1110b070b00b911442d00494080404011072032042c03001c0d0400301c007030b00d0b40e000181c14158495916016041d00c0c00096040c030000007000145240c8150074a4055140100300da20452410483e5030703560b07111100c0c8010894940002a60580010040100182c20050003a081140c2a82c121402c011000d0020490881c0c080c0305030420 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 982618956 1250 982617706 982617709
    0xa08010504121d060f0c0f0c030c100e090a0605011103070f080c01020717040512060108030d020310090507080f0f06010824060d020901140f04031509050102030f01050f 74
    0x140c0d48625402060075070207246548055480402e002c40a1011001c00c225014468070740d03038001c2883c1d01c8580780d8562518045942140f42c07403c1000f4004a0340c00a034201e4105480025507058089400c8521018100b5249000c49295504011150f44920354009200c585001a8050020382360281d84031440260840b100e9a903c0c03003041c074002d0008144151410100d010f803000381680760700c00d00002d40b40022580f1030306031a0f00c40e81244400d00c8000101001145001640583c0b00c0000c1030140a4071742c03604880f40d40b03902a580210700c1590b0000f00240d41d01c110b0b1026500a040c01d85420400350420b210b00038880c0e54100c0320444124007907808101c0000b418201584500c0050b95285640d6036250b003001c00c1d56680b0800ca1040000f029080d500340c1c1c0d00c8201400000075510001621120910300040c1541480e104500090608000c040090460304084800380ca41100c4044100e0a040b03540c040100015003025141c1c0d4030120900c41e940701200104c0d41210350455060710003030325650 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 982620206 1250 982618956 982618961
    0xf0a0f020a0506072f0607050610081b280605031e04020d030c0309090c08040b0c1e0717030c070c0b0c1906140906071b080d0b151303020a0801 63
    0x107008040c0c121520b01080d0110885841703001c1581024000019041d404100300e60001c4404440390b0304400108084042c01381344104c0180780380c1005010040c00d4000540e62200c0c92080b10340611501000c410b95111690f100020f0050080145051143c0e205030042940c0c000b0364504080d0b61210003001d54620b81205054041d030340040102040b4441da907003c1d90541031810044052103640e00000444903094403400303070000c049032141e090a1030300f4a45030f60f582c1001000f24030038280a00a2501700c12203481c0c104082607a20401b99503442d0781c0c0c100310852a0382041c0007505440008100a20416400c02400301e1030300c14441044440c0d00c41422004070b01941202d444650701444040300a0302030b4601c10302e8814002d410004001c000e2248441c41c0240072102c0303802603808101440b03e800e505c0107880c500c01c40700007560041c880e443c1d6a45e1a1500c6100449200d99440740c6196942c4c2c2c2d2440003201d9a080340440c60303699142ca16203c032410070054032041c1c0c41a00101400542d242d07060 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 982621456 1250 982620206 982620217
    0x180f180f1104050108060a0305060901390503040309180207061401080c0f1804290702030306090a0f091202160f05060a1101020a050301090624050a020f0a0f020a0506 73
    0xc41814105410f00380112020b2800070001030713000c4c0346101e000002c0b840c00c0c440140101404000410203240344070a0b00a000449400070f183ca1315154800d44003002e52000c1e001c0c5000c19840c00d9540c6e07807150301701105c20740342940000c000405010946034034200164003c1250611410062203441c202e100c018503019024407034101e581d040340281c02082d140c000740e40c4482000c0101652080002020280d0280200322400c4441d028084d40c10a0303500c0c80b10004d04150001d04100e85103602e40414000c1d203900020300385500440140c0003184494210f5040400b80900403032040103c03100e03609001c03000300c0712035401c04050b00606104078088c3c280f03a002103054805c108800c0101c5841d1a060000d80d91025000d542044a080c62642c0700392800e00007003400c44030303554400d81c8950401d68401c040342c4c620782c00310f5032a18601407015200c400301d080c400c891341c03407608090361034400307118040c1c0c10a0030703e4801d1050340c010300c0a01d8041100b9000f81d0006507000340e460429450315042489400d1003107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 982622706 1250 982621456 982621481
    0x30703021b0f07030c0e10090b010c0c1d090d02101a1c060606020f0a0809010c1505040218040f030f09150c12030504170304151406030d0f0e01180f180f 67
    0x31f160140a4181c00fa00503600c007103018508515408001d495600d0742840d580c02c60788003001500d580d141d41101c00585290000400809045080307060540030b5555440c1c0d141c94441c040d140c0107011000c1034240c0d1040c1d40100d02400c071441051100c11850300c10116013000319a220f00e48200400c401d07100061881000c0c500e08010040c1490035103034404039400c0031140c14100141410810001861100a00b00c1007041d414085082e0410348104040b0850710329900c180481814104804106084a4505042e405040c01d0b440d01301d4400e030440359480f19400200030310340c0b840e1150300c2480d407001607944803a00580102d44880c03080c0204409172842501d001d0280140808032003e020303145001950041e06c03409042401700754804d050340c103480300030031103074500181c49c0200304182c107003842032028100181c6420100b402d040c800140c00d0322a0721108604100e21070323504500301c46001d466040608903401c580b00c5c405649126414111076445410002c2c90f007890012800034925008070842c9801 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 982623956 1250 982622706 982622731
    0x3050d1806020c0d0c1509170d0c0b04111210050f01060e060a110610150905090112030302122502150403110a0c0602010b24030703021b0f07030c0e 65
    0xc010030058013600101055480b840c0709000010010400410204c80c190280c44003aa094070b0040d111903060b590070900101e40c3c101c10700380510180d1000c50308040c43e6100d5090070301a01d4604010500c061b402c69403541012480010781000740000640000444031207409015994500003001119a001c0c45880302003000081203103118034114024061030100c5103400204070542c010b00c0da01d810401d9681004084110409002c81d035481c0aa06070591210300b840740c9200d00e4075002c50a04d8605114a0030100c201d0841c0c84200351103a0111030054100c401881380c242400c000900c00134001800d01c0c041c403890303921903282d82d500103d1118070102c2c520040409135035450300c050300c41c0c001c80000a0820f014686d00140094180c0c1481d0029001a81c000a02141404140415078801c81200d498914064042401d00680d0008907944000c041c540075031210040e81c515400007d10200d503403c0343c000d484031104001d2001801c10101d900684c103408403281d03031701c00602060005480c401034002 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 982625206 1250 982623956 982623973
    0x4330b03060f06160809120c150903010905010504081207110604020f04090b07021c051c0c031d012a08060d02031606030b0a08120d110403060603050d180602 69
    0x6002011034401e0b0101070019468510880c80c800d01101140c2021105c0c43c90110741c0c1e240c241401010301c019546800010000c80c1d10040c000740a03a8048044400e51800c0041c1000b299103003034201040b203d90010081c406400c10f481d0040300b0f41c00c0010040e004900347d10004492a10404408030b070110084007804040d1101c5d000d0180c0301c040c0d00d4a00e608251121504400210740402c818441d15035030303005d402c0040d4402221800d1f0004810701200300002407003540020084030211403940b0030707a8480003641c2c1880040a42c041e041040100104100040b0100c4001d40103400a000031504028200507900701801c04a06c405440505000043c003010700184003400c2405241003042c0c0010101c40c2d118404810750440024680c02c0070001070b448001101c503900304000d822000c0d10340c540140c2240c50002d204c40305940902010300504a80341c4202c00c1403000e4060449002e15040b500c14072040b516030410b00d40c2c90002c030003c400080c82c0c28100502c2c58a1032036410013580c120364064040780 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 982626456 1250 982625206 982625209
    0x106050711060c060a050106140a0c050f03160309050a03150203060a0e0a0603020102120703020d122909060406051e040e0708150f04030801090c0e04330b0306 70
    0x40e00003500441d030710a201d60340510995603040c00381031400320007002420a4a400c030b0b0700340140c61040c0e0024041c04007882024214031500b1040c2c4615240610f0b1403042d0a2190600e14501a01008640c0d1103000000700f0007010328540b842e800810f8003d8890802d560340d00c40c00c0c048240e08610028092b0306075001d03902c0210120750001c64010710000d01000d403040d142e501c1c44112a1080d590500d42ca13698040030800c41d40c0503c40020050b1003241e8803420485030752000781d2107030030001d060380401c145600c2c003002c02d00d140d904c500b00d007100300c10607a4940100101c0c3c0c500030701d03102c400061103005214000b50180c9400d000324400d0362405440c0e41007600307803c407180300e01c0d9400d864050340c4940c441e2142c0003040c0e010405500140720a0008010301c1c01024810000304002405102c4440320440802011030b4000300e03000c1c116003a0100000c0c44003020070044131440e685002042d4868209010102d03c000100f681000f010440918100820182d000c200d02c40c0712a4401c012900d102400002d00a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 982627706 1250 982626456 982626467
    0x10b21071a0d09020d05073b0a050921070b0115021e07232b2613180b1e04090203030712031a0d0f060225060c0212030106 54
    0x20a0710241c00328034414102d641d8071f030a21603503801c5110221301d078a040c46409414920354050385044900102e80c2820301d40d0740c52540c01030062440942c9616000801c1c44600200081c0d000340031250b5110901c008013040417445a4000007090700c1e240507140000c00c051000759503c0701281c10a40061501c400c5000300055030b0b5800c400044180d020700c150001c0c010000382e801064110502c0f80c2104c100350341c02c00b040040c4001181420a603401507400c0d040c94420081103130413ba8100e40c5040c0fa0600300b41e0002003602c0c2c801c0d01e0006a15008c1880340d0341d800f200300040291005062000300145410805100700d50400c44003035444104042040c0d0048a2038400b079000100151001c1110310454020078038541c0030700801c0b50403030840d10300b00701d044d50300d449100244909c8038280a040c071034080001e545103111000192190b0fa0101d628030800001d0750403034254081b0300d500c3c89956041c07206140a10200544240d176245d0400303c007510503500c045800000c0da02426042425079007085030494a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 982628956 1250 982627706 982627721
    0x30a150b090c09310207060f02030709090f060b07050c0301050624030a062d061704120e0a090b0a050901030308220b010b040512120a0c05010b21071a0d 67
    0x1000c20f1049250404c1654841810340307401011030015a4445042c80c0400482e07a0000400b03040300d10600904c0301c4507500406144c110740815402164030080410014001c100b9903201681190780080c200041150108080d62615030860003000242d40306424004c44c20f003034540c4a8400480d10400c1014070398440007644e0032081c410000684191500c0074040201880c410503003425804141d0511950604900c28014000790f2410717800092020052806011011b40b00800301c0d400f844268800c1d0f84900c64006190000074030300400203665106c0c040041118040240c000c401011000c501810903090742812241d240c0e988030322958a040036010000300101009108011414841d00460600c0c3e003121f01924001c1c10702640e9a00e484c00b04212038003d946032000030307040080104c0040030310505035000c3d24003600f001d025018852602d940107282e040e629550000440040b2100881000c00018040610004070f48032a92107048c0300890040916a500038098100421140189103402554 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 982630206 1250 982628956 982628989
    0x1101050a020109080c1e1c03020313150501060215160807050c1002031602010c1d01110102040e0f091c0e01050d1b1d06041a0702030a150b090c09 64
    0x83e089880d03a40c1d080450b44145010302159000b01842c00f410451070045401843d0b40a0051440031000400075803116480d41d141800d0550120008075000001c1c007030700015991203c01210b003400c00040c0400201400e004200042c890b8a40c0c0f20041c074400a08140925050702c2e0745d80150a806004403124140140400d04200c1d050020321203400302042028182021004c0150320b03403800c104071000100e03d045601c01160b04001444001b075400010a01080c565994140d280100703c60050b2038401c42480442000c0d0310003c5c0c00100158650350b07190003011400952030098a8050f1003560701c1d4500e110796070295101018200030781c3d02400c04000031070018105503062801400c49182225600b0402d0309840d41c00619118409510000080c814462654160226804480400e505010718014203041000d50394020508400040a49208035070040c1155501011841c10400c054941d4002e840901c2c1000c040d01c4162030041c080b5882031304000c500c10300f000420002c00130014410440c95 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 982631456 1250 982630206 982630211
    0x30615050702121908180f0105180609030d02010203100b211312080f010512030909040203070305010203012304060b0910120e1e01060503070302130e0303040b160207031101050a0201 80
    0x11800b99400020310542d42d4085c441064440200440503000300703440640c11b6200700b2280460b03128581c0c00c0000e4030610321654040b50b449041c00f1001c10010b1040481c07640d41b503c6034814441001d58150002c511a02240002e07280311944d4080d1041d440c0541010300b002d0a1143c000038100c5102003c2c1e159000c815014850704c400c499885001d04e101205c00580002030100b420021070144020f0400e005005c141ca40015640c1401c0c0c0301e45c2c982c000c19000301e1094040e0400700f01075680400240018541100c021962969901300b5240041886081410002080d9a4a107098580340c862001164400c00219181a904400700042020f940c0c02d40c00030f00c084036800c5400018903104207001040721030003d02c0e9050740001c0d41219400302c45004000d580c18401c00b40000d4030042811421640c4c19240750351640e640b41640c0010345041201040c05200200402c014820f0880c91a40150041d9816510b0381c0c00d09031049881e240140405403100c00c260524000651041c1c0040405030107a1000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 982632706 1250 982631456 982631473
    0x304080d1505101d0d11190515070f0b0a0212040803061323060d150204030c050d020a06120f0e03070b0f040308010302010f09050402031603061505070212 68
    0x5480455884104610804107440d00030702c15800c0c4030030302180c40d189504049490360141c0010000182d0400d6441c0d018444d000c140c3c2d000c10107602807440c41182c0c001c05086c90401e0812030098075541e1481540e1145080c1200d07150392080303030402c0343c041d2504101000503045180c2c81d241c2031030030090164a0b05503030030000f0025042d07a204034640680e129025482c1d90f0304044080007000d001a0100303840b4640f03042c421145a11045408200c1c400d02c20140601c25070f1a0000101800800b60014000c00500383c40754040c290300d5801401540d10a4990003040c54454061200001c0c20f204020340101401005201c45030042101500d11408030030045400070740400c91000b074401817690305025502c040344c08010020714001c00c40d03001c105209024035624240e240144103000610019042c4500380302d41004843c4140c1c01c10307001c3d110140040d035490904980249440c559484140002031400001007078a0199841143d445101d43d911941403c00603000c2141c10300340021070441c01d218072800d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 982633956 1250 982632706 982632727
    0x604120c020d060902010207091514033f0a0f0e1f0207090e030304030c11010e1507060510050607060f0f053408040311011e02040303021020030408 65
    0x82c008a07035449100d011030b1840081c03002a1400000c0e8001041803402c00e8100ca00b18240e5160840841c0c54018042251202c040301290034500910b400c0900f501c0b00108464011003003080300d600d4264013908003c4061600c6c800c08206000300c807004800205c0c2501a1040103205410244040340010107130050b200c91003d0716901c2e004a07004c40381c0580c102003030030421400706220740304240540002951031841d080d07a0041c0491101c0c40002e0849901c4480c00c49180d00c1082d00c05825071003e4102c4005034543c3c0186800c42d000b80000b1250705007440300050a80c05201290700c01c980c0060b2500d402c08031140c4d1094040c20b40329045034421684d507203851165000e6401001e000301c021030402e84a001d010509001e200324640b84003800c02c90301d16001d00001d980161070079802a0140f0f442003401403886140c0340503010581c4180303814401a8034040c20324445900610403640700c1c0c0c00b2502e0409464651106a906014140303c0009040c2180301c21180c6d44001198868030513000203151115554 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 982635206 1250 982633956 982633969
    0x190809070f080c0a08031303021e031005041401092402070b070302090319020a09420801060b0d050403050c03030a0b100512150a0314060709050a080604120c02 70
    0x1800b4044540c000c1020701c0d02e60030480203d501030010403010310310f81213203203072487c5100e1050700c4028050740007450b0b601800f2030b070701e01d07500e0b51007c0c001c042c0c481c040b6011030004080c16041c6d90503103031007050340103150b803001d0705200b201440c69000d1200425012450001c0b08604003000d040b12426808210354030008800c420f90070320845841d1801a120780100c0c0c00d15140c07031000b6070404a1100070394640350150b69403402d80e03c1258501480490001101d4541c146110042007400250034041205120000b504044103241c0260014007030850541e215112400e907174003441981e46c3c8050400c01c1d003080c0d111a8200d035a2160090030101d2408236a004076516552049500080c02a511390491425240c01d0060b12040c001c607141841c100600203a07961005100034048558800c096404800b940e102c0a4150700115040340304440e00b070a00d04090740d120181110f2100005d8040c1c00c0c041403524080140c0ca05a50b001d5004002da036a4942c1c0c0c01c201d46c4c02045c11802407004030340c01440140d4031003 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 982636456 1250 982635206 982635209
    0x60a02032d010e06031501050405070519030501030b0610171015020307170405010e0d061b030614060f0a030b180117060f010b0702040207061409070e0606190809070f 73
    0x25070700d0709985442280d026080014100030b00c03941000c0a41c0c0c01c41c90b01c546040d410740f07408450020340f03500c03a0a429640d51091035041d84114403001849140c550305070740030b541268018605054195107010400145068515050b00410042445410301700f400e001941e81c1702c04101d00307178010740e501ea198000c080002c2c40350020040c2d20000391001000b83c003110941d451803200829604103414100042d00c0480c51a05c901c0c003c00c0454180700500199411902d00300348000d803035014030320541038000c000c0e150a009100e808050210a4034040c20703c101100d4030889003514041c2000c0031224118090045860341a5000c0300d0038099149420111000b01e0080c00d00c5034880a183c0d00a40341d02d4101040108900301181d01c903030041041034902402c8070a881d904841c0165112114540b103401408035025a882c000c586070100540c80c1400513182d019621403256100969940c4010840c041c41482c1d4040c5034040252000c1010134010511160000b02c1681901d46040d2030f00341c903a09070301e2103 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 982637706 1250 982636456 982636531
    0x15071b030e060f0f0408120a2025140901030c06050319020406120506010206010602120d060b0d1d0c06091003090204150609120c03030809030d020f0d05010b0903060a0203 75
    0x2c0801503040101f00e451113882505424a00704950040050401e50081c0400c42841c9603005040915900901000620105610020150612040214040325600d02071088801a1a604112a882e2804206040703075130104280c0d02c4103061640031111a000070301558103c0105000000d6020040d002030006080c0703a554000c0340005402c900c0c0180c0d10f014000c40d0640d0002001440100d502141644440b040b18502985e02c44840c0381020040010b80e011404091010a20035420800c41d0000032051102c04a01c01141c220041c2c0f050311402003c0986601c20400c020f800f4590600da8122100c4a2190800040c10030306600800c09036801842e01c1e0003900c0341e030300c01031115503001a00c0d00047c103000d0300c0360f1804c00b44a5981021400603804040c092003000303c00192140c03010030456181c14401031042d52181c8003001801000c1d006062015a01420034001151825864060719840c6c10020000c03e483d803908914000254800703485000b20244408a5480561b4a480d800109004 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 982638956 1250 982637706 982637737
    0xf16030f0e01021605010c0f081602091f0303031a090108030d05010f1413090b1e15061606200301090605060c0c3c041407020a03110a0f0515071b030e060f 68
    0x1c4e900c10880301400037090b1906899050340360490345880345060800340d0b617140c1400145411702201c040300ea11104184264401408000171460303600100142000c0c602500080c0400e036200e201c0521807407100d015400c4c4004022203004507914082c2e10401c0c01062034940010594a203465590035940c0890310741c44031000e003100304418094464501ca034002d01d100343d000110b8541c071000030130700d1141d030310f1078450312140503d1182405002e80c07085414550b010811a0007558154078204550024414061a6071928000064904242003118219082280600003034a07101d001c00078601001079105502c002d034440c40000c11b000600201943c00c00c5102a4440d007801002040248d411400e03401400328135102c24460902d8001501d240240d038141080c20440035800c583c20301d4021380c0040602030701c01002c2d071941440008078501c800200d461034010b0083d500c00d0400e071594031800c00446202030411081d01c0210b413041518101c9141c00a183d40e24014142000c19990741140040c82e0401f01c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 982640206 1250 982638956 982638997
    0x120218041a1c15050c220810020304051002030711010608070302011b050c1002010f050610050403200315010306050714031506070206040e190b150f16030f0e01021605010c0f08 77
    0x20a0214041c108846400d407100400d007071451148e00c0302081a41c100c80380d6000700c0410200041840320081548a9400c1151a8600320000904c0c2c0d911007454103549510301400884e00b85004242e510559070180c584010400c0a01716055542000040075a040d004030346210700540e4494401c0d1041000326400424941c0407160300d2021240054102842120410b8407000e50503000b600340c9086075041003010501e8040508107014002c02500204d40c58007580598031401c1d4028540f03541a03e00880041090b59030b5110150351108200d8604400c92100b440000d0f21507502903681890030310003070700d81424030201e60f0224030103410642011008148000400c1600b04c1c2c0032a52900e07044004000340404d1150030081a01412250300d01560f1300c0c1c000035040c411802c00c40440f0680c50140d14101419082401c0041c05018424282c00000d052150f04ad05158400940030203503100c9525030b00c0949140800550341d80b140f250046400640243c0c3ca0f00100d04420042c06a1001180c885062107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 982641456 1250 982640206 982640227
    0x15052502040e0d0f02150c070311010c030f0e0c0f04051b07050109050f071d04030c0213060602071a030a0e07080607081b0a1b0201120218041a1c15050c 67
    0x10303050b604c41e44d00710361140c0750b07103a040043c40d24000d400c183c050540903603544545c102114a00400c81e00c42c510b0390f00300035850701000e6050344100326040b800d0108016840c10807031943d1711943c800032107980c8a4100c48040546103807640c0070b250800c0f01c030000c0388407a40208804e08100c0d001001c0560342070755501000703c140041881603c081032020000b4004044c10104665101c032aa604a040f0000fa0480000c007003500500112403003d030001c0c07804050b070401d0060711001d0314890045070014020f80c08c000601c1303030a01903c2c1e004290440440d500f542e0322080400014601108414101c1c07241450000e410740060041c180251595910b46003d8601407203942a107031410070024030301c24810800041644d9003c0c0460004200c0b0880700e0380340d001c2c00c0c0012100d40d4034007a80e031000c151000401e118105180311007400d20801c1910240480700d9044401382e130000b24001d0464010b102c400e001c0400c81c461040342d41c40d80d4403890b0442d4481d44e00780c04140843e0070460300300c0301c511000500c85100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 982642706 1250 982641456 982641467
    0x1170c250b090d02060412031116060606030605010909020c01060b0c070f0806012402010e011a040b0d0b131a04061a03060103080a0f0203040b030906040b0115052502040e0d 76
    0x81141000207080c03a4003a400f00035610b030002007014040c401c4007034944003050311a1300f0500040003080c09903a00e404124010300d00411600c0012240c1c00d01e000c070002200e50081c092002101c0c016101c10003031910b84010180658049c01d8800d005550f5458013152030b21400b409041c0000b4014000e01c180b42c00c04200d411200429001441668064001000080142c41a81e0749074041042c10000300c0c510f11009074050501604841e40550034030000381d40d229042d0545200441007100d050046443c031105100607020068400342c0354068840000315100b40044500308058482c60700701b10b00c1c0f4680c100314403c220040d94100e070b41c640c0747c000d40704800d08999542c1c14000402c4000e0f00b40e239455a80c03103203800c0c8a00035404003406030b140880c80d040390013442507400800b6081c030000d581e4601124000c3d21080202c404880c08003030b00001040c00401409038800241068841e81c2c9494184029200300da490b0001c030380b501c3d418101c2e031000182c84034003642210003407050080c0000300982c10040c00 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 982643956 1250 982642706 982642711
    0x3070c14090a020702030d1d0306070216060513060f0513030c03290103030305130203010e030307090f031a0408070204180203060a0207020d0b0604021b0d020c01030b01170c250b 78
    0x2000340c018011320002d640d020540e4500142c0d80d0500d0403540c21710030000e140d134011220085505004e00010801055004241501c1403a1481010b8120b192140d00135a41c40c000c8246031f0710500d80781c403020300030300b80501000140d4001c81c1c00c0450a02440b60f4680c602c800e80398008450360400f0702410800c004011803055142684c180405041e40c00c440c05a061001c01480013808142c0c80d02e000ca20300c0e8202040340e07500d10341c000d0001e000000307000928590325401074440c40001040004009415008950550141d9a000d01d012140da0782c100e5030780c1e84000340500103a030340c050100a10301c016a51403194800302e194007800d82d8580030031801010304007440200f400203003a00412180d4010703130b0b510f44084102d95003d04401d085407501400304009018130070449440d4810203511a03110301d00020400d98400d003030760803180040800d50044060742d0304964034601090007080d0841d007103081d07119540c0d400750f0a00985400c03c04010399046400403c1c11400700d910701c045d4a400b00f2310030801c28203a0b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 982645206 1250 982643956 982643971
    0x10c2015011508012c04020105041701020910020d02070b1804141e2a0c06131e150f150b0d0b10090e07030207020a0e09011a2103070c1409 61
    0x151600351a0802100ba00210003100c58440e917088005411680554191000b90803100034014000b01100700f242d0003584241000f40c4100d00c0040d400c26028030000349400800860341c0581101861305da10b100c8150481c000c800c100143d004e0030088140c0b514429028548844100c1030280d00300101c1111041c0e94501480146041203010003004910f00403102000401031400c3c11a000c00d1044e0301542401403030050309d014001c1c401806481d122469100315101e0050007081c007112010a45030070b1224040070020402800c59515000b019140e0344200d0310014050702c0403800341c0101c124022100d440307410a0380400004110050080582e01c00d002c1344000980f075484c5402000b1030084e242c40c529108454484914000207841a8840c0e01952a01d139400341070600490b44a45101c0c22492045500607501e61902035880c0040329a000c02806000000d00302c100070130503002e0742d07441c0341428107846141403004100200c000b031070541c2d10700018080e108200e10030642420030460706400181910 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 982646456 1250 982645206 982645229
    0x2d0e0a1e29100f1701060b120105010f0201050405070611031e032a180d0b0c0a080a090b010e070c1401050a0b03060106050d021c1a03010c02010c201501150801 70
    0x18440f0200d61040d1009075410b0012070f2031854420300105003d49243e403c42099039902060300c590840711004030505896090302c400c542124558412400c0784e500311806491079003d11f01c104020380c0600c035420fa50a14180c162440c180784079003a07200e1303240a501102c0506d02d0010801ca5003804a0203404800141034020a040312031400b0404654043c00d01001103225000c41b40c3e409964521480042455110020311444d00d80885042d03d25048509110007060100700044c6c10030080380b250f508550741c4410a0b0f00280d080030300c0750102d010001c0c000418440441d9802c0040703400c3c1d14415000c150740d000080360b20700c1d15801ca1000c0e1048000c1c250300a07445240144001900001502da0407999440c0040c2c645904026110010501c0040c10803020300d000101030520f50001c09404128200b0b400078040420f201070101c2c02c80716500c03180d100041382c2c1c8070800403a0341502200c1411b01c2140080b15000c07000c00041d552880403c0e4000103e00c0304140d814402140c020700f00500426605184 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 982647706 1250 982646456 982646459
    0x210c030d0c0b0c0a1b0602090102010f0605131109030f0f1219080c09040504030e24160503072a15090501030e102d0e0a1e2910 56
    0x2ca603408a800b4102201c0d00030089026400c1c68480c0d0b0f20f440318145098900d042000e042e0503c000254040c01105005500b080e440d014503ca044c003c040c01c4601c064000c03010000884080e20090544011a40105000300951500d42d641045160401e26002c000741c4003e43e041f017115480c00b0381c40140e40e0030514003800040a100300310740341e03100114841c1c140b14605640d1070070480340610030314082540c45407801051005160348841c801c080803400380c440030141c408000c8029a10742000000c0c2c1d158013010080791103a09520503030003d080348140101c90821540d6595004050303040c101c10115240001e0b082945103014854113001001510342d8410003500c2d411303000702413020b2806100e05160b140c0762180c2c5a283d0400c000701848240110401000800100501880004464106ca00340f800d5210342002102c900c548a03030b441c8400d00a00b52820320f95203210000b100030798070101c1000b0f0030300c0540c082050f4041c80451622180c90f00d40c441c1c40f14040b01005250b0292000b045c50142c03100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 982648956 1250 982647706 982647713
    0x60d0c030f39050316020708011104080105240114040e010311011701080c0609030f160807050a0e0406091a07030c0314190213080106080a1712040f02210c030d0c 71
    0xc036178002c003501c280c01800d1441038109074600803096229607500d40c80d1071003c0340f44100c580b010f031003070b00d003998000c0c8000d4480003459214003008407103044081600701003400036903000380b90174103901c3c00b1100a03c2c281651052085981f810981c4140c44060a880d022519580d0048810314000c88c801c0c021581c40d418442d40d1a5540452403c0500a0380b0026040781195010003c006400448400b111840d0720f0002c0000c08415251054560b244a22940461540b5040001d1002d45051000307d440c50f0303031075480790070103484200e02c1170726003014004041007d810a001c059125004a4034046408a50184002d080300c04808401c50201400e02c140210400380c121840c800c00806000507031150020340351421944002d910182080d0318140b000510701c02e000c035110f285079000d1508008440c01050090300284501e02885107580e41c0c0300001030024041c000b0b00d01c045400034056003100310202480c004c440340c902e0451201c42d03201014001052a04202071086000a803510000301c900070395 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 982650206 1250 982648956 982648967
    0x1141303080d0902040218010e010c030e150f040803120a090b040312060504090507091103060a0315020909010e0f07050c0a11032b020d0e060d0c030f39 67
    0x605400700001c00c44000c1d00302da00010310107a001007085644018800c850412003000d9410207000c1500301c000d610140d0700070043c0c0306010740c050315460040400c0408000602d01c07000203034000d0180c1030007848203204117800604040c2c180c440003981d542880100c1d045021000030314001c00d050600d60f181e00002e9000b52016001507250600c2d14411507641d0058010340f6060304415041881c2000c0360042c094002401d4084940d40e0008010240b04401e58000c80c4c4000c6036880d030080314040c8104002030b26460410344000000382d00504141c801d0780042c0342c02400707074400140b840409040c4609482040c0e141034001100e0704000c0e113850a4628166100c0b107450002401c0c0740c00c090b800f0140c903101072000168a24540000c40c46000d21420f00c011580b40c031002c80e40051060200810200b4003400102c100e10b6070003022281000c0ca94203154014021491180c030800d502d8801c0003000c42c1140c0180140402c2c40400e003241c0d28031700b0300512104142880381c1111402c8004d0301c40190b0b138101 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 982651456 1250 982650206 982650209
    0xf0f090c170a060e090703020111030c2508010c0c060c090f060e040b030102030c03090d110a06021b0f030405120109110405060d0f0309030209070816050a0905030a050a02011413 78
    0x400a031400da41c405201600500113544010441031210080154025003c1803a0065034800d0300d4080503c001e0114007030784c9006a05c8402c080741d0241195040c0070b0345c41c01c0075071410700703c8002404c0740c6034440c0c07142401e40710f841541001142c1001c09031401c01c0440c0c01030001e40403452030302d4103070146000e03d01801514a48251303418006044c1d441d90540d16140c000003030860018000350b503241002e24038541664002c80d1261b83d18010103106c038244070300c50b85000c51514000c2004101c03201258031000c00941c8080428072031011102602211403000f40708140c0e416071141c010390346031480c0100f4003482c00340c040ca000c0d505924080350381d40002c004902a0404038403d60b40010181d40e138401052010951007000b9020ba81c10b9602c0710b007090341c008000e0041c0c0344240c135220b4042c0c1319640c060300c1c03464041c0c1d803c80590980c001d80303244452080d4040d10820307a06c2c0c1f82c418011961440402d0400410f034005031400e4000f0b080d10015542c118400a000030020103100b4503001802c00c1c8040ca48805 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 982652706 1250 982651456 982651487
    0x150915040b040608190c0b031b1c0c02101521050a0c240e010f0e0114040b12060f210309090903070302010509030c0703020f190f0f090c 60
    0x125001c003001900c0d0b030360001c8041c02c40c140c210b80c2c54036500040309203070350b030b207540120b500d100903c0380400c404151005481c00380c0c2c1c3d100c2c001000040c01000a16040d0440000304598035003d00752000554043c0c01b410702d400c00c60780c02910804004010103000d480e00001e8420350700c0301600341008600e19840001091440c0450ba45090750901d242080c02c1010100014106c4140302c1e0021035040156803885000103e401c0722213210080456040d180076101030b0341d250203ea000c410b08058a4000e4817651007131041403500b040f0b001d6001c4401081c1d80c1082d04035190710318001c22100d484812412100307130040411150420154408000601001c0c400000c460103245240007017100c03100100b05852058a00500702c440d1490b09111243e52a00700500603001503003000003041c140d040200c00c032241203080c035020308902419a0244190000c43c116290b40000c030314402c1c0c1405528030940c43c006001d00c405001403403803914403040944c0280d90440018686032a1a41c1052500140c030030500880303 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 982653956 1250 982652706 982652711
    0x1a0a120b0c070b0f09010f05010e0c16150e1006080a080a09080105180c0901050f0d150e06011e05090115030b0a03030809070605090a0308070f060c02010515091504 72
    0x203410208203042e00640310010200c5800700c051086803441503400610465000740204020303111400b1043c2075900c288034454810002c00c000c2142d06c41103030700030110b4240032034020481999035914808028002c006504e88650380705c2c4c03880d40d01201804043c0e07800d80303521018021281040860341d22241c22010052014400280b502035083c0a040f000004000c42c0008214900c0c106a00c10040941918141d0141c0100c018050151801c030343d2150507650003914048207a541e481c07d10030240000c550a4600200d5515044174403405400340c40340200020b0007900f01945004580105603c9102c0c041c525812004010301c007a03154521058116240300c0304801301268100c00940c01050841c14458000070302440120515030031200350b90041c2c2401044426003035486004a41034003601c022a603100d20000410004100d070745010301501d90040855080c0e0a0041d82c1d4502128024040100581d440e5010807907a4400c104040311044400e88291031a407400e40300100d51920000c0300b8601c21517 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 982655206 1250 982653956 982653961
    0xb0a06030b030f121b060f0a020a051309140c0a0c0213140a1e06080a0b0705090604120201090617040f051207060209030f03040f1202060d0f1a0a120b 66
    0x9400b04030548005405006880100c180318813203a10a920015169031507003200b64205000503000102e680c40b45209100d080100e880c0c004401c03019500c0755090100300681400380048000075001d1a0009100703041e80024910020900a110004000d100001c0709070248543c4d0740701c40d001f42030a10415412a114081c9002041030b0400402d800301400000f40c1c901001c110f40001c2981c050461400600b0982c1c00c00101c040c035080076145940a560220340281514400040100781202e4011000e82815401c000c010070207d101600150320100180700d40f1391025043d940c00c0980a000380c40c0078a8902e00e03002e205c0450042c000000f9100404030508012100140501030089504420048100035036a01903800e04c1700182d001180210303c03a02401c104000320342c42c00012a02200c0d203481c0d05801d42c5190042c48292604402010f98004e981000728820502140c495400c4034560840005042c50100c0c02d070102c3c042d0300691060003042600000d112003d112100340b241d203603010803001880d0b03 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 982656456 1250 982655206 982655209
    0xa0908120405035106030607090302042723010207021f0917030d06050d020d031413030f031209020303031b0909160f2a020102011409030310090b0a06030b 68
    0xd00082140445040582d0329060b1300100c1c10120390460302e1100c10a2641e02d941003010b4607001c055512101003031a2032800c0006080c9900118518412040031210484c0c140e43c51880d181030f40a4100c03040b00080201c00d1034203085140c8182c2070021000210300301010b980c081103681000e5030b6085801e0002031100c154040c13141c0440c0380580b6000c51a1300744101d03242a12507603608100c81e0305210317601f4007001144504141c0501c88205800400340e441c042c0c03954505540d030a41840226864403800c0042d03045941a07620060b000390300c503080d02840c0341c030035040050034000140d0524190070b0034100d192000da40d002003540d8102c403402ca4600d216600c0d0181c007800c00c1c8500c00c90940c10500010402500e51141c409249425460740c41c0c1044007031558000b1500a1512181a01c0f82c40c08443c0c2050402c8050302140342484c07040c000003620a4521814105034001141c0321001d6600000400000f124030700c0e0700d0401445c4040007400000c0035100041c001c1e40d01030040b4000c1640c2c0d880340345c609 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 982657706 1250 982656456 982656523
    0x1501050d110409060506040b0603190b010c0f120305160e010516150c0f0c080403060c12020c0d110d0c0b06011b0c03170c0604020111070801020a090812040503 70
    0x14003c000c03903010b0b0301c0c00130081d14040310010300c19443c2241c502c01c282403000403a40310314007131810034690100c5415100c005040d001c49560400410019000010b219040404881030103601031002d00c0c42144002001d80e072008110003130303544801d2440800a034002040c11451082400c1283d290424090580c410041606d0044d0034034218008030341d5454901d81c01488040ca142d590104e44110010f07054460990200d001010700c0c01c1040100086a00c0d42e10142c1c050307121f45481110114840d842c4000e83c1c01c5a407030000b02e900078182802e080b6800074030300c034030030002c140c040c20190303000c00005031208107040790241076a58004000351640c0c1c411948054007060303086020001494900f0011101d094500003151a900c0894280301c2e82d02c1d2100aa41a46000c00001e040680d50303a801141d0b04090524650114880c004020429007000c1c0050100c1e018555202507200b03181000540c580b425604c6040c16403801048140700c3d41c0c4001c110404400c2d0512490701d040c241d02c0c0000d05c40b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 982658956 1250 982657706 982657733
    0x60d06020d0c110c150403110301181101020705190e0c090d030c03091a0301121a0717250c051c0302071407080606040f02130305060709081501050d 65
    0x401d071504a95204090f00f055003007100f40f04000c203c0701c0a0301c40c0400e0050180c3c2031010313510310203c20b0204000042c2c0c2421842040b0380e015001240c05407420804a5611400030021100401880001300007541d0401c4220000c2c80304450303e01d401250314045e0140703100f00780a03c1c8151a1a900060b003101e2515003141c1c403250000e00905489525428000d0090380c40190072400903101d40d03800a403c2c000b0258040e00c003019030792810300d140d01e07080c001002e603041c0740c1084070f0701140300f5145a1000d504076040c80c0b00c1c42e101d450b9400305441c0c0c0c08400020460081000700d8480c0701c0c01c0d900e07101c50071617155422070000506000310440b44a09200c1e1a0410001800d51112114440d101d040c1e5415000381103541c1c401c103098180300c20161a03d51716202140102001ea03444000003419500d043c0d001010004281c22005150560040140c003200704940c00543c2c840d40083c0900c4140c2d503100a2000c000d08a220140c0002c048020a1524104041c030505201e520900c15030820702241142c0c802 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 982660206 1250 982658956 982658977
    0xe010f05070c0b0409140c04230d02040f020d06090504050303010311061603050a1b03020d0813020306010f030b100312140d02130f0b0a051c0b09010806160c0b060d0602 74
    0xd8030344c0e65540e00305025000082e5029402c5070218007081e12a01c140095170107039201030031601c040840325522542ca02d911017030741d540e2005589508070090f07221031040d005c410854100150780c65100b0b5401c442070354059803107046850b00d000d041001241001c001d172819a40d00c200302c00640c91601c030014039607009100703c00030304e110540c2c600704c2059040002020120341540b01c405e403040b0080b848030307034807400d2920107405a0000411902e92034811380440d5402400a0005c803405051500404e01d80182604011400218008144213100b14024103e41c0042c51140c0c2d8203641d420f580c0c41c10b0260114412a409200503841d4103041008607030203030b40846191850454803403801e646c9107034200d00385208046105503004804100d9420341320455040150342e0f1a0f4a1030040381015800c0c035956003800d001400c590710044254a952051a41d03802480110024002420501d405189180c1c0e2040e403d024050001081c2000403904226954001001c8401d07a01c03425450a060000e03116480d82c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 982661456 1250 982660206 982660229
    0x50a05030c13020315120d03051308181c0614100b040303141c091401060609060c1e0503040e1509010302040209030f120703090e13080a02010905070b0414010e010f05070c 75
    0x18840c0f8000a1010747c1850203680602ca0ba495040c400364900740724282c0503021000421000324203544214480710004809070139602c201c01c4038180140f40c00c0c00711742c04507800e076214800c0c00d4140c001d45643d60740108490481e443e4503864501c2c80d01ca18402c40c403000b0140a40455403c001c400c416083c1c400c00c0340480500036011841c020504014030155008950a840a0303120703004076001442210b090340c3d02e40c0c442801e4103080110a5459a1703209100300c41482c110555610801080e001602d8401d2040004649480c24a8500b00103001c006003a5038a0076000c0300804196500c0d0310800341101d805680059466240c800802d0030454180f482500602c1008140921050400004c0c51518001d40c4c9000c0341907140d100480c07110b0004c0d40e291680d42a51503030800420f204100510b980320090000240c801c120740c0c3c0703450410f02c1c594010f65040c140850100261844a84401880a0309103800c180c01100540060400700c02d04404208202d804035000041122044444000d01041d9214 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 982662706 1250 982661456 982661479
    0x506040906060206090a020609040e0307080a030b09070c0c03020409080c071403103b060f04020f0103051e13170d060f0803190e0613050a05030c13020315 68
    0x10409041c8030710515006124510004001200200c0ca4044840c0e0040c45185854005010403019101c00603181c6000c0c0400c02c114400151114003d005580880d2404600181031404002070954010055011b020205a91400084082c0100003c0d81d03811a000136540e142420820100e00899038000100d01c540075020400c403104040d0000c145408034104d0700c1019459084900782c40410700701c0101008404e43e41c99800410380304c3c41005080e03060102955400c100301c4140351100c103507218845100043c2c05e120940c186606942e051240a080070b010b0342c10038002107210941c1d00384862402e03006100c0030560b010403682d884081e1907040400e8203441c006807040c1c00b0399035012140c000807091400c0400503064076000d64110865080c100a9800c00031003241c48090000241c01030300c1005001c4640304240d80c0e946000e0001c4880004500a00390b0030841440407002c0d00d81c0029104e41d01c01080201c169132214035101184104903c0980c4030740b20145a510b48001403018a07903c200c3c407006 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 982663956 1250 982662706 982662719
    0x9030207031e0f060c0e1f12050903120604060b0a02032a1203060a030b041103250b0f130b0c1b0619091e0f0503070528050604 56
    0xc122003520b005440d80701010a00010102c0079450201000746003450b0500b081012403145c1d0711911035028642408081198010009070f981c03003000c551010782c2c204d652958042d00d0f500c18140000b03003001c2003013080107040401c011552401a600c90108164400703000804640300c54100c1d900403c44036800c0f0b91501040365000c0d4903504140241001601c1454158414020100328a10030041c04d1002d04001e4242c00003010569200500050701b0000e100341c0080001c02c110300c0180f189006030300c511200140e00c0c042508040e80d01942114000343c2540d80ba01002e1406052021503403491038003a5030303031005450010360303008900030a000201c080e02c1c001100d49559000302054450380041d50052001c04540440b0710343c2c48580c00e0b411840600003802e030a0b510040c030003104402410300811a0353350324124646200400041641000e20f80d500300101c1280d5015500030308400c130040c2a400b4105808504029542001c0c8401c00741d4600d99500412420002c01c0040e18001d0105540c0703646901c07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 982665206 1250 982663956 982663963
    0xc080304091a0f0d032a030c021f0915020a060c020f100203010608071b060606120e070b07020d1704080318060909160311070b0f0601020f030706110706090302 70
    0x22052000c103014414241d8546000710a4510702c1000030b0103044a4211614216031001403006440e490718040e64400801d03901e086c0c55505060f02c26a138003611141e4520612401040302c20941818124440a0000e95a0498460030544650607100700c0180c829540c1213162440010b000707040103240c0300c003000225602051040150312560112001030b4404501c4030201d00c0309100319000141c0c110086031f5510300c14003c41142e06916909002200a0354507510b040b19026800308010640840901e0280c600343c7c010b03d044000304c8400381c011a8604140303a0307154420850000d1054030400c2c60503041101e018418003201c0c99202180da00c0f070380c5800403180e0326848104a10305510742e0740402d000525181c401c85603030280103802c98001d6210401d6400405044120311001d00d6194041e00090042c400064103015001d81000030083c14441c03070741c001c02000500041c3c119007040300030b04412072001007184c090035400080021510162008041ea41c003800b80014240c40c01d01020205155001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 982666456 1250 982665206 982665221
    0x110c0c091f1d010806010e06040903090e1311042904091b030501050a05060f0f01051909052b08211e01060206090c090c042408060415030b040c08030409 67
    0x5102c00d00340703980b5591055614102480341d2003003242000006461401d0642083c0e140c140f1a0a050b44556202c2441c40e002560449205503c2100602100c080c000f0800e90103021010507903080198640e881c92041e420304044140c0c014000302d40440e152141c4591b070041c07200301c3c0c11844c20070000c03c90820900700c0c24404e1109484035802c007001702d0740380c101c2c520406008501c000c1c0f090300c81c0c061075414840c0d106200303803045042c014140003403445041103c4428452200c1d0356202c1170460300304070400c4408803081e0424020031125074000c600305006542c035014001e402604c86920707442242c4001200c0b071070070941205502031550503c1a16643e000384035900d1800301003605000da80310007040ba658081210b80030001c0e0f00c0343c8221403407800c2c01a5a00d40110707251991610305a02c0740007011990003201005801d44500300e0302d01044940c042110303a0007010485d401e00200780e000c070b50b0040c0c1004501001c0c055a0081e4003090400080c000000d000340070400075a40c8682c2d0701d92401000b030102 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 982667706 1250 982666456 982666499
    0x309060f06010e0904020d060e0c03071a1b0a17280f05071103010e03070515061e041803050315010908030a180305030f090103110c0c091f 61
    0x102004100c0101154044520490069540328010614001007150540c0081c000f41d82201c032511250700440c0482c05000204515003004151146041c010306240c490300e036000c010703c007041d9540220b1100c00e05003142c0182c41c00c824844030300854500701c1400c112140000801e0500b407000e0b0080c422619101a1034174016000340b03241c4209545103100c4250803102800030006103a403d44418190160001c0c3c420580100850b844060060002c2800c417440302c078916001d580302007818820032000300110810074110280818040c2003482c0440c600c1c100360045c60b00b400c500b00180c1c0400e921540d0140070401201140010079400505015045d40d0083d1146165003240c0c1d584620707d5405a1400c0080740c42040045261041e2404204d4200040c1980d050300c17400034950002c04502c08001410b864106100d900b0350b43e40d042d400150071038911400000d4007100500010104440200c0d090301420307000d858040c080d59070200811040941182c0e002181c608003240031407426048100076410710031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 982668956 1250 982667706 982667713
    0x62f07081510080105150103050a1404050705090106051c020901030f090f0507050609060d0c141c050627040203030d090f020301140c0d0902030c04061d0a060b0a050f0c03040b0309 79
    0x4450740303c10b09136082103540c080d10441e25002010710b54441e81c00a0392103486801c002892250600d601861480251800e8406034000ea6046c401803400e4032400e4018013503410079038035103c41d8040c00911407090940300107a0540c04200c040003170340a074008444001c14280e013004401a00e141c52031801d14044002d407220300c215403000c1a50b0902100b100e9648000502243c20408652141d4000d00017440c010f90411400d2034401c200d4801c1003000e0007400d151480701f1400b1100b02c40c0120101d0308024011407041000c030030701c805400101d980220304601140003046070b50f82d035400481e2461141d0800a801603161544040900c8800d11510300c08030b10072002403000140c0440940c8484005848164030034900300212220244140d2125901d40c0c805000e590440da074041c0000d0403104e05500600403010700481c00088442c0220400c0d80c85445200100109810b00f9000e42940c01200240340500c007001440c88e030300d4a01c2d0401c0e0b4a1921840c01180c0d55a610b55600e542250400d58004203140b2 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 982670206 1250 982668956 982668959
    0x106050705010e0102041a1806120a050604050601120e1c0c03090b120f09010e1f0b031c050a020a0204060f05031608030a05070f15050907062f07081510 67
    0xc0045c0210f504030382d24218404804400710340c0c11503003a4403844000c6400001e03000240e800381c507440060426244000c288001d070385401d48a40c001d6403402000d841c80340d807030403040140c1c9a811520000d0018265030300080c0303880300d1000e918034002c06035180380c40102040303210107041a0320030442e05505119036103800034182d41e80e90000720b501605c169030703030300c1542407000408210010008076840080f0308000b04402820284407424070005440c68424940303a0590400002c0c428043c2c2410788a05800802d00750244400b03a8941c0c0c500d0b075444d1720420000003440e006d054420001030900540041c010420103603685001c0a040d111445014041d001e4500c816500003030003144407044521520103180341050041c2e040700c0d01e9111003800c894050241400f10085000480388400165060b4400900340c2030810303000c0d242c500c8650211041004401c0028001500070200c2c0300311840081003a80700070100100e550500e10950032520070f81c41b820303501c01403d000741145140150b00952118035160b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 982671456 1250 982670206 982670231
    0x7150f09260c060721060e150d0201080f0711060a090c061805270907060816021506150a0215100506090d080f0a08160903021f020114010605070501 65
    0xc2c02800d030000c08640001000444190041090f00d501c031564043c02e500303d46080c10703000211040ca1300804501c0e551072080299403810201421140c02d02120440c2641d242c0e07900003024040001c101c00c50070340e249004100d50f036000c1c003c0c1d65014120700003950518a4051952401402c1041066588060754840028002e00071182650440717804090640058140b0080c41034050402d4151100c0e8018424410722181042c81080d02800700400505005481c040c0c00030311190000c2c010803100340c243c0d000a04595000542c40b01c003804174030003145080d51200d00188000ca40c2958803040c82c3c40010701082c550b640458600b401c02600001100962205514940d413800207015480e040380040000c0d0400c1e1410a0710030700303042d100344186440c142580000c03211a0f013004c3e940d10b000c50010028000410294407a903403981e6994600680d4161664002a0b020000e4409800310154000310303031402e4074403e401400003450900c2d80030049503900c1d0030050190340040015980c5520b00905030004 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 982672706 1250 982671456 982671533
    0x170a110f0d0b0f13120503100e15040e0601050105090f0a1208120906010609231e0301052a1b07030f02131505010f0e1305010303080c0702030307150f09 67
    0x995000009500c04035803134841510746600c06004235004480c200c1c3c00141c802808450344e44161111000c0d0050303a0030403000c0c4415213211006594068210000500240e68004240c0704064011207a2014000044012402ca603450b50030118800304410280700600c01c820005240440c481c0d4022b04a83d1b86003805591107081c28080e807030020b10b2580042101d24181d041301010001c10740014540f400c0712200023218900c440343e82c440320350984803003003080749001e200da01c1e40b11341c422a000d0550441800b010754035040765245200c216402040180c03044091401d400c2030054442c0480f11881d4403410500c000c550042d42c100e100c0d8101091101c0c1d018802d0094071106880340580000f0203061a00641c3c50702c81e00c0a00c0ca04001107030340010080c3d91241e42001c14039050902c0050154114140103212146c0141a030081c28410091315006072000001c031084a0782000c004140307056941d490401601d404a9100205070410040f02d06201c082c0c03803152642e04490011541c2e0405046e000500f = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 982673956 1250 982672706 982672741
    0x5011805040215030a230a0b04050114090702030f0c0c0906030a120311090a0f080c03151f030f060c03150806060d1a0702010c09170a110f0d0b0f 64
    0x100007564182014004440f0006141c020101000100f0054505040c440b41c440008014246029101c414000700b50300a2003210380307001040e036080c0990342c1803013148410445040080c81c05a00950000380d2801c1c800e05c19607070823409540303402d0307940c401c22090169101c2080d07026510404210001c14050300e40021910402c03940106141d0011542200581c000c02181e00b418680c1c120800582d078841d50f820a4040107807851402ca0082c00307080546113460541c42000c081d00952043c03000c50b82e052058400c03507030720092101e4003110381004c507881d0301629803c5500045c20070541d8502c610401c00c1f00c0e0440050307030040d640c081185800000c0700f107002450f98800c030b02c0c0725080a40441d400d42040b0141d4030340d07103000d0f107000709003030400c4903d502101d81c0482d1818010b0359202c040764a419401115000105182c640400302c0d100580d5266032034040f140130007829103480540c01c2c0e425840d00242000f10442c010031840c002e000a050200540c2000c881d940009203034071000038001e1720311008058 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 982675206 1250 982673956 982673959
    0x22112040f03020d1d04050603011805100501050102030405150d060b0a080702101505090603120301030c030b062b02030a05010c02031c050403090b03100503060403210605031b0a05090703050118050402 88
    0xc05e000c0111040c8401448054042a0503540b505d21010051511a0300b21071a50b2207038009009030310b200005601101c0c01a00100e045400c200800c1040da03603a00301c1c0d2055880700a0140d0760307582c2110b04100c020035041e4410b900d1400c0104c0ca4215060b0401c42d00c9200700c07520380075640340b881d1140c001c00480700310400403a464100d070401885a400c00030b200d107a0200c0c3c0502200c0c68008126030070a1560826402200c40161191040c000c01c40039031a0640c000c1030a80791889400c00c03070505010700303481070071220015000c000320080039550100300d00031451782c200b0001c10180c40c120200030b4880e03011200c016030400c0c0b80340d09203420f440d4520480f0700c240d8141e0344031815181044119100350740040c0c0052424080600003240c2940c0c01c0c0600347c0100c3c400d4480e154480f003118240d140204200007410b06492400c2003c124a40340451031101812410001c021142c01c12000241052250b41109400040200070400401e4140c2d0041e0f0607540f41c0800346480710302a4050005a50085400a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 982676456 1250 982675206 982675247
    0xb07031407050a0f08010b1804021b1612021318020414090118050d05130914070e18010b0c01020c010f0c020f12071b08030705060f070f022112040f03020d 68
    0x10b9000a003001081c00801d100140098580024bc0e9288581c0c49411200c40609800c20700b0301c406407000b1944031030300911207158812506042c5400041422110704019040d55403680001d100955400c030811940c958010010003051515040d0300400f4901102c06110301e40c0f070600d001600e00b21030504400c9155001000302285a04610300b02c456410880074401213109030000413903801c8603400350350681034241c1107207032892138081d90003020140b1215049000b064140c40424400c1c0c0e50400c40d40c1940c0c00440c12640e01c0000003141c1c1d00a2151201c48003203540b90000d404a0200e5580000b101c284440e800c841640c025600910b8480c05a0b0b102c0c8101680e040200c0b030001400107010000750101d40900c110166992051181158442d0754100d540e40c201c0000c2011035203150304c41d5900030307060f40b0f0046040090000041d50395520317996400c00c5210031460707450041030801c04a9140c0442a140034159080929043c01c80030300f190400c502502400325820140340c814901070f031591300c6003043c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 982677706 1250 982676456 982676467
    0xe1903080f130f0b0705162411010221090303090303160302040509041b0b040b07060b0f03011b02070902091f0905090c09090a050f040b07031407050a0f08010b 70
    0x111040e40d200c070850600c103100b440e1000841d10503c0820344020800080c6456036082d0f01d2501c0c0d420310028024400c40741e00c1c042c07014000c100c5000000c106100d580582c503450268090001d44e20050741010b074803125800002c81d00d0201d4040d40301240c070714184000c0401191500e148494aa00080311544d28550040c000a03016001950401150080301c0c1801850562114003043e03504004460990b00d011321404603201032409401c000b801091480c40c003508207810400c03503020b2482060400f500181c4c41c0c2040340345560f40c0c5510110b034200c005000b00045610040c039614040141220480035000b50b1000084040346802254034040c401007659000090016034102022004c2540742d04001000d54040b0796610f804075224000c50540314601d13140c0c0308030410425100d0004003801c0b101c41c01e00c0c0501204a09195a080d0459809403200102c3e40d15036000300c1c02810131691306520b00d02d14074144100540c110005142101c42e5a88020418070f20340d0043e16481c0080c81080350480e400c122 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 982678956 1250 982677706 982677727
    0xa080a0f02190302100f02061014040f1407020106030209160819020c06010f0f051906050f130905191503080318100b030f210306040b100e190308 64
    0x10b50300740c0b0284400c91100040d100c0d0080b0341080301180e20040410350307007502c81c1007a5404001c4180d01c080b118403d00e400c281090380c0310f2007290340542c0f414055a1100903600003404960043c403000703081001107003454501820000d02800c0e09120590048425201040340c405054090840114158a5200b855100c1e04c500f00304a5568400e066080b07903090018800000d814840a802042800000e00c901e5042a4081596075010750000d84250038520700508603c50700080103040300c10904100340c0311844c1855401d50b038403503021030700054034204a0209101845c0c3e0b01c414002c003201c40211840403803030400c4004030b408070b03000207451083d240d0003040040d1b00d040007143c0c84041d15080310301640c4850042d0f40303468190100c42402907286c0c940109142402c00501c4407960040f0020001d00c0c1e10008020f00980c0804d040c2c0c14503490000009402e62030310303002803480e818041c0089080030400c2000810900c0072401c414402c800044045603d40454070400081e43d0704100c0403840d0401d02074 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 982680206 1250 982678956 982678969
    0x11b0f03080402010c080703110c0a1a0c070e010306150b030c07120513180e010c23120c0915040635091e21071b080c0a080a0f02 57
    0x40040341086080d45c403440000d48010003a0040b14440d07201d500c0040c0a900300e5070b0a058840c104940203c8900108100300750720481d81082c0a68041c5880ea66040242072490410f08907401004400d0091400001046042d9200903580e42810880029481c0c0f01c3c446075031688030a682e1244401c205001c0f030b1001c00d0480c3c210a034502c509045c80752424289508017010080103a103d0010019000808859500140100c0000d41d103404002c001d1020800d001030400c03600003031001690340401070040300b8110b0340811030344504071111400015141c408a500c4607a400f212199000301c40c9109401e90812981040d101178400300c2d01c40032a02c00e0818180c44840c40d20000800d08801203030001c0d81229420250240181100c5025000020440c2c485a0728081c68440f8140305501409198104216034000c0b035221145103c6000e58500503410041424001c46e240d0301001d83d000600060712070000101010407400580307000b84281d07920b07450f994455241c81006048800c0d80280c9000518210 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 982681456 1250 982680206 982680211
    0x3070b013305370806030106030b01030f170f07030f080603100e0a020904030206070f0801060e0d060b13020d0b0103021c0902030304081606080114180c1605060105011b0f0308 77
    0x8045980d0f080c5454082d02d2070344400403100c001c00f04140f81140f4591070340001400d42c00501600203229140c41d60f0340d6510350382c40520003d84054040301421040200c0b99035000c981c9a6107115458503600d124600f00c0701980141c2d0110007003807481c1601120540030701110351058400401a0030060085104500038212004401240e4000c101d48000182c0d2000c45003070280f40a80c0c0140000e00d0b007a000500a0900c400d6200c090001d5000104805540020080b0090f14142e40c02e4000b2041803425002030030004040b55030110a54810340b2501f402c0e46d002e8080300e02d01c51070620144200600640891044500184d0a01c040c424442c0c08020b60340c100000c0180b018048070702d0141d661076250f041000d4405c00c600c1988068908110032030303001104901400201c0101ca1010707041d080014602c400d5405103043e44400100003503903a500305401c0d41c8002449a110040c07000762031400ba80c9601090140c6070208110103a0090a0b0034060040c0d07550310740c040c003800507000c0d0986060300c090b0b400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 982682706 1250 982681456 982681477
    0x1106100b0c0f0a0606091401030804050d140a03080a150509010902070503040f120204060b0c0606010f140d05041a010303021f150803090f0621040f0503070b013305 72
    0xe00c0c00741c0450000c10000310b00d40034020400001c2030b03420118114140d41c0070031f5030400d00d507590034010320105412030103c1d01140c40031100d00307041c1551450010480038404038240240d000710701041091540000040f44248012081041922100314054649044038000c140d006800c2d20014842c8100d26401030030001e008000701c90030720ba42c0d0000c0e4040c05040e500080b894600c482a81000c60426024010240c2450307641e281c1005001c0059996070080140140c0c1041a0410000345130350040c91002503540020103070554910080744114090070b01a50b04540104d41c224540c58000107101185043c4d13541036018000d55460b070303a524050f40030303400b2a11a81e541e841f808014003188262600c0001d20303540d40656280d06516040160710b4544401c007034028102082448103140009101c0894038220b00da00c0409602c407404c12002e2600c048a0040980c88000341c130809005042902c40c0c101c1d00110a50a40e183d1100c8521001444041c01d60380d40c0d12024003407402c01030058020300014800b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 982683956 1250 982682706 982682713
    0x11060c0a17040e07020706020f0705090420060313050c0319260403060b01020105070c0b190b030102030a0504140f1c0e03010f0b18150f0319030905011106100b0c 71
    0x80310300f003030700c070550040c0c03410009680400820400283c0500040c00400c0c810f0307019280c1c0c00e207401301040700f0f81c000410007000c0081c07045625503048107240045400c00790103010f40b6213034a00a015600c0790010303400240e40030b20a0118408a030f150009040c51030640e001d20b88520718105a07902c04102d581d2901342c0d041d100b6101079a03810582c14030050801980102c2004ca20060400c00180c01c5407809030a40303080186a003039110102e104954400d41082481159001800350301e003403e0010000300310401d60550000081c030900300300726000180281d00a1000240c58030300407e00c2036a4100302d807076050035a004048100701000b0400260310030142d032030170604c404a0301070000a08413644a603000342041d568074900085030400720428085142010101c2119080000c8650510407040403080d11480203c0700d4050b540d01d0500042c01401c0c18124540318850366440e0181a0f1401c5000c0c043c0014606001e0643d4030100240c41030050840c10041141c1c0e80c2005c009101d2640300d08c06003c454070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 982685206 1250 982683956 982683959
    0x4080405010e0a091b03051609170a0f1b051206061309080715060b0715051308031315020f1e0c030409050615070b0c160b0a0911060c0a1704 62
    0x62040c02417040300340c6003408801030071a0084026084410145c1540d20144c150140003c103a60444198404d6820b01000b01c80c000f2820005186403100301c103c0100000140305140007000342c3e0b48a490524108505043c40042d20342003030140110351519966565880031000c01c0c00360034000d904000b20320786441c01040e02c00c241d880c0d40d43d0030b0f8081201200c08051242d214a1402c040e4401d16000e4012003034440e10344011901d0340e144d01142007404580003551a00800c0c1300b04031100c803c0380702503030005202e40c42e89003091a039580301e655a0307000e5642230682810b00f0a907604c103208503107002c01040041800c0100c041c840c40281503028480c5610b400042084104d45c0100700040c00c010a083c00c0f002c2004d00e48503003449001250403511710713480b81040c03194400081c00b0308034140c0e10052a2001940b00c000c640c0b03048191425610300075000344000000d0046900564000f4400e481c042c00903a0401c0c0c68500901c00b00f07200d594440b0915030050409440080e0f032541000112449051a00703081ca03 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 982686456 1250 982685206 982685219
    0x6080a090f03020313150507060f02040f060504030c08120f0a120e03071e0209240d03050301052d100c0501020c010902100c0c0918051f1404080405010e0a 68
    0x404414000d8025034000710390310041d0391141700e0040180a4050043c88000311003103020b043c5004103403005101d10f46175405c3e491040c81a40c141c4005000625828001c242d9034a400740c034070383c8540415180c2c2c01e0b001802240895002804a0b110210205c41518085032010400590740004184000304454030700200c05030b05050180390103118000000d15551480c40c0307019050300f13010310721603da0720110043c3e580c0540d0b51440c116500c014803250342000003421024000a110301c11021a50051210f0401c83c14154094040d50595100340d810007850121442e03042034054220100e00c420503075141c143c0e0750600b0b0011040d03d58016609041070301c00d0180c0d40c6d10b400da0b00b014660420582d52401e10303001394601102030140300c0c401401c12107064841500e6082448910b03003d15014144c40351040c1c9100c13090607511245a54010081d01c041e041c6511085060f10940022071841a0800d8410b41d545852141d038540900c0d845080c242c034081c540f60054440e901c2e000c103920340c0504039503c0040e81 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 982687706 1250 982686456 982686473
    0x204020d060b180909030702012a1b0e13030f140711091b0a0e0a0305060a05060f040c051917040b01060f0309023316140a02090106080a09 61
    0x5402c882c0d407002c2d00d601407000c2002009807001d00040c0300d40c4080040c0911010080b086552082c1c080c40d01c0162854000c0121b1034598140e45400500354030307418080244010449503411222540c2d003c01e140030f030303a0003150f080c2540564103c0801c8844070030082c0041e000d08441074104c1d5260401f5820400204000380382a00142c006552480c90311203c0c50f07051030066610b960001c04210031041070404407074410540c0c0a0b804150040c00030581a56075103555140712480110307840021038900c0d203070444860b1701070a4282d40c4030f030003140c3c01340d00b003801c0c0d01c0c09002e4607072807240541e82c01d400c00c05c903001102220422501c0c0390041c460321490841c207004103001c04a11950284e4000d01075540740440050201580200b2501010724101c6100010fa4440c07410384241e9854031100c104c4070403041003000c09a0f03d0002008040c1100041da801080407401d0f08160b20f42c0100d880244824501d440300d51164200000254000ea07800c0040c4240d42c000d00700c058004001490019404040c0c0c0c1c0c0781c411 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 982688956 1250 982687706 982687709
    0x411010c170414030c01090b0417120c0f0d050406050f031803191803020906060d0b1009180c1e050d020a09140d150908130b13140306060d0204020d06 66
    0x8110242c920100360f82d0030100501402540c0c00c2c030703203010700514100b000001e03402140118401012401c0480001e038104111543c040080f01d600c8035034407a07015103215a6003403418a0b0440754022074191001e258010300a030303000c5480303a440c0c042c50080ea955103080560700040c00007070103404280603000820320070006881c0303402c40d40030144141d41c140c1d42c001c0c2c505011148420700030a4540018001600c0e441101500044195845922400076981035405002805d000380d0304005030350042c8100640c004211001c84019640c07240382e9808441600058030700d02d44801e00400e900206410015541802d4107200151501d4402c0c100081003a449042c1c2c2d1080601c1400130f854800d0a119040084d0400140d205088403400c80540c241e6445201301001852141900381d42c1c0e007038160511280d0360454100800a00c10b00c980c00f03442e6420b00a25403c105211b80004810307000c00f080c2842018104948084010010402683c070704c020012400c070b0200049800903028451a1010000b5008440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 982690206 1250 982688956 982688969
    0x2040f3e03072a0c050d02040914010605040e1b1903060c090609120c14220204242123180304030c1403070b0c01230411010c1704 57
    0x80c190340414001408040342c3c1c0010056040c1801c050b00d001070030340d800300001c5807010745503051415004c0c00001c0c001c0c03580a201030050a454000c0d062141010340c080015a0802c48042241c212500082950f403440e488104030f074026074008010b000c0ca40181110301c180040c01d9111041c0f40c681d03036010107a0f94141d00d04004a45070343d00a004654105481c41d02400301050302074108465521000d00c106a94030075648642c2c66082150200e8856011207101c214819194100e1090702c0300840c0025440b0744600c0d800000b88502c04150041e0b0340400071062441c5645503c5248643c84100c6c0042588903400000d10340c1da80d0b94124002c030f0300e2160344051040c8a0400031a45042d040352542040c00c00c081d0001038008010078000503c0d58108107080d620080034025030816850040307842c0a805820114490307002003001c000d40801508900600000000808017441e245540085400300940b40149002d4010b18a6545548a080603940b1207000e0380200032080840750340c41e0b0040d03106d900940d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 982691456 1250 982690206 982690217
    0x1e0301050108010b07030c140c040e07030b13150b0f130e1002130b0309010e01180c0803030105100c05010615181508070f0e030607080402040f3e0307 66
    0x402256030403480b0b0078010314402007030754500a01a90018a2986961070050084440000f2a250100c00700464060b080c0090820070003203507400c0440d030751002c2501c811984152040e0024012000b0214400c1d2030503841824098600e401c10050302c05801c10f00c0360a60041e62a40c1015503d0303442e8240b64460f403001043c00600321403c0d03402c4a0030803989400085212b80108500c40c1103c4082e054a800c0f2154030b102d65440380c5402c1e4403036000d00130b040419207456007800451408031500e04c80652500b80b08402c0d01f1022070345d0b204d0480d1240001d1080c194440031101140ca61280141d50115400d88100d00008156444040c40b1642d081036509240000f421100c007000411080c20f00400a01484800d000342c00c0e0302c5400081600c0c0b80207004500b0031540c00d042101040c00303403201c0c1f42040c000509a551500d01100300800002040710240e20807410300404002400f0140308250b00c500f100c41540ca581101044480024610403890069400c00024401118804000950300500c1d490b500d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 982692706 1250 982691456 982691459
    0x1b0b040c08060a0b100e0109030f050610090c0507060209061603081b031b09010c06060605070201030f020a08041b05090910061a0913020d020a020d08091209040902061e0301 76
    0x55407400400400e50f004051070103001c4180c0c3d43e40d607001100901e0362440c0c038048011000004a440e0300d0180e0000f448062041c0006040120100789540701c1c0d04040201034282c1e9696200b90300b52500c050901c40401c108002d500080342c0c1c69001001d107100050007191504e401800b07079201c8030700061000d030005903c0c4018440300117240010075041c075098080060541c08c00002908487d0041d801051044a002450203500d900640c80c0a500c541c20400030422180e0359000503120398458002240043e24025401c001500d81e80309403084da015079030741d601417581e41e41e0310105031a01a1140c0c580c20b40f8204030020780ea6035001105446003e4100140266580544041e0180d60a581160074909502c0e007980c1c508412000c03d54007101003c40741c40e140c44952401200c000e1190500d00c0541c9400000c41c00c0d081900041d288451008941ea0049243d94411001d03440b45411920255104030400800704646015003185c0001400140010b02d800c0e0704070380c040070103c9511405090040003100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 982693956 1250 982692706 982692719
    0x80108010501050a050f040b030c1c11060415080603120c01020702040b0d1a0601030b101e021903030b0a08010914010b0906060d050a060f090905101107031b0b040c 72
    0x1074900400080ea41840000c0c180400100100004201c1a000d81c1d55104200220380e010003041c9031000005c1e10360208251242d1503011100b240d0441616005800c030b52210090402000301e8084500f010300001c00003204000485107160041c02a5505110300c0da8400c2c01402102c00a1401c0c00a40c0001603503036650f0300c18001034030301c0001107a120b681ca44c008130010800383d0013064120300c0070880d02040d595410005074001c001c418000c41e0040d4080310803050850304000300c0b42100504826110b000070394000308990310b1481d8041d2004607025140c0010000f8003c0e0041220503a0051004881c1512124000d0031a0314821003918040019500301040c007800788641c01801070103552020840c07400a010030a2071041701c0aa0f000d10b030751200061801081c1c1e46c02178018041406850300b40d01c1e6113441c40d0014066601090782ca9004248200e0480356244c4a03410704110000300460810030300da20155050304403200304412040d2344510700c20005010700f8215100d10700c2982142c000c00e09040 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 982695206 1250 982693956 982693961
    0x1909111e01030e070b19170a022215050d02071a1602010209030a0201080414010f020a0201060512061605190906081e0a05100b1603082a03180d08010801 67
    0xb0a01c3c50190841081400900300b810201c0c1d0501c240f4141c001321408903100d0071180c04480c0405501204015010b11810038400d80051510b0f1604d550b04003074201d0040070503c100c402c941701c0c00c1070381c183c1e40d20a0803075640180f01a0054580441c801404c000c50350302c5800708401004910003000c3c1401c0d04000c504000141801404c0510744000c50070071031181d003c65a110f286282c0a0f050001900000d402c0084506006091a5000d4001e102d50300d414100500a90049190300c03016500b0035101040d81c1c1890400402c0701d070034500090031180c0310309190010510003031005a0030803030108101604407008010b5118030115603600e00d014180f81c0000107240e120058042613100803692018000b0088000810341c01c1000b044001030651583c00c42402038100903849034051000105800b040c810340c56910b800c1c0c0501a0301c405045999070356566050143c80e0941310140480e5050340080c581004001d194402265040071074544100b0700c25510b0700f4600b00c1c902000450301c42c010f001c240001e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 982696456 1250 982695206 982695221
    0x21303050607090b2a030a2f0705060d020909070c0b01060f080a11040510081902040e0c0d110403060e0f010b010504140a0b0c0d171909111e0103 64
    0x2850043c80660500c903404a081c442e9000000b02050714a444454500100c40301c82d0600e102c40701140c0d40c888594001910441e981506c80444aa60070709403014496440e18501c6031142c540090402c850500e03003040360030341260100648490742441100c00c0354650ba416140500b4241d00d604408502c030f45005070030030340140c01c90401c0115141c41b114a041e0030000c1c49412850642c0080b54561201c102d08102e07001d00c0d03100907030000c14050414001ca4218034481e0084003000d0140e20f06d0300002180307005034803451040760034a084480019403501d00007070280040f8000300790007003000c071000350852038150000e40098a856555a81d6060310079420404c011807154503000921100b905500013174064007483c03181c0381a04140c1e801743c00c0c0580d504154400900f02081c810750700e40101e00c101a40c2d80c0c43c041f0980d40410242101d0a58440c008108144a1414444900c10b560b60041c00d1a02500080408856001a160b0040c1041d42c40001684c0c210109089020043c81c21000040985904 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 982697706 1250 982696456 982696471
    0xa060f0f030506090a0f08030403020f10020d1b02070302060309070e04030e030c030a15020a030e10091403031003021e0d0803060103061a03070e28051318060509030d0213030506 78
    0x166817002600700041c0d03840340c940009000f80c030780d51036040c00e0382131001c00104042c02d401118000180c1c0d05c010340c040d01c4014403025040220041f215206000210300504200240e0b02c9020b041006290103001186d00029060a9031640f9644418070f800310306050310214003040080320480320300d060400104d44501d800710010540e4000c02c2d11000903465401a03541611038002034401003e034080d0b001500401581d501b10f60402c1c5c00c00328407034001d05914404072410500310050280030341c0c00000ba2401008080080c8800d1031950b800c01601d40d50b0400e4180d40c2244580d08005070b0360752007032441d03001805407803002d54920b00742c4001030480e90290000d400300b851461044075200700310300a50360b12050387c1c1032207043e945c403850004810009a0b07418007c440d0300000e116000e642041159021504103441030a181c0c20381001e078809640c282e1503c0981d00d110b10102d10089550380e008107800880c05c3d81030701d103031004900c0d03603070103a0b409003519a00d124520041002000300c1001200e510002 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 982698956 1250 982697706 982697713
    0x9020f04020315120102070f08070b01061d0118030f1a06040e0c040b0f1012050a0504020f09151201051e0906040f081201140f01090501050a080a060f0f03050609 71
    0x207280d1441048207851452030350150100c107000344003a00096041f900c550b03805c8003150f80554414540640240d104810490f000c8a0203c00025540e010b1006400c88120446d02c00d510b44008000440b0480340c80f40301a0585851020000f02041e400d012951406004401c07410131050411900ea64007103010b0011406070b840c0c14128000c0c2d150100d80103281501c21103020503c0e030308000000e082c0c400000d0041e580802a048200034184e040000018901e01c03880091049a07035081b0070302d04a9808460107900282240031403401494040c07181a4411003100390604600e4016000c00e00400c2455101c80451790344405202d100421120048242d1000c06d5007081c90b440c02c4c10307c1a44074200540001c0503030846014001c1004420f0301070310300c07200195103802000d40c3c0d201c12070500041e4801090340520714a4911003040e51282000c0d20944070180c4501e407600c400d41e207044500d84d40042c06003844656440012480c04000f00240e0024080d03688445491030450804504144018000740d60690 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 982700206 1250 982698956 982698961
    0x50309010b06270a0f060507060e011401060305180f0f1b0f1e0904030302040510080c03160513350a150902031005070f0201020f190915020109020f040203 68
    0x3c000c075024000f600014400032103a0040880c500340f01039000f04802250700100400d03c55171040160611034000c580510041c0c4007400308a007241d4010204000070103480c8010301c910781c020b0f04810341004001210486411400d0303091400c1c445000c5000c4a079812104281c81c10035410401c07819040c80a00040841820b40f600007102810f0440300180030762804c2003030f4040c2c800c03841111704107048050040c60561806140c000c00035480f41c02580c0c0b082601d803400c15140c5102d4029240300e100500200d82ca50380706d0600344031140c02011401d0080001c100044100d14884030007540040106100310149100201114517941202e02401000840d00340c5d044035622000280f14004942c002e4007075100c0c141100098006082041030107034042c455250b0601001c02160b000c50304c5012075070740d891801c40403c201282030748103041c105641c0e078405200d0040400c7d050030080019118500749030000756507032441c0403102014603029002503551068500c0c158180108a0700c1d1003c03040b02d0071803852 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 982701456 1250 982700206 982700227
    0xf030c07080304053a0c030b09012c01090206041707060c05070e0c091906090605211302090a05070e06070807030c020604081203011a0423010903060c050309010b06 72
    0x6200311700b441d0b0140030542042081d618200c3d003811111429141c001c0480f244c0c01d003030401c03002e11244012200070f880c1c0800188150418850494409030912004070030454114080300c0c1c940c035440450606540c0c510300000140c4ea00000bd000404000e01d46000e0310b01210105801c242c031940c00001400394850000d000100e001c22044227071229420040d005032610306680c6802d016810740700d504208280300b808e440800108004007111a641c0c0c81504240d1034100480d800e029501c25120b908035104c190b0b07800186802c16160340040b03800d4224040e0302c0142c0018120400682d00c0551055581c0c043c0711100343c1c01081d181c890b000960b0200c0c9040c1440c1d0765440c251045440180c20444c40002c03103411135417540c08850017014200c00701c6200003824a00b0689030b920030300c81c18490110b5a81c200c0d214852000a66046600d43c00d0b10350030417000700c80d1b0085680480c50030039041201b9078801000241c1c0900c40c041088020303640700341e05da00e40420503500319011a02d0316441804207100c1100348 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 982702706 1250 982701456 982701469
    0xa0f0803030a09150e100e030405011209060b03061003120f0c06181b05091308030103080a112d0109050d030c0e061207080a0603210507050f030c0708030405 69
    0x120382074180014000203e8189848500e0300740307444a50407424180d96441240c80081c24a61100361181d041045007030880d551540c0348920322555001c603c03c017000301c0310042d02e03500050740280070300808111500100f0001f410003804644c100c0c1c0065a4080600900c84446004c03144014141800c5404400524018182264030540141303040d480c0c040900b142c0e401e00513444401c0e54003140302220190a00310001d0034111b40d00485008485000028007480a80b5100c0145280c200407100e01e581d0958881400c2030b4402e110702020300c41410505400d90324100304400c50035040280301762034040484030641664031600940841790307041c0704154003c11004500d0b032050040c0c1d0b050000d9032a24201c025610340160302451a805100070070502c21a82c03400d03000509c10f83c0c2c40c0d52880e00d107070b5409a44104854690002828508254103000115082c401103125030714002d00f425400d000c61562901d10702640316860b9905a080402e00c0784c1a600100b11410250a0440103181005d0824000c51903 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 982703956 1250 982702706 982702711
    0x9081036060b12070f1805270312010e0609070c02010207090b0a09090b0601110f19060902192105190227160509010509130f0e010b0a0f080303 63
    0x820341d6a6140304120f07551501c090300d00094071001e440e80b0540d40c00c0340c14144440b52003600c80e44108464080d00d100380d580704141c8944100420040804003940c49003040418001c017480b014401044031a40071000b5001c61402000304286001311480d10b8414020031560141212050204841007000146c3e00818446d080d14800c03000003601c615a02e000130201f10565001342105450552160113000e0b2440607188502d0081c2ca5100c02760058019841d0784035a80a41071580d40c00a010307014140e0f4000b00c10301c40c05401a040482e0141304c940010302d550049410626031820b15200400404408104103e5900144560f91342c41c0c0c4647c0c4c560680b81c80c4c040c000722200b00088680c0004541c3c460a0030708003400d001c0c80400b0b084442c03240c80d0b020301c18103543d1986c4468120b0000c03000c052190040f182050010b07960581021410030030b1142070049521500c0b071032900c80b18086011a039031700c9a02481c43c4001d0010807544d8211003031040050160b0014020005c08100c00c5c1304640c000411241c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 982705206 1250 982703956 982703963
    0x31202120f04020a150504090507020f060c09061903050405010c1e05030417030f101a040b090414090a060b0901080a02060f0d0c0e180708070f09081036 67
    0x24202d96aa2002601c8200c0b1900b20300c40e00c0c40c4144410804a07444009003098401465081040303440b03c030000d983c1e48d03c014000e544140d011a000800d03c0da07024005c3c1100c007201404050428524508900c3c50701300074840080000e1750b61041006120f02401000107442150400b1010f602c0d44541003d11511795000540c1441000004901082402d18524109652440c40587c072400d05c1110114411f41c280d40e4102c039182c40c580082a8420300260701c0d01052880b040142c501480d06c3e880003256045409096403040c1ea42c1100d001101da05440b85200c2e0900101600c043c44052509400b210390103813505000c2c0350300f240140a03154000580c016041c1d0100c0c2d03203039103400c1c500c0444a00c0784195aa250b0110b401d1440c1c20000d9a04040e44403a48a82100c0c1140a42280c040d0020026800c82e450700c0015041c80204800c9801403104070302d0b101c00d51512040b456214142c1a1800207a2903c04940541c3c907101080f8150030a00c200421081802c10444450b8041c800811380c40c00204018 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 982706456 1250 982705206 982705231
    0x919050f040305161e1223030a05070c0b01090507030c0201111210030503161101030b01020c0f030109060203010b090f0a06020a03120b300f0304170705190303120212 73
    0x41090009401e400c40900703440c40114000940c5c58a800c403010303040001e03c600032407083d006a0f900c05944580d0100a005107410441c1180e48800070350010f00409080101800b604502400105008002d4617000c2c119140c004038280c100b00c07a00808950b2140044402c69160070f080311074201daa90212a0904041116080c00d80c85070503210180c0805640002c21a100001d10500c160041040248280740100109200320038014015425901c000d50702d24010707001420746040c180b8141c01d80078000301d005400010100b13182d0b510070040364800c2e00705a03c0303014003107100645032903c034049405444003900c0e15500580740200195880c041010300405110400401c0843c03561340f50311801031110000d2821a0203a080204400020710844408030501300000c0d0100c212040050300744d6105210400a5203007524041c0d184c00300d0300202c40c241410780a40040000c1c503135181e0401410b100e000300044801e07d461840c2c01303021010310341412101280140042c400800d04103070856031110314245c00 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 982707706 1250 982706456 982706497
    0xa02060d0b06190e01020d110c100e0a060206041b150c051906020304060501140a1e0e07261006050c0a02060a0c020f040b090601050c07050919050f040305 68
    0x8040d4092040400c0c2d407000489030340304034070744c0c003400c0c2400804082e001e445250307100d28401c0342c1e1200d005203030b9405035000408041e0729050040307681015400741d24106070b2000320360001456002d250790148005030302030010b001c284841e1451141001c990300030140c40140c9008030300d032401d900c2131b4035103010700107801d040070107014040c8a09000c00a410504500e0724449192035030007904103440548510b481c100000c07810121090804083d90f00c011703c0425090728196440b804280c00009058101c0d040d8400000c1402e40c0c44813003402090a17494640c514107000c40010803a2501c3c09a548034499407000b441510f44a610016003a14258984190b0702d8031090170442c50072426100082d0845400203401d000ca0798000204c01c0c40900c00c8416074140c919032000c000564442c05441984603660501003131056005400902208a81c0000c0c3c445050741c400c00585407810481c0e0709180800100010b440340b920710310486520440c0c0c0d0214028504080e00c00034200d0060009040f11440c50740e25 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 982708956 1250 982707706 982707709
    0x303160201140903100f0b010927060810060816050d032f070906050d05101503061b030b09090a0312020909041a2a03060105070209070315080a02060d0b 67
    0x31502c0c10f0401404a07072810101d414000000c2a004071007040c094030300281560158840d03201d039401c603a9620004654042c4040020300c0c2c81c6404444510041d07681d20000070640307414442a00802804800040c1c0c2034a42155142014070f04900320700d50350002c0740140140e5540000050b0501c1e0585813040404030540c401940d400d50301030f58180c202900305000b80206400080d560141d83c0c20000520100d5510800c2c464006c0e26080c0042c9990403080c07900709201c4465104400d1188420300d403007503459a17030325124206c404402103540c130b882140c03800119042c0c01d07000b40e048690f0241c0e0041d20910304040001e0b100c140c100790003003c102d010011020003040c1030301513038804103009042c2081428030389040b00500e86140f04201c03800c078014002680d1802c02c0394452691031031310076010624042004100a130f5520040c5800e052040c18400e0741c01580303882441d14418810b544002901700d00c040004a0040030543c0030502075400b8003050030060700c510342039036218503c1480c040f0302c24245e1030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 982710206 1250 982708956 982708997
    0x60c08031306020c030d0b030d1103040e061504080d08010e010509160504050a2706060917160308120901021e0c0f03130e0901020405010c020d020d060501080115050303160201 77
    0xd40d405a0348004500e06c0614a59948103001030b00f012030403500e4407915400d0640d070303030244d100406c0c90700c2e04180300c20408000300528150b400a80108540c4c1c2205442c3c00c0a00e56811603040343c00641c1c0aa81f525014607040030151b80540400040001c40e507160400065031400c00400a40605c5c010008540c0c2543c0034209403005408018124401152605a490001d0b500c0c090201e03025184190300b20010b8404c0d11820040c0c54007a5501c0b104a070500354003402421b4051851a128411815600481d5074800b1011020b540f00b21202c41c4c1e14285141c06510200f009801e102d20350344100001d219440d03c0d58607102e8454148040b03952994010b0640c4c50900d03645c14001e45060100181a003020020920808181d0b0984401405640c8508490908034000c46c05140d007c2545c94070120007510301513071001e00321480200340c0c042501d029541c50042d22421f901c01443d40e915000f10215403c0120301e2107019202c01e50081d410102002c5290060b05280d202c040d0500030f180031130400c0d09070b040 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 982711456 1250 982710206 982710217
    0x60f01120c0306020921010b090f06010f080405070b16051c050a0c0507050d030c0218040308010308030a020d0c1d3304090c020a0c060807020601150c0c090213060c0803130602 77
    0x10040f54110b106c1011000d01901c000c0050030302c10005500080c101100300800c190041c40103a40f0128480f90041c0c0640702d180f07015005540e2441042400079821250300d0003000a82032491040c2c01100075454140e1400580001c06900610100b902c0401e440e40141130362610f04c1d2500d400c0d00c58100741e0408904044003a080f407030b040551388080405040d044850198514400c0e02c030070841910a080012161405607401000181c00b07000400c0880e191001640e00300f110400018606003031052114100e0340160040d0002c5141d072408042d010302ca28240740c402c40c4040d521408070f506400c2050600f40003480703c1e6000c0f03249010005650059006c01d6401070101a84100440c400011010790349010301002220f5403a0800030100c0c1c0d041c40342900da4000c03020390b0002e000c140d0a0090305500554a0003d4008000b20780110f8404a4078203042440106520b100040c0c4c1d42d4550310140442c841107402400500c46600814000203d814044942c05820310b07070041d01c98125464000081e1141 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 982712706 1250 982711456 982711489
    0x504020a0f0f111203070e09040f0204050402011b0b0402120c0609121f0e120a020d08072601180207031b02010e04060e060306010e060d030c02030f0a05060f01120c03060209 76
    0x84c07080e1075050780560001140100d055440d40c0d40307040282c1c405c10200e0b000c101c0e4000c080b00425a21a00181801d403c01c6410910505200400403a004440312400e0114041903e407910010144070560800d4441d60000e041041c01520500d9124804141d4600c01c0c820103e0041404200394001c0040500c042003e0a015143c10001c1802c080e003002c000d0720701c215181e0004e0040724880c2840c80da013081229118442600584242c84a003802a48c0c0d5280040941c0142301e80e0400c41d00c2450a40d054052440381c04842c3c1400721f505180c00a803c80c0540b0b541c039281c241c410050000800d80104d8040000b9111900d424900c13507403440121803100e2004c40194100342090804100c1049400c0312900c036071400c0d0b00304c032516a07aa900200030000c0584106400c41d0201c10030002191003803541200c550b0000c2d080700c03035041c043c40c0258034000c08445c040c0d4503500300100b800700f8200790400050050880100d44108003200d500d488501004900c001406c01c0d9000811500715103c281031103412000c0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 982713956 1250 982712706 982712713
    0x15180b030c0c070f1409040c09051f0f0b04030803040c0909151506390f03020d0206102d0806150603040b070302030601050c190c0504020a0f0f11 64
    0x309080c40324800d40042c00c00c007540e4000ea000100310042030b011004212600d59031503480c22079802040c41030448001e0b20a403880156100f020501c92942e01880b0302585218048510910018115418030070094000c445040482541000107007885000d81d800d4a401c03100b51030b075a07200d40c40c008941e5103091f84095001c508103000b40e818010003a43d4200c4d1010824024401418000843c2200413039034000c000c04070311003801c41402da4600d1400801c07a406000450035000b400c000903c4500320b5500411204a0010644101010b90510405a4200a0740000c00583c01d0030201031042e41668040d000c4901e400302946543c00c1d44520800c106603194000210328281c5403404180c0300c002c101c81409000c00c03400c0d0428038904001b001c4902c07893b003000c403040180d250000c04a002c0d40c0f010340803d040180c180581e120f00c480500c00c40340500d0750600c0281c00c508192408540d01c800071751216114603c18007648401e6600300000c49000415450700c0103041400390019913601034426a00301e140e10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 982715206 1250 982713956 982713961
    0xc021006080c0405070f0207060e030f011a041503030c020405100b0d060e0601020f0c090c1b03040e0703020306091305100c03060e01050411340602091915180b03 71
    0x310041402d0001941c10b0b60240115900d82d102602d040071080c4680c0c0041e4081d075401c0000350300c11100c1c050b91100040c01c1e90300511201e00c0450a403558818990440c0070300d80c100c00c0803890710f441440d440c0042e1804034a0f21500c1e40e100540b2415458034068002c40e161000107240c2040d816408000c4d20b803410116403180000c000079001040c1e2405421b80b52800400461402d43c0001388040c00c551100c4000c100c1a103035001404014030010381502d5a00c1320501c01c00d42d18041c0c9950728610f13010524011900c55190510302809440060b1100c014148100305101c880e403200712065600200780e807140005202e851400a14103620200301070070040ca01480d40c8661681a0030040840c1c1076403d013100719989440c02c00c01151815510f0041d20302082000c2200c0b0103000c0e00c3c0041c1c420300041b880c002c804015100f646001000301c011905240c1c00154031140d81b82c103403220428403107002041e614803810882c4848805d501c2e49800c0003403060b0a4088a9a1090300c00b0f0031028041ca01c0310780b616030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 982716456 1250 982715206 982715219
    0xe04060308040308030609010905061309170a1d0103020325020a05030307050408160f150e040219021b1c02060c1912170604110c0d0e040f0e0703060c021006 69
    0x1d402c2640c2487c41451080000030300248540102400741600820810714698050304901c000d0900030f108030b8050b0701503041d4204c0111100e0141c480700306942c43d0031000e6440031b480d9400100c00b40d041107041c5881841488020100a40e0550703040351480111002c1c403d8169060f4601500080c0040640c0300c0001040b105981c004083c01c100da410804a6003418102040071190300d2071401594400c0b0300c9501e040040402000b402c01c4843d03098240354022258040108051740d2011400603440704500310b40b407496aa040107640410511515a0040f01070b034440041c80d8055080744102144503042c05100a42d541c0304200d480717015024085400d2098440c643e1002110001c000395403031040c10b608810b040b4050a002940f0316080e590020741980c401003000b0050503070304030300d9601c20707400c0c0080c5c8a4078004019008251541d41c6541c5014032915040109981011581d03004181c1014003052017203000089550550f0341c045408030307841c90940c504a280c01108454000640c1c01c1800001c0d89 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 982717706 1250 982716456 982716473
    0x7080a2a03081b060c0a0507020d050607091511070b09010504271d060403180b030a14090a02011b020f100903120e030d0c030909020c28030f0e040603080403 69
    0x20301d080504a44280056402040c0c0c54a201700e44502c0c07070039410404480b0103486840100304040c8014400200031701c4540700c07146415000c4454030041040030340140181c1600e0b80182d5010764a61800e07408100101060984070641e503c50712541c4000800d001d04141e010b6019500030380080710440f05002001018444102a0000c5010203546041c00100b4218403082990300c400c0c4080001306855160b5503000c650700483c0040c003140d119015040401c20254400045001c0e001c840b002207212151410b0f02050240f02419505a550103102c0500050741c110740307000c49aa85a841644407a4050300105002d0f107584040e40d544140c0c612110300032107402121344001d4902400350101c080d40180b1054440c0a00c011846a05900240421801c03501c10a0f01152492091074000c1d5525030310f1010100340c3c0c03c010a03a00440d001011201c2c3c01928120018008034a4400b0020001d480d0340c034042c00041e003d40c3d0070400c1100c0f91065609944030b541000d00115484502250740302e03540c2c10304440 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 982718956 1250 982717706 982717717
    0x3091912032703031b05031608070302060603061306110d0c0f03050a05010b03010513091506051201021216020c090a05041103060613020711100804050f07080a2a0308 73
    0xc074000b49011110701c0d80055200c192589a101c100d40c1001d0000018404484404119490700c01040768840100d502009803026510a000300d82e02c8142914000e81090001460300303001e5800482000084030720000f10482d02908140e000881141c0d02c084502144a40d0000084035401c0c03400543c0c89550007040c00c01d1310b140e030781e4040101391261014103040d11020f21810714490350a100511003460403648903141d02a4200b00062502c0039961022041d190b59400111215a0341400300a5824610f4003000446507880086180407022030000e01100c0006d00b40e0700010307000c4030101114a00811031006000d0005040b0081440d0054600018007400c440499000c420100255030504000402c5402848010456601e07016015400c07002900012016204075100803c26000b0751038034400b18120903035a0340c03041c10601d403a040152400b080e40c080e1260301e50203d582006466408682c004556070300405080c150303000455550031010742e0303850104210140d40400806c011f42c00f0002c0a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 982720206 1250 982718956 982718987
    0x30c0d0f1b0617010321020a06110901110a0b04142b111902040b0a1e0503010b01020a120e0d060e0a0507060221070c180c03050a0b01020309191203 65
    0x1900004940b116102070000c1c800189160702807926054015624060001b84a00920440304039114985a070025a6010540c26900302c00000c1d03001110b5a000902c01e0010401d036008029102c26552000d8211000401c050304c6d4040040c9101c08151003442002104002a10424080780c9041180ca0180c1e0180314001d02241ca1000f04154040000c00d10320366000c1c81da041c2e070118092907001d01001d81100814982e110070b480c0804145141d907000086440c4000c0000700558031b0415007403600710b4032041011303410340d44101c201000180ca441c0316007413508038920f00b0b920702100700f502080071b840e012000203000c1400c0c641225044140010650442ca000d003003190f20300c503911081661a020b100030860b6108218441c119441d16400c00240015441004400412551212015665001800e9192609442d241c2c1c0140072035040c050036412aa041001b08641a403406c0041d50700d115680742c00c0d0007402140c101c40041003101c0d0f120320003041e4211103100c101c221850000c00b8101e0840041c1e = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 982721456 1250 982720206 982720217
    0x309050406060e010c030305181527100b0d0803011e050109081b060c0106060221090904151d150a060f0b070c151d01020606030c0d0f1b06 61
    0xb880e6101d101800312920060711000c160785d00d0b030346049000c1c1ca001003080d50903540e00d44890181d810101f085401c08981080302c5401403c10603502c90003450390308034054882d2183d07040b40c03004040100c2e032074103501c6903000009400c5240f00045000303098400302c040c0880300040300018800d0300c541700600c0784810080d40c500c95161500010350b05a0501e000c0e004203035105111b043c0c1c0403c000030b14080000b50081000342051030050115003919259048000160070154580301c040c400508140c104407203007240b0504080d400b00215181c0900117102034181115505d444900303800b5544800202c1c2c0b0506142280101d004007010380ea802c2d40e0089400c0321080b000003030402c58007803280d44c0c242c902500c250882545844141c000a03040284180c0f05144081c00000300d00c0810044c40261310341948590701404004a0500c0941c03148898843c1590003410401505039008194034002e200304442001d240d0066080c080445030700340c1d000800044008525508022040d03094000b211800d41e10b5 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 982722706 1250 982721456 982721459
    0x9050906130507090b220b0310022b020d0501030809280e090f0312220f02060d06080f0a0b10060212030c090d0303140601090303080615160309050406 66
    0x80764010104640c058040d8104500603c10400f03141c100d4a0b61003c010424454907a181c1000b130703800009a8191003895945454590b518102806908503c0c5400c880c2141002400381c500c21200710080c0100d44403942c1c060300344030749403d11707410f640d0820200780c4200410340c0c613460154801e51209081078400c102c0c00320410910440c10b0f41304807e080c0f10b611281e000500e41008000c00e0140645010064024903a007040704002c200080c05030b84c1c0c0c182d0515030311030a102454101d80c051528070b0f00e4003403107054800404a0409051900801e6064901c107980300350040c1c603580100fa0035044002c20740108035588208140004070640b41c140241c2c4c1c0d21081d52511000c0340f03a156854840d8001507044141400740a00340030003d11740c0055014200e83c82c2440102c001119040e424004601203039440a1403180061002d000651000080c20a004850b0031620b0143c2440b40081550303124a43e40c4c243d4130003041060040d6542880c441d04a050000e0542c034019002000c1c5000705400340b40381000 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 982723956 1250 982722706 982722721
    0x60b0a031a040606120c0e07020a05030c060717040302031c11211f12080405040617010507050322060f05040807060b040b0f0405151f02070e01061704050c0a09050906 73
    0x1040d007096502020506021f85407241501e03110000401442c1580541440140801c1e401e0004140c00c0b00314034090303c07403441c01e16005400c440100d00d0200350b00d03070038004200010341c00000b260311056001105900c0002d07100900030203010113180c800e81d960000700742321003185c0540280b42205c0d0310107281e0095569031411948102c0b0280d080da2481c010040d50b0800c40954070305600910f0a01412115213003685800214058800c1c035404000b0303910745685100c6400c0000c6c030030301c1d8000c0407501d403c910710b05040303035a41d0365040786840d207464402c101c0340342d07200b0402a68031210107054004424000b6203411304216080780c0140742e0a83c1e109041514800c01c501c3e040c4aa050710b010001c000c0403100501e07505000091400a052590a010310040c1e0f4940c8c0e561050882d0282038410140c42d014421148000d040c81c1032a8890011035003140c00520040d0b80080181c03682504002d04408103075500c1c200240342545609004e034002c4546403003c103a07030340640c2040344520103690449415449209 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 982725206 1250 982723956 982723979
    0xe01120b0d0209100905070f030e1501050f0a030606080d0f02010b0d1112060f0a06050909120a02031210092f03060102010f0f050a050f13060b0a031a040606 69
    0x115050707889041c04076500d0040c81d251100c507401c003036100e038903582044c0c0307903403c0d403080312800d68655020420100004c16629414003440c40903810080140c2151081c0284005030340300107003e0548602400f08604116403100f17003183d00215008681801203507665440c0c10b0310b40c02965031440004e0b41c6401c0419196005010302071401e140a4808500308520f40c4595104c1580407414a9201011401c0c4000c002070030003d83e80200c60080c0f140b405401c10650040441d100c030b07400765000300c1c807030000c000304440082100d900015031f1001080c2c0c3e403621180200d040d80320700111148022040000d10110740b8801c0c0e03c181c01e445001c0010000440d4510b0101d890650407a41080613140c0b1007501d80b5280400c0003c0c40c0c0020b010700010400040032807880701911b00906500d0000c6035160100f059040c468024541c0020480c1401c003400c0c2083c000503950484004000741c00070340c5070701144d074068880c200d600d801141c029404003200114992031000e6041c040d501654a20304110b80405c01c1074950 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 982726456 1250 982725206 982725221
    0x6150e0a0b0313030c022205220605090f1b010206010605090d110301020f121012020915010e21071505040302120102040b07210503131e120e0112 64
    0x2808103a0031595a00030350343c082000f0807011003c100f6400c1090005031030f50211402a0180b149003000c1c6000c074004110100d80b0b0042409100c10007a030201a450544034a810f404243c102c403004c5016680c1540d110300d0f1000c080300c03001651040000e50201c01902003d0313100c044009a003034407902d9990f00d800f120325004120ba129400000201000000741d018040c00041120140001d400c0c0303c0003540c0b12640c4d230000c82442c99403003619020400f07610149107000014002620070300d0b040e070000e500440c00b11a070003042160303000100014194642c0c00355440d00311001005001200900700f20194801c510500004504140320340000401d180b004280c903031002000d03554645081c1850341d020000c070840200030791100f5560802020402c0011080105405400340345074030700c580c0c18132801511600c0100b20080c10072805200344004490103001c2440b003140c0199408040c240c540005816003543c000009000000c440c4060038400e03048400c003114004d00b40c076589190081c0020740400d49541 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 982727706 1250 982726456 982726469
    0x12030d0f020a1b0c0b0a0201091a0906070c111f0813050607031e05090703022409060d0b12010e010c08040218130501020a030204030c05180609061306150e0a 69
    0x3d01a89581108540040075046070144548807182c550702d168190140d444003810350300507511a03034020148000c16182d407a9590020010500a2814284032512620050448010040342c95191070902c59002c58031720328004000d05804403040080020341c854400c5070705440c0843c0184001491210184440c548503030f410401800b05540c07640422402048003041c0104071540d1901c55458020503441039910a9440e41d00400705036003180100a40e0b2110207007030050304420080c5a00c12621210207640340401c2c10f48100391500d450710000d03409810103d1140c1d070040382c40031071f414100748150802e203040d40d0702c60002c21952000040c00c680442040310041d40080341520392544030411902601e40c0100c9003029140d07142c24940e545826a80450803620000b03401080500038032460b82c580700d00828088452070f00780e100f00c10101c400c0c1c000c010305c003d2048204000003441c0b07444115080c980d1940f1440c041040e15181c0100e054104c244005800c00650142d00c1c650960400000c40010381c0c00c0b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 982728956 1250 982727706 982727717
    0xf21071b0302060c09060408152a2b05040c0504060b0702090402060a17010305060f01060c030e090408090612011404020a09090e121c0c05041203051812030d0f020a 72
    0x68084240c42c3d0780d4405641c5d240c109404002c0010b0b11101400600e9803102d00c100102110b003401c3c00c202840d181ca00c0140c08000101910100c1c160f0400300c1103400700d000685c1c4001ca03005581e84000c0c0d0600000d581400c03c2030a010030070007003000b031401d000c056480464003000b405e511400120030030300500c403009402002c482d0101c0c000d442c2c8600a0902d18460f45000c076007980c100100c41c2403e0394207070300894141c2e2250781404419041c00c02d80c98094026454403040c00d2110340c41c0241300540d101016030154050102080a01941100711142190058030380c0c0d0340c409194a13101010300c8241b01d81000420400f400d00d100340f81034000c0343c007072600c580d494072003541c140011381006000500361441d9070310452001c105107200d0b15001c1d0161901b07030043c580c07003d540008808151a100d001d00001c000d0104828003140340900807035640d10350149010750311b82506854002071307584e040030b040380d2020b0040e9981c0d040c00d40000007000042b0307500c0001c0c0543c80a0902c06416400303103009440c013144 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 982730206 1250 982728956 982728961
    0xf0e0a091a0a032102120a0305070201060b0313060b030a03080c0d200c0606010906091a09120604051207020321070204060801061d011a0f21071b030206 67
    0x1055006060031100c481e0100c4610503540703000401030910b0f940b00302c8045030002d058910301c0c801c1c21440300443c01c0d640080d0444404800710740c0068401c41240c20203060703440340032aa00c4d9101f548182c3c0640340d07001401d6544c1c241107150400b082e8103107804441003428640801224200403450b02d41c3d0643c1070301c9500c159112680b0204007034000040c5042001d40d07401015000d48210b0b031410a007418880300e0b140e501d54202d8201810040020140e0303060040d680707020868184e02000b207900315181c1d80b8008941c0381f80f0400c0e000c03061245498459210486164200e841c2c80089002801b55110784111240080390302e264240f2401000000b0794503800c41a9006803920503d0101d010042c880c5103054a001c21990004007100e01c0781d005100c4980d0b41d00030a0104440d001402610f40744402c018104662500344141c1c0c04020502c407041100002181040000c840013086d56031001c43c0c00000e1068041c1990f0300002007004903403142c009041c100072030720824418000e103c402034059002e4041399 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 982731456 1250 982730206 982730219
    0x3090f090b030a03260f061302120f070309080c160501183b04060506030c0904060e0f2407090602030304021908100e0114010e0f040314190f0e0a 64
    0x145141485c00e040079051200c078802012560024600ca40341c00c43c180c650609180c014010241714044052040c82d1040000c26540400c182c003881c2c1c00750101010716000d42e117100c0c0440251801d560018072600000c56284982140442e0010b0400318421945110342da480004481c01041c002085035141a012410700c549944811504900f040c1106603410402c45083c040755185010f141c120260100402400200007883c040c00e41c0002c0120018590a216480000c480243c05400204000d0f5076040c0c40d01d42c5801400030308001c6580700b003a1541c03d800554000651140840c80760321003406040003494150240d540720701070b9607440d402182075036680d03828044640f2044524807c95542c6010016240104015003030490701c1c0070001143c414000c80200b400d450695152003050b00003980140204c548040e885a408040304007011450345a50034166048200040200101e040000e491001080c803002d5000000c0303142e64507010742040525045601301c1c5808406680502c0202080006 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 982732706 1250 982731456 982731467
    0x105030c0c2b1701060504120f05120d051b0f03060f040f0c020105010f2403020712080411031f1e020c060628060c0503090a0303090f090b030a03 64
    0x80744007042100c9009940b4804014000d00004501980307a02c40c00b0480989036219030110103001c01c98418243c01e50505201800900542c0944c4454060000c00300d0248141d01c141100030f150000c040e00d20f204a0000c84c000154400811020400c2c03c00011800c284c0b149a102c0c8041c01c80004110308185002407460415403000d845541d0082d08516554410350f201d1080008500002000084041e01141d000c0e0a40e841680310040c240030054040000412020311074210080110b10000b00744d40d0008150002d0042240143c140785e585e201c416612031300b00b051540281d004982c0381030690b80c0310b410503070b66880521080c03058142c0f150b80140400c00940051559041d445030503080c8580d5100301004a03088481c12802640c03202c1c0c03d004007401d0400189044200304c80404602c1381d5040e400300c804151903c6401c04004154185000380603044c0203448680b8001440c0880c03c994900300208660360500820002082400000454174024400d41310885c8001d805848600c600d91026100b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 982733812 1106 982732706 982732717
    0x1063b28090b030d03180816020108060603071d0f03160f0b0c070509060105120f040605090a0507120302010212010807060e09010303081b130311040e010b0105030c 72
    0x20a503e0215507807400c03610342c3c00c002c24a4100300d0b80e940700c0c2190284000e0303c00348005c288140b40d060300c0806140664001d0b6a44a81a100c11040101500c01650000c0c04210100304400c0f00780c00d890001000c88800070074080c0c0038400040400c0c103003081c0046880958100ea2010700003500301031142d001500015010354101405440d80c50b540d030510380202446407001c100050074907031003001101e01c644091070715810351703051100549104480595045850a040c440012408000000c6480900e500440102075041c9040300100160b4a42c030b40980440d502049080040d0252447c110700034212400180519460007100a00040026040340d200d15045801003000c13aa000e038040750000000910409a1464801c100140e40700c0e09100c25804c6e0f032100d5000003401050080c03a441088161424050003584045160032150f245600502044090004c02c00c04c1400300b01a08 = true := by decide +kernel

theorem cover : BRFrame.Cov 982553956 982733812 := by
  have h0 := BRFrame.cov_init 982553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 982553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 982553956 ≤ n) (h2 : n < 982733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
