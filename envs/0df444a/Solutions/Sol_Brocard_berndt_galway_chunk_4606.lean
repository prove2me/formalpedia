-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4606
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:09:42.256576+00:00
-- url     : https://prove2.me/submissions/a9b53d66-59b4-4473-b71a-902a43dad81c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 828237410 ≤ n < 828417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 828238660 1250 828237410 828237427
    0xf05041401090b0d120206070813110f1801031104051b040902090f0d050f06010902090f040f02070b0103030e0315070e041a0d052b120b011202070f110411 68
    0x41c02070500b41a030084c0d5140c05600c00184604100c2c85008142e40c042d1400342085035004100d00ca0181c035024681e02d901e4481c0000c2031008440322442c01c41200c5462000300c404011524000420032044208107880000105100c900d144400002c0c0017150b0811031591f03030544100743c40412036030071211060b00303000500c00d41c2d2055000300411031004241c140003960b0940010000618000200c0701a0880400880d01c04030400c212405095546002c0d07040209000200b030040b0360440c8003030b00c542c2d00ca403100c400b0a480c660442c4d01d0f0980194801180350384908001c1d0984044401040c001d106103d40101003044100401d8091490f43e6101d0341c42800c6401004054041000c80c03c91401020b030921010385e8842d003000b0f611074400c001400084a0100b8044a1140092820b51100715840c480f034060b03d0303111070080401e8178a550000b403010100307001216141c01c4074040c0039900c2d10001c3c0740c0e020700c0049944448414410f80502c0100045001440b06440843d030340285c18881c180041c80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 828239910 1250 828238660 828238679
    0xa0503060a1a19120f0b2d010e0d1208070f090303080103110a0b1c0b09060312030a020c01060b0903060709051c05030706050c0304030810030507060f110d090f05041401 74
    0x9803001c10301d011004c50345458010700072142d2541e02d0380c00303050b40c4848200ca541058205142e4000c00043c0600e80c21a00421240380f2440280c0100e0400000ba080d040031941d8100c07100c4699500701800880400300100e000d003a20500780d8501d808103111070007004860388200d04200c21760368503a580b000d15900c0c641c0c41e0300c02e81140d0101d0036803103416003401040c021062409032020840300544040702c410840403003811980c980c005c26000e4540c0c0c40800200b5100010300300031b000e0018000070740c2c9a489a034424024004c0400201042d401c2c4240002d1414001d0080c0c114550201d003138408513110302100365028002c611031190070120400201c050200a0104403c02900500c10b492810f0080d50741c2008880c0101c4000310f4901c408024401450b5202e1155507005203451648000241941c0340ca0760354a1540c840c140802544000c08603001e4404e0f10060540d481d0340046402c0c1d809004c0d40602150500e006600d20500c1701c000c001a07a2030036016008401722540881803140e42007510b03c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 828241160 1250 828239910 828239947
    0x1080a1703070e040516030e07031e080712090312080702061b0d0501030c3b06040b0909010504050609010b0a03021201020708040b120112120e01140a0503060a1a 71
    0xc184002109050f010b83c039035001700c601c00d10090b060018204e1040c40e0107812562044545c4013107600c02d00090002810000c60404103401d401d078241c00d603c41e1440c2c08805071007038000007490311852100c003000e1030380c000110b082175038441e09846004241c0d412040390048000c80e0b184c001a4444004243c0380080c00c12103a904001c0a000e8600d8010000007030810342d0000e9004a50401002c2010000d036240c507102c0c40148202d4608007020b00602400c0d80458240c8030414090050240c0042a001d035510ba00401c00f003070028000c1c0c1002d01d08000c0713060082c0000c8505881501542d40000e11030760040c030811140b603c0c0107018a100c1c4d03055400f0710004100b42c022145203594204540d00110350040701410040541c04002566410381080380502c1140c182d00c4034043c98240b200382c40024441211007000c408042c44c0401c07101d156500100d5454080c0e00c60110b800100240a141059006000b148a1241074030500340325503a4038050811140d0f03400c10504d0448040c400d007564000c041681 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 828242410 1250 828241160 828241171
    0x71a0304200103150f03170703080a0b2d0301050703061206020d14010b040303020709060b030c031e07020a0c0b1204140a050114070e0a0b0901030903110d020705030601080a1703 78
    0x403555041850b00740e107054245c002c907a4048800d08100300b04052200144070490b0700000c69800c02d82e29035005490058060301e9880c0058a803c40d60300c4c43c5c0c40d0074215a00300e009030345403021a0000840892040244070329014000e5003410000303004180a4014034040720507080f003480d201c404544a2000070341001c000c080c0b0050311085a0b1a161040580d03007806020b14812443d580c80c0b65140180c50000c190b071001500c81d0908200304600030800c03060342c0e40052100207003581c036034442034117602e1840141c0a2441040c0b000b014040055400110703100c80c41e10800038154a25240c212043c403900840443d1100c0c80450710005000074411a0320680c02c1201d00c040b42d100e880303181c2d107003800d44003050088000030100004210010303a100700c0e0030b60300080540c0c065020030304010b10581940301e0b41d1240742c180b5407200c1c12101018804c103000300c95076021a0a5840260880c2c0b0020744032131040c4034541c0309206002c00468640004612620300d00d5020a80d4850301d142c0703448000b40d90f00000c00 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 828243660 1250 828242410 828242417
    0x25020618011e0806090a0606050f0a050c1002030105041a0d02010c0f0503361f090b0301030b0105041b05031303120e1f0207050a080d021605071a03042001 68
    0x10b00c4489040c2810031990700300c03c0e2202d844610b000c4082c8082c4c400c00070240d80140341811070030040c650304007013183c42c50038805c402e41d6070380c0505280c1a40d0920a40b929018203219002c5c4038840e0000d00e82c065410303900100c405000c842600c0301404034203c1c15001070744c1d1024244458800546c0142e4125220324460308050701d0040d803580f0341e80c0c1550040c2c1d1400030080b826480306004481e01c00c9449100041162600000301c6205022460400d880d8052030401210500d00448640c0122400c200611650820b2a03480d80c403072820ba2240c0c5020300c01c0301d0043d41042190511950b083ca48100c00d2120765030b415045a849294840f6102c0400e1401d50030321030014a60302001c411800b404014165030401040710100c2d04500c40a000342000524140074410b103c444000341010a08449140d0000d640d90307100d207a034030a200001c0c0b00368610300c40c5601850191000b04400412110115418002481e103080c2e4101c0300040c42d48801c84006080801c81c1c2d60443c22081c2a4900c40c40f030410614 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 828244910 1250 828243660 828243677
    0x90228050607030806100c111302090a0803071b05180c2115100f1d030106171203060d02060315040e1f0608031c202502061801 56
    0x4000c0703030555000b201c054002503429004c10203141803c004010300403140349042d043c45400c80c1c852540e0075407601c190034405e0200f081030b92883c05894041c1c80b0f40316801041c02500965801440d40d5030b40c82600221482240303e21000c030100104103582c003c40d10f01070720b0142d070840242c0728500413690080a1a145480a10405003031903503242181d01d00b000c200845801906214103944801d00111048601c80c0030814903442c25280d00c0402a109401d42c4c1c1080c0b05100c030a44000b0920038669190960950b01e05840018400321b8031118071403202642054076000740c02e003141c1d48090b01c012180035030060748209100006007051001554844491440006e158840d000010141c40a00b080d909031903100503440000400d107042d030305030031081d00c1508000c1d280c68514016140d0051310741c0c9203440507189861031070075500f5030001c01c80501c800401c0c025510b44020060b4407030300300d51000e00c20304800c481050841080e41d41300720301f0250010000c90902c81244902c120a07440713410380904202030301 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 828246160 1250 828244910 828244919
    0x312070311071220130b040b15120c07020a030b060f04050a020a120525021509030d0e01020a0c23060a0501050f1f08041a0f01090c0201090228 63
    0x70300122014004040c1c1402d00140f182c2803074510000d03101c80c10125550840c16081a554460080c02109210700740c010810528080000703008114480c0304603007004040929002c2c4286400042002004e6001c0208007a180e8546464081c0036140000350000c10b943e50074004205141d0546600c040d00801d80c2500300c82c0e440c0810160352050340d0041d040358000c80c1c0d1501094204c0300141ca48011001c00300080e20f4032851100c0e50039000c40d0b02090b05203091141180300342c800c0c025070b044d20300024a40101410030a41d400e81d40c0d0f0080c1c4044007968984500028014810700880380054000c0d50780d5a0380e105241c60311040007200701001500da05130020480e4036031070240205441103030391a10000e0690f142c50107004031014000000c03441105065544046100c04611145050040d460802869516480c2000302c071110010001007903c545000c102c003503414181024140d8500c80740030b003d4442c0000e001ea081c1c95030f410300250720072011a10071003005414503104000e00c408031100076100d50384 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 828247410 1250 828246160 828246163
    0x30f0a080d021b01020703111b1507020406080d0915050705030d1a030a050c0312030105060a0f0e18040507050102060903040e0a0605060309030a140304020612090a0215120108010b0312070311 84
    0x8864200c001c48c2103040303841080703001404450140c2240c00038081c511100b00300014507100305030826045039039021407010203540b40c5600c4580601180000c4600510101c0c0e8043c150080c5032040da030034940e03014a8107050b00e00c1101600c0d5940d078080025820724107008002070140845001d10708081c84900c2650790b082c0d03010021a00c845000d14060016480307800245420550a07609c500ca184008100400c1103840321002c9520745c03103107841d2810640b0b640d00c0d07049a1082d0055078541e40400c0c26140010090b00381350900d401580b00707401300c58240b9a03400040e41c6a40d411620305646800600040001c4280c0c000e1180d07000700c0e0030308000381c0c3c5629140010740e00c0e001500e1102c207aa1021a1507034640341c01100082e01280d5541e521802d40c42d00f640014440c0c80391040e0170640d285d050300403c903101c2d030820580c58400c3e801007080309000c419426040164010560f454030300c00510b000001c1502c03040c440d220040c00c015015140e4114960948802d644c0f00c40800c5040008655103003014010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 828248660 1250 828247410 828247417
    0x120c02060d1d1209060d0f09231f1107060e0102030f010b1204030518101e0302031003022e0504031106030f010315061d06030f0a080d021b0102 63
    0x4030701c400040441070700740078035242429501c00c842d1070352000424220350802c40083c3d0320a89011198981c1d07a200203894980906010000350324041d0070031803048100300e0f00d8484a0304030059503401c01146400d080f026a6100c4d9130150038105d00746400903e4141c00280e03080741e40c051050003401440c0203055959002160021a07000f1030030b941c04800d010280801c3d0741030a0050100700301050414008164490700946d02074401014030000051904040c1d0300b54442c80c008040041015400c8c808440c1c01800140000c810902002c00340014664818020310a980c0a0804c4291460f082ca04590a01016844441e40380c2c0c2c10f5811144d05158030203161454891182040e03856070303100d6107145480b800b100d09240b082c600c50300d400d00400c419400c905814504480d04a07584012000500021200808050b00001c1c60b6151b04500341429103404590303940900802e40454241c2d0045100703007901d807400d03010002d145050400c100c41c005100c5401900450000396a4071445c00c40090364242260b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 828249910 1250 828248660 828248677
    0x12010e1b130f0e04050303070302130909060f0b041107020d050a052505061804050c0f13030c080106051f181e0608070c060906140f01151704120c0206 66
    0x1041c92005000503003441c00c1079001000c41c0040908541090741e80c150300c03400003c045400309540440d201a0000a00c0c145030000c004101c410440d0b0211401d002c0090440c60391641c5a960a206d441790b02801c00e0300c01ca0710201034031008181031603c5a42044120510329005982520a004661001c40d00c2404407444488401c031a20262422980c0e1100c0b1221440d03000a101d0030741417142c0704030050600c84115510700d040343e00103140d9a07207420b0940c5c0c0b40240403103e0810080424001c4004141d45a204144c9000310044d0300703140e0741c03548824282c42035405001c0d008080711071412400a112000c0058400050520000d19108118806140c0410b94070440052a00c100c1c0302d5035000080940c038014052602d090003180c549160003401d05007504800801c03060f910600c0f5800c1c4015540450703400d403003003401c4c4036180c00c1060007040301002c00c2c002d030040088207585803c0024010104981440306058051080c1d44d126101c0000100d070000301d00051042403000d900060395120010800c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 828251160 1250 828249910 828249937
    0xa090603090203070e100602061e01061107030c0f0501081006050702060d0e0a08040510030b010f0c0c0f06031b0c05060c183c090c0a09090c020c011412010e1b 70
    0x9507e06000203291850142c00c1e5075211861000b210b201202c07414103981076500c0b505100c4c24850344590303800d141c4035403948081e100d02342c15040424840340001c1808104c4509a03107400d490380391040c8288174281e4500c528000b1035000c0007020014200840905100454501c0020360420000102ca00b089c980d110b080390031a1001500703102c00c1c50f001c22400c4c48034945181c108100101200044c088076203840c2d25105003c11030254808004181e5015405498000780d2400080c0d07484801401501340032820002c07c418141d500342d40e49200310160300d649500800204519244c4d140c8008003075205621100218040c2464520341d621074030450042007000340c0e4001c40220107410312000840f0b04034002d400301c41814628480035230b00d1400080e000b0310541d8201c1d07034030342042030107176003149483d8040c0700340600b40b0f5085c140c043d4020a40c0b507601a401e883c4c000000380d000c2c0c4090b80e2445109468241e2803d001d00601081890761000d82d4002004003003030403500ba10700240001f5412681c010080c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 828252410 1250 828251160 828251191
    0x30c010c080c03090d05030a15091b021209060a0318050706030b100e10170f192f0409090b04022403040b060a050a0e09120a090603090203070e 63
    0x155404601542c1c4800308000359400c0d824142082030300e540e40b42400c0303010802d012004c12103c0d0015400304812030744800031802456030b18800c800280000381e000010755514002c0380d0710b0742400842c07010300c103c506044040c038254000041240941000d1807410406170348514810310355040741d0203290750310300620085c102c191400340001c06503100c0440003400f0301101404000199040400c20b000900101da12030880e01190f00c084a102c0c40031482c0f142c241c402501407201d007107803100c1014047d030112121100048498042d0758181c40e4070010031198207095181c01d141419000010300c0c2c8071058140ea081c5003c3c3c0c0c0c1c03031740344080c0d401c0140f06817510003480d81071000f145018001d202c5804081204071403400b21141c0ea40c009800020001381610b0702c0e4000140c815540c5d1014000903210040c40c00705481d0726691408409081101c1904c001e114070040404130704100c80036035a904091b5038503022110b0901c40e080f0060401c91108a030180b01d01c0e10040351114481650502c03565441d0303940b07040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 828253660 1250 828252410 828252431
    0xc0405210d050406020d031109040212010306050c04031a07020111030115120b0306040212011b0804030f02010603080910020102160501140c030c0301050906030307141b0102070807031b08030c01 85
    0x81c07200d6401c405082c09000c01041102a8001c00d01704030150071428001010150690300d1003651041000b081d500038030004a1285041c4100e0384141681d0003484104519666a981050180b00358040a46111580c905007000800c51160495112030944000b04107519481411001900300b81c104250740e0b203001c0b4118400a501002c05078120a0b0010244510128800880d4031008054000390080b00205007080d100402500a840c0320540110007a04230065480000d1051509a034118000b610322a00c0c014405e00c140902c0081d26085440582b4000000f0108800c5540d0121403405554080c00b82c41c00c107202c20300f01d12600c00c0c014400423507260414105003580660003010f080c0740364820b01c10310400201c0542560706481060b580c1415580300e0200091560196400050403400306c0041d4040c03041c400b050240b40c0030000040e030414541d520005980703c0905001f1004940e00c0b107403040011410803c05014076949403c0009003250f250000e0368256480f401c03d030007a681d181d800c943d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 828254910 1250 828253660 828253663
    0xb0105031015050f0a1205010b0405010b1305061606090503071b0b04061407051603060b120303130609020310141518040312020d14060d0305030f0c040521 68
    0x888181e070103a0800c03100c0305a04031032421080300d024040c0503100181100c0b02d6500c4440c100c20280600d155458103804141c90a540602607540f41c0900950070540000b13401d1078841d0030340d04010100014031306018100001d1041a400c2050090b2500080340c1401000c12040e12800d034483e80a42d018503a076a500c0d0505141004064026983c2004503010400041c0140701c1541e0642da61482c18a120166400c03401d4005d02804c1d00180c07190150f40c100d20300006183c103010007100d100d51024080b074a034000401c8401051310100710000d8000f04009403c0b03400720550140700c036105031000030307801d440d0750003081c40c20441c414546500d035540c518000080c103561a516901074140036118141085400110f01030700c100c0c03044003603a010400007043c1051b00440c0c00718a11000200115111074100120704064501211084907440012003c56041e0a041c0300340c951154054503114515215030122072280c4000400c0b005c0008002d12001c41c0d16a1b4008801c03000c180750030800141c04600c16282c5 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 828256160 1250 828254910 828254923
    0x414010906020d080c1306030c1706060901180e04030503091902010509090a1b050405120d080f0406090204090b01051e0120070302031501060f09080318120a0b010503 73
    0x24140000d8540820103568001900e00c1085110b18002034540c456402d49200340c0103c048408000540070b001054107907243d4000c4203011a50354500c4020948066030b00c60340e040039a011038000764100514505540074580b079208094003442d44145040daa650322140e900703003c0d282100041c10000030300240032810030460401e012a801e500c080d03c0070a9002074620302c1007170000390252030030380300207a050000d590000c018184171107800c804407117400ea8010444c0d8007034080c084c412544c4003100c1c100c0102c00190b9400c004d400b61034107215500d84030007614401500070411610191a01007020040e00c540c000c00e0035042c0f01e03000200007541041d040203040c50ba08091707804407044140200358142e0b88090403407181c3d00004160340d07444682180440c03c00b40a030704069014841c4107680224500323070925440c103c4249c0e5803000f9603509001400c642c5229140700c1c1402c0d03a4014040390205813048030041c0b0380c20070000c2402d07400c0b900d80329140d0f0800305054000d50308200a0001005941810b0240 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 828257410 1250 828256160 828256199
    0x305030f150d12110a050c030114010e0a020f13061d0d02010e2709070f060c03141303290c07020a0306111210090f0603050c01211104 59
    0x1a15107018059010564681e2020005072802c0001e000d0380c00e20b0b6000d43e10144034000344809482c40101581413159550306c000800900942c41c01403805614140c241907035058914030b0781450742d9900d6402850000e900400c00421040e4410441d203000c9919120b2510020502500e840c0c4100300402e0402c560304591500c1140075201c0803082e000141c0e03000c0c0e000c401d02201160404011030400c01c07508d2581c0d0400d1401103c0800d51420f0010b00000014035100729107040070648038890712514200c80b40b40d034140c330040219981d50078501e078210002001d0b240e0340b101007050000843c3e4035120316285611418181c2c00008010140780044d503035262400b80c2c00518234030640e140c03d521741c0c08580402042d2001802a41d9141c40510700035154908442140400580e900c1107400c011001c0421401140b1414040f181380005100e015003450044000b100d4020002c0c0c0001500c45006640d000e00404c0c1c8100c0e43c081c030340584800c007459445000c0c0107485d00c0004e2034a80d400c20007880501103043e0745 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 828258660 1250 828257410 828257431
    0x506040b180601030510050d0f0228030305250f060501080c1e121c0f0e06030f0712060906051806030303061c08042403060f170c0303070305030f 64
    0x10a07010392803a07240c1150490402e1800098076545c01c1d142044203c0f45411130b5502c032914141e058203004480509900282c02101c00960a0702000004a000c244080c5080c200c4110b0003000c0001c82d001d40e01074001c0400c1d032203010342100c2c0000002868060701d40002c0758141a240500d105010081c8101800740403600002c0014155141c000740d040101000203400e18480300010103270035141c04c40d00f03401d00c13074440084a036070010f80240c00340503c4940d025503002400042045038068440c1d0b45100207144040c159a245480b2480b8402c003030075004100106002d1413080800744495944101001820760040014603d4103202c00c00400b01c44d00304e03079881d0150304001406180c0c2e6012049a030040707022102c00352000d50949070107480041d8645c0251215401160018001c60702c981403003011305000e20950301512501c24103404407001c5001c0d0b092180036180c3c0501924a08201e0549440d65000c202c5250740c94a0000a00c0e5034400c1c2000ca0010300d0200c14071101154161003607800584100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 828259910 1250 828258660 828258679
    0x3201c051005040207060e10020c06070806090c0a17070906091703040e09190602030117030a020703030e131a010207051c080a2001090506060a060c121e030506040b 72
    0x158112998081c0d4014603200c0ea50000d06481004147c1d03010030024103404003515034007008a100d50000703402c071307035006085409140000b81501c0c0c400c00855128040040c0f80e41401e813071b200b02100700790308800044070600041136140107420a0703691096108000030359426000b1810300d00006c0080c80961301c102d000c1e0900740389007440c5840104c182c2d07017525003c0030091907640d10203004915206442d880f0109030141b005444082c0f001e10380046058560840b00240a07407284403400ea903030311401d150b03500141c20006007403000034466078541041220051554584071903100701c840c1101d58017034030600c039500414a144d000d960107001c800d00500d8212440034004415200e0f0713444001c2d50b072800034600000040da01410a0180c4001103a44103003020748131948010401090082c910501c1c26200c510542c00000c100f0324090186801341d41082d03803440c146000d107945144050109114400170311100c09000c61171006c0a010707030000703030701d240d03030081001c2c14201e090004a80c0b820004030b01030755512 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 828261160 1250 828259910 828259921
    0x9070f030b010b071a160201050708040b0a1a1201020403020f01080c04150320070b18030f09040e0303090615040501030305180406050a0b0409060b04030c031203201c05 74
    0x740a0504444880c2586030751801e2900c0c083d940008102c007000c54104200050020f0f101070003100c611894000d800802207910ba01c2c60035694002c0031140106002c01010001d4031002c425003004881000d004400f01c038800030500058080340c40001003158070380d400302d420070035450000f2111803020703028207041c00d580c10b2004020341a403042d4001e06200d01c1e00c0c0181181007030703c41e620034509810b044240100c0c100021889111036445007130241c440404a4000c07408142d60f40401c6a60841d040703000750b28040e0100380c0c04c80c0581000d208254003507514010303203006500a200030351003400418013818030303403400d94400d04035101c003104054001e6140400610000340c000040b503480203100d13038400515480b86000980a401a03810003a005007500c00c000410311030380390191040c1c41400b0001e2103441c3d01c81040c01814080d920002e01110300301c5a0400100d0160404440d10807124600486c40d83e40f140000600c1d1500d499100304a60400900f1405984210f03403c645044810700d801d100324140b0303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 828262410 1250 828261160 828261173
    0xb09220902061605060a0203012103180f0801050619050f13090b1909080405010806030c040f0e0f030909071b050303070518011d01122004031b0b0a0815130509070f03 73
    0x1018ad0b840040042807500c0c410b05008039014101d01070400c418140142c0c450b0024074241354103105400351503007041d01107580c070303e000030174230351031402500056000750710b05402c00904250320b00c0c0745034110301c01c104800340f000c0060140d007400d01e0080811401c0b07810519010081107841c04800521a0718240c003c90000d052003040320704545003403810802a07121100028240b540100b29940d0161402c2000c0302200140d41240789244403980650b40c4840540701415200e2090071281603103d4003400c0041c81c8940544183c142a00c400301e40006400350581d41c5501d10b030700a45200300030580220f404007003660300ca00e40643c1078000707180c4075141c0c0d83e2541d0b14041c10499489070605000340c0c00104640605d09a100302002c7d80700b0900420704c40552208807006034080d01060f20803503002c2c490542d14642089041c4200c9941042c1c4603d0012800d8088460140182115a00017142c00c0001816921819060180c000b01e440c002414200340d12000d207040d469604c01c14041d1400e040c1000407645 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 828263660 1250 828262410 828262439
    0x150806180d0f0e0f0111031c0513080708030a02040f0605040806100513050403030e07030f0b070201110406180308030103030509010915020d05090f030a0f06060b09220902061605060a020301 83
    0x81e2139131900071100c4d00043e2600341c44007850f034446100209603805000d07074281001080900d096000c0091342ca48845c074003c804060a805424154100100c200046805d4002e40d0f0103101020700500f0541c95402060f840700342070b40070400044002c40c040c058000c0500c107880d04001031405200c007070780c6007401246040c0c10640a641c000c0b03503134800007010706003e03030480ca15041c102803c0e00c000503201d2900000018511600703503500c0b03440078002800d040c0148201e141c14200202d12038101807500c0d00c100d032000c40b8085142c1c140400568000000351b1140c0c0a1030107140b01c0e4a41795120b626030000141a044290703c0140e0030382800c01840401a00452850f0842e10945802941c420041d804074100031501d0010303903010b2090714200e00034058544180c0d04080c1c842c4c4818401683c3d9010030710308a00580c400390394130000c0406403000208650317050001d0448003c002041c0420030703030000340240d04030b4007070030200c1c3c16024903007810000180710071a44a194060b0440c02e650400c0c100424011 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 828264910 1250 828263660 828263687
    0x1031a060901030902060c0d08010b03040f02191206020c0c0d02061c02120901090311010e15041406071d2d060d060b07020111150604150806180d0f 65
    0x300018441d9181c0c0d1098000c40b030f50313079000f4007000c1d0384804000100e0345c4c926921141c90000380e08003001041c07921008084a010b540c00200c155102c1d8400d80801814400540406800352507241c0000392404603034800d90b0034540034000050310360442c0c443d51400d184810715807a110714003910381d40005a90700c5064501042c0704445501504080e0000540244034003000d80342c42001c4101040140c1c04150802c0f0320b6648241d4810001e40280c0c4212800c2e140254044615600006200d24002c0f061080c040d600c140142c003401c0c40504010240c50800e007050b035054000071040ca41c0858107000d40030300c0150b500c8080d00e40031102c0140c0301004d04c05010400c0f00c01c500d0799102d8840a402d41e184030550301c905035418020050302d65030b02c241a850b0741c404407080340414085034511070390181c04104400d1610144040107015a1108108402040d40c0c4201d00502140c02c4d4003c0b03554034041200e2403203250082a2040c4608035900e00d5887d1084004942e010040d500760f00f22480c030f07400700c5040b045a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 828266160 1250 828264910 828264919
    0xe011e050a031805031e04030b13021f08070f0203130e130b1513020705030307083c15010c030f0c080315130608120c2409070501031a 59
    0xc0d20034140840107007014030600c2003e0510200b2410600801200030038100c2c500014451980b80d9070512420b01d40a1407101400100c24800081e44d09482d029103000788c948024407082040038402d001b0801a03040000100000b4007003070030030038800c0c0c01802c14444001240029800d000001002e948054482c0c094071810701441e01c04503004a241c3d0001028860f409052244c0a18203440d40451902e9480d6800340301c1c1c210840d131400c3d01e181a10844004a400002840c038668a000040da0200d50140c04464021040001c1400c50b040211020400584c000d500e10140c0003c2c00307490840c0e450184c00d492041c3c8030800400c1d5103a0700b01522199050b403505048007103d0f44000b056400314445039014040b18000000c0090005034100c240c280c50000302c0742c4c0300c090b01c20201501c04aa15a0150f000554441070b00c0304038501e090000f030240c000d101002c698443d0ae802c91071940c22400300d03107090101d80160040c8444003a0502040d0701030802880c0c2088034212001111610390300c40d89e03a95009 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 828267410 1250 828266160 828266167
    0x102031003021504050a150206011d0106031a091503010f0213060c051006090204081c0503131b0608090f0a02010806040507030e060709150206010f0e0612010f0c0e011e05 75
    0x10f42d0030720342514000c3c070000b8144c0c1c4010b6524120b400c1c0140c00404584014052480042044040011440003c0081022030102a800c209041c0d0080c171049803210004c0386171009100f0a555110092031050260019586800e01c405060600b926214a506060640140711201c0c0e080400030407030084600301e04d01050f1130791340c6040c51401c03d40b04100f0a44203a007003400110700720b440d0390024000c4903e03070390072070703240d0f56078030100704484000800381d10006001040450000e5044500704d4421500810508413081c4580805041d02d185560004012485501c00c0000c0c4d20020712208010211802c007502c1032040990000306036441c01080c4904c26655500854915480790f070024419a0300101100c1950500020141214041d4460000d0341141c0b4054000c1030381c8007155403412102c461044030380c03182c00c0c2059510000001405d058000c0002072407850548400d000e07a012600f400c1c0310005020011407001001511080c0e00107041c0481c1302c48075411f110740030307400b45000005071501030344 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 828268660 1250 828267410 828267439
    0x705180c0f0d06080a150c0f050901180807051504080303041b08190605010b04080703200603040602030118020408030901181d0906130f0b06181512010203100302 71
    0x800740103150b003001e0074510303200300410701000003e600c1c030085008082c000e0707440c12949010404e940a1295000c00561a2540307911040d008001030003803054141811011210184466400e080107070f4450026603012400420040c140391020382411946c04103214506401c00c0034483e1b0742d210103800141100c0c1e0381810540300d00f0780700355141d0250200c48207036000044250002c0d800c10788951000d80d255890000009a1211014112012900c81802412070306107141c555049540b80700c080c108884610404400466072848003d521441c415100141c807941003410708440300c07103004880c10402d4030403c0107001c990400429207188003001d281807110303003012540407200c0500903400385001c07001c2c031006c0501d850400c21040b4031590505040380c415a4407004401c045049400002d0044070083c028030010941101920380c2c00304015004641442004000540140040300c00c0f48904268448014807890400901402009440c000f0340c00d60034600c0b030418182045210007071013106402c0320a031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 828269910 1250 828268660 828268687
    0x109031d2b060617030901020c01021c0e060d0c021e01020a1704230109020f0405010f1a0903060a02041401030b0f040e0c100f021606020d030209040216060e0705180c 73
    0x3e018154800b240341c81080c540b980c3c150340350440d401c4603001d40074101c0919815440001c5000c451880c80001c01e10242e580c41003555010100310319290009010400b0501109146c0910342c16070390b45a00910040d4102c40c023a404100c500c0c0c001c88074690041100a0100b82e1020b017000c48803051044404035911645440408007904030020b003540d040715102900da074034040d0301c140398490094031076007440342e9080200b2085032030034050f400014689030f600344400d681103081c00d5844080401240d1511580a0000780b60100c1110740304079007030700007506200301c000c8200c859212100a00701484013820381c100140c05844007030004c0d80900c6ea90344101148000411001e0119880a00804040300301003000400d8081d41c0e096200c0981b0500807048200d81129a1a100710740b0a030780a44842407244208602035408611466403003902403114565419000742c202c121075218480000b010b5030510441420300321390368030507071196890a180188400c02c0844490f80200001500b0307580d100070307510a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 828271160 1250 828269910 828269921
    0x16080106021c0309050a1209080a020306070c020102030409050c071403090901090c0e04020d0e0d080411060a03060b1603020f0c031506010c0b090703020a09020c0c12030c0109031d2b06 81
    0x20702144900ca801d1814021820003003401f1070030036661b03048110f441c0c11000750b4480012200940560041c0d0028030500d11a90705860312910500c1a17030b28096071703000c0803070a0b10310541303040042110000d0346408002e2080e44049503110f0400240d82801748031000101c0118052144032281900d0395407030030b42c1038818901241c0000f4001c0c01107407500f684143c0c501c014401c482c070300240c500c295200100c030070b8041d03203400d8491a40200ea14225240100c00c2c0100f9820080452041c99102c0402080503c850f201500301842d100b0b241441c424190b08000b441c10f141c1c20720000700d903044000c00e581d4545001ca20104507144184100d0801d0303d5400040300c03442005174003d4040b564002c01d0044420300424240300320790084960740856a220410740040307108501e40030440c0e0380845401c00c580e0600309245048020070388103480c1040481e6441c0350030348840e00b1040303000540c1d041e40c403409580301d84c070350800e5004140d6a10044000c1301c04c0c00a55401c0901c00381003003160001201003005400d8000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 828272410 1250 828271160 828271163
    0x306221103030c010c08011401080103021507020f09070210060e0106020705011808010e030a110309010926061603050f04020a18060305030f092110020f0c03070b16080106021c0309 79
    0x200305e60703022108000c000040a019850074036070710b1401d2080c40c2d0301c0b50a4480c1070b20707002000741550032025803624a290703000ca10100e81240b116000b9106503941c858511b4410010347d00a42039044d03804040800301c1d14607402c0951a209400c0c014800d603580043c404098a1007800d194142540d9243da03c09856002d80c8110303020b600b81014801900800b00c06810701a016458200c100008900705540700c0c0186801c450020780e48100c1044242243da58802e5000304981e1000c018403060203d55050035800c58011a05211010490100326418030032194002c07a1840403202508150f40051314640c0503201d249940042001034180f0300b40f20341e01480003903074440110795075241c02c0710800c00d4a40210034150310504a00c10421030300d0341c4600d20352411001c0f0502074110790314401e4000c002500a60f403e81c480c100d051001450b640c004000414000b8003c04111040b454424140748003280c01040f4102081182c41c010005103400280140303405420000e044e10b07060441c04c0450091900950 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 828273660 1250 828272410 828272413
    0x91a0103030507050d02010203130f0206130e18071202240a2c10180302040f09020a2c040f02130c0201050c130b09061306020c0306221103030c 63
    0x400d600b21000344003440c0b141041e035138031000a07101030b800c0b40000c81e101500300500410860028170081c0ca00d645182c801800f050034810601103100c8a040160402100c2c0b02d080d4041c4000850048810f600009204004011070340c1071809001086100380c40083c000d0319184540941e5100c555251000090308000d6951102405500282080008007818030703a100307001d01d8400a14010300d00c41d01c5a11025042401081c000d000840d9108020036040110200ca0840440107a0703443c06404280750310301e007000c946120030b401000760140e00d5070b001484142e03100c0034012031000d0300b00c00c032504c080203101c221b0f006503114185015450400400250302c10500c08041d40300100990010462056a60082040740c0e02d1009442d0703588100c001201407091070600c10041b91400c034009017042d01d0f01074149401d2900c00d910341f00c2401c01e1504107101580000001c40e0142c101001400e40c4202183d0001e02e9200030360700070101c24a04054003401c1030441d00141050b81d1000c00c119124500c4410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 828274910 1250 828273660 828273713
    0x6022a06030f150f0303031807091a120a0c0308070819050a02061b120a02070503130303020111040b1209010902090915100b0f0307020109020306040609020108090604050d0309 77
    0x1c02c00a2210021501d0715011600c0f9401089142081800b456100c030001d0025440d50312000c031000e030300d50401e2400701903030301c50f01c40c0c0030450886901a030040908c40e503400e07644050441c2d00300940d0b540048028140343c2d0100c0c2480001c250301d1901e41049035040041160303102700b107041180c024440c01a20307900b500e09400c80342c148103601c000103259900a6509950583d11101000318072a4200b03040566426424441c04092070380010a140e0041d084400061402c4d030907035610350442d0410f03080c0103424000d5010030030a060f0280117442c0c8031540c80841d6440c0c142480c0602d10b00d40603800105035404e00f0080041d03c042400d52094460940042c2500c0280c81d0a04140e582e40003805c420307000b40c416404c01f03d000d0880326054641502c00d26603c0070308102400410080f5034000400c142c04640d00e40c0b45080158800f032000c5400755001e0000443d44d01c0103400090400e0401810000c00350303200900300404580d000c101c076030481c5824500410f003514181040c44140310f0641c6010814901103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 828276160 1250 828274910 828274921
    0x9010608040b0610200a050d02061f060203070303020c011811031506130903120606181d060f040603020604090b09060d031b06140708090c060406022a0603 68
    0x21200d01c180d200d1122000c09645a4040c488210000a20b8601007154840c071011401802110303c014400041c048902000058445901c0e105550103150f0258120b0000d0250305080c440e0024100c0d202c01060000305498001c00030364901c1190006010140e011503140c8620303000390800940170000c0c541c1010184003c0c00d092030310f2840710103203522078460001c0c074181402c400c0c040300c0d01c2400b00600c003030b00d40c3c24425008070103048a56400c4041015806091410134460300c00c0d007000c3e201c15669420388a80382c0203414000d5100703400802c418a1481c006640d8111140f0225601050640745c04001c0c81c0b036034001c50054800b2b070304002c0d4811390200e80401d980c540c039882014440c00c1111a407455881341800d1041d5002800400360014141000466149656404e001c50052103407000041c900c019400380900020140d0300f0303e000650f500203000c0c0c550000c02c038680b011001111220302e820318241029540f10320410b07004203110030445000074103001445080c403200c400a00115507a2404 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 828277410 1250 828276160 828276167
    0x14030a0e01030605040b0a0e09070810050703050f01080a12140406050322120305041518020109230f030a02031203100b3603010606360303140702090106 67
    0x440240c030780024030380301002400f8a001c1c001c1c030b0a80320000c2c004100d0b030f0b4104120b003101180000c0c00d0140038814102d0002c3e04a004105081c4428514240042c42d030030550001019a400070f00454000e04500c001408110301c040341840781c0d25804084a0f42144211134261005849501c46d22201c0c84040780010f0b405030040000c41c45401d004800680b40382c501e2180044203415103001900070702c070020441c0d2089004c1d0b0f0006402a001d04540d400c0b00e29000070103800e0340c0905510b0684001004502021540c020314031a0150504aa40481400d41d038420400b1b0454040080d03407082a4101a00986440900c18101c2d00368025044d1080c0f240301c00700c0312400381c1c02600c01081481c802c4c0d90001da560000d000341c5501091594544ea0308500b007040b803030300d00c210301c1c03520051030301c03e505484502c1e913002d1241000810458031402600c81c01c1c0c14626041106041d40200c2d101880028418201180e1003140252903150400c201d0310069a1000000b5015030301c0c0007500442010300101e40180c1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 828278660 1250 828277410 828277427
    0x10090806240603090c0d0309210201020f0a020303090127030c0609060201020705070605071104050a0f0e0c09130c0b0c0304031104090203061b070c0b090f030706050d0914030a 77
    0x41e1254148480003440600005110072a050406600b0110014005107049a40e81c07520358003a01d4913940c501d40315005460340c01403004103000c0341c50200b11094110750701809402d1074041c51030b01500c00580b1036008aa12441031101c0390381080310700c81a008414805501020040c08254045040d071030726031030120b4600865020304400700c0c0b490f035400901c1038814021141445e611201900b20545010029110f68000240c1207500c0d6170b07001101c182035156071103118803c0ca8680800306078401305486071380031910701840c810841e070082024600707942c580340600c50300702c00411300007101034000d8281980214050b4000b010304840024091840b0000000500243c074000c000b08a030003101002000120b6042c05ca00a401d50800000a540078030380410706c408084000e03008901c0e00f24980c0d9004106030081d081042e042e1008684900b044c10039910f000e109134420f40081c4501c030305228010f400c82c0684800c0d8102c8030f80b1440418100702400042c40b9103003201108607a00c2d08000c2101400000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 828279910 1250 828278660 828278701
    0x50d090609061413060f06090c3938010608180c04110c0d12150617060d061a0909010213210b01120c0f0b0910090806 52
    0x103041c9400d01c40e40b40c200b110b001c1c1c026064070f444007545011380e0361224080c1800010080c940c1c3d42d0b0742c03000a041e50703c5000e00e2581c0b07425a40e071a0014100360100100180361000003901c4010400e80007030540159001c00b5010540121419010b920f0302c01144295002c1c40601192114900340c0c0074000c04001e00700c040c182e540075203d40b6029034903002002403031240c512086801e503001810202550909910000d05111584030003032811116240c40717843c1030004084000002e00200396a42103503083c1c414522000c521a0400290078038102c4000c081038191040000703d0a2001d003c106290784030f0030303504480b50b484002440420300c00c6810882412642e1592405002801c2c00104480d0701813080b1080d401c1b0b41c2c0c403003012007420302400d0324005400e02c0e201802c03003e44500c6c0da404100c00e814150700a200c5130310b42d1190b10b480707454100030745412588509895401c902c002c1c041c0c040380307400307071418010203844100c1e00981d00310040b141c081d050f80c0012030318001d010034400000b0080e42c101c0c0108 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 828281160 1250 828279910 828279923
    0xd230d090c0b28140414031e100e0d210207021509100f020706050901110303010e060a060503040314090d0210021b03120d11040801151d07080412050d090609 69
    0xb203500032000e86105039092413550700c00e07400700000c2c0542e103210f05c1d94440d2410081c0072112410b07124034a050150100c0c400c0f10307459500007022000051414040c5c0c00c0540b0603480540901081e004000c0c2854021480000d805d94024060303502801142c0e044e140c4554008000c2c411210b42c19100802680c001d02585004500e0241200d015900031010324180c400150300a20845140030005c0350a80c02200300c90b03040041c4940707040c030017800400c080c40c041d0111405840303850030a034040000080055016200f8441c0900c1000b012135000603046c0c5080321408006551204d9440002d0060b00c0d010394000c0d07100140311141a8565400102d450040c040800040a601c00110405549441d005130b00f03c0d2008003001044005510741e0401c0d2443d42d500704a4a060603118030087e170942d040c1004004140e45580f608001088101e24040207842042c403008003207040034103004106c030710300502c080c100342d038550a05a4001d2042044801c035011aa41c00c01c0103050300d1400030003030030100b5004e0b14078 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 828282410 1250 828281160 828281227
    0x307142b05100e0712051005010e310207060903080406050105041a040f06050a080606011701051c0512280305090a1415090d230d090c0b 60
    0x8940c158800da60140001201440e00c0e1032800c02007100b200e00041004003041a00d040910b000f0380d181c016103000c1d0b0750309098003240c0b5043c607000409094403903d00600c91903c00b2031082450541500c84410007070700c04d000080002d24160030401911901c00c0c003c0c41030303251030b094100b4980d104074540e010b40e00c01d007000d000a903030f5642000140c1d0024481001200b50002140400b03141c140d1244907260300d12040819070640d107400061680d060b80d440107415411a0080103d01d41c0c2c0440504569140c04a18001175414140421884440c80001040702060041e410080c48400c001030854080482000c0760764190f5280041031100c41c001c40c0e0740701080f00c41d80300c0b8101c034000e02406124030540340003000d0404031030b281d0a200950000e4034100c0da015200380c0c103081d06c1808411912450000e40180602804041e0080c4100e241c4102718052031100b00c200d061014442080302c4003400304c0140030400c99654103099130f040b05c4d19802035044080c002400710a42c0340007020902da81c8a45c0c40710546 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 828283660 1250 828282410 828282487
    0x3050315040e0d0309020d06051003060c0801030b0f0a15171b090c210c03090d0c050316110301051e010b09010c06230a05160e060f030714 61
    0x2d4540d801c100c504941c0100340048101031103948100700003030000749042040081c54480c1c0044400940d10b84010034003c40b014420701a05003d15010000980f4020260b0341c510346803e0034140d0050407507110000301c44082000e04410b81c0000c040c2d0040302441034481070743e88002c072024002c48032801c2c5550103503e51504542e03a041d01d00301200e1001404240c507540e6254488401903010600c02810f501001c8012150b42810300000381c41078013543c05003566400c244500a1034207281080d0312040125896680c4005600031040d00d0340c0d540d940340f40b501c0340c200c0b030305c2e085149040e50707164150550b20380000c04c060240c00e00c040b002400c05204541480b80d89581c2c004503184503041c1000c0c08101940e80900001b07401ea40420b0840058643d04ea0240b4104843c450112906880314118140c0790740034404100c1c60a1050f100c099010f00782110f45000c41000b040c114040c039900e2824032000800003807ca50f01952001c5409a004e0131901e50701c1c038030b00300701d03000450320b00344480d403443d207090b81001 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 828284910 1250 828283660 828283669
    0x22508192a060e01090e0a0203070519030b040f023f0906040b0702031602130b2218030e040209040b0d0b090c0d030c020409082104060b04050601050a032703050315 72
    0x81540c44207400c00100b981c5420380c7c0400703580054040e500b0020b00b040200c4080c0ea014500340075031400e550300403c0d00e561400401003960a00e8540352a414070402c0102c2452403001c04c504194000201144090016044c402840180744944015032403a104200a202c0402051441c8518419103090300551030f501000c9940c0d001c0c3d410301051003a00a100701d07015141070310a101c80d40c4094800030a855003000041880c410400701030540c001f010003241000c40b4114001c0b45824400460114550489034400a0a5201903407100e409182c1c00035000c407aa40310340e04400105440680069184c060304c0c80d21032076490741240e50601340d009038a401e806d01d1522a004409443e0036030340d090030503c440d40801c4000c00d10b25004a9640c40100400e40c0640301742c88199006c084014080c08040c80c11341040419200c0340d030740a603c13481ca014100b0907203070303000000d882c80070030342e4580000c008035000200400503000c0300c00100c440350a031254000300b50f800001107100306c014421084081244a0070710 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 828286160 1250 828284910 828284927
    0xf060f14040c0203091c06150e04051b010e0f040b030106030807050c041407110114010f0807090506011b030e030a0602030402010e0307050306181c022508192a060e01 73
    0x210344c490388113003807001b01c0c00c00310300615101030241c000015040c015075003142d1034007415072116101800083c200028030905100b01024001c8280306450403980d0080000d14400120000c94851030914026000d15200c940c00048461800780080108603280e0901081d560400c0070211024443c15081c00064101806945801d800e0701460341c50300d4031515003d0303035010a4000140f290b0b6585034515103250254410140c001c04121507040c0c4400d040c1019281080000d03000101440c0c1000240041b83e40c3c4441d507004814052403a810b400c3d81c2600d401c03036804140380805079062040421f40c9003404510350086001d14801d03212109800c00386014591100c005104490f410b4000740f00140340740d8003908100f880840340c071007980c400d030b0454039480d00122042c0c1c060000691084804410340295600c681c03000a003940c0c413805a80703107400301c443c1d500c21003000d120301d44035205824001004551450b1000d40280c03071103126000d074403040c28050440c440d881044006100282c0d07045003540a041303003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 828287410 1250 828286160 828286177
    0xf091920370c110409020a03150f050f06010509060d0c0e040e060403020a1103070f0306020c010b032a040204120b19090b04120c05060f01080717100f060f14040c0203 73
    0x150300c0e00b807855849140c0c6121803000810780103612804c004c40141d0b131f03804103003015603c20000030f40c442480c880404104c800204602c2d4040b13262030180034940c605805159445071091034840e9580d45042c1c04502da9000d80929401c95a0030510781d1041190070400003000c00c003041d6020010b0703180c4101c40a9079100c081d070700a80541c03c240300107404140003490030031000c50090226850680d5500c140462040960300555141d0390214007e11010303400e001d60011140100c00030b02c481c04002c80c10a162500303070198401c0310144840d1181a03529180c054800a180d803000c885601e040764101010310703e10481d456007245a003140c2240342480144541c0d582c0d16007020212a6903500c50b5a0741c071594865804030300c24400d13065290030005408103c41803181801290300070b140c0d45000c4080c0d142c06400c0d0441c4a2500a842c030302440070200150090a90310801e001080403030f000120035008121640180c01c03140c6150f07802051031003804051040641055134104010b6984620890b1280240b100 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 828288660 1250 828287410 828287417
    0x1b0c030f1e0809071205030c0d0305060310020307090b040314060903030c040b0c1203090d08070e011202090415090c170c070305071e0f020f09192037 66
    0x4200515108580c031981c00f075040c004482c1e0803515020b0356860500e040000b1100ca03440007501c070380081e20a000f0b81c507492044d4141800203091100000b0740300c030007184540c0152a400300c00100440d00c2807819100070b101034031070300390740e29264144a0300c21019401803d11a114810104051000000c201c03440f0391040c829842c01c0038140300e1003290a5001000d0b10882d48030f010341500303a2000050040d4000c81c2800e00a042000d40d07400098402c8c14010002802c0c40340ca00d0151151b070b6000390300803103c659100401a5a0b2017004c0018009004c882a00e0244035019a008900800b8a610040d900501a00c0d403241d240e61030f110b500200042141c00c803240e00c0301480040300290181e4080d10015100310000480203001ca005130171841000041505c00c2c444aa000809508007031801c07051081094401c011186070040700c000d0206180c9910024040d5115010400340120810300d0441c1240a00815620342d81030060740040c030304071141c498543d5400c0011004030114218100400d01c416203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 828289910 1250 828288660 828288707
    0x41805160605031f15110607020304050303070308094602030a020420030901050103152313020910080c06070f02061b06130605100303020a020f041b0c030f 68
    0x7100207046029070134820402c2c40c40104c0100e0070441062006060480c2c654880144448900c01c030740c40c00318082c21240664008110612061310007004442c1842c0d0103003058043d64030b6042c8128079000321141c2c0090300c1d1180b810940a0103101001d5810901240240300c03051000f00b00340020301080944d0000d41c1580082c1d401070042c10181c0000719840068004050007000791030400506501c219100301050350f4410040c42049054000c0d046401004401040140f86264031258445400d450080b054114200000d07151089808005441d0703902400c504083d0506085010b0110150f014070000b900070152040c81a040040c140c0d49004d4100c1c40d01d00300c170079564091080b0703a8041d1541d024609168440c002c800c4404000301806841030943c1001e5840413803c004007158405402004012000d1a0070000300342d000400c0c980403501120241c0c04602c030000001c0c01010180300303012a90080440d110b000541003480c035980d003806034455101100d41124211495194010052000d03086907 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 828291160 1250 828289910 828289921
    0x20c12060a0c14031305120405130506121f05011d0420040c020d02100e0d0509041d0a0b0903190806121006061d0f0d1104180516060503 60
    0x103801a040d4444182000440f5900c840340ca080e041e4800c0350484601c0a910a0030010010108441410b1150305842e8908042c00c2c04006000500520108050f503500c4902223095603480c40707092620019004229000008461080050f110f450b40d9040005480d28000003105110103c2004400e05228100d179071550b40c03961010b580d42080040e1300082a0425010840d03070303c4902c1007161181c6036800410003018041002450003d1241c0c1c0c2e5400305003010f100090f01140041c4440803020f075414120b40b82c981d40d8010800400341d94041c0d0700780b50f0020205440b51036010454254a0340121030000c401c0d5590501d46959225225000414480001541c10707028404d514454109000501c5203002201c891031803441c10901c108001802c664459003009141c0d0403d1281041c8044134a5040c4440c080200003224030464040c001c3c02120300c407010000300300141743e2003000007034014400c0114101c00c00b5018a009046001241e1910400d00346000585001002c0b03070807101e0036a103051555465 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 828292410 1250 828291160 828291181
    0x120c05030f0c120f0d030e0d030c0f1b0209040f0302060106020f0a02040504080d09050705010905180408090a1205060613050405071401030f020f0c1204181e140601020c1206 76
    0x500d151019240070f0a0068041000180328504070181766550200c0e410030103043c2907003861030720b1b203000b0240b502d08002d105049800c1000030000b010b05007040c124103100020f1504550540010095105040320f08110411018030381032011a07000b94200c64881e0b0b01c03030300140c0e650301049448003583d91041004030014901074100b103501c1841404614184107038541e40409071100345408440a0304032a000388295680910104c000303007001c0340c60041384148254840800a4040c0010340101b01c00a51550240c90741500c0b10000c2451b095480704160302420100d0700e03501c09454452080d0215015007841105500074603004a421201400c40d88e460001c00c050307140c620f04442410f051700c80c91003049540d4070348094000c902d050007403e551200c3d60180103050a240c19981c0d020b508040c001030190509941c003100424041a40001d4625004850a00041c501e40400c0c207081e0704224254030303000c50b06920207018400c00c0c0c08480d001d071480010005000101c4c2c46900c0c16502490024141152 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 828293660 1250 828292410 828292429
    0x30f0c1a160602040b0310090b010c081213050d050d050a020f03060907030b0307061805062d12091b03010e0d0c150603030c05060709150c15020301120c05030f0c 71
    0x1142d02c0051810355510101c0200da08100c034204109202e98804000701060340c000c0c094001d10910705118021000da403000100d0003071107081105400080d0010301c402441c291010050b80d0800100d40b50700448180060140d4400f0f00d40c44201420302c80800d105015034002d6860001003490420f0450740c0e56800d10500020042c51802091740354050f4032113940301400403c0260600380d460603003403811640d600c910300c40700e80d00c158091441003001c084421981c018541c41081d2921403410504548012050b20b405007584031040c103c2c131017060018208c000180000240c0f400b180b04003c8510b400101403c0f0f03805000c0da00c1e11a044801035010952080502d41c640c0c03441030a20800c0990601098011102c06070801c40200712034501e0179041c4041008915400b004a01e80164058107180740022400b200754410024046801401e0081100305800c2c106000d00b1040115242d40e52100c1141c42040e0900302943c89480304100818a07040c0861407121040e0041d00900c0210010010f0091910 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 828294910 1250 828293660 828293663
    0xd060e0c0d0b13020414010237030e040609050f25050715140f0901020310030f0302031c0204060f1806113a0c0f02040e030c0304030f0c1a16 62
    0x503201c00e0081649a424400341001c0c0100f200c1c4900c40a000c0400649000840c00c0500c00c0d0340a4130310340d503101441000e880c101219501d0824a0503003000e12b01075468110340e10050303134080e04101001c40c0001c034580c000703481a800140801d15503241c0070b1500c81300c101c1204414034102150b10702410500c0c0620010b01c41c061249090310402405044480100c80240c0c1c44100303031081442c01d0110070302e080ca0009411800c500b00840c61030500c10411520b4480f188801007030881d900038440c5c141402441502d1349407000e400041c201d10303d101c05000095009029200c01325000351204c0300c4c0300c0c0c80388502d500030008001e1054400d500300403007900d02c0700c884004a40a40304120386900d0384030013400d045090380c1d080014000d800d155040d10204440c3c146440340b0070461401081c60209034121841780300306805890000e442402000e501c4d06500c181040c0120b140300000c0d0010402090040c8120031501130f080350300403e130303c03810008a22134006443e200c3d808806d0291005490341a41000c3e6060f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 828296160 1250 828294910 828294919
    0x10110a0c03030519061d01051516030c0203060709080f120d0509070503030a020105040218040206160302191a0f0c0301031205070218150603190906140c0d060e0c0d0b 73
    0x602c502c0c211350990781543c0085200d82084407899550000e65901d2034054101215081414041c0100044040c0205400d41000307a0a80b0b0b0180141030141d5440c401448c1c01400740c6141d031900d1030000c0c000c07407810b1040e840103100e04c004110b001e4001185c0130140300001102946840140780300203001d00710280115409016107103000030740d980c0400043c032035007080d40c002027074519150040086040c29203e0010355410460b04000c010b948181c103c0e07820f1b60f00c40c104181c0c0005542000c0345050300781d038290b24994a401141509215000c82c003c400c21241000200d03190351031960f0380e032040c00b00f69081d0144001c02d00044c000158403812a042d01d900b6460028242030458000030521011188003654094041c0b0501040c040c2030000c5402e954002d4410a14604010010064040e118880c1a1100e9650220b6008024290b04182c2d40b120400c40c03100c20b01d0138041d01e040e1240d40888405110140f410a000541c000043c0c0020304c101c00b00f000007418486881c4a40c00034080c0c40a000b07600 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 828297410 1250 828296160 828296191
    0x1d0d0212070b06060f0408060f070f1205041110020102091c050a0f0501090803070915030507141608030f0f010f08151f060e0301060f050a0b250510110a0c030305 71
    0xb03605c64840604014081140104038500307150743c0071900045d02910b94030402c80c1003030715078221540010710381d120820110f40c00035440c1e42d982058103042c2c01404580b0740c403a0b10061180030a0303078150060000e03200102c1d4050325aa5040200ca011a03004002c000d2168205101200c0441d80d1008c80048043c000c0c0008a840540c6959140c005c0d44111000303c080380341e0b400c090207409400a400e001e0140a800d01300a107040c0748401401c4ca4403140e80e4802180c3c400211903031103850009804d07c440740e10242d41d503201d0070a03056008140a007100d4084603480c40400016240c222031031124100c4801c075010701582c21007420301032003144008203940c405020080000c0308504202000320000d180540e03070300005c107002c18105825a41a90f1221140e0740d0218030901c5550303603031120b12040741d220846013565140d203030182030072803407107441030310909040c140d0203c040c440041200d54220b50301580c10010740d10039110039201390051000c4000041c03c4510400000390107980460781002045200255 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 828298660 1250 828297410 828297427
    0x6090402012a0c060f08100509071202070b0402150315010e0d0b1306050c04060509040c0e030d05071506060e011d03100e0f060c0a0305040606091d0d0212070b0606 72
    0x100d0052128110fa0340024900c0411446034422620035003460382c0c0c5400c01082c100300008820b058441d00541c0e10a070070b00b1011404140c0100101c0b800709075400000e640312001403c203e0348111046030164021460340c10b807202c000b8550800c9034403503001708020714080f034603050045071403035070f07100e03c1d00d42083c004241100420b001c1403600d440b98603d42e10003c40805a4a80b100a40b0000742132002c0b0610148002d120042c1c10000f907942c64042550b000450342c00b00c241c115519001c0e080016054002c030031a240340c02d40c0c00710003006e645009400d1a0050080e440000048030b010f031041c90000340b0646c3d5a0106036116115543d801c100000c8a501340540100c000390405002d24204002c659846c17540782c20402041c84107562440800700984003925040c0034a04061080000310b0041582c0c0b03000080030400280c0c42a0007400c140340d42082495407008081c0312144a81c0c600341c109109040190641510004605104c01600300215040c048541d4505040040140446510803001e211980 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 828299910 1250 828298660 828298727
    0x507030f0608030705010e0d020d11120f1305062506200c150702070e07090902070804090b19090b03010b0312040608010f050a170a0c0806011802030609040201 70
    0x20b815103002071070f501d85142c640b407402c44982ca08002d41c280c01c40c2062005554000c15108419505410482e05074002110a00e0400c800002500ca0510b40071403c0580c08981e40701031711001d000e00e0380d0b02600940b180d04105160081010381c0d20000f42e425012180800643c1014460f03e214000c003058120744403014070b88222060010030042ca4000c25010454a000c01000d0300c0483e0030f04002045007000380c0000d4072040540101d80710045070b0004150740754420b0607581e00803c81c9001c11511520a4500f10486901912034071108900780410b80c001450044c45030360341800641b003c58441441c14003400040c05100d41110303815580c643c041d1485440900c00541c0042c414074640d5512414007801a00014060b041805082000c050500c03040d101d0980c40000c1c6c89083c41450081b20584034142e182c00000540107054002c0c0d40d8000464103130024519040c2c40c80c04462600850b8101c1580c800c9000c116141e60f40b0000000100d405035004040140070b401401c6140d540b0300e21600040b8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 828301160 1250 828299910 828299921
    0xa02240406050c010213061d060f0405040203070207150507210e01110703020d0f020319030804020105031803070b0f0711030f030603160e15010e0d20030a060f1b120507030f 76
    0x50100d03c1032021804d413860701d08c3c2492481c140440d03040342891078a0422810720f010323070b003d41d0f805103030300001041c0842e008200c160010500032070702c1c0388124500e0304010701c03607046600100c2d11748801346200c5000502c1440c142c0c1010b90350340d4422501250701001117480401450a05005000c0d10f00d003c805078540e500ca0002c401e01408001005000510501d8176001122088014010140d00c039880041e0303000b420741d60401e809281c90341d141d4541050390300c2e00c01c0542c4200e400e079110000e4090100261980c01034400d034100d10b6120760940e20716609030b4004012082400d01030700100509e800300c101c15406143c000d080a01101d01401c070006000005491603004101071500c15800c10491304001c0345459041d0b1070a1074001000c015a0021503403c2a003a0b20003000b08807202e81205000102082c54114900003c0c225507103458a400c0481c02040014043d02996041285c1459098080414000b126201ea41c2d641c524200003480d1300020000540300c02c0405440320300702c210444540c000c1 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 828302410 1250 828301160 828301169
    0xb0403030e16030507140a18140a05150a0b040e180d050c0f07030b04080903150a021b0d0f14040308190e01080c0301050d03020c0a06020a02240406050c010213 70
    0x41c442c00b182541001864603551741d20400b01117000082609494561480510855000b000c5202000708a003890394040d10701c1c0c01000c0300030f41d8404104031010b003040d04a50701921156800310a910328040074403905107403d02a0440303240c810082080003154801070181d100d9640c012194481c00d94884190903c840d82844800094002c90102c00102092020024880448000f4140c00740740d561107800114000f4800350490b6000b20300c0c460661024840310078001d10740541c902c110320346400c0f050000c2d0080218509003a010032556800e0003070028648280000540b2803109183c0b8419089501500c41a00d840c90680288000800a17039070401900b5880510319071850081714940000384907400c009003450401ca01282070290b4852141c04403415204161030303000c4055807600b0141d240c00c440303c180540149002000080003940401c5010000d4800c480000c0751100c11a030700c6003030220203d40d4001c0e560003080100641d5020b00010068000b946c03002601302882c2e08068200401d40303511 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 828303660 1250 828302410 828302443
    0x40b0d0305071209140d05010905012d06180b0a03051212090a0c0302040e1617010501170601060f110d11010501050307030503030402060a050f0d140f0708040b0403030e 74
    0x35082c08009207007028900320020341c40c140d45120300c0c14042c441030f41180d0f04c1c954040d1582c99541010700134203410011050b90054000c1c0540146000302072501d000002501ca4100468010742200e1241400785404544182c1d0214180c6840300600e90300502120505e40d40c4425031400000016106001440c0250207400469894a089001b0880c01c030100070101c1d0f5a541005800100068024160078103581d01500c0005452054060b000d250580c003005120341140c1e0303605e0000d00218520320700c8140345001e9000b406203990756005801222003035840303080690007070310041c071040344580404510020585003071002403e4491515007010f07110f0050500049400d083c0c0d4840c91747c00d000b0f26004120a5006040603407850301c0701c589a02020b00000e00c02c110000b00640c1c924800c10942e11510031107440140d440d65460a40c10080c48203d8070904258400c000050b000c0d00c06500007032140100340c40d905030b10340c4c843e50343c41e02c1c044004104500740742d905c0402410150b410031800800380039400 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 828304910 1250 828303660 828303667
    0xe07090b03160e073f150909060b010c03080c090d120512070e03030d022a0601090b0f10110a1b0e0f0c09011b0503030c07142109040b0d0305 62
    0xd41c014420010300841340c0c2c5d14581040854074800c070f22103040616218000750800d80000e5901554080d0141904044035402c13000d002241e02007990740801e00141c4a0303007041090181c8000155148555000041c0200b8101e400149102e0f103a607000f00748640000700000b00201d0386a8131040080080c02502c0300282001c02c0753b001c4105a10142c03a0010f80c0e50514030624841000000d682c0d01c902c1204503401c50b000308000790044183d400310080460b0100d0035108185416514031745c2c61000f4400da041e900d0030181480c4450410201c4400140030103000c002680680b000151480d060a0800d241c091140d210114003041400242040c5d4450f0707460f0554a080c0340160300380d002100940040325001c00301003841322800058040356070208083c2448a040c1c951001e0102050b405c0050160150200008101101c408071000b0039440e03200d04804002e100754500e1071a55a1604188506001d401c50258010305a800c0c0240c11480c2000304046454036500c000314549003407098044001c2a40030 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 828306160 1250 828304910 828304921
    0x1050105070f0c0b09031e0d0f0207121406070810030b040305070c0b0301050a050915040b030f0d0207060f0c02030714130f060905090312043e03100e07090b03160e 72
    0x303000d049550242580300400e031003803a94100c1e0700c1d080701c60140d40a200c600c209c00d8110600074050403005100c258039032519100581069a042004c1c1c03200800c1c1801500d0014001b030b40100d402c00d02414001c1001e6030420705654480c202400040c0c02581030042c1408104006000d00c0c0805018003000070f82107032203515100034007a9400d620b421151281c0c411000300a00b03500c4600006446910032200451040940300119080c200101e00c00311503400340a0001c403000703400003a114120f41107584c684a42d028810000c480c050b450b55002035250b002501c5c100018550700301400c407000e800805040301c0301c1c12150140111380f2a04004141991681010003035202c036840b8182e440031724100034500c3d001450b041003083c1d400080c802000c12182811140c15400e02c2505145020b58400000400c1c3c04014000c1c9c001600303000d44d8521034416040c50041d400790138000d4201e4013000c2c10007440f045003403d00401c0a406c00a0341031342c152140f007001180c6040b4481c40c400003031101d00340d002d6840c11325 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 828307410 1250 828306160 828306163
    0x6110a020a050f2b1b0b2212030509010609181e0b0406110d14150a08031e090a0e24130c09151808060f01050105070f0c0b0903 56
    0x5161580c0001d07040030803040342d10781040340e0040c04501070781101c080070252044103640d66034000e03040f003ca024001910300108041081c0e007d02403080b0460300c4052040d62000f0070348441c011a00105036200c1483c24188480c00381c1c10090708003a03400d002040300c83c3c0b80c40b5148103d9070202d10b0306c81c005540036800400e1044003a440d81800010a0354105040320030340702c00fa422034003e400100425911243c5050384041101920406a041c0106205103003d0720b505000d0000c080d15105020031083c0503120451511074444002c0f19010005141051034141c21600c084203540c84080c01d960040111840350394444c001320340a0640007001c0001800c011032807001035030302040c60000341c99070786803141c40d180d40d00c1c24000829000d1420210340e044052600f21000c68456002c3c0300703038184030002c0d4071246801c04d10342c2006801f03c808603507d40340d80700c1300708d07680782c0c4140e46100c0d04810600c01030080d9445140102080d038050a102c90210300a90340d07030071703071400564440c403403280010500c1c0c0c405240 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 828308660 1250 828307410 828307423
    0x60b1507170301061e050d09060504050c0909071e03060f0c140406050315011e0f0e330717030a0605060a080a0b030705060c0d02060f040302061306110a020a05 70
    0x280010700740d003958100000a00358400c0d1280d1001d022001c0d012610606100d0000c90b01181e10f105402c0c03101252034a0f02401402041d80c007203800d8050845244120300340010074a2180d19044001c207001403030b000c1102c00d1141c5444000401034010302012022500038085c1c5050307403050400029400343e451100505201c81301c119600361007420001005001d520900341c94020340c4440b00003480701400801650704002500d2071160000f42d9405110340c3e03a030002c401248400d0b0b20340351800c12100400c10001000754000082d80b4011407440040910030300400b603282d00401861025140c001c46031287c00440c1c030040c00c4810741c07030800030410042c0314141c09420f00502c0c090b1821805c10241003409031040c0f10003031042441a0383c0301c45481c40740d0740400c0480c00501016107040d80c1e40700c14a03441e0b5150079034091a600540f26660102d50484806085140305d6074055003d0111a20b4812044401741502c00d0152052512503609113000000322008208856030740d0010500c603805407400e1800c0c0321 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 828309910 1250 828308660 828308693
    0x13080304030812070e030a03030c08010b1608250f120f080a09110414010f0b07030207060f0509120c030706020325050f03120103060b030d1407060b1507 67
    0x40003808204002403803401543e100c004011400156542c07101c1d42140d58482c42e072821985403144148407814107405071320a0411802e00e40c0c60f1020b1ba030702c40c42000c5084c0300e00c00940c1032268860041001090074100a44015546940030440000c1e6a464034108090300303003000e8130701000c0462100c0800c031101247c545034682c3c500306030380917040000d006021500020051081152101c0350b0804001082105001c0000002d0080020070b00b080083c0074030900900400e41503000e240b2000c2005410726060352842079155005146003414513504880348032902071107406112003031091b001c880e0380314400d030700090311110700906d19640c1c6030040510384805903000200b075400420001c3c404e00300810511920320b0640409080c55003651501c14501590201d00060034040891814211140d941010307042303901500c01804200b14217420540c9030002013a1410118405101d8401035194490250440601a8900213500605100892001c42692854484422000030700c1c03000c0201c849282a00300c0f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 828311160 1250 828309910 828309913
    0xf0606031a072a03110102191202040b0403121205011502011506091e170703121706090411030a06020d140105031e160807170307031d0d0b09031308 65
    0x102034403c0314400400071486030070b43d41d00c8800401400d144c01103104070f80b00109100210341d5514105040380101c103480c0301e0a000204050b400d400d860f6101c0c003e0b141034619141c079447c605442c590b15451210a58655001030022142c02e02800390858400d15000303081281c43e0610310600084028211203070380f0640c190060701e81d00c050000310b90090581c8180c1d002c10000300c0210012014000c01402654401c803c800422543d01340d107141c02080220481c1c1c440e80d80050158a40c070025140d82a001079000d580c1ca00000005034245070001c1d00741d0b002400f5a100c2500c14528001203410035044090985455400180011804c0303030503c41c4d101c0310000300800b100d06504200010791903240311159a0381d0503a14070414500e82506110b071560b6080d5980f074054140c0c1c0e59246581e10703a1b070648141c170b100035218078080700105004005c40311556415545e40700c9010500d04800840c10b5a0058290404000506980010307071143d512070140180304021a01c0c0c000320f0324880003020103900000d01a = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 828312410 1250 828311160 828311177
    0x3071d13050304510c23160312140405091e1003020105040e0c090d0f02010315141207090207030503040209100e0c0304061103010b0d0b01180b070f0606031a07 70
    0x504c040c40103415000300d42c09a105400649180407a020b00c8100400340c90f0b800c008440040c4c1c1c8448034102d402019980c800d4031012007000e60218101d8a49200c0030b02000f10000c40040c22a02c16140c00804c10a80f04070281450780715000718482c1882120001640c020031140010b0900c0b1203409154401d07900c201580c2407500b580c0c002031460050f44690075150754580701140180c2801d03401d988040c00c002d840e4180703003d0942480c2071512242071041c1e01103440c0403034000c0000081140002950807641c00d918421040e41d01703000491010f00c440280901030005c011801020b2070000340340d200d000f9070795642c8a0034940100100810040e01840489608400400c40c8030b800b1800c50fa8040c03021440c403a1203036100d091141c00b42016601050703c0d040000000b00b03107000100040d081d0405040001c00072040e00074015075130358601c000c0f50040f042605004001024001004000d1148600b03030126800c0e00680c0c2c1c1c03105507003003038104417450f05005519440740d2451045080d4004454900f40e0301 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 828313660 1250 828312410 828312509
    0xb0307031e0b180621150901180b042a23090103151413060e0c03060c0d02040504020301060302041502010504021c0812070509040b03071d13050304 65
    0x1054001c503c59480814681400240d540d598858a64500140d543c20f40030818008005240c5421680800c80ca80a000e64085920507005109495035204407000040a031a160b407681e00500794018411150503412414203d104030704090000100b00501c5208a10f240c02c4c5101c4682514900c100035840d5140e1215200b65556080c1106046942081150074107000d034001d102c01a08000b070130210b0600f042424004041640f5000b001c1a50081c841080b00784100c2d81c480303441d0940c01c891030364958010008204030038001d80c0144000b100b200001441c5c1070396580410300303903002603002c0d20101c0c0e4080ba04000007511245420209181d604c002c0042e03240540c001566802c0d40030702d094144210500c0102048001c40444081c02284803180c5c0d164a000074000307000354810641d2134041c43c00c000750b40313001d4240025850240d80000200301d148811014528070300c910010400540030281040160200317805000600240c881060041000780c8005c44044001c05800809001800098010310 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 828314910 1250 828313660 828313669
    0x4110d05030c15010f05040536120417030a210608011d07060f2f03121017030f03040c0509040b010f0b09030316030207181b170703090503040b0307031e0b 68
    0x12138840b0300300104e0341c038a09c140102e2401d102220500203440b80d140040780004058001c0e0045454060307a0100804100ca1869180c6c0540b520100201d8911525003003139000d6202c604084200a00300000c00b1683c45804500396030f10028900b50001c0022012321002e9401c0c00f04070050823a41c1000381c0407500b6400000c0400000b0520300100c0c9940d49240d18086200c01d1505d44d1468540341101d0b2149a0100c02c0070003400242c2e0144503002c590800010040d0641c00000704200660010b94184288080c14524550008000b124680d80c001801300e003603680c60242c0d07070103540102c1c01d42000d9814031a021200d5400c64110203490361060043e1035490707800008540b1100a40c540781e40d26214240f406902d0900b26801c5040415228842811922040d9000c5074100018000a402c0444000b0701901c022180001078040807a0540c00a03440078001e412294130f4900c02c50449144c00e5445201030450b41080d03600c2d41c0026100c400c1c04d00845184120040cbd03805011008010100307107900040d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 828316160 1250 828314910 828314941
    0x31e020a0608070201020d05010905072a08090319030c05010b031b060c0c030d0c02010e090c03060603040c03060213080c0109062001062d0e04110d05030c15010f050405 74
    0x1c00030026203100103024140300b90182d132100d40c4809020300465860f08143c0c0054034040b00c4a40c006800350110b95083d9481070b032414034a864030810501100441e88a51165902c1902825007500c0340049240d03c10a1040d20700744001e010f962151290701d1305182c49803c0da41200181e80c0b03ea4890300141030010351740c40340783c40350a13400c41d45107950f00240e80d00503041051a414066141c01040c00c03500616030807020411130203200340c1c2c0700032a0407040410007440316815229040c82c0c42044c4002401810084011a0080c2c0034008846441340da0341d0701d4401ba40c0c082c0014250100c0d281d8010844000200300b020007078402400d01100b098105240149030182c0b102401d14071070741d410258100100203502c801c001d405c180100129000c0c40b00800b00308590408401c245560385c50300d000613040600d80c8807a0040340e02c04c0d040080021408104041d0200c21300301a07038940820444110309000c100111440e181ea0003240d040150315281d1010724030103140e803099014504101c1003100041404044 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 828317410 1250 828316160 828316169
    0x12030a0503071b060c051306091815120c0e011706060f0409080309030403030216080a26130602010509340503030a080a1811040507030f060e01031e020a 67
    0x1014059410780c800101e10483c4880a01039901c0d000b0491440355201c801461450b02104030799441c2d41d40e0308411030b21700d030b118840d03604201600756040145070482c2c5c01c0060703d001c0610100700081e4039486400d80b6400c1410080f07030200c040781810003522200301200d60040c014003c404034400ca900c1c26403616524020700c4a0322503000441c2940303559541c0d81c043c0402c07681214000707450380380601486507291302500043d005417081d800c101d041200305203000410788034a20054503000601c1e40d6104160100d20110520040c091050804600020401781203811816202883e01501d800406400c40d10003800140e040e03002184081419480000400c001900f102041c06281e00260010720462100fa0030450345400001000201c3d00c0e07004545a000e194445402c03c1034041744e5000300380c11000e41500a20451281c2c1ca10311407803800d984095400840c03402c0104420350041040011038145812620f695403204005100744280702054202d09040c185d031503800b0f034442d41c0014000000d148139 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 828318660 1250 828317410 828317417
    0xa05010c33051512030a050a0509040e1f0b06070206090a080a080309010c17010b090406080f01150b07020a0b070516030b0f0601022107061d0c12030a050307 69
    0x200c0940325004031811a024003481e140c0c8109600c1c40300c10401070a4140c41d91003040c0b0508445200c1450b00c0100202040c060308021494200703a00415240c42e00421420740a00c40d050040d50f0054546014921b4400b1046014050000c0d070f10320b00c003440780c08901154004900d000382c88452500c1c1c0c44103d4100a4044800b652a5a010300c009500700b5000d8029240b1070144811400c00c202c20840030f14001e51040000703004120343d951003110300707501c0b030454080c03054022001001000f80d044003c01041001400110b0b0040d1201c1010341ba0240900d840149a903440c800c60164566101e200f82c0500341c180d0700d0514090b0207400181550903103010700c04071480005032389410000100f24401201c3d40c1c01030340340599681c0703042101031036204840980c00c1c0352501d0000f54580d0b00c0800d84107080c401c2c00c86070f00b0402032007102040300c0c2d82000c0b07000c13501c07203940741c00b50f1100910b90801000a0210400105480c088000c00d00c0200d45154000115562041c0520f0f040240c0000a580c0e01c00c2e15443d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 828319910 1250 828318660 828318683
    0x4030225060302130f0303110d110a110103180305040603060b030114062a03181801030b150a08061b0a0207090203041502121519260d0c02010e0a05010c 67
    0x30525440784005071700c0132040d004031203400130030150800c1c6194952100e013000c0e00c01006101e002940c040b83d0742d00b01104907070000040c02c2c0000e5640c010300d1102c080306140015000e81d070302804003002c1c6010070041c0e000c15000f05040100c2c0c1ea060041c0d01c0a8100100b0107419545010503d403d80c0b001d41050780d11918011540130030720310b12000e240802c003081d0440c1301c99819806004c2500e90740643c105d19141c10400e0119a91401e0410040208100b050003844c0da6030b196403542140300328090040b18617503003100100f4000740d5030040c0210181c81e0100c003404040c20050a8004041d082c5c42c40e03a03055aa06000c1c0041c212380210b000011a2084c440250340c03540c40b450101c124070110700b051105c891000c1043c1e0100c00050120520410500d54101e0a01040004200f801001120003040204070700030240b01c6021100c00600300c1807415a0b10340c6159064120050610f241d00120707000250802030000250341c1d000c2a460b40d0760009890712502c260420000801c5d490481401800d00310380e41 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 828321160 1250 828319910 828319927
    0x7060207080f0d0606030f060b0d09060b03010e15061002060a0f090f080a0e01110a020625030c0c0b0f0d0c0c02060a0905010e030c0108060907020102041a0304030225060302 76
    0x703084505005840281c242c2d10074801c189400181590f01601000a01d8910211005001407207003030252096008400c0c203008007441d10700c0103000517030011181107444122480b03264809020b034203022903403600a030400b0480c44065004000008001510603556041007001003070300882e806030400d00d0400d000c120000e010803c04007402c12420000c001c2c86022842c001130050a8003d4414011180d8032154886086001101d10800c903111800498104541c2080181b80c13440003071003030111612007200c808e4211a01005032608194003540401c060001030307030030081c800300385202500f001082c5505016201c100f0a1142c041c02c0c07901880c440d580c0582103843c2d4028194000b00c04e030300900b8159505410362000707091120922030140072a0108540021910f808074084c1290708040c0d490f032840380e6807101000940781c3d0282c10241555800c00011440800a00f0020f031108071100380c07650f41c0c0c1440d00d00285000c00030520a200403150307ea10769482d030881800c1da42226103a16025031100d450 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 828322410 1250 828321160 828321173
    0xc09070332190603050601090606020d0816050d290325060c02030f010606180605091c020d0f060c080702010207020906060306130501090b030f060f060d11062209090807060207 77
    0x4e8001909038410140001800390361600030005482195003514101075030084155481030080d1400c152001c0400c50640245100d480600008500860041124101c845041000f6548030703170805036401c003007011100035090802a01c0080b0940c501103603486400541c10a8800a190103258100003150224001350340e030420440880741081402007042e81d945181c0500710000070588184a1036900c000003504030f0090b403d45006910190103500c00644a552035504415500c00803139008401c0ca41d444045040c0c3c84c1c042c00407d00c126000a40816080d1000e030036250010a041c0031a030040080f0b20068440c1e10345503070401d0060f6480341e125101d9100242c103805d02441e40954003440e220000070307030510b25040288104010341c29968600b03801542c042c0c6403a4101c9100c0c00c0c00c190075002c00c40a00b000c2170a802c107940500356004228001c000002d01039406500c1c02c10211705800b404010b60425810340030010300e0550820010b05495543d030003610b01960783c0140000f6030210310325052214 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 828323660 1250 828322410 828322421
    0x906180b1e031e13020109090f060803120105040b120c040b03031908060f04060f150504090207081201080609101d0d050408060906060906040e0c0907033219 69
    0x285220365481e4a0007a43d1803c0b2050406144443c50b0200004034050f001c3c2c000c130b149a503540681d50403c46034201001600075100b80402036034001d42c0c6500c00a101d61081c005002045a021070308507042d45002c1c100810340d4040403075075100f25243c800e20b02e101d0500040800e00c00009903004103e4400b4100000d080d4001c86505903004c600f0656400d01003607001c80580e218003c200d516180f130342c210070f003440203c9a09010718541c0c2c220800d03090100c40c0700101c114010156a240c041d10b440d03160220101640c11100c001c9559081c0404d02c0503c456624141c1800751012030300070304a074a002c2046555451065100324441e50341d840c80c3e18140400008038882440e4080120b0700c4204c011040104180d101e03229100940c01403101080701000045205400313114010001d503890341b80e03881000024039000c48001d0944c03003402800800760b11922582c41c031a02240e20001800300740450403901c0b07442c2c0d422108401c0c0764840104c55042c0ca098140d9074000c4608070160f07a50101030b5144200811 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 828324910 1250 828323660 828323707
    0x140d0e0c0411090120150c04090603080a23030c091206130b0907050f1c140c1003050906180307080403080d0e0d020a171201150906180b 60
    0x81c201401c1c262800c0d2901c0003054440420303a07400c045441780c45800d0721280304000c04001282c002e00021462208110301c06900302140c10201458140d46074400c000700e034400c1d841281d0042d00818001525604024002e8011104a00342d940d0b0808420082d8401d2000601000c0c089401003190b841e55102c00b4104401402d00c4421204141400c0300d09504108484004480c11842100026048100440e42604480c0c001e41816003c1888100700441d85d034500e61070440e2803061400d00404102c125004540d4484500064108401307010144481d403081025911f061504200601040c03900000340b0766407000c2081c2c12056180c00320403520341140f082000c050041100454044140504280106080425101c04000709220703100e0540d04c43e03103a0034401c0b0158002c40a100d0204012880f0000d01a18811035580b0300608074541d401440c0083c1c00c40c411180075031148508143e0030540650140c00c1e141010700c10038001d2001080b943d8420301071048180c5000c00c0d00700720891030b002c0001002 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 828326160 1250 828324910 828324919
    0x91d09060c25050a05010605061c0506010302270a05100e090402010306171b041a01142b050702010501050303273102041202210607020601080d140d0e0c 67
    0x30b000b6050940ea0b07684822416034095107001e2001420340740650031613044000203401840402c40003041d00006080007809141815000c0102d8110b100528040040d5140480031112080103528180f01010400f90030090040e40c0f1550b001f100950004205222641c04661510312a90f41d0710040300031702120f0340508180320016000b510306c004081540700c1c058030808514001408440c042005945829041904070410140c11050300d5105003c010342c034810384204640340101c280c103000702c1050b03003c3c4003e003c6845880b5a5250306030300d0148503009002840240410350600300003e40381e200356041d485c01100ca580004021442c0c0984202d1940c2c03009111241c01c102c5205000020b41000840500d203151072240c001c030920261080d501a504054005810003206030f083c4004450700c0e004960b0018184030003000d260408200940c490401c56000d441035526001e140e0380307021200f8108400b44a4103500c0c0d1650340e401d803030564422900950001c144403c90790b500e242821108540750380c01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 828327410 1250 828326160 828326227
    0x308030415110a0507060b010c080a1106060a1505070312020301062a030906110c040c05070c0e07140d0b0301090c0501020705060f040909080c0607091d09060c 70
    0x107000e04040060300a058004091200c48103601c49015548a10b00d4814081201803004030040707505079108105a5106060100b4010305a40f60b2200075002400f850f4006540503008002c5101c0034010b00e9006074041d40d8005000d41040f04d1540c80c0c0440152200401c040032801105040c41500b904202500440741150307a5619058004c10100c00460b6444880744852007601512001043e8406030315011342ea40720241e418140d04440d00a1009041d04c2e541c402c2c003002c003140c2d580c0c6106480494282e61a0307142e490540345018001c0c3e250700d40c461100c00310700c07004014000360400f02181b0b6504071203c049550300203e20341e010062a0b03c0c030750309403d5840c0400c5041044002c00018050314400d800301d4800342c1d6100c0400100c0c1c4140151a0f4001074144003c00c1030205030b42040140310f10414040e824104120015850030710301b01e90b0000018000003080001518001d458000e0b03080300d18074800c0c1072514101d0f00ea5500400f40501034010000a541c1504540002840c140c02e4032485c0a82c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 828328660 1250 828327410 828327413
    0x307060c050d0e2112060909010b030111040e0f01030312050a0e0a05150c090d02040b01050c06131b0509060f0103060803070507081b0d0f17070807050606330403080304 74
    0x10345070070545011408915041c50a18040b08420546120b280310380c2184004da51075000780107c0010150101c0000c0d0340ba0580c03130700d280ea0b007805040c4110084501c0d103a2901d1428241c000302c29405044050380c0c08038000188046079100e016074080f10b141203000702d410b88500c074102000b40b60608001ca014001c00c1a10410080003040c03140c10542c030311540d4206078464444007001c078413034286c030b940e4490385144120f801401c0641080060082c1414242c1c1050344e60b06984d03090000840f40500001141e480c03003020048504060304030022000c003d801c002d42400c0204290b00009420144100340c900341d06411070303100b1b420820162280d801a6500c2d0615072815586d1031280e401410f10030300541c03282d1405031100c0c00d00300341c0040005028042d5000591140e074500f90003010185c503444c07000c0e0091211540e01d80c006003c403070f11400000da0f5403000c1e42009402c150002e00303418070404c1a00c20280c00880d24010842c1701110001d00303a442881180218641481503034001030505801004000 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 828329910 1250 828328660 828328663
    0x614071b080109140313141305010e1008030909010b0903010e1e060a0c0807080703140403170f0c0d270803010807241b05010f0e19050307060c050d0e 66
    0xd081070310590b40044c000084224035030322801065004041909259020000110480d00c213400b940c0c0003a014010b80040c1c58002000c2e81c10982100c0c4041107203030240445400c0402c071340c40051506d40c010798186650780b030000d98010360620075030010b0140461010541e6600798414541c02c1a500100d0740e10704807400220a41d03800b102c4002c0128001d500000382c80036050300500703030b5034a103994501025a0364120b082d2080750000e4034103c01c0513658402c2c1d80042080c070b8181d9003e079010b1345030380f45c89404e980105e81c00c07198014401030300b03107010405020303004c0200b5040c0c80c0250139109011614030f0503200308001140c044122085511501c0495000748202540194181c030821000e0700e03140c80d2212a0b117404420224818902500c04258130443c4a10901064114030001140710802400c1a256242540c83c00300c1c4030000c40340d94103e504401a810044075010780d100c0c4018407144401034071402e80302d010b80c0c00003500458580c2030b41e00340c56104400700c40b8a900415410004a03030426001c6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 828331160 1250 828329910 828329921
    0x1611070b03270f1015211b0f05040c0e03060a0b03100f05060a0b0313030507031e0908060601020d141806071101032901031a1221040614071b0801 64
    0x1803184602d40f40e1100d411402100e2880c0c107071a407030484018081160005555101e02d06c401c00e40c0c4140c4440f00085009207100c40000041192800420600741480701f000126021061a001400340503030a000182d140400c03c02c1e8052110b0740000b0b14101000003003400c0007603541c241241c02e80b8041c4c0304079000b0180e41c0000c0c080d1100ba81c0f000d82c250340302c2d0159403030ba120a4950410020032161000d000078031070001024500d2003880c056011611004c0c080e400070901140e29008561072160602050f04100442940603109100418140400c00c2c0c001d01000002c4200300f1102800103401c030305440440c54091803441c030250200b035880c00541018801341c002c00f15106d00127401c00c00503240740c51107150541e40050011700b180e01d01001c03a9005500820100050050051102c010b41c001ca50300d110800c9450340c00c441c05842c191404860324079003010108543c1e18a20824001841a0366028681c91000003103ca4402c1d03541c41e0a042c421141c2c11205100600416000c20114000a064000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 828332410 1250 828331160 828331183
    0x17130f02040e101d0f0a0809040605090412021507050921070305150903030408090f151303020a0509090319020705130c030c0819110d051611070b03270f 67
    0x9051010f8015203800d0702c41c680d9070700380a05e82e40311001080c003180515009000d548401400011500c1d5200041035205904807800d80d90440000e001c51100381d018002081034a549030900e5400e4589004054800d001d0701c0c500e06d0044449107a980c00d1901c040070035420010140d002ca9081c19501c0c5000c07941c482c8040ea840f04005182d60203e0503d81001042e00e020b6076200750002d0030402554244480034610210b0030b5030080d43c8100360320507100c0c202c004207010980301d03028030030441c254014050a4541c55000700e000e00d8082c001c0103603886011082d10706211010700c00c12a4820705107000c91130445143c004581c0804912b007907698540c4180e1001c6282c011075101440703d80f46603201600d0315801124400ea0b40c0d2201c030000c44903424194001c041d002120040702d41081600045e00301280c00840d41c3c161180340781510420340c282c103c40d9880c002c0a440000b400014103000303006034580401b4180e541d804c00d03410040540d22954820084a505541040f03440103e090103c4554940a1414 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 828333660 1250 828332410 828332441
    0x1020f0f0303010504230c18060c030901030902150c06070807030b0112050702160308040501080906090c0f0f030f01050f06100212090a0b03070305060117130f02040e10 74
    0x68800004000c1040c0c08035608034409507041d0303840c0100f800050191501c2d03a400301814045c900c1401042d100c0054000e2000e020000e48400580a0410340e81c0c02114100703210319020f00c80119013010000032110111000c2ca00403c4070706082c404900325180103803c4200d00400031070004034030540018031507c66182a9506112504c030000b081c2c08540a9800e41c5002440070008850036160740d0708103d030010100e1044030f18101c075000b10000d00044540044422402c000f8080007e50307400545580c0002c1c040014103445d082018120f56070312a8840c40c2406071001c4545200280d1340c10043e1b252510020702074482510614003910700a2100303c40c50030b0411640c0d0080741c1141006541000480c8690300200001c89100c00b882060750481c482455200c041c0741008100580d80d83c01a5004900c1910b0218003414241c001500415a440c054009440c032003041040818081c5c0f894040c0d079030016689040f110450012034040d103800d101c454002d22035a0700400000003a1fa0095005215070340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 828334910 1250 828333660 828333673
    0x70e07050304300c030e030709021206030115031205040518070807020606060f1305031606030c21050a24030302070b1222020a120308090105010b0d02070c031a060102 73
    0x41c00000b050191004050030001d46040c1805841c040c0400710001340c020706240002d5240c2c0400030b46403014135005060841d40100e5003000c2c003040410318642150741140280030001ca50100f08007218800c0c071001c0e000143c1c2c21a017605150080b002c03100989005400b54640c02804e44401178042826201d03540000c90b01b100040000d40701060080c02414020400c40c078000c100a10410107070007200c030700f0b5001103240f07500080700c0d6010011142405901d582030558940392440180480b081c1c2031540040c0540c41407081c409545034948010301610b903c000003000c1d26425815801041581d040000c1d109840b0710328442d1003102038541d8101d0780302ea0300319840b00d80c8070466500741c0d02903c00e039400f8100e030980101e0f805d040d00c031004250010b80b554442c149036a0503000a1607107040d55006e41c602040c9601c00c10203069201c04529031061910000b070200e5454a1824803036403080c2042c00805540c0032444a0420101e08018001550000c0b80c01010b0311000704070444400b02961030358058861803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 828336160 1250 828334910 828334943
    0xa140d1413020609060c01140103060510150203120a020d060306021306030b130c121e1107050a1101050408010905031818160903150c020c04060311040b03070e07050304 74
    0x1010414a12603010f01418181200c10b002c0c000c96401011450095548070340c4488400e1800c440024001c60003403002140600f89a00341c90180001900300d026038440d4901c0b4641420380000032034000910700401c05101d81d0352042100001d0060800c0c807174007542010400410300c0f880b600070f00807643d85080403440c407554812007581128090061250801c0d0003040014200c600c540c0f204062030021b0411401c40b422422001040707075426901d110b00c104103c11601081c1d10644030304034a038004424071524013230207038403165a03030126160002c0c1000c011001202c0b05074429002d440081440341c000340000741c20380c6400c85e103903001617104020642d00450405d14a24000c0724100608182020f0741c1515181c901030544880c4100f000d4070144440004000000380360311000e4104801600800a10130040300c000a0825480c204c4581c426420304c081800440d03a400080c140310441100d002903401200c1011031b0074200c0e0b69100b00d5100076101d0800030005d4201e0000c42c4140c0c492912682509a074 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 828337410 1250 828336160 828336181
    0x403030b01030b18130602070f1a07050a0c0b0702071203030504050d0509060304080706110a0f11070b0d02130b0c031b0715050304020d021207091a0d03050a140d14 72
    0x2001e00d004190003482021545088060386101d417507a000d03403405072038190581c40d141c00807448481c00b01d50914135000008683d0b5980c039507140e00854145025854583c010b480186140c9a0300320103090410b850021602080c02004058000d04031403106941011007410003500a207400c51381996503001d030f5482ea20040f0300c110100c6941807070003015541543c40b191101c00054010850864200d682d400c520244459a100903207940c0c43c0a550f42408a56100d5004042820098414645902080040c840c1801442c25548841682003005842d0090341c0c0440c1010105a4003100300400d0005004404042c0400200000726604110403010703204008440e50728072641c400c10602c4580c441607c120f082c840d030010341d0044e0000301136402400bc1500040c0300400910040f118607030014200304620702e058020b041c0319000c01160702110301000008185034051644009080080006004492600812501c07a05516050143c0d031505202114034005280706030005c0114070316480050280d018 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 828338660 1250 828337410 828337429
    0x509070207120303110708031e090706030908070b040809100e0904030806010507021806031b030706050702060d05010e0601030f0b1311040e0c120f04050705061b060403030b01030b 79
    0x815802005010700d02050341d006605405011410940c488903482440c2180700c010300702c60f81c000c281090b503c0c1403800d20b80e2800000941e03861204035080040086141001c50700c5812109281004218006185041c1d652407141d0107004001c2da0b000b000b40418016681c0241c00070400940d84030000b613190b418145c801e242c5001440d54440080c00000d400640300d128580c0e005001810003e0410a49500044800003440f5030403090a40075400c1002034901003189900308800110304008201c4c403100440e494010358005c05051180009400f0f085484036411030301e0350b40141c1010003440d6142c0079600c62038078054400344d001904080c1c03920086d049500c00e94249980c010028140c1c00018a84070028141c0340c0302140700303000180000240303604401351b032500c2942d1000c0b01550300d42d941541d1104500001d010701901d821000100b200098000a00300142d98040780d41d1030f2070302080401c2e0201070349000702c0744455001d28014030007095015000801a0b44090f03c0a2009402c0501400304a10 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 828339910 1250 828338660 828338671
    0x50c03040311010e060c160f0e0c030402010e0907031a060322080c1203190209180a09022101050109020c0a0303110c160f050603040f110d0507060201150509 69
    0x100200010400214901e000b030015040c181492020f80440324005207458008100d007074504c0e005851888004000c103000700c0c1c06031541d646041e801074140601c103031040e40000c00f0981188000400704055a001380101600b001000740041e681d1b01c5c028400030080c000c0380c0d1000d102d07002c084040841c18035104068074407234004690799104003920801c00c224003404008007034814400401c0514004803042c44058044903407141030664900781583c0e11400740743e0802d810b0103071074030500902d101641c0d2140040241e42e94448a070040361a1006d85000418050354002d500000403902c1211070100321a01c00480c0c0e694400030400d03aa070300c20480f810f170720410072034595940094601100007402507018111041648541500b000d0800c521a4035207640c071442101c4048403004100080d017500725691703002e040c0039a43c1d17a086041036038070340400c42d001c59001022040c6040a2694036210b9010b0700c2d58441d0400f040300c4040d903a4041c06402880031106161806101810118190070041165400341 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 828341160 1250 828339910 828339913
    0x4060c05121c060803070308270f01150f030803060907110d090302040c09060f140706060608042901120203010902090a0b2d01050a09090510051206150405070918020408010606050c 79
    0x2c9e907d841140000d00441e02031030500e04030003520030714405010803a010345901c0940001074144840214400d401440d50720103111041041c00502c00102403400356a000101510402c010741c541c540e05035064074240c50368451601ca100840100c0d1075100c291102205c0c000e0714100000041d1002c1151031180900950020482000d1000800c61145500c220820940d0f4512030600801d1b030385000955840f64400d1000900c0c1005000500080082911061002c01c0301c0c08101007820310b18440c0190705201d130301c10784242e5120070015500d083d001396001d554001e150060a00d8a030b03e02c03400a00344484114014582d400301140d01c1080400124030399074000000302c02c1d0515107401119075501200c015000c200c004d03034000480451384d001e10b030b026182034080000500d050209008100036423449405007944108180701810601e8000660b140b07400b0b840c0418207548101003510403103000d41c880b0b40c075406107010303101c0030072060f5016000341c900d080f00a000b4030b0390f1980200c81a000710711001d4403e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 828342410 1250 828341160 828341177
    0x50a0608060f1509090f0106090602280804051306140a0807051203071e0203010f02162a030f020a0b072409120f030605090c04060c05121c0608030703 66
    0x940760405440006242d0b4080184c034241454010840c0580251120f0002107034200050001d150801c0210000d004244014204034100d104640854600c2441c4001d0200500001c442030004480448026240c00381146a92170060000b100040000344103401e14080442c0003550f99190842c4c3d0b2000f10741d41c0a000f411850f0400042041d12115002d0708002840100041c10004521800d0041e40002482c080b4500a0803801418251110310345041c94080c07040003810f180707680300d01c40b02c441e05030888502500840080224100050614003801d008081250004200301103917100701c600500c01d4030114140d035a1040307082c20138022514010302c015468122401d000000348402906030380040340c0828a030401d9107502c103442e0b0071444244000b58103805112411038240c0100c0008040550383e101c010729010700301c0511400341e0701a50f0200560740c0001e0003482810401c02c2c3d9810092039002e641cae1940d500300c001d02030002d2400703406c18038101000005c0c40003000c0156007007245c00d80ca8540b031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 828343660 1250 828342410 828342439
    0x1018030609051f060b0a211107050d180b0a1215091d070e1005210607091a0a2106030302122109100e0705041104050607330204050a060806 61
    0x1107c00302040b0306050b0f40c410105050411405009040c0d1240030380390515520411030902034103008017411201c0c244118814a000703c0802002c04601b102d88400c1441d03160107a0074030465100003c4400c511044e400c10410b450603018981002e81114075583e0100b1501c9403110358205201800305c40e00c0c40b6904968410400003c006034420b074003400c0445852901d548a4000500202400d4088840860140e103007040381c0030100000d5170407070280d04101421a142000e0a1094a40100d0541840c1404122070600a020340100385121b900c0da08078411414000340c01d000200aa44015801403191003c02c4d5594140ba004176100201513000d51400d0035201024501802c4000e000c0e19240d00c1400c0c1040c012104c107100c0c52540083c00000b6128441c500001c100a07110070380901e0249800800040003280e50b114115402c10340d0104140c40201000d5949160f42c2e04072030b2048046215900c0301920901c1d10f940200142c44d0119082401292296004c8540c05011240c0d41c0d00034140407030394003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 828344910 1250 828343660 828343667
    0x13090e1504051b13050c030601110606030a060c020307170a02120313240c03150902040b120601020a0c08010501061d011b1104020403080403060b010e1018030609051f060b0a 76
    0x42c401c25020300303881e081c1d0300c0e0380d044ea1080362401c440c00d0413101404818892903603888485400014505d40040c5420f04006000a840b1910003500800f060307550084100d9aa000340141d032343d0260808402c030074100c82590304288960204075800014081e102140303c04140e8182641d001d502501c1c0c1810080388990b9820f004085031280f4440464004ca00c5480442158000c000315904140d5001c950b907003502d14202c00f842d0762600840e03040760040c0020301600d81c1e0704056410210040700d09042503100e03000180e0034020300020241906a0310140815501c0c0150001e6049034050b61f521103d560f500ac0c1072500b00c1450052240c0000d00c803004803851003c80645c2d1500b200e02880c52002c80c200c089001400700da00c82c0e482142c0e00300b030100d800c100380481441407a200d91003e0074240d690000032000a8a6000c02c1c410100900966501440c40c54039004140ea01031072340100e003002103d11909080380d943c403441140000c00c51404034038030064100350003a1022101340e915107600b80301a08100741c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 828346160 1250 828344910 828344953
    0xc070506070c020301062103030b0334030512031f12030f02120d09020312040e190906051005100e01050301060f03151e1d0a020304050313090e150405 66
    0x5a91646d2128000300d40800c0d4803924510000c19451a040900300c185409800d07590070318156446908000600d581d011001421080352500385040c40c11907802d5103122078a00001c0c2d40002d8058803a81080c2c00102d6103040042d03009a00151600d5203140c0748502205034010240942d052040d4000759000009000f50324240c0c0111880c01690f50303046082d494100e1540107916000e08803922980c5803805c1d0f0406020080e981c100c245d18552901d030909803017030003401c0080c1c0781d5203804600704800410320265034462041141c3c0705030188128200000951001d0300d286c06498495180e000310040c040b8006c04681c80c500724103840301170a50b0f01e044410740c0e0303040b0021001070615850384025410880f820801002914901c20000d0755409909641040805a50027106c04c14081100075440d0b203500c02209980444103400140c3e0b40e80e62481c0035400d600030348000081000c000c00f40403407095050341000c1d41d480b001c02d04992540004d1201e19114a20a03540503242d5040b82041103401c0200309600d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 828347410 1250 828346160 828346163
    0x20307050f030a05060708010f08121803070f18050106030506090a18150204091121062e0e100503060d0c0e010b040f0605090f0d060b0607080d050c070506070c 70
    0x3d4805070619a1107080c104242101e0394400940c5a0300140311640c1c002091001604840d002448496481d010303a084500c6060140c6d403440d06400103901583d03400b0841d0202070841080524400d6a64060419081032050030903042e06042c200040344c010b100b0f1023441d108101c01801100e01d52500401c090003442c10325202c2d05414152070841c404100c4076180856100d112000041e5164541107030201107684c3c083c1c500040f07480400154a5480711010300c1041800307200d094090a45230b440008018201c0c0101070841c0c6481046c503140c9592641e9501c0301d0a4a035600d900d070010401d00b0030082160010301e8404c022481c14000301d0a64182400401510341c410b140c9038441c20740302c16072080700319026071003800411000101070180706c041101160040100d410304509081305980014844661200c4e000d00440c54030f0000d07400d2010039003104036141c02c041c0440340d03150014106030320320340d0005c0d403554207440c00c00001c202d040710b10404070b80000ea0044094000b0b40c544100880304800d40240 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 828348660 1250 828347410 828347413
    0x1b01081e0405160303080907120c060f09050a0303121b200102212203270504180317040f120c1203050711010c120b030a06231003020307050f03 63
    0x3e241c492060002c401001460194540382d0061420051039858007810b60010150459012100c4000801c6004100e05989180c207040200444165080300d035100b0640c0855803010041d540041450b40000102002030400041407004400084007c995040f100310101d0000b0011084070070703001400c00401214020180016203001078608070000c000b00d4a1828240821101c4148444022103c0003c0018010b041e450348050816480c0038110304e480101e1241901c83d20307010082070445004046010b010018005c000c842102480d40700450840c40c0300710003040030b5041801a00c2010f03004144180d51210300356848491550314040d60300301195142c02030081074458840041c2d5210030411180b28507035000601442e0421006040303440c1d0f0710070100c150745404040151540d1045540882200944c000b192110781200802d182424280700506101d180007480740c410550303441d23500355042c114840c41d0311a03214525a000001c030103201c001c0d41a40040000c00050514025400c0c0d9550b0080 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 828349910 1250 828348660 828348673
    0x61d03030a09060b0405150907080112020127080303070f0c02060d180b091006060f0e010318020303070b0f09150a050a02040819060e0106081e031b1b01081e0405 71
    0xb00485c00b5103030705030307074649800c100d030842403849090052815a110115140407205549805010103049a03410b4002e07040103410341c5107940302000070103400300b4540c50a00a0f038105540e900000d4030707504250381c190001016038110300700c018030400c0343c1c1000f00c1d0000c012526098010021400400030341d1a092002d00002440ca00803c10300360f01c9a1203101d0941c00341000d1144040c00e00700712441c40d04030400344105084c024158951000205610350030038200000e10708400c4062001c120f4550400a525200c0001d5500030801141b51190003440d6003100e1103580d440780b04a65031280c407000c0112590303940d082c0000e61520300b5601f150303402c175145c002c0062800d80c60b0043d290400000502007100d05030010800000c02a541c4035214103038290f100200f0025091122558648890b44084240765400646050103410306008450545800b405030049480c0007000e43c94070382048483c4a40b0f45400280c500580c1c1d401040c401c1d12894098541c0700400300303000515400e8400c00b8009450501c01c61 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 828351160 1250 828349910 828349931
    0x12030902060301171603060b04060909200112020f090906030a03050304110619030b0a290912010e07060f02030f03010b07031403010603150f0812220b030103061d03030a0906 76
    0x141442c5c40558094500400c20320254020701055811960106642c50b140542c0d800104208502444d08010300c6115845811810f50040f9150030040b1941400b007407000660759502c3d40c90400400d0140303800d944040d02035031100e080689a608404c0c026001c40c8003080010b00040c0c86094140d400240100914103000b00b188583c81d4504115620401182daa0032240040740f0304007100310f00a21006090035680c07909540105450184800c001da00200041403410b40750740d80200f07403403407280408003c01041e02c00b08986942ca400a10841000c110141d060281c2c030780c400704c102d848030409944850301c2d41c0d2030200c001c43c087d40407407020750400c014151818603000d1020001c0d802081c20342e07404244c01d04070100110f02004154403030798860081842c00c201c01100401c62507011031202208a440e80034102080d80351031100c03103002c04034100b4290045003440b2600c0145060f24014081000b449405d0082d40500407100203900086600c01e00010b54106295004401028810040803a0621f040e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 828352410 1250 828351160 828351193
    0xa060801270807051f0e0c1002031e16060516050c03043003030e0c1f05030415050108010915050f0402060310182003010e0403030209061b0a1203090206030117 70
    0x1a422000c00c440d2204800c3c600806c0800c02ca021204d42210550600030300c4000203596840b500400c5004110b4881d411034414000c50103075048820490b2100c0f1303059900d444e1071001084d0403202c00720f0f5058400d000300400303481039080e11440f540c1d62000398641401d0100b2100c0390300501484881a040320701c2c26030811240000030440651098a02245052407808450b08065001c44a940940c03554608180c50904e0030b400003450001c2410456520784807400c103040c032546505881124141410000104d1840540c4081c1e03d80f13008228030707031018289038800002d8843c1070303030180d21110040700480d01601c0e03c02c00960300b1000c410b010004050b41d41d5a1445000003041409802c10307070b254020348030a02c54100d40c41040c0e80f0800b44914543c107254518864640152024081550214100a080d20782c01d00f00c47c041566803c80300c00c500311018496a465a410000301c8028400500f01c210443c06401380b98601507005100ca401c40e801c15011502c160940c5100384203a1003a1146040b402c0d41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 828353660 1250 828352410 828352453
    0x209060a150206010312210e16151709060604050703020904090609020a06090303050f0a1403010e07030b0a051e0427030807021c050a020106050402030a06080127080705 74
    0x4060700a0112585141441040c48031032186160500a824016047c41e841045c0803010080d1a1136001890342143c2d5501498498080710000e50400c00c95008180b60110404480d100c02d01582e030580c6000c88000d2904500c241587c4004183c1d000c0701c00b1542c0b6182a801003070380f20400e450014107041c411800142034030140c850580303465548142103015030501c1070101000d0112400d1103598a89944d40041c040d00c1840b100588200001c1707003081e0b10034880c3c0201c2905601c0d101c502c98880d45c542082d4151440d00b5500d400110786000c1f5601c20307a0620025003812110001e19005003035660001001446000508640d40039541c0d090040311258002c5d45200517002c0181d501031011500d14002d055214050042021340d07101480952401400c14005ca0035103009281c03280e240e94000c0720603030241080b40c0105c0c1c3d0190001c000c00c4410f10256200c01e044070f007404000c5c00440306080410071120551680301c141440004031603008580d1480003003c1640c4903404685e8452540c00c40d504c0c1d80017 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 828354910 1250 828353660 828353699
    0x206090121091505060a06080903090603010b0a021b01140d0615020105011809050613060207150b030111090f04200f090a15270f080f0d05070308040209060a 69
    0x60b41e5940581c00d000c1602030f081e02d1908200c2c41044a802c2200000d0040111442040d041200d02c6001450950781801501d100383c0001d400e00d5101c2d41c58503040b4060307400060803800140300b001100469541c400ca0416031140741a10b0722080358180c0c86030391340b0543c07000c030078005103a80b01c0600040f40103501400f43c40c1002d00c2d5000048035410240081c5c45001d41684207a001030402c442a00860f80104080e80c0106542420741c03103e050f00c1c81d1001c0640140c0001030302c4280013155155005809800003c1028002c400030007010782040300c0c0c242c05001e88d900c0320f9003110340700d03080e16200c4c04d06034480940000109121100e18191516010303072a800a400c5940030f0501080301c039203c0c1426480c0170080d240120a020b10014010760080c404010701014070500c42d8002c079612101c042c080828805441c42400c00440e890311100200d59409900c0180e0806111b40690308035500c0c80b03401544d1651340d07d40d49102244d141c580821001c0880034001c658043c5001a0000f4035030021069a2400d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 828356160 1250 828354910 828354977
    0x12d0216080d03050705030906010918080d1a060705070e04031e0c02040b040b130515100203030f070525080f071b0f1a0c010608030a120c02071202060901 68
    0x82c050503070081c15503902504072000d004041c410b00c007441c003010410303506482250030001100305031040d80c0e000c12102d03410080c018040014846a26013000e0b003200d480302d0701d000c440303032008806101840014425038101070020303013041405024080b440c0e08842c0d00075009103403004441d210450240c20b80a0400b0a80001c41c400000314011420a4081c401050310200c501f005041c816601144c03c8041140544030101c1da1003001681e0f4001d00800c0800c0c0441c06480100711050070350f00070755039510640b074200242482c02c0000d1025445a4111800b2a1a0030480821941140a5028905a403400c1124a00400d200f0f41041000c0c1001030035480c0e00510b0100c04008a03010a8120300d0035641000c2d070030070051001030251041d0300385942c07400714010303241c3c60b62120005d007201d004210681010105000c006030000301141d1040b42c0109520413440b0402010341b660000380e0b95a84103210b0802282103100080016113000406048070000605022074003514425a641c1d0015940300d911202 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 828357410 1250 828356160 828356173
    0x905011b081c051b03060913061a150405010221042114010509060c090f0a270b0d240c02031801021b150c0d0e0f012d021608 55
    0x810454041c003600980003518410b1506070504c45100703903200c02894a401100c010001c40c0f41d40c1a18101c241c072580d0040b6040048468030380c80c1c80540780f51824013501c200c0c1c030801040c400c0c0114200300e408075a8140c0040c90302d4106607920039944800d00faa11041d0000074080014000107110440040718103419008650084034541003031701c022454048481a8508020044100c4001a815801c1452880d500b51221701107800100113001c0c90002c02c1c0c102600304e20000781d00c8c0100990440881d0707001c2c120400940e001001400b120310a002035603114088110700c034049641e8202c1900c103e0603203500e4421285001d02c03071304240c03145510310b240180c1c000121000e40c40c400d0304103002110780c00d1000e07204070414641c60440c1c2040c080c410610401482004c2c030030030005501103618520a0005071149030640020140000c503d800c511401207030000d8010750030750320602500c03103403410300c200110403803c4062045030106c1102c220401544680054400b0601c448050f580042282800030500d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 828358660 1250 828357410 828357457
    0x1b370e0f0f130c0e0103150c021b03030c070b090909030a0c06050c19020d030c0e0f0418050703060207020901050a03080a1808120c010c0f091e0b040e060915010905011b08 75
    0x345140d48141c003107c40d81c9000c0503481e089901040c900004c054a80400c01034540c1340c00064198400e21000d1380d140d116102000074003020802c06040f03810702c1140d882d10a9901c1001c0300c0c0c1c407445880e24180020f410703c105980000c05035840203422901c82003c141c00c04410440087c045444504064050380c403e83d22001056454090003028001c58030340384803030000c3c0c800030405400048462074810364035004060054000092070520300b41d00b02040710441562824404025881100b09a0040207072400124090816445000449030f00c070041601c0e1598000701100e5803119614030032a518140000015401002c204005680303840f180644e41c0c3c0c5680000440c01c5681c0502ca100c240404c49032404031081d0030600c468101e0b02d018400d1076107480e00070034100a10155130000a5800c00114000c54a04000d9810b14071568056a404055855550094410341c0c84c490f0a1800984410b6042c0540e510030704112a5a4070f4060203040d00b213016933170b5145990040c50f007000c020781d0320014840 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 828359910 1250 828358660 828358673
    0xb0403200f0705060c010f0c270b03040602091224130b010611030f0304030e040e070506190e060a050903120a021b370e0f0f130c0e0103 60
    0x10040c440e4400601d400a1100310356511040c00b8850305220f00c00120303c68101240c00e411000d450b010500040242e900d0710790b806420808108481c0c0007501c1030486044410440c030301014240c2c0c00130300c50b550843d0703100d0382c422010750300c040310725034001446403100412144e00708859101002e01d041c001400c40c148450904003402c00070800651804002144e9011985940066055401524280c0e031400e1851401074514406c81c00f00010203d000420402032640c010000807406400b220306218540124210503522030a500400c1e6000100f00407000f40350084600e42c621241280c2803514166100e0740000320160000d01351000403410004104900b031a080c02a190200701e000c0640d418800700090080d0f503010385c02c044d2000b0408002103c2e00395650084c0c03e001c0c0180f071810301e082500c02490600c51040203000c00e5034001840e140081100c944011a13107203d03200da4055049140d03030b0008070801301d1401070208090f103100c020b004400300d0b01e490189800b404495018040a51440c60841c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 828361160 1250 828359910 828359957
    0xf0e010e03031b040e0105010807090f0e0402091503250e250207030317040f0813030c080d05070b0a0b090a020418050c0901030b01050c010e0609011a01021f090b0403 73
    0x41c0d00f0040200028001d120180351a01c0c1940c03003e103403501c0b9607514041c040e039900b00340da00004148404000001128840040300318810b1344291503000c40d64803140803040062050443c5213605800150401800700e418001c0680b0310302c034412401020701d0f0750702c801e00e0710701400b928100c800158584244810703450b01c040140d8200c0e0148018140d0a146890003000251440340c040480041000854144440c40640140d0f650700310400d2036846050821390603030103a0910003202c03071004440c0c0018881102090880d050b13860390720f0fa20b1501400d5628400c603280001e01c00065242e498895003500d88510701142d01c1502d09030030060b925414280030203180c0e4200101c00034040d04043c200300440747e4a07803c1e185181028240800c00303043c44c400588582c018a1441552586402122091300f0b074001750b0917015410f2000204080034030b001c4004420301c8543c0c0c07c20302591185038032561422040c901d18013031200700500000c0440e603684c6c40e86a5002d0a40c0d003940090848070040d2a204020800c1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 828362410 1250 828361160 828361201
    0x160603051b071707020a090f0b0406090e0706140408010e0a0308060d03090e04060618021b0307020a060f0203040b0a090302010f0804020f0d0f02030d1115010609090f0e010e0303 78
    0x107600b4002c580e901d0075116000101103079250341011400700110348641080002030b01047d02d050129014030f103924002000d12012052040d03080020004014041c1d21501510b071240b400034000036420b180c0c1c06c0e919007044062800c401501080002980034080c0300d1410100412000707841460070a0600400201001c3c040521940d820a06100042c0c1c02290303100c00c4500c842241c14460381e450618000030040c1d41c0c00220080c00681f44d800d0908040e42c01003100c080362403030b0025030811490580b580c0703001d50040250881d40700c03030040c00001d010304150610188036204036441c060701d500b0249655045501d6640200d01d200f01c0c24000c660b0040743e445113030303242d500e0b08804624158001903403074980400c1c01070003040c4176403000c024001c41d02090a003407034004d01154560300d1400001049010076503080d14080c094480e0301202c0c40480c980c16812201240d9519100604080340030300200004c00340b40142950310314841c100070100380984607000300700c880a551a4909207407140c40c2140740828 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 828363660 1250 828362410 828362461
    0x121e03090a020d020f0405040c1a090f040b0307030c080a060c031e051f0f09050903280903051506010806010e010203161a041415070c110316060305 65
    0x410500c40c000240315450103404440492103070869001050030501c2c1140d02540150400c002c00084c890000c2001085a03a1824420300d030f6070b60218400024000d29000613403100300004241d0780b626154101101c02e05009040e6242503640380e4600340b00354a00e602018a07600b0a540d12020300136244201104041541000c1c030440ca100c02d900500e1240c00c15500d4131582e0707100701103030514601e8500107046031401e0200c586800e448081401c480718141c412041d115003007900080800002000740c4000381e02c0c08510340092520720f091007a06080d0f00c615034040286401000022034800c00c010000d41110840c21045824030f20300050003010010030040c1405405009000c241e6400812207031481e01c0701003564982001841c0582841c140b913980c0440f468207020500044c40321040050138900304800848001004958890446840445800300070501c0c80540e80e01180030013682c00142d01d0005c09a9202c110500c80b151314102c0c058200e03100007582e80c0100039034101040d1800014404426 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 828364910 1250 828363660 828363667
    0x7060c02091303030b061b190206030408090112050406051e070c1b030503040621050103121b061b0e030f0c01120902090a022505030a0f0207030203121e 67
    0x1004101e22060203071401410031102980841894403944c0301403402d06004128130354840748102c507600c0340c3c0c05d6840d40081501500183e0034910034502d200d50206680a401d017410b40c0d0702c54030f54410a0300a00502410f01c41503180061841c885032040178421407040c84000780a042040000640c0c031401031600c40354000101c1170025145e040340051841c5581301e059003412214402d0325104e00481584001d08500c0f0205001c940640c011200211312020543c50704801164a2106401e0350020301c4060920a0b070320301d401c0da042d4030414120018010401e880d80d90100e1700d595581c22940b8070b03058211040700c07011900d61159400115141c203607004400510741002e00b15403064071900c00120039810302c2580d44120a80300119084890015002060301a843c901803021502075842043d4a48038000c41d510305041405c107585c0e00c0705c0c1c0c00f50000c0056041558245042e5070f00300c10030300b440042d481000c2001006030781c1000b0070356150507214001ca441d81001103e074104001e100c4001d170000304060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 828366160 1250 828364910 828364913
    0x30501170607121a120133090e0c1f0f08270f0105040503120606211b0c0102040306151212030e0f0a021306050d0224160507060c 57
    0x6440c110701d800c0f8a030703001a0304012003e011046140d00c1060135000241d64500190030117042d03101480180411304403100d10765580f41e103a00000f008101024114a07400c0041c030040e20958000d076052442c06003214901207100d00043c0040f94820400b15000d80100c83d08603909501c006541c6c00c200b01741c01c1450a03800c04540c500001c0c00b0380815510780e10181c0e07a81544000d81040a400700200c200001c120500b03107070801544a81c407600740d003c400600400071880c107041140446040d01c280c6080c400211161060240f00c200c0c010309900c4504100070091400821b50301d00400b59401103100040e40c461030f501d404d0007a81d500048200703620781c54503010003102000c5903200d030030070b5480a6813444a2100d071030281d000f04000786100c00b01d48207a10b17101081150018900310110b00850b4102404091403c456041e40c01c14043c4a4001000e8030790180141031200850312580c868020b0504c0448030381c0c503803800f650007420300c0c850440c41c503140050502a0a22487c0098070381440c19080701c1d000f6 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 828367410 1250 828366160 828366167
    0x60a0605040c1419032301060201060501051606050c0d1104140a030213050901020f03011203120c052205030a0309030b0903130302060702181006113415030501170607 73
    0x600448203400c0919040c0c08901505ca94051284020039008030116004078086106e0b55103005d005100c055840c003000801e00b98010b00076140c46082038044e12404c50159a00e04019010107002203580c01ca080c0404c5020f004c850245070030400c40300301e065407190310300120f004607265004403c6005080c1c43d01d0500250300c40c0d46200003140100c18020840f5107800f0b2800f0f009100301c2c0108604060040004911b1959040410204030300a40e01e224400c28003100040841e400d402c5100c01144041020890580782a0700340c6003010007004100210300d81d1000441c0c00d086d1648001c50000d50125014020459040d00b01a0080c4280004605001840f00504480041e80c00081e220b92000b0502c0000c56403495026030890682d80002c22960400804100031401240036810101c0e14000c0b030705000b0400013990455000004840400f45481600c40320f02902c481c2021040000782d40d072012510f208100030309407025030580d0300003516614102e9019200100500c1001b065000007003480b141c03030703407 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 828368660 1250 828367410 828367417
    0x1703220503030714070302061b01050a05070219020607171b12040509220b15010503220f12200f06060108090a1a0406060e07020d0c0311060a0605040c14 67
    0x40c030160421228140b0041545000b4040e40300a500c02342c006000784201c201001e4481c45040e80c0d030f00034051a00c402d120348042d24411540d5000580c0008642140c4008510f046040b550018060528100450b20f0b6500d4490076400011080d03d00000c070307681100900c0d00f003510320403c2d80e000b030900200c002000f10500e1040b40300f00d501c0303401c50101207842a140130201e078480343e600641401102805140c030000401c011038a004850a005542d089294016000c43e44070701c10780402d025030765150760480510390415440940301c0c19910011071001a1047c0890f0129400c96103d91181c20303140c502c2c00c500f850710300003200029006031007501d03075074940002d1181e00302100f403c11501940d21080001d04c1c242c480d00001c2d086810503800c2c008904054050f66028a001d07c0b400d10906860319009465094240c4003040143e004000201220388030340442c0d40792602c240741c0541c1c1108981403513851b00005440560b480e9035501c00810061030107114007009504241004001801e81802e031b06400d01 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 828369910 1250 828368660 828368663
    0x32070905060a2102030c0f1c030e0303070501090b0604090b1b0c07090b120a0b07082d0a14010f0605070c030206031806010518190617032205030307 65
    0x1911036020440607a90386a07820040d041c0f140805006500d0440b29040900d200c01060b4080d000b2a0000b01450510300101203005101034442d05d50200f50703003007148400714106d201381c04124000d015030f0025601400200095402080042080101420301c0a450800a0502c1c0d20842c54001240c0000d0b04400c4050fa110507a103042c0b40c281050304a020605e481185a1642903008480c40842d058019a00200c4098001e80e5404039030b10005009990b6001072400280200130090f0019070310600ca8244d4550100c4850621342c032030922a10150283e040ca007560107440710826041145040c10361254085482200c00004c2c071039454002950301c240f005000d1101000400142042806500a120710040d94090103199491a0584800c405036005001003020780c003400300002607038680f10036504190114251250200e0722501074041c9507414240c1c01e00c500b603855010020b800c514080081e0b041184000103165280c3d03040c509600341c1030345030f00102000c41c4036000922880e00c001082d02c52030b6 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 828371160 1250 828369910 828369929
    0x5070309150e0a2f18060d08070236160e12060a06080f0c10120b030706020c0a091104091523011103070b04060b040212043207 56
    0x110348680d4442c00c0503003046014140a1455401100d9a0001c0083c85000c0d080d040b403d5000030551801c00001380c4d600080c84491040001c081b50392842c1801c900401380313100312445407506480e5808504020b0391100019031941c100c40c48205c1215242031105495140c0803040b07802480e001c084001c503081120b41c0c00c010060004410070f480e480302c80c8180703580741c0250100c844901d001000240034003a603000705840c5000d008929403c0340c20000d01c510f4101c1004000700740015500000306d64038030b480f0ad450240c03e5268040b60410351001d01c5100040c06081c1e0141c039407245140d003802040240d66221412591070719444801c200440000e0f2070a4440410300450114145200916900701d030b6041440340301c1074040d001d540401035080400c45a0700a80365020240c030040f8405480e80107800f4090078003000a00040d00080b81c9600c04202024018001421301c804407501d040002c41c2280c0488410340c0c1903a10024050040700803110250300c12034070099100042c180151504039610444004 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 828372410 1250 828371160 828371171
    0x120912050f220f050d110f0402040915051504060c0605130c08030c01050c0a02031803010e0706080a060b0a050f1312080a0e010807140f1b0703060507030915 69
    0xe540c800d0122610303160103400320b203042c04401980300ca2207101c40c8942c034403507002180005181d00b4201441c0381040e0f04860080400e002400500550952524460741d100307034201b0020440f00014403d4101c4074052100d0f40c80b480d803d01003408000b0043c0c80c403030300704040d080c0010800d0b070b40d21401201e101c2e50300800224a640b15510f88061001c40050300811100308500f000c1442c003c0000607107441130300c06000b48602d8851900030b031300740d1007111240301c01608100034076451601a1084500b10700b40140000032600d44004080d828002550480720000c4c1d9802c1c00c1c050740000038051040074110903100d182c42c0c00c901c100c0107001740c0700d5802c25031007044c030124884035010f05143d1038200a02428450006404003458a64a0355000c1010310000c0792280c40400155407080011620039403031911500c0c1006084400a90ba40c0c11800c22510714080070829031840700d80d440b00d80c2030201e14241c020f00009041d0303d008015a94020a503504241c40c121081c008541c070304600710700d03081c00c0c00c000086 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 828373660 1250 828372410 828372427
    0x18030206070807020301021216030504110f030f120705010b0307210809030303070c020415061b230a0506130b0a051e1611070e0f1003120507020112091205 68
    0x8843c011a440a5815440424010780103441d016655109809042d80011176651088044d000c80354203541c09400c02041c0710071a029030030202c0301308508903801011134108010b48015180b41c008528080d10b030425003c22014100402402112187c020460240404070f081c018100e2508409010f40c040c1580d4101804003800f149000701d800342d40028040c1e070303520300e0650005000c200100b4800c81c01245003400300c1c500080d1030b012170416211117a50319240c404950b28680d295107a0b441080e10554281c46480507400510011000380c00c84250280c450141e0504029040500c000d1092403a0741d50000c0c0d000000e0050140ca0344e000341c04040c0002d903522210003a08094290010b43e2100b0011b000c00e0140c00c01c060400c114000030103907a03d01412100400d070f03e45880c45840381e003203c206420702040c5011003600c1c43c80c3c1d00c400030011400d90b081d640e07191035000415442c2003201080c070008020056582c0410340408100312000c1c144240030a5035101021440d01400300d008110340400e0001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 828374910 1250 828373660 828373673
    0xd0f1b05250f1a010f0e09060f0c0d06030b18030406020303010515120a060806070203070206030a0513080a0c032c150409060b090901060f0f0305070c0c060e01020c011803020607 78
    0x1080c1d680148a0394044001c000c1c3e0701c8550902070086400000145400181a4140c0044903202d08103040140c95075850300e2440c01e900b01400f800032410034105101014914a21348500e100940c0110711024540c1412043e003041a82d14141d80b4100b50400c000501c0348540004c00c4a04490040c0c42a0148a0705165183d02c3c070300522550b140b00e1303040304c400d00c2030350b01860300000c01f030740c1e03115060398241d07183e02206a950313100d8444000c1d04442e0074000600e200d05a9030045600100281240e00310400307a50703407802c00d540240c200f0340104040000c0310060592002072030030010300f421a010225517641104150042d0b111240910403d2411280c0b600e03444103109913002026403400600005071500800e20f419080400400c2c0900f1900c800000c0791071141004400040b5203481d88034055103100d10880140100520180c28449200e191400295401c0c1c00d100003081180d44185525001100080c241a00d10b6031480c1008107034912800501c0044d03c20744200c0e54115a81603070f82aa528080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 828376160 1250 828374910 828374933
    0x803060415090504110a180510030602190e010f141c0f0204140901141207030209040303050105010224070522080609060a110403060903050d0f1b0525 66
    0x106200700c03901800156001407a08594084c80c410f01c40450741c018100244440c00840740b117124640840030404a41203c1107500c6540c00000006032007914603101c0d192102039a01c4548841700f8460840001c0f0550382d44254007410031f20003480e01e000041d554280003000715903d034624084200b4001014101c18240340d2403030440030002e000030b00445102c11180b10082d080340c405c1d040d5104410f1f204005c140f1f44110081e060b5118040c1c80a03111301032109105c03414102c40a540810b108082010002da515248114801c030321a60f0049a5981088002800d11110103119800054089101e020041110711010790000940c0741803500c41a007100c000c00c040440c9102c4a8080c0c0c42900003050400010841511034400c61007255007640703a02d00440100c0d010448030f005845418001030000a4641c2c03c0310344824060302e03105061407020a000d508890030b80c0024491a030341c03069041b12606801507254003404490130840d0500a08000c10199a140d14003281309400716907400004021403950380 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 828377410 1250 828376160 828376181
    0x30305150901080c0109080f1020040308040f06232a01021306020613063c0e0a1a0c0403080a120510031e1110030501090507050307090308030604 64
    0x901400c2c1d41c1d281e07040b03502d07031801e092081e0020307a00e44000300303000c0030010f0700c2d103940c5041d50000c0205598007425240140110340040100b01d0640c00d01c1103d00e80202d01500285024406081d0380307034904460b02c0400440d0390f024000740302200c06a0010b0302032410590a8400034800c1a0795502c14403941e903452007842d0a01012a07140210b1400e1495005602428003410b6a800700d8100a440301d200741d0741c419003220041c1b910040e9404103000140e030341c1c000d2145c881003941c0e01c0d005d132550413007601c4041c421321085031f075003001e0740d00060125400c500840c081d1614910180141128580720b105085040c54001c00b215803000700410a82c001d1b18003102c00841c0c01050079a242c60100c0310040000360b1040680c0c05560400000c078040e0000030000e01d0890b40c5c4520340c02100902119100d0f0301e48221542560440449460321400e910740046038450302c400703540d000900d581401c2d0900c1c110303103014041804120b002e03c10811081e401c100d008041d2a0010b907900d403030343e4034070700014041c2041180 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 828378660 1250 828377410 828377419
    0x2101a030a050133090f020904020301080f07050603070e060f0d02030408030103061a0a1809060e0a05060a0e070e190c080712050f0610090312091703031303030515 72
    0x50710705014040d8055001c90403c281c442507403500d4030060342001e403035441d8200054807880904000d00204c0e98800040440c0c40c0c3c0300903042004260004040b03030402d90000d030b120b40180c07969026001c1c0c14043c000c040c0c07500302c522030b0441c00d1414000740348604034a903080c020030001441020303941070201590012100050150f540e40ba103403600c680c16820a1204498040c18612828544c80001800d0f00c0d81d6200540000000351030030600340e2000031108440c018a5a480003484080754040c0a1240040940001482c0d410039a1400e13502e41031008003508030003840e1100000d0700c5034011504601300c40c0303214000c603040d0b15405180d1903442413103105403031a00e00e04400b03421a55044071203a4452a250303155480681c0b06418454155101291490729428100000841e6072425130110b021140e43d07803411010140e01e03a660100507010702170300f1401003000b0074420406034610700c1a1401005200c1f020b14210b00709030008c0703d500900344c08020141030f21000040d4600c409030a031481c401c403000b003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 828379910 1250 828378660 828378673
    0x1107090915111902070b0702041802090c0a14130509061305040501090b0105100206010302010810090218330d0912120c0207080c10232101030302101a03 67
    0x41003106582d2180b4000c407100e10888000f083d509001040d8101105c0e20383e9020740c80c001081d8200030003400060100304612074044000d6002d40c84d56075a203880781510001b56555100c18070300242c0070000c2820b4030484810200448285000412a0a0304840e01640c1d13400280e1640c800148417140e0094030b003440503143c08200000d01005412555819002d42a21482c03642c896051101ca910700d0085d440150380054010070055200e51801170b444021045070000c41502c0b0202c0d80266031011005040c040400750340d05003545010750195a803505821400e151200311150030f00140e22034103401001d805008190040440c00715004403078866400f0b208903100d4080e00c80054200c840880702030a030140b40918901a031400020310505494401d002090710607041070030001000039a9900c481001425100761600744c8503444001d0242c0520b921064940c5c11089001c001260503110683e440c0c4050001000840d8001c5162001e00f0400c140c042085880880042c0408101c41c01d03043d054440c85 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 828381160 1250 828379910 828379931
    0x206010b12130f031206082407031107030f090501080105090f220308060307080610060e060403020a0e10141c110918161508040311060702012007120807020f010c1205071107090915 79
    0x11220b003050b1407da45070fd0380da240c1c80c2c000444071400309014542c0c108045030085054510071866055020344400d0072403115000101e04c9030110b800320382e07048010540b04024000309140030b004601c00380541ea4014146843e00c0404500317030038480c1c840d640038404a0f841d038235280c0c1c96040841c3c001d1a0080c000341440d40e0784140010006808a40703500c00700318082c4012508445000481b084e0a100419459510940e4500f0041216544200700c61144000b12060704507200d1924a07803141203944c45490401d03440c00812402c00e483c40001440728400404e060000301c0440c0c200045c18221454145104da4407071409031151000c03408860700380d2080303408200d10240e05400c0088140c0614040c42001040301800a505000705070340280400d22210040f071003103200e401010351100f000d2045504400c010246182100d10513a6400b0015602c0c010524401d10700340078481d00400c6034a0014103800b0030286640e04c840c030501030700143c42d84811030b141c00e200b070140c40c1d11078980e906a8200a101c011 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 828382410 1250 828381160 828381167
    0x30a0809010c0e03120a05070f060e0f0105040309150c05070f0f0501030b1f051303060c030c05090d03180e0a0504050705010206010b12130f03120608240703110703 72
    0x11115000c06609168034020014801c2d24030010400c00038004202c001e85240c00e085071034006032080ca00304103042c0710700700109003448020444980203940c0050341d004101280707401c000300082c0102d62a81020103020010317034040c09000480b841c480c14640c60009814040b01c501c1075294016050b40f11307203013001c03d69082072030b030490840f01d098a43c1000d00b90b84400540030b884940c9281588605151a0801c040800e0443c8034500200e51038210300e8013030700381100d401c0450190402c0d5902661017007007002007501071044204030b0106003405030605038424002812003885040040811140700481d00018410b1040000905044904910249080240d078402800304640c01e607154030032210f0018095001040c00c5040e91300d104240d40c6024440409000304184c060000d01c1e00b0016040264041582845403804462003031380e50001080080507075600303990741c40c1c1144a05030062603480c091500003080c3d0003801c05299440b01d90b660f030382020680003041501c480c0c180740c85d80026507908041c0e1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 828383660 1250 828382410 828382427
    0x60415020607110f0a0b070c0203120403110a080a0201030b150414090c1201090b061b010b0901140f01081503070612060609050603070315150e090a0b0913050c03030a 73
    0x542d8806201c40908030f000703a52010104030910700c80d001600a50089201c1d5031a5503405580b40c2880e00156006502082c0b400c064045030202440003c10700344100310703032440d50030300300003046400113170640c04c22809075101c0c0303c0349000130305141e42c80700c002490b9102c9013503c40849051801203515550b94451862000400b042c0c2c05206100100000703030584501070940340006000b203603403903040e803d00014100415400300c1d90703036011b0000e003c400224403d1601c03d014100e0345a00102e2075240940620034441d4060b0001070700324000f80200c04664541e40c1051209034001d103003015464543c4c0d42b668140f14401c0c0307c459054041c03c840071030700c46d4000584240545220604005803a504c98048a800c50107001c0c403035105c80c0401c00f0131503c034420340119140c01c030f0344101d8402d550364032041001110a0700c0c0c6018041175060a900089252001480303030310540048043c0038145003180003030009400145a0700c1c0c950780d500841028407108100c42a8080b00c0501281d681700c1030054003414055 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 828384910 1250 828383660 828383671
    0x1b0306050a02030408071b031b0503010b03010e19021c12080702010903080c0c1c0305160201020304170c19030206060913020d060f020c16030c050307230604150206 72
    0x40c1040046150300c21648202ca02c10f64120b544181441002d0f50345060071603000c246d4001a0303400c00b2010010805644e8400305900008000c40c02d154900014982516150f6940070310a924004d21140113401c0814109507110945401d030a041644e4400549400c810012401400e01c031305040008001920906203103001064850382626990b84004a0030385000c0303203000700029507140124030000103c1c000352028000d00020b8503046010340040e100c3c150944805000040e450b2014003c605080c26072880d12042c1034070081d45945020740b54440303170700b0942c10f00c43d16901c000901c40402550138003600180c400d40c000464460300701810000c4d034400c002e898140c421100c2d003011401a01002881c0c48645502411009400c2110740301c02c4018400409130131005602048900c00c1c0c81c034184003000030b6402d006e8603a8422030031410705180c0804941c01c000c1c081e6011840602040c90484262242400141150451702a02d0004604c050285602030b12000004120b440482600441c1013440760 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 828386160 1250 828384910 828384923
    0xb07080a032909060f090916090c02070e100e15010e06040303200f0706020601080d05040b0d110d0515040509062715010605040603050601031b080a091b03 68
    0x4002c2c008240e089240c94024600311410005407001c1e2500b4040c040c540e20400c020320340c83c40b01301120046450b0043c1114085055000765611040340c03406610024042c00104000f000300c0c4035602006540c600c12405005964440180000d8407848400f0b0404054906009191414105288000b01c581d41d03101840e800300d14279945ca658203081c10300980702201c0e0181d50b140040e103170a5982c0d400003091306000d661075001c0d0340354198030100100400c8000300b410b80c3c02490150300d4106c0d1281094482c0b007440c0e04002040004009150141c001d46803403c64002d4005510100400120004c0c855121900710150402e0100001a400311f400c0702d88402043c0c030184426550b100696446004c212080a0600c44055004090106141c03a030034418110301e0031201c1c01142100c00c00180b2600b684040c002880008050104c80d5150141c036420a50a08080c0202403000b4540c005150b01921070904103e030b00c100241d4180d01c0c40d0001c01801350072038a044082182d1203c0e81c080c1d030005002c1541d40 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 828387410 1250 828386160 828386171
    0x4021f050c070510140304150614041103090c1207150e010f030507020706030207020f06220f0e0417190323060a0b070510020a02010906060e0f0c03060a0b07080a03 72
    0x35404c4c00702a081c401da00590f1080c0741082e076001140f0003504041d100792840c903000b243c0c04048054600c40d27403024120b6a4219040e0054800c00c100907141e00c8203c2c00d14400c0b00b40148140650001500c031f45c482e60454151030500f41e0045443d02d03044240d4440c0e40e0303140119005140340f6402888040c0031003000e07130315a505210141b40503820f45405032003c9005900050003007004502c01d901521190b40b0040c60344c2a01030714000080d040c0d400030184820f6845012a400b250008950303038803401004003071400302d02c0740d00d000a10b0a013120020b0014014190000900c00c08d4410002222100c074502d0310410701c403000800c0e0040c028062000400c00228152610600c07900105035220300c140780040200c0c6d090381c204a08607141e0303040710380d0484292184007040006c1c031000340060207005060741d000060f0494142000410b0b102d06034800e0000c80500d9081c00304a440c0030b40f602e0751201002240b10381e00d4845001080d007103d03080d88034810000f0b011510000b04419031004003514032056509103e03 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 828388660 1250 828387410 828387419
    0x1060e070e01031a12150906010617040c05100c020319050d030e0718090203030307030b040c111c020c030a080d14090a0312022b24090504021f050c07 66
    0x81391090b044c0c005040d07442004d10810b51034169240d420780a00841036a03040da55000070020451000c0e1007031345142c0c200700b0040c084641d100040a40d100889000c2c8040d50a00740c07614001420607020700c5024021030604864414000c07070200c01c200d1780c0a0304032403144100b0800480b9414064a044a0030300405004200d0544240a0440c0d50304028025160107031030701a0104021203c0300100c8011134448400c94013581d014405984607082644010078140e034290108422501d21002003005d012071005200d020700000a4100241000d00c0b1601500c0750484000b030b8a0321061071101c543c18441c0b2040041089081409401c00001840b014460341c2010001080e051508941007140c51303100411100c046842003a030050801d4009000602c1c1107410703014910002c1217803400101680c4d04480c0c48808500510500710108441e00d807841c042482800d01c03070b05030315051003420840b6032503002080a558421200d9022001440e0440003c8400313a807011380b960704455890303606801030800014 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 828389910 1250 828388660 828388667
    0x20307051201180f200c1c0f02012306060309010b03010501081506031b2107141201060b04050d05241b03010308122208030a0c090e0115020f01060e070e01 68
    0x4c10301c0c80e01d4101c0109030780d049603081c617541018140741358078400d0321000c0c00d6942460892038240300c903941d90014050101c400290039600c480c40c58102c030628540f000324180f12071f8170100350840c01c02c4440b1b903900d13210291035502508103034040f40c0e07142d46802d0000414031000280304410440a002c14a1159152401c241c0c43d07124508031701c15050303110040d031788003450b1014090501b07400403034034260700d0100460094541205500404121030341001581141c0c07420301d440500c1c01d401c0390024015941413481c500d410340070f10702c15140030b03461602e1b0800c20401c041c07280f100c4d03000c611400b44c4004c07071a002081c0501c0000b9600c441103241070800990880041c2d60032070341600e420480f854601341d0650441950504003c00744020101541091403100029110254185010361070150303c80c20701c052400304640303200040c9000d000c02c41e842042040e001000d0207045410f85ca4212070120010441039080081c5100120815441c0100119201c81c05e501c4080c054141303980c408520645807801075 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 828391160 1250 828389910 828389921
    0xb090918152403070311120a051f0b0a03030311090613050406080607020d050a170f04112b060b060f1e071a071101020c0f1603030c06020307051201180f 67
    0x3900f54011003070a00c00301d03d100740d000510400182c94031780c98101c0c4c0d030b010f141000030040089516030000d04c244e440145040c0c003280c0242002000411241c408040019400981844000c05041d1034007020f1484207080710986409440281055a03510704010091541c01e1a03801581d100c1d510707042010814003000200544100e095400911812804800039503d64102d00705850401c01901c0c2c0100350411a03e000034051551809180725508003450301d003910302c20402c545801a03600c8040c1c01600c036800c06040340480070203a9005c8140c41d490402602038000b1075030140c0c2100000030698046904040142464054000707211040310304c0d1140c04100d8482c0940c09412042c44550242002000440e815048021400d09005140b0050742c0242a6007203800c83d8132064210420008003908107100510304c0c07241036401401568110394000e801468040c2014042075400300000b0911406601207070040000c0002c0d2401279070b0b440aa82c0e001e54409542d00281e00d041c0380d00d00c84211880e0003031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 828392410 1250 828391160 828391231
    0xc032503091202030304050402210601031104260a050a1a0609060f030c03061006080114010207030b070216090c020c040e030405010c05100c03090317010b09091815 72
    0x12607034501d140405000c0301c840c0700041680e050004020004980d41c0e2032004000001c03020b1140208401005808035244000a11890601d42410400352240c80e1400440c0d0985d1540d90040da03220020008581a424000c26502e5261040b41a4002403100001c1c0c05d00d095441400517184000415400c40d00844080d0340d403c0c1c100700d070750002c11a00d15200318000802075024040b100c40550303071000a45468426a80311040304c22244042c068541d12844050160902c854100350442c80d40e00001d45c0c4040610010b49009141004102c50f140300340309200c1c1860f449204c0035141c82c0c07070b070b10310740000c0c80307010224000b6114031040c0180604041c040c038a03224215030003450515280c28019212861807100840740c0d80140c01044103007503403e00c40e0001d500841c1c0c0d0002107a1000b4a40070740b0b050075044120240504190040010314003560403240c8000064030608220380380c000038581009900075003940c2c10b0203429440650b085043c80c1c9184070708045001802c042004404200b03040c00c10071350 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 828393660 1250 828392410 828392417
    0x90308060924040f020c0d080105030c040b0904030804050a080309160e04030905010f02101e1410030219080303070e0114040b120417030f040b100e0f0405120c032503 73
    0xe080c59842d140d03008041200134040003525006c0d071814860b040c400307080500808200d55000600803801d04102404005e40152010014402060300061403480c0041c0b004003040700500000c0d0411a06021441c40b069009031701680702d0400f0075000342c45090f55000a0b2841d042c03048001162030020170081e019642544030740300035505040c011600d0f10804c08010040d03116656511100c04450300c5294141c1d030340c4100a0b003041103a0140c401c1500c3c007002c4200800800b40c1d0922810030000180641204e40c112640303860b5070344904580c82c280304180e0100d00c1c580408001c100c5841c1c2c1050031381100e07480982e03c1c5024240f0645d802c035100c1c0510300501d0300346141070082d6100700341c13105602d40e007060064000e0008100100c610b00300742d9004070390048000821000b40010420755628003600803800c0182021200e08218036100095802407001850751040008501444024048c01e8610015509295907c521406540303a5950050030041e480540c00c584001002242c2403a80036060f0b40b558 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 828394910 1250 828393660 828393721
    0x80103031b0c0513020408010501080a1502030702150901020a02162304060906080307050d030219030b130f09170c0c060f090d121107060f110a060903080609 69
    0x48504034000070480111021588000041116580c1c0c0d0036001c1c2c50800018050f03511401e184110303094842c180c0c054000b951020005000003518882d1034140032074070042c016201e0781c41d004200d1400750f03031040b01c00c04090240305100640506400030070280106401f180e82a4214003918088c120f0307103200d4a00c8e07a034041c800103000340e2640104414120310007440401e5682e101c0ca202c0c000c035040c960080c5c0701d507400000d1813020410f0500000701202c03070a050071030505007250104100107001d41251420556201c4c0300c0415584c503c06445440301c41c580f02000001011003503140103100100082d16554040f041c26541152004116140c1c0501030b000b8000503030391407040c001e0540041d07032035007207440f400c1c4411500780d201d098124108501402c1800001443c86001401c2c555940102c0c0c40703da0807044003400615001840d000c1d10342031b01e01e4404500900203c0907400c0c88400000201000c4c00c0015103020b0640c1b20107000c4c0240b030100d4007040ca030b85070750140c42c0b244200414010035110600 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 828396160 1250 828394910 828394937
    0x108030f090d0206040e0403080a060303020705062a100b060306060d0902060d0903020705040e010e0a03080613020c0c090f311a041e05100b030c1e1008010303 70
    0x5015000c0008042c100d55001c2c0c81c1c941c0092440d800c1500141c001c0c4d5540810401070582c0802a1600a0090342c01041800e046490080d1109014001c403805070704001008015803030041c0c40c401c40c003c0840c0aa9002c400d11031038041e1580d80810800c008641040100321013490f103003007100d01900317008100300d140000b1400b00350701900719110142ea000101780300443c06003800d40240342c071243c82980a0002d05044c60100300c110f9860542440b07550307240c5292003a05c1080040d035007100942608005a440da925000610402040030104171b07214008138000c3ca503428009440310321140c2c12108000c06980d191484060014201c4040d464001c80c04007210150480c02040a4904a0b501440b010320705192030f51410008415007000840d803100381080248089141c1c3c50011280525508003240500c2d103841c2d0b652000c0381c0140d0354455a5a109031a00c2d501000517034502100a80314503503901401b07209074101c41481c15014000e502c094000c0c00710501c92020241030701c0d40358440045242d0309 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 828397410 1250 828396160 828396187
    0x2010c0c0611070b0403180f080a032706030b0a0911070f0f0803090619020f04141f05030f060f0d3c050f060f070f03060e0c03010914010803 62
    0x2418044140e25004011400110703584c0c800c3c583c4280d0003a121209902c0c0920751654500041c0e500c0150550f02d4100113200d464008240449001e40614208000c00e860480190100b2203020540b50712005030035002401503090340002f140400e040341c2450a465561f4001e205440e540c3c01d07802100c0c5010020031000803130300300d5000c072094000c40000320244007941d2054640c0c0c1c802e0314461480d500c007600300700c40120b103050684050414107030190700f000140d568589441c01117010b0780d603001681c90700c40621520344e4004480c0d07243d8085448101c0801560f000f400316401611045107211074200001d81e2418072040c00f120b1140c0181150504400302c3c0c4441070403801008043c403903442415414004224807124050448441c20070254040903c3d1501d03619006000700700303040caa001001002500e20140302440d5001c6414103000038500b616841c00c40040c500ca230003556001034440300341700b2501031180186042e101e802c0b40c08c0184807000310303030140052003d10410f00503a00030000350b40114031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 828398660 1250 828397410 828397421
    0x60112120c110405010f0321050405041a03060a05090601140102070909260405180411060304050f010609020d06052413030b01080303040623280207050703030f02010c0c06 75
    0x444803050981ea80d00c0000c3d060318020303408002091500e900c24401e01204152000104994004400170783c4040310f40a4140e0082e4440d091045540b071a404042c2d8541c1c0616000604000b010340b0003078a0418036080c024403003034610031224441c40e030020455000c90688850301c0c000c160010b0422a01e8050030300c000e000c0d0b80c1400c0f03070103c030f141c0e0809410142501460192149868415442c1d60604003030040250400311041d22030740c0c85105010100c0c401d2030318802d0122042e26080e59a0351035041007441c2c0007018401d40c429601e40b2000184108160b03015003a03802000740140035450340c9008000107812007505840e445d00356254006040849400100183d101c1000c440040980e6600e402c99450800da20082064000000b00b2041040320312410402819050003140b800303040d42c8640b907842c0ba008042c68240c1001a0340d1401000351205020721100b000c0303005555a13021894002d03224251448101c01140c01070b003040c80224018028616100318507a1885100d0925440302005040c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 828399910 1250 828398660 828398663
    0x3010905070c0515040623040b060d021f170919060b130501140612150d14100f061a07020d02030a230303070c080d240602060112120c 59
    0x1241c0c2c00344100050060120026200a01800c3c0c425480c0505089040e2412145150742c00100c0c4680d501440d45d006c02040d82040e04031030001540e945402c04209028400c03240a58040d100301d10305900300036003801c0714224405d680d43d0f07604021408a4500c1c240130058a525000350000b2525031408440c0c5d11140000034050030003c0b52070700030800854250101841c400c20f086881c0c0005201d60038240c20350382055901601c00c01e18206914012070035030000506404040080511400e0040d603c0c80090060f45d0f40008882000790200810680e40701024090300c40c1c1c85041034501000c60b00035218800403255030071f00c141d0000720f640008100d560311200d03040341c5c41030391010f21a0240c0c508105076817050744200410b00f00b1440b410f4404905030a9041d5420040d401001004003055014000c1d50b29258455051a00c5010380c440751005030041c8860030a01f0a05910380400b2008144500c17402c641c0540c0a60301c490b62a80c0301c1400800240720090854008640b03100a014170a81c40b1142d4036 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 828401160 1250 828399910 828399917
    0xa0f080d0f03021602220c0203040e0c04030809100c050304060f0e010207030c050111100230070f1103190305100f030f0803070908010f020702120102030601120b0d0501021b0f060405030301090507 86
    0x10f03409180c030107c4400c120780200592004c0303410300198000710380c0c103030b0400911440c09042a14541d102e0406215002505005441b04140c140000b405084c8603a6103941c0b0a042d03d44070794460301e009081415400d4848009440e4181701c030301e5035002040d840c00340c81d00503492442840c1400c006488030031070406280540e128a07844841c2d090007610140c044c40300c1c0b50050011200700307106c039620100c04079003544a0144008051003c042c1c2c111030440c028442034108441030742481c0d4007050650007500420035074061340a81d0902d15a070326034070403485004030242c4440b005880e00030f5241c120895001c0105088601216500420306017009581d01802a01d40540b5094841200c40c3c25074038080b03140d01c04c458000c94413008602c0c002c01c2d1403020581c400000c40c110302d80500020000c12491b0000350b089035a900c0003109a480704440c40d004160080025580c5d080000001c01c0c01c10014060f050710b5004145130101031180c08a0b50500803038002c0015400c6d030b402c00840c03000500c8050581c03400d0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 828402410 1250 828401160 828401209
    0xf080a081e010b0c0c0306090d09051e040b04020702060d050a0e0c150c01060f0b03010614180d050c03011802040605150304140a0f0803070e04060617060a0f080d0f03021602 76
    0x61b950100481441040301401400c5402a8058040e220078855040f951144411002224540200140108108a08a8011401c2c11250022030000d1140c140043d41040002500d03203011406900450700490f05c1c0036003000348102480c00786e0380f070781d480020169100c0f0441e4201101c4115820140803180c094200020305256103d003011201c40301d940c0714881161001c0010030007150420219210300005421061806824121100403000410406886060700c4402c2c5e8041c00f00400100d40400e02c0130300200409905040403851910f00150228400c0e0f0a00202103841e003448150659000300c1c4031515401d58680d50b4491100c60914400051030303103d201c0c0c2d2100403500c80d107002c642060003030104540d00c1c2046a401071003e0520f900e40fa0040703040a508002c2a980090800940b8400c080c1440b000e45469002551103c8158480995545241e201151442001c2040851507065441d005004918000283d0980c0112220142542154005140581402c0c84510f40c42003145140303600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 828403660 1250 828402410 828402433
    0x71517040219080a1101020606150714060702030c011506170a090b0c030a0507030501030c0b0f0903010e0f070609060e0f01050d050709170303040525030f080a081e010b0c 75
    0x140b4103040d600c00300480e840b815140040c000d0f0700070040c125400a01c003500b054030b80721000c21048441c83c42100c00c01c90000500381c05020500e0b0b080e08050500005071544d070300741400025030b06d4018083c0300c0300740d503c0c1014a01850031900041411500c80b600d95030b40d00316910710b085041080040c042e241c02ca03144c40c030700310002c0c15016400b03100320110102991642015128501120300c0141100141890000144041407080050100b110582e0940503914901c2d042505107501a000311141c1541c282800c108002101040001c1a08039500403122110343c0d4150440b02c074074032441580042154030440c90f4650414020284aa0806050003407908410b506840115281200d200c6d0000d4840003062140c8041c1d0b124090010032060001c605500346522100c0e01d0310b10713031103114440e1500040c140307900c003120640090045406c01c0c000d5034a408a428020301550240580c407000900340303000100141484524603042040240fa28001c0340e09210701501c540d44402003100303540c0300301c404845 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 828404910 1250 828403660 828403699
    0x905090417210406050a14040c231809011506050a0509040603080a031a0406061b03030b060720040608030909090c04020417010c0f0512041e030807020715170402 71
    0x14000c3e4420b003400122460711031039a9003120b04c60415402c61904881c01d01c030118000e19005002d603404440b070001e90505081031459901076400c0003540040740141c0840d0f45044140041e03101d410201c00074404603850110156070014540286c0b0041f034001d0100a11480c800c8015102404010304006100c1351079072103000c3c00b6007145060100282d00e5041007100c040301c2201c1c142e00c0c81010768050220710b04042028141c140110451409410200c00744000e1620941218020607005010943e0f184418100305030214510b000c1c0c0d2a043c080441000402d0900d88116011141c5840241d410404c3d40400c00c060220301811018840c8160307070070072216a403184014001400241e400010600045c84514251001d003003540e42480b000c0c0f420803100d55007203c115801060506685c01c107941d5030f498894420170700c1154010442183e482e00501709500001e009004240035021151502c0d5150076102c0200d00202220001890090b0000c02e00da90684615400c1880149007030380e11841015200c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 828406160 1250 828404910 828404977
    0x60f12050c0703090608060607080d02040f0e0403030e0a030f0323011206060e010609120503041a09120a0521090d06061806030807021002160603050105010905090417 73
    0x4164880001a0ba03000c040d04424014020655420244110300d01140000c580d4040d1500141208900164002c1c050585d5412140604010024503440f08d440d1614044010f03012241280403d140c903118080103180042c000e10456450b5135250300480d242e100841c0039041c60086810030a4003c140210380143e00c404050181001c00c84005899600303060210960707000b58010f80c140c01c0c0c1c10006100d1503501ca0304000c25502030b08148204507035240b03842c80c47c41c4650b51200450840f20301e10b018140d140c2d04001c00c070b250310403111081103901414105403140e40808008016601034611080c2502c2010342924415134109011410222080d010510006c0e803614110b4003950b40c0c100501c0058094213441c141c514041e10308001d95421551008941c1c800c584002c0c1c07084410040c40b41c3e03001c1c401c01c904a8025140800503541590340c080c0074018000c01e00455001c071b02e001c40003040b03508049101320321a5800070542101081c840014052a501548108900d02405020201d4100c0440c0c3c10 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 828407410 1250 828406160 828406171
    0x101b02030f0d030c1103041e0801020a0e0a152109170415021b040b040603152007020109120305040305030318010609061211010509042d02090a060f1205 67
    0xd0119290b582200808075100f03095450140032111641c003004070000015981620520940c080c90250340c540d1040740d040407a4020303046580000380140b600366024000c2000e28009584c00c04405455028500b4060520701810000407080007494090056004014501b12803410700003c401040340c40d802d036a880301510341c2c44101d01c0010200702070200104000200ca0261000d028060070317000000111035003240c84a4030851300c4241e5028960b642c0e5210400455003d0074810780106a0301030140501066a00d80c4038039045011440025180c140032601071035416518100054140a101502060710745c000b5800c00009010210004400700001c60040e049022100288040c1d08451070070340c2c0b42ca8120a0344241440401c01043e41c0da080d4004510341e206a40021000510300102c89500604030f01a81c414140720380c61103080b181c080404c2c54000d42041c2c2031a40d1603070405140c2039101d14070b00ca40d00001e000c01c080011500c0b80c3e00c0d0b404c80d520301d4585215003420060b5071781e05840b4143d84 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 828408660 1250 828407410 828407413
    0x60e0f060d0221031b060f04060903050d05010303121b050702091302120a0b06032a01023d050103050c0d0305120f010e060d051009030507080310180506101b02030f 72
    0xc0c59005c000300800007150307400039100200810300d000c0344440301c1110048c10040c056919400400c0415001c1d00c292500b101e080b074010011507940741002001007001c9200d911045247c60b10a4201c0881000304244503203c030b4569615210550b800d01002000081c4070105680940420600603544c1c9014040e2904480004044011003800c0007a2802c40260015200b50301164407040395120026041005040c04140c0345c00d0480c0100c0103074249541c0b0003c802028102d41c1d00100c0080301c00c540c05550754192441360220b040215410401c40d8030a00001c0d02c1e9a00c6100e03003552500d007012501d000a407180c41c101c0d041801d00000b0218000f0261b42c0b0311b0910000c0030050148881d422402030740114116281d845406240e00d5a44d19040c4010482d510551034845070700c14140688201c600c119480300b6990b80c1d901d00007401903007413425402244045014544210703183c01b01ea00846001d890001c20b0002d91005207041602c26100103c0881d0341e00040141c14009a07400f8090014022518030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 828409910 1250 828408660 828408667
    0x8031801030e2e02190f030b1002100f230c0f0414120d0c02091806041109102312030c010506010806101718100f060e0f060d022103 58
    0x60790100c1c52100b0f40c444900b41072040c0040d0b581d00c21311400c1c2e1141303484141885080d011504070210080c0c0818130302c2c50740040814501c10b1109600080c000035000f04a05c040105020f06e1104909079840f0f001c0140c032054100b80312461408110f9401c64001c047c2c18141031078a0700c8102d5001d0740e500150b11105031a6031441c0e130440c0e9810f00164018a000b04c7c100640a459200400a0408070b00800040d0184807400e00080c200e4894140f0000d01440c0801111010300d800e2401c03144600e03002a10320701031075006d008150200c4481d00c2c05801e68007101e02030408541484010340c1907154a031181c1e40d010410402000380594244010180344501e0800880e00349840f80024241c1070006c2c207110f004d6030076045c034581004c0e03020407000071022071030440745510385500300c480c6441c540da0801460180101c01c403c0a407504298000e043e6540608024004251b646142310309068085030001050342070100040c40c507151286900c00210310040a01a02c0981481c000030041883c0040f803103640d0000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 828411160 1250 828409910 828409963
    0x102030f0a18031124031323030d06050d0507030b0a1b110106060806060d0e0a020301180309050315070e01090b0414120a0203030901050f07120c060e0708031801030e 73
    0x8042e459a41039101000c0b4007264a410108071b80300041c4101e540c5140c03644141c00b000060303042d804070514800d6949490317140c5d084185441742d002580b0a50681e10300300c0e00290500b0001030700d143c410341043c0a40f090764503503124001c07c441c0090074180361542e5001441e040840c407401002581c1c1c496a212400790305100401800c454107030b0444800c1c4108441000030f556184001c441400040c00c4001c50200384001c0c141d0b14000d41007030002e52650801841020014156002603207950003965650045d070307034a00c240342d01d40819103504130002400a00080d0401e02501d6054072103241031401041d5280d0320414101039030080e8008a07021001020103400c0341c134195008001c0b41c840e81d400b8010104180c1d001942c2c07807042c140f42034140000414142040c007a0341054541c09a08078484414621020700010510840404200c40e003074904203814400b028002070b2a002d540c03000e0010341c508080b0180c00c40e00032042210442c1010344900e00c030f5450403030602c80b8141002d0101444004658070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 828412410 1250 828411160 828411169
    0x80106020c03061b0a020a0c03061e15030611090901030308010512070803030708042141030603011118030c031507120906020309100c030b0102030f0a180311 69
    0x107034000c0d18826800302040c0940201007800800094112807100e5903205105481a410001c009901400f0010300181c0003040c04445d030801c0f04111401c4400300d03010300b040107410301102d5a8412001528500c0c0c034040c40001c409502c00100e01000842190400c49000005a4807031400d0300100d001401c401e004004d141000140a055031580364080c02e0501e040c140c14582e24003000700740804000880000c1010b000f52690024000001d450701c907000d80400320720140143c0c68004404115241200040903540c4141c0040b80c400215101d582180c82c140da2001741c015000a42555499562500315200180b9000020308000c0c0034496400b5a00c0c0e1404109030609046441c418002d400a003880b60b42c19004050045e8094020f082804000191101140080c044904010500707072000044c490406400944500c0303114040e07506021240d812403044050390400300740302e80580e0040c0000d02c0c000b5641340144c611840c8500d0b10b00f034486221407800422001e00e91003504c40403001c02013503000b03080 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 828413660 1250 828412410 828412423
    0x303020706240b090607060f0b12010e070b071a1f1403070608250315060206190e0a03030e28030f0207050a090b0a180b090105090f071d0a0608010602 66
    0x1070140d0305280395080405c18030b12440308001c02c0300da507072800b1711111070180d44004030649000e081e290710032101240c458001c0104040f040380a100740080050084a02c8003118007242e48004550074810b0108000c14088030701a041025050030461802c89c0c1031a0b1000c102c0041c40081c5660740c40c0e03600c40c010300d403c280d4550042010485602c08000314801d2081000004d42224202ea000c03058002100300c006161200d05140c44a021001c006081540069000e010707400780d61100386070700502c0a03544100e03501a610101c080c1c12002200000c03d000e9400854a40760800a0303c118969a05002d0008100c05801c0030030901b58100c00014035170302500c07010b04506540000e120171410000020340026291183c8980c1c581c03150440307140c6444020140d00100142241e0140042042c080c2c980a4600e008040e802060030b01c0000585181c0140c8603405104581c802040d25258998201c0c0e411800488141c00300d00a008411301c192214003000c00108001e0b07403880d0095040560081c28042d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 828414910 1250 828413660 828413669
    0x3040e0609070e0d0f0b04080417010c080c1b12280c1203020c06070906020c010509060f1e1903050702010e2e0608160803040e0a09030302070624 64
    0x10810703080148043e04484a5800c0720340c211100a1800c4035482c09840c4a0903841c40142042d07880004d0108119041d000ba10a4400250039110b49071203008509007211240e90340b44c0d00181940001c5400c04201900410b2440b003881210f00d003e140038403002c0e103440807856000940031400a240d091050384030092185108140c0045103440c1c5080e04028020045d020000d0300701c0101c4184181c82034000d904542c4040d1800c002d444007882c11034805409100540b24600c098000c55261111030762003101120320186c0001c0106060500002e5070003050b800072000102c41c070b14a0419038804290804c040c200d0b00d65450905500800c45030f400806482015201a05584c180101615600c0003c00e0107107210903151844103240d0180c030035046508141c440d504103400e10705280480c90400100d511590210a4802000400d40d18042541e0720700c154450810406550f0000c240c8580060f00400202c1b4004e140c090b08088290f16000b04403403c40a0f0b07071028034020611041528070550740070b0b0080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 828416160 1250 828414910 828414919
    0xc0105040317030a091506050906030111030f130218011d0106020a021509120604061409060c0705070b0d0f0f110f0306030a0503040305030a020f0105011d06010207031403040e06 78
    0x18510b99074070b145041c040941c0904003401100046580035a0341c0554060780d084000c0c4c2e00010303509611100244a117000c0d1501071014000020480e0030140106040d428241311024590380e200e0791101121900982201038000791403d90802503664000c0380c900d0b20740200710514440d454a0080c2e4220003207405941e40c0e601500004100d8142c000c10203421194060341d1a52540101e0b44054603144a540c4d1101c1c0d01c1001c1c28200c84008900045091160344907040030480d4254006c20141200c40c129901d0205a000100094540d03c450018100d907500c074000b04d80b010307919076001100c40d82003c4001e204203951040200d240e0300d03070350203242140c2010010421203520030300b800c660070380301e440200c0340a27507400408140720341c0f0100122070300160004103a0b074850303450340780c410380320b0b400000e54200500c02d816101c80322000c107115245c1290b22441c4154824540340d601742c810100c00800403819070060800000c0460725041c04d15682102d10005580d0311800c0600d020340303640000d82901c0c003c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 828417266 1106 828416160 828416167
    0x901060e06040e07030311100507030f18050c0607050a050a0305070212070e040f1406280908030a090c0b070c030204060816140a08010204170c0105 65
    0x80d200680103058150315035104000507a0703111551107407580c01c503400810000b8022900d084800c0c2c1c0000030b4484a5403103003035520440d041116140046611010b03410640c104520a03020100e00034019294000c1e1552034042d61960000c0c0703094060310f000141d46060000400c03201c1c200c2540034040300c805010740e15005216402a141c101d01400101c200c00003000804180e00d401d4844c40541c0035800e07590347e03c60b0324007009144d005481042080c10881c020b02c2e81400f131113114000800d0710000600c030070410305051400e0844290310f00c5103003045490001c1c4c010310840e07801c00c000384804161140142000c00841d501a44114014030700010240104462181c18000f141d008860030800d6641e0780c000203441d21010020f1602880518bd006e100c018411680440c1c0e0300e1012b041241140d454002c99800ca0340300d9004a0a201e28064a100c54942d00f004140f5801c103081c0b0b0094203 = true := by decide +kernel

theorem cover : BRFrame.Cov 828237410 828417266 := by
  have h0 := BRFrame.cov_init 828237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 828237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 828237410 ≤ n) (h2 : n < 828417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
