-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4051
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:25:43.329978+00:00
-- url     : https://prove2.me/submissions/c04f5f7a-c736-4428-b69d-18d28d8fafd1

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 728417266 ≤ n < 728597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 728418516 1250 728417266 728417279
    0x30c0909030e06031506071103250b0f03061212040306090c050f01080a0903210920031b01032c1b030307020d080c2a18070c02311107030207 62
    0x50035507c0d0044403030303a980b00c0703408011034108951010380321445080708455010341c6c0307555900c00c802441c1d00b100251a1901c07c1c00039409074000501030798032030070a8205c005807a000400081410340c001d141c1303440d07440380e13249003200c0244003034441110300250703039000040e461400c40c0144051074010f031200c85180c0d803290010801003a03407040880030310454428a5040040b0001c030340303154030800c0a000944001c0d40c10840024801e41000250000040c41c0c0301c2c0542c0c80125402c03080c03030b0791402124005480d003001640600386811718880086000082101f99010802c01120300800080a03241d080e00a0401001100000080150194400c100d40001030604944120340b850040301424180b40742d000f425401c00d6a00c000c2081c200c2094038080c013809030400095600703868115841da02122407030780c0c88030200f6402002e190900444a030100291740716002c09181000300d14030b442140341c0085020b0b49000040c445d00c1c16409180c2044019031490460031500c0c0690903800a200c0c040c640304 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 728419766 1250 728418516 728418529
    0x20f04090609150c09150504420f082a070206030f040c0e1902160f030305160c0f020609210c1224060406030c0909030e060315 56
    0x10001c40d41181e82d90750316030118164085100002480d2480403d900d42030090003481080710760890822100031608186016800408460031100040b81c03120000300c01d590820044907120104c40599448000041d58180d01050020000c50030303a00d8549104446590032100c800c0201e4034250105d0307041c00800203000441186100364000c10180317515044240e8003003030340740c0c00584044805d10b28110501c01007010f24400d20001e041010318000742441c0500300512000201c6003508401a400203c42401490020426140c00e400c0301183c17000410342e2a00500400048032050040c803040c0b04883c100503ca0700e900c1d00700360b801c81e031303c60190426070f000c1014650012900c2c0741d120340300c100d102c5061406900858565040300c0e002e000c8041c0c1e204148040e405075125449001d0304a81c45000d0000d10751030124016110100c0303e40d00c0340e552580410300500107500050030300d0022500c005544180c5801150469109030740e16581c0c021400180080ba0105440440d0008440d101c0e511042c00d001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 728421016 1250 728419766 728419781
    0xc0108041119030f02041811010302090a330c0305071101210606020706050a170c13091a030304030f0b07030603020d03080f060a1203050705070305060106021c050403020f04 76
    0x7003403094202c40100d900d412402140d4803ca03900c4032100c40900640c50207125028081858074050b5100c5103d0380c3d20070410003010401036050560114403a41c2c03d8840340c100390007034200300341404110b0441030072444d4040f80e184074001c00801c080117100c1c2094402e907050000a41d16495650601c0300640c1c0b0420f43d0a500c0e405ca44c1004011118505540ca4a4600e4135425140c408000b800740c0c20440000e04000b9150071240130312008001d01c050443c0d0042200456040c854144410b6442e1100001c80d680304100ca50300c8100d005401c00304659205038804003147c410070200d80c00c04000501031588a028512000c0e160014881c0c2400220781800b403125440803180c500042c0b0191240d00003807080e01c0205050f400150f0300300c2048602040032020a40005c801c6421b45400341c504500070a140345d0390780e4011f040041c0400c00004000c03040100c0000f0319888019580705e981c48050084d62540c258682c4000759403003d456001d06801070701143c0540c0d401804460300e602d845014080a03242c84c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 728422266 1250 728421016 728421019
    0x140708211c06170106090c051623070519060804140f031201090515060301090e010b030708150f0f060103050408190810050402090603012105160e090c01080411 70
    0x441800742540d41080c440c58016214050014007201d45660700c440c216021900a031505030b24188004072096013100075501b80414240e0395080054140c64907906140710310480700340f43c400c0c0c0312800007003180c049445020340b01c0503200400860a0070700b40c01c05510702c9204100104c1c05e0300c000303c0c0c0400d006003080d4407031504510440e006550300d00e000501d10341c8004901180304580c44c00601500b5400c0c0142c1d50072080050700050071105e544c00280c010700c0184112041559601074800e8000e01c00e40020b0440700b0700405540503103555511403500c0d000c002c41d005c4c00c4404821b0010701e010b0761124072240180c01e019410b4040350b80340030064000301400780c4244c564100520029031f6008542c1d24007015455541e4031341c0c00d1400c00c0000c0610303c107103980165100e54018410078845407607000681e4111014440f041000501c1c0d400c0c41c40f10849680e030040c145001e41d0b01401c448042d1002c0c84011146251550b140c80d42c2da104500b921640d203920002d0000343c00d40d0120303004c40c11451782000d50b200c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 728423516 1250 728422266 728422297
    0x3603010504080f07050a0507120b0f04020a06031e02031303030b030a030203031f180b10020f15070c020a08030c0c01030b010c0b071404090f1a0a0605220314070821 72
    0x2c094036400e01c3d1450907805040b2132407000c034034401042b20314801c031030300550b0089844015003030640c00940e2a140718080c07401050390700c0c0c0840f00610340b01509469000300103d000c641d2401c0190403040c8220a00c0c0c0f0560103e4140f91504482e4200041c40e01c01080d0190301450070f6440d003150948500303104160708901041c0c2c0c1240420540d202907802807000069180020b503450071002070002c410741c4004001c0664001d000d50041c4400003140c0341382c400ca555031480380e855031448030650301e848640d080650041d81c2c4c14808241c1460010080c00c0001010040395072400d0500011000c0d140d441c8040d44c00503280210a800207400250700c5c81d0008070900b44403240505115035442c15400a82c000043d264a41074404c1400c0c00d1842004268083c0b1205c03d40740001d000003140c0c1218030b52040800304030001410f80f85220b0340c05c20004804803e0070045c114207540c0e0900848414550800483d5402801030003e0309035000924104000d0186400800070304010516010ba85c00501c0c050701c0258 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 728424766 1250 728423516 728423533
    0x50a02151303170d050c090102060106050f0a030b0d0503160b0a2c0a060c03140604020a0e0915180f101503090206120106020f10060e150102033603010504080f0705 72
    0x1070682c005d0310321420004100302d8070303002c0400009203004010792104003804020420600e1214204085a034013595605003c00c5002614010681c1601c3c1c19001034803500001c10552104400d0f1a02c6280050044941a2554075030000d0f41040301c00d10b0700b1500084e1141c03041c241c0c90355110041e040c0c04000b590300b07030707046540c5644032803041c1c40d24646a0400266100d030f0003140345560411f0030b40c015201341c800b1800c1001204015014007006440c051285402a0000d00000c0705290030700b1429402130408444800002550650000e00390b490301c1c0418003140c00502010190420001298522003440402c5c0c414180300303038000d0403440c006030b07000390303003044580c106006a0002c2ca00030a142d600034003501d80035a000a007060114401c07516101e003041000c001000318000819000403241c203035440200c0c803020060b46035100d259036038080d81ea80c62118083d05503520902a007900700ca0700070100c001e11550105070803148100c800a210b05c1080c462404c3d92074000014200b0303140700310115150103 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 728426016 1250 728424766 728424787
    0x20609071e061b20100309020604030b10170c01090b210c040f0e1f080d08060402070b25170a18050304080607030b0901052107050607050a0215130317 66
    0x121050301d070388400d064480100041c1340c02c0100030255040c6892408002c400c1c100c0d0b00081151043e8403020744486003650210b603045542c21031140c02040c100d03111009412510994646032529200007078003250390100c0c005489110700c0220f030340300c040c903500c142c9004c0841008108014009041810144401e22010442c07660004050024040d002041e101c149021441e64100203801c070241d8501c1024004100260040091480c00720400f906003441c480c0d40c0c07a40407170001c1c061207402514000c41c101c18851000c640d841c0b1050140c007400c0542e00d041c440b511003500c0300328480c981e031000700402c0c0700085d60204041d40032802603042c0300d0405026450503211030345035030000c2d08482c9060b00480244601c0c02e4041c03080090710700d000d40b401034003585001c00081c48511280b51240c00948504006035000a051140001404009040076145c1d480d5050003940c80700e2000c801c9018a86408455041e0302544064075803d50182c5003032214282140d45403040546108c00b8402500070522100308003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 728427266 1250 728426016 728426033
    0x11100e06040204050105181506070b1311101b02030307141f060f090c020a0c14031e0304060c030c1e05011803020d0c030903050d020609071e061b 64
    0x2482800400203814140100f00880e2810ba01c014424050b402a050030110840721480d48800c7c1c540b01031201c26001c5011542038400d800005115500306c4082007641c2040c5c0c0c1d0542c030082d010b018030b52403c0c107501f0244101d086010105101003100041c0503500071f502489025899813010301624141a000d40e140452010062440d02042d0011b10704e00010210710690020707001c1005100340161464480040311280090007074a171400c0d20f444078215a00d000b001608081540b1050030074082c0c0e904d5140c0c103418110b152919101c1e0281e421400840d50014004440b1a030181c6c01851070715190000a881c51641c801c02201489400031800d40030039013085102c00c1c4c4201c040d82c810b920112915159003101c58a0040c6500c402d141041c070310100780c0c0010843c5560309282441480030a01c0d0030255402442e0b5800100310340f243c20441540b450340442c4c118040e011135800c0b18102c1d41c56500d40c035090041c44807000b4100701c481070100a45407007411801c04848050001001c060764540b10100ca = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 728428516 1250 728427266 728427281
    0x606010e04180501021321020906041a0a0314160f0620030a0806011704030f080901020706091505090f0316031205241c021e100305010608010e04121110 67
    0x703d200e080300d807c001e00c21041c0040303c0d50750508280050715907160760028941c0000945014095591008014080c0070305000c15962403000a1000c2d040903900d186c542c102000c40c0090303071454014111a61211100da01c0c0107070988001c100c852808a05002044940c40c00841c0d482e040f2101401103203815100a000504080c1902c0c0d40e8019107103000030000d01303555207405d0241c216006d00710401001c03a500005e4686e841c0454a800403003510740c106544c2c0a8040e203c000340050f40703401c03d40001c1007002e400b5980340c404242c005001d00d94814840c1519003101110010a50304200708150a941e1038600e030f24801d620078100030001c2c0da0f021080200305c9108403040c1e0624035a080899030081848071101c403503000700700c0b10a10414000031640001300d54a010080c0200c402c1c0c181d540e402c1d00760800041c6e88290240c001d205a60800038001c001c0c3c182031249401140154001049084614000b24460340d008030321540100311f041c07421100c461144019100d02d00a954a010031510140590301d1b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 728429766 1250 728428516 728428537
    0xd140a08040f06170c162105090a090903080a020918040807061a1011030702030303130614040f12030e0303012c04030903021009031703180606010e0418050102 70
    0xb0071841c1028809402c2580041009804100e05004c00c4281c0d1405011600d40e40d441c0840360301880410b103880d0294022400c0885020081c00303a41195140d03000000d0324010000300c848600403541c0c3c001110844e070450002600192490000501e940d00e9a0014580780d0000341247c2c01070f100050705881082801d44045a01c1c500c0001e8500030b0160500404030801900c40129400b0400032000541c400c0012040105106406a04205800c424010f41d030400d5000341c01e0381e94901d40010b8140d0b040b12031050480340c0382c1c43c10380040704880e051504a4801d650103d1508804411340e184c900c03150741c1c0d40d40000704058072000001048402070002e54028005000b030092003020300305504010000110510307200507845020040869407140300002220f40556030020310b4001d401d0101d0f49034120f9007000c1c1256040c00d82c03002440da5040c006520840d5403640d4a02407113500e80306c0c01d407034100c00d0ba600c0d40001c40c0410441c0e140c0c60305501c0b5200601a0b0100c3d030700c5294040d43d4542c203a0b0000f54050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 728431016 1250 728429766 728429789
    0x1145107060b01020f0d08070e130c02010501170307080717091e130908030103062304050a0308060f2107120803091e07091e0e0f0d0e0d140a0804 64
    0x301c0c40e035030100102a20175590070040d00e0400000900280300d4000103005100b08040242d60520079200c40c4813100b80c4002c0c86a0901141e0ba0b06c902c00b9010300020300c980030122810320105030920401005a50304554806000317407601708282c03200c01d00d01c0d051044103108100208880d84c00d6590701c4050458500607441d80c4505200c0c2141048425005190844401410075401000103080a021241540c2c0d0002c00010b000f10b40d102e0b030034002d59003000c05030308241c14001804180080000c80149507403003941c1d02800350790b402c41444450390500c0522500000c1c040390304402141c030104800095240300040b990341e00d81d1813000500c00c0413890025524500300000b4840d440d0018001d50301740300c1e2078800641401c03000184947d81e13070314188108403445660388540c0d080c45203132403003a400d118a01c0c80d090100ca0802c20046480e071444100102e020321443c0c0405d4501c5000d280c810040d4403004001d2080304030b007916004892400c0c0c4108101c64020003040c00c00080c0840d014101074000b40c0280c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 728432266 1250 728431016 728431031
    0x301051e0c0a09172103060a060306080c010309021309080705070504061203030c0c0b01030302060708070806030705060c010621060501080a0f02190b030114510706 72
    0x2841228001d41030124103401008084101078020021100300c4021a8007500b51a4958072168109503250705103244c0c6104c0040748034140f050810166010790401c4950074942603542c90700340c0c203c40852140b0b0003a03801198020800b0b40c06030f404202d885001500104bc2a5204011a0202e942218041310404404507401d8280301003080716001420302900c042212a0421240d107a03401c07511314009040585610514001e903100c0d0070341c3c40c0c03101d910140034141c55860340f41c0030b5145d45040b541c43c0300007000c00c400a02c0e0a485244801d0003064083d003d062590b0502c0280065540320a0030511f056480e03000025160321081c40072406000c0b19078051203440c20901c1c000c419070308185d00145c07284e0301812070b4602096010000303c6045504031002c13840800c2d007171f94071155801c543c2d1220a100744048000079051301056404002a407044403034041c150f03c4004101c1d4041144400344002030b130031030b102201c9480c0582c280d021808040e001d20051000e082d00608140e404401c08480c0301e40c03200070 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 728433516 1250 728432266 728432311
    0xc010204081209090f100b071a090a0b0c070302150a020c12071e02130e010c02073f0807120f080609041e02040f0501051005070308071409030105 64
    0x603442d550710a2a5481d240284000c0003520902000e40341c4145145040c02003101d20a42d0b9256400803c001000b46469030b42900740241300e10036a68031a0004510340c80090310550021440e420400c0d031080900d1140e880321602001076070404c0b1411802c0d072180d42c6c030070089a49941030342841400c5048016990b0070034044c3c543d00308214050580004e550600c442d10000d802e1707091030303000114004400c5020310860300010391441c4c09500115055072806111540394107040d0402c40c03402c9a00e408440321196035003c0d24806022001d08401c00014490318204a104440350f000d50000070981b100c9040d031013944036040d40e80c0c440c0800b1511820200040501190812915010107515003001c54843c07904801040f11100010001804243d00108400548206100490303a09030050020403003550b9013882480104020700035144100c04070494048201d100e4001c940005a2540c0e4928450711480b0042c0c403544209070030011440c0707041c0180b00881e03c0900c2503a21410141003007005a0990303e1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 728434766 1250 728433516 728433523
    0xf0a06060609080d031a0409030e090603030f030f060102070b0a030212011a070f0c0f0306020304020f04050709120507180b04060f0609030201140d0203070816020d08060f04110c01020408 82
    0x41c00745082c040300da40100207403003000c034003444401d01c00c1c01d0201da4101d4452005240d41c120545040c1d0092611818005159004500400700f003020307225003003a91929000c0503900d0145008034148803900b000000c2034602c540042d075070002c0041c011206501d891b092416410b401050f02c140010b1380c00300b45403010105202c515801400c18800340e117203004820500b82100e1003028405048041104200010441c0c580c03483c2c0010600001d1509075640c4a00d425406948107680c140d00c1031031071600007030440c9880c0c807402d40200f065031100a241c502e010785080d02c0602c40074054a107400380d0038000650b407a900302020000b81c1c0074000060f80703540351010002100c440d031300164a944e1b07000342c0c28800c05400280003410340340c090801c1c001c04484000b044085e880354030754511076280048144000c154000e0041c501800032503065600c0011000800c03072347c0320700c50b508000000755036101059250400706050072000320060404102108844581010ba034030203c607010450f940028100819002403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 728436016 1250 728434766 728434769
    0xf051006030812071e031a0312070b0a05060f0d060902060706050f070207032402130305010605030714101101021306260415020a020313030c030605010b070f1101030e0f0a0606 77
    0x3130800c14006615405400105160700d042c034002d047d070300c2034042d00d40030340480702e003510a070002d046a0441c2400c00b851459a00050021518000e03000c0214005141c036011345441410003074044c00d64240c0700d808100c00074804038410385859035100482000350b00d0350b1000b041f505010380d6020131142028010340a0025000700f00384215006880281f001070020352000c0d0048a43c0d200d1000a440d940c03c17040000c1c4103a105288208400b41000820064190405412120304a080d508000c0c2d490803000c50225a07201030715440101506000c45147c0626400194000400001401c0082d00c0d09126444001c07900f244004c42d00701100c80e607906140c2c00c502d00c00796060b0202c45406051a42c0ca0b040380c2c0703041e0754160401503004501d0540c264400c0003a03039a17408a040304d181a4542d20b080540d0440906e00040d05d120b42024000b04030070000404a075078140d803041202e81806c2c66074841500c6515200c100604141e154415400e001c2d401304522000340c0282005440f8100103450680100d274020f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 728437266 1250 728436016 728436031
    0x14090109020d1b1d22120309060b04021b010c0e061206010c02090a020a0206010b040602060f07110f030d0e150c0f070b09060402120c0d0f051006030812 67
    0x140110240142c80c0e4001e00c01480b0703440035408255010740c654102400141d600b051101c1d8850304559007614800d00c41c480d004403e01407414000000f01240410700300b14040d0058411400040740e00c0300503200ba4829400c00f4099080019029034000010b01030340e000b18000c1010250203440d52100749428880c48447d4451420b00d15a50740c400004500a805003588655103141c4c0c140000c0c41c030f40d00603d410341404d94020604505032526908c10402500000000307001441203200110f443d0040c60304407400e0354020f0f0020000c0790348115580007a28030080494040007554000b81c00400f80030070401c00b02400720400f0355160402441c050045503030071050901903a0002e050f42c0d50384e42d07003001001d405c50b01130344c00165520440f5801c00340500c00d040d001840201c030202040881200818414081c074800c07203180d04c032440303003c8106a41b40000012940e11031101588500059642d101d0701035403134802d00945103c00c1e9403800401c21980d507a0b10541e2411000550341d10515001c07009154070412 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 728438516 1250 728437266 728437271
    0xf06030b04050f1003080904020910080106020705060405011205060d0215180f060304081b030a03050106020c090c0405100c06050403170c030106050304140c10020f0f010218010f0c060f140901 84
    0xd1403c03000d4240800391002405221000844042e2501c23140c0484444420160007001e4400e0a8030005141520034480d0320018011000c01050500c0d05000311400c49105039500d580d1025030700000d0300102806466a6440241c036642140107889401c0e0005088003120074064954944041400440000000140c410710749080943c451fa0345000699801c40c1e000383c20652a00011501c8010705000d00ca10098240301c0410300c15805c03649504114113071030082c2c2c2030b100c0c1c19511209203c234100c2c0907030303020503494024401407102d4100042d1213000840d9500d1703d040c81c100c890315420b0850b08242ca0076400110141414081c09090600f16900107450401c4585950700d8034a00821500000c0c0c801810110010201e64903a80204a010a4000b00511000d600ba000020182da035044e14036406100740600710709128611410b100359006aa5202418420582d9040044560002418900d82406050201c08000c1aa5486406079001030b0220001d104040350701a4a00c01c000200454a240e0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 728439766 1250 728438516 728438521
    0x405090c1207140d05190510020409020a1d0906010324080304090b010207140d0303020405120606090a060e04020f0102150a0b03011521080f0d0912020a0c0e07090f06030b04050f 78
    0x344000740140b0361b5440380c0d929041400b03580c5001410060020326000c0310a00204010801c00c090713900130400c0743e00540f2041c000c10300300481d09104180060185501c000140300058a035402908142441a000c0c4040c0031861021207501210b00f0068006240590001c1414031010066105252410070240014010780f480c4c482c00303880584095030b4041c05074140807007004c02c049c000e8042e2800b4220040616120400030340000359a00d00450f0316620501c3c0c43d07004610009014803e2806030740b504035162249a4544c0c09020346101301d01041411446005000040d401c2d80000481c00b5110700301c0040380e51140c4404160950714040703401814030091030020444c414021400002218403000112985505810074001c107000c0d9000710707880400006590700c00d0a0940d4406c00110f882180d40e42c130510703a80c8000320b9032480040802015805d400b0707000d00c0501d4030402029480b0a40c1c1c0b82c112500d03130309c5090040700760181364070540105c0d49402040f403540c50f241c00f61581c030500c001600e000c81d1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 728441016 1250 728439766 728439773
    0x4050d0c1e080a1b09020c030a120b030c0402030c0d0608060f012c0406090203071d0109020406020d1b0609080309100b131a041406031009050c0405090c1207140d 71
    0x504843c04010860411984418166140441d01c4402000100811510307255004220382d247c0d8080451040040c440e0390058000004510400819240241c020200c200c403102c00e0000039440941008120501032048820420490089030080c00104002d410582400010000a94010313005004424000e512488103809400005412180400a04145038942d030030580002c1401e500080d4040c0520140411400c118910403980c28141c036058421a03a40d4003102c0089001714022400140c000310f0360084150310031400301025203288040782d00000429600e01080704e100610031154408003000300101100d040c007404d0100c49250b42c2c2072148844440000320304240d1101801e03101c9907280364111200641c00442e80700c03180040c00c2082104407000109410030000c84a0500c00c0c0301c0d41d444000d60501c58090007440b03035071003002090307141001420040502001002014184219002480155145c20707880700102c0050300a480341c542400b661000e00141c008000307009035071000044001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 728442266 1250 728441016 728441023
    0xa0512031504050c0c0d0e0a090b13270501050103111c02091317040302030f0a171803030a08070e010c03090312091e080d030603150e0304050d0c1e08 66
    0xc6003000c03180002c1a551310041d0410300d004803020342055100d8003518404031504000100d00b0354404990411100385c0d00d4020009484288413101c1d081040f20300000d507206141d401802e00c0107a100030a54038106240d507401005d078090041078810740c1d103500040041c0241d008284200d0304069a10038840c4100b4000b018030080f048000034014144000005e03030a180172402d000e0315603404445220001416a800e01444d001030206034031902580040c2402d8441c0010000340322a405a40e40161814001d1030201c2c60f00941150001407526402c15115582c0030320090079a490141c4030380e109414603071401000c80d1007002c03c41d414001c01185d5800460b8000e1514400c503030b4440c0d1141c0c18582101012203411040358030821b441819203610000545e080c189410541c0d2101e0100c48103840000230460564846200c058070700202a0040e400c1c000c1290441c0317154804e46021a4075055070358010808003040700b0815904000290018803450703140303000503400010340000b07120351307142801061501c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 728443516 1250 728442266 728442301
    0x60504111b1c0215010b0c0d18210c150e0f0612090f150f04030c052a09060402030405120d0626010f05010b0a0302070204110304050a051203 62
    0x4100d41881540166070390411014200103903080d8001c40b0702040c9600a951100600550303ca100c030100000b10740074250805607860041410004d0a03003030030046080e290001e40b00c84043c0c00303001e14800441d04008c0230807051516844280c00302c080c40118205850075070003a400406104d081c0c6240340a849903c22700042d4850011240c0c140e5645580300010160304c40c121890340d0200c00300c000c001e04240041169401550840306941d20300c1d12a0924000000d07045452804001035003004c80c011a12036250b01b004039120b18202c41800e45490a440d07850364080c10740c540c80c0e204103118944542001c1e002c081c0c001e40300b920103505500301075581e04c0d00c6007c0011003820390440480d0300701a502d01508000001e124941d0304641107a0402c0074820002c1454651480320b608121032804816042d118860489400000c264101800038004401943c040d0000740c0e8003a0304c1d41001e424005100700110f020b64401c03402002030021615005061400d0016400c40082d07003401001000c0342420700303024 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 728444766 1250 728443516 728443537
    0xe0c090606090409170901022812050d05091608010e070605030402030a060501030803061c03080103150f0509010606180303050723060a0f05060d03050414041b020c0406050411 77
    0x589546003080420004d054140300901001c51056182030103400d180c00a0000f544c3c2a800d842190011043d03144094400c48012603d0b9095800404007103205000000c2054a01d481c00078034102c0025000004c2c2c40b02a52140742c103802c03209070b54048480740d0701c0110003802550024402c5000c1d001c2800d440b050107204590130721500000040031980c050181d808601d038000001c02181d612800c0040040d0000c407071150003080703132800c80183d001d685040d642c0d01c0356140ea00d107240c903802d541e500c81003000e0b2416a00d0707078140ca49156081501d9540601c501c01d24000000140d09464075200601d01d40a0005041c03aa8910080074000700354000f0440e00b4041e00001030b01490b25118001141f4455100c0c91100703e8082e04003440540c02490700600784418a07220240100e8607102c0030401c20021544000b004110104020480c00003000b03801115541c1c020710014200c0709540038005d10a00e84103041c401030700712911901c80d600c2c3c5881010042c1c039088e9000c000c050386040010b41e0900c1610502e0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 728446016 1250 728444766 728444779
    0x230f060c0a09120302011e1a0d06023c0c03072402040b0310063009020d0c03050f1609020c10060b09130e2d0616030e0c0906 55
    0x8211a4090050b400060000d00f851000212903810000e00800300f00d0b21040e50700260f000d040c100c40825000d80710355188517120020b0202a030b1020800001d00310a0110fa040d40c0034055584c07010740f03141d4030115204960001006000707801c4802441c13202041c0043c42001000c0c0a4418410000030944d0800c551110002c00d401c05050509800c01041620086503240002004150b202c071141c061802170100810500d0a00d031651026210f0b000400551041a80b28039102000104d450102c0d035002c48494400042d1408150049040100c1198082c2c030031301c0b1402e000700100f110400c415108180d04074080d1400301e02d61407000c0c00d02c0c0820710400c01300b2500407801d00500502442a10608035144100f081519580c4402607201e4125290003031082500e4a013000c0c002d100d034040c01c4260301440021707144072190075403ca00c028440d003c07041602d0108681043c0c0000040242c14087d0b295107e10000031210444014151440306010313400b00e4000701c20b0301d05c903604c0e020811a000481260030 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 728447266 1250 728446016 728446027
    0x603010f0e07230403050114010b090607060b060a05070c2922140f041e0c09171b030a0b18120d0606180308040e13060504230f060c 58
    0x455151425000c020310f030840c01455103141c14030350001003040341c3c4990700920404001d800881c000710000d2085d80d00301030081000045a160000c02441071503c42c100010707101c100f800106040f83c00c02504070004c140d000580f902030207092000c0034000e004000c44c944000914588640003600e00360703030b8091002c0001c00c003c210011703000b244448549250b6403d1442d695201002801c040b80c0d40c0407103002c1c51081c68480e00304c0c2454040c0003018103c44a000c4490704032400280020042c2035000e40400000c0c100c0400d620702c00307076114203060071120010404000500400d840403a04040707030038440e62011070240c0020381c041000503800382980702504d40e261001005c040c20160724413800782c504640010741d92807503203c0307a010805440c1c40d960364480035507580441001c03d813410700029001500034481005640f280562556010034041004100640e2544d80c1c0001d99100f514202c40760078103200042c25008407581c5100c482e15100c002005c62301c514030300543c1c65103030140190410600c001503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 728448516 1250 728447266 728447281
    0xa05030402011205090705130e031e161a160806130e0d09031b030201090e090102040308030a0b03060a0c0e09040f080f0415030209010801060518061809060603010f0e 73
    0x1040c198003150050f060019107007020350240c075030b5030f0341c06468410202c996502c0086941c52056203400d440c031324010b600e00540c10348110007206641c0560794018100b00440d0801075500082100279a10a001803108001c0507800c072882108011b1a18a800c10301c2004024810391010882341c0041041d51228103000d06034403058040d014030000e9904520901d9103071411b4a500180401c1100d0165060305144410b080c07042007106264440139001610130001404000b0040c2c200503084a104000189400d50741d41e070794015904100c41c8802c03407a540d110082c240782030500019501c441080001c00089400c00400390210304941949801800c4000000b020441c1c1415629029504500b0003612074039000841d00d8598000e014000c0e464040590100300c050007070007540c500840584492400c0d80c07c08000310391642103800d20b40c101302d80101a022164840e074004044004000d41900241c540d19402c1c8580031002501e018010502007004100d001c2c4105118004c0c2c40802c01d56030a5a103e654 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 728449766 1250 728448516 728448527
    0x81305190519020d1b21030215060306010b0309010b0a090b040c020a0b0c0a0903150e120903030f030606130602070f0b040807060c1b0e100e10090b04021e0702090c0c030a0503040201 80
    0x402a00711101141c14205408800544151440c0e129074200d0b18440300709c02c00110700c030005590140e015030040005010071144d81e80510382c07050307082e00001488810070740003844c0d0382c0546c0c0c081c4901c0c543d114020341940c01d080c020000301c080140014201410182c0c1c3d847c43d8100c00900210f00580049003d15000f841081c241004541006540c0e10141c00b090000e0018412420708500c984201d00900c40b4008880e401e85c1c03171501008015604200401d42e40514951005082a80c0001d00304a1200c00b091100701c0440038107400c0c3d00a10440f402c1500c84008110039401100c64102c00384401c0000400020b000070940e501850300c0e00a003880380c50b00d402c440c03000c1d01500721084499000400c241c030110f103860340320702d074001602c1c0591582c3d2802c1c0358820200751005c0510040c17002c001d0000c0b80041d0485944130380040c1006140c141024050100c1030b003407000c203020382034001640d0001d510342141100d0300142c030f151506242a8852202c20794034880c81d9601c4003880303004030000c0c0540e030280 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 728451016 1250 728449766 728449769
    0x120a0201090204021c060807030305071b0510080103120203282606041803020604060b06040b070501051b0f0a0c02130c030e010c020f0d081305190519020d1b 69
    0x10f0300c259103c500c111001c82c40d680c10118145001e5141640004140304c2c0000c4080c201c1e605a126107160840c01e07182d0844090300840b050001c1d454440c00006c80d900e40541502c408061a5218150f40d410740c03400305095a50900c5000c01c550080c090004048841140a91080c5048207440554403040c1c9042d55011058203800c00010541c0355000c1d01082171000261040008440402c030725050014100207040901b58007034010392008000400294180d44181c3c0d0441d001400c040c241a940c514801150340001c80c00c0741ca0365184c00031700402240640b21415004505403400b8100100d1140c1450280034030414903007005502001542503450714580343c0c40711410603900340084001d80794050060301c0a44941e0301158600004260042d102003505400c500350303040501031050790142c0498280d2005031421821045a0500d18001070b81000a558070405888002c0d162038103034208141085c00c0502c480341e0032401398a0041c01641c2d00458820210303403117003240c06d1108a02ea0f000394002082d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 728452266 1250 728451016 728451019
    0x50405040515120a030f08010e010509040c0e0c0909130b191503080c060703140720010609090308100303050906030901090b0403080109060504180807080d05070810060f02120a02010902 81
    0x3e250b25520b40c54008110224200d01a40b00c6003202070407410100c0711031109220303500035640020010303c054a8000e10f6240c000303004000c00c0c91029203e8500000e440360507500c61226510000700c04020b414103900b00e96105e00703100f00da203189801d40c0e00e6100304090001c100c2010f500c642d07080101e844c607143d0b02081481040c0c0a0720740700940c41e442c040c6550350019415140c1c1d0311598001980043c0702e4083c211501d000424a80e00070381301c0c1c15003580d0817418010f00700032a07000300449107200c103c2441884020b11a02c0408a0105003904000d4103c81000d0700900c2d581444a20034400f00c0e40080855400d140191041a070740d075940e0100900520098000402ca00070242c00c0c4000c1c0f45c2d001c011300d4180c0b4403c0004004c0d056881c400c00044508002005d8000e400703851651000c0b62014015184150249201d03074a0074007030510302c0040390f1044504201140d02e02042c000c0340d03654044420040c2c415424241b903442041c01c4041d568450904101c600041c0018826004520039000110b06a50 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 728453516 1250 728452266 728452279
    0xf2508070b010e06031c141e0d110a0906080c04120b0901060b0a020730060515010305041e022d120a120e030c0d0b04020f10050405040515 61
    0xaa20341009008020300c28000f80642c0e80011036218580498891041d011252400003da50b08103001c0c0c80b141c1c0c40c00040901001c00f0301420517010b28808400c1d00e048074100700701d07945080c0c00180c50100c80c481e12030726042410502000c44425040345010b4156401810079001c40da5800e040040d5610841e0048501481e55004200402403c40a0b035030080b1100700091080b180c41d00c403e82d0150050701c103000f0040c1c1c080001040303100c01e041141c84214084000c0140070b6a0502a054000c5014044c200c5045a6450410034a10b5043c42c0c85503941500b46005d028505090b00ca40c4002040003101c007002030706805510003155030700950189040784444d00e07003000042c0480d0240401d46440b0f2203a0244000311034150500c0c0002c12240045540f04450314081c62070030608a551113001c1ea00d06030580300c0c4075141d503070940d0380615481d135881c40341030800c06038034080c0f061201052107419928003a24400540d5401150004203550980d20709035400915030ba01c0d400e201e09240c00301c2c00321580000c03 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 728454766 1250 728453516 728453527
    0x21e1c090503032401361d0a0203040c0b0a030b090108010c23041203020109050a0b180d020309011d090f011a03010b0415020102130e1b0f2508 63
    0x40060741c410400d0758440444c2002c0c0003020311205816a9203079000030501d044c1025490007030700107003656080034141641c4014651000500151003500942110410585072510b15080c101a8a40c80700c0d00040c15402c5040c07503580d40740c068500380100800d0160116031b04401c20300c25840460107050040140307146595460056009084c400e42030800213110b012400e070300100c036002141d4610303d10009140b42c1441c000c0c1001440011060450440d522181110302040381041441c4649019000101003400c10129001c0c3c540807050f100440c1c0e400c400840380e0031580110545901d402c0a003080c0e440e110141c0440d00c101500711002c15400f03c203d8044c030504480c22740b48a4140c4004610303815030301c1150f100000540c0030902c5880340d00b000810040c030942103005645c42d01b0b40d055000142c1080250300c500f00712148207404c1003202c3c006140802c11140100707030090f6042004200b1407807400c40c800150381091b110b6800c04600050450010b1132a06540d01604491203401003603850311032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 728456016 1250 728454766 728454773
    0x260601030906320c03060d2a05040b0102010e0703170c010504060209040b06310e161202041202040518030a03020c06160c020904110d080d0f021e1c09 66
    0x49201603a0a80c5000c0c01c0c11110210140d10025140200042103c1c81e04643d02c5e902000100300b070b00503044424070201e054940380980d0469445107014608e41c00210400d00b4401400308441c0c20280ea2411a030400c1440ea5030100041402030031741e41c001810010038540300380c2070b00b45480780100c000e00b2b543c6007108200500c00d85a018002a1001300c50a0054103954410000c1901842981d081007040100403410011300513100303481c044061074074011820b80d6814115144040884084807691152008440001d074030411083d4072409043d82141000e090040620444055640003800f4590756000b01e105010084403541c030741e80c2c8000c2101d6854184240003000383d0496001a0700e244913941c0410311103000c6c4620210401002eaa0350001e0348966000c000351998064000d80b0300d64642441b03000ca0307172104030108400b940200b0500d581d552000540004076100f00407d0a8075904c180003054203448488a1104402c00701e00c00d0301d4495402c080d107516540e0080400c0c0204510381500d00080 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 728457266 1250 728456016 728456051
    0x1003031e05190c050606060c0d110a060524120d0309080405120a0c0803120a02090a0806010f1805090a081b0604060e16030206090613180912260601030906 68
    0x244c46001179034015160b0b01d09126150054080d00c030342980100c40703060b100d180b242c0b4224850300d80d00340844408102d82d0b10b901c2c084420139200011032800d2481c107080442c0c80c00050344031a00f0b094590340042c407851806261201081c400d95402c04d80c65604d906c09100c0b00e0010b070b0300034200c01130501605689008103682c2d180c0700120100d820703040f003100008803040040701b03a89c041c0c0c5044401120507950311541c0d000a511101c08540c0c40010042c020415240030046c0a0281081c014008840d5040000e0381d0500a0a0402c1c0b0144500740b1003084501200030540c8803410764090f64064441010344a54242c00000d2580c4581910402d4100018401d558000324610740198090302d200300403145154564000f0760101a4200301c0821034000705040080080100200c03000000c28140d8603100401c2c030844251185103a80c9484880c0c6100b4405204080f011403d114142300703440540181c030500800e43d205605840d80300000b00011081d90103500701c20034603607001d0001c001460602004c2404c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 728458516 1250 728457266 728457287
    0x210030b06070c0e06030d0c0f060207060905010501030803010801140105151c0f020a0f0f0c0803060406030203190618030212030403030f0203070903140304120605090f0a0b0a051003031e0519 84
    0x70134860103402c0b003840f5025161848d92076130800800390b00444103880d5403000c2d40c40711100700c07185130ba6141c2510114500703206040c041c502c5081550707a254542142c40d400c0d00d4800c0000c1810024504c010490755466529000700707030f040c41c3c07011500e807034840c002d2403d81ca08100b000728515040c0841940e0010940e40200501101901d4420400200c14421114481c501c000c2d5008243c5800e0000046801000070b558844002040410026260b0780800d007420a94500314016103480c4a14000f000b507680680340c541440c02600c58507803440d03501c00940d114485629107181c2400007010900b03142c82904243c880045613070055650f8105542d0081c50340c0b01520040c2c0d10010740813403a1040c4000802110b0803513001840b94550b111064480c00010403025144020900c100c2e580d495140c0403d0020000d011f014611705a030510b0450000030982d100102492042100c800060000070381007441c501d84084c40716003080040c42200410b85851180429088624150180030405613500c50801c40 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 728459766 1250 728458516 728458519
    0x809061603080112050d12020f0d0510050f1804110a060f020721031d031f05090a12030b0f0a080307050f0a030519020102040b12041e0210030b06070c0e06 68
    0x1690313990b01036600c8403088502c0f008185401101001076070f0b40c418140e0341001c64141c9401880c080e002902c188865000304080110700d611102005030741030b1554a0500205801e031403170360070042c07600c0008400e2581158544800d61814000c1002d01142041c0800003050141c100e88000340c0f41c69020300301508407540d540042c400c0034404101c004007954460034400e0105140040c040f86507a0030b607140c0e0030814415035200110f0310051300b02e035030410a000b0084415901801d00011410052007503030801000f540c256804001048001482e5190000c400082d038a4006000a60030780000c04000c00542e01d59400090b0501c04541140044010a0076911881c1200c503660500b1400a8444441c0720b00038010840a20507041901d030301d00c03c00c00c6000707928400140741c1a00c0307a4900c0f4051700426801020344d15004200700030081c11100c1001b40140c0f01e045c800c447d52050380091031000100441200701511001940381c25201c45040c2c0e03881c56406071040030f0700d685610546205a2003151440d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 728461016 1250 728459766 728459777
    0x91605090312090418031d03101508070603110301140409060e0f0f0c06070326010902044727100f05030a1104120b010f0f1805040809061603 62
    0x4954100b036452100302d170302e5040d2102100030000c640340f40c4c400300001c40d0113078050061551000440034075114a903080c00d10403402400b0103007807492442c901941da03000401418904204c1c00d0b580c58400050704c2c119101401d0400748100c0020228004d084003140040c011804d26083d0b000101c404115030310000c50010442e1708040741c008107a0380e03500184c0a1150049010032169003c00d10600b034020315400030314001001c0802c180351060300d0080076841106480c4e80418148200309034410a0f00d80380c1040000480007141241c1c1c3d00b141e040401c000e00481650103540f440b52024141c1c00d5401001c0c1100364071100707094200a051480f14040c42207071181541e28104a1a14014042500d240d0800e640c1c0c1030035075440782c01d40e100801000040b040e10a03410301001070181910342c840180d00c0c4c8609127642080d49060f82104031903859800510f0741000a030002e0100002c03079101c40c40402120301001c106070f2140c5c149000684a0080155008080012508608240c1d000961700c80c1d4800c0e902c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 728462266 1250 728461016 728461031
    0x2090103020d0e28030903020907021c0e10090501021f110a0504080706052b27050622020607020d0611031501030903120c110715030e010b0916050903120904 69
    0x1c03c11310000c1c00d100601244c10f9090501c003606202051542c0400c0a004a07082c01e0241e002450b904040d4880d00000555150801411400d080e1070340c0d4011405800e007c5505418800080d440d8885989110301c0812403100c0304005090a401c040c02803040b0a19107581c880d69500000c0c1264064001c0c605584076413032001420b00d05c03400494403510800400701240801c0c41c6004980396002c0d0080541d400d883e02e111100c4000c000c2a00c94400d83c5040c04c50504546a1902c581081c0300180506055806c05901c100954030f610030603036419a0460707145644403003e100040910801c0000501254a0300704824451403030b00f0000c50094540c100644201803d0310011020b039101d226008001030075250030f5140d01c0007540c21801c100d04507810114089042c040700549045c0650780580f00b60030115400030900ca030148119042c0c0501440203001c1f030821040492000d05e0094109450142a00e200b690381a0bca202919480c0300014103881410007040c143c01855000480250703c120301c1c0c002c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 728463516 1250 728462266 728462323
    0x706060506190c0c0b0a0c02010206070908060105010f02011b090806010e191a280608100605090604080f1506062109010b0409050d020c0102030f0d02090103020d0e 72
    0x81d100140481400c99007210903601c011598143c1c00c480444000481c65404a0500c1c00d000c054802842d0316900e2490800250000a140030000f52615050140c940018000c3c0000400c0b1039054650070300f0020350600400c0801ca00401224905002d40c1402d8110040141d9000e8102000ca50798401112800c2e40c8406880600030416150421400700003010300141400ca9000419100f402110b100071183c02100820030006900b5580081d05050b9081c1c102c003002c0c2010000c0c00b908031494100340c1443e0003608811a14440d0185c0002d001300400c0390510340e41c0c0d07030040381c0280c01c405083e12100c3d25507240460740c030140c968003512114180000107040c1d0828005444803149045080d500d100f01d510228480444041d080001c4c4b5500e400c03410965803030f10701400c0c2103648110000d11074000015402400c01141ea440c290454008210490702e20700038800f51641041c80040040c4c4c0d0b0a002d9005800034450100e250640a003008464407002c100841d100990340c01445070a0001c41c0d4044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 728464766 1250 728463516 728463529
    0x6040b0105040c051c0c050408100912020a08090d1b081f0c0e0f13090b100506031e10030c090b09090c010507030804232a0904110d0b01060507060605 66
    0x104040c5d220041c52507402c0e41a100c0d40c001c0c1c038400c41241000c3c0d1500780c45031109410611800c1c000a94036480f0303102c680400590603081d44852040340301a00231410103940d00c408034403603a4003c80c440d84a58030701d0801c0c0124030a025140c0419110006030070365032040c009458800c101000071a02c2600d443c00600c0c0c007454020f2500c0c003840340d0f407120080c041c45010886980b50090300c550304160003103074010940000e071080c940010b001d401001002e21345004981c002c0003240e00828000c00e03090050291103440c105c1d41d540760032419034900c0c60b217030303246c004049030928260700183c1512811600020000202d50103040801825100c080c0c20703984040c03800da5980c0501a24030b0000d50100030b5003001c00c0c824541c1e42e07089813080c0100040f010000d20600c400c002c505007504042d40092811821101c08200309101f00c0180211015071030110000050b8405801400902400c0c03070078a0000c00d07641c8458942030f94640c8951007440310b58458000800c550030460080300c00601e445000308841c506130 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 728466016 1250 728464766 728464777
    0x207050414010501052d0c1b0a151704080408010c0f02060a0b0301023a0e06040206070f02040528050c03011401090b0a23120c0a020c0306040b0105040c05 68
    0x45048820607403821004484c550700c10326182440210700781151072261102079a04071400c0e0b545006d41d480d0f4000c901001d080408c9a5015020520310490114180e16070f43c0f020001c480d6002c08404120303050369401c0c1d8100c131000c1c4840e40407010010802040001c400040c006485401008000010070303200180c44014180e221100940d11070000181c0c45c03400e98000b03404641015001600b02600f041c800305411568000a124800a80262401d40c51410488411500381401300780702c3d000390111100e4403503030003804c0680103403000180f0303c0070700c01900d0544000c658050f1040102e8502110300410300644121a40d40203281c0c5036902400c1045030091902030405400c50a145902c1c1503ca080c030061b840e8017150520604071000210b003d182c00240c030120480d83c9a4507021b0205940b10b16200305140100500c040303082c05601c0ba280320410441e030740020810540c80e42c407454680117034900015110015854070038201003004100c5c0441080c0c1c1200e10a80b0300b8441703010491003e940f2070042c2d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 728467266 1250 728466016 728466041
    0x61d0303060f0603100b0d0507030507020d0e040c030212040b0a0509030a02072309040c05040f06121101050f0a03060504050702070303020d1b0c2303190803041b06080702070504 78
    0x106072088030380e407400c04010f54104100ca98174054860351a95075803119000b003015104603654030300c20001c01542501450342c0c401c0b0f00b0710180003d00120140a020031540c80001401130380c2d50000705400134081e5048440310802250a5140e43c901440d00d80150790044511910703a41c00d01011034800d680010699501c401c080d009003040034240140a0103d4050012000c20891007000482064a410320824003ca01900076038644506200a01041e01c180e0f5201604103880c142c01000944a2000030101255000030820603148240c0012109400317441c41043c0c00c5507000a280c03030f03401c2e0154071010403a1000e0318103014654900f02c4c1a03885a0243c030020b00941c202801001140c6d1007000d081c0d171441d298480d00646000c4031349601400007415000301c400728003110001500541001c215500910040700100300b0441e015005401c026100b0100800c00d071408004a42080042e02d01904e5070b40c0602c40100d8a00d50b10000240004416902c4d50098081e485c00440c1c1d03401c081c094034685070b4a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 728468516 1250 728467266 728467279
    0xf032218150f061b170c0307060b010c02090a0c0908010f0b0103060506030103020609061c0f2c03041809061b110304031e031707022a090109200403061d030306 70
    0x11390080060350920440c40403102600c081c0e5260800b0700850380a400c003155144029030701c60099191900440b0000e02d107460500a07035402c903c00503074401c0c1d40c143d40f2145804000c162000011030686100340c0a412a07110755090082020b401f6446600031403c030b250036a800d0000c1aa02e2082c044984428000a17410000401c010b450a0401c40e0091551803407100d0007403003105200d05614111030040c0c54544096894041c1890310400d41075400c1c0e1841c41c00e05d500c180e0323245980b6201d69a442130380b052004410450302c0d42000d10015520040d80550414014460030360314a20b00c2d80350080ca50000c0011580036540c8911107880042a6420380364030521544646070740d08408061412840c00c120208a034030400210315a155004842c01540c46800800d01104c0d550484072207240c2001c0c5101c019441c91848008a56030b180b034484c1110901e80000800c000e188407403032960711550110b02480080000e0005c100032950313121051003003005e00346803504800241500d071207100503503020342d0244 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 728469766 1250 728468516 728468537
    0x1406030a02060705071a0306090601022409160801060509010f03030c0f06091b050301050c071e020a0305070b040f1202030d1d180a0605030f032218150f06 68
    0x41540060898600404c11034011030f81e18810000600121101d04206880c048103028550800c000400d8010400340058840c0d00200700e031a4002042850070700c106005a000452122041441603c00140724003a00218181e1103403071040c044c0241e481154000c0041070b00004000484502800a40b0350640d00d80d801c0940c0c07615600c88015840d0020790307903a9901c00412000407100b4183c08107150302d40c0305114404e4a040101802c465000701100c4401100b0400300c00001c00d000c81104d0b1101c0d03541680702085800e400419000040e54200811610581c02d020231000c6410020300115078409d42e91001c01a110b034a00002d040300d561000b901680305a0711603030390300c0c050310960006044c08000011000d12820000301a0309000e41c1c00740030b0031400024440402401e002e54005000c007680181124488154035990b6071003400b00303425107078040f410080900c1c1c00d28404400100300980540400e0300c40050804010811041080710050720141e00141040000255008807481c0e5212240c20b103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 728471016 1250 728469766 728469769
    0xc0f06010b0703050c0102090a060201090614090c090a0b0907090312020111090909010b031b0405090303100501080702010f090c080f1b0105090411070c170304080309210a0305030a1406030a02 84
    0x1703801c912204070300d65400340920780941d201d40e10000002d11f115030000c2010052403c10b002100c3c01203501f03c070400c03a14070070007000c80400540220320760400d031101c2d41c0558500810074014408101103c0c0d0050f19481405486035100c034090003034038090105c2d06000003030014140d00b02c802040800004040a1080203180d1400d410403035401600540041410b584850010b41000160f80c4203a410b0b41c1d0030890340c4802c2c02d040c8140c1e540074600070700841c0766013002c9084282410709071003944c4c10004001c0000c2c140c0d074402e400c80640061080428007900c0b0092410b1140c000c1c850040081d0f0788214100c4119031030300003884075a0001142412041c1c400c059004403020740c0300d1914660000d494901803040c044014000301003203401551108446403c18664008600174000d000b01d00b64018031043c00b03010000301c201c51035082d044403503410b0700b403c65a20000d0050110400d01c001c0c0076120014091680200041d0b06c5400c40d040100310000c04142a40c004090507254a0f4142c0c0c80341d102d08005 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 728472266 1250 728471016 728471027
    0x30813020a050d11040c030e0c1905061b0f030306010f0305270109080316030e0307120e040905060708070f0c05060a150e040303020c21090906060c0f030c0f06010b0703 74
    0x2607130082c01940c28032803c81000c02c1c10b4407039510800000036654000012000000c1c000120042400c55800010100d00b5041400c0300c051070280038807601c0300042e041e00d2080900110b40c050251902960800850820160703140d40080f030703089002c642402d842520040c40f91080e40d11540b015030000085007a2000c00300b40404d04c1c4a030340c1015668882600d03012450035400f951107104001c4584202d00c10340d68005041da6845821080160300601c191000907072600b8075a0080c04092030000c1d1404054000540540b20007003029000c0c2c014042408482c961001515118900300c0e00c600c00702250f030031400c0b13a29508942c406071051304100c0100e0001d10312034201c3c0b161159015440c00b2210340f2002d625000000a035001c80120350300041291807110107002d41071144400321070000d01d0b016030503020700c2c4d1762183d008a40e00c501240400103c813584d80c0015225110745640c02c40c1c1c6004a0f14141e01c1d80c039840a00000f00c94031451a0303104d60000300281e0f441c140c2d0003181042e41030001c1c41e07500341c40 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 728473516 1250 728472266 728472289
    0x30d0f0e0a1205090406080c0f0603040c120503070b04060506040b0a060c23070e0906160c060207050f06010b040e15060f0706060308030f0a050a201303080313030813020a05 76
    0x2089020003003541e1316030755801003401424030007010303102001a40003041420320300e52007400c0c0030384001e1040001080f80c48804100300c8512541c90201d2060918049003180300f8520000c01c0c10400d02c3c20700040c00060b0344058801c1b08156420030007288883c081004484881c0f090400051001c91000009504620686500e8100814016580c0076041400741041201d800c840900c0c241441045811601001150340000c0103285101d5a012030140003401d0f4031a42101910302c58000404a041100c20032404810020001c03c0c0c0b901c80d611125044803661180c03040c4400d41c4500750100d0050160460a07454890004119528205c0d07541581e50786604a81e8003039652540d00e43d0300102052002c001103209800d029035818451400510043c100c84001d0040121280307070101844510710b0890182d007140000948094441030044002040700340700b5080101201c1d0301209114246003440c0100c503006101c2e40365403640c2d80d00c91805a1418221400107948044041070804c8075040c820030009 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 728474766 1250 728473516 728473553
    0xe04150f1b0c02010512090f15100308030c1b07090f0516030510030f0b040b0106020f070e09100213030c08061b030411091608011508010b030606041502030d0f0e0a 72
    0xf401d00c1b9032038103072540c81c207030803141034289402250a1080f5904240311803695403095804d002c0d1035050000d40310000c0300042c00000c2103614004081a441140c4200340c92008039000103284003c0781294820b0f031030b940584500040c10b1b0800d140c04114a00368000e071f510581840201200c04030804104901620000e000c080c24103032203540100c0401c034100000e0309418050310004000d030a261400c410300e200e0503070083c000c40d003040e1505036030b00310081400d078202c07a401c208480490b161340c01418100520040d103045035900c0020600901030707801d1125812030340100a480302c0b140d591051107448040494800c3c1020340700481030501420340d140516003050044642260008400010420b54541a0384407080ea13800f0410381c00c111036029907054017403c1c0510b4140242c98107004003910040060250b0030106901100058098503140159001086015102290300d20388000103501c903400204c1400c05141080d200d007160007543d0040320111083c110080414504584458404500300703400305 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 728476016 1250 728474766 728474777
    0x30a06080312040b1e150402220302030d0528020c09070c2001020309130b091006030605040603020a06030c120f02040e1e0417040e04150f1b0c0201 65
    0x300d400c8004101814440919035500c5040703040c50708020540c42c800a2000d0003c1c81a244442d0350644078860700f94111607040b01c140f0017074400c0000a0041c0c0102c400702d492000508441003104021400b007402140c0c000d074103442e07040f00720800c2140c0521038130b040781c0481d04100010082c0c0542582203003489070840d00c1900c001c8158a000160322880650310003002907141d5000720140302c40450f40c40925034080f684029003032401c1c00042d407030740603000c03620384110396042d103001c0750400c540c000c01e00c4094000c105c0c10480c642240c52340340c10310301d900844c40068907003a80400c05040510a01c410780750010164000941b4100c0103e018100300c00c003210400c404202c06141414840c000c40e2202819400701580760390400c3c80c1040711020050158218207510007041c21002ca900f00300940103500034040103200c6481c0710040c5540d104d070340d00105400d900501003000f440b140301e22b8440c01614209007031010035074a216840c10f4400702c440c00d042e07000744201c07141c1d042401840d002c0e03012481030400 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 728477266 1250 728476016 728476019
    0x4061107030b0c0f070501020d020301080c0307210804050d03020a0b090106060801030638011202120a021312050105014b050414010e0615120a021c0b01020f070e0c030a06 75
    0x2407d00703a8001d044c1d0180706940100050040a0b01480015800380041d002891518034260107d00380907480c49404403014483c240e85001d02080c0c00455028040150003ca07500c2e065140095880c669204c0c1950b4202201c80880da1501d810b0240302d0403906507603100c060301d034210749441d4001e20359014595607140c40304160726900004007611100005d4500c1043e1520103150b00054003104080c005d280c0e034030384100a210034404060309001e0300300c0140b050043c4c44030b001840c1c1d83d04540e8150042c1d40c42c00b080c8403036001007281c15044103042c1e456000540340c2c100c0461501650840146913a0021700ca0303103404200c1c02e0580e00384402001d4841d40040b03030341c003070f6a00086000c65241c2c0c000620001e000e00c0050082c2e002030801326030044002d0368144440c5092000d01080c6006011803ea244600d034030100d004212203405035540a80f400307a00c9900c8141c0006603400504a01400d1801f60043c8020141d54250128002c0111020440481480e41d1a114848030341c4c0d1000705440d1416664280 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 728478516 1250 728477266 728477273
    0xf03021003061502070302090a11070f0204090203121801050306060a030b04110c01061401020d020319020c1e0301060b1c11040801060602030301080105370902030d0504061107030b0c0f07 82
    0x43c48803000c0c4881e0080d12256095006002401c01c000b030640d00c01c070b420403007804103200a0b00102d482858203c56800e51401d010310025000e00100d0101030740c184100740141d1480548480142011a40041440c003503514080054a090104a071080c2d0706c054140507070381816000e900001041d40c4000c00006800b084084140c4d020781040d0030704840d5a40d81c44061082c00c640701000700d044103090008103003d0521060007541d0344580340b00300420b0368110741c00d508010f008100c891a0690000d1407900c18205174080c1003d1030701080920343c8250b083c03480c00965540200304a8504031a09524041350021850743c10014211445201c2414401000001a180403c1c400c80380904840d03400345a0320351401d00c0041c203550003e05211499490401e100c1042c84441c1d61481502c600d038034040812540c00400d0790300601e004000650940103000245011a60000003042565060b89440480301b05407840d10b59681502c0c0002070130703021752901044c0300208503406854000d405081e030902e80f0700d0559 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 728479766 1250 728478516 728478539
    0x15060105161b14030601080c0603072003031905060108060901052103030f01051908031b01091b06032009300a030806030f07140604030b130c0f0f0302100306 69
    0x24814100f0322001115402c0601c0d0512105005040e9103004115440c24000050071502c0094049400c1c498841c204202c4901501300c0d26034044411410340b5124a0060041031034002000c01c40c41c042c519020000f801e940c05035039441d0041c07030083c21891587c3e0034801400488064000081c0c00c2c9400040140c541e01400c000852140580e2003009829525001c1841071070712402040c2c82c17480c0d58101c07061041040003c142e410100c0020503420004501141203401030004c980b015180a440e000014900c010b14400041120300940e01001003400a2210542da05200f0b0003a42d8207120070419840a8a409a0341d1200d608001644c2d0b00d981c40d0741c0064410b40a0030b122900440e4006a00031010316800c04205035000c2415070150680008040e90030b51103075540c0c0944854406080040289502d0b0b540945010f158405410380742c0741440e550040c0b00455503481118045284030001c5100d042c8001a141241e60001100c4641c0d03041d9801c1000080d1981101001c240d562240001c0306807014 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 728481016 1250 728479766 728479769
    0x906050a0c0f0c0f0f030b04060c030b0316210515040827101d010809120d1506031b12020d110702010839070c061115060105161b 57
    0x1109483c40d01e516208207615000c84550118102c0c180c0c01e8410404030f0201101c880d0702030703032092001a40620f00f030b909400070026204140d030144070742120075088102d08043c0c042030f150500503960444021000d4070030031600c0100028443c5d0404040d8543d8400e50b0350b0034075003052140c50801d0804a01c075451608443e94041900026810201c40d40c055041c000e01443c0c0603034141c50085150f410350284010301020710314140c1d04112114000803641182440724284118112414642ea8000650901c01621001074141c03d0162a0b00d4001021800791080d2044c11007142d1058a600007041b8080c5c0d8088083c03000c240c4596005c000720940d0346060b00c03640505084800300c05d61181100c1c00010003c103c010502580c1040348400242200b4035108121681c2c68030308148a4040c005440110b000e004808008200072440e84002c81c40310b17000f04000000820110880b07102c16200c002640c4004400e42c0c005010802c10024812648a00714100310031034002c4003d200040001c02c2003810001d060b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 728482266 1250 728481016 728481023
    0x302120c030f0307030314040b010e0402010201060b160201030e0303251e03320115050708040e160807050f0a110a2303070c1e120803040c0602030a0906050a0c0f 71
    0x1615001c040e00351080c402c000d079000c00f201d1f8051a01d952414411f24042c000e4400500d01130000404681c800d406c240050081001881c0c0c6444450743c10103400742c040b02c8101e0119003008078080c80c115000041d03038442d02030848801107034000003441400c0300b01200001010006181040c00e00c4070302c0000302031041c404d01e5a001403000007810550181460440c0020a0b41640103e21020900c0f00043c1a05560b4035000600050f8a0510103440c3ca01c2070080c0108081004500010842000c408840c4940094503a15078001640d801c100c401c1d82c001c80b02d0401003001404107543d001b00c42d4002d015000b0947c01c0c89052004411845803a0042424040700d56419501c1410480c03a60420301c080c03502480801542840718540e41e400321200b0f40d0040000020a42440ea0b480d03030400580d8a0050000500211340c030009800c2000c1558421942511185060800082d15601c00002c41e071545510b540c40880b480d00b0309004503440d501000b03c050400021789083c101240001c00340c0f1a42a11 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 728483516 1250 728482266 728482273
    0xc0303081009052503090b090304053d1103190f031a13090f12021c0e0d1403040b07060e03040605120c0d0504050619060b040302120c030f 61
    0x501840c1090681c05580140c1c0596080205000c0400001d00c0229106411807035248035118801303074110b0051001c00700262400003107105220701c0442c00b1005005a510aa030b001d40000300b1110b040c0405814035100f80d03070700e0640c024442c00c0920460072584079100c1c0d070f05e806080c905440d2003082c1307580c21000302024140c04080c0015002034204001201021003400c0034007894186030030008600c40110240340c02049480952030040d81e0540c80907012075444802d010241c0c0c094242408840c3c2d00c000b58a0161251800f0115000e40c0c51000081c0b4255566030008103100c3d03070051004001c003e110848015004107404100e41d0030500141c40038258085c1160b45a50b017070300305a029500e42e1a0340410540041100307010a44d0f00c5000c80d46c00c03a8141410380e040c0d0715480e0080444d445610709140c1c0d03403403402c01808200240850030038080c182c0c0c815000903a13500080810b04580700f610501c01c020408010801c01030030070b040040b00c00b20484003590003100f8000d011a04096192840340c01541 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 728484766 1250 728483516 728483521
    0x3030203241806040e03040b0304030912020604031104090204022110060f080c0408010912030506040b090114060d050907050a1d072001150f140319050a0c030308 71
    0x40744141400540d20034241d41e14200308003020848220126088080c140d100304005000c645032508030405441c0a03200720380d6165500c0c4550f405a0300240ca04034005040c010000036211070500d0313050150b03a001881d16240520316500c0170b0070b1108603105142c10036141c00b107a0015a540d8030117880940c4200c00e58041002d581300c211090071400800310017020042640600c140c3d0390040c58214080079500340141e8540b50114000d1140c003540e4090b00440d07081414407800c02c16020400c2411a0040c1c5060000751144001c100543d03442e000720b190880c0c00746d00104121512011400f801d508003034451454566500e08c43c00644800300c071160169030003e00108100c0c02c012003c08000c048a05401a15041080c85281c00d0000a0508400c0261480b06d01611608420320f006100500400070422a420001d86075034100441c4180d811030b0100d210b0000c0c0c0e40061004070500303100010044e1500185603880c1c0d095016081300c00b9102403003235004000000d15035204980245020742c440c20000d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 728486016 1250 728484766 728484781
    0x14010902090a080303090a1b150f090b0a02060403030b01030204030f05061e04050601152d0306050f1507060e15090d0e09070c2d140601030309030602070c0b0703030203 74
    0x9140c1e4880c03c100d600800403c1810603011071130240b55540000b03003030b0943d6442010f01c241501c0c160485403002040e0805c480405070400400b6440190701d44420045582c2c440c0700c4076190040190741005a0826400240028802c1d031043c0102481410700508042d22911517500c120b000420032102a40000c041c8005006d4503480c400341c4240c0d2013003419591406541e010384502041c0315282c010b020388011114510b005620842d41150f240e413200ba000d1088684203101c8003003098002021900e00040821396040c0350045040285010784410150441200c0058607a400340d241038501c2640d640580103240400c1c071109920109180c1c00700300e10b04106081a0078902006126414480340941c41d000b592590b40c0740560003842c1c0c3c05c0101000c41c113030425030b0142c041c0440c0380425041502514102d02a41148485002d000350282080c00c000ea0783c02a40d00d138001c7c040034010810305c80c010400508150002c00c043c9104059100e090b0303545d40c010301b5150b00124411004240c010007080b605 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 728487266 1250 728486016 728486029
    0x80f060f0f0c0f1c020c0a110a060203181309030f18032409140f010e03180616020a090e010b101b0c0b04031a13050c060d1401090209 59
    0x40004071403444258240440560b03024400d0840c0c501840501084204103584910800412115202c01c21741d038889181c4801034541594441c00c44040d980d200c0c843c1180d04102c0f6008084d5210350700190701e460340d0b01c0550091054003804507a404074130040700000b00311083c05035502051007078856018946e11200302402c1d40d142142c1c8600d450395616400c00118000e41c0038017405100b50481510380348014400390000c1c01e050103024001c4d40180d0060b0791042d10000b00c1e03c0c09008164001c101040e00d03200001e0320792141008540308214a000c0344000c600d40f0382c0003401041d400c400304c050450403940c0800c0030314801d9445159869542e03000000e000d0000e00918501f400e0131181c0c080c07103460540e8003600ea9612602c130700040c000c00c000720340d08000d8021500c0b0060464101400d840c0c42c0c3d24a00148800c114200c1c280c1c03c00348150114a1f01851440100c54165104021f001d040004209200070b5030040b800c0600c081392691740300340190340340080040c0a4000d1500c05030381e0314035440900a1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 728488516 1250 728487266 728487271
    0x41505091302010c020904021c05030301090c02160b030601020a05010c080a110a0f030b040e0102070807020a05010801030b24131d030708121e09010c0e0d15050709080f060f 76
    0x710410000012001030781e0000303102140700c0d812203440ca1980c43d076001040d051100300303d41d1662244000c0b202414448000042c5040324240c2000f440040f00c9064100d27241e1f030122280e20300c400b0304c00c00140300b0348502c10003a41d1300c2101841120649135198035064290b401e24080a400710761180240f01d100a024020110001440b406c03c510745124420001c00506d18480310900f0140d841c40004410354494004140d41d000100003503445021b2030400811950001c0c4040f449808207440c0040e0075402403030882c0c1280e070040130803040307a030700e03052401482000700c0c0000343e100c8107084011010f6521514141c12951007100e000992080300200030a00c0c0d01e40c4000024694001d018110008940004071104402c0c2210000c0c55521100c5840c044003185603402d4266010f20010030170803907015405502409501c4d540c0f42014151138041c082505d56071107001d0a010324036800050488610b0300715036000100340c0f6280d00c00e50ba0b9030000d0f504200500f952103030160045030900c2681c0b00350301003154 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 728489766 1250 728488516 728488531
    0x3060703020a0509040e121c050f060d14210a030f0203060f041a060703120c05160b0615030a1a04020a0c15020f07060f0507020a12031a04150509 64
    0x40c41d1100420000d011070042c0011548a1034a80d1503003030380c90740d0a101e006050047c0d817503519100c0c6d690408241c503d807013084404040718035240c0001c05d11208101601c1c018800a003010002c019241c0f10401080e000021320f056502c10300c0301500200320110a10b00c3c66034466101d15483d500c040000038192201440704844842c01802400120355400110b5810110704079030000b40b1800ba8144440349000c1454100d50200000c01d403c024940c0101030501400c030400c03c100b0110b007410a082da4280030f52003150207044204441074000a5103116250380112000301400e921101101041b060344c0c0c0115200041e0326210300c0140070483c4580c081059586003100c0c15401c04007203010007044008101e2015010185d620304200d000c01969045801c2c00100d03c010b01c0e80c401d01820440040c029090b100328549180200103043d4a20120300c0941c0e803680b00d050140e40c01e00b291402c5000c4e00008074041000d8151004078071496542e8425480c4440d007284036201e0341858041041640b100003030160 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 728491016 1250 728489766 728489771
    0x10905041506030203331302011106010609050609030316051f1a041508070305282012010f140919122105010515090a0b070f2003060703 60
    0x144010f81c0c5c0480c841c1d018140d001c02281e0300305a60b00030000009a4500b002d084040340c182800311510010303000c038a849000f80c96803142103201c2410199152002d00ca258000703000c07450f091010307180076401098080d10040c21241461501d05041c1c048440000c8200c41e168064508031070b18044a0b681845a101b4407401040400035120055051188495a05201d80c1e50380d4128040000d41c81c40c1c03800a89110411201b1403526483c080740e039a610b0b401c03007021086001c2500d07800d94140c0e17881580a603500c08103144241c50040e004141c420100001503501c5040c421070030998042c01d107d000001c20000c4004034400d40d4800d03a181c4e00e0075002d051188245c000345000c80d03081203000b2500304802d41c4101c4000c81500314480032910f500a01800860180046420311041003150b004241a200c086809840c0c00b44a4403050a56119502c03409411200c1003004000361982d0001030145540540124025520b881d035800a040802c049030700203984040241842c0ca050410442c1d030f00c8103e50808 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 728492266 1250 728491016 728491019
    0x2060c061902090306161b0b092a0d020103060510032009150c0c0907120e06060d11032e0506180a2c0309032104031506030209010905041506 62
    0xf00c1e858850003015406e4800c441c0c80c411600510403000c2c80040c410303250312146100441c2c45c12401d080d0050355001041d00c0780030b4280d84155080c400880e04903c0340103440080400c03200500007143d411820580c1459034400e00050640c41c0c0280c140801d14081c5d4000650200705059009095900010001da0800500c85011561100b209002d84078291031201c80e1a068400001460100454541500403100b04248080b40303810020b6901e15905512044c44150601030099565200840d0320a600508610b079020220b0000c1c0101025030308081c0540311144c1c1440c602c0141001f4002034012100d0706040c0d0041d403980b2602c0342941084040740d8000d500740342c2000d254a200744c007a0142161035a602401c6000403006200280100690001075100582c0d9031001502c0390030041c2c4581c00390043e5040e43d01e52841c407811504000701420035480c10141943c90b002503001c0f500c070f81030001d2542c5207004009603480e034600320b0007858070030000701d19494645090245048042e84007580c44d0b051440 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 728493516 1250 728492266 728492269
    0xe01110d15270b0307140f0103050702121e1815030c0403080a11010c0201020c010b03030c060a0e03041701050415090c03020405060607020d0f02090906010e010b130302060c06190209 80
    0x1c2e6038002003460580b004102c0644803403030300502c2d045030070130303810b00ca440b00c000b40704541c10000c00d42480781225100003240d0180010360030340d90b04844410058100c5645402c034032007080f020704102000c1704440340d0180d55010302c91006034055981e040c0d0440700d103202c0711040d141042d149012400c5c140e0100d811410551035140d03690040d03000050480303201040c02d60100d4843d249944a81a8240c000d0002800703060703000c0e00079800004038004e0b550a00847c00300908001045800ca2000c3d03800a20701540c0d0b20440c031000b0004103603880746a020400000504100c0810038189103100d0200004d60b03800c00d440c0040249031000d17000d520b1103040200d840b01090b016044201101e4042c1e4020801e599017400140d05441082c800960103005c00c0c540350148582d1000f031840952007640c40350107030b03280c4030b595a03500c8c5400d1040135117114880700144068076000c409440030031101d441811149840e5400511660070880702c6d209540e201c6810440a0144807610608005070424210f00e4000c0010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 728494766 1250 728493516 728493539
    0x180d051608210411040b0105070206070b0a15080601141002030702090702070506070501050f0f060a0611100903180b0c0c060310050916020d180e0a0e01110d15 70
    0x160050000c074000b04001d81e80b084030b02014210041c1c0e16440103518034251a00e032030310f401d0003020302c0c0c01189045000c41c500d500500843c1d030142c0c7c00a04a0303041602c1d6030343d4854200300003410300249648441407074402e562079070b0360440903101020240502c1c0d030609151400c480d0250594030701c207140581c2c0c800511600401111021a01542d00c051583d07100c2c0002e80c642005903100030307040701b40000e030307001401010b40c4040d000720005800c0d540503481d003100c8910001001d581c41c039846422a80104881405011170107080311440066400440440410b081114903040c0e056001c1080855404034401044404401400001418034200070750724031156070302e070481c1c521540104000000b00d840ba140011103040208002085600b491400540781000154081d80003070251048202c886200b034052402402e40065038841411707064a0b00031074011b240d0001d043e10300c015681d82d5029a5071341c800c0c01142c02011081c041d0f1075035614185c80c03010454a0318000c9060100030801c0a2005041d40c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 728496016 1250 728494766 728494807
    0x4030c111c0311120a09140405040201170405010e0111040303030b01080103230f0a06141e04030507030c020d030801080c0a03080307080603030d0609090c15080c030709030209180d05 80
    0x1403500c3c01c6900c00350701c8000d19002c4402d544000c07501c0081005d0b44030590005114081c1c440e04d03000b03000745503038903070520003544ca0a4a00078041594242c41040d130301d4602204a03031042c0180000700d4188481d800e16070868030300c4513203501403500005050080c035415020346c84140c0303020300e0500c1d030540c51519101e04204a41900e1942444251883c40107100c040001c2e40720288cca00943e400007140d440c0c440c2c01082000080803c0c004c0010000740200000030315824020440500022959102e030b03005c94250303001c001304a041c0520358040c8000f40e1214001200014440d80311081654140700a891900750110b170901c0c81034450009c14000515203900784c941014260801c910140c44030000a030641c09007002880e615868090300144030407480e04182140b501805c140c103840c07903c1d0300071007865980c001e1410f008030b000716021030308903080c2c40002c40d071040c420700e481c403417071501d903800039007540c006440c40026094107801701d409401051180c007180102908065140c03124208200c907004050 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 728497266 1250 728496016 728496023
    0xd0506030c0f1009030506190c0c05070b0a1202120601020f010e03090d03051b01050a061508040321020a030204030618020102060f0c0715050711030906180a090504030c111c 76
    0x981034810035590086130307103501465000081c0d81c95450401c0440c40704e410107028160245c1d0034441902010b0340144003861400780c0000c060005c050900b25013500e150b201c01c0303c030420400c4146001501444500c0540800c042c00907080b001410540002481d0907a88501c540040c0d142c03410384515504004100c0300701300340c1559014407076600d13810151424040c1c02c0110308202d80100028824820661019119140d0070701d003044a90b44517850051005285031844e00429400d80104011034000c01002c50407009400402e281442419400c001342e800020b21ba002007600400c09204020701401004c10240812010503541002900000c0d6980070281000d5a030f0b0a9013808600e20050a03812505801d401140920140541000d040010071040722a040010076011300c1c2e90003060040f040b00c1c0b1500000b4909810100410a0301e204080c002c1c14031540103130000000a011100c500505210301e001c0e4540d41849003941c20000c0a10f08604101c81c0324142480c9480891a5020098190b41c0c1c0c0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 728498516 1250 728497266 728497279
    0xf060609100e10030f0b1b030f0403180f0f03030305011a070312020c060f04110a0b09060a20060417040509010b070f0b0f01061101050903031302010909110d0506030c0f 74
    0x6551040d1071400b075107608060080186000b0110620040d00034283c01640c8441c00003a01c03da001802d9040f5000c141e400038103a40949c404030780400d20401a44405014001d0341040f441c0d030324070303003941e03200c100d68411410721607454130402c01d00d40c141c4616401042d9071806103030301e1050515401198403c402c401000c0c4540b101814a0b02561541603c2d0f82c402c0b00f800312400c80c101003840c5d003020132003224101d42d808081c00000509040441500080303030014840181000c0350482005000d420880b801d80c00c10150b001070f004401440040040d00d043c1e0200684071504041c00c00d243d21002e8465500c10040040200300103a44691070307003604441320103c4994661081e440d00b1041c1143c1080c01070300034031501c0c06100e101180e004c1c0ea58100c481a07151442007041c0003003640d09030350741100c3c940607640041c4002215039605101c0e401043e44149081c0c1c2606131211b600d08110341c000e0300c00403000c102c0407a40c10510003e41c4a6203802440407402000315170311400005003280030403591140100d4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 728499766 1250 728498516 728498521
    0x20708030403240f141501081602190b0a0507022e0608032b06121401060f090f150819060f0903020a061b05070f0305090d03020f060609100e 62
    0x100880383c0c4249107050041e051141d00c1100d02d40c80040d01c0c070500941c00351070805010a00100302903903d058008410384880d000e50380c074252081929490041f00d40158003d401070780e884d80703944091484d0380c1e9100d98540383c01802c00c6200daa003200e500a040506540c0000d940005008490f491000841c00c4401d10324110348005c1d00b1507000d003505038882c1c0528800410460341343d0048001c001c0e5069824003042c241041600034080580e9018850090f190200c1803106010545622402c8003032507080002084d0305540d024601d1500806034010150aa914995084050f0444c09541980d5142020300d01a075820143c01c40d459001c12501c0060302102c14627030700d0030040303039070022041200d0b03540b404c000c1124141400b075115952441c0417144245002a02e40e030307400702015110702500044d42d455062071310b03a65403c035580e080d0180aa060290500030159582d4034141242c284030b11030346c00350010540d4941503519144015007894070030740c0b0701801c000001c416400c41c0021140712041c400b1158 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 728501016 1250 728499766 728499803
    0x3030c150f0f1508070b071e020d0503030619180b18040507080f0d05120a0f0c0203071703010312270b0423031f09052d010203010b090904020f1f020d020708030403 72
    0x8d44812002908400c08000c12001d000c00800510f2159205a5003080b00307602010b191003480c419801006500307981c403c80c40c41404075a0b80105001c0f4406044ca010040c2d030007243c2e1484210407107048800d41d1007103d050009110a02c6030341802001c4800070841048250000750403030240200381d540c20784007400010100469504500a44103840d0020460107510110081d00c07903010130015200804100031090702c882002003168100c0350028158841d2503a40c0000b25506030881042480d4151804581000b40790710001c0d1f140200b000140355980d96260004818080c4426100800c228186905036107240d1000b10745940c83c15080103001d00341c0042d000003030004140260001d8070520900c0e807109401b0080c04441e10304a0f45200a17080200c614120003402d0388402d00404a82510074000e034412030900b10741c0700d50810b00c01440110800d80c02c10228501c206109070600c503034101400360300e042c00e8061048541e10101ca10140c000141050300d41542c0780f065100060512107498003c1c50b40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 728502266 1250 728501016 728501063
    0x21b010e0f1c06020d0b120613020a0305060c07120809070b09130e0d031503030f0305061f0c022d100e130b0301050601080103030c150f0f1508070b07 66
    0x5140200220003015140c508111009401c005a4201820315001d2010701c603240800098403100e03c064003c0002352788039141c1c1510750b04031000c00c80c1c200c2001400071000600c10b0080e00c0c843c1c08680003c54543c1c046060481400395000c02400600850f403090045404004c5440e41c156030700184142c0e507032402407010900001266000319a1540740c64600203002d00007017450303040d0801d5a13030240003040c51a503031a03403e40c1e0640300c010049410205145070081c002d030400c580c400802094072003101c1109204e41c0004680420900000304800301c240d0440c900fa0f42000003001d158070203004603030850003d1401c20000e1030341051085510800c000703042485410b098103041400b90110700000076a005210151501c07009061195082c100000c2e0b50754417500200f4100e0f07426581c0c4030390b088050b40356500d4442180343d50100658581040e911131030254012101d482200eaa000203c2200d020092a003d80540d084175545811540701003101d00403403800d4422140d000301e001800d0b03000240380c0240 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 728503516 1250 728502266 728502289
    0x32d0721030f090b04020d150906061a041d04050115060c0b091207030503040c031406040317190902040902060f04030b09010203010602030f250606090c0c050d11031b0a0201021b010e0f 81
    0x230b031f80d4100441c200c1080032a0b005401101c00b00906510382491400d203025a5001c2d6000b959a030120f0024904030a6000f6803150f500b00380a80000079150240d44140c0407005042d130003400115100c2103003c400c02c40741c80d03051503000d960380000c0d2443c16000d2413070300d000d4440d90f0009420404007101150510050ba035070400110b07441403954801c00116890103072607400849040d80400e1042460f4a503511420403094481c018800044a5070641003a215000f07041c507140a0b6040703581e6130b0f2000c0040e258400204800515900e0040d140d03461443c04c6c101e012001000381201c1d034014001080310781d4000054134042c1c0000080300d6110000c0461003085010502d4290000851000c401c2c01884031650000060340c48006080c40081c0c00400305a4021080c00c0f80185a07500190003641c1c0d01341b040218580a9040300d05807450710003119500304441a01c0c2034162040d0f040405607000b19030701004000e204c04000314111038500078a0740081c2581c0c1d0103203161801905d105a41c1c004541d02c030340b210070 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 728504766 1250 728503516 728503553
    0x5030102040e0f0f0f0403080712050903030a0e070308040308071401050114040e0114070f0201020d1d0c030a08160303090813030b0603032d0721030f090b04020d 71
    0x1511141c1d11080c2d41d81000301501c6004007010f500001c503041c9007a80602520030400c0c0d035218403040c0c0380c5503400c9401f103800410407010403900d0b44003824903408502440d0700443c10a0000c684034240900c002d0119103440c49140d4047e804a0003c00c0043e60390001d0346c00700c0b83c100340a5030301c92070113040003c2c1c40604c5d1903080c0220f5282100110303c540c24007101000540040c0d9040020710f1010140300c1c2203d90b816a041070040c560070000f00c0c030f1846040294036148143c4000740c101500e99500000340c4260016888500c0d07948201c2588502e801c0003280c000c2c0c04100c00411542c581610740c1105840344a00c1100d401c88900328103400e140c042c0d002010950703401400655507440d070304ca010303000382c0f0745020485416400c04013086c803074603000042ea0300d09910304848452440b030382050302450700e6050107040c1c50b0038010321180000c81c3e0310b40e064101c80e201d44583c0b081c1e810031055000f01204c010620700c0f0101c526040d1024041002c40c0c0c0205d0f40300f941541e48044050301d9040c100a002c0c0014900d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 728506016 1250 728504766 728504771
    0x14060a0f1505090a0e0a060509010b072316053c0607120509132313081c0501150c030305100b1317010b03060f0c04081618150603020f04050301 63
    0x1441c3c0c50040c11175104e6154081c04000450300c403401c20805035800e1140e5191400184048800300e09c410120800321849214540903441c2603101250510100840b03403c1501d1603c8410825400c0612200b07502c14002d1424681e417400030008100080d40042001503007013029855455a0707218101112200ea07081074000e242031284070b0000300340ea0301422005006095065448400081500800c0c3e0108844810729070072a600035034541041c0001450a0148400c031904900403901c80402001d0560000c0300745403210640250345015240180d102c014400d50120f002d00d0740c160720502407000d4561601c0d011032191604c1c103007030b03107800b00941012041004c00079243c0a100c49005a6000b122920340c0c00c03d40103202c40c40364038200d62001000b20707010b42203440040c1e05207444c03445203580302e00700500c007a013440d07140d20343d0368503004c080c000703e002d40c412910b41403000f0201310144200e040340703600e003e00c510303100703c4602401e80440f0300c1100d040c90740128a03644c0324400c18054401401c40a8002c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 728507266 1250 728506016 728506019
    0x40305031b0f070b090d0f021201020702210a0b071709101103100e07020f031303061a0a0303030209010c020d0b0f0609010f0605030c0f070614060a0f1505090a 70
    0x100c10300400c205440354031540918851680d400f00e290000c03100c015600a09101500051100b03080407001c040701c290400c629200d0042e0b4540c01542da10302003d0b00016222038842c0705100401003045148041100c1503503144410000c0002c1b1607030304940c850308603110b68413565025541d007094900f08001d6000341600f08000c85400107000d51501d03000340010b01c079840070200b000101c0d100c02d550807041c01c8900e00c0203011081d40010f8003500184a441111a0002452416811758000c50301085100030822420000d2291a02804440c0200c00180741403c1c5819000601403c0281c440207090640205802c10302d81e02882c040702c1190780281031002000a6031511000c021401c45420410f80d00b00701c0840c3d414201250300318144d03101104803524481c200b5400341c6403608020840312581c1000c00003a64400e81e014040c00f815886024042000b4010b1041092506d1006042c5802541f52280030060001701107644004c0350140410a20b2205901800315840e00c94403440d00c2d00414038200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 728508516 1250 728507266 728507287
    0x207150c2d05040b07020a0e0c0c06010605040510110c0a03140d0804020a0e040809040207050303151509040510090203010f14010302070206271906030e0102030105031f0204030503 79
    0x203215291500030a10801118051240c4181da04040c0c00000504140800d000b480300020040c01864001040c024940e559240102403180302203403a603000c0300010441c045003810800c10709004d007015051180c20b103420200412590310708541800204600000c1c00b003003510092182120700031001c1c041c0180140c49007800990004000701a100758494184c0103d0f0a51083c0042d6000d00c0d030040c01010800d00d04824000419000f400544086404114201007540d8a100404c50284074601540d1240341501200f1090007045d003106015407100c0c441030705004001c80840e940c06000319000101038441c100c0c14481008550840040c4600c00070020400c070fa00700b02000d081380d030803a4108160204242c011801d0340103c00c03000b50400000e00c4020304600f1080b0741310411840b4402e080c0b51102d40c0c5800220b81e007007100c6110541405400c000d01007198140525104480c6d41e100039450f6502d005d012990700c400f5201c1d510994400202112100040c640480c1c0086801c581100c0d1140840700 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 728509766 1250 728508516 728508527
    0xc02010815060d02130f050f09190504030e01021b0f1915020f0607020f0d0e030a050a060509150412050c0a0b0a06060912030801090e070b070506010303090e090d030207150c 76
    0x71501040342d0105c00044d07900ca080b8060b002d40b800035141c2c1940c2510380052001311800036003114040301c007209038442d074a40540324291285000360f8580c0704240480c1c00190030312220f1401c04140e80c400f4000d400f015101c41040d411090000c0c0e40034182403903078410398031070000c0903007041c0140c0d111360311103580031540082c040c2c546a00e050140c0307502d51940041a642c0b04c000006c444641d170010070340307692098081c0800c1d00311344801800741c3d01d130708940b0b58525007080501c0b0002c484403079592003480464801007001c0d40340000b0f440f042d520241011780304e1001c06080d01001c401040800a06500114400c0c06030f03a91442e4844031034540c5040c034100f0040030b40514000e400001e0000c41000407200f40c0c45100486c4103405440e645001d17403c042002d0040c00d0740e40c0040c0107a2040e550001440a070740001400803600501c00760000354103600c0e0003400100d40740d00c08640c0f08000410700c03003240004607102c1c1507040c841c200160303221070900c0c0c500003000c440f811103549203103404803034218550000d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 728511016 1250 728509766 728509777
    0xe010f02040f12050a030f0e09090a030201050601030204080304050f0409081204051002030c0703110304120311010b0103140a0209010e3d140d09052505040203070c02010815060d02 79
    0x1905500c030103e8a40c8519540080701080140c0194015140100420300981a5060000c0140340c042d00405007800400e08040040d03444020755400201144241903081c895203401031402d10303007035103842d140140c1c29640b8059402203902c01c8030340e0b4003107003002d54840c1e1000010662000325551070b0011a04084031810089800ba038047c0502c1004000d409064400c5a100701c2e203955074a410034616480403a046c440c0c0b41c80ea039050340700401012403c64046107004464034880c0e980c80c0e82d2103680003802400d50b52002d88441c10306003490707080e6010390008040d5030750240221400507156248000100d440d0b1241d0b008858001d040409000c40c041d50305c4081d40c841141c2c5008500480c000c0910070b000d00320b50b01c2d2032140040e0003d40d500e2052020040100440891751201241d04040703625080c0c24040304100c4500715030141d40100364120301128802c001800100e5003141586030243c0040c4c8440d00040e8004c0c1048240c10010743d510400482d02502140003404040d1212212900c1034000d5000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 728512266 1250 728511016 728511029
    0x80c130f18060612090302010608060c09190e040816021509031902030705121006060309051501080606130f0c20010207021f09030b040c0905070512190e010f0204 71
    0x241c400828400c400c0e030103008100e8110380e03104141d415800001100030258103000720b00315502c4110006803107008115050141203091106640c41d540001082102c0d84499072004044592100030420003030f414695540c416044480749946581c0c0060b1462400400034009611584084035400c2d002c60220180440840036012591480401e2071022003440c020b0364001d50541c0306800602072414520360b207800c580b0080041b640513106114444c3e00b559015001900000d54802c003100601404014001da500c0895800c02c185505100f5425160180240164020802411540b4039500c0950280395008800501040b0000d4400c000901c80d07070600c0c0d06c0407030303612a0100542685106100302ca611583c0101118403862640440711828401308180a09201c0d0070000000400c0300603d100744114443d02012032110b090045143c21a031010b041641080320070b0250f03800b951400710ba01ca800c501d003130f4180009088817103502c001529500c0204642942824101c50346016183c000d0400e0702e0a = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 728513516 1250 728512266 728512289
    0xf052b0804050a0210021207060e0721170c0102120711070e0f06010519020d120603050a2a0e091209030304092301060f110708030a080c130f 62
    0x1504441296441010341d005041c6400801024005190501507400c03900014015100c5900e451040d281c01500075000699040381c6445014010300c405104580140600284861542a070320300f010701d901c0d0905100404214a40303082048045a040c19201d080640100075035941c2e05d25818070401e40c80641707040d404200da02814142000c0f0206842003600c0301d02544541c60742c1c40b08000ca000b40d502034220fa040c004100311040310010704001c05000020640c00918142c6e030f980e04003c011a5070b104442205914113942400080c10101e8000310306604501c06004100001100c003000d40c0f98160032500d40c0f8001c038000582c0d41d0403440c00901c036081c007005480c4100c0c0d9130a0080d03d60311504250b00c3e4075400821003400380b801c0690000d004c4240030003440070f01c0062490000d00817002030b0040c2010403070104c449981164800f8603005100e4540000d004418580380003240e8a000d51800601408060300c001401810074100795402c8030801410162041c0d5107026043d007a1609009410303480c2c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 728514766 1250 728513516 728513593
    0x504050d0f020304230409020a1e0e040c0b09010e040c030608060c0a0e090403030627180b0a0b0d021c030f0201020a021c0c021009050414061008040f05 67
    0x10b00202c196000c035010242e00c802c4030341c4864442901e0001400c03c1c41c0c0e01c290344080040c0961504400d4202801c03400040ca0481c0b004d521500202020341c4d2302c00405400440104000156500c8804044070038820035141c40b09042d20050b2402c00c2104002a00586800c1104900540c150081c5c411603c50f8816100300352125080c84080b442074030060350100d00401c1091f5064107210001d41e900c00c0c0039150006120351a02d000c00c8a0441c030111000c14070552104201c000d12181c429800e01f03081c500c002c000860899a11003146010040092505541d182011202a2a41e9640d040d843d0b0b4010540405204400b41e2105013140100c0107a0001350302d000640e481038014400c640003250150028905001c00b40700601d0700f6002244000100909840503400589600d4191401034a0340c0d145c2d244082d05010900049070840c5110316000d0541e1010302555440d080c5000c0005190351518005035074460500b5182c1d8200c80c02e00900f41c0c8242003114241518800008040e0340110b0200050305 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 728516016 1250 728514766 728514797
    0x90d050303070e0f10140706020403062903100b0a0807030507140603070c12050c01020c0d0f02030403030912060b03030c060403020120031314030a020a0c1508130c090504050d 77
    0x4134074045550307400c9a0091011010745002d0b104100617076041c1c00302145400f80d642d40e580180d8000e0b6200705d0b0340d1600c40098030051112294072410303000d50110350301e070b981841c40c0002c0c1d6102000340070107009079580c0180a0319604c844010402418401080b00c8100c2d83e24501a035072030100d4031442294404985030301134689410f9044a010b0751203942c079641d100c00a80c54400d03614801d4452901072000030804c0481540c428005860102d4902029100e150300f1041c0261190b480020b0100854000f0002880082d800c40b00c8a8150340515070305188030700980c6401c0000705004148681d00d807001243e4048140000140342e840759210741e0007480551101c409000800ca60300d0700031817400c1c1080c400200b64401a42c030a0318846d0290807400103c2c5800c8988504551109001d8001a00400c2c5044140120032003e08010202c90149000f00e0f680080014480341c400b80ca40542d94800748040c4007800180d145031710140010a00c00c014a04040c949265034168192038000401e03065015415407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 728517266 1250 728516016 728516029
    0xa030e090105010c02090a1125020a0621090812161404030b01050607030225050103051f0501120b0307060801090c08040305030705090a1a030906090c0307051203090d050303070e 78
    0x152680603221480c25100c081c00c8002070000610010075549040c050034030180c0000001032740d20750794041c40c19550300c3d00e0300502100c0b141e140c03c07840520401640280c40c094010004070501c4420840003d103a81c0c0323600d040782c024401e4100c40708031aa0b007082032060311814902e0500560310b25450382e100100501844401038061480090030000a040040020742030440041864510a10551b26558020b07410700010b01901c3c13400010003010070a041c001035825104143e013041d1174240d42108084000003c1c00580b00e5030042c0c0b070403c801c29031100425906d981021011a000a099845554462038001c11180013441401030450400c2150341560307015000342070143d6019519180b85030785020303017030f07511f0340c05040000d07044501c0180c0010342c4d01c04002044c1c11424407201643d0740b07003080a00c03240f038000003038426446500f0510048003541d0340014504100c1d00103031030000041c0308540046045024202803e030b08945509050f404022000c402180b20b24119140c02541d100840248001c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 728518516 1250 728517266 728517287
    0xb130c0e0a0b0a0f2909041d010b0402280207090204080a1109040209010b090f12030c1e0601050103051503010c12052a09040e0a0503090108061002060a15080a030e09010501 76
    0x1008620010710460007440100100754102c445c42c903d8a805500c00105044840031542000071001d400d48841001a007801081100d00e41214107504041d0f81c081c80ca85100c010401c03600000008c000161600782c020b01c085401440310180840d2101d55520407651034123685030048039000c1d9004248815441e000000500880d00606a208aa802c001000c04594070854a0962101101d0b0005407555210200c03001040e014101a54890102d411070720302e40806060f07038044448038001c030f807640100000346090444409280105440c0c4614030f02d0640b84000000c0103825501b864000704000d90482d41c604141c040203074041106649010740345001d641c4481c1000c40c80524100522603c00340c0d400030b001c066100400004610008400507454074103c0317402280c00d03400101d240c586660308035000da54040740941342c85c0d064202d01c54000303440c3d0307000821800c07046907241c80c1c0c03e08846103141007001810b010f1046450010490074042c04620802106902c80e011050000c0340c00d520941d007260 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 728519766 1250 728518516 728518529
    0x2010219050c040e100c0201020904110c0d080601030207060504050a02100212040302210312091b0904121106010b0c011d0309011209170307021005040b130c0e0a0b0a0f 74
    0x140600b10380410019103030301114070702180302d5007840c0c00c0350b0541803180450300e034416000160703a42d51440a0005070741e038682c4008001c44c1d05216044150a012a42040300000c80c606070034203585007801a4024082e03d00b020f8503080c600800c00c41046000202c050103580202c450781c0d03c8001d4804101c0e40c4141c43d022405080c14103210400041c146100c07603d03150050041c0914070344074207003202c51950b00010007102180c0b01007000d0040200003480f06a0040305100d0303503055448202c03c01304080c2c40e406000201060b50340c1d0908880c40d803060200c0210b0310021410781e806540c0d0f4400760001c5400c102d040c80155403800341508008940790b9070741510410081c1c0690300b080009001515444116030960242d19100d06a04000036045100d0030740c3c0d001844a000e4036420410310003407800003082013440416203802c05000100e010480324603031299464200840c007140c0c0c0c0c54110b0700d4840d03e50108a00d010401c0511818503455000f0069925084d11400c4840750303250070750210000c0a10505 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 728521016 1250 728519766 728519773
    0x40b091f090b071703070201151409060d05010212010b0306030c010c11210d090f080c0a090507110609100b1906030f0b0d0f05070506040e060609030f0d09030201021905 74
    0x300505001c1601508145004401e000d1400c214202c0c00340384c0b6841201c4d0080181d564960480e200d1004460400103461015050400c0c040c1340d101042d12141c0c06842280304401c0c8a140204100c1d0940441d6070150902014074403559652894085680054500901c00d029101401110f5481030700c054909980000106a21002803070078484400b07504100513685000e030b2182030303c001008100030810049242e6400080ca413402c503949507064140d8014107084e403c44102860b15982d840640416100712034400545600c40340e4003500c2650311400c03007190034080c01e000c000e1880808540c541d14020940c0c410f120f90f01200080048459121440c3d21113009907460500c035552082e802102c180040340000918007082c94000f07120980034070350444101708004040c108220007800520001c100c159000e41c103007800d0041200480c44000c280c1405814081507030115a0b40070859108580e40a0013034901c00c402142008100d8a00d0340402e0b0301500c03c408210952907400380700d82100e1031300800903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 728522266 1250 728521016 728521019
    0x3040803041b0305060109060b0406020309010f050c0a140f010509060408031b030a0906060906080c0d150213080d0503060d020f01111c020c040902030a0f0314040b091f09 75
    0x504849400240c025074001c2d040c4400d4089038501e9800c07a201030f5004600504181d8903041600f01503d8058100d80c0401d013062000700803554001094030001202400e2844000c0c00d0f06804a50303030b0017a801900007500c600700103e400c3c0000160b01d00d112144590948450755041a44c00e03081e1481a150340d40760354001030007c1d001c036803050003440d0403210301c0c203001031b0002208064130f006400075110350314600d17540c3c5002405c01540344034984c01022070350000e2215a00d0011004c4e22462414185806081e187c0d60000820400302c0400c50b0100762007608544800e1a1740454a4140300d5015458541c0704070490921401d02032025030b882210b00408400d103d400550074003004034909809581441507181c140030300458140180d084000c1400d41141040341c844074000c3c94041d2048481d03000318038101461026880207e048042150480417108503a02c4a10f0220758903040d2946924245201140215007030f60700600510460703c00310b40c07480105408440050350b203448103555401092401c0d20 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 728523516 1250 728522266 728522273
    0x3f1621020c1002060721060e0708060d0305030a0207081e070210090308070206090d0605090c010f0806060a0e030304030602040603051033020111030108010501051f0e0603190f09150b060304 83
    0x2048440301188080c04880000d2081c001094070a07941120001d110460100449d1503885110b041c1d0115044403005000c60072928003a0484c80050b0803006880d400056100c18803140e03904031a0b200840600a10701c0071045101582e1035001044101c1c464202c41c80201d80d00b5100d6444807082e26004002646020140d600304a42584042c0b2480d4001c0c0f4404c4000d0042451440f80912580b03101c0702400115500300001040c4086940281d01400804002d01100e511003000f620141d03800c9040516501d00100c001a1950249510003084039000180202d030540e815000701d406010a0b01d000344080c0e885100c00c2021250740a81d00320610070200c49030a210b820028210280810748c0000030b0741c00711903075005609600036008150b96a44074001044a410024840042d007130b0511200d03201d11106440007080740c030030741c003180744540780c0031021448543c0401c01055130710b01004401c103c045000301d951006880d6031482907a2010f4000d180500142c1c15000c1c1000c16200180400d00d11354440d07a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 728524766 1250 728523516 728523527
    0x60109031b082d07140f2808010e1f0c09030516030510270323030f01050607033c180b040f051302070c06023f1621020c10020607 57
    0x301c010398048100b0035084414001d00c40d02d40c207c68821054900ba0b03d09010405003910f10315464649554040c1480c030555040200341c40a03201c41002c2c002c1a0724074000e0003203941700302c41e030005000790217070041100c8010050064442100d01c10000ea07101da59804902100b15100c002d0035180f4203107041d0041103446914104100594401e0070302c071209a200054030301540b015044941e81821000080c003151120b075504040c0100411604a8646080e6581c02048852801218913032405221030070014019420454445192509035443c070210032200001c00600d0440c41001c0707496903180c00401d8001d00704e002c0b603041c1c03020700810081d4640392a0512019031280480d05400580c00c0c0100d034006101d20140b48003c040990044c0810b0304030103030340c90107008100c01021010341c0c90f01300700807041030040c592844050340480c3c0940310b07131034018100f0849105a07002007000322440c100400488034002c01c9210011540e0840d0003000c00e090900c054030040100510141e0303c4100000d8226210340b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 728526016 1250 728524766 728524789
    0x10e04020907050a020114090c0f06030c09090a09120309020f0f060a1101020706021305010f210f09020a2402011a060a1107090903080c03060109031b082d0714 70
    0x500c0005911140647c4150045105941e11020b503080410003800741d1034a5800c0b403004203c211082031440c1004895418113114007140310b4007074600080000c0490207660310081c81c5035005003031032000035202e400081c010a80880201c0c45810b410741001403900f441080c150886030003501d03e91400070b81900c00c0d60b13640b001c64008180785d90200071210005040f4006003801c14014480b40522605080c005400404025291400c00c600c00003102d0018800005203564103119003800a4100301d440041c2010302030154019400c48070340c6000007100d501910300485800401140c2c3c2c60400032841049003640c030709800110405030348464030035140c50140300808506840c1d080c01e4100b555140d07015030420000b81d01010032542c1d2920400300b81a0001103c1e81c0c4014440c1800303266181c030a001a00d074448901004d081402c941c014481140e000a1914000d05803240854280d44a0100c01001101000001141a03c10309a0300c2d1903505001071060165030003410000030701d1070aa01485200c5481 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 728527266 1250 728526016 728526037
    0x180105070e0402160512070b092413060513050606010e090a05060a03020a06020d0e2e120e0f0f0f0a0b0604020706050708390d060b21010e0402090705 66
    0x5080c5131000540d0400548078034201c0c0d40709417a1540e0107400c001c1c5103080c00504600582e00036880d240c102d03001400e03a510100042c2c0824207000d0f140ca00c61240151042d0100900492402041c083d0044d900305c8403d6200b0720440840d0895070f901801115040355942e442d030b400400b40da0110311064460f0b0011a80130f403004e80655000ca5994000600e800e640d54170002c05a08065404888568062000300078982d06441c2d4104180f840c88070b00003000910304602c17a568540d40180138810740304803a00e02c1c1c0310b1811001800380c510f5000550340c40b1322541c502011907100701100701c206c0c60340105150807281c074828081c1c0800e420716195158030307010041600d03500c550308022450000700345200d0b80b0b0003030038656960b90311490003504582101c2c6a8071040c05d42580c0b01009051010340481803940410364402161b134654a0402640303001d043e2035000203140c80d074080b031010004900703440318102d400c514104820f0b07036076030b90654080d8150094030081e40040312400040c251a010380001c01c5c58890 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 728528516 1250 728527266 728527297
    0x907180b180d08091011250303120e0313050310060815041b1202030d14040b0a02070e01030b190c0507030305041e0c36180b04060203180105070e0402 66
    0x50001d501e440420a03007201056058014a0546c0420002000c081c011080269000c4002059840082da1148802402c0002040c1c8444803492260083e038203010b0004122a11a03031103000c0c1c640d0340c42d100d001c0d0034081c0c4180a0910445204e80c05441e00f10340091000d404e0241502003c142e141c03400410a880c001503048806080500b002c14860052000400300e8100101a01c10507051064a20005041203940d00080c0580035a0904483c100ea0310042c0746551804814020390074044242e104401c41d00080e8000000d0041206840d4070948905040d10440700d4007103e1340c1d08a6415400034800203c05010010010b80241d01c13494016001c0c0c9402c40d9100c0c240010591008503541d01207030301281c2e0400070003036107444072095000c204410418100042c1d001604901c0c40840800c002070080c1c031000d1007000c0c40a00d41c0e0242c0c0d8203802002d000c200c2d24060900c203010350b1050360817030b6119400c8401003050380b4062040c01c0c0a0350701f035034038100c40c1162030040001940080354030314000c82 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 728529766 1250 728528516 728528527
    0x50a0303081308210a051e06031e03030601020106150c061503050102070c051306051c0327051509100c08040f0816050a050303070813050907180b180d08 67
    0x3c0030107000c0e0a000c100503403400011504100e84040c6080e028040e03002c068104010f01c13601d2405a0105800c81c8031a8020800590f1203000003443d0801194101d06428000705020031250404001140306200030b030000d2102550340d10114821020070350006001801030f102090000300703190055154bd2808446203281c158132a10350508a03032215400b260031543c90242000f6506100c2914076002c0300d0321104103c03780c03030400800e0483c07135190011400b80d141141c071041098050005d1245200303a00502c00180005484221134007400750142500c50055a0016181100d04070211944e10f40082c044150340a040c51042d9116104010100c0e90350753b00344404100d000244c40400018280400181523100c03420003044882e00c11500481d0040d521841c0600860301c0000403180074a6002005680c0c803291041c4480710343d075080c3c01c01036002c40c1210902103843d51001d00102c405050391210b1501e29a00e44580419210f07160160088900e40406002d19141001c08a1150760081402501c0e04 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 728531016 1250 728529766 728529773
    0x306040b07050c0c0619180515031b1317030a050a08070e040c0201020d050a06060203040b03130606180f0e100f020d020a0504031a09060c0c010e0703032304050a03030813 75
    0x61b0042c410700100ca11400c494522080d0f440f90701c02940b03031b207040f40c030482c07050a00001c1a00c40078001250700e0300000000c041030300b05101700012142641601c10741c0d500c907500301c080994296443e20622060003942c0740700d0285000088100c8801c004a5140c0900e00006420107440312080103182400b4452009084015a101c2d409990000145a030005a9401e0f052103400c1c00ca070005084215271031324003a010311107607800004030340560301101075a980b05c0c0e9803006942c402c0c10651200910640c02d01500144013940352140840408000c003041c4101c09151460b54115800280c1d16807480d0311140d04e91100004581c01490790980d81c140151600c0c205a0b0320704160f0388014000350000b20005400c00c107000e51000c84a003052441e00c410060b0307080c10038015641d4900a031030128001000583d0b2100300900b50300c141c9280950200356140d00381e80b400c1c054500c1c12125482c800315602001524805e12000e0120780683d00c0081c039040c146030035601e0403100e40800809201d0320924454082010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 728532266 1250 728531016 728531029
    0x3030705121909030506220f06050f070503043306080c0f12070e22030201090b13020a17031303080405150f1b011e090606050306040b07050c0c 63
    0x7814551282e9902a80d40784103801c80c8030300e00e8a60820900e10340c184001040402d04513041020440344590403010101001d6042103d00e400a003203500300500582000b4254003c1803041c8944155001c2c82d0740c4080050f20144821034006000079003041c0c0d00c0d00c0d0031802140c04201282e2000c3ea00c01c0946008100408580503a000075490341c3c0559600003c0b0300e40700c1d002c00d03203c0a0a60b0300103014001e00c1d01c5035540341c2da9401110450320400e030020354508480c00c401d0a03107404811302074041d446030f41806402000340c86000e4440e04503100c0040e280082440c0c0480f14154058182c00f81e103441c02c0700003842c400c42604940003501082101b00282854546c024024500030114580d80e1841d040030446640b4640340400d144810a01c071240482256209403840420605039004d800031910211500421a6515112288041103810009010700c8d80c80003120074030401040005540750000c055031543e04070b40c020300c0b210018001074402403043c0090141418004e080b01d40b07803650600000c01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 728533516 1250 728532266 728532283
    0xc06020d0c0c1506031e02150a05030613020a020a020f120703231f0b240706060b03040512070317010605120a0506010f0c020a17060105150a081503030705 68
    0x40300c84020005218184003c884000c07041001046030314a584d54007009550502441c2c50f100e039002c10b0a00642d02d545505c3e45040ca503840c512543c0b04a000c402400e56081610b4050094181c25052256001603100b220001d102a4005095103400b0350f08000c007085c80c1410031908854400c20450100d0070801889002d14410310500b0700b1304851038205101c100004150380910b50000c0081d0070310800d00151460081d00d01c0340c000c65440d08400201d40c0003030011a850701391144140c807100809850b100070701841c0d03101d900d040c810180d54900c0d0f8015400144c801030126080302122407002507021000348400e602c03a05203021650740128035146039880c2644030101040000500c80b0400c600501c003d584284c240d68108064200980000c0060021040240134844c0d0107040000355075030001d82e00020f1450300e504150f0385490201094031050f081c480ca902422682034694002c0740e00c0c10550b000480241d640c02e01980d61141024407070ba00301c40301c064150108009450114000740318811 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 728534766 1250 728533516 728533541
    0x403030902010f020303040c060e1f02010b0a0902040b0a050c070b27010309030e060c0304081f050f04030509040b0612040308040215040602150a0e0307030c050c0904020f010c06020d 80
    0x1000c505a00000d00410810701c02c480c00c54004108100002c0d5546420209503002482c0c170720343c90400c80010980005404403424031081e400308454404560540000c4142502a96005c1c0407503a6241010160301442c05040000f000500a0001043c890702c081d240542115044410031070b03603404a90342c00c1d070081010049072800c4007149035403d92030305903803c8003ca0a00c1d0400401100e034800030001a40fa014941c8a50400214821080b8081080d01e000c0d06400e4160317204030018170389070006540380b905007280c1c0606100c001004c03c451405032a1203075405031119458080b0200c1000020310400340c0c480c0d4010803d0080001c001042e082d001d00c40c0380719031a05180c40c1440d004019a48104001541034040c0c00c110a100942d4003107030100210000040305000703034589860803006032030609110001480b01280c09002d06034400031800480e03014206031400521100144114100b0865002c2e40001010300307004610351080c890b401016001e81c0c0d005080480c0201030009681c0e280d400304 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 728536016 1250 728534766 728534771
    0x60403140d032901030b010e1c140606060d20030a020d06050a1203030b042013080118122007030b0901092a03060f05010602161410120203040303 64
    0x5200540620a01442081c0842115103140ba242c0c2810403001810407018101742d00da02c0581e03901d0b401004180e11010300201001205e040c108a0324034502200e0000f42c4110307000b20300d40001d0007004200f46000700000380009141454140c0e8420240c0504007803803009001e07c200d1081402800130145009150340e00780036a84000c00e280341001e69855400c154800e1994180810801c00c1c40c0e900000010b0785428041030320802c28001600a118040790500c1c100f0b000b88445200c2c84100c00246010103100c080b9201c7c0340d03110b881080c203c41082e5640107d1010000000c00400c0204400010520681ca45140d52000407040c0c2c1d5101d0340207240160702d036840181c09000700002580955072044e90344008000e040d99540f1501d8541c24030703240300b80c0c03918480030300450442c200e05501d0b809550408002d221181c60000781d80010442446843c005004100d102c0c452100e4005500d8110340150009422844a46081003206000044040c09205401d809620301030b0042c0082e6216501a8800 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 728537266 1250 728536016 728536033
    0xd14160e090c0102070806011a0403120809060f1603020315040e0102090a0b070809060a020f030c1005070503100902031807090204050a0b03010e0708130506090a0201021c12090206040314 82
    0x9042c545070b10070700d00a066400c4080d06000700040005c5060444c0e02e0302030012410403e22440200342c0c81160000703003e840035a8191505140c0000360640901c85030170480c0c545076600001e40361448400d8030100414401040b514541d00e22980195801000318943c00d03c5803950381d00041c013200c50301c003c40001e80c1d4020804904501d04599106c00621200c89001c1c0703001480e80d2a01c00b039118800b1024030800001c0341601c0418405c000a4a1b1030040c0c6080300d5031751007807031101580d5007014140d1458040c103000c00140305034402c0040e207026a40c00c80013042c0d0303141031011141c040c2d0802000781c0446035000c40550355010003005448000d00b05690016681c1d130a0106101480e99550031040d00d40100300300410144108102040c2d01c100e9614000042e925580110510071000c0b0314041d00a100c3d00b0140910b00c032000c00c4c240c80340c5100340c0885000b003000c51044c0c0c00e014054075072180400e810700d1404150140c01d802c10310b0801d100400a52403d92603507a05181c00e00d0340300d6400c03460b501c08040c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 728538516 1250 728537266 728537281
    0x6010e09071701090b0f060a05121e0606040303080a0b12030f1215010f03090302011d0c03070614040504090c030203060c0a022a0607260c010f0b0d14160e 68
    0xc42c5014028010342480140d00c0c00e4041483c120010409038002e510005850118034821001d03a1500c0403844000b0016040c21113a5681030040c88e2800c486101984000c1182890b2000898040f80d0380350b100c1510030b9460007030702801440254a916000914905041000e810a000820b0580181d41e40c15480d060740b9842041c0c0940000c1c84041510318105080283d1ba03044040e031482e8255a1130007203030041c0d2525080307000d01301c1110302200c5049030140b2040c40b8407000c29110a422020340443e0405669241c0c01ca6501903000c03d101605003080100380b00354103094000c0c501450150922448283d601d501107440d18500312a003031070541c0042040035029038148841da014160118111196007001d800310591440100d08051044038005040b0341048419100747c020100c03004541040d0b10071920300025681e0250b00c00481652030b02440c201d00310440d128903a030100d40070307054a10307021030340c2c1d100c0d1004070304514510302c6803140071241c611400e4110004c3d0040c210380c0100300340c2424202c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 728539766 1250 728538516 728538557
    0x2f030a08090609030921010207110103050916090c0e030d0206010608100503100e1c050418020408074208061f050f07151409061005010806010e0907 65
    0x5100c00780c990081410310640d04000800d40b41070b80002c0300c8682c44410030840844400c1c01901c0680c0300382d400401c0510a0040d812016442c000c001c1c0c8007480982c1c0e803000130640300c0120544200c403914441000703000f0010150300210300c0031081c1c10404d10403607070000024907004c5042620001a4010b80c01400705035800b02625801096855000f0b8400b070074800040e48556490400aa4032a03864144441c801010494075140031107400c015003500c0c3e8120401441035225024008100d50141c6000e101030013548212000c8a803e500a00869418808081000141488441000441c1d40b001c1d0088800c01c1c410680100420503c64941c0540d01d0303405004014000d14070b9101d82c461129030440e220004000385491100d074903141d0361718184a0355040c800d01a10748050300809142da41c58400c3d06642c1d219514000340c81c5003800642d510405903550b20340d0100c40c030413007803088482c080045500806880b074000b0f405042552454110f6804103050000c101c070460001f94004080e146c040700040d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 728541016 1250 728539766 728539771
    0x221205070501110604030503070c2901120f060f0b130905011b05070201030b06040810200403020d03050306010c06020f070b06010e011b02191806050a0509072f030a08 73
    0x81c00d15283c680000305525480f244d000b0405000e0103400000110540d10800815420603402006224100c901c0b912000b07242c4c0642c40c00105d40c2c400c034000454100512208011290351115074a503201840e0f90303900014102e55010b80401b541c031803000d0203460b81c641c2c8041e10b0300c030030315400010844503d0420b1400d40c2c0036620540140c5031000003603a0001d903c10100d401c541c2d02030030041101d0029802140961180d1781c802040c03401540303802d007060600f0303820034203011000300214034110520351442c0e80e0901c118070000b5442151010300000290041028541c030000504120740700860035211f40701640c2c00160450010040059140c007001001c210715a00024280313030040c0150650400030b0f04010718422040d100c0c5401d002c5007000c569603a00e8424516680d056442043d5503510760b051240400307041000241400d080c07000ca401d060a2882904603070001785910260348a030007040e01c0b40b4050504040f40e11601c202c280000d652210003240b405c0746900c1c0210344d1080255001052000007 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 728542266 1250 728541016 728541019
    0x90327120d08220209090708160314162904060c0219050a090b0d021807080c0f041424041e030506060609032407030f202212050705 58
    0x40e090302c2c507190a03203111aa0113079042d191140c454462244240c64810103510010781445514504c4a044207000c100c00100da1040000d6907090805450380748d243d002020700c90f5030b050304814042240014002c0384010140b0882c0c00103403a00040a04542a9071090300303c00c1c040341020020500718140300809141c14072030303c5000c114941c00d220004040e48134034401d804005440d55007529607603403035045034410030341c1c02001075561200907880c0c1d04101104490701c03008120003900141c41c80c24100200c8100c0c00e520048a0310300740c18803e112907640b000300300b050341005000800684030100110300d1020411005d2505446034130b481000d4603200c10382c00039a260305141143c1000002c0d000500e40b03800081c11107401d912400e0340c8020030b00d043d02d80440c000703a03503c0282c0110108009070010314003031503440d5802e0194000182003c002d030340c141000505d540006a001c0304003c03110070090000c2d01302c0c054403411003130307403510a40200b00302541200100302900030003201001410006603000703040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 728543516 1250 728542266 728542291
    0xc060503042316030b10080604031704030918050f0117100216120c1a0609040212031c1d0f071206110d020c01060e090327120d08 57
    0x41c9a0784400c00384120100000703090024264040000a080c4503140d41e52a60004124400b81d480c00d0001400c14151409511400c0140001c100c0500124006100300d0f0581c464009410203034800c55501070f030041c816402c10040c000e010585c140d0403103100074404e41200000c0340e1403c01610108039403606a1054204801d13083c440403ca036408a00c110f0504240600180c0311005004485035014512000a0419564190100b07010390080955603000f40503040b5800e4183c4234400c203a01e0024281c85080d8010403010001c3e00606c1d06001c41c840c00c800d010192801c00350080c8900860707c49603010881280d80314040901c06000f800c9041d500440804010401000000480ca880790703141c2c0a4200403004042c00141400580e030007041e0320702001060b00c0d548009890701c4030003d400c4848945d490354205140000d031180e0a0f142207009800c0000038500d0150b0341340040782840700300002201402c004030002d400903a03802c1c0913aa0305080100280040f00510700f402000c50800a100d03480840c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 728544766 1250 728543516 728543521
    0x406020a1701062c0d05070303030f091a070c210216030c0e0a060b0d0b091302060a0e0d02041b08090102030c2703060103030e03070e19360c060503 65
    0x194818500991119138685005003400c0010048100f42c030f11100d02038000c016800820f0802c0350015000d001c0728040d43d401c000c00c0c40e44500b008180ca0351b5a1014054a0083e20448045880d548003039800c4419070070014005800340e66a012114060f14a0320a014035180166580c1c82e014031241007030384800104a407050741559550004006240907003e02c2445040002c0c24001356a40040d000d41200382e005901d90200fa0040e401030a0f03007110190250341c0410224100303203500c025410406900034030281c1030032180413044900000da82e11752648410054030b8900581c40302d214610f8404400030308101c40514201d8058031919001d411030040342c0c410001c0105500606080d00d0140c404000400f40720307144285c1110042601c182c0150385401110000030805411244c0c150f0580000d600f5201c2580d03880e4621002c0c0e2508407090b00804400041c0c20302e00c900c1f40d40c02285505044040240d442c1c03042100741d40340d508409190031107460032012240910091544000c020841351414500d540b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 728546016 1250 728544766 728544779
    0x9070602071d18150f0a0f18020618040212010618030f0b040305040806070f031b080a0b04020f0c030a1b030e040509031e1e0f03010b18090406020a1701 67
    0xc00001c00c209890309100c0310200e10000c050040401ca8584024100181c1c00c06810017540080291040d240051030005141c26105e484c0c05180900c1c081c68038045910404c40d000c0c04441d5001c1c1c0401b10034010300c00081d810554407440070b00400701203003a089055605000d000303000d1001c0c80601c0701036a6200380003000001c89000c1c1a508545d80030181c42c5003900d8910b425a01c0d1300558011840a020740400c00850a80c080a001480821941c050040980b0b10705514401d8140c80d0981380012080d0000a02050094020007041c08000c1e10061419a1082c0d004d0300ca07400c010f0444c2860b0f000021030048842e4400089078010007000710442c07a0614030303500038042c00d10b04e041181c011a01c0c0c1c0006283c0040c180261500c0c44d070a16880e051100391110420074603400344500d25040a10300d00c2c40b5040c80000000d5520200e0101c0507113203543d081521081c00d07138102a054841010440e0080c80294861040083c065841110f01580785e441a42024141d2251000b908031848600030040004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 728547266 1250 728546016 728546069
    0x103020a290d09050d1103091e060f1c0501050f042f070b01090606020d0c06060503150114030c030d1d06070f03020f0c03030f0f070b0907060207 64
    0x403280c442074aa49468402044408500166480819021008a603600042e41c0a0b040001c0300d9101d10f05507100d100307182006640f0100a07100c55140d9600520070100d031410706d043c80c96a1000f095921000040001001130b20a5110300b01c18102490b01142030b042070b800d510008000100c504909005a41c14140811002e205521821780700366220b180c2079181540f041c82d0f14500b8041111011003030b40c0b80d0142203d459100c51011959000030800014415103e4450f20307090768881d50240003069a40b0004546405108205840701f039a280d0000038955402c1140c0284440d0364050b03805198507101c000c0b00307100c41051926002c0c1e00500d03180c1c0c1c81a03070040b50307a0082503001e0a2a14807111300203018400d061100b00d0503500003c00040860034441c07110401c1c0b903d41d12075400c0b2040e9589110900d0b443c0d1100907480d0380c155006114484519102d50041d10001e5904011642425002d46510703440b00000d50303403134050b5003003000c040c03107465414083e034006403d80c0081020f00c014030f418038840 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 728548516 1250 728547266 728547269
    0x40f08031c0504020f0a0b0910050313030c0c180501090b0d0228120b0603072412020d0f0b09060402070b0402040f0603050d050d06151d150d0b1005030103020a 70
    0x5582d00c200190441d90b0f074109801180f0f2001d85003015140e140c0281065a45c80410403511595603c100b0481c214400c13400c40744210388102c8604d94010055600f500d85410310305088940c241d0205c0c000c0352200340545c256516091001d400300781940b626903140c049410b03041000d8000c10642030500050380322001c000c042100c0d9490b0041300d02d44010340b5141e084c0882d8114188812041c0502000e000100341c4403802020210181c4005942e42d02e40000d40d04095070425080403c0855901803003030090380005940d0304144d40c09440c0022541c024001c460031440007100d06a07940f205e01d0303502d007842128694080d409a6045240c0f4480e612400c4040030020002441561100d00041190b11280c1014001b594000304441c0e200c1700c40b00740a0041d8101ca400810312901d03182001031040c400b4000d07940300c03411903283e400c614444003039402c0c00842841d21043c4c10000b19685641c0a0b01c91600401c7c0071070055a000030b00700d12a00c100400700c0120311034201001130038001480541d80701c0e1803200 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 728549766 1250 728548516 728548567
    0x6190305101d07080403030f110d11120106030b0a150c0b010e10050f0303041203111c0f030207050724110c21120403060b090603010c1b14070605040f0803 68
    0x4005c0d42d881c9801c9000c0e2917245000f642070340c2040d0001a1355038040c8094030b511710810340107204119903050003084030f00a0801c10420541048010082d0078001d0344003040075400504040c001584400344200180d0160b00c2000000c0c07092024001880b015403039041c05407054141c00300b600d007884800c82c003144400c1e0003514410034183e00c2d0418150340c00c008940007480e6100c280c41c40c00c0f40364100900320485008a205850191000300081d010345041e4006070749000d03498030040b100382150304034001d4002c00c00c11591392060410106420a00001e25108600c0400101c00c0c00501c44000070211078000d2010105980a40c19210341991000f080740c0c04d5041a01410500c1046024103a00e41081642c080304464000a008411300c6015040a40d82002c181c508018940354042810308990798080b400c03000590384644030420007860f001014041d4020501d098107180c82030b103d01c2c140385680c0c2c0424041500002c0030031044520311043c20080824501460820750b06050590031042a59a880c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 728551016 1250 728549766 728549777
    0x16081908060901210b0c0309190209040b0408090405010e150405100611120f041403030319020a0c1a07030507140711060c0d090305070506040b0409090206190305101d07 74
    0x21142134000b08030258150304081064070606100d42891015403003512113480070b014085910034400c03484410b0b002d185901824449039556141c070380340c0104101800450b480c03c02003080c45e05603520b9004050182484209840150a0041c071600c821500600c001c1d02980c18201001244041e0a5030030b02101c0d510b08121540058200025040042036a1220360700100440c8c24451801010080c006603410140ca8205d06460903040590728081290802d1050925800f914030542041d000381c18820703ca41403c00c0d400005642d05403442c183d045000030035248040800c00c450b6454003e083d08080982000c0c0140c03610b043c404001740c492104060040c0940c000c007030540b501e4600454090083c0031090b26076120384002e0007052040984401d54051044180100c0c0a01d002402c840c2115a66801c05251a00e080d01d0b1001404204c90266441a000d12542c0c101c00710300ca01c607120031003a50f5070000d0b0303e1070002c500040e4003400b5041408000c4180d142e82201e00c0c41c40b103006411610a0a04 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 728552266 1250 728551016 728551049
    0x7060203040f14032208210c0706031407030533060a03020a0e151c02281b02090601200714040b1906080a0216081908060901 55
    0x480000150001c02015950602c069401207400880a441e20641e60780c0c1713000d0100c14410305101c032294140070f4288990441d00b000c61a0f0a901e218030000403c1c01e82d440c508080310700c2900c6081c24810b030302640210380c94242a03840c1c80d00400070300b640070780b050604000c541400d000420003c03114a4040c001c1c010071401c07070004400c6c22a0845203204005107903640d103960031400200a0740107002008081641454091050703d00b0701140c1c0790b1240d8a03000b4509140c1c0039501c1c48882000d415a0601450303080040d8031000c4400c083c42c0c0d698403014000e0003201840120024035020714082c40b0291110312861078401a40c0d08445075800c09424605600e01601415458000f0440d10130360050070721490700002070710a42800718182c07801080350100504403030007041c89001500402003e02500da090024010780c1d00039400180c01102c000401410090111075882c3e00b40c94201c000c0c1c1d0030180c08129141c0e13021038603074030240900807450400c0c4c0342d0500a002c0f031410981030003201a000074001c1c1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 728553516 1250 728552266 728552273
    0x40f05041b1b0605070c0302010b04060302060f0d02130f1e05090a0c1e0905010201140c1207090b040914060415030215160b01030b0f071416020405040308060a15050706020304 77
    0x203000b0345640c11203001c200c0707418128005002012284011805542020280c1041d40b500303105c3c000460b9005010789142c5440c004404800c0d03442004400380a99003481440780420301e83d04081c0240045072003d0003030500309264141c450034884006240c401e110f040070700c12074a40782200c60300100d0054001c81c803d002c0d00e07402c0d03031941c06d8491803560814840e44031842440c0d01c42442002c450003a0005c004154050000c9a448401140c0c00029001708000c1c002d181d519140032680e02001c20b00d000c685007600c034500e29005074841c0e0f014810030f81c0c603050a15106c0079080ca0386904001c04480030010308415104034000c01005100203440303521308010b442d90710301c000c4080f610101036101c032020f402c0740c903483d002641810038002074540300d94000000c4c051f00e40808000d805800f035030f1180041c1d050341411680c155840200c14540740603c07840801d00603221030280c1c6000c0c030f101380c590010500d401004d010b06010b460b440ba18001ea0001c00b486603103504281290314964001c1009a0781e5591400d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 728554766 1250 728553516 728553557
    0x4a0a0303020a122a0906080402120c1002031c050103020f040b0f04060e0411011106011e05040914011a0d080d020906040f1a09090c0702130c05040f05041b 68
    0x241e6560480c1410107540100209103007001560454060030712a0f0300004e013044946500c1030148001080300c180c045000352804145901380d040789281200e40449001020841e1032960400313140240c1c1c004a21420441e107881004008200340c01d07010041e561450300022000103008000303a01a542c0e54210b001ca03500c40000f1a81c02101c0136005004241c0da0750760f030115600b8210380643d00316010107050001d0f98880c1141d03107604c01e441401403441d0707400e0031091440c840d429028a681c000d40c0c00800038640c0c813240941c0e4000c5025410950303640741c4004a143c25a145040d10000d02505441c0c2402140d0f1101c0540701c0503070b04946d85a03119095008548020321895110360ba001c9408940000c280d814441c40d1010b44244540070080c1e0b0070020800d02a6000b1700070016403042042002640000392000030340319950005020306000c0c0030b118080c0c811905c005411000044000070203200883e150100900100000c1e5000c1094085003008030a040002c50b000d2010031071443d103403004090041 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 728556016 1250 728554766 728554787
    0x21e0a02012412320c0d08031b0705011103010501080708090601140f03010e010c02121606181b0501090605040e0a050711030d1a030619050a4a0a0303020a 68
    0x881c4008541e441d0543c2d004c605009580942d11505c1004548052030825102c0000728a41c0120014256110300403500841c0741034240fa5400c8140500c01c0c0808a0b200b401013001583c007100082d0f990354101400104801c5c00140440280301c40b03901442030025000400d81d044445500103500010b658100081030b0300c0030003024944c59800c01000b2100d03280b040d4084010454245c0803a105200484e2038030000d8040c0390600c2d0030110303c0881240c081030b030343e411060501c00d001034011510704455541c13402c00c8540700600c1c00710044c0d4030800d010761350700180f103c0090b00d06400c1880c04c3c0b92403e035402c445000c2c01031800080c191035002007000103010700314040c20159194162a200d8401d100007030000d080c2103564a4002080c0e24200c110f40c20701003505030040401c40034104907041c3c44d04450f005064041c0c842400c880d03071011052084400400b000c0094a00303410000404482074843c0e02c11444a48402c851800c42c144029004403030015285101c00c1d40341c00c001d41c039081c4007a41a02c100c00d8a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 728557266 1250 728556016 728556053
    0x103350903160b030a0c0f02071e0504090b01090f02090a03060b03120a1107140d060b061603021b030f0a24060b090a0902090d0f0501021e0a02012412 66
    0x2d0a40400c02080550185208014109080109081c0c42004440da440781c50a80c001581003000103002302400101c00c290f41c039490b9181719003529036550100d070440c0c5c03421000303494040d411401441070030014014a1011200e22a0640c03c10039150005001c03800a4032008203100e56410700710101e80c0f01030015280000b00c400009481d020488005012600e9040000b8520301a4400103c1d8078074104420590610000e071641050700c81c1642c901d00280000040543d011034107020700d44416517050780d100340040c030a40c0905106485074031000074030400d04000522030380004840310704818001070180c081c1074105c90440c00c0140700b06078250040a01820908204e4107024002c900c03a41008003c001101f4251a1018056501c00c0315104038000c072000698021182c2c001a0003045201e417410400c00e00a0000600c0d000c16856082d801c40340c0c80c3c80d15020400e004c2920207420381c080c0302d00610450000c807034034900d0401803040c41480c209401080452035404002e181404080c0d0b4030724041d60311 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 728558516 1250 728557266 728557303
    0x5010617061309150606050301030f060506010c060f0b0405101d04060b040633020c061b0304032f0918012003190612020d0f0f0b0103350903 62
    0x2030909204008a00d113001107003000741842030010f00d19224108a9040701e41154158400300380c60f5440c0d101814001d4101c5041210111002020415a106241c000c552940000424081c020180025103000600c02c0e81e40e0b40f2101d81c1085614250b048110840c3d26030b210f8a03426940300d28182c8010042d071200641c015103042e01c003051088080988070101c64030000000710400040c2d11700c11032401d2082a020043c0c000d03038100b10290a140c0080c04101109201c20305e0b06144c01d28600e4a580c2213a44280c0c0e80d441e20500101d06844010355241c0316006090020b54207034840400311701c0194024040d280d80c42c0c0350101e08111041d0031b40c403161001e460071512406400e80d50401480c280c1090b90b01081d990b941c2400000d8200e0188690001c44000c072180d04e4200c40f040d002c00043ca007001c1000e0710903a169518040010305084412001d0500c600b44000380c80d41103003400440d403c4020000081c00207600c0d600e018220014252034596000358444650351032102000c40e041180302d41d40b1403614203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 728559766 1250 728558516 728558531
    0x1902091c0605100e06030a020913061a040b030a12210903020a060f06030c03020d1406090303040302010c080c030a050907050406091b0f08040b09031308010b0112050106170613 77
    0x60aa002140100540001e0a43d0580c40d02400b50350352a007910a598903a104000b030340c00504180000305e81c0032003002140044604c1540720301041c0c075204024a0303219811100c0121040c6040c2c49007881d0400c0a034010f01d90400b0036a039092a100c1c10b000c940302806291443c41e140d14104031059045441c1030704052060403014900a99114032800084545504041c28130006500038803c5204413034010310901001c0703240d1b4082c0718089540101c143e66001c03c214614503100c0c010845503014104400c011545c0b07140c2420000e003101c0200340140108045901444900c0011000340c87c0c103c4045000000d0303a0322202c04440c074182079688030b250040c1c1002000034806d002503210b001c089682c0c1c98494030805d200442140c030720702580d4510020035a40710118001c18007401300940d01080741e504a0b4038150f144440d104800720550705c600c0b05a9110b507a021041d507400425110b0385030112006102550400c0d002606d80c40303c030b10301448001e41e12400030354140e580a520300d400300c030a40c10400206 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 728561016 1250 728559766 728559773
    0xf180f0204091103270304060e03030d020406091815180b030f160519030f0c051c12140a0e010302160c081b030d0507110a0b0307171902091c 62
    0x942003105d00e032803801e001d4640c102440110324040b10100060380040c510380f500b41582a50300d03100c1402425010f120500c00c4204000a030310040018080c2901c4103c0c5192808014006241c07281c13a41000c00c03420400c0e00c0400c129203041031000c0d504004112401800c0c108101c000030300e801d192586e03041c401e01015088550000c582d40703032100303c2c0c95004424079445006100a54607010101c1a80f200c00913030400100d274111800300742191080c3c00c02c000e203990703a01c00900d04408148a5034400c44280d0061f9040005500b124119540c0301d060444900711080c1d0401e00314020703184c4540500819800c4202607a10030750444108040002202c0f4021256090204d45103043e8010b0308031078441d00f200b0305e03940b40c0c0c8401c101c0c411800c0140181407181d10028100c0d1542c1280c84103c402d4140c010781c58030641d590049070b002420140c80c815449103410140209440040720b424605407412405010762046030140b2401008400100943c2c1c50010f03201281046986100d100000501c00c0102401c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 728562266 1250 728561016 728561051
    0xb15060a030b01021603062c0a0308040f0c030302030301150806010f050f04081005010501020f060f060d020a0e0403030506031b0d061119020a02151804090c05060c070f0f180f020409 80
    0x1240410701c21240d401d26045400788c2c0c07201c0c100c0d60681c0c540e0700c050312040c0000e12480702c0d140d21502c65a048030509031940d27034400003d01d80b50400c4000d40c10100042c000014020a2400c5961403840c20b0300107401d11030000f030300301d01c841d1f0017007402c01c080060b9440c1c004542c41d080350700400e000021200381c9400c0e82e40c0440200030a0143c68018042d2602a503035900c0d00141590048954051100150310380b281000018070031010204e8002e0000180010001048085181b01d64040d86010599161000400d400e01440500707030f00c6034440140b1498459100e108444200b1540f014001524000c2e10a801003140030b412040e47c810b4000c0201c0b903583d9a070102ea00071f00c151081e500d1400e8000003076040c0305280500c480210048015001050440c41c00c0c1d0071003202135005202c008505605c4e4404582294442d1000144030b40c403640d4200480c2120a20f448000e00d94082c00710450340c284400844009291008085c03141d45a8081c540b000d0042e504590040c80c90031010030258844ac01d0300f405 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 728563516 1250 728562266 728562281
    0xd03060e090601030c091e0603060c030605060c120c160f0905090316060906090501020435030a0507051501060c231e0c0603010906030b15060a030b0102160306 70
    0x580002200208042000c0090918160b030360007800405d00900304440803006080c0e000c43c0c6d0208140b0041101d041c0034a82c070806000d18050320000c01c11100c51100601034a60550005014000c01c00c108000c2c0d020200e5019170540318a180030b95500300c40080c0c24074110300c403401804900c882013030000d400703903c1d580344404807100721506002542d00c4031041502d0380548460f001003981c101801f800003500c5a404116281e102d00320010f80310a480c4c45850880e0410340042170390000707a10310440e019101c1d41c180764a80891161540300740a041407425101c5c000c0c9003510381440400318200c41040414400880013440329005406551b031b541e000140340c01450745050b540300308243c00200c010340e1191076403000740b0a140011f00c140e0043c0054007100941201008020b405002152103095075a503000f54000c013a000808610941181403074801c03600c019021045101840c0d8443c40796403541419101c0c2e465071814002101120a40140c2c00c1c03221105d8900d05001302c0000102c10014603920958 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 728564766 1250 728563516 728563529
    0x203030106021002070f02060a052206030e19020402070c0902030c0a0f0323070203090310020a0311210601092103180605030406020a0507050a0303091203140a050603030c0d0306 78
    0x3c11403140403064804901c0b404070054840300b455081c10000d420500b00a0060319201d280c03042c40c00e01e1403081c0009440c03124002f00341880074020b040103c0c55043c0220000040e0f880058450318441c120294003805a41344001d01070b9401040f19020f000c085d4042d900100901c800655032882c2c040580c4c491644007034060b40c040f86a1602c1032105034441e2141965091045590412040e001c1c000510000c4000304540c044ac0310800506426480910154199600c042009a01c0d2a0000405819a40c5031420341c1c4a2002c1030000e012040300b58083c0324402a010580a03070745460301d0b00101c80421b5140c1006d20301d140390300f019000051b01d0030704401d0712500039030b280118101c5510010643c0d54052007000005101840400d01042890b4010901100d4505016140502d980d0300c180c00c1c41c04807071098020035501e0024030700384580e15524600303000140c076007045a490216151150240080c02c0200b040759500f0004a107030b01c08004503400403c080c070071610615040180240a80a03600855 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 728566016 1250 728564766 728564773
    0x9010e011a04030b181c1e020d020304030f03020a081c0c140a1b14030307080912040e0a0b2814030c10050702060304120e0d03020706051606020a020303010602 70
    0x71902035145030300780d806a95004000c403a0310784800c00101000324007a03030708250a019100007504444001d015038882d50541d91214000e508000842030240d1011452010540d00003072098100c503513001c0708450980780d100d01c406948000c04c0c10106d14042c400c03840180340002c00500c20b220140c10010030504900706030801e002c80d4601d080122600500894000c030015000d002041d0114010308003003c9886480c4011100e008080d20344498504401d00c200203560000001c1c0520039a0020007150712008101c000c0c00d11985501e454203c920981c440d2602c40c264640201e2914001d41c0c00035181d01c0760040c2800c540e03d0b401e005c00c60151400a2151030b86d0400141d0000c0d00690b80080a481240000d0250440d980128248001a00c0000c0e07800d041000070842c5500595502d0003440c012805940c4840303807207107407200150a01ca03548001a00c1703176400254480019600084480980c2c80750f24090740c0750340605166070b001c480d085500816841c00402e020b04400e60000280d41254019400c6 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 728567266 1250 728566016 728566049
    0xd0815030a0b071b0215071a041e0303200a0f080402090604050c070b0a020909060612010614040815060405010f0f03030e1201050a1a15030f0a0b09010e01 68
    0x80540c1e440c45400000c003400c0780c0c0c00006462500640d8103580c00c00c12880311a4440d0b09503800913248041200d1131299144001c91142c0a100424400004200c161201d00c0c0035030600fa19074921014821400000d0300809107000c00405101e600309490401c2c90035101202e003031201e001c0b19056080002d03181c001070030941206203243c2c41502828003642d0098002003840c0c0b0348109001c094280207228155403074041041400203051460301034424403030f0000041c1c50300011810404c00010103440c1d240700d4101403204003031554001c1040c90441e05c90b070a191100205001c0e0b0803119005a0344102d0440c0624020500c00004d24003400e4882d001c12941001540e80304e0826419144040c020010341c0e14401e282800000d02801c0369104410b40281180f03210b4142d00d4a190a5030000c03070300760250585401d500c03092850103415031110000c08450300700d020b81d00700609588902005049018400c0310070045800c40c11076030301030b00c001a0301610419036981c50301080740e003c4000b0b00c604842c220319041d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 728568516 1250 728567266 728567269
    0x309080f15160302040f03080705060a0506090f1b070606030c0b13060c05030d050a020c1209131508060403020717162303010213181401170f0d0815 65
    0x39151503849400d602107907951038001c0810140b1005040322018503608001c0410b084030b000c1d85010045114041090b0f550680d441c285090100160100d660541040b0500256030744465441e54030104810a41a082e510414000d24080e42c1c80c0d00c440080c040083c00500f072000542100c002d907030080c500d020005603a01d00702c510b00d10980320600302c40b2a6040c004d010052003800d141449c00e01800480303050580024071401260000e65445003170b1580060140609103007800715214249298221600b00504040030610008160b41d46208969440700500d4025071701c0c001d00800392540f1030840345c0364603046c5000780d0342d0316003401424500503680400c00003641000034840c250082c0341e41d000385142c0c070300b0fa01c90020004810440d42c1d200c3da04030405106803401d20141807407410020000c528a440d0100d00708840d03030140c0c08029210308000b90180303002043c031a00c2d8119082050039036480485000d4240c01c00d010141c6803510303401240b00d0090b04540c05414503000e10303a40d4446c5480103c8000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 728569766 1250 728568516 728568523
    0x50915130c1706010e0d110915030d03110910020316051612080d02090111101506050304021c150504030906090603051e060a03020402070b041b030803190204080a0309080f 75
    0x21070300c81c00100001c5d100131441c24540484000c0c1d900c1a00c06101000c076130000964080400c48110301070b07168986420260785020489001075582030704040100b1041030300185590302c11910f03040e0092461a40e103c200603c20030840d0b4200c0e0b2030714201d503803054041c9406515524542103000c483c03c140e40c00400c0c1c40025074100d58000d03500521301441d000104030000082c4d0090700030141482407014120b002c0b21414840703403103103044050700024940e031410b064a440720b40da9000942080014010000140c480309084a20110b0004144020700341500c0e00651000c0307100e80040d00181030400340010150801066002d8491a4841c0d0b4605a21000d0071012030b07008a84480c21308400e4001c04247c8140b017584190400d10241c21451700c1a00c1c0e40104e01664812241143d03030181003070801007404001c0c005d528561030099210b140baa4550303226120306000150007502da03003942920340280300c3c5580d03044900610681003954280c001c1404d020384a89507034894115180500c1c50b40001c403c5020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 728571016 1250 728569766 728569771
    0x30809040b1f0804171908010824090a02150406090e13111f020c0a06051c0507032d0e0c1005030a0f0e070924050915130c17 55
    0x410010301c2200301240e040794034640c042c0045d9043d601d491848034104050340014a0118500025a00c0310300200034002c148540591141c4410340026501c035150b0402400c104404010075901e004090311030750784550401308034280c001d5228103011030030702e4242000b001a00803a10282c4403058102e90320500c032041402c084070102000f031540180e860019000000c401d4200002034681690fa40c8000c0030302d45280c02d1068440056804070000300c2c0186000210354000c1c01c400c0c03608606104ea410384240c0e03160001001400256110f80028031001c1c40b07a0701585034804a2044d00d8090502d00c0d0100e4440c0c180d03800c09054103805c0c80e04e12170b184080022955803006000c1c12688000e505084104d50b20342001d0090100207851300864000b003226809448240c00700540601415441c04034042c013115140c004480c419550700c814094400c101d002e07050300301d070010b45a21107030f0341d40d00030078481803a118041d0b00e40c00040203003209220704613540058040703041c903100c2c41c501020100034481c2c502401c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 728572266 1250 728571016 728571049
    0xa0f0509160909021804060e01050a0b03120c031c0b0d08190819091a0f16031103061203070c081b1c030f0516080d14130615050a030809040b 62
    0x50382176411080543d40e007007681c4580200d00019100c41100801e40c00d40b0800d0310b4405a164458a9241407850140032005218107071400c52440d099044010742d4907401201110300e0501c0d07811540c041c0e02d0306c154114400603513008204075052101840c001d00d1540100c6c14032502c001d440c0381340d035076140c0c019054903001f43c20111900c1c0524018455560140500d50310844842155154148400310101c4400d40078106100050b40726281003011360702480040c008a0341054100504460b82d01c44840840f504104281d0724022036988402456185104081c801004c5940b17a410006850601143c003034190a01d00e40a002441000c80c20000122200003060003000244501300e400a0f000314070b80007100d041801c002c0d00782a0035440c44540b0707000b018025207130550002600f5614803098442c124041c481c01c601360310103041603680c0703000c0040b080c0002010560b41c0c001d14150f8840640701140240401407030403641d1500da14007013060342c009121880c0924280480c1d0710851410b4081d02084101c03 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 728573516 1250 728572266 728572279
    0x1908040303080f070c110a1a07140a080301050f060708070303061403011505060d150e01030201020c010903031704050f0712060609020f0f091807020303090d0f0203120a0f050916090902 81
    0x109900c68a4508200c40206c903403100c400000050600803000e05c201d0030325141041ca81e02c8440504040c1c0e204400c1c3c003500c10807031b002000ca01c400210060203607410b58200765101c504102800c00424914802c0e42c40c0504040c82c01f1440004045e07140d0403c50a84440c4c2d20301580b5142044141407c0e640303013404480103c0804142800039003495409003c8c07a94020300085818003d594a10b0740040b000d4106c1030782c031943c000052040d0350b010001403c0101080c070f80030082500c0d5171002044000c9005904840c4968040401c003404000c001c210b07401011202903590182da90a4000072151441c2d00c00c0311100e090060003e6a80350900c25501811060080c0e145895001c8218803481d90004604941c0940844000415141121201845482244c00071a680d090a8402c9864140c1e0985048204180c110100d0201c65010056900c2c0c04640e42d04000070751101d50404002d8128208070303803203092038201041450000000d0340b10208007060102423000761980071480c252408c51202030340004 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 728574766 1250 728573516 728573537
    0x806090a031803120f020111041215090b0106021b030303070203120702070b04060c1a040c050103020901030b0414010608010e060307051e03060408040f0503061303111908040303080f07 81
    0x900410301860610342d00148501219100c0ea40c0c0750912502c0c000c0e50000503410000d250001750244031741c486015654003a5800d01d860708440c8000c03001c84a1001701041410510114442c220b9080255156800a904031096071030f200000c0d5500c292501010a45402c22000d007801d08010045900941540d4082c500d4511015000341030201e000d482c06085200e000000034903071507183d001e07101910156a508581a00c54108035250b2420440941e002e020200188400607420340342040803a1030030f00b00942ca8003280001a4000c04401280310341050414940344a40280214054140c0f1420703141d54103240d0300c603039501c0300543c4100c9450380c150b07010032000c2c0041d1500c1c0b0f40107130003102501c0200b02c0d24078403240481d050403000e440c22200e40c04081000d01400c0e540700304400140506800401070752418941107000d41381d60340405014004030030701140d08650f050219120b030a00e95001094480c000e0700d00402c60f984140b2040c2d000401a43c04a80c020840c0f03a50345020b130289949021441 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 728576016 1250 728574766 728574773
    0x9020307051002150106031d0d0c02240309071706100b13030525060318060b06090303032d040b06040c09080706120c05030f160e1c06060806090a 64
    0x41d4a804490425071098540703120441d004c0c000078a01800803540c002c2410b0104442003a0a0001200c2a000d150444080e074041b542d40420034065081d01201c070304415400381e40049c02d048442a2111a0142002080280791000043d080c000c88040302510300c0b0380701130031100b1030311340e07400341c85000c844600040c003008100010b4004d4510b044600407941222541c0c0d9440d20710b44600d001c2c0c064150440b00551500e22030060920100a2034141070511540c2443d185480300c40b2a4010300910b0196101c85000c02d0342c854200b41c1b101740c03002400326607482c100500f00611100314a404640b40740c00240000c60201c45012521307010710b9100c0c900d540301d034407408100009000460116020001900d0000910000810003003000b030446840349a500e8902c43c0f442801e480074480c1140c02d1013401c10234818100103007466241d06c0400c0313282c80b00d94203810340c20440c0c441a400491036407180116240300000031540403201c1c0d94510031803041101c155a92103064441c00100d0b0440d0044e040a5070300b0011 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 728577266 1250 728576016 728576029
    0x1140607061116050c0307050307080717160e010e0c0a050a050304050c100e011101021315110303010b03091b0603150d02100c0506070e060703030b01120e030903010606030902030705 80
    0x520044100c90030b0020040c4a483d0b0001c0c0e02c94151900c1d8050742c1c00d001c03142000d10040c03000d060203401900c11503042801c81740d9245290b124811220042c441340c9003000c08103001080b260980d0108201210b41d50f90030302c0e41c0c0c072030080c01082104030050000c500d43d048000100e940400064036054203150303503c80140d4050300010416a0b1900403000000619543c422828074403082c2a200d0080403100c46000424a030814809503403160720400003900036517958030070b07401201e46601d00704001c2ca02c0102300300c62000312900c40c1076281c800440040354002d070030320245200c0c03503944080f51800c8904100740c6610440c2d44c2d460b01d800000800110340e1074828081032410118001c0c100707403000c00056001c41c5c5180b1480800e540003562140c041810442c00748147c58100c1d44074680302000c1c4683d01c1c0060650700c500301d4020140341d90b600c1e60900d681d01034582da560400c00035008001c02400310000640781d0313100901c880d02c42e529280c804101140240300302018103070058000c1002078100000d0202 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 728578516 1250 728577266 728577281
    0x20a0302070e0711100f0e01061d18010203072313170c090a0504260d0f110703030c2309121e0705010e06031e0a020d14040b0114060706 60
    0xc11013241c08450004004000d0907000d0b800e2103100084d0017800150350300440c0c90381d1400340045e07410140c04011a40041d01c5200940c2983c0c0504565070b107411074401c1408103140f2110080754000310400081c1c1da044035455081a0303004091343c004000c03210030f80d07051780f041100c4c0c440408448039007031060b00003034201e4426400c01c1000700c80512142800240c22661304417542e9401c5504c0300c0401c01004203503040300d4450520700d03c10403807940340040650050b019488020221961326890b1500445907034000c1c0c15604c1102d0302c45640d444841c00d00501404000841c00c000c525907d0000d1012191014021751403500103888904000d1030743c0801620514402400d9018440c61501c8087c1e2042468811903582d22400181001842d000c005030985c991810740c1d91144d0b10600401c00030414090b0b51000d10b1281d0012078042c1c0c4c3d502600a00240101d17404201c80910b00301031800c0b13a8013500d980034000e50081c01c1d0602d040e0381c0c032a0488071020005c48c115070408414400c075000584190040c44 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 728579766 1250 728578516 728578531
    0xa030905030903011a1302090a0308031005040e0f12091c020d1212060902071707030903082205040509031e120a0b18060f1018080106080706020a0302070e 68
    0x1d140480540000c4d003985c25484a0355103401d84442d12418510740400040c692045078403081d0300b000c404c24000b4102042c1c2d8031000d403000f50000300059100c0041511507000e80402001004001d0041c450305580b0780510b10304203d14130036141c0c14045c0d06021020b450000301c00820500c034944d03c0d800600403039942d1142c100e030018069080c6400007008400112714501c620307a1407050860303414039044256240340e44101c00e8280304000d01c0c6d01281400103500c0c9010f21003290165240b02600e411241e0751041d50016021050100b410310806070082c0f1494401c40300c5500700c0030025100d01c1008100c420030b0b9143c1c00181e1040042800107644e1001803242d100131074003151f0030010a403020f245401c1c411141a40f01c1d50359440840c010b454685100b02944800c000c140580303140c060042101d01e08400e611074030035184840390128943c403030340b201040541180b5000c000c46030381c0c600c2a400b0f010240140c521a000d8190b021407980e100003950518142c15500900c40103251140c02e81030030601400a1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 728581016 1250 728579766 728579773
    0x1511190b06010c0302011e0e120301031a060f0a0803030703060515091017090a1a0609240d08120c070c14040e010e060105270c031f0303081005010302030c0a030905 72
    0x1c102221803401c0302444d2521f0070b0041803800e20661410304041c4001d0010b00205020701c01800843c0d03100758841c003156000b008141c1e494a40e203000070481803400582d154040c0042d1000304042d01c005c0050740c00f520844d1010701140d41c0340c03010040300307004030110403400900601288200d450941c100d604001c40605108501103034460924000c140119907441031544459800020004000c0101c0c0d0030440e407021000c1e00d070504d4000146280005800c00d6a0385d04005060b50103042c91a00a00c40da2000a05840c080f6000b881c103800e01b6003111815818240000740014070700d88140c0100c920090b40030440e030143e01d041600301580d510680c0e0741180c02580d61102c03044101000d1049400300e480440040095614013000c000c80560141031400c0c01a4142c6804455050540c0074240c0000d240c0030251380b280d43e80011150b0307e0b440c2c24101c080e10415642e000060680007241c04e070145d10058215000c0315100c000543c241c0c401582c080c00403400403c02110b410b4820383c0a014031504c60700c2035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 728582266 1250 728581016 728581031
    0x90c130b280806010602061f060c0f03031107060501090b0621040c15020102070c05040605130b03192015250b011512150e0705041511190b06010c030201 67
    0x101d4503203c4240c028401580c0250148009400025181280d403000301003605c0205040c030070020040302412500501400740b440000003003600a80110307140149034286203171607a917a4142030001e441c00f8410031a985151500115850828100b06d42d95030042c440000103030401204143d41c070b140700510a80e280a40c1c1540400e52aa0041d03e107480d0264560001d0380f07130f0400342031415207598194882e91180789400c03c20072403078850500000e04c00708481800910394046002082c1040708201d801e02e800c28944038a8004c102c0c07008141500c0c0742c103803041000402d0714a4248510f020604884140c0340b8011f100b4001c00284100320125001c50790f1000c008240b030143d4502d408544203801c044e1610340481071100c0216802250703403030521b902000a10040074074aa0000d0f5500d00e034011003420010340b10003e00454014001c8030000d0110034204040c404509000901480c40c1a4061100340a03141c0b081504444159802000e00d81181600c4100c0e107400c0300541d01c10075510812000d55403540790 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 728583516 1250 728582266 728582279
    0x9110d08070c0b0d0b0a05031c02030c0d0215070315150c14030d0c0503100e061216050f0d150507031409060601111216020a03020306090c130b28 64
    0x10b404000c215642046484401850307041c429200446405406810410710400060b13900042c40d9001c050504a0a02d6107161400203c2c1103102d0105140c8440c0300b424408440320b5070007e0075540d100500c400700222074455100031015a04024015640c200803802d09104000d000716054400c240c40d81040464820656184030034522019080d0440b40c00208200644a00f07038060401c1c000398514200e0300e50316006804540c204424058004401c894000083c041e480b0100014420345041c0b0031203241d0701c0c6040702070f0418841801442d004400e2006807402506000b0b4007100196800300b01c0c0f00002d036034044c0c180002c00340102031400301a1a00451501c80c180c800c01c0d24010009540900f100349000d00015000c466511189110307a4042405e2030152007156040e203420300d5401b000c0c5043d040890000580384000c980000e94140245414415a61000203100c0a91042175070288510140d100e8147c0444403410003544c0c2007001203007601c151100880881030b9010f1015081c0046544070310 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 728584766 1250 728583516 728583533
    0x61d0607091e0e0a020a030e030c0a0303060e2e05042c0a4202090f0a152a050a11030316030f0215090706110109110d0807 54
    0x1201031011522031841403052011810b0101c0301605080306000c1458544081800c1c1150300a0100480a50104101c180703036209411100100706200c003280c1c1c8034a0041d00302910b0b801c12240c11400710785056000500840740b1184184a5100000c02070840c01503144120344200c1950070001c14003076040070101c0c860341c441c4030701c3c050307004101480b445c0103850300007031140540803400520440c0e019040e003070300040084008402c83c1c0f40b249007440703508181c641c1101b030703c03036002d04c00b040e0600042600d1000c07a0003585c042c142c07485044902003070040441092082540301c6001d502d600d807003282040140d260090010111841411075000402e6184480da40080340300451f0803038154001d20107103030600c8207081001c01c04113801c5010f18941000006800107669400100a0901c1000075240c04124000c1c040c0c5044440c02e9908842c484c500440901d44800d07141c0103440c00304805580400c50700310144540610554880c1003a007405454034100034058441c114100d420305002c0004100140144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 728586016 1250 728584766 728584771
    0x30108331612061508010e0411060708041823010b04060e0a0305031201030b100f06030504050a0f050c1002070b0d0203090f030a23030708010302150903060411031203070903061d06 79
    0x22030720004144c603180005010920691000c0e1100d01140c09010206a00030003a81808204403101907072a019031a290136540100d03804988a8400144840b0707a4250a811044400e1640e919412400b0001c4050410410080c007501200e51400d0005210083c01105c100280302c00061003051480e503282c1c2d0b91495a403104516040c2c00500c0c1c001001041310302ca00c4603800150f0b242c441e103002418844071011413141485080d040680300c44c0490207001c002d10150446c640c101c030320032441200c1414101d588075641541c007402000f9a904c4210914804030303100b000d030340b0302c42c019602e403c13100200b1078041d41001c6d2a6120600658442c4040341700104010401c2e41d289494054142c0300844a106182c0c5030000700c0208914204108000070364490101410360340e044071072130380300700031114041590b0007514031081c1c062041da0140018801d4502c901c0024410460855040d544d6050100700e10303000594104022950a10040c800140360b0340140c44c801507070300082c0c010411110741151818405 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 728587266 1250 728586016 728586029
    0x601021510060e0d03020a030c061805060f0703091505090c09070906180602030a2a060b040f14190207060c110d020d050405041d0303010833161206 65
    0x51a80402206030090290300003c1803c9074002d03004420354034045d450b0750003c0710040410000d15440c4007044071f25030104519014107543ea10701c007400c92404998a5109403051048a0006c00000311590b02c40d0082004c0e16500030b50295100e602c6c52808400350002401c010804d000300034034031810340c4403440c3c010300c1131146555180c041460001c01a08607010000d4465503100c04840070311a040e00041140c1e288411890540c0f114030325031410300c03050a054101d1504c6050111303440d106004807600f00701c7c0c0c5641304840410403040c0c0e80b54210112058001e0780c0703100b00002000208400d4040140e1841107000000151038000547d588000311202164000081501042440100c030020001c035507013416180000e01d0690001030300900580541d00c2040d110f15260101641740001521500e10700e0700c1c4105c03c40c1c1e102e584039800311340c039159030304140c0101c041c0301181ca01d00c2031034010100c251039507043c00c04062610b88043c0000c51490440000044c4221890b10301c40c07038092445050700a110 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 728588516 1250 728587266 728587291
    0x20a0503160519080612070f1d09061306020c07032004090b1302060c0f030306013207080c0604080c1005090d2106120b06010507030206060906010215 66
    0x1041c40c09000c12407408a00e440c1041400d0042840c22949203d4050100c440750520754070315520240002c800c41d020350741e000b406000303c01c1e0020740440c3c03058265055412546100d46d901100340400b142680007162030b644158402404148001d54110b0001502402500c001d85404c8074840951702d046900d900446410381001a6a004128110324140c9a01c40803a014043d504131a1280d4084c540003509100d004e050b040c3d100340c11590703400100c0c2c2d070810344081550030600520b80350f15201c1d001128481d010913480d401c9600203108804000020803050b845400881d85c003024054110340004400301d804840c100581c1c2040002003261510032f501c20b031802a960400071200342d06040c0c60103e55500076091009001c2140008600028108802c0c60300380d001000c600e0b450802003022140d00812140340c0100842c85590700c170700c640e018501506008035541c81d0030004551921039920058010781240c4007007001460401d941a420680501c1100c104e084008451001600c080d18107441244 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 728589766 1250 728588516 728588521
    0x9060f050a05061801031817031605040b07060b0d0519051903090302090709031203050603011a0f01180f090b10180e040c0b0301060f0809010216080c03040504020a0503 74
    0x40c00103102006090141e44803400c02d08040b130b42e83c459003c105621410f05868200401c3c515400085404140d80c1000c0740511071608600f20085a600650351451314000e1500940d04490146044404548901070101d2402a094940e46c008100350141e6651001c1800119000300c0c200b00b20704800c415452440550740156483c1141c03500310380c600391181c18141d85c04c00d0710200c1e4008a5950490340c054a0341c0096a8a40004a034180f40d25040200401c564015a140540c1c0c5540301c5441540103400030042c1c2012240065000f240c1842c445602c00045081c0070903c0d40b04154010b00000d003900348d00751054864a0701154810550040179079155110810b842c3d501c2c0003008000f940c541420f02111005c140c6080c0200c6550354000c0200c0f110512010a08100c1e1a042060080a4041859860396101da4000381813046891083d400a55160702290340c1e03035010b100f05c40212030300e5907445514180664070a2503a0304295000d00c000d000610001030b403030f121400244500311003076881903070380d2 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 728591016 1250 728589766 728589769
    0x120b0a090e1006050303122d0108060604060b0d150b300903030c1b01050414010c020d020c0126070305061005120a02030630010e0c0303090607080409060f05 69
    0xb85441a03003105050821804100a4401200312000b40980c1400c10301e4079983c10a090404c00554176942c9500004038005020300c03107514030058161002403064aa17036403038260411050341d40e0382c081d05606500820010440b081250301924401704a5800c0b82251507a5240a0031103412414a5805400c1c1140720441d020f0480000e00303040803110600c500e000c1c1040e000340e640ea4000103000024961000800080c2401c160044c0c1840d1001c01c0000e02c203030f10305860504521070207881900803660030300240308102030001c19404000302ea11390013082103140090044131095800001c80040202510352082d8041c0c0c505500c520940c81038401040310300b0a1000d1094006190004504014040c032800403281c41d24003805410915100340036890b615200f0009076142c004039000081a40409003c150100d40100c00180c1c41140307a000f0080e1260b90000d091310340300403001040d4950000c101490300d620b80346010f8040c540c0540042070410f525401da9008940480d0130451201c00d0f89079081116 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 728592266 1250 728591016 728591023
    0x180108010f0c18140628031802101809060b07030e030d0e011d040c080403180b04090509070b040b07021005040303120507051e031e0115120b0a090e 65
    0x21114618122480d1403200800f0092510280650803c164038014418880d0b6241c405445255041000c0418005110700d410f111200420028801090501180c9444000d001d03c81c6003030741d50040d1000d07030103244d1610102ca0741c9103130300c02411480481c0c0e0008950404280b240360050500214282d964a001f81000303007036004600f030894030950100c100350080c43d5010324000790324007080c02c0036550700c410801d0076980045044080c1da000342c540b90141409540c8401c5075801140039442d2100c0168062960b00004081e5001d40070480300304000402c481e03a030350f81c000f03070340940c1200641c2c040c0350b100c40b03110a05e5030007644800500000443c0d22415854000c040021807085810110316003440e60b500a440b400060b42403124060b9150b002030620b5002c0e608840700b09140c61842a0000c2c040f00c04070409403c290380c40c03542510314600d8203080902c0c01c003449059458440d40382c40c1140f20101c00f1038800c0362914070b4941c078688482c81011107440e01c2c420040501540900800d0b500b000c4440c0c01e14 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 728593516 1250 728592266 728592281
    0x1210902030c1f0809100c0507031e1704080702120303010603060905060d03201e010b09060d0f050c1005070501050a05042103140c0702010807050a120b180108010f 72
    0x114049000e2900040200341464203d0750b0250300f80300d21903650703441150b0b00b40b00140b0001401c607410b142c0820029a03000000741100f81c400d0703e0700404955401e1884071061a00c070012000705101c024051030505000818680c050712880441c1c1c5070150b941d010450710018045210354070382c404401805026014003c0b0707000344c00300329030812981c03612900090402424131005424070203c0600d03601250484007482400030054011204960488c0d12007200108000401200355442c01d01d680080740b0300f44400c00d0107400002c2c00c42c140790a030b58035120b1310308900c401d04035164480c2441003030068550f28030204c0e21020700d44903151a055181409803d42d080100b60a80440c5850108000680d90030b40c0540b0321072020135050100703580c1070350079001065a59541383e030240d03c400400c108818843d0040000b03600c00e076559481915003180554140c060304003010045404259522241b00d660740c403c10201c0e600405048084001e0300307600ea00120207810011959466522418080000340220391 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 728594766 1250 728593516 728593519
    0x9201912050f0c0f0607020310110c010c0203070f021203040906093c0e19050c280506030a0603120206090601080a0201140a0e060a030509120f03040f0201210902030c 73
    0x400d2203180c40040c1070078013018041ca1284002086030010340d00c0801442c0d07261600c1744001c02180e1412081c0a070039401400444078507600740b0000030606403021080d0350300140e00260080030401560700300140b2041d405002801403000f4000081c40d04810301034880203080c0c040300011100c50943e0450521900000ba0704405642000400c145040d0ba014400802030315a100181c0350445070301117400e00110780c201c10301c01d40314030f80c10100313015001c900440d81ca44221510403142600d240d40c1035408180755440c104403030202e04200414103051009650006c151800015035a84030f58414021162035002c410042c1d215104220003803004028090161036420300900c06484150f000a00001100e5100c1d04040b0004c074083c0c0590f4011015101c0b101d07001031500c3d0700c6a0702403100330000c1100f103400300300c00d01c41c5404292411070035400b120300344840300c0105880d5aa40c0d032100030150f0f40c582d10032810080b04c540b182070540105120026030890039100070039140002c2c01094606494401c07070710f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 728596016 1250 728594766 728594773
    0x1501030f03140f0a0e061911061e0c070303140406140907050303090d050705090103030f09120f03110c12010207060506190e0711240a09201912050f 65
    0x30300440c43e00005503000e1440c00e20b000c018000c181404950a0f00400d140742148000e182c46040085803c07100240350340c10404126500381da06c1750320801901880201c104e2003003421002203a903110100c00101541d50003424041401401180810920501142c4c261001a540c0c4844502d80440d40049900410300b06d0040404a040c100025202e10403014a14418440481c01f981080f9062101d41c0040c6002005071082d0341e56410054545200144c5c1c4000069902d2400b0a02c00e41e60b61500c1600c940003404192804145e40e000c3d00d26444542e07007800b4078850054441d40581c0d60329040441e101d024000942c945003030b4030380760050b9540601114801c1e191300ca001c19108180d40d40c50012100d0344100180030780c850031000d40c0c1c4d01414400803066402401d42c10074440480d101000b881c3c1241e143d040c0102e40e1081000e2044a0480400500302c2403154040d900c809840160a0350703c45000f40044070352840d86e058079103614102d83c040d0380103001c008115002e01c0414000c400392610120b000c1c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 728597122 1106 728596016 728596027
    0x9091e0302011b0206010608010b031503071502010c0813060b0a0b030411090915041115040816060c0b06310605030f010e12070201021501030f0314 65
    0x441003c22030700300300c2c0c000303880c400641ca6040b94045c0e903510000c2e90810b28412004d038805012440c2140d1b036844a401643d4050000000030903656004142000c07403181c01909440c0601c200c03605002410f01001280f00c0728800d5801910343c00fa90010f00c60500348000b4039080c10310f400880107030070040104020081c3daa191200c200404443d8101346c0e68a284100e030b610052100c950340e030500300b103011400080c40041000c80c0080000e0011300c10308055040794a0390741181e84030708525070200c3c00d2103810300d001410b000c1c06080180740c13003201c902460320740d5030f00082d01400b0035000f00c00c0807606012420b0310380b00d012400030260b4074150310321020400180140030f036070140521074005c0c2c000d500f0454005100f0b000700646131402900c0342c2c0144203404d054640005005a042d8010712a0030071180801503804d502031031050442d600349141c1824010715500d4003d5081a1642c2d08202e03 = true := by decide +kernel

theorem cover : BRFrame.Cov 728417266 728597122 := by
  have h0 := BRFrame.cov_init 728417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 728417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 728417266 ≤ n) (h2 : n < 728597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
