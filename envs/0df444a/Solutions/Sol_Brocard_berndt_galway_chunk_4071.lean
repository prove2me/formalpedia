-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4071
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:29:24.430689+00:00
-- url     : https://prove2.me/submissions/c3138376-7d8d-4e27-8534-9f7672a987ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 732014388 ≤ n < 732194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 732015638 1250 732014388 732014431
    0xc161209140a0506031b04030c060305091506130f061503060b030112061e09111903080d2310061701050105070b0903090d060b100c170d1107080a08 65
    0x103400030200c607000c41302255290341d9103240341c0c0740c040002c2148444490100e070120070050303510300c040d0039110740d40c3d030420450707031000e0307840396907071042d4442c400080c42c0c0c0004a00315003082410007403d640801000310720300100001c220301719034496004920602c80c07500200d040300d916024220090820072402411541054072044403014000c000400d030584c1d0b030510900300da046608800d80490075201c2000300307144601340b1907800d03400095141e120307404404c07540044419040070402502e130002c03455400c2080c1d40741860020f04240001c04c403000c4039030702c0000d50300e2070100c1000d00c40c0d15003000b00000703039180250207809288d64021107610241000014001a40d001044ea600d594020040e0280364031410f4542d400d40c0305100d04140c001062500d000305010300d6420444017690b0640314400c2c02044004c0c03c5540d100c0304280100360704c108040b4a0600d40455001e42400c0c58980000201000380d04144621640f01c406d0803620002e001c9985c2d41c20344e411408480c1d001101d425507142c0a070514 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 732016888 1250 732015638 732015649
    0x510080f15011715040f050c09060d020712090f080c010e2106100e0903120711191401140603190611120f070c02030c090c16120914 58
    0xe00c0007829211604101c01140c2c41070300b40d801522030030304003a1880d0605045841c10f001d4401c0f03003180142d05107070032551803281501c0303440d115040354884903043c8410705080083e1a8000030050020580034002100854a1048040702d04c0da42030722a80c0362a851310321102c000407801e41c0b05002c540c20072001c184459070001c03a091b154000803070300800e010810b150b04d11948003d15070307280f580344121000c200709404484070400580385000030030750944e0344a41d0020341d00c0c424640200c2218044401003894140100c288020314030044040d204c40d4607200021020324060404103840c020402c000b00914908203103d42161242c40d003615a50b0380c980003001c6a81e482480302103031402403a2543e45402e0024590003668981c001c0850140c0d03e10400c10b103059175117020356542c00ca007403103900802c6800c0c1c050400142815400740241100c080c030702d8104000711500801142515208004201c0c5011080c0c1052035075611540d0300075003c000c81c407001041c0170190b410940e001c43c0c400c00400510381e070340c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 732018138 1250 732016888 732016891
    0x1e0909012003071211030601090909110f03030c030a18090506030a08031005580204090b07020a050606010e010801031101030608070801021e0405062a03130510080f 72
    0x2031440303403035481d12640c0702210744d110302c0e010300b501e46403800c200d10b100454070a00a6002e20320982c3c890800b00c0d12003a1560841e280d0b0f050003800114802038100841c11304030300b15402130400506580c01e0042c0908020f045601400812002444800d4090244c05401401c0000b51180710401c10041c41c10f40003080c0d58100d0400090150f00d00400060383c1d0819003c41003000d845c01034424180400e040c0e04903502c0f200302019207944014506118403441001c00300c0303c0c0850340c1403644059050804032a0245071100c650091b608103459041c508003155030000200e01500302c2c3c0d402059021400d0400c2403c108001e450b8504000d074000211809a034000381903815240c00804000e031070034005005038001c1400c6d42c4661190b00445000050f5402706602034030b0300e11441d401c02401000640d141c8156841180101640210284030482410610546400065132407001141401c518a0b42052031034008080740804911001003d014508200210021070380d02414060001c0c186400142c014920 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 732019388 1250 732018138 732018191
    0xb04110903100902040e12030906090d2304090606170f07020c1e090403020f010b03070b16060b1f030e01020f04061404050d110301150b04180603021e090901 69
    0x200e0711220000c4d95100c3c1e11510501622004442c1c0903001900070180540080382d84410720702074500000c01c5d070000480c1c1c51103904003c1d660f14100d650003ea101c1d0820350560480c8800040c103104c0410625118400d00e40900340c20f484e40071403008050704414264100800d03040400d8001000e011724aa00080c210401640803a990510710441080501c45408808000d03a032000c00007041c0800d264000c2900414564040028000c6054000034142c1e80c41c0d440c4102105600204445c0010801d100c0740044128031030034010407450410400200d16000d0403c7c44c0f000034041640c1c41140603090b220320a076000e03110f0000e5040617007540c42541d090080e4815482030002a507082c2c454422000100e801514009100400c1d02c2d00504181c0040310200c410103000358038101510f0b0341c04008003e080100d4095008291410303080170041410303014806103481e5429242e44011006a03aa18100c0b000f803800304a8803002811010104101c07030401034024030302a49000c0c50540c00710800d0400040c3c560 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 732020638 1250 732019388 732019391
    0x30d1706040f09020d0b07120912080403020f0106030c06170f0c0708040b0f460201021b240405070e060111061608010f0605030a05040f050601090b0411090310 70
    0xa035201180009442c0c0c56070000c0d031195008092100304034007820541d000380c44c0345c8e48070a400c5440c200d0b1103080f5180e5004c040d00d20170102e08990451407042e0141503020b48a0701c151a0600150307441e450a65200d82c0044901c80f45281c0241b021030303444111503903440310b0f01150400d142001140700702ca50304064090803c0c4000020444140240402160010100c803000d4a2b031f43e02040501d0002d58120104507041b0a0049000301c00c0000c03030401003005501d086d2801242d010b001404209406007100000c015035409000584130f4481403030150302c0e1040e07030300007411244020044100485019030928001d80c115a410312011580014900302903540c412041621600d920006a5a0182c132040b00c80b1144039410400030b41401c59925403112800ca51150a141c1c0d0701c500016000c40b2044c002c4000107441400010101001c642010380c2007400340c030303840590104503121035050007001d0b01309043c030588401c04040103041500c900c0c0c03030841c1e0810340316041c40c04010019455100e000601c02c5010f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 732021888 1250 732020638 732020651
    0x6060503010b09030703120c110111100b0a081504050d020706050a0503040221030c0c06030c0d180803040b1b12070e01030b03101e02120f0c0c030f0702030d170604 72
    0x207490412809020350341108016600351f0031000018101070741c043c000c0711010746141c1d00303e1495005040244101610340040c008594408031f2401c010601980255031001d9507110014003100c086c000f550440c94041d0f2002c43c54500f9040c45460140c00e0300d08501190f02c590401c209155110b000d44880341e000b072509a681c1e032943c2c00050300f10001003561014641111079012480400000103002d000702600503103c1c0814079038204502404100c8480303c80d080e0810410351a0a0113a1240c0c0c0502d0a41c0020140540d07151074203010b58108840c2190340e07107592030510200c2d0300d09108440b07070001180c051501c1d00b80502207200c1e41400c090a05401d21849003000e0000c2e81c040d0300400c03c00c10f0701070112980c00c040b104001d005030801003841d180300258120705044510060003114541500403081044584a0500140108070020181110124240241000004148010302400c84d4a01c0510340301c0300c0c0da004250074006500c07003240504c46202100b55400d0060004035500000449000480 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 732023138 1250 732021888 732021907
    0x9060c041e080d03091101020111090d0f12050406080108060705120603010f09030302090a061d06030403021c030b010905180a0c02030904020c0703030912030e04090f200405070306060503010b 84
    0x1d0840ca42c00040c2140220f89807190321644c15804003018078003400340c9142c1000790f1401a0f080301e0380714001c0000703940d040004080e94103001c3e640403200c0f44030301c000c01c85124482d262010b20323071055039910740041d10015040214642c0003040a02400001c1d0151940303080c82070015085100b01c081c1254103507001e8000030b0840c0e400b90b0019180010182c0c040c040d841c0700340340007002540b000b1007803481a4645c80b80030803010310a2942c1c00c88807812041c807111506d040402c100e120b8000810440031486410716960300044c0664900022140325200400d0461303401002503d08509030b040180180f02840c1c01e06841000320942681044109800090415003a00203c0c214800c03090180d402c903000080c654055480050100e00b160300a0383c3e0301410a444408407003580303000c5800640002c0f52142c0d04e8480f4a031683c8503100140c8914881e0031200f5480d40d491250300d010901800219040219601d0703181418040d955000341c003460100a1681080d201422600040c050030312003000114261f200c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 732024388 1250 732023138 732023189
    0x30328090807060509011815111308060f06100c39050a06050a020601061407060f020712081e040212060c070302070b0f1c0b040509030a0809060c04 65
    0xc15401800d990350361240c6081c41c4002e03110030365040c88598030703000b801e41c8100c0501101040561303020403421030380d0000040001c023070041d000700070080c02000c00203000c00c141004240c000600d514400741a44d480d04150184403c20010000e6004000c1208007000d40d0358440c940e0b0701c500e0f41c0041d404400020f003803000040c2010060303150740d00b80c0380c1c5000c0c4800102c03070464038021600c0c221a541c0d099a01d1307110031a00c074000d40c0d000e00d02581c042001480700602841044000380c040e000360506000e9261210420b80b8203c48404107240d900040000a20031220080c0c2c00508040c01c2c4141d250418610f07c400c8605400807000d075400c008400310f003c540d21440542c1c401e0f001c080c2190f02c40c3c01c0c80d5102110355401400100d0140c400c180c4005019022030b010b5a503a410001150790601b22000502805070b882540c252103000e50701e82d040c104a41e118451540121030710b8009640742e00300ca0b400944540b40c00380819040e40d110208001403842c100f401c40e000d80348000d80000350701c040100ca104 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 732025638 1250 732024388 732024401
    0xd09030c15020a0b0a0e1b0d171603032702032e0213061206180515040f0f0b0603100605090d0c0303020c011e0206010b1615050a0e030328 61
    0x1300309000020901c80e581020760080d02d100c0c5a07202c1512445c018100710000c100c41d403c2c3c40350fa0406041c1c441c504c0803544010100c0002075500d4005450914030b090b6041d28031601c001e0032008a41e070340e4020b03000007480030591148160384035042403242e0590f40020342c0c0d406071b40a2140a0030100f00e46010522010041000036480189065407074003840c030041c17148844640a10350004940d9009401c00103094000c2e913088440c10322240c10450b03801c0820601821004041008492410f008074041e07403514400c05401e503881002c0041c010142a81d404107a074030160070f60348291070038800c1c400030b1400703a111082101c84c641070056a40c8000030110304140c0c500343d800381c00101403450003c14960045201001c024090762420284417203a01c00141c01c4011347c08103c010380c440c42c01440b8041c001401407603038002c1c400e9400035442240d034030103815800b04042d251005031113a043c014142601d014150000c200d80d4050350a41c54030140e82c00d91807403139180d960a528015001d20003c004135a1054 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 732026888 1250 732025638 732025643
    0xc0106050909070326070f2a0f0501020c03030409020307031e02031608090d0c020307080706120b090910181a0402181314120406110d09030c15020a 65
    0x14122031a040240300d495560901c400d503038a8485d402c0e040000d9440c1402180380d840c0c18081241044210f03102c68152a03c0d00100304d443c8174000d5075450489030b08808540400040200c0d0314101800e01703054614042c1294402810f41d4070506c040400d6a4010090300c0948011010041c0c0b00e82e1030034002c6015100c8030000510300135070041c510002600540056110350200c0b0803030b800117001f81004890701c0c00211210543c2c2c0c1c111001066400744200710056600340001d049482240d101d100c40341c2425803940c44040460351501340c441c030300007943c00303400312000c4c003200c11040e2490500c9000fa103824010141030340d06030342d420700c0d915a10003c000d640364490b00102e10001c101e00f403100c8801c50b90b0781654240d100d80310b98802c0e50310524200851620030503404000d11060203542c0d43d4007001e40c4181d070340b010300340c00b51014140710304941c60080c01c000c0146a881c08284c01c032918910b410701140402010070820030800610220b05c2c0c2e89825001c42c0c0c050200600300780e1002c14120300340792103803400 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 732028138 1250 732026888 732026899
    0xa0308090316034d040b0405011502120304030e061c020f0406170114010c020409050a0c0f06030614010f02010b040507180803190c0f0b0916080c13020c010605 70
    0x4010310054018500401d440f003500c0340366881c0e004551403841000d0204070800d090794440c1c00305601300b82c603064207084403000c2c00214901b0f00101c001004c0c2c4901341c0209030302c1001c100001400d41d604010812061600002980c5103007400c1d14010405c07002c0c0c0001c14003600e00007405070121003100d42c564a903c00c0b018001c40d251007100e010181254428440d07800020003280030f605000501a00d0141220007240d19104001268001994807008011080c0c0e0720036507403045540850001c0c824040c010340300358500e01c491420484d40200d0050160007050400d881e05106001a03034a06c100c01c4d41448003400c04150840001d030040740035144550707000c3c3d0442d080c9030034020f081da0004c409408400c091041e18072800d44075401103940340140300019040b42e0f0003402c6910040e020f40f400c0b48601d80100d205402c2c40c4070075154420031043c2524551b490703a01c24900e84822040143c407020242c00040064450b209054002405070030310346913004522a80003440c808110703425070000d8001c0402505 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 732029388 1250 732028138 732028183
    0x30e0a08010603151134020913060c0828110d0b150f041404060305070e0402090a0b06030f070306080a080d11120408161a0907140a03080903 62
    0x2881ca130b003480905042c800c02d6050841d0000284540030540d011403282d99500341d842c00c84130310348a000c4ca0000d010641005109140303580541c640b5040b051040c40441865a00d0102d00d1605404480160304008100100b013404e002c8542211a9450900c0c804420310304250f841c07034941400200300d05244080580c10005000c03500f02080d030441c08400008a4001c0c1880c0c0c40c1840c0600b0071b00c107924100754018810482032044c0420030300c01440001c80039100080f8540c595581d41e240582c140c1100d01d0300350740c1c0b0302040f045141884440f03510003a00341c0300780640c10811000c0b9100780000f90840480d10a03140c00100281e200340d100400610208048030410041d908004440da40940b504065860a000792005146400008c0b6080d2101a4080030300a5440d07485c1c180d550780201ca07030020049000c7d01c0c42070101304c552086180305100c440c800303466410000d6186140160700d6202060000140c805020241d4609060f03000316074111240c507907609481c6d000203080c0024189a940401c036003a4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 732030638 1250 732029388 732029393
    0x1b140d0912090602030f042102030f07140429030f1b0102061506090d03030204120c090b01020f0c01050903071a0408071710022a061e13030e0a08010603 67
    0x1412045560001d03102d00104075200c803000c0380c4074030809100c41200710080208114030440c80307a00d2208c2840074401d00b11703006e1182d80041e051607141c44500c22181d01c00c0c002803002407000390f990702da000c80460302000415800d901c2c0b0300c074403d086440c0e10b800f404103010000301c80d1010711001840380b018400b0745840b0744403007590781505150070b81201c3c0107100d65400207403014841d1840c52103503500240101c1c1000c440c0320403c40403921f203040480030550280000a03c54800c0b05401036814403a1103a061114100b9800104942488150074110351000345540302100340810042204007082c45e1081e43c1c0c0c4400c4012070700d800340c00da01420645c69090091100d440b02034000c1d0098508980940d02415643c4480040c4030444a5a08815811040952080941b5503000700142c10304000d050f100381303004c3c0c002090305911106140c60681c103c80c0802406042000c1c0800301c00b564415204114181210040032001042700c0c0107061088040c403810b62999042c0114004100d10720084c0221a12403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 732031888 1250 732030638 732030653
    0x60309060f0c1e0503060d0b04140f01020702010f0206070e190f0b0304210206010605360f010309030c02061605061303090605070b041b082a041b140d09 67
    0x1180c800c40d22110f80c40c10685044c8184200c0740212001451808a02000e4850620a07400980111211444c5400da03648489061101111441c2c4250005864400c103000141480d0f980c503103074070708542000c0204187c1c5508280c034041c0c18001552a80a600312040c00c4030810b1301d09422043c24002448000280c585480004502c20303031042d07030b80c2414454440400c40201c8081d9a81c480542c10480040c030400313124501074815107031445081a11840c02c18040b00180b20940c016180c140410a507861003401e000130902d096400c00c1c41c04103c50030705510001c0c43c1840c07500d8000c1c801c5c3c0c0001400401010580c188011068215042d6a02801c0288600c15043c0c003412044010401c1c3c4075002a0b0103004400391031505400c0321b0041c606507180ea6542c1e9811000b6076038580010f21458000c9180d150800120b00040586132883c400380507401d0000c83c142040a01d418070680c20800390301c0b00184600d03000b801c03981c02801c004000901da40c0303000c006401032070010314079035241090034014080b01 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 732033138 1250 732031888 732031907
    0x2f0a0b04170d0c0b040606120b060102122502030703121709030301030f080309120a18050a0807061b08070609020909280206040504020f041e030b01060309060f0c 71
    0x1081e01c030050821188107071115080c60040c00440e8003440d038400443c4140300e955038054410040003901e1a1100e44075801d1420125040d00d15800d8a02000300d1540c040004c02c5800d0b500c0c1c0a401d042c103d00010171250600400c1350891041d29041d40c410440d20208540005594440084641060300410042043d030003d0b401200303011301080860300026001c0103c90680c2d0700203869000c2c2580e80e0b01c8401b155840980000325030f08c6140c10380c3d0f100001090162000500070b03a2410014131000c075400280c04116000a40700b240040410072100c05e00040e01e01c21903420b81415207058000071148043c4000900d005401001c0000e56801049010783c081c1480b40d00c00c6400c1400d546071003003a90303902c5440d4503090394011145c16254407401c0001c20a0000302c0e01c024402883c15840e08049400d076049000c000d0f03003070300f400729003400584007800650403104540d105903d001e519586405490f15018811362043c15a2080041c0034041250040c510021415805000c0f4074504640241035511 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 732034388 1250 732033138 732033149
    0x30c02100b131107020301050f09100e030d270f151419060810090b010501050c15060d02030a0b01090b0103090804050915090106080907060801032f0a0b04 68
    0x412449040d1a401407041954004010344a03881010070000b441d0b0040a5612040390040d40a000000060741d0134041c0350b201d0b411100c119256418801505890300321036608451115040c8640003100000000c00d5505662400501044490aa000b58801810243c1c20340c001c1c5440001c104d418000b00740002014540300700741d9000c3d0340c04064205001c840e8218410402d262412012a180340b442d0b16840c00100b441c600d0015405645450061070030a22044c40e10000b900c0c0c801c540180f21900610030300400080c28580c0c6044440700301c15071030b00c002010003002c0c07041a001146c040d80791020a2041c0560190884220b03409034101540c907040240700d820211800c2c41032828480d403290164074100387c0e014461609250401c0108920000020b040b0320010f06d021300e804140d0356030310b07580314002c04071a101d403161410306040ca40e00f41401e82e0401c0040c05108801040090003e00203150340d40300c88014400d40003141c40c15007101e64200e0321110760280f0340b0800400d00c158034070000d0007280c4 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 732035638 1250 732034388 732034393
    0x11180103080c0607030209061b010b370321091203021606091406072a230604270218010905151c020c0307060504020108060409053307030c02 62
    0x291054000c400741e20441c00480d8115005210725100307007a402601102068209d8004283c141400c0c0100d422407000b048103030040c40d40516940140c031903000b071460316880300640c008402d504544030700c0c0350480701440341b8000302c1c2c00d489440c070481d01c0761404070058080c0d041ca55040186608000f5913550708c07004510001c1f400307058001195402410b5030002c40f440c090083c800802c2000c20040c00303401c01c2030140c1c0d2941420034452074110380e003980401964141101e1450450801035409070001001d00d204811201c030060181c01661411f0a4130111550700a48601040f807850030909403265050041d42620300100d14502c00005403003c1c80e580440a0380d03507100e45542c401c1006400c0c0c1d02d51440503070b0810708022903003a10b00b005003541141c0c016403d02600c3c01c65462102d61940d40444001d442c0b01c2d981c2d0080c04215a07015640326040801110280f201e41340640701da030713201e4030794100110f8001034171400a03400001c00e41403140045031590000b0900d1411180140207828444a900c0060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 732036888 1250 732035638 732035641
    0x406110f060a0e010c09060e0111010f0509071802070f02061c09080a030b0303070f032712111206070e0d0602030f0121080a051b010203160905150711180103080c06 72
    0x100c2c814030b200310880705155102e44160808d40019140030343c001499120035503d4000c03480310141c06004043c000c3c1140c600604040e494140c050300010320740f803c0702000300c0c0100403c0001c114460f5098003096011036405070b507484840c0707242142d0f0a48251882a15040200d25028804070001529500b41c0310b841c1409807010400402d07881c0c1c80703044401004d10441e80c0780d81020a10070141000a55444850090302c404104001a000512079104102c29003e1398a1070003000304c0e15075608032404003912030402402540c04150707100c0d18000d1005007000004099180d0a03503c94880c841c09a820200843d52070070300e40780c04095070b4024025140200c0d0a545650000c400d1040d090340e000340c0003140c284c1040d098810031601607010601d00c041d03155031100c070074844150a2000b1030082151014070701680401a80181c2041184d52105100c1d42c44101a0000185503004030343e072103540000814114201440090342140f0501d00503400c3c0d41c0814004810410400c00601001c01d800040f02e269 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 732038138 1250 732036888 732036911
    0xc1a0609090118080921160b0301060e0d020a05120a110f0303042c01061106100810090204060b1902060c03130803100b0a091d0702030406110f060a0e01 67
    0x3d9442540c40000546115081000403070b800c003014180f01240200000842000800465a405504600303032006d40c01020105001092000000c402000702c02d14071419903240c40d80203480016081c5840380103100e030154001c11513961081e644040c12004056510f002c046140c01540d038020400200c840e100d00411400c07803403402c1200880d11440013002586403604141c5180e000d20801c8003c101c0240d285442c180111140030345040c0070740110796841e890000b080103402d10306403015010882081829800b80700c0b0400c04128108809c012190100350a015840490000c0856501c0f43c07140102c08110890b4294915020103980c1800783d00720380340c1e40c940b0803005101d4402595040340700c001d280074040001e440303c0b000d035a001107520144031010b07030751750300c01051a4407941c1c4c45000102c40700780610011100c0c81c6040e1855802d90404401ca01d010701c3c01950340c2c03050340100700c00c0c0700700c035000075450b100d08000c1c66440c07084802c151441810209074042c0a0428101c0c859203039400c01521114 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 732039388 1250 732038138 732038141
    0x91518080a050f2e0605030105040602090415030c090c02100f0e0d05031003030e040b03010603051c020303010e0a09020d050d0903062a0302130806040b010503010e0327010c1a06090901 81
    0x4002802c400459000301410311000000d4100c0113201c1e2440c0e4a85e080000d03641d60030f12076544140c0c010100540e40e4020031f0200011036402c0c1c2200c02c15019160401c0c401709011000075010354a8042001545400d1110181e141540081d1601412400c10303902c1d00600104da0090703080740b5102001c0741d00c0041c0030881a14280000c403882e8000c114030100400c0400e2103240c24a002c880c0c081d02c009003080611000c2406e5a509800584503644054000c4400b8180c0d60b240002d403212030b2001c1c50455041880140340d0303260150000380d81e240c0390003401080d03650748200030310500e911004a402c401c401e208044e002004070311007940e9075443c00401106500c45100d58400e03500c03004180b40322441410400350029000900040c40e00b6107480030209085604004d80c5001d68014891318140d585884c0405007951101441900b00d0b40052012120002010510710120280c1024030110039200c0c0d00120790400701c44070040c1014007042030300c4035030b000d151101e940561800c1d9062204d50703441480103070 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 732040638 1250 732039388 732039403
    0xa020a0b10080c2e030209060c010b120a0b01090c050906071b0918170c070603090b13120f051207120b03010209060a03020d06030c06050d05100303091518080a050f 72
    0x9201c44118030300c00c40300000480f0448003164641c05c0041c207003210000421055003101d16140c40682d51a8904190f614219540802c4007118100920304510b00e1341d50501429410311038401080d4540e0f40410045001e14181c804941c80074012646a1b909420115140c580e00c00c07030400101258100852140014060300d00e5010650703410442d0500705942d07080e10030420411400320020140300c82c030a07082d0184200001420565400700d030803102030400079080b01c0e010703140340440824000003600149007403ca98070140c0d0f80d81440001948803e20a0340c40e44601006c5406c8040c29004104110341c00c0b5500340e00580304120304106a082010a06d8201c3c4511842e4a030300603010303c0400d02c110300c40d03002440f101078010b1010864590365510560050342c030741c2004001c83c501040b0910000014071a00d81d0024091044418107855520702a00c0107049028010030302e001c4403080c58001d4000d0320000030504a0035070501c501c595030100a500c85400c4401141d02d4040c0482ea400b20180025105 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 732041888 1250 732040638 732040669
    0x4080d0615080c0a110709091a0126150a060e062b080904020304030305180604080316020327150310090207020a08150f0109020a140a020a0b10080c 65
    0x42c00b4907120100c0300b1101307030032078420002081640080d80d0350b0b20b40e00384003207801400001c02c0422441810310b0415440a01c00c15a48064003a030001045203101c100800b005402c1464138101404034107202403400d20f2420841c18006103810824040c42131441d91014040300c2041051601c161242030800480402c0c0710380d0940711020304c29143c00250385620040b17440500c184010f03858450990086802c1c1d800844068002c295907000b0001d2038407002150000a54101015005038a1309540e4040a40009040070100c1c218068000000390b00810403030780c0c01c541c02c1450a12100d00c1d040078000c1c41c0c00c0c1d01e05131809910800d1249005106001c20387c2c0c092110b1403280e400303c2d414204090000c0d00400800da9004031070200018050b0f006000c550b2221004504e1103071245802240300c60b03210b4041c0e000352134240c4108105095660f002004c66001c00104042658500c1c3c00e040403482e015000c000a0702c0c802900c802d004159150810345d40c1241c01000c01da034030036140c0300108a544800800f28 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 732043138 1250 732041888 732041897
    0x1b0c12031206040509030705011b0816050301060c170d061a040e06090901020f0d05010f06050c0a030c060e030c031c180b0c0d020a121401061b170304080d0615 70
    0x1140d00c82c50a60130082d400240301c0112800d2040948030341e803c2d0b4225191a09a0782002405005115402401c881c2d01020074010f40401e030016820007046440148114020000701400101c20071005000301c40300610000340907510340c0c0000c6150001010144540c40c103810b40e0000364004800c0617026a4100c81c000b03440880165995024440401c000070a1005195400c109021170102880e0181440ba4040c6000164943c14481c040d21040d1140d0092401e116040c0044400040002009101282e243c0347c44032485002307140c8407019100c2c0dd021070209020220344102c00d440d00002600080840001c840740b243c0d8100381a20031a140003c00340c4288440c0b8940da004a14581d50854104640702d113018a013500078211b000481c1c01c69500f5000088480010b007488840ca4015540e600c2e4103061b10315210352600c80042c6c0f0300402111502440d40b032020400c1c081c00140c140f06000c40d00251100c036a04d2601c1d181404035507001e02ca4402446181100214154403031100880c000d003695100d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 732044388 1250 732043138 732043141
    0x20114180703030e042304030905010513060c0510180614090a031d0d0b0604050901051006180b040611120c0a030e0316030606140409020307060804081b0c120312 71
    0x404a4515400804c055002500c6170300d401001103070200c04410418035168078215078146490020b1165035107030300c61030410400340860251441d448040d9822600c290604400e40781d0f0038503040f4281104032a41c43d0b0b0591400840b10120f0b08800c01c180a180d01c00c2504018410078440100c0d003880f000c4d610108a644550007000010b400303000c1c0151200d038061542030880f101000010b03a0039480c2e5404030b0b000300c00c010501c01142028000c0640000212009001e1494070002c0c4411a030b846101d54002c02980141d03503000f030200c00d846400900500020b90740e44070380314840a07101c2200c1610b0300c40f41e80701d110818031170800e8403002e80c2c0c200a8a01c0240c070b07140040d0b031021528269a8040254140901c081d4000d00300055074402c8000d42c403030000810300d01d28041921002003c4000c1c1c2e10b00079420039174000010b903000f051078002e40381340f8144240c1c1505c0307078102100c1c00d00880b001c2d40800070340c0351840c00500c040080d610b00c800d00c04513801aa540207007050261203005100d144d500c2c2000e00c10 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 732045638 1250 732044388 732044393
    0xb0d0c05150d0608280f030e060f0c01051b1305190e070f0207060e0306061e0d05010207050706140712020f0307030e040b06030c03011703040510020114180703 70
    0x1954010100010600c407800c2402003a15003080750660342c050559a440704a070303d00501000c402c802c81d041c00c0040401703100316007078683c8001440c252070003c04010012411440c590758120603100c21410341c41c185521020b40c500948e0003002c09480b0804003000c00c020910648120000300d50028220400002200c2c2c034050510010b824041406440d041d820305001c00c070343e51000281841402e8a036106072160025020103801c28119801003410040d8070742120169481c000f4480b500041c06035040721030b010010307813540c0409110703440056100301076601480c2030002c1500601240ea0003001981c8405540703810540d0504070010103c0c82880c0107115a5003c030354500c2d00e0760502c0300117006481c84401a481c41a003107900c035003411404556080500e43d04c070304242c490034010314026141c50745907003841c9554500e1404148142d01c804008000400f024031020b20556005007405000c0203d919140034010340a4141c65180c981100a20400600c002d81031a0b00318107003a40d254003401c08181581c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 732046888 1250 732045638 732045649
    0x30907060e0301060e130204111305130e0601082406090c160210170a020306060912010b060310151d13060f0b0306030601060215060d0212070306020309010b0d0c05 72
    0x40c80700b94155607542000a14211705031010303205500440c40701283c121103104010071504046040c0c1e070019000c0c0086c48045440b0000e100950f5001c40b0102c209491540c1040d000d80a04c1307a4000c40d900071b8400004001c1400603014a048180c00c01010035980113070708400314060110b130095480900f44010074845951351000700662141c41c0c0d02c0324062160350300071072a5200c0c2d03103c4690002d00000c0401034400541c1408580010200340190303e5810141c0001d0741c81d0056601240c412060721000614851007540203920a64016110903100d14000807141003003d110312540c1044000300303009040c458401c10b038400318001180341d00c4c50441d0003d0107001c811021520b0075408903944d8880882c200702e4a5028500601c14013a115030b492401100f45401c0407030680c095025035000c00720421039104880369241d0301c07807001d4400005e0714403240000f03040419020540b1b803031402400c00100034410301c1c6d0015403290135080002e000340d1400005004c1c5d8490082800341c044000d066042c862403925 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 732048138 1250 732046888 732046907
    0x11091e13140121240b04050f011a042301080f0601021002030703020405040908040503121303022704050f0106050a0b030a020a051e0a14160230011d0303090706 70
    0x582000208011155140d901c004d04515415451010301c0d03001c3c1c03c0b50b50842c041c02ca10b4134400e480078880390415003034448001da4180203180b80d0f07040391700c889004021b000003524000e20352000383c848220519141c403900c0c4807500c0f00f81400120910b001800000504116034002c0f14181c1c0209005803d0305842c030002e4101074109010142c081000068958480c015202c0141c022900c2e1607a0310700d8182010314208061290240d864020f100400c08400309402c030f00704880d01030310540220300021243c1d1905030301c4000303004200b00303da206020600c6000140550022804030080242c0d42d1900204810b5803410310907402044c0c010070020b1901c1c000c50700a0401d016031805c041d41082c49440f0301040c070300d806200b902d02c46030021588441d9981d024a28404000c3c010b0b9850b460842054144e403248540e02030042e00514a851010071051095a9140107890640e24100c581d109503c485502802d565404985101101940041801c0d000700c00c890042d400d000c000c1210602e0481e003540d00060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 732049388 1250 732048138 732048179
    0x406050c04082d070e0a02160b1305070801112706210106050f0d2309030705150c070b070c06020703030c030c02010902090a11091e131401 61
    0x101407000042ca0881040f10328841c100c0280401c180b0300740311001d407042c0107150300403003540d502c60802008081c00914216030042800038015a4407111007425407820914003a0060030f40800d0300c104882c284c0b4162405290500c10f20075101c1d0f41d03a660700064281c50f000485142000c1080100003450552000600c11444951021102e0440c2e01d50004402e40c0060141d542d180d06004540d0f081110b0246d020707400743ca80c5041c410f0a021071149400d0140c002c041c02000d2260b03459105100307101040d0440004503141045220162a04041007900c94103c4481102d00d407040030103d00c45a403038144802d101e0342c1007284003410b2a81a484082c0710300d601501440c203005848140e100411703101d0008202441c0170340c50110744042000d0700201140d0b03c0010090459150446500051f07456184481c4c20031300000d404100c00d45009219105c41c460703001103e520080c10820b602c02c205080245080d041004c4551001c4040c0201190054a80c105000415268071600600213014100d42c080442c00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 732050638 1250 732049388 732049411
    0x180403050a0e0d020306040501050f0709060206010b0f1c0e07050a0e0f1b0d0204170607020604030e1314011e081c050d050a050613020a1409012d030f0c0206040605 72
    0x3c1c06030f00480e0508000780c0301900c16945800810908155000010303811000c42c3c541103181d030b4079000009440d030300180114100c03c0f01c009022000350191600751000303402c4480a0749005c0c2c603140308100040c440c0c2c150060143c0a582c0300000d0900e01168040b01b00c41d01002121076541d104c10380b603461160001c060090941b0600c0c00c0301c50610104d000b50450408001c40141d40d642020035030185109040e401c065281d00000c1000441c41c0d020034a103810950506107401c56100c28800143e041a620769000001858203240e1004105520110340c1200e4444103640c400d040d85510900c00311070580039005090384252111944d001c5c01d0075200409050701d2400b6800d01015070041c4065410580300030031001e441710107200503490424102240c3c0120443c04510302406202c014040783d1951094415039800495080c071140d0040c806555680c1752150851400e4040c10000b2002441440d00c8400191a04180346403041e01031280344011f0186070000c3c8105d6603a591a400a810020400c82410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 732051888 1250 732050638 732050659
    0xe0a030909200a14070c03021503070512040320150f04020607080901140d020307120b0f040908090d080c0f0304050d0b04021207120506100f030b0a09080d0902180403050a0e 76
    0xf03404004c00b6201d51441600b0300c8a100c2c6c6940104200703416821007081701e0034002c1060143d119000022540710080c0308600d015540e50702c2c2825109240041d03548090310600e040d284004900108050034188603124505410b0f444010b641100d100040310001d420440800c4a100812000c1d0050718000c00145041e500641e1032076540003460300104d20410080d9004000d001000ea001075500842040045040102030b0001e4006940d21460f00007680c01a83e039452464203000e900800c171115000003a1650402c0815442c0501866001c10140c07542c40c01001803112081c0008011103007140d400038901c0c904c900b410346541c1c80840b8090412170344a0343d603801c014482e00090244c24000c05820068018182081c00e0841c10040d0003070603010a0f04150a007402520f08001e1000305480d048181d8440340e95503600148010580e466001e030594002065040c080030702c1c2d81000042c103100391400043c10701d41c1035280e41c0721041624000c0200b82c040c0144462940710b002a20b203030100081048051 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 732053138 1250 732051888 732051917
    0x51b030403030c0204141b0901030b0301020f03071403060a180f06060e211b062809050d15020f070602030f0a0b0d030504090b0a08010e0a030909200a 66
    0x1164003652085003c11100c00c8140203515051040c04001100c401c102c01072890700c0d0425044400024680500040011403601900e03486540404030305000030380210350310321680309a0803041d0411503040d030004034100700100f603062110041e2401094050030b03003c0018144240c210700100c0a10900400c25030b00e500c12400c0b540c443c01007100600140e01c0c2d92120300070007401d115220341c110070010401d0841c515800013001001410070000312116100701410340300344000540d1449002c90904170704000310303040e903240341c0c40b030300c0c0901d0500d49501c0706210070790b440c0c0601c420840e00403c09080001e0100910210000c950000c1400c090f0884c0c14a15001c401d0340d40070200e80081d948042903c40240130007042c00114490111035560445e00300000221554009040d4031550141e80119030300c41c00340007920340b60000709138007800081b802030040c223101d0200d080d56a050058244d000407030040000410401714070440701c0380410100b0307540d4450042d0300401072030341c4003211180400c07154003202c0302c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 732054388 1250 732053138 732053143
    0x240d0911101808010204080c040e032101090b040c0512091e010f05010f0e0c0f0708041202030d09050a03030503090a0b010e0901140f01050d02031204061215030b07051b 74
    0x849030340c58940d0100351002d08000e100c2001c241d008140c041c0e10400040c05244030008110000d801e01f103501082540c110034019042d0301500f100289062029003250120320524072029040e104c0f02c01003006100701d4a4104015203046101c20740102e801003005040c2d8100001e4225804a841400ca0b81080f00c1c0d40c0c49594844000b1f1034900c00790b5920703400c2e0000001d182c01002e00500340f100300740388030324100a18813000340f00180034001e03500800903209415154580a5419464202c3d01064803260380e044684205180308104901c280900c0040c0240745002d4002501a40d8018100c1c507542400d6960942c1c1d40d44c8080c064004520403001080700007001015018080c0c11400909007542c20080305041c295480c40440c840c034444018100700c010300c481164241110400c641079254503030b01e8008242025900711508001c07900004020618580040440300c500c0d49405007004182d10000d51240b914101e4000207102d1418400800c0b00140301d04040d02c0c0600814514540f10301902c038080c1e1 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 732055638 1250 732054388 732054409
    0xa15030b151224070c020312191707030e19050a0515150603150409030525150e030c1f060b0a0c060c030905060114240d0911 55
    0x605481d4080000740d0030b0a1500d00c02e103900c40032800a04900b0002c44a00044041425850b58420741c3d540c00540d001d8843e0b4800d0305000d4018050368018405010340d04c002c0d5200348070100034001e4031807030700920343d11450f1602c07402566601700a2880d103c481088016104007003c10401d80704038000314007408544207880c14128420f0700141029882c52400b2818004024607500c00140100d0401281c032011042ca074008401c1102c4e00e9940782e0301e101070b281c6104c050700b0044e500140303000510030070144c1000060400310b84000300d140364000880c07180004914840c0c0024641c05c0310035010388200419400000b6030300e072040c06030b0303003000306c00401d007850050042c980b542d0204040020400e92400c501c00c0c0c4029220800b0010f1814820b50405482c0c200e842c040106140c1d51010740c80c2c1658401e034040d5070030580c010b09503000b95039207d00c1000b0400f040b0b10301a02c078421203c45056600e820341e404954000c0d051010b582810ba4450852000b04516041547c48005003400000aa0b80e89a81c0c81c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 732056888 1250 732055638 732055651
    0x1e0309010c020114040807030e01120e0609010f0612080318031207030b040207031b03020f070b0705010606020f0a1103160909060605040b0102030d090c150207090e01050601080a15030b 81
    0x281400d0214002030943d240061311980d9144150180300c040344a041c103e40240d901030a14645000007000100c803241034822015490902d09894010406000b1602c1030041406e24000d200017103600e2101c408680c00b07849004055000000b48000040120001d10b5100040222122a40004818007401e41d4030070301c0c81081d111904030401c40d4598140c0b264003003038413040d04c0c01c5040017a00c0d5005001051101400b407060701d1001c100004051003003003d0f000d01080c00c01030341c00084d95a0007035405604845001c8070350b5401d103c80415410b100050a40208007000d005050401068039032100310a40314407134940501440700100c42c0780c08507014000c020800307910f00240c8036285043c1507084031240c4d002644158208828210b17141c6e0700100303641030307200172030400644580540303003c440480e59a40245c6a140e10241c0590081c1d80200e19402154480b0000703010036241c01c0200c030f0884004440300340c00b00328860041401c2c80340c250301080c0c030840d074468201c07002d685036207a0604495003110b05 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 732058138 1250 732056888 732056891
    0x130602040e0a180b0601030f0932030a2a0506040b06120607052506050f01060206090102091f05130e090d0e0607030503100b0408071a0903070603021e030901 69
    0x248201c000c614407521018a05a0843c8204512181c2e94882200e4001d482641003549548040200410591200c0c0c21180c0c42000e07240140548034130741d480a0740074100381c10020352096080700011408411100c941da100d40d2001e80c42c44007660704070700101190b40818644040d001d0703440d0004800304640d502032402490070244500e4144100081181714004c0906e25401030014000102c6e00541580d000e45211604041c6802c41001401c409007200304005c0c1660b0705001c01c0c82a001900885503041e2141c42d070a4850f84d660388207540c1d0907440fa010000d43c00c007070040585c42810480248407039040c070303c51608920308444039000c0311408840c0e82250896810034001c3c4500e9102c20072000004041508003910351a00c20700000d4014011354101505101c400400201140c0301d8000d210050020034001039144ca407651800d03036075050360707001c1c0e01400c58510114401301e404500503030b148071600070300901070f070b40c00c040c8128065003100d9541c1181400c1059900b5001000300061842071508000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 732059388 1250 732058138 732058141
    0xa11070315051504090b0f1e13021008041e03030617010606020c100909020d020712030b01030b121009050c03010227100909020a140c0f0c03070f0608130602040e 71
    0x9506040d03100f085034948150b1034100c4d0203002481c140600b42d4420203115010300c0d190f54103200e1132810352881141c5c4140c007406804104040b034070b240310714200c0380c000c0d5001000300d100141c05441c0c554007520f010b08007041c2c040803c0e4000140a41079002d90784a4940410072590f1101001120040260b0845c0d40c0d9440d03482c14028035904000c0d640c0200300071101d440f401103074a0030240117140c56020320540a90006416040d889164040b5941681e0042015200c0d006401e0b00074003c0694040181c0000d003042e40b00201450000000e00800303a292025001081070307039507850000d0a0041c2c1c100c440707000341d40b11a141642c00380302034500601c80d0702c403211200c0351070b165205400750000f103001d02c070700c0c0610940d02443d13a10482c24001d40740754a50040e51400381c0c441c140c3d001d2400004005400c400016562804035000c522100c89207128000c41e00801d5801080507100e06107030058042029180404010301c41c89529080d07000701580c1016120030f40310f0780b2010306a90150700510343d081807190 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 732060638 1250 732059388 732059401
    0x8070b041502040609090b040b0a060f030e010204033206010b07020a0801020301060801030f0c0e10081b2d031e0f0307030c12260109200a1107031505 66
    0x200c26552186070301d004600d02828900e01400d0f0100502035000170036655003940c115603d07264407180000900401c013074038450ba61040104003a000e006103100003030170102e01500e0000d05009490a90341e010070808900f041c0300f071000928041c2402c8206a204512045d110903250903c04a0302030038605082c03a0341e1f40302c2d50040c0683c10a9903071000105170b104000400001d40e01a84076410340394803204140d100c981a0a04124109c50781e000069101405403d10441d004100c840204a50396130080d60041426841172818203103036000030582000c0500f0068411441782030381a001e00c244007000301d201050320401701e0302c1d100040e0b000885a807a00d40c00b07403140ca10200110200028004000c528003d625503000b088200c1000000303081c0c59014000711900ca0282ca204130b0060011840c0c00e8004400388600c0130a24420700c1b80c0003505140c2344100980044c52120303105032560810095180101c3c14804555044c90b0100e103020a020341c04000c80000c0c2d5103003071120000305000001c2414200750 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 732061888 1250 732060638 732060653
    0xe04050403110c09090d230a0509040b0906150d020c100e0c09090a03080c0412050d0f0e0105072d0b041b080d030f06090e061005150d020a050708070b04 67
    0x160a103031003401ea0f40c08100700e4020018a0000000c41451f040041c051507008101c803541e6840003a408884010818109096108018040140c01250107111080107241031100444e02a9440c0e0b8103d10b45080110b9107814280003041400d9079140d005103080311004105090110400e0310041c19a2500202624214100010100207004407400400303410300348178807691050203c0b0002c1c14402c00c1c0f00054001c21010043e2001000500810700080400340f4040751a00c00201d120742c003084810355032000702841691590414041030310390303503c1c101103511103d45082c0380880400d1850841251640781d1803107454408507907485040b0045003401c1510f481d0340b0443c0315000014050304500010003021000007050440c2d1040d034103000842400c8000158040c02490300705020090910240490328040040c20920030b008112844c43d82c5529101000003d18170b000240c07241101c2402110ba2580c2c2c40e5004100604150503d030f0b2400101d56210461500800005c4e0b9002e1244810030060100c003 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 732063138 1250 732061888 732061903
    0x190e01150503070b1b01060905090a0506100b1e0405030111040e010503011107120c05030406050a03060e1e0a140a0b0906120d14070b0c090a060309150207030e0405040311 75
    0x442c040d02090f803d204407180c0e18000c4c00c400745a5100f507005840d118035001c0d407121002e0802c0c0c0340144400d20703020b80c401d9592000030b00121410301c5048005901e4089841d02d1209582c1d182c1080c928122044c00340128007495204aa2100c00041000003040d903024480c14001d0707003000b840d40d40c481d841c04031200e0802e08141c1c0201d000384d0500d55101541c4405604440c0107031341c4012040d0502801e0041140c1c0014004001003040c800082c01041c1550000c0c00307040c0d0301070103139020310106403503c800c08003026042c1c440400490710009900d03160842c850005504c0040340e01c0008103050f45040b4a10300c88400e4401840039030341d8034000065801c3c4080c22642c07254ac10b4611690b402c02007c0c0320395071a0607003440ba104210180c01310410018042003118441e5401901c00072050820350134460159015004003885000c916600050050190281407440c6401850701c10502c1c8a05440d00c01962200c2e004804000f07100040301d1043d0703103502c200303400b650013030303803450070460903007000d0f519140c2d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 732064388 1250 732063138 732063149
    0x1080f0105060d08030c130e09100b100c0812010f05120628110c01020c0601060804080d0b010e0316051e061e0f1204110a06080609190e0115 62
    0x1400104070240c2c40741c0c030342645544c0e8810302040e43c80e503802d032010825015410f40b030a46000100000140305190b201150b00590204c0140c8900b04c0303901e0b404504440c0c240004c2d5800a090072540140d42c0d000365842c3c89013502841640d407600c032007540030402024098010544031210341509224905000307410500307603050200144081e06100809110300e4551480050707082503200039506101041e604203100d440800031056480d46418030b040e9003c0e401c865100952171141c20300018201d0300c50110980202d8210042d20302e426000009603000e0002c01a09a0501040d80088480d40e1020040748840100b0070000c04461401e0000300f000c010100c04190717800c2b00315840d400c0c0c03880d683d4000311040f18159050082c16a000c10ac07a1034503502603c58409c1586101080072900b03200c80c400102c3c80749200f91446404604500d0800950413018016080002c0c2102c000400b60304200300307003a41040072030b4544e00c4804500c5420909851180d254442c41765141c0c0d407080704914521005402815 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 732065638 1250 732064388 732064391
    0x19171503030d11090a0303030603060e0d080a09110d260406120e011104170c041803110715030f050c0a0e24040605190f140a18080601080f01 62
    0x20a0080000e075280104545a05459a24000302021031151412a000c448010b00005080c0d07540e41800b5004080c40d02c0305861a50030515480c8207203002003803241e07400d00345440750034043e1a4a045113000b800d100e0021100415401d00e0440c00781d0300c000c0c99404141c4607141008540e50706401d0041c4e10040c001110a0300c1c8001c4c002404203540142c0200d00c60044500001040362030601218058503104400c1803003268001404220b41700f10044806255403c1d10840b1014015a070503c4101e0b40d9180743d00f51b100303440c0450240001e2140003610f442c0021802141d190540380c030f240c00051a07402c4d07900e1001c6a555526821f07242040e0003400e5200080d140c044d814145015005003c5142d005035040c0f040c04200d900006071190010020039450b44030500c030703071613a454180140c100d0740a4545090301d00035217021594918440e4001c80480070196658010380002c25645074855003000b05450140700c0c00b481100040e41200b200b003002001090001d102c25490912258102500c0304e000403542e9 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 732066888 1250 732065638 732065671
    0xc09130821190911061c0603050a0201081303053f1503070e01061808120304030e0f0d06051305061302010f2a02040b2d03031813021917 60
    0x134580034043c500c000707003520815500d0140c03402c064006280c00928030181890b060010040c0b240006880c00f14a20130380b2400200d854100e003007040d804401500a0009008102c440d00a80300080f400400602001016900032641a4154405001034481508524107142002001d0b00c2010354881c9500e4143c01525190b402d1516041060341e050145000380240c0c41c0d0050440b0b907028280f04028406442660300304c02e14284001c0355648203030340640000d0f440c030100c0c84d51403400c1d0028800c800d02c014050070403400f0564910b801380074000c01e07400041c9504841000031407801e01800e07210b92a43c40c00d81041d0030040c0b0024003881034007140e000c1040210899014050702044091848000302c401d0102d9003021480043c0280108170981c581144d00000b0801d14041d407200080030b8001c90020785514a240c41c0141a43e900500e01c0300c03051159401181242c50800c00030f074000711200f0750380151811031954035080008401070841c90009011014002115400f6840642c000708641d2414610 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 732068138 1250 732066888 732066893
    0xa091415010903151d0a03020f0615011d0a0506070803060a0e0f040f0f0215130b090a0b07151404061803090b030a0617100e0c091308211909 62
    0x110a0584d00410300c40d980c2c0c040c0900107109041840030b03024064021070f0703207029182c43c000b501c52000054024083c4248800310b400710700d01c54448629400c040c1c0d19845402d007a4101d851300c1840342c4445503008891210040307496152900104559802528126030301d0030101c0c1404208070f4164017100301172101c0c40600610040c0d00c65006d030003903002860041014800d0070030880142e0807a000942c441402c0720200c4072a02201701030030b10301580300780080070390740c1d10500c03403115200c0d580d01c0c20350100b9205014808618410003500b506402108100f04900b18881003504a0760050301d2610041502c1040204100203801403420000003440a00100380041da40a012891700f8060f5403c1c07220b003c00090360b10003213684220b0003040f001c2010640303055000451902c0760038821104581ca820406401c00c40940014040c030440740c003a02c401110750301d030541c0c1d0b82c4000b1201400c4480070f40c00c01c5484138038052001c080301600c041070611056800c281020202180c20105007040b154185840d0101 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 732069388 1250 732068138 732068153
    0x31b19081609170106050315090c030d050f0a03060b0406180605180103020703120f150f0e0105090405030705010c05040504061203080c1b010e0f160e070c020a091415010903 76
    0x302d421204043c2a454800300d0940d0241c034440c1c00a94040c03040100c0c1014554049803258012400b940035503904074084001e03d07403180303984112000801c01c104071100301001800c00800000b0010b10780001c16075140c0c00c101c81c1c6540700354060000501c2c4001e9600454420100d004000c20540c20400d1400c4510800390304443d43c0c0c1d511003414160b000c9048810305005810034055101400020400c0b09045001e000c01070102080100d44004940004a800385e01040c402099030a0104003c004da880d01080019400000b0801c44060009112400009009010308070240a02e43c07202c98aa5082c0018003003120f10951201580c2c00404031210702003500101d48a0700800c022142941d0348032811842074014043c0c0319824078035845c004400d020600301150300214640d45c402900e41c110086d01c6606811500d1340100e48842110001041401d80164401c01c500d41c4098001403105540340900d0b41110402d0440301d0030380d44101d08000781c03040030b448040407454090030700510046c1192980013 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 732070638 1250 732069388 732069407
    0x5070f06020c04180f0b0a110f09120a152004030206090d020f03030f03040605070215070c030306090e03090a05041503080f0405040e0a0b0108010606050f031b190816 73
    0x1030107550766100c40c03400c0421302c1040007000d90f002007034803103e043e0034a414015a001100c01c8087c0c40e00d0030b101e0b05c3d660382505003180c03003040703500c810f031814942e030741003007105400c1c180c40840c10600c00c070100880000c010080342441c03e000a980042c40c941d0b42905808442c0e201d1503210ba03060b508000c01e000694542003a511002c50945e800c00010b0168408145e64188031501a40e040c44041200901e13821254011803107244900028030007030301c030010180d07550302a0850000309030090300000f4400c81c1c407a5030107040150184c60301080d5107584506620444c6c2800e05050076540000a800c200c50400c20240c00c0102000d450800a0080f00071040748044004d0100500070711000440c249141384a10569015041c010b1040114849001704c15a403050303404011500e0134100360002403000ca040c40368004541050700c0307071450280040f0041d81154801407078541c00a41c03901c3d08022904215026140064006e0108022804c5140003d0085400103200300c9030200c28260a0841035484030000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 732071888 1250 732070638 732070663
    0x1208041b2607090204082a03061909080301380307110709020c0a1e02060307200703030f021b06090f0307030501050a0b10020114270601030f05070f0602 67
    0x1030700024249078995003440c101d07500000100340041008a4403400c0810100100e404804076480d007528000f00314040442c801d0902689900814005107500041000d441000c3d0400301001445440641e80c5500a805c00c1c1c01c825449100e03820554058170f40594928120700d0b02d8070000c00c03000000390440c08280320040c070341400c00c0804204110242410003091340a072011000940d115444001c0382c42d82c0384180d05003990856070441440c9003120517004840229a0003611091640e666240c0c02d5a40107000c5104840c42003040d010300c80c034280c0500207100070750b00c699039602030b4481411009180202d4207800c0100400700025a404590b101c0741240c00e44041a90080000102200001e041514070b60020b40310313508100400c80503002a030301ca6901100b045443d0841610645022822521252046c2540c9040717640440c48103c01c0400c0c08203000b86041d44041000301200500c0d0400c0030a034001c40d48880840550410014240045005030450900500d9001c0c0b401c00001c0d664000e03002c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 732073138 1250 732071888 732071939
    0xc080c210708030d0b030d0512040b150402070f050105070306080a1514010b040f060c260f07060f050a231b04030f030e0603071706030a1208041b 64
    0x1141140c040a000c2100201070802c02d698032007000400f84400b03420303410b03c418400d000320f400c034040e00c9000d407090350700f0515a90400c0c07150350303076a9540e01688000686241c03541c2c3d40c1070031127104d07940d80c2e400103004692150103161084100d42c80c3c05401d44101401c80002d02d41000801c2c00101000074150f010603800c10511103400f40a14203100082c200c0040d07204086107450008147c21000d000100704540c2001058140301c1e0707a0f20000c960101c51140c1c001c00329800320480c140c2c110188425006803252603126a403900c0c0000200f40d00e01c2c1e01c0802c007118515250454a6401c0840f071041540c001e52403081402400e517080c2109090070366005924803a2030000000c0380c140724940607690720800c00112160fa0f41c58880c14042420190300c2c008500055030140014140d050035030030703240184110b07155000030001604440c002080000d01482d054402c0f080c0400105552034030702005440d10b6140d801c05402e1a041801da035008a80b500c2e074840302c00040411901c4400e115003201405041003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 732074388 1250 732073138 732073189
    0x40b0f0303120c0705070303020d090824071101060f050406090b031207050705041517120301060c02040e01140412030603020303070605060d050610180e0c0d050703080d090c080c 78
    0x2900e949500804d00d000e003051150907000300c1019000644c052039070201d91140e00c0c11543d2804016550300200e5030300c408065110300d075071491140f4400155044840e174104040d074070001301849400c4406580c00204114200031040025050a102d5400500282c4000b03108070403a40700469a01c0306041500000e02200007242c0b0144035050045101505000b0000c3c0422040380350115028462405480002112002245e8900c200000c280c150102100c450710704580c80c14005654030080244281e0b0096100c2c00201f02d085000e11460b4890500451481c045083c80d041001c4820903481c120b006041c60600c050001d41e5001082c0c92a155110402103003654a00010410103c0c441380010007512500c0144006002c4034100f802c2919800300c031082518400f0310000c000d4500c01c9000504680207200300503107904264481c480400e008078115201c840d52941c98800c203900c02050b440642d40d468840c0360410050300406001001e4800c02803030078039103510024030001d141d0b5000e000c241c000e401 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 732075638 1250 732074388 732074401
    0x1090b130b070312050a0912020607020705011803060e03070606360f05040525050109090f0b0312040e0606120f06040b101e020d1719090f02040b0f030312 68
    0x1084101d0413502002c040c0203c2c2880d1180101922810108a45d1040f000348185191440002c0c000c1c4203804940c01440020b20f060010360b03030111004010741901c04031850100c0031814074014850728040307603001503a0300c0c4e00d40d041900c110b40071a001401e1448041e003141c8002100333013480c1e010b010001d140c1407260740d03480981480140340c0c1d800180c00e1203052500308410300c05d0124455110282080640107054400e400e05203c1e024a40074540c0402c850400a02c0782c01802c0d488110000c4000750300141040712880002d1803e005c0c444404c44043c40040d050108006040684ea0889015070b1498104110400da0000c1054010010120a80c1c6880080c9540d46ca94000c8100303004054100f40c900e4030f940c4070003829540003c10043d50f145819080104180c03000840b0302d06000d1554a912071a0034410640c03000c950087c00b296416400d50303180d050700a85504c02c25a845100704643d942c2c5e500d9500c14042600c1880440354800ca070106440c13030060710007200319000b01c03580c0d040c41100d999500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 732076888 1250 732075638 732075647
    0xe1516050708060115050d060509090a0209060406080a140106080f071503020f040302040e0c15040801063606050a0f090506010206010f12170d05040515040206071121010b01090b130b0703 82
    0x903270000b0785c448410400d0040e0501c0101c4c010302058001d03140504580d40d03101c10f1000fa2151341c41191031541c080e580d00310106a07070283c00d00d82c01117072a001103484d59440001c0b03031030f1440c41c04035441c00d034000c44010020300c1002d007030304124010300742010b504203103a045104035940194400a80070380d44440981c8040390003486007041080008209143c503151450b08203031550424061480c25629000003c68103000210540f60a4031610214108417810744003840721001c0781d51120180203842c0e00e0041816680c2070024005000043c0f10b083c0440d05d08440074003554030140400707042d900300c2c80050040c42e400103032140a0341c082460102d000d030702038038144602594000801101190124111208080c0703500044d000724094012500c000c0301242074425030b4001990001e5001600300142c0c0d0000d408681c0c135840309140105203815020302d0409000e24550000c1552451b42d566014015256800442207005400074142941c20510b1101010480e811203009043c000880854030f007081500c103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 732078138 1250 732076888 732076901
    0x3060118060201020910020a05030d1808041206141e0903040b07050705040606092313050f01090c0e0618060715020c010506010512070e1516050708060115050d 70
    0x240030803018a555540c0028003e4020310820303407185c0318104150320340e5440004c4100c445600000074510384080200c4960003401c03035079102d61001d4071454100010a02505c0a00b00a100e02003600603059068175008040715030349061202d10003c4101404105030019800e0031441d8800240c103121900c03405080c83c5103004681c024401c48000203016010044041500d400701c54041c0d80130700c0001c0d1a0102940c000c3c46a000c2c07100c0c410980816000d200e00f100400240114000c0c010300000100d600c0300000341c4000315441540c1e0342803640108040013140c4109a21071505242554581035548005212440750400b005044d040c19800503406613100d5040b00c4000b0b50215040c0c9003507080d291044e010f5003094203074030714a51810001031615405030301100d480e01003040c1989074030f9139043d00903103007207584440300c54010a41201c1c412080c040d140c010180c0c07040e0000c6501c040000703031810f83c1c504030007038000c03450030340000c40100800e8509450580d1100302a041550300c40703500d00c04400c018182c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 732079388 1250 732078138 732078167
    0x10906060c031103220e07020715051305180f060303030c090409020f1206040b060102011a130603080d0902270708090a06051504180503340809010f020f070605030601 73
    0x1d800d098036401000c0e00e40b9801315004602200d0700b5070b440300c4090b0f84400c400e04c20340c403d482c200602202d101e840f64bc002c216060043c844440d20715240d5001c2585129440c0303100c101131a6000a200c6040c035540c2641b45d014004400030342c40c600c0c2101d0800224003c0b01031542c00303203450700301070011552081024442504054510403000c1c0085501e5a5904400d03201601c108004002042007548180189004110842c8813000c050030300d4028047c00071000078526107010341d2640007000069100000b0603840f0a440000305420180f8010080081134010300b103a0011550a12181c8040c42c07245401d501888a04000000d41c0d05c005d001d6040850704440103060702c0c942410861454094500d502c0140030554040040c6020307a040c41a0100220801412540c81400640340350018403480e1800c8005001043d00840f007002800198601800000c0b0b46000313002c540c0d00010350340200b0211810741540300400189140d6014546c541e0303180c1c0190020407a001001443c26401082c20004640 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 732080638 1250 732079388 732079417
    0x1e1104181122060201050108030f0d0b030d0e01111f020703091508012c0a0b0607020a0b0a020105220602181806010219050601150e030709090b010906060c031103 71
    0x402004681c0d00701e20304442c4505841e201d100811003500c1407040d01d060b508800010b614201c82e9032081fa4880d0812540310940c50780395401544640c60034005000c04404d280c0360381d102c038401800050709400c400c0644504a5001c0d1801180b00c01d0580c2d61841189803a1400594410f02d17803c00b1240346250b500221960084809900e40c2e0075800780a403030488000342c3d4000310410310400c00604208003001898641c082c000041403800c05158040244140002d103103e1801500d98041b601b200c680f503001e01c02450700401d010303080302e4080c0219580940c00401641c00441f480c80690300101044201070301c8113501007040c41d0845603d02250340245070007040648041400295102e90920403503040d030050140e022924401e0390301c801041031182e403007400b404040c0c0c03c00c50310194075180c00c9880010460311400c412101d072818415200603080781c40010842c0b82050800e800c8541061780702c0ca038141e01e041c0301007140b80e5004102c0c0c8501e0ba411b240110352402410300c00c0b071031809155044003912 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 732081888 1250 732080638 732080647
    0x50603010b041505031611160905040506010902040506040b09040204030f0b0702100507020309010315030c0e180307030c060207170d1d070e04080c070305010507031e11041811 77
    0x1075441400b030411251010f09900080000c03260440b40340c0002d480241c40400048003010055010b5070707000c00c010305100100e841d02c9900000c0c0c01c900900503031140a0b119500d60921050000600403036014140345001540740c14904030128419105600c41d00c1107a89000c9a8407600365100d40445008503000316440c0c1c112481418210800e481c190383d11000340c030034141010395480582c094540b082c07006030091740c00c1c1080400158013821990300c1c001c070341030014034000c80000c0c045003480001e0114008006030314505070384014160442c80d01152087d40c800d10030100000d51000c0c0c4003285076400003015031074050034581180c8444040401e0203a90b4808078001c102035140350f100c5030306880e1914403600002e00c904611034a4880500500362408070740c00010740818060002001c0d0143e994088518150352626424212241503c8070000213880b0900300403c050202400764541c0012001001485040c040d081014403883c461f41040d4002d51001c2089414242d100880314543c580300140d46 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 732083138 1250 732081888 732081899
    0x151e02101d010e010603030e1e030a0c153b0307030501240f05012105010e0105010e04020a0e0114070b0103060212091b010806210a021314041103010605060301 70
    0x11042250701c000c55540c41c14030280a0008140104401c5036015242d0303400c401d03081700034810316a2034081804a403003541c08400410392420440920705038000c901c0d00030362a0030301c0c191100c1200000344a1040211420a5250540c4144089200301040c0c040d1010490f8030340500d00351302840c0074a4280e050040180c008188a03042d0060103940c042c5110540111402010300d42040c812406442c940b40d01c0c800c400e00c180c2d4011042c2e450079071000b28011515404034503d20342941e0090b0828003088031841f00402044d60003104070801c040381180d0039030a1500d8400c009103094000c030400307810002018103101c8540403031000c580000b600040c1101441d81c59040100c041e40c0701044c40ca02c501903001c000b684554000c01c5262405030f050500c3c0b00800301100044030b401c100501b141c2c2d030009507204001000b03480448141079800850010748840c1e910b60041009042e060b0704003100d540d0078141d41311380000410880a03841580111409120346200020074014601794120070307000300000002045 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 732084388 1250 732083138 732083171
    0x50f1e0d0c030b01020115030b091906060501030c1b0b0c1c0605031605010807030908190201140a18030c1b0e1008010b0f0906150d090c151e0210 64
    0x14081d5071500c0500244003618012422221011400c0301c0f151a81e0380c00b80b000905003000c4031741003104001112100703d0b40742714001c40020030341001ca921507512402041503580602900300c2d000010309040209217101c40012019554000c00101640550000070340254040070a613444842112940c1201140f40b030140c41c0103000d94050305100e48192459120702c0b03d0a132030b0100680704183d5440200740c403a01d4050707001d080e610380226580780d42400207111254000310440480d400690010034080c0c040880181c15140c00744c0764680241c144904002003c5000f0005400c0e0790303241c07400c80384950060901e0005940c08405029021000101c0060b04c9074070750030154018502c14020560081d82e5199644c2241c1c850750581ea00080c0d0010002580c0c0390410140d640040c000e811800e400aa0394561a40d0f640400700c00c102c41e654414501c824880a40722507000b4054030014001d21482d5206d01904c42918008031881c0210210b454a801a1082c03106000907222418148541c1a100b0220070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 732085638 1250 732084388 732084401
    0x2c221a04110901023a09060305150603130f150905060702060f131b03030201020a03061a040b0703090806160f081b16080301180c0906050f1e0d 63
    0x1441541822045205031107503104558040d08160001d00055204000c100200440c3c00144a9082540e00101d540007151324680550300035185c0d40d000005003030190140440b00c000c0c0c98901c580c03601009010103615240c3c02c80e9004100d0111990103805245000b201031b500c083c00003040600d00075141015001c003a044404074610803800c1d554190342c0c0b502c0490361440d00322100800c51810342c0c00b16216030243d40340500c90310300610082c2000450b211401817103c9107a03004600503980011460b034481e034140700300c60141c80288001c60403011043c00410f458042c50141546004000038506c080501600120b0010300c00030701528400d24015287d00c4c0400824010100411110407010310203030b100c0e4050b14400d0303011440404103c880800e40700919082200070300b100d411007240000c0440c4000c0e02942c003c000034108482e145c01c0d840440d800f500d28100d20b0205002031890309006154000c01070b101c5002c0b070000c149458800c0f80c0d55280850301c1c45e40381d10340d4414001500b501115119007000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 732086888 1250 732085638 732085691
    0x80606040b21011205062208072604120209060d0212010f0b09163005090c040207080d02030a29010f0f0c03030e0111031003032c22 58
    0x1d0000f6aa20740100b03c891141d4200140103400c03041c0095041c920003112040014159914500380a099030384112996100070019201c1955410b155104c4600c10a4000000701b41041c03401c5c28a8600b41e00b90109004d06000284100700e00e40001d8182d07150b5294003880580c00070194645400464120f5000300b03100c00603400701c207091904400580c1081c0d0519401450341d42c0301003500c15078190741280c00d0890003422198082d202002c4582d40350501d055010038a081030400203213030510f10a4103117014051401c03540540c0c01403000304081003413241a104030307001c0440c026a81c0c1d958003200c0c00040206030491212113100300c56000301c10710b07601882034070b146003030700c6024812030300c004242d030030b4890207070510000b415910300c010011740320707800101d000310118002166040c0400700076a8643c10449981203034003114581002807560003442604401c489000f040f04541c885160f40e4800141006018025042c420f00c1003800c07250130480070b003c3c0d66004410000801800342d01c40d000d55050f00038 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 732088138 1250 732086888 732086947
    0xd0501020f130f0e0a020a0c06020c071e2103140f03040303050a1b0516050f0a0c0b03070503070e281502030c06130219090f0e011a01080606040b 64
    0x20415142240f0032105844056110503590740d500501d140107035020303038403071020043e8031402c52000606a0000e0100500200c000d0405c0364205240c504401414061300d1642d010394010030804500303000c0c803d60003c0c3c4034107158284809142410b85480302c0e80030342c801112a0000da403052511012003c0d5000d684250740912994403400034800030748a600340d081702c81004075a00a0505070007007005082c42580c1249200c103c07089038070744904052142d0341d07201c425000811014100215034130101d01405890b410340d825421702520007005030200174403007000d11081480000e129078691a0710050b81c600c1182c41d49a10014100f041d010b02e40302c0c03151a03049030300030008410700341c004802d8601c1140700718000c241035550203200d4141c520120344180d801c05c02001d4040d54210303d4010810144c1080000440e08440da058400102c806288a420240e450724201c80c140d0b000c04103910007a644246000710050300d030200010002d110b203030321001d0940c10002d80f1044030010a1012038450758610b05 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 732089388 1250 732088138 732088177
    0x260f06010e030f0705040c030b0402120f0f130f080708131e0b070b1305060414190b16140a110706050901050d020708040302150d06060912030e0d0501020f 68
    0xb0b069440300ea11025030f00c5030708640703820b20503800d2a902410045505141c045610a107030701c0803c08a032b0140110010044183c801c01007007002d40d40f840d03034002aa02c5164855450840400e080501c1c011030014054010007406406101c85403003601c50f040c0e005510399a80303080341d07201c41d07410003224868034a4501c03860001581c14074101213003104907030001402c02c1c40c000c1d540d540e4143c0c15034000e040901c4070b00e443c08454041581042418800d030f03ca81e841c054034010350300b042da20381252400c00111202c0100d4030360002803000c00140d42c00600d1400c9121005c0742c000c0060311040d180013000a120b03000800c100c5040b40d031004c41b10441c42d68200c180c1c3d1146803541c0e0103d5207441003100c0140401c03c1002200d8160320658001c1540c3c90281c05107070300f030988960003d034100c0410814202d500c040800c0d806007411162051800502e174600342403003034038070b02103018800c03140a0b403001e400d00450380ba80401c00d84520b005444070940c0000219654000c1030071120f03184e0440050220046802c09 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 732090638 1250 732089388 732089417
    0x81c0e0c0405093720031b06031312050403171801210f020c0c0d051213030c030302010c110604082b060807081b0a0501260f0601 57
    0x104590003210f003000604000c4501c4c0400442500c05001841d41d050000c580766803140c120340d00d8000075544545501038801000109094443d10010620b62003608001d41c00021015a40d0b01d47d140e034001640e0b0103842e40e451a403c1c8880c01d040500240c4076900741c5809030304c4540d014000700b05603403213040f80d1101c007080203910700303031600070701401c108641442460b00c0300301d40c02019030780c0d00038401914403000c40c40382400790415101c2650220b20480c0c1c001c03074003c074400018440301c42c9014068034000b9062030551074141d60748a410154407050305c0300040810400f044280014045c1d5000202265003da40f40390080c000c01c080143c1c1030010301c032140396610000001c180b40340901d40001d075603800e107041d000c1c0380f100c0c14040d144070146a0300d03806480e0280310740d41d0059400070302c4c40101a215840c0341211150400c0c0c00b002403024005c1e0341e541062401c2da80d000c41c09042d01c000b840e10b03064801300c04c1c000404455071204d4041c00c0c41000020041d540c4c09500707160b842298280da85a403076241c045c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 732091888 1250 732090638 732090641
    0xa030e030301080d05090a0807092003040f030e04060f241716030b030a0609030f09050a0b090a030209090c0a24030e16090515090c03040609081c0e0c04 67
    0x83c0121030b40c1d0b8000c000f40481c0c05101d50094843e0b404010315011880741e9803880545004c2855100c1e42000d40c54640302411040361001e603203076041008040c01e1039072400f5510f07401c1d00c3d400e0050040c10320150985a0b6000e848503031018000e4002c03a402d04101d242c8480c2072207001b030114082c05d448004480e242c83d04640c0b06285c80c20701c0a0585021380290b43310000c030078a038101e650346902c0404d81d491a03400440d907020000402c80301e00500000881d00500e04008012210b0307510303e201400121142007151b03480d642d10180441395800031694958003010001550007038154806507005030b032a0f0500054140224948460110407610001055035484120f01d1a85c405c2c07902d026601114040c5008080c00390304070071032464110b002c2e00c1180700b403a8a1900304d40d0140d0441c0303581030741e2007040141e000901014103007900c404490700400d500e40b00208c040b413844010001084903455003141400c100d00b50043d04c018051a0101c0381c3d030072200c0701c01c600044c04180d503050f0840c480c07940a5070f0300b414903 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 732093138 1250 732091888 732091891
    0xa02160c1415121f0e10060906090b0c100914010c0305070f03020318250b04050d1e0614071d090a180602041e06030b10030504140f030a030e0303 64
    0x94101490a0100ca843c51040c640340091020005608130f811904c204211281400083e000307024900401d42000c10b0003440d42119900103409020491201740030454001e03000c001102c1c010300c0c840f41c0d10000000302130309014544086441c1e440c01c180d5a181042041d000c02134441c09554002c0220904e410170032000d86005039607450100e401c074000b00740418441e8004550001220000d00d0030203015059041c9018500100713500a50001c581c0202c0c0100a000340310000c25030000200d01386400c25000990820201c80d004103201008074001d04142010648000099009034040064503801e152039983c000701128400d00242074114443d003000c0d915000d502000001400024180da07489085070010641c490221016011501d149000134105000920107032246611540c00200c00625414004003150071003405d05060500390540f540701d4051240000f1020700e4042101c0c1c03500d041a007440d54a107070b07605c04140100d1106041d48507002008003201d8442c0d40c3e04001c842001020252603010 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 732094388 1250 732093138 732093169
    0x110607050301051e0d061a01091a0703110f01020901320306040f05040503070c0b040e0408160501180b06010504030c05060c0f0a0c08120a02030a03050a02160c14 71
    0x405100603c00e034204042035110021443c070312180f4000010001490001490600f101d0998444551510204d04070340d0000102000307090504003039040a0b400b803c401c4181d02c00e1840d0800108030403091600c6040750340824981e0300c00303450380c1312098906c0b1400f0354001c54805003c038a0b1080c4010381080742c0100b1f00b0001c0d45030f0070f40d048000c104c20201a107652001d02900e601545031254960840014428140242d104400455448100d850000c04920a941c494400400188002c005164010f2660faa00540c080b5911756034200c0031040f84490000e504c4044c00543c0b81030140e244800c220708400ca9054040d0115500581c0c483e030044130305100314000240640200c6108002c0360401801a01705800080180d6040c7d00202c0c0aa515080c80c4400903a950350064008110080040c403642c00303044045c42503213140c0030a5442c00b03541c0b8460306030124209551400007405a01c21541a5000c06e0403080c4103000b01d0805040240000d5001c0c011514003854031580403219280420041c0300d03642 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 732095638 1250 732094388 732094397
    0x303020c01030c051813290901060f140a020a0b090607080109060f0b09211f02030f0112020123120603030408060613060b0a120c030605031902010302190c03110607 72
    0x81400a106083d0710641d511100349031110702491416480040c01d10081c4011f40311802e4240440082089511040c2e01080c01d10001d10040c1c81c41d81d81c440050203001c0220a0119541d890f068412803a00180490260030382541c60140284042c4c08109203002c1c1c03a80b80c0d05c00c84203903280d800b03000c203c0300c3c0e031710a559845181c40c4040041c180502e01400c011b00e402003103400c01d00201803113525039541c10582030000f41c008201c0765581c0d200d80350024a02d501d103180e0440c01c6150210084117030319418040c1ca20000c52903440002103a03c1007014250135018210049034900182c40c004045411400201040b90415000503d440c200003043e54203c1e2203140041c00182c42e0041840842501464080d004e10744414000c21149100d500420407040c4655544040f070070b4400404088502982482040604009040007580d5002800d0315412415000c1698408110300c0107070002c4c03140c00c1100310304000034050030721401e421503842c46442e40030380c0b00c080b082c0ca41d0180c0b0035121902114590040b4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 732096888 1250 732095638 732095677
    0x4050601050d1e050705120c160206090607050a0503040602150f1803040306062c150f031009060605010207152708060a0b0111010908040b090a0509010303020c01030c05 74
    0x12041904041c007404090051a89a40f081c01000301c00e64400301c40400219200055028102c103e00c0704050740200240c580d5801c000c00f1404160215903203960207031140401040c401c2042d560301007110251940001103c052010a141031900c9400c64414040076020701d8060702100301512552a1240014020801c195a207a2042c40904884030b683c5000da0300c0103110101c0000d17414403036080a0000414108620802c40300174242840b5030000c100c011440481c00d00c080d01c3e01c1c0300004503070601c04a074001c1c040c800220201e8601516100d5044200c6e00300710300d65040c40801d501c03403025950282d01341d41c001900c5680607403200c0c4030001d4800006009928249040b08160700010b88401c0416540b007080f5503840c9010326102041d120805010741e03441c1c01c00c95035030304100280000600c60009021220482c1c440c0d085c2c9014504c540c03102c01c180000c070200c803035a61020308000f40c0350090050341256181e0034020740d07030140380e510103003c6840c1c0039000088a01420642c2c940003000d00c1c41c4000c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 732098138 1250 732096888 732096907
    0xc170711060717040b07170f0133080402010e04020706051e090d2f0105060406211509060203090f06060a030f020d050f0f0f0c1008060904110d110f0405060105 70
    0x503000001c1825042001078a4641507590000b000c4234000ca460951502a07541000a202181d080d00003200c4a8400010301885203860007214049404500341001c04441d276503400103803150b011035507029611610000b01101000340690149018461030710300f041f030000b0f0010902100e02800d907280c05455201401081c1c1c160704c00e0000484091001e01101848442d140102c0010b12180c04181640e945030030811403107040c503204600041900450311000000103d0b05000600759071a00500303800e801001071a02007000d50414076140e6401300045640745401070582c3d403100280b0720400410302804001c218507103032805ca00403d580d040b402005034179149030308110101404044c11242c03400344074031841710302106003c411550346404010b8252602c10020041c104409526094450304c80d54842e14a0240d000d440740c1d40c042410340761840c0545450416441c01c00160310740c158001c070140301d90b4003005160b502001c1004016036213034121007110b604100c103840e02281c0c06e40c0010b07070a0106450703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 732099388 1250 732098138 732098153
    0x606181d040b1005061303050d0c03200705120303160309170c0c0d0c050f04110d091401051009060b0a0f3c11120d0c17071106071704 59
    0x810150880b89158900c1d51031340030450079003000044041c0440d40200800c00d2080c2403200c80c10010440ca010b41c1c03035160541c1c002e00304640b850202905220244009031902c2000c0048002800d8003c15100c010b10580c10000c0d13a0740c0c4120368101e81000c0f0160003402e440c2c00307801000c1041e60702c181195940403200713903038000c00c0d04803e88407030151040503c0302c242901e4139540d044031140113040301c40b103150802060000008500c240c031400399103032086110700600504250f8010850201020844259a0501c1a10040040d032290004e503e44814811110464480403080b0f498103d01031004135a941e10f00715150141400402c045082d8045400c840381c400c400440040c403034158445c250768401801c00144004c003e00ca030340041140409950302d280c000302c0d207001c0f500304000100f200c2c1001e025203078614020040340e19807007074540160841490041400c169031074055210448689082c041c02409801448014a142e00952010400c1580b05180b51fa1400441500000d443e40705c0b5500c544 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 732100638 1250 732099388 732099391
    0x3050702060a1205040507050103110c0c0418021207050306070302210a060b0706022101060c030c030203120a0f06050406050303040b0702040209120303090105070f08010302060307030f0606181d040b 87
    0x104022483d0300340c0340c10804070310907103000354040e01c0103001d83c80c108800542143c140620721541d03102c05000c03d541d11000021700e00e01e082c20541300850030403008001000c1407001040002d40c8000c03c203c0c8000c84550000d90074013180d030b08a04982003601c590006408a1051080000c800c514582a626041a00d01442604000540000249941d075030240c0b4072a41c10a48040340c10711340001d45140c0784410911680000c1c1c0c0d0725000f02005501d007050180591096842c0201404044284031007031500a00554004002551030085145440812040145940117104800c1489c10744040380d28103192151800703803500580114900360800c003040310550400038080740d015408119903c81c46e1142c071004410500300000542e200c4c240000b01c81d081d40c0780103100c402008851402c02c85001d0b481145141180d805a459035500c2d00d07840e00440c094420031040042107401c00100041c0703240e001c40c2508501c1c024181d10403903141c869040c0800489010158103581e40010042004500d22290b82c1c0d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 732101888 1250 732100638 732100657
    0x1060e15090d080f1e030c1b010b0d030c05061605180a0b16031b0312020903010e010504080301150e0a05040b06070606061d06091008060a080a0f1209030305070206 72
    0x184110b01c0241c1e51480c00b0b41c82030403a007901c4d550203e007042d1101d04012401a04681215a09007585006421010a4040c40c89034484010072403080100c40242036100241d0201d010344080c03100300f40e40c00c0150260b10b8070182115640f00e040b0000705007924451100012201030b40d42c0e103240050400856151072103041c0720700d9001140c41000200f490300c44000f8840081118005000c140490601030305c2030440381c1103013000d0b50080c0003400000380d2005050900141408005032140301020119005085400341d01e80d08d5840c02040c0418072051401440c101c0c0c3d80051182e01c200b296480c01c9a80f130f01980d07130140d048024407409004a2415030822058044090070f498244065a2943c50613170700035a01020205490950004000e44c101c083e030400c00c982600c0091038803c1c503070045050007008c0c04c0070701d08001240000c03820325134174001840020806501120341030309140c1007440080c4c4900804a640800440c40244903034061030103201117a405803203c42c1440219002d100c040d070311a8504 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 732103138 1250 732101888 732101899
    0x1090c0801172d061e060d080403120c0b070801050f0f0a180e0d0f02120c06070e03010f0e060f13120c06140a0c02161404180203030f070b01060e1509 66
    0x5081041c1c0007000104e21a400044100c445d20720310811110a00d240540520300611040b901d10010915040440d801c07a9440160510010748180c401c542600344640000d0885480009001c03503294040e070014186c40342100c003c411258000c080221a0510728503403508640c0e070000030805150084030802c2c4003c001c000c04600a00e401c02410b042c24101024500490350003030041c0d00580d41004564941d440300807181d403609540c54841d9980744030042109041211385040458191800e40140c3d0000015110074804124442281d139103510086403007a00c0c0103030700000500c0d070480701482c1c2040c4035000b1900c0c80c01c0e24241c40c02180c00083c0b0700d9080e24100d443d0f0f0450420440744254807442070f240b40f00c00062000041400a084c0381340c0555446102808003000d00684011716900c1130b44078401c44001504100081c202400c03400c40c164060350600010805030648604034009182440c441c490401003aa00d0306070545600801451550708006080007407100303a0f00f0f21000786030b4088020072 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 732104388 1250 732103138 732103213
    0xc010906091b0806010e160e030d0302040315090b07050f04031a0906090d140c070b070303091e050303040f0f05100f14040210050f0706020301090c080117 68
    0x848100391911800e08980200c1d20b016061240302d0440b04010140a441c0701404541d4900450380f040e107034015003074000d861b96010003001d00a01a0120780080f007000740c16900c0c510400807002d4000e400900c03080d5400140048144030040c00391080e141d009a10101c07940c166101c090b01140c05800400303200200c42010040803012a684203440741d55086409005030807031804022032818031b07a0240086090f5805020076004858221201d00d010b80c4031065507030b46030054656054988402d95000e0b180d8140d00041640616a040d0081030743c1c1401004a500c8440c010030203510a402c0c520000344c01600280085800603208103082d00384103000700058041030f101a03c0c0c16040022001540030381c15500c0240c00c0500e113250007100090b186c401105e05a920b0260007140f0340003035810840d020480005080c0d20390400500c1a50b20098020f4811912903844088040043c80c0180c94070307001ca45101c000007601c1d030540040840d5010030601034184490120704808105403910600310300050140e9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 732105638 1250 732104388 732104393
    0x8060d0b040501020403110607050a0b07050d021b0c12060408070606151d01021b04020c151003030311030105060d0b0103180f020a060503040c0e0a020d0c08040204060e06150c0109 79
    0x402181c01140107600040e034840c0380d49400c1994201c0506901d001c0d01c0140301002c081500444d4130782c14103810000d00035440da1a0041118035104000c02419124404035101941e00c1d04941e50350b802100c00130844981d00d0300c80c0704014014483c40400c14003903000c4c400050004006074060481c0611814006c41c00c140c803810285000c0c3e007094134000010740500b8886107000100c81542356620402c3c0080e08450010624070100f201145400600464001902c201d80c1c0c2c00811551200d840e00da0410710985c24004031903250f1040a1005800190800c1984e1040007070410441e0304942c8010010780c40c100d21b103071148002e86083c000c05418195039003410341946013030341d00540d10603116000c660110042c1d0302c10000c01e0f01441d0000d204100d020300400001548403d00401950741108001c000340c1d0351000d0b500042d22454a40c4407041d8140b5009155094002c00c650f070166200312800d00201d40c03100200211400125245540702041d50b80f6584405001c00c0100309000c01c2000218441150740c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 732106888 1250 732105638 732105653
    0xb0103020403021e0108010e070e091302120307030f0201020301050a120303141f14010e0d0c08070b0c0f0a051009030e0a0b13080a030804021c15020a0f05041508060d 73
    0x2c004d43c0041400c60750301640290303440320640c0e01408051007455481c0c14400f000400051603a40e007030b03009051348408600c602d81204070692046a0041071040449061240c030b6890340c01405080300484d6150201818290040c000d903811f03124043e14580c041842c0401c51090b040050b0001d405050f030360858000a0359004200912510040d01030b0041c520304c4003048200b1a1007030b80200c1e0700045040a040c010303070313106c0c1800814403021a009640b103082814451000c400d0b81e0300a01d003900c0f84917400560b0011030000f410007a94940c040e242d202c1585141640c4482804000070110303007044409660300b01580d4424100342c0d009250601411503074002141d0041140c2c1c11180f0b401d407001c00d514010300003120503003014220503070280c00c100315590380107400e00700d01610091103008094010702003941c0c50b2440020b101d4100a030765511416403060721000354085581c07807001030030720f4241c140e105000c0d6007190704492542c404c000d0b2081c207952048482c5400640340641c40b400056001c008554031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 732108138 1250 732106888 732106909
    0x3041d090d0f172d041a04080d1b080f04030906051b01050a0b0906060a0503010909151d010e0f060f09240108060105010306211112010519060f090b010302040302 71
    0x28844544131072000c2241d400f800c0c8800b003c05040d4040100200800502804c10041030b0071165003100045c0d4a030ba08d4403982c10301a00d10603600207480c0404240041c040d101d86000401d030652130310b04c000e403100c180b0700409420844019021030300884003007160301c0c442d4000b0601d0021300808a0110000e00c5405801e444040d1103a81d445c82d1a0007042660b0310b0140d190503003003581102c81c240703401ca07041d0020b0701501051050003c2c0b01c0d9921070f18824058509448030f40302c2246030003003004000c20310020001c21503603240ca01141d03107400940b9040c490001656001c0310084001410703940e681070004500740c0360040817100320b401201810a50000c02014a42588403001c9851590b581840d951914007141640a141014100305081150b204807003001d001400c040700c1305e5441103c0310306108200c0e541031030f0116000041c42c4038034010a0307010760001d03000340005504850044140c004001c180e0718240201d03115003002010411010019511502602c0418180541000d035a5000103450600c0d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 732109388 1250 732108138 732108151
    0x30a1407050414160207230411120a0c020304350a0f05010b03060c0f0904060e1302040605060c030339030910060b0415031b0203041d090d0f17 63
    0x542c00144120074894401c4c1021221a910040152a1500082c07400303000740301e411000da00c2c0d020900001c03240c070365410070a15511801413450b81c41c294400840c50036101115001c00310341c60920b20301020340c404401c440c2102d11010200000043c0004c07a07200c440048182c03e440c5100a040c03003400941c0900c4400c003d58044c0b13041940c0c2410604005080d1460950713068030a0f0081802c104904030083e081d80d0001c070040301d215460750091000700d0000d004541001c1002908507080110b1004143c001668851003a1070a001c0595105e06100007400386542e11541504140b0000b400c1501d481000c038004407940c80c4081d00262a40303440800c8410b042410200700e100001007081d41e850410491180e1803083c01c04106031450460030007514052070140d101c1c1c0603580c3c1e5501800e80d200743c110f41c04806240c42010300100304410065625030003032151507030380c1d50307075010125220904016240c41004004044d04100a0016048504036440c0b2480020300031000c0781c0b541c1822958469510510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 732110638 1250 732109388 732109421
    0x70c020306010e010803030406091a0a0b0103111201031b1d0a06060804020a0312050d021204060c09080c091902070b040c08011a101710050f040902030a14070504 71
    0x515a005041c2441d5058114004044400c401005000740001c2100e41c0580c01440026031300000d49841c05958562583d0342d00d2420003c000c0c0141401c0e5948219001942620308200100c400144d41250b4050040300c845512980030040000c1a440c40103d042c0421550500c400d8603190052115101603110310424080f107002c0030003140340c000b481510050314071810402c001c1d01d81070f0b00264091490b800001e001c40350803219042650b01640982d0145405e2010540d1a401c0741284501c0b403000c211425290141010340841e00c140c0195521000c0d0f9a4940203000e101d1900018401c60341c43c090000340c1f0b00c440d1804085460030091018207104c40c4a0710102e41c06040c503050451040107e07800c131420591415180c03600c1c03140030305000708070010b050780c168100208410042d64101c4030003801c1b50052420604010040c1061a03100c01a944204c4580c0d0040c0d8900060008a5080c520000d425520181c69000400c51290403140b503000702104075000c083c0c840e4082019039051401141021 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 732111888 1250 732110638 732110657
    0x6080405061e06040902010e03070306151202011e0c0602040306050a060915030605060a0302041b1103040506030106031a120f06060f010915030e0d110f07050102030406031a0907 78
    0x5800d001c1290040e07042d0034801003100d491400b81404000107070145102ea9900c43c000400c690140829401e1000c009080e10206a42c908141001d00002020381c0c50284e5015400b14840c400305400440564040c1e48001c0b03245240c2d03e482c19620441e22144050040980300e50001480720700051028603c100e1010400342026a116401e40e032003604190001c506000100b945034a0f95a100c3c0300f2290811008140c90304c42c03078040f4002140c00d0308065001800d00907041c04204a050040c00c420035103640d01846081c445100c1d80d2240100c0c042e85a01403000c10040021602c2134204a140b19207540c58480f00000007000a08002e5803500c540c0d12075004a203101b42c6488092002c164441400d032000720041c0a4400001c00d101d42038080c8100300150703401d54a03003982c882d81c489074051440c2c1c2308030b4002195861000c0c00340154541000d10920880c14204d11130036000c1032140c00c654042c3c0065040c981820000e44c0601100309921098071040e1a80c100c05a03500c4c9600c038043d0900b91117200b1203 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 732113138 1250 732111888 732111893
    0x10b0604030c061112030a021605060a05010f0f0b070b0702010e0109050c040c0801050f010f02031620190911091314160806010309020103022701020708070819020613060804 76
    0x306900c01c0700700c0703001e8100000446a5004585c220b0764000c0d02c904005a8403064910307050b441d492a0721015000d441008104071000c102275200c0d6050398030720b0910702445959800d9a05869549001e4215454010b121039400240190721054000c4558000803803003041001c0c2d62421500c41d05403c1e9496404100010301900340f030710400500c0070a52410406940c10b140c04100d0111031030b40014100035440c400c080d003481c424401c0d0364800c29801801d5104175954206910380c903011601d60b00743c0001c001d642c90303c1480c05440c94148040701070001c160441c43c00c54800011306000e00c002c61498010081036080d5556481034507860030742d0910000d083d01c80482220300e001c03c000e284240d404200c101828032641c0100d1400c0d800318003441e002c656801c0303d1004230040d000e096241c4001380e902c240e90044016400c518980489c10a90842e0425650b6821403690703625940b080c45807a8114000038201d0010003104455198000b810907807600040c03507048840400d00e548100d0000d03a0352400c1c8400c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 732114388 1250 732113138 732113147
    0x5220c03030908010b030a02100203070b01090204090b010305041e0c08031b0706030c02250f03060509010b04200f2208101a060d0f0c0f030f0c02030f0705010b0604030c06 75
    0x1d804414000c05c078900804010035520119148060700c81c103040f500e40640640b0800071611041e0780300000000300e5a5400d01d15001e50418002e0300c01c02ca0418410140b1544688521031003150072141403003644034080000c1e100725a83d1001960749085004000c070380600100001c00001140c50a010f022021403803569042150b80e81101003014107182d4820304d4103034001491001c407000400a10300000045d07038203d42000950344424613505d00c0440000922502c2d40c0280c1c4600c0c00c44000b403001402c9501013004440a003405410b001000c442c20111100c0c9000140070b81054544d180d51a0911440980300034003001d049044050802010030b0080007000d01c0513405401c2641000d01c0b511040c68013629562240c1d0a00f603000c2c0c0d03000b05000b81e081d1015004009400404e41c0200105801c03580010402030100302c183e0040f0b03040c1a840c1040300c07028401c0c0c2207802c9144d07000e03504000038a250500d00d9400b81d4000d42d4a5903c1c0e500c070203680d81c2d8a0000300003c511904400954070310b0100041d1 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 732115638 1250 732114388 732114407
    0x30607050901081b040b0a0504180c18230f0301020c01050421090515070614100b1204021210060609150203090109090b03120f0d0b06070302030d05220c0303 69
    0x703002e4002c4560100c0780e013003004c0680c0c060341c40c03505051b80c9410f02d102d000c0700c90307015603480010596204109000040003580c0050903c0780720340c0d0780880f440450251100d001600b84074580c4d650448419058080704c20880c28004184000c02c002d100c0d001c16400a401e980000d620302000780d668809000400c100803440040c01719200c640002c503400c03918030142c547c01c0c0f20322856001d00c6406034611441c0840c0c00c00c03505040e62102d020000084c800158800025044070030300c2d0340e0402d41c50040b50082d0100262101804418411045a540d0f80d003846144468002c2845451107100142d0300b00e04000e002e550050700306581c1da0000240740004003502c5445087c6042c0664104116914a40c1d81c010044003d40c0c0144001103994044140440e01d0605d0b515203c0c944400089196404016084014118041d011806105a0360f41c0810803010f445070350b1005016038800c0050303103445c069540055a10411300100110710754081021182c060464400440300300403904014004c240c0c104001c1c1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 732116888 1250 732115638 732115651
    0x12150e04080910080708070e13020d0501090501140a14122a04050906160210020f030a0b04020408070603090503040906030f0b0f06010203041a22030519020f060d060503060705090108 80
    0x10000b90405c030701c1c0a8820b0710041e0004080010003420106c1c1d079120071007503500c03208000b5411513940500c0e1600c0c0000740000c0c060018002e052000010b203c1400a001100200d0012311640915251010345680010703040c140c0e03900311141207505260303410140f01c1c049421222044580c240101102d11003550396481c0e080034402c1d4500814003c03000c80c0001c480d58005460400b80240401042c0d041c0e1410024600d05004140001035100120703e050b80a0340c042d0712444401d01015880a080100341c0c0194020000725603c400c00410800f03100e9044550200d0184007034074a847d49515806041d01d855030001e940c455485c150310010400040c180c1c45d4400c2026805000a0400341d000039141e215520131084501142c0a40c103083c00740c04011101c0000608800811400550042c00307003c1280d0b12003690340340906c14120700b441c07205400521200d0707801081c3d000d0900c83c131002c00400790002c44001300c4141d9110f001144c1a14104100b41c004ca030300340c40341e80d11001a40d0004003111802001c4 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 732118138 1250 732116888 732116897
    0x90504060f0b03071107060906181a16120804021c0506061306050a03051f020a051903090501050711011505060708160c0906140d020112150e04080910 66
    0x10481280740c0c941c8001555803a41c2c10503503944440d4400c41c2d400344001600c01d0140a41c0c07000040350b40d008076614044905540f100402c0d41480d6040c4552034415200b80000903440f13891103524101d40000400c0301500c1003c41400e02041500c841c2001c040600e03a001c0810484402d000c15846e040e01c90020b0050740c15044c25441082d0b03a285621080007a0485000b40032841e200e58a529454012001421028003082511962403c0c10303590344c0d401444030070926901000903645102d090003110600001500c0b51440c10003040b152842c0c0c1900380c50680304040c0e0341d401490008400780162400340b00c141d40e80f125981d0007480064215118550302040c4610346080401c115100e40084c3ca5009030480600c40c0c8032428100e140345001000e240050440c0f03480c540110701c0c401603510101c140d032804040c0c421107103200c01c284500003a051074044e01040603541c01510b000080d4208140c080c1c402010051603e80e606401c203840729095808880c0383d400400c1c020b90504142c4074210a00c5c515281 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 732119388 1250 732118138 732118151
    0x6020c01031a0d08030a090204090c090510080d082706060a050a050d0b04080f030a0509070f0302010e0409050f03070302070314010207150507050702090f042105040612110a090303090504 82
    0x103004070b010f0040051442c1c0340031000400440c8198421000160050301c10700c0111640c2c5407024810742e0354081c4807007580c61f0901041d4030005580442041c8e401003002070400400f4071006039007098008100d03000d042d40f5241d008654000151007258180400f000034500e505240042104800541d04030f03034000c2855120400650f900ea61107010000d07001203400c1c106071120f0800c00305e40d11135454655410f103000014000d0301c644640c84248204003070f1096a59013a1681032000c4100c4040c4000790000d0380034032040340245081e40c42100418407440842d61040b148414190840d04175400980c09604480c00c2002072080344042e041900550900071458181d02e036543c04024504441d1071070003c3c2c0e40e8000100d129002d0000c981485400074071044592402280500360600308840440d0b4400340c404000c8103140458102100c0c0c1851900c0f418100750a01104807203d1074100b900031050340d00c5102d40a40000e40e01d00030318541c800d694540d80300740e055040c0030303100c60207541c410f40c000c2d850f249 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 732120638 1250 732119388 732119441
    0xa03051b0307051c0e060103030206010e06030111120a0b1504050103050c04060906050d02070602040905041101030605011d031c0302070302120c0307080702130e0705040c0e1e0607080406020c0103 86
    0x3d0845002c0c3c40082402030308400f005500000404d552004850a4821040040240340d0005840c5040b00c143c101000800ea0790181818280c3c0c4c4684c002503c078030400d0250584a105900c107003988109821320004000c0501030029401e8080c00c0100c0a40c0d041c0001e0601c10b950381070050031303401003851401c45e141524042c1e005003800b00905c01d000400401051640c00c852181d0106e90001e500940290348903905c0b5042140200ba040c1c9003107034044580e4000ca0125400303400380d9001c484050f1a110325100c102440304c140712030306642083e030500400800d21404001d05e032030011200e40965005884d20003624000c1e281c000c15820308803400505101c1e001d2010400821940039590041a003604d03003080d880464803c0e46500d07040c42100741040c2c42c504001c0400500310003110400c030303000e01031017aa5003800c4d283c0c000c04a020070780017002404007200007100001003071104200540498640641a154020990881c0d000800184c1050915000c69a454040e0400d403441a19011351514440c0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 732121888 1250 732120638 732120647
    0x23f0f0a0212070e07020303100602010e0d1b0506040809091308091504080d020f211b1c11013c1b0203032a0f09040906020a03051b0307 60
    0x803400900c0390020b50800c100c030388000d2205030010919980512001d00306010080c2d226001120400585d00080c0000203085105005101ca1140c80501400c8400c002035000c89001c11482503664031241030819840010304e007000010f01c118028550a034407030406100300320600d60b001c0c01c0b07040014035004074000403a0640e0202d8004000c100c6283e00c0000140d04003030391a010b682e229660b03a00030b01c0c1a1115071070300892455000894038003920340060800041d0a0007192400c00d1005800d801c2c0b2146480d400440f1300c00380010603403021150f0705480d8102c4c402610400d80000e4000411504203814500e000340500080c481040d81d410980190b4030020400341070040754130b160904206286540300030000c3d4003142a0020740c2407502881c400343c21019650f980142d1703031046440d21200c03074000c2c0c1803042d8142905000314071403094603044080d40d1107078081e0410105107504c15554007001c0002240c0c1d00c02804000e580380c6022500b450500c9500b41040040d4050000c01e80c0100100001560700 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 732123138 1250 732121888 732121903
    0x5190b030402181306060e13020103090804030f03050c0c0a051302090f030303090d1b0c0302090403020c0d0b010626060d03020f0a03030e0f03040311010507023f0f 72
    0x401556125541c038000070f07160794000c044401600026909105064083e01d1a0f041624080c070710030700c0099942c0072510f140c124110f42c52031420b0303c074140d0703100158400d820044006010300c40407803c0c02e45035182c6c0b54040c1000d40045002c601d000800c1102403200388000005154101c940045561400300442c1c041c0780498981203a00f54001030101c0280c0e1264030220345c0000140c2160703120318189442503600c4020904507001f0482c1442d0300c0ca90029814400220181d100e40031a24003481c560030303c018690054001c0703095000b1a40700802c19102d14040c841035501545940d0495407620300041e1000c0240e1000c400401100c0005404125030320511a40180094565030b4510750f403410b00b00c0c00c01414020b100d40c2070203450021401e00d50325405c2100d80c0036810302658081a18944926500d200d548401464111740081001e005e600800151810307a0003d010010384020202029000f41820003956843c079001c030790081c818401c00056503c1c610061401010a4007172100f0040c0c1d140d51 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 732124388 1250 732123138 732123149
    0xa0207080307020609040b0402130303050901030e0c100302070302102901030b090f07020a05010f05150603040309060e0114131a12040b07030e060907030b0f0c030a09030203160f06060519 82
    0x22200c000c81f486880b1036040324801e01d92040c908902030703102c0c500107110f0b600140b88030340000e00b000f103c003200c04808520760143d94002092030300902d0440205030701a400502c2c059055010b202c46001482000d8003824203854101500c001407140d0081070034148a6003c42002d040503e0004030b080a5210826215008a0341c802d00340c6440e55007800480c41e000c110203000307000b942001c0380d0318410385d017580000f030142d81008220212a040306040c000301c1e0104581c0600014806082044032900500e01c00c03202542c10700d0000d440300d90000d6421b985510031007460707512202c403000412640c80c0211801902002c0250300618082403036134086605100648041c0c0510301d2140400c180394045d61102c0102d030b15000a441e22464000c0a00303440721700521054401000d0b25000135100c1181c86643ea01c107640c2d19800c1801c5448a280c10300c01050700c02012030941c4000c001e042540690030700b1045803688910b5008814802911f0000140c80309a4031032400f489804501030003000e24044800309860 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 732125638 1250 732124388 732124391
    0x3050d081614040914060907030504150203130218090c03030903030f0f072f1f0804020a03050609070f170705010804030e060a05030f0f040b010612150b0a020708030702060904 77
    0xb862400300e02584034584c028aa028580962981c1d407160f0800c4440c401c42c0d00710b0b10f54029a803801c0095066500c1203070010140ca0402d45026201005d6038090b5411800801035064181d6056000c107000102d4803c0c02d002e074440000c02c000b0100b00c10442e84640c02415006035082022078400300e0f0356401100500208a000070032184440600081692802500003d020030a0b8900702c5078039482d0500610141840316000c620020b40b400c00300c0c2511301d1001032080d00450212a04c03000c13a41d40b00c001e44101e07030040e240c1100201203041000f5a50040050070080d0451500d000b011602c600d00681c45000015142e40d240d054640303004c540c0303a0454000b801c010000e0740c0d0390b140403100c2c401800012030340b0000101d6078400c0305d0350042c040c501c6103440ea180400305072100f442d8580350800845004000f007094000502c0046e101d40c21100c105007050402090040041805044209907a0030000c2d1a80d07005c90107124081e81007111800a017000405180b50499035004507900348945a05c0a0155 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 732126888 1250 732125638 732125657
    0x15161406360c0301050103080901020f0303010501172215060e0420010c050a0c150e0d081b06040f030f080f011a09090a0b0a150819021e030103050d0816 67
    0x101d0003445282c0103480000c0c000c100c5503840346000072841d003001004e00d00510440d21342142101c8c0000031681030b40c2050712050301041c00b034901d031140744030001c121540707008050701d2402520340406400e4214900c00c003118030390030241c95201c100300c0c2c0c00d83d40201b1100c00302800307000100e1444551031101d01440d0300007940111800e40182d0b500762019200074444e00c510000c0c07074184246d2421500c1598200c2c04a03017041c85028608542c48180181c1c8550b1241180c0c1c0250000340300440144840701b50b03081c4516110001c0b0188a04281007100e0035102803103200c01c940205030384248100401007031746c10700072440d04041004900c440c00c140510002983c0c91000302001c900e08106a0b0094a00140f004134540f40540042001c0c00d01a01c04034040d03504000049a5080c14218095101980d1341c1d404841c3d40e100030000c00e4000760a80140f001980c208180b1110000231504808080030101060390b43e940f6600e4100c4c9009040508042001124018008022100454052403108501e00311040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 732128138 1250 732126888 732126991
    0xe03010507032d0603080301060f020d110312041506090203040c0b03040305031305120f0c01060501110a02040f1103091507080105150912070f090e0a0b0615161406 72
    0x4c020725080034269040101c00041d41a0b4480d080090f00c3c0d00b03640c02d0313803034403d02502c099502d00040007180f000c40d001070216101c0d031076848031110791143c017500111060b9178808080400322005c0b500a410340710f400000f00401c0c000700c1c000d030400402c02d10113401e1652420741c6008100d4080985041460010340d03501109108040002c0c46c107002c01000d94a690700c3c54040d480e441940003040c940415424440001290360260f01d0200e03a50744090007038140d90b40c242d400c0100074040808518200d940e11076005141250780006581700e0350281d002440004082c98000c0c2c07000c80c0090014041103070800050040f86c554400380303402c4120900d0096114415a0f0000d61910800e2100100324800c9140020301680540c800400321403140c0010040c8001d074030311032602c0d5200160041c14014000010031342c10708081640754410340d0703c000c11500300040420000041e1440941c16a4040e15552000312210802e010554009803120b01d80061060103030b15407078020324690041041011258582ca01c17 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 732129388 1250 732128138 732128141
    0x405210c040f0c030c02070e0c131703040e1803071707060c0f12020c03030f091207030806010905040e06010311030f013b0c060d18030e03010507032d 66
    0x2000d000040c000e100b210b2050280a005150008003800024240944100940e001290380d4003a1400c02140b1032040d80c4015190b145503005044006058502581c00589156400c09a0b0407944446020395680c2d07180c82e400307042501028204410a42c07111f199103002c510300200b15403400da0b2020441c80140c0100400f20700c40e00034101d01800003400c4c501b011607050b5000b50904240d0346541c840d0b1452003c5440008120301503140c900304d0070f9208001150700c85405d0002e196110403d40c0490302d001103244126182c0d42c1003290201c02041c40402403000e550380001155002d80025641081008a0840c44c65038500061001600508480120000c161401c0c0448a21480c8040c024002415103800c05100d802060310075140c48054150101001c0324031034000c2c0846409400102002e11500301007104ca6070007150707480d00e003075a101a012701000011105000a44c003e46800c600d9111010a140c29070300b0013002c19080510304074141d2051041502c040708051310358050780c0d070a421000b081c0e10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 732130638 1250 732129388 732129403
    0x50a14040908270406060c1a0402060f07060b040c0f021c0513060c060c02031608090a1a030403182108040504141f14010f02010b040f20040521 63
    0x4600034600c018043c2ea03d4515080000400c0650701040360560701d54041364618101070b002400031000c1030780592150b03240183d03290000d00007081186000c198690199443c0e0003071400710758954840b81040b0080c6081d102d034080c041d40750300b060300c4000740100d8000c2d102c15041a117180101580c00e0190a03040c40343e003e4810308517003032000ea110540c0303d4201415849454508558082c2031800306031040c0d2000c410b0f40c0e200e94080581c44170f40401980c0d0280c042d041418217036040500e00800048429812a050314203a0708019400c0d904d09150030014000c080b56146070081ca15000320402002d2201d03c034500d440300384101040105062031400c080c540c441e81d84880e0b4014185000c1c01c00132801408094091803c07901c01d01d820b403126000800b48003a041c071800e581480070504000742540140c60340c910301070440c0300000d1561a03040c0014201c400b0b000f1a0380040340d580741454091025900440070550b07058003c01e0a05280c0310005c0c045411107078501da48440d100c40342407071200b41000401e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 732131888 1250 732130638 732130657
    0x10121a0f0421020a06020c071809020d020d1a071d010305070819020906030702031315021f090f05160b0c0c040915050a0213090b100e0d020a0b0c07050a14040908 71
    0x2555104c00c0c984040b035441c1400e0042e1003400d118110509c0c03142c0640e1080540b0507501502c1211114015002c10ac1180145a0162507240300c14001c03032010a107004550b03110340c1041d1201d110144841d0100050700418030b0001c0c4c181840e040c280f10030140c0001c42c2ca03078000607840280c0d107401140ca4064001e402040d00c542c0c0c001101105101d50181c0100241c48004005000c01c1400783d1b40b10000c481c1d0074006040703d000b50b0003403544118007012080110800c0c01c800c070400714150405594011100021b400151016041548205901000e0a030f900c1300418528600a00341060690700070b44801048045a11070342d600c0702070204202c491480040300408084c0200498500021200081e40c131044c0c00c0c04198484400124850340d0740d00c81c0d003143c0d07003018240850807101c840042d0f4841300e41c003c610340e0102c2146000700069440c03201c0c0304068980d8041007a21921503529207860b03d0070542205200d141101014066002d07030500301440d01804442c08034042a072400c20208500c04d41409 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 732133138 1250 732131888 732131891
    0xc07030b06131103010e09030a05030105063106110706090e06010c1202010f0f0614010c020406170c1002070b0d050a110a05120a0c0e060310121a0f0421020a06 70
    0x14a66256590011354102c84103d01e41d000965506061251244200c00182c00450400d000602450030007202901404c0f604c1c0841482d030400d25016010320700104003046004010343c05040c0000d0754020303149004080c481006100b06420701c0e00c050542000d50203140c030b21300b486600049090b8840c0c1d03000c0c494560480c2c13611081002c040340c0240a42001d8501c43c81c01c038107201000e4007080084c41060b0807101d213081c408526090010045402100340c550613070380181c40303003008101e41c08990900c1c1c8044084500500d09a012081440501c403048c6190b030056402a150410028450318111071170b941141c9000140d564585400d000203000d1400207150708480841e00810383c030780190007001c80302e1060000a1190352140b0001042c1c0e801c500e031050001d442c0c00c948031040d04100c4099a0031112038048078000c640c0303032802a402c0000020301510751009145091110b40600302c43c55420901c50f4423000c0c001d240c41d440301703030410340c2c50301c80d581e03200b031482040096080c82803003100c1150351310110 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 732134388 1250 732133138 732133151
    0x602070602040e2208040510020a0b0c25050303010e04061b0c0203010509010b0310090c0e070c020a090e0a02060a031401030b1009020702031507090b28050c07030b0613 74
    0x203000c1440100c0d10152440c2c94a21032513021240781c9030655603940d0144115203000d0524051006038180200b15400750f2089451850004811a400601c541d03c910041c0342c07264070440b50300a080325106181942d1800941030000811800f00440b41507444901d40d12035961194a0618001e003070b00501c1c0c0701d240c0c40c0e01660351030160b401804c0b041d00a008030001c1c0709584801e0080c03800c032501c110320741d0307410751281100d40910355061b0400c0650600850703c205031f00d075070340c0441d90882c2e004031151000684141501021031414898210160940c41c00400500558500c015910517080001070700c503074404503030302c0d140350f00c2a00400e00814000700c041d00e080d6520310340320b1500380054a84802e02a41e60b100400e6890041c030030340e010030b13070003d0045c01e06a502d1044210709090140c0b10300100b00400c1000304407240301c3d00081800c0583e01200c0c40d064801b0803040d41d10f480d030b640410f000b0070400304209445004000350b00f4007501d80200400a880e00d552000400c102d10303a16218481c20b06024 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 732135638 1250 732134388 732134399
    0xf0408010f050609060906090a02070624060203030403020325051504020a060c0519080c12093f0106081e0f0a2003030412060207020139060207060204 66
    0x4000209040c1e046030140016200e45003004955031040701c6031a00038403e100003503440d03d0705007609500841603d86c0145028071a48600c5d050b03500300c480d0581440c01c91501100e0240480303103142c0007420144051425410240d9009417a07210b50180130403442288080d250600300d030000d810f90142d80c00021248081a2841c2c0d0560302c8800f16010392040304c16641c0052a00c0c000c507188d81003c0d43c810042c0418154100c5060b6910348060001d5506003c248102c03000328a08220703940b0006c41810a003900d40418200f0080004540f5644070020030907000704101d04003030304ed03092001c030f00e1720900140d07143c0d0300303000b181d00615107540840b90911900c5406c40318042c0880403000454081000c0d160340321052880c0c140e40b0754014000a00b8520301101e110b440c484248000086004020180d0b407800c0d640f10700d5034101d4030750113030156616940000c40c03600315a0010b030764426494074804017420840c00074114540e0019050951048413482c0a095000c0050544c100c40c3c40962082d011034941e620784 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 732136888 1250 732135638 732135641
    0x6030b130501081e0304050a060302070f021903290a020a180b0405090f010e0f091f020c010b010819020c0c060304122a032a03030b130e0307030c0201050f040801 71
    0x72080703010581344805898200c0010040f5015210054141d0b0f21191500e40c08800a40c8824000d50300c000584421030300680d10f4030b2000060811032070206910504500306000721240c0c00e10740d5007524000c07219485007840c03080c686960081e4042c4e40142c94405c29101034800781da8201d02251540300400d00071940301c03c3d40c00a40156001660280f0f402d507a4007580c00c000c01002e02480341480c85810004140c801c48140c400e80c4010420252200300f0034410b45102400d01280c42e5100362074002c80c0d01c03410200700748940804510240323048205c90030100a9490b003813581c12200603017940c000540e0008840100a540007049001e42030560b41e14043c10101d40d6580076105072030000c0d00c4600c41d0446942003101807070312110340a185081400145d60700f070b03c034541c250041901000c6102861610f038510101c400f000039010b9140032800c4131505041240d60b03547c3c0702c00c40c0319061506103809101c420000580c0c408591608051940d10014001a601401303861001e900d10035002801042001c4103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 732138138 1250 732136888 732136903
    0x12030403051b0303071205060f0402130305060106051902010c0e10031418010b0109030b2206051e010b040b1c09020a0312020d05030903070b0a0b040f05011403070b0406030b13050108 80
    0x3a42c6e8507020302070004c0d10001030311400d030f81080c2d1181c1104495003041c9401e03030040c16029481090902d945944c2d541e11400d100c002d0340301c074000c01c4000c58004011215440b070403c416480f44000c019130700c240c41d0060441261142c14034080c14245042e00c109500943c0090070080020340f0400e2240b4207402c0d80f0030f035406000042000b5509104250380594001d0710b40a0076258011001c411a5403440c804240c02420748400e0101c507070000700c0d2200428017a201701070080c0d1542d400c188850405d1300300a8010403060344120b130846002c00c410000c05440c0000e4030311262a034441c29000c0007032200740d00050004210302a600c04025030b00001004052a29014507082c1d980035102d41d000410300580d8907000c2143c440550380c0042210030b00007007050324483e51041c803a21001035550803d10100d004c40f2101280c00344d0540c1c4d920018012240f41c03440b1000c5041c0100c0051091605082440c8003070700462182105040d00d80103100700959948903206003421400c1e008202a42e900d81c40155074a81 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 732139388 1250 732138138 732138151
    0x12011109030d030b060d0b010203040b0f1305060c150406090b0921040302010c030c020102010f0227030a020102251a0a030c141c020d0e030306011403040512030403051b0303 76
    0x2a442e68004a180640251000b80800809441c02c1c00d15008100f0081c4c0800034009046020412001c00c003142d08c000580300c001c580d500e40903100c80d06411500c158441c1d6411040c458402030102030a5030000243d003040c5a8221081b43d101c036261454030790003410314081e0003403003030440a0400c07044200c001804104c4405554800d80384625180c0d0b8050680b08a02000c2d0004043c98052400702e4003510215030554410b20002900540b0482e201c0e049030800401c1840000d070918056000c1114240049140d083c1100503060788945680080e40c0e80745e07881128081c130740c503444c043d8800d00000d50f88800101040e40d90803042829150003401c0f44c1e40400010800309260035030b01036205200e02ca041d0b00400d2002e81c0303075280c5003008600240841201e04a40e6000f9000c124000c089903450041601d0303512444003c0d0f459060000001d8442041302c0f040340310800042c400c11000c1000010848000e9840390310003503407501e481c00e0840340740c42707200135046488060030360000903000c0000080d4030400 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 732140638 1250 732139388 732139393
    0xd05090102101e050711010c020c04060519052b1b080c0a0303120605030a0f050c0603090303040303050403050706050411030c040213140f0d030302031009020a05181201110903 77
    0x40c030015404a6036419a1140200030320060601c80c42100d0b4401c6400550751b007011500800301848050a403110125010010780000f42c24820300d00746070054034041c000407034024021482c41484c0b0008020b440c0b0400e441082038248841141511440d0029070b40c2418148403000710446c100303061a514664003004840030075107000503002401051000140740300801c0384854902d10740301150030842513001007a40c03039903818000030b00740d80c100402050b0600c27454040800d501c481c1441d90914103c01c124500a5004000708030840101004403540030f6414180021076450300e0a0444c2d0301d020b0108020002850b0030b00703020a0180341c90100c0007081049027140c0c990014031052009a0044d1181c00c0c0340141da203d030501a8079000c5400c400c0c42e100250868030810300c5400001c20008a03007009501082d80001800704200048024a003e410710160a502e030244440005105100b034a0340401e11301e941c140c403810a076891a50724445180044024031642414041412140c2d000d10078692207807 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 732141888 1250 732140638 732140653
    0xf180a2408010312120b0a0801060314030c030a0f0e150712020f0a11031c08150a0e040f150203070f030b09010807150302120109050603010b040e1b120d05090102 71
    0x2103114005080c1600e1344030f1194030011501d0700007a540300c0f000c0c3c52a0300c0126140c0503609099110550300c103000380b801c0070002c5101480d50910b02290711403124446040c0e041084404e061703040000c110355a8060780e02e000070402c40240d40440b030000e80190026485030b00c03221508265404c0034041c10340a40260300342441d44042e28026640d4450403103003d482034021a00754404214040c000300340103035020b01074403041482071840031700c00f070040c42807000841c1801c014014900e04102c44e80041c2041503c0c4800e41e941070082604031008020401402541f24070391920401940b002d041d00e844182c4c41c01036489041480000c2c00a50034540c003a0002850890104110300e4084001b604950300720000e4080319042a0301c0040031004180700e8011b140c2c08020000c1142c10001c451030003410550340004050034a20201404d40b1a070071724040c455414201440c00314000800d42129411b45c03a48811600962078000c90301302c100c194034030f04103400340c84400e13184250404000e0510b000b0903829210039 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 732143138 1250 732141888 732141959
    0x30a0e0d1715010909050f04120806090f0903070c0308190c081e0c0313051201020c15060d051002030709050303030c0301090f0b0d03090314120f180a 66
    0x203448944100c105119818003141001080c0041007450080c113241c0041c2c49915000036106590b02a0341000c1c0c02070500b0200000d015081c142400038411a02e00102d4a007881400103200c400003030140c900c00c0e1502c07404900507076010811214107580c8081001c50081c1d5a080020322904121100000d440701113105407208ea200e212500700135640400c00c40e04051001100b1418051030f26280c100c0301e00d041000b907030700d08020070103032150410340c40024440b5070500007400001100c05154031420780c0140b01d011028040400c1000c1000300c0314192905a54442c000075114144049015006002e9421342d0402661641c005511600041d00c4181c42d10383e441c010715030380348000c99400900709402d00040c007010a05400040300b02170040004598030506c0b0700015020203100000f1070220f52b00507010000c2084d000020030500d5501409080701100741d680750480351064020035007401700005420002d1403030081211040120250a4024550310744031100e1103100341100040180540034640f024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 732144388 1250 732143138 732143147
    0xa051e1006020c101205040201020a0c090c03060e07020c15040f030b09240c03070c0204020313020411130b090a0819050c0312090108250509011d0d03050f090402030a0e0d 75
    0x2c031050117645080001d000388140c1030041c00050b00403411030084e0b8101d840032944480040002d010060000904400c0c40e280c05011038504ad800401d561f0300b003d00b00620150007294101c5041011740b1410046c0b0080300c218540c600c10354121810300c0d05100004028000c200f200c603480f48a1550882c0c003800006602c5560205200340b00d0b0424003d0b402c0010b00a802400280d82c03c9445410440038209583d8005011703a041115101e0304186901000820342c6824055558003918568001c0c0c81c0c001da003140b00010108500401d164140700041d40300481d01c070700310080e00070402281520b40d021000c01408200468041065409109594850085e80340c007192400400d00110143c0b4030300894030700103540350b1900504800034008000540c1c284201c1c2c80d8101e10490344c269949a9a0f100c0408c00500303a0f400f40400c2040c0000380004c500100c1e2508240d4555580c0c00d0f0400d41d4a07000b000a01005503c5060300494100b8008000d11030710300c1d00f603007000d0701400890040d0f81ca4a50343c00303c03c95 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 732145638 1250 732144388 732144409
    0x3070e15072a2918031e1b060705031911070609180e060f07140405030d0c0c09090c0f0918020402130e04290f0a051e1006020c 56
    0x1000104080700f08002c800d09941000901da0a840f903284207142800c00e07100c0340e00140410751001000c14a0581c20340340c1171040140d0008480c0e1746119031884442202d075181c400100c00102039140200d0160b155440006030f07802035a2080459a84520101c0c000b0200307404c0d15055000314210040e094403403240803e24009803400340d6a0981500c1c900340545d07058030445105605050f03a5001e100031048800e0018034031072000ca01c1091800d00b4040c1000f03241100d40c5822081c000410300003030000b6074000c5807000f0000c1c40340c5841455075038242065900319007580c0c050709409140c814030000700011803200204551070340c1600320315140c2d00c110902c01e69048001d020040f80107104448014509a40503180c45000d9400550650b52a4001c40c241c43c0000d86082d1840c00f044041e0704024002c1010602100003404804040c50074510010b80b4100c00c054010980c4a803120001040559101d04201400790703903440682d0f481c20003054009814010b03000b40d0006001e107900340c05d07035801d0010654 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 732146888 1250 732145638 732145703
    0x20010e01050c0a0c020f0a0b030a050603070f0311061b0d0e100905010215090115080a02040f020408030f0f070b0103083105060318010204080f01060602070302090c03070e1507 77
    0x1d0107210260f40c01c20591910380b0302c0647e40a014648045442c020820243d40301c0c511300e0900207800c3c142041010303d0321754150700002c01101208410710015442d24031000744071009507003140d25483da410140c5000100180c50401c68801c060704003400c1da901074031a58042005440c100105c1c1e9a0250885d50714903540030303140c056400802e00300b0303000214010040d0306c07140006c00080d00050340904488101166400000a40d10a0749041c0039450144911560946c40c08800c61a241c504800709072280108625581e03110f102241003030381e400141003110445035025060850310b6841e40b400300302541250007014266404428542295200c0810108124410742d52003140c0b40d2401c0100001540000d10001c0c20103440180707100e0f01103003400604064004c8a001e403041405030340c0124211611a07108404540c41440c1c10000b42e10348104081d0004141c040031aa01d82d80c4442c1a90074118021003290030400280920708011015405001003034454210080c8894003013545c18054080704410 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 732148138 1250 732146888 732146897
    0x40903020d092907020d1b1a0c070b03041104020f04320d0809030105070207080607051905090d020310061a0304080f09150f0a030b190e0720010e01050c0a 68
    0x40c28082043c240260413440e100400c100e00c030075404e80d98a01e003040000c030b0600080d00c1031401071020190410880c41d0001d410941281032041040c03100b690b0b000c0c28851204030150010101b8280030501200c11154440a0015580c071001c5002d004840c0c3e0140c440e5a410f0242d4000306ea081c5140d48003030f845000c038070240f0700103181041400c00c26035455905c002ca0303010008001c8424103403400c0c042c1d18031441194000e0b00c0310601e400007450030304800174140c00401400300440e03a00c02e0107500c1407525007007903850f1082e1141d10302c40110711141c0c14100040d51500c24071440340c0304c4000300e0304100d0544640c1c1c3d9003400e142151150f02403503800181c6001b00540024448000100480000780140030801450503040c50f030481d180f180315502002c034110741c1c00f20000341003c0480d00340c024002071036000e4801c500805070340c048200300c6001074040e040e003c940c0c0c1740205001070720420581b04131050703a140c240040005d0f142d08500070046a1800c0c0c1d080d50800001520429404003a1014088161517 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 732149388 1250 732148138 732148199
    0x9090803060906030c130c180905090f15160504031a01030c0609120206030c09120d030c0f020a0f21110124031202011d060402030f030306030703060209040b040903020d09 75
    0x140f01500c491f0124034100f01000700030022061801d03490000070205078400103180c1c00d100a03d0303414140719407000040341e481100347e0b40f1003091f80e81405500c400740da090070417814421403080351144215030014110041540c10000643c00e401da40320304807882035807504142075407030305c0a45440c0800d104024440021192400150400c4170045078840142c20001d890411024001240c888031114040603a40c02504404282501440345100c0b14201c4e01f000d0b01900a01c1400070b40e120758400004040004078501007003007160b0496065041c0001d8144804207802460008115a031036800c10070003907091015415009409241003410050009100b009007821900c860155000c1100100c0c210341d45d039615000c00d0f02c44a1140b5a05080410142580b401c06004051a15800f1250f0f40c50a40040051149075a8000358100449600a034096210500c0c180007600030129401100d070482d04001d400302c01c2550102d20742d0100e01c00c0751141080c170354480c04035107024540070082401c850f52110 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 732150638 1250 732149388 732149419
    0x708070923030f070303050d05060a0b0a0e030a061b2a02060c211b0c09060f041116051005010b0703050903030702132f18030709090803060906030c 65
    0x10001e085000140c01c4650b05204a0384a0b80741440640c0b0a8001a602107498100702480f8015203030020300c122038048006050401804e818401c500900080c01000d0300f140c0c865403401d010042c0182c0d0481010040007800744070381d0614800e148405800154405501006a0203008032040030410078000d2596031500caa0a00006d41d110040c42070103880b0300000b0341d09501125182c0b00c01288a070440075103640050310800d40c3c00d0030980309121030303810001e5590000e0311a203110660104c800ca03145942110f032407002c100208280300420314041000a90b09c4580c4c10000d14140803035118108a60056003058541000c0794800e0161a080c0702d0102700460110b4461400b400d81540020305591400314076500051014011003480405076440c1d80784400081002104021640740610790144408002c500c0326045101d08040283c0d450051108045a52020420040a0104103104200306c0035242000380c041d1701b00f2521680314155032030003d04103042c08100c103038104801514100e102003024 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 732151888 1250 732150638 732150689
    0x406030b070809120a03020403021e091f051f020601080f10050a06081603030210060b090607062007060506010c05100b03031606050919020a03111906020607080709 72
    0xd00100e11921134040b01c00d0309407020400906541d11700d81c400603a503d29510612160b8505204034022001402d62003581d140c507071701e0f1200d0b4010040210b00800d1081ca41d8280c0403110f0542109400c150b150b981c59400080c80100d01c0e119901c80c4d021a0b5190782c1c1d44149a81e28a5030621540c1250401c00e011400c0b003071a81c2045800034049100415865107c0c5800c51404607142031084401a08100800905030140401009122031354000e03c099030070040c10701140c0c4900c180d0305000300d200051082c14001d207603100ccc5040c541d054070740b215a5803007003904100c41c0d04615401d035503603880c3c0004566035601825084054980c0900600f0100b04d503a4441c000400d8040002501400b00708035041c40665500108010107100e200c000805050000020349844800e0b02e030704240d010017403000d1b00580d0f40c1000c01c004481d80226404542813418010841d4610007a40100803808071800202d0020340103d40342e0300c01c070029901e80d44150354401c400c8030a04a503209080645211200c0c0c0d00760540350 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 732153138 1250 732151888 732151891
    0x303050703170405030a0f02060705040315020921010c0306060e01080403020c060a11061501021507090e0429190c140c1e0c300a030f0e0406030b0708 66
    0x2418a142c9056007004400c1000c10216803c41c0c4c80d400003d0b1041e00b00e5000452178072a040d20f44028680c51a0480c8003901e5482940800341c02d801081c03494001042d102d8044400d07183d00500903816010610041908006410b00003900b42c0d400c3c00f2048035520b110b48180c008640d800d543d0382868180e440f00560309010060000da04501071004042c0064031241c00400c044241ca560701d05003440484201800e02101904540e4070740c100860804c0945c1c1d00080102e40d034041502d440c070068075000f0047c1c50410707081d84441c040019a60070003040c400003410b01001b060250f442c800300c03c40c102c1402c00c425181152098983c9200d03d4032485860442e0b4441c516112490900000d00500300c00300d0388a980119507404e00682c401214003000304401c1c0d85280707006c640c503001086680d05c941c000602c0600300024801c041190402c0808013039003000200300146010348241c8103c41c9a078180100100030004140001c103030100d0410046092034440d03001160340014601c0311a444001c3d045614100 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 732154388 1250 732153138 732153143
    0xc1a10030f050c032a01141b03120403030209090a02031311040609050a0f0b03070e0703020d27030230030c09120c030c040c020309040f0f02120109050a0903020703030507 75
    0x3030f184684026202005010170104014144691164520f204420905000d60141d81003114004c244040c000e040c1d400d0303400c00d00b103006d10300b401e00d41c0d00200c07549075008000440400d40078110900c81815015401004080710079a0702c482c96640301809041a0311042e50000e10741c42d220410304001c1060a030080c080640004d1000c1030541d030301c801400175a42d05541c1b0f0240c2641c1c5210401c00c0890910594038041c000360041d11880f0300e001c11100c0d03180f20051841060580014042c01c080c10598444081c11a845110601503040e0200c2c000303071212005d800f100503124445214a0b01e0700101e180c80040200d440e0b00c40400d10041041d01c1443d0009090150b0f510028003454842c2c1d500c0d50481010b0b80c0c060310082034455020400c03d880c081406110038042d611304030b101245542d002c02150003440041d82c1c046140b1001102d440c008003d94440c864220380301250001002c01b1036500c0a048518041041c0f1550b2224200c0004a400300180100580e001c0c40341000024080c1c0050200a0b0 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 732155638 1250 732154388 732154393
    0x230402010e01020123011d090a0b070c020607030f0305100503070314070e16140702060d050712230c1810090509040807030807021614030a080a0c1a10030f05 69
    0x20300d10340701080f041150940320703500400c9060050010751386a042181700c2c5841c46185081741c8c10304000144e2100220301c40034142c0c4a0302ea001178452802106100d5003582d0203071a150750759115003402041c3c0c581300c419800010b4185400310b404c082070f415011040d220018058040c041c510b0303985403c40d100c5206618414080e801c40040e41c040d07050102032041416241d002e60030441c291000b4100d0100d5a0302e03184005091190070090380318941500c5128242c0e00000420b516420803e40d8403103250304580301410b041408070310045140d045202c1d150441340ca11465942c440400c0c50071301703018100150b031407181c20544440c11403500e01942010b0901e0b074245000038540381d002040c0341004c100c900713482c2454009486800c15912000141e0301c06001d1018090b6050701c8800d0b98008511481030100c00750021040411a541c01e10074840350300d40c012603003a0303103100208014007006c0c2080400d607600a1401000701e26000201c40262089070780744110180c0314110b42d074052070400091815592807 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 732156888 1250 732155638 732155651
    0x1b02032a0a03230c0a03081b0628090f050d0e06120c0a09090e060415090c05060c030d14010e0105101707030209030a0b011a0702011d1f0801030303230402010e010201 73
    0xd8a40c40017041c040c40c02000480d694080420180c0c1c000342c01711703082440302d502010070042c1c01c0f0000416040840303400c01146129038102d080c040050001c0a03c0902941600440c2804008000410780c0c3c1502d003985522281180310020010030740140000201c0a00500300060301c110465001400c0118550513340b51840d120302d40e00f400c0301c5072007c49504a51008040c00b050003c82e40e111079404040074000c1c400b070391460f0b4540d15810030a10485014410110342c1c1300320a50140300b620b00d0050801030401544031200e840c928490350a1140756126002c0400110342820444510712500300300e501d07158455108603011242c81c4100800080825a09002440c0d0680d82440003040a038080c10f66010b0550500c0c4000b4130048582d410142087c008000030310050741c120381c6807c0718100300c0714411070400d00540855800c40701c0e183d9410a40320491007502c41e050700450418140c9020780d404102c40940b21101400800e183e20060881c820403000050056100d01d400e400c0d520703018400814035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 732158138 1250 732156888 732156913
    0xb0a0f0e060705120c09131104090f05220b180312041103060603030a09140d0b01060503090d03060f0e0702010e100902010e0f101b02032a0a0323 64
    0x74840c05903400c1c0005600004c64465042c000e00200c0e41000d81100c1892400480307900041880a045003035425583e2511400c0009444007001d403002807044100500c00c1c0c41800e1703d41c078000c100c1210030758220b048210152042c2c4540803005d100071507010800080076101c0040003640c5036003440650025210801a035036107400c19800d61070280748a036141084c04008074040508022006125a000e41d000303100100b161540041200211140200c16803c0080d602010030714102002c03070090101411440002051680704004602c240800f0043d1004a4596602102a200c2d04d104d40140261414400d1085c030700c03003030f0300c103500031356a4000014500d100c240b2245c1007104001041c1d400b06d903146254000d40d6001090482c1c1ca070760407901040000800700000e2210302e103049251041040005180404803003442e194940e054000b0207c62001124040706544050021604010107075040315210700750034107400880540c0e5200c10b2054841100c440501c06544000c004180a03100f081e140046 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 732159388 1250 732158138 732158143
    0x80105060d0f2907031a100f030b030307140d03020906030703021602030d030c0f090e0f1807081f020a020606060d0204030219060f140712120c03050f0601020a0b0a0f0e 74
    0xf2102c04020445056207041d02d0b0290444d0380d0b114003a80404152203140345da6a41c3c184191018069038107124141c0715080307100701c005000d40030210360107200c00540c1c0d4007400b0782c02070200c411804220072a2090000716508070164011000101c1d0810002d00c013103042c0e0750003a0040c00041c80d543e4042281c501301a00020710b0255002c1c0408040383e0b0f500035150301c155004460100409450a001850500e1b214119401c0d400080641a807505520041503180000e000e1316600e40006504859030240c44c1c860702501d4003040c40908480600ca00d42d0122807003030500940e0f04599a44e00600703880e56500040c4603ea5224807021210190308100100043e40d4550f2080d00241d4034001c0e001301641041d03c0a0800380340c5070010400d00030941c0c0310500c90358001c0100c4298070b0b88000200100300b040003054406841d02c5040b05903481c2014994400d4942c5030f40100e11a0804180c020007a4507000c005a07101c038484000580f51050220000d601215507400c6018161991040082c00d8403c1815050 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 732160638 1250 732159388 732159443
    0x6120203130f0b060a140a05120a050a0302030a08070c0209162c2719060e070c0203010b091026070305030706051b0306010c0c0f150306080105060d0f 66
    0x49803540f0080501c645800c2942c5514007500e400d240c2540100c0106000451624051140343d1060490020784032141c0010700060021a03400304c2114600f403024500039450703402813108000016120700c001000a4030600300c42c690b054018141d0340468075040c070f068810805040401050100c1c0b443d0f120b80400125121081c00f0030366078030003000ca445090411046000c0c1e407440075516800070412000110750305061a81100d29402c01440341942e80c140323100904903961054003e844145c00300a819600301c030030400c06ca8400c8000b040007880a004010320200d05071169040104080d406005a003032044171906c803002c03c1c6241360302010320148041e103404950b4004841903040410400e04114136030080702e800080c0c6d00004424614101c480880728080188031504101c52150300303c09000b801501d29003c0d0000342048030201c2d84170792422045541ea4550480040e1400780e000501e00c0061080034001c00c1e000709102008103031625840a05804040181c1c1c440180e40b4140701900090f95858 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 732161888 1250 732160638 732160643
    0x70603090c17060c0a031803081807060815060f070f0c210201030b0f03070305070611030313030c020319060f111801030c090f08010501030507050a06120203130f 71
    0x41050102841c008400d414180e21120319030800c280704245800010032440d038002071516200d51500b48025046020f0021600c0c514046240030203031909159100c4880f900c074650001302e0080c0e110344c840105644110724030401c0700041614010409d504890b021440c0078450040060b801e002500d041c684039540308034400c40303c900c0315101000401c180360704032704003c0030070266a0f807091000a40d003055850b510000241011b0340c4410414041c0c0d1006409200510060102d440c503d8036071414030f546450501070400407030140070764401d9485001040364444c0341000e02e1005032804558060f10490350241d000c0784d0501031005102c441e0341c00c00302c00415060041001140440264040204443c11044003003420a0b00300700000d02c0420080923241668001c1c40c00248062070444120380102d42038008048101d4000c500040a0703205400550607079005009a0b00525030b90030030081c1c0c80c40c90744101d4001c116100064100c0140603030180d503000f42840744101607065242d9a1a813a041e45d0f5804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 732163138 1250 732161888 732161891
    0xd0e0c09010602150114210129010c0f0602070b0718050d0506150301020903030406020109200d030c030509060d15060e010c170918151c1401060503070603 68
    0xa0916614100c140d00e4010115800500550710300f103207492841807070500856416040c0e240486100343c4840c45d0792180010900c0c0610305807918000c0d018007902c21000555040609862810841c1e58445041d4016130f4058440d40607030070a9030349100c50342c885510709039901a424402100800d480041091084080d079454035900d1602c0e0800014603078290300b0560103a000ca82100002400009403681c0007210051500f80016444000a0181c440c1034603a40c2c01d03001c0810002a5507405400c02281d092144011a1017905508002d100c1074104000b400d41c8500200d00e0440440d0060000c4402c041c02450918a003028217004240d031703540250103401503a43c1c0d82d1000c134a000317409010000508000e1400e10904444000000c0000200301c5000d8111401518043c1c510031001d02251400c1002400c0c56500180a03110101448001c0f0740014004040420000070791600300c0d08100c1400030403500464100050b142d81c00c43c9030460221414666a640700072030955400c01500c002004103650 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 732164388 1250 732163138 732163153
    0x50c0d0203090f07080601030c0b09120f03130510020c0603040309080604081b0705030303150d060f02091503040503190314041b05150f25210c030f140d0e 68
    0x80c0749240001301d5014410310303000b40005000040480c0c40100c111240348070000d460b14001d0001500088082c000c0003118410203d02c10340c0e0134030120241007101401000610450b542c1d006103d0f100a40c4400f110041c2c1008030f6880040c54280080c41d0458000d18002240704d1b21200c2680c50801c090390146c60003540840c105a01000b03101c040789504034804042c1045a2910307021a680e400301074001d81003048031103400c3e40641c17545038400b071000e50042c105100c054450142e60000b5808682b07c10b01680c9140b07900c040d40d6513040b00326402258000011450050380307028003140504410b5460040503280c4cd40c005510031821801030156005250f01c8403046010700740c115840c49945c2c000340c058840c4154610000c002c000c01d07100c0510712451810354642e5200402d880304001d035a01c04180d04000344808080c000104a40601005d4074011f941c54231007480c0301910f900905030001000682064040c9018900c540c020450790b02c0051816420003034200e003d282641c525224060b07450380410b4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 732165638 1250 732164388 732164413
    0x803040b0603010219050901031e0b1c200d050109240b09040b100b0d090611070f020d020102070510020a0215040815090c040c02031c0209030c04050c0d020309 70
    0x1081e04004220001c5140003401c003280907180210032404d8051107030200b007a034400d03406a080803081032904110603041100449070100100024000180261640804030701c007581030410201c1d0184d00245480400ca80c800c41c075004050301181050b41011414140c42d00042c824003502088501c03494010488220401d280702138294103101550040741440032003510341d20b6500c0350035002a0410745a42096441a4039110029001d42c00140000f074005444000c016007030b07100d410340f9071084600380210602180015118001d643c0041c0001941a07405401854600c2c02d51070003501c1801074901d402da881000860440300f0300c048a0150700802101411450014101d0341d01c100c03602d040c64181030400581d280e44060303e503c070800c01c00c40040802c408080c100f09200c0c510302c00402c01d01a544031560000d46a803c001c102980c85034a000c1e4440480c050740c02980c59103032010f4010070441e1003607030070803018160203002c40360144010031017400e50741842e00041d84105c001000400da0081c455 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 732166888 1250 732165638 732165653
    0xf090e09160b0702120d0e090a0603020d0503071a0601050901031e050a0e1c080610020a0b070309150e0d03180b010803040608180d0807050c060a0f0b0f0303090105070f0f080304 78
    0x4110f88803035134106c02c1d201400ca1f1b4021503000c0501d02e068a03210210343e611100c51005010070381020703500c00c84580010080000000040807410f11072000c1780a68680c2c1c03a05901001e4054070040e010400600201d8000e5229500c52401980034402c020303002410a00c54000300c0740c040d200721005a8483c0c840100d801700c01c2201803110703011404009003804807813400400c1190b0140070544500109420901098420401c2c980d10542080c00702019041110b405002095111001c850420380c000940202140c0d520640807043e55800c081c107148122403004900030010200e5052040a41400b030401103090595000d0291076244003c5503103038280000504125001031080c5d80401d081c10030b100c1802400b0030f030b2140342d485605040049488081c41640c4902807500005c00d644a0130040107514130711900048024412140200071000380e40080c00302415213655419090381c1300700428803d9520840003014818016000c8c804c5034201661503044002140500355003050000c0300740310511514 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 732168138 1250 732166888 732166909
    0xb2e05010e0d0f02091009020f0a0909051009022b020d180f0f02061c0b0a15020303370c141809040227160f090e09160b0702 55
    0xb1160800340c0d4aaa50382c842980ea0000c100a0245105c0350200d003240000074002009481d4054055480c0d4110040300007032070b0000c0c401178000910030500041c0301c042e28481c490041c0407100030700603e1800c002503200a540a90f44d81c032203d5040115008090800029005040b0445000547c0e9171a04035000c000ba1001e10701c011580c03803040200c3c0000101c01c01c0796603507602c1d401204000c041c149800000d40c3c80c044c8200d103841c0c201d030036904086020500e501c91200b08400f180c5403a45203849035038140c10050300c040b906000d03902c100302090805041c6220180049940d001c543c200c1140130350303071030100303da00051051400d841d1000380c2a49034200070802900b04d00c140009007407140145088440007814414a8011540c0201240954035080e2844d0300c12541c0e40000785c400000c010b48610070f880212132164083c0811814075041c02d100e034400c02e4280d5511b0b07407407884030750511049404042c80079080c02140d01c91000344030404040340180100404100c08034603102d0b80140107204140741c5 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 732169388 1250 732168138 732168167
    0xf0e0a0602101a130b0f04140604050f070c06020c0705031207211202180913062003011511010908034008040305010905060915070c0b2e0501 62
    0xc2c2001c2c10156100c11031441c00100319004c01213402248400403894440711005541d40040c00e00904000303034101c00641c1401000c064504020540d1106a4681c0050303003a10f0040000704100b0351880411140d40152444583d82c0c000d41d841c00b07a40e00c0000385440c3c40074100090090000c2040c0d001d1003641c080304074218034040f03505510001c0c030b8007004040300c040f13050754414664085414003881e40d400003803180e000f034003400d240540c1c2010305690802d4040a40f044502d0b605081c60001640704100c10b0310350b02e0b6070a12800341580d01700000b1004900e1aa0402410020b55005441084509000e265130003401440e40690364186080c28045400742d0302044000c00c2040c2012003018a040384004525212500180720440980c0c0340c44079441c4a41d6001404c0781d0b0038081c0b10ba0520501142c0a4002d603441412030340e218840c41c40e08881d0b083e0848008022031340c0055200c0202c4d80c00e45a543e0b2040c17904001001002052041401c1c0d4000c1941c2032100405001d400d0019581012103800080d1 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 732170638 1250 732169388 732169421
    0x30b0c2a0105101413021b070609140301060e151c0803150303070302121806400302010c020f091608010503070819050102070b09010b090c0f0304030f0e0a060210 71
    0x1404c200104036034a5006403100c02590380040c04130032140c500280c0420059500054a820740c0d030300c0340020450105805045101c0c2408076407011f09282c14890b00d400c64152455501c00340ea01d8035211400c15088103541031b04048540180d03562100d615800c02c4950f8401c403440360b1603013010105500070100350b04c040e41c0603034000c00044002c00d800155001c040804411915966131404030000540030102419070f800003408115103460a040c0c04031070042c1c2c2010006100e40040401038034424074201010784031031401031702050000d5442492010080d60024000e07030450320040004c01e000d080d0480d2017003c4170701d805444080c80c551090080c0e005008c105e00411001d400d0820058848240d6408901980345c0710f00740c2000c001307003034040d40c6001d500b2100c40710080c6040c2680307a0180c1300c1c14810f14820040c400c0000c80400c00542958000815851010705560b150780e0700796600886150a1401d1022172000c0c0211507480300200805000640e000c1c140d580e0184d00e01009643e56242e91b5603079007 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 732171888 1250 732170638 732170669
    0x6070507080d360b060d0f1b17010c110d050d15081203010e071b060513061b110a0519060e19110109030b0c2a010510 52
    0x19584000703685480004600c0011141070200420800e104506008450365103200d030040e60b008006804000c80e28044c03115248030765034000811a000c800004000c200c00b200500c04800303c0d842e140c030500050b000a8039189516203940301407002c803e60040d0310000b41e45502c80100016841882094407054403002410508810354001d00140150340451030110358602141d943c101e032440c0c00c2c01c010302c05d06041d16002070312010007140684c0300b4001e00d0310140e2001c000c1060707148185418608001e900b0b01c0c2c03840b40000c40e50346a0241002034105500c103c00c000c0c1c5140810201c3c425400c060b505400c052501d0701c0c8070640a40080c042e1030a01480303400c0344200d54042100850040c085a8100d05807528548003850024003e00c941c0c180c503546403089018800400707680444655005003d40703504400611071000443c1d00740d0315400010040d080710404100d8002c4540b018010320b07426a00c2d441e1945540d5440d280c40c0f0000041d002001da91a101880000d62400c1c007642d0240c82540240c4412 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 732173138 1250 732171888 732171893
    0x3030e010c270b03091501061103040306050603010207060f0e0c0603090a0f021206070806090606070c0501110109050a08030a05100b0403020607022d0301050123150702091806070507 80
    0x102c400c0000001d0001640941c0c0d00c0c1c09248071010015010000455031642844600305070b9500ca07035a4800049084100081100c03400385203900c107400d20400042d8982801c55507040702400e8083d003240d80541d0240841c0d030000700107000d01d0000c40c005080c002861310850001d10b242208080d0b02034044e5204005000c07110380c2c0483c101603469000896821240003e00c04203061401944585049000e50801d2008a0303501000d8240a804202c8641c90703a0f41b50401000441d10403854001d100e25044030342003000d54000c119501c0c0001c41c00c40006040d0f0144c2d2910788c18642582000c550580000080001000036846170036044015241243d85860602c2c0041205108a020107032148201150f07032011940e0700c80c1c3c200001c205d01c4001c03090071094a002d041e401c502c02c511980c840d50900c4000708209e101d004144da00400700d0a0402e8400b061700c420301c101041940b142d850504400c02c0b0070405600e80c0318443c0d0040341e13030b80a07604640110781821030400802030302c0d820801c00c0030407983c0302 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 732174388 1250 732173138 732173147
    0xc0d0e0a05011205041a0405100c0f021c0504080a03020303090d0507050303043c02090a0e0a17071b0f060804120e0a030623060423091005011203030e010c 68
    0x108055160f1002615031580d0800904459400590400c040030700000c1104022002c00d6810003410b030580c040c06030000301070703003070301c28080c01c4a00b0001a4000581c200360682e100c0d0680c4483c0c0c034141031a0785403645500703034282400c0c0c2c100003c0d030241e8000801d2020146041104009038185d5203042e03814450b26035a802d031644800b82014020000300310f455200c10210354210710f5000074242e0341500c031045104070003a0300c10100b602a841007a40b800004c40b405070302e001d4007a010394180f01038001c0e2a250b0f40e8021a04605409507840c0010034480540000c1d00e1402d03485c4081d40a03440c2244c80361800c87d107070005848a811550401c6000d1061000280b60031280c204ea5210509201c10404801d4010230403034416a4005000c050070007440d4041142c030315014400041c04440003c150b9074400061100b62046518062500d02035108000458a00304c4841030f000340e400c2e02658a50310041c412081034501c20f0b086062840038400d490b900300354061056050b0841d40300024051110060300151 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 732175638 1250 732174388 732174407
    0x60c0307140a18030f061404020a050d1b0305011515021005070203070b0114010e0a0305120f04080d1206061806110304081e06010b250c0b0c0d0e0a0501 67
    0x6141d0030206040303484a000e551041c4064107a07500407100c080c0c3d41e003403109001d02844410390310320f8a0054040300039251200c1c014415600a4811035803a40b9000174400e110f6101442039650f4880c02c40f403d081020b001c1c03c0030700114001c0e000414000601504154164055480085500000f0300100740c450703004140002140e00420001440c2c0da40d0328410b9095201e280700040008040c0400070401030302d14194001940d500b0b81e50030b0580b41500c000c0c400006010301016082b544007048580003808648010b05c08250719502207400c243e40c0340c06d018038060088080c03402160449000d50701c0a1142d2050350010861413801c1102108104d05284242c1c58500841040098030382414146041c00c1044031300030301c1004111044402c030400581005108619420884d002d550000116080060203445800c6919080e4042c0c070580005861012110064204d81074000741c40001841c44001c0060450103503020050079004042000040294041a0310039100c1d8070032501c1070140c1e99010f445017 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 732176888 1250 732175638 732175667
    0x9062309060a0b1b0106050102160e04060605090a0e010f09020f10090803041202100e01090b07050727140108120318030301180608070302090a051b0a0504030302060c0307 75
    0x11400c1c0c0310540810001003581d040300c44400c0b40064100c0004080d5400724103403d4548008000c1162640700490b2245071620400d040720710301c1101401003140c6020700d650040d20074140002c2040c0c0c2c0310041540400b00712190040103941c3c0078039250511080c0504240028032000030060414554001402d54400308803580c060309950160302c01c11801002c008001d0305030380e0b003143d46559481c030306d48540340c0f2040c0049000d144006425400c0502540c01c18080c100141c40b440315403410a14000710b40e41215206445601c200d0500103107000d100d6110039424100040c2400c010101000740b2000d44003440001404103a840c80104109100401c5400440e00c0b00550190741c0d481e0700108141100c0d0158000145001c000b00000d10506206200904040c0e2000140943d60361141304a0312000580b01c0a0341001d004400585103114661006601a40f070501081c0c4920b8051a16030a0f60030001061000c6400003800b4014140c04109507640050411030152a52074003040040100d28540101d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 732178138 1250 732176888 732176899
    0x7080c160611160302100204030809090406091707033c030207060507050a080c160311010207050a0615080304080c042a021c0503041101080910050907090623 69
    0x60801c41c20703070841000680c1a030340300c6845030a01c84102e10380c0005808124058803a100316400102c50600070f6408032a0170a140c3d03402d0002d0720b07080c46080d0000500c21590503556003417280c0000d4480b0a8200c030203064100c40c6071039442618010b001002400d408003104003079190444c000380c000b02c1c0c54150880c204840c0d40c40b10040018250041e014040c4010070a504200800c903100c0d5001010313020742c450a030346020b000d45030444a8102d510031840316610104044c3c500700042802009103402c3c1c0546540014580421a21800e007801030721201114038646a0380740650340600643d00070041c0805501440c60140b9007444669140c2043d1302042c022901d490240500c001807511614840c143c19802c9401c1c1d80b0300b0f060007521081c8016070702c60340d40c05400c02d07605003611601c00d680c89540d120014003410101c90b0f00540f204880100700068034461402c85002c907100900855000345540c0d802400300e14205580082617416a40081b00446120324400b804070340340c050030b40c0381c2c490169003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 732179388 1250 732178138 732178177
    0x902090103090f05030c060f010305060c0307050c012a090602070e040c0f090207031b02010c02010809250f050306060a0306050a3905040f0311031e1507080c 69
    0x5038058080008041d241c0f0032159031034001c0c003801000170f1580350280c20582d60b130383d900c00341020f091801c280005003155100000098441075105c000b1600a80141801410030300344140c00f500313580e07200e128142c004800c2140c03900e03500b1403018190200c1100e4200084e80e1400c0800c02503980c04079205481d00320341994081410700440e0b04600c406010061140c50b442c030740b6404803074042e611582040307000840c12400e201004d200b07030308143d01a541c161741d090400c0506800456400c0e4015000078268060f126510314241807100e114107d81ca10b08100000040c90580d0226554400d40d20850103500300340704120041e03642428143c242ca501c84400202602c1e84825903000700081c01940d078800e5403018044d541c48245d0340c1c0d18003e254003110303817000040d00c010007210f0f0f0740200d02c40c02c5001c1440c41030900000f07003413031507403c44404007804803915211104101c40c24668101c002030b081c0e400a0030000b1203882483c40150344440c8606000c03d03581084c01d040e0b025485404140721503442c1032030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 732180638 1250 732179388 732179407
    0x9030e030f250b03040c0f050a0e04020f040e010617100c022109031501090b0d0b2205070b13060507080706020c031606020405040b090f040201140c0a0c1a12010902 72
    0x54424003034683c00e240c40d502d80c034292810000039041130294410f4065540e01c0051145071054080041e501075500600700394840354284010403000507445a4026140c107105130300020244640d0001780300104031035224140241410341400d1002c03034203410290078050840c00075500040e042e9140700800300c00003601550808850a18007a12120300d605000e1403e184145841202d0801d0507038882c48400c12201314a20104200c41019030300c01001400164005030240c80300e01c41119400e042000c1c00380c0a514140e841c01c1c20175425800092054030003044502d015202090036801414050400502c1d144694940651a00410400a2069400086011480405000703940c2d90983c0d42c26210a00da80c2485d003407000e5003040c02824080c034900180c03c03a1514203059180d0042d4541005046191200d800445494081809210301c2840070465078040e45010459083d03840d002e451191010343c200b28100703007641c0c1158003418150b04107000e0000e50000342e000780c0303044560030140180d80e641c015 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 732181888 1250 732180638 732180703
    0x41b0801111908060306040b060d02040f0203091c1e11030315120706120c05040b120103021806063a02071221090611030106020109030e030f 62
    0x1500208129420034a0312501500710300050301d680e450040c20030a69103510001140e220344225215903050713000801050110f61101c0d40107812560245c4070707110503a0306401150075507002c204000810b07a400800c010b1050410300134540d48800150541e808180c002000500911110302e4580042c001c00d0960b1514a010b00140707620401070909881d164946590b4100b61920501d00b1203000d80e200350801118090041040401d85501c2d0300d60520300e030495060880108507045140040c424100000702d00c000b007000241418151380300c1285141e60440c0b0610103441d80a03041e82c42100041d078144942562000182e60b110010361001c1a82c08a20891802c242400c4044103404ca50080c1041882d4040e00e8000308203c500031418400c400700c0d9001c04490f100f0700303000390b141c40b060070310400c1e0014805500400075076406001c021540310406010f42e800fa07403003a401900903030340d20300e003150405411401400c108202100078015140441640d15118041418002d40e9840400c100c1030410001c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 732183138 1250 732181888 732181943
    0x50706050a020313030b0405010f1b0c020d060923031c0c090509011502120c070b0f04240f110c010f170106081012020627090c03060f0901030b04 64
    0x1d503041c00c4035180c5d0307800c20f00c140303030419103003901e1550801c14941803082d45030040d1055100340404051306074003000c0040780c00200102080380d1040380088142c012801c140905038126009a8450038420681c00040700c06c00341e030510303252080d00300b840009042d22a07103d803104040c40c01c100c0824a2a034100e004c44203200c0d070740c1105e60300009600000c41c508602024a8150100d5074080302e81810074501c6212a6010b0751170300c11620b500400341402146a10700180400e070b88012645800c00d501c400c0c0c1040701c000020210302c0840180506d80821a038020311010100b1a076090000000854107491038442f152800003078103000300e070700384c1c0048a44580d030798200703100000c0b00200307480d40c54640040c2444010b851564010003003039404554000d21034001d51031076500a1200f03207400a40508050b00c1c4414001a070003004862601e20170580f0b601403003911440a80c0c1c00150f5900d000002c010f60080c0100300d450140999100620009002d1040150272580110200f020344284000c2a01ea0180 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 732184388 1250 732183138 732183157
    0x5010c051c020f010b0a0e1303050c010e030a0305060f0f040c020c0d080a0f020d0f030b0111030711041107170d11041d0a09110904080904020705061b0304050706050a0203 75
    0x107070400380c0e40c6007507021804280c000f4050009014061441003045105000d60044040308884280410252514005400181403090400900300401c2000d102d0171140082c50008050b0070005100000d030340c1c136206003544444111403142c0c00380074600c0030680300407aa0000e14004ca07919490303584094003c008030018074500510303021900c01c040c076218290787c1191050761b010441d01c012a1041c9070002c100d5001c40007040e074032400d508640c9c1c0341c00ca01400200f0641030600c806c80788080007140003030009103100390041c81c0c518803aa5400b818072045403800c840460200d1014860040050042085508031001140b1810703100c000035041940108100180c6180d0f03024002800680311907201c100902d01026110f504582d541c0311080c82081d940043c0000341481d40c0c08010b103280e4905007050b203030064042d00f501c50030501a14080350407603000003030503101030b8000010013450b8030800007000481650104511f05500f0584d41d4950340391010700824040c040301013159260b00e4802c100f664030000703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 732185638 1250 732184388 732184423
    0xd03050903090f0f10091a07030815010903020901171213060509030c04060305060403030b03030a080f1b0a020102040f0f08070e0a0f0501060e12060609061009083403030905010c05 79
    0xb141e55001d8289007840c8a40704103400003c070b55461071f10400b07040d10451909038407031010513640c0d00c40500c8402c4176540a00d050259149003c000340e25007080480c080c107040e500f940c89078031071903030014a407400301c3c0d503000a030030030800c0b2007105408000d200c20122405420714684071091200020306144026a2054010746000d10000c103024001a42d24000c070b0082d1010000c1c040b0440c18182c907071141c80464000b152502010981681043c0916540840c034240000101600e10200f407403030340d120100140040c2c1d00400c0c207000703034591030b5241c100030703ca00e100b1882e426281c20b52080c1c0792052403152840c1c201c84c2c2d00c009500499107401040b40c507180744000300700b50340c0c4951700030b1701744a480c070f15075806540c0ca9001e290010b1000914240558802030400660303581e043e0030030031502400907482c010040c1140001604410403c10443c10a25002c0c1780340b150044d4a00318a402c0c0b140516030044884071f41800c00100c1d402003424820b9507001e107840c030455006030410b64079009003061540400c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 732186888 1250 732185638 732185659
    0xf01091e140f1e0d1b02040f14060102120316050f07050a0f0309062c01050d090c0608060904121206120615090207020303030a2f0c0d03050903090f0f 66
    0x109004240401070f5403071030000d00742e10015189055030340c0c0e29150180c1d021451a43c090713070f48214a6132400c0c460620082021460001050b181020b81e0707140450b44081c0e5500d8400e000742507030148082e05040941e036101605528080510a03207058031906107a0501c48000707503141c8039031300804c11680982d40200450f0080301c00c2d0302e0a898031132042c9005038002295030a001c02c01c0351103001c0d581030094802c4800341ca43c421f44180f51a01c15141800c4905000c0c1c108680c085a02d0715024104100e0302aa0300d40351840d14000f00640083c00040c2003a1140b428001008001084009100d210508515120607081081196103005081d02d0700300f956401c1402c0081401c00195402c6194400c0c00f94014000c2147e0750340c2c0d1304090f03004611b40207615410a10002c0c000c81a00d034072240e00807495102e070b1081400d0b100000c0c030b0140030802010110b103100088100440c00c04105a0410000070720b01000f280c646142003030340764040c1c3d20440b4030801103504808100c0c1e07101d01c3c84908a5000804540c0388 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 732188138 1250 732186888 732186913
    0x3090915030312011a1606111e0d060e060604030b190227040614010309080906070311251509080715140901020703231c020f01091e14 59
    0x1c58400341700300c03010141015408000c0c2c852110a0360204555001c500c524030b034407961840044c01090303a00b8503116109022403c045210002c544919000c5040600d50760106542d0b84410b0b98000d4004070880950f9000f40901601c80004130360446c1e80082c85521f507500e50f181b4504030441c02002c03d6a41c1c60010850303049800810303541d00102050118a00a806003203030511056544a01c101c01e0141035004504203070b03501076044109080e200342e500f40c0c50402090000b48043d085224203400069800c43c002d51159400c0041e00c451160312a0031460400800300064404a05401040c6d8080d00401c94180c02900078011072000c0c152510503904115101d0304001610b803452080708000031040c540b00381600030f000d0101c842070741040c0d0107070516904588a200c0c2401b0540c101d00760512207a01440001c0400b0b0040c05006c0f55840040d030600940524000d10700b4507481080109645071003800e00005d4801c6100441001110700c12124074115400c0c5244100c9500000c6032540c0100844080c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 732189388 1250 732188138 732188167
    0x230f0105040c081504050d030b060d06090605090703050105150a0c0210030507020d08041101111005010b090a05030d12050601110a08071218061803061802030606030f030909150303 79
    0x5403902c4600701c8001104007406411003040c00d95001c1c0483d00150b4408587c80e01c241c00c6040c00d0140504014542030010b2518402c07604180c0c400038101f940d03000c040c00b051800d2900c1d5500702d4424501070050754107000004004182d911030180e06140d002030ba610410340224001d01341160001c1c810b520348819480040c0c0903200403242100180180d4003920001030141603514015a004400380c03d01595003001961000ca034040114810310030101e40107030302152801002d0180410800e6280c03903080003814024455083c5d04407901c41d4002000d00001c0b5030b07103e03020801c20000c940c000300d0142c980700c0040e94030440e2141d00041c240549031051007070292042c02810428400c01c95103000804a10045448115042010030310502400040015611898035024040003017500e910a4940d01e940d02d10486a0003001800400c2204030755409510b0140205035000100350054049461040c04194072407180700300b400d00c80d80c1064049003000307015242c882c03602d010240469030303215060324003000d = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 732190638 1250 732189388 732189413
    0x10f09091406100f0516170310060e010915030f02090d08070b0a050708010b070c0f06030b010306060207080309150706060e0a0e0a0812041703010f08070f03230f010504 74
    0x140550309aa0100081a2040204c2c2d40701d804142d1700d680c24402082c1c18001c0088020200396405448409040c4ea0380390300400031402400314091180c55030b03180010103404072215185841c180700e2125420004002c458800b10f81c0581c4601c2d0018408030904c8680300240154110103402007494800c000420007894000c000301380c05864044025034032201d50310140d45044403504c0000c0c0c820340040000c2454103024048a600c502a449903a507206d510140d400882e80d80088006929403040c56000d507014030403900075001c0c0744082c02600303080c83c003650741d00e115002405000b4200414401201c2c110342c415200b02c0d90b0301803c1070020655405140031070541c15524002018034065030340f00200c0300050054007007980001d116003415903910306005423140c01407080c0c54121440c00035480e44080c410080d80680100e40080301001c4c2040b400602c0c200315500001066041c411090021805000501c6461090060150032142c00b08180320300b000030509501141c1e40c20f00c4c0c14081080103421010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 732191888 1250 732190638 732190651
    0x180f070f090b0f100c0f0618031b120e03010f1103100b09010903060504020f04141b03010807050d020a030c030606050f0f13050603010e0f0105151e010f090914 70
    0x9110711000801000070064091a909a00c00c0d580d08103004d409008045413400b40f800f6111180d1403000c00d448440942e40491445c0880e04d408000000406070068460080c0315000021705203c1e04240d51040c140041e61000c000901030314088a0840c0e9400b50011884610f0002051041e0016651216803a40040e0340300414110001d0000c00c9501582c0191f909400d0141c1d200a40c591440d15a90000c050181c01a60003c54401c160050380d05c0e580940b03900c10411b40c7c4001590302e803c02240c1000d0450000030329103403804200412083e03800040400651700c04072840f1001240034400903440009503400100b40c680001d4000082c40880c1e409201141c1c1c00390340744100e2400d100e0070004c48503006507585c0ea0103000021100705200382035100a600050250002078207005225401d850845100c0107080ca603910760007003100c00c42111110b950000e40a4600540b082b950f0849507619007035208000e4100402c060b105080d0921500c0144010040c0d04010444a520030340140d20005084920 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 732193138 1250 732191888 732191891
    0x90605090c07080405060d1127030d0e1c0b0709050f0f0306180118050c030d030b0108040312060e09100e0303010f030809150a0807020c0a0e180f070f09 67
    0x1401000401d011140d4440d40031034180d203403038201020013440c0d8010840e6680100e6483c9403098400714080024020b8441411031960800a0000c6107001c140c1c038941c51602030b8201014030240c55411081d03011840100700d0b0031002c01d1421030300b03404e58200b1514000d017640f180b07901400440340e044910501034600640d0070022000c100005d000c1000c0e00c3c01225030f0568090400240820102c00c801e10058012900118030a10600359080010240b0031059601c0e030484a020b240b42e00e820400f244400c055410b06005003002000080c00260340140302800b030000e650307080104c901466103c0c10151611200200c800c0c10724440e400d0b600c07a0982c503452156440c1c00780349000c2403000000d40b4100c81c41c5c40e0141a200d400c51751484040e80140010641002074401030411250980000e00394070100341d640c450841c0b410b0381e0002d151407004d02e449801801c0d00741c004e00111141d9101c15034400003421001c0c280d4890146884c3c0b5104013040d110515002d5610045104510480c200b01290003d150 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 732194244 1106 732193138 732193141
    0x270f03042607141302040f122003060a0c021c0302030402130507120b010e13021809010b0915120c070218160305090a0c09060509 57
    0x1102649003006101459a0040e400381e00038508030340040c880360307141c01070500c40d019030f02c5400e9014142d000fa445030301c1c90282e0102c8000709171081c0083c180540c0c400d406013100c030003c0011120141c0c1c3c0700440d80c140e110b200f002c1c2511440100a00401e0311201e2428008108502c201402d5014403600c4000300803416111112600c45510003607a2451301c0c0c070400184503c0040b416041c1c5141c07406100c107050340400701074141c00080c0c10000c0c41c41084001600e4042c0b0650300c0c40c0c0d0203101c07500e05041f0034166030060041c10406601c021403280384081003003141c0300d0900030443c88910511521140e071603c5142c5000e060652518146000c0d00c1c5d03260101c0c0b255048443d43c401c1c031781c001080c00440c100008040c0140d40b00c01c2044403142404900700f02c60050341c1c0542c02c105902d0313501040f503249091002c021110350020040000a9503480c52001030b01c00c5c0e20906115a25000 = true := by decide +kernel

theorem cover : BRFrame.Cov 732014388 732194244 := by
  have h0 := BRFrame.cov_init 732014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 732014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 732014388 ≤ n) (h2 : n < 732194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
