-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4682
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:24:01.995508+00:00
-- url     : https://prove2.me/submissions/fb050fed-8928-4c7f-8081-719a1fd5661b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 841906474 ≤ n < 842086330 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 841907724 1250 841906474 841906519
    0x411030415090c060306050f03060405031b01020409090f1103061005011412070806090c1c09030c1209140619110708030f04031a090d030e030403242306 67
    0x703000304900b43c030303081c08294180c241d0010010f88400342c031407041031210381c01090b41e502c500b658041c0c910340081000c040840343c680180c03002c440020700098034082c2d580b003900c0115400c2c50f800f43d5840d0259220300d41000007048142d41c9100c002c40042c940340c1400d402d5581003404910030785050046907245000304130042d6090383c8221401c40c034598000d2600080280030b505044500310711920342c1000140c0520340750001e489030a20b030010160781d0b030140504050006d1105c16801e400388a424110320000400000c0082014070090765403021403440d2031344c446254500c00c0c0c0c00700c0c400c0c030040c00100383c84404004503581400b070a00e44483c0c0502e010001c182465000e400c0744850f1b0000203180c1d000078004000620460344910080c500362281c0034840c0080b09025191141550002e044042c0001e00c80d03000035251030300070810f40e03103419a00d030751340b00c007a000741c540c004602146211440d503d80e14910407158410f04a401c0100200c0c0c24090180c2c2c02d40000b0710310f62280c0704250b44030710700020814 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 841908974 1250 841907724 841907741
    0x109051906030b160f0f05030705120702160504140c0706020c03040b1c0b01020a060c0e04020a11010507020303010b0409110403020d080304020405010614180d02031c0e0411030415 79
    0x400030440503440e030400501c0c45100311000036078500000c1d074484c02e03903220354106000b40043c1c1d0340300d50b03031444503d03c00c81c0e80c1c1c1d001800003400c002040c01141240c1540c040a240200c0c0c0e19002400d460001c041401c0503880b06911041c0300fa89070101c41120208055030180e4401142c060342a80e580c1c95107014002401038802042407441b0106001c1039898104008000c440d40700b1000780700c0c06000344428003d44e8952220940140c01030001c280000e00150031a01581c841403c02c1312031781d1030070030119040387c0058500900042148110190220003841025045081440078500d10344c104106900d40b4400c1d4032900340420307610b082030081d588800090f18091980100820070100c2141041a01c640080e2800d0340300350314190000030010302802d2031400c03c0100b00141d6040007400003078010928038030040300f504451080304803001a6810700c90940c540d42a40702170f0040d42c27920b0100809038400751034690300031307880d18444130b40301c00e00300703058075445603021020103212100030010001611044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 841910224 1250 841908974 841909021
    0x90706111e060a110414041e1104062006270a0c150306050906041a03030a0305012102030c060f0706050108030405030f0307020a050d0f0f03030203100815010905 71
    0xd011004008800b1681e14061103801200f403111283c0c5488035602485188207171904295a40d034030200328103050700000c045d0740b201da00c5040d21244400c495010340e140c40313144c4651032170002400d100c00c90304040d170201e45941d4900a000346070220b840f0680e6030900503143c2c104495035207004038a451449401a28803144510555000301c0442c900360404056500503850b601503841803415060303200344201c00484900400400007507d8440921005115540000300d1010b01d1003504522510104001c1c01401d0b6680d400081c80d61425000718407804044442107654a40c9000440140c0c0e0000750418103450122501c580c0c640c4060b607448a90300c1010002081c19040ca8000100020044042d008940703040e41917030001820541c52a45034800d03140d000b94000c0a002c03041c469400c01c8403000c0300341c51044062600412960700c440d42d4901210b0400c6001030740010810200440c40c42c0c00380001d040190007820071404000b071500c501c10050059000480d512000200e8101031030309900911201c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 841911474 1250 841910224 841910263
    0x41b0305100b011d031023010e070816020a0231060602010f20070c080f031305120a060506130207110a0b12010605090d02060d0509060f09070611 64
    0x58540041c0504441801d5074049400858950361102d41c4010304078407410020040c241c02e039006507281c0300034041a0142d1043c40031005151807412a045441c0b4060558a15007001c50300e4a180b00505070a0028005100c012105190040c100c0c0c0000d02c04000b1681250b01c1c1a4045019a03c6660303446101e174841c0b40c0400403807680580614a510030001d403080c1d58024018003212200c244291200c0c008007200040b50f40c1c41c0a80d80104031000381010600c41c1d06120a0582d9030143c1303510301009129141c000780c1001403100500400007640c1001000b05032403440f88030130413018042d22044a0321001d4401d586030000100195566819808c0712450301d4800c43d1074039800d05141c0004c0c262141200c0c0500c1c500e180104418042e2000c0d500c00e41d8a880f0225100c2e0700380b2204958503000400ca041c0c005a10015210050361a80d01801815980d0386c000612458040689454954040e050701f5200301d000f420310000e0310001c608001640e80f18207040c0b00d80e91040615924103aa44185280c00654 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 841912724 1250 841911474 841911493
    0x30b1510080a050a050112080d110f030a0b0d080307050d06150909060b030402030c010f020c09010902090f1203041208070c1d07030c09030f020d050a0803070f02060f041b0305 77
    0x4001c0300c4140949403404080000341d6450300550f0440f0028010380c6c90303c4043d44c04000001c2e1490006101c0d402071810041840d902c03504a03070306140c0041c02000c218000100400181c150584030307404503414211620710b0b124007c0d032540c512612024005508100001803810700c1a5860b411a0000740541460503c0b18841c17100d004040e080980250300782c06041c144c0001d844445981924051034000f4003500442c404000191070020034051207030258020882c100c1e200381d0381c03441c00e107000304a00c0502690301c4c03002c482049a042881015a4403e207102940c40c11000c10001c20307034003650180702000c1255001400e020507036000756003005100c0e06d407502c3c000c80d9070706209074510303078822000b02340905c02d444014054050350085000b9100003001c801c02000407466414100d00058000380c901140443c5549480307086c04a0741c0004e40308400000203112086521082c1d90184008501c041c21031801d12480000340800003070009012003040b021000c0d138201a0f0f11803200215441421103c0c00403 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 841913974 1250 841912724 841912727
    0xf12090a12122f0a1b0809010e0303033106090501091b08060a02030a0f0213061b0206030c0d02090330030411101407030801050a080f07030b1510 64
    0x1241082c90b600b05801c09102c820300490842c2c01c220407001d5001941c98640d02803601d03141c55080501c0351001c1211450a40c00e400000005d10081c0e140944982a40c8140890015142d60007400104d40a5842002080481c0603858400c1a980181051340c4074166100035400e0400b0200380800341440b45060070700d40400c4815401800124400c54803001e800888141c40038007031a00b0f208101246e003002d0000340c3c0c0000280d0007564454104480000c100300c1070610b400032030f0030540607282d040b901c1c100180004c0d90446d040c14024400c005907151400000d0317000c150240409405c0200e120008516100c481c0000d405481040c0700c00b41c00c0750410b132030448203581d552a001c003800c01e0600802c080840e200046404481c07085810081045048081c507042c040501e1341204d55804002c1d071201412104603540700241280c90083d503401c80e40394102410480818025840403d4a5200c4e160500325840041b40030021a078011642800a42e110303414814110320744d080d0598040e101582c03000e0a036 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 841915224 1250 841913974 841913987
    0x1804090305190e100c02090403050a2d0909020f0703050c2b1706180415020414090604020a1b030908031303050c010216151806020601080f030f12090a12 67
    0x10f03441101c0084680604800a40b0080c0751914043c0d042000d03000064040b034010001849801e40d2403402e5030348201d440546d089494004088803c00001d03080c17912200c80c5d805650390b0040e0485100440c5013418800c0c60309124031031402c000b0f0600c5408242c603203125109000000e03d0101204000c07002108409905810004011005004c2451100300101881c801100c4a00c280b82c0a840f4010f45640300c0f0740303c1554000100704a6611904a416440c04001e90000c1c00007002d11b014581c110311100780800003c0701001b002030b40914414804143c1d1141d01c5040c10041c200d840700d0031880084075050480705031140d40c002d041d1610000500c442c0f09907a241088089074010390a0701d03c0b155480004a84881c14072101c140c3c1010b040300c0500c1107503d10b0b4003d030f001da0400d04022252030143c0681c1301c503800c00350b400600960803c0f001080a07200c14098a8210040a0041c52401104501c1c000850180703241d080035072450b0070001441c1040400c807a0b03120a4020b11810f00074503e2000c0200078 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 841916474 1250 841915224 841915247
    0x1101060905091501080c01090b090f0d080a0306080a02090f18160f090902030c09070507210207060804120f121422110f0307051c0c0b180409030519 65
    0x42c20f440c50000070384894086008419404141e40b9440920728142140b00560040210590b0101c10108202c1040d56482c07041d101941c0b00e400e16a031551426000034040301d03481c3d0b20400f4690440010800182d580c0c0c2c20655111400581170340c003603111015000844008000001800c1c03049103481c220821103402a07100b22480e9220400030241c0310400c242c152410307d140250076903c10100703540903242145d92141c2c00041854000d00b80007250315030840c0c108101c03c07141600d00c2d101e09050703011541404003101038299400c216802e070400d41d03180c4100c087c9640b421000c02ca01e203107800001c00d1190040c1e400c45080848240821a40a00f48143c41c0a0688424080946d104413420542059070503481048d50080c5d86594003e5101d814005118007010301558107001c1c549001c40d065850003808100a0b54400c07980810010901c0c1400d2001342d69000207000346420b02c035900c203010261064411614055a0108080804c0d160a55043c002d0700b0741c00003010030341101d01609580c0710035802c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 841917724 1250 841916474 841916503
    0x15030d0801080c06090d0209060310021308120a020a14032701030b01020115030206130f0e0a05091c0e150f070219050612090a060f05060915030706110106090509 71
    0x441c8003100c0c10040e42d8810b55401d070350010745c800d41c6d00317015240442c2c0690f40300d02c001c3d00303482c04014140c1003103080382d221680c0c8001c042403e000c14048503204010044210410040091030030550880282d40c8006540000300f030100d402803038488817041881503031004440380c152890744040b408004500002010700d41070000740742540e540455841401410240324400744201151030540e02400280d80c80103000e820003804c0701d03200284640940010000910f00b440d4a0080c03410200b00ca08262030b0094403010640d070040c200e00d6005000980c1c50b070800066030814259492210010980c807190101408900c0321000c542c00c500c03159400d0091090034400c40d0b413a0342c01c41c860000012413040900600303400c441d007807168038084d01e0480d2519410485c0341003100c0c0c03030f200103549900590b080d2402c80b00c4003c5d00c2d0814811981000d203042500524800c1c00d0030224400d44020030f580c1c4400d4804d200410640d8002062000c4c000c3d800078002d01030940b814040792401100255940c03400002c5142d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 841918974 1250 841917724 841917733
    0x311030703020d140c190c0503160309090911010c03121d1002030f010608040519030215010503010513031206092a1b1203111204110a05030c0915030d080108 69
    0x4e07070303035124150709441102407030320b810300b4044406507025510881031004018011171780d50140118004001800d10200311400d582c4880000d417a0041040c01a079201c001001e0410409200080c588101031910f19070038a442c3d0f00c070144a040440301d5101c2c040c10b20100d58a08a035001115000380d9005000703080080403100e03070341403078100281244011250740d0390a980080042c002d40d44156070503a041802007044402d012795425202c8519481080124090380c0050801c1803513080844004d401058110000c005a00c0c25051580302500d8000c401401c1001030762060b40c02181540c04276001d000c45c20703c01c01004644454a1b807640300c21105d00c80c4800302d004c1c42c01442520070055208602d40e54000f61201400d50365036040c04a003141c03046000d051300d5080e06500100d900010304160790880e081d0050070b0416083c030707000c904201803140f4001ca00030001401a514002007a1827121815980078880741d0714444007007000da11810b841a8103020b03181032401d620742d10041b4541a00d6103003041c0d5 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 841920224 1250 841918974 841918991
    0x3020d0c290d0b010507170306090c091e1c05010f0506040b01090308070f0b07031508030405010e0d111f0323130632010b070c150311030703020d 64
    0x55000350740144800928404116500311540103410a00f0800010b042c150308007001562013419014090120b0300c110345003c42049040e1408500d002e13007110b01c8403075061602c00752901107050080c81c21500c0904143e900c030106a0358403609101c104444a039404542d188280d880c0c001e0103080b030601218002810400031444902d810300c6034258100e8143c4440002910b96900d00c146500940c20640780c900c0801420340200d5481c0035020b108503070700c0d5400100d034500d103c0b0080c0820026000101664020b00050241c0e9030044100c400ca68801c0728805000c00d802e00d400840e00281c9080241c100c5032440b0b03000222008a54550300110042d00d050200d01d90b0124a1403126041c1c5c100c244d0000342c45008140c03c0f050454030040c4144c041d51010568040f00c1221040e83c9000c5207440e11400041124a191591544d81b5540500701400c46945003a2036031722420b28400580c014000025040c1c00c8607103025009074071211000216601e45901ea10305401c000d23000750404c5103449285810030588 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 841921474 1250 841920224 841920269
    0x190e01121b021b0d0f14010501121e0b010911070602040b0306090915040209040812040809040e070b0a110307120306030c0512060a1d030309030304050f06090705040c050403020d0c 79
    0x80c500c0b066009003c8444c0501d99441d17246400c510100140e81110004082c0d2030203500c20b001300342c068411201011505d0900303140040c2195181c10b41c0c3d4580c0c00020882400040c9035284550459514000200f0764858910034003105110b200303801041c00c3c0c800180011300030005005984550001c03281401d080c0c1d503c002180d1600c40f400b27690000d082c9401c2c00a070051502e81d0074950040c1c0030701c080c5414020384000c1c0c041400003e41d030076154440301088500c0c50b45013500580030380e0410600a081507520f8080900c51a00034020300c4020b1102d02c0741114030018040054821031600001d99403074803003003502c01400600c00350005940c29004948049041d0416500403442c0e0243c09004000760340d0b40324100002024074649411207200440701400940c407041024502860f1032101850362030501e454040e1411010230340b0300d24103810003c104070801001281580882d0400e6401280d000c60302c2c0f0040713860f440345400081d0300c451002050014071100d554984103541000c1c800c0100d4550003800c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 841922724 1250 841921474 841921513
    0x140c0306160e220c05040504020a02060a0c02030c0c10020a08030f04061409100b040b210114010e0f041719170c0d0e0309180406060506190e01121b02 66
    0x14800501c01c00150101c0c2000b2654044c0000c00440d240240c00e1544420024040c0e0b44480c03451b80050b8000800c2c05511070301803041003241c14036400103516004000841c2da84984080340c0c903501c0340408102c2c1611071342c000e0017102100c5510410b03190343d03440d28100e00302c010301d010380e4240e1b8074a181454400940000b201d01d940200c43c15401071000308003281101d80640260349000d50029244d80020f020340e20352600744119944000da4864880407542c078141d00712800703091a51031070103800d0010807100411241c003e030400d80e190b2015600d17a982c3e0a225400c643d035004c10034088100064004108021881e00344013120040d030310325450811025030107070080015030b540312440c030781046040d00c3e042155100001207414003043d00d04214020340040d40010004c0001c001604000d800c100420041d842550f01528040b141d080c2442d44000002820485002e409020b02183c0e13030320900c042e0301560401d41030762038805003441f8204450f540600c100b0b0710300c600040540f04003a1182d04520440d407 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 841923974 1250 841922724 841922749
    0xa30020a0305040e070915171b040b0d06030b180d02060702070506071b0b091309150c170901020d0b01020109110d03090f260a050a140c0306160e 64
    0x99420341040d0030010303400313120103001c0c107040b0500c00f03561b000003020006168200d42800098642e06a440700d0341421900d078202c000c0c010841030038807018900d0502c3c14001940d040c0da0503034030b0103902c80d4170394050320005101c290400f0b481229440100040f040c01c01002c0308140c00311605580c0c0c1a010381c401641d4074071054070130030096004044140f000c1e0501c00017403e096170051404203180304030510030741c0030041c040c1c2140401800026880b50035042c200170484041208500401c8074406949500900040356061390114076111130042c043d00b4030136a030f040850b9400010040745424035002c064000c1d446448020707141400c040d400d51540d8018464a00c00a03082524455003804000c10050004071400080b0f040c0b0504440c08141141c214010201410b42c0d000400100c0760301c1c800e022154217280111048642c030949050001401c04601543d01d46c0d4803008140e950b09450f50014100311191045130307054403481c400c0141c81213807041001810395040c1c9800c452400b104083c0603a400585 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 841925224 1250 841923974 841923977
    0x4091b0f020c15092403010906060f020703021c060f0f0e1908131203090504050f010b0d0905030904090303061401050a0c031209020a03050c09151509030a30020a03 72
    0xf0711801021404a0000308407840e8000c107000d4a40c6040b40700c042c01040707445552244410080010f1203500e04d203100380700141c0341e0f038188000303052090b00300203646005a0100901130141d0041040f40c9440a8801a010b15841042400740d050040d402600400c0410b1070301540324100003030400d007201c0c08510000043c00314a01d100440b001c03501d403d600ca600c50091110702c403110f01d03800240413007110341da550018440e90303905001503e001c080101f503440282c90282240c42040040107407500001c22a1904000f440011403445081d00303003641540100c41c40e079501702e4101100344081503813651142c000d594868141c50f400940354001144c180c0594a2b8141c0419194101c40303011038020402c0141e021040720700800d00b60f006901080e81094907510891740e541c410a8898994504180f131958440b0f10300d070701c4070b8074190440c00240320031042406010a070100007a204001e605e080c4816114942c0100100180c0760031a82e650900744071402012010407403c4100400f56403001ca504400c442d090f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 841926474 1250 841925224 841925239
    0xf060f0f030402030a2a08010c050a0e0f1c06230f09010e030a0507120c11010e0402220f41030f07060e060f0f0a0504091b0f020c 57
    0x500d034824041d030026005030703030500c1600011800505c5003507100c49070720403014109800079000100b40c20148265002299546d0601205107410750f44481582d00f48407503840d101d92034004100c0820311000c03110f109150404034011400354900300091f15000c107148a00740400ca5468425540f08503491807014900021070520041180111101c0700140c000340200000a224140c81649a24583c414580800441c1005c02c272101444550303c14a4a04409810844e9140307006540700986490055006030500c410401c0821090301c8680c1560700d400000062030031001c00545501c5c0201c119842691400030740d440d03011403061441c2c91642c5000b00f40c88442030b4400c1403040b021800086d0300c030390781040a07007a034940d511b40d99042022100c3d00c101c45010700229420b08800078003030349080d010980240e900300015510003c65030106c0e112040c0d80b0705865102c1d00b03402d030200c5061041ea444003d5044c10440e2040c48107041032400d01c1ca92200f40c450f4400000e004070142d072280300503039803280e01414 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 841927724 1250 841926474 841926487
    0x309090a2004080a0312090f2303030a0209030705180f15030102030a0615020a02030a0b1f030303020909070e06030406050402010509120a3f03060f12020f060f 70
    0x1160007044481e0390701e5070020307039210000800c2607a0303070090390103002c072a400012a1028140c100c070120440004020f000d110070302250700d40c6556400c200800500b00d010b44292089004003000d61140907850724002c0d070f5501c0c109a25042d01941100200d40c0c880d011703002000580c0c0c901007000818021100024000965895080d000c044400400c0e5401400003040740c0f042594007071008520031030f0400b50008099080080718000740c41c80031960003d40d4459002d000c01350b940080d0002d821030380f20301c1000f036944e6006500300782042c1c8603141c202252440070703000c403c054140d0094030400c14299496586699a10b01c11644094148030040d004481040420041111a005140d01034010b06056141540700c1012420303140030800b01c5007141d085206410200140750340c0c115000d410b081034248c0240104404402c11440040e41140306410000c8114040f0b4000e801480041c0f0707254103812040c0303076a00e540000140d1150310891050213084580700c0546052400d4407007011031850628100708 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 841928974 1250 841927724 841927741
    0x30b011d04060312050304060b01093503071202060606180409050c1c03030b090402011e1209080306031603080d09020d0c0902070312021207080606120a15050102030909 74
    0x240380c812541c00a0301c441001c03010a5001c66400c640c20701542d182644c0340382c117080907002c8400d94081c0c2070400c42c15140401c0404285200c21034640011210b058880d03034420000c1414405000e4201302c0c1d4040031030301a0074070920b00185c4101921030b070203881c0380d40d44900401c040c9200314000904241084444120681403552000c0324071441038044400d00e4445800180300c854212980175010114245a841096498000da03c02444103461103511420b05034000f801e4598019921840925403400c6000740714400c207404441c040000c20108032000c09810644aa03600031a4244d00a02c2040142600038440aa01100700d03500011224180981c4080c064060100001c05076440b6522a64000115400c0f501d204001c15201400607507403940c1c0d29014120034401070500c5403461050104204000803c0406903025100b0300e00401c09643d8440000d0645c0071b00c1008203a007000210400000c00001e622094010b40c0c40d900303200055a0366401243c0c0c03071281c1a0900d810500c588040741030070 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 841930224 1250 841928974 841929017
    0x612070803120702010e07030c080c030105040b1b0409020f071205030615090d0501060803130608150108042a1e18020c071212090e060d14010209030a05100c030b01 72
    0x5030913440003044849550720300619140e0320750000c0c0c1c0c41900c1c2990410200c00e0400441c01006e030140c0090101d0310306030301c03400450341d8020422540c44412800340c1100320200d0007240c0c050517a48908544070461220030385200d170048682261218030a00201d00183d01400075203114980c0113010196066210745c120046810455a440c2c11044030030017500001c030280a0400603010303401c0159160820b040041035030201030303400381050150f02402d00c030700c02c40031444000429a080c20034070080d45031490007400c0c44040441c04406910680c0a40c469194115003c408480e200e20103031815a80c80c45020000d62032511914100c01002041c3c10030050294003d00070303510b4220241d804081e624200c01000350100031080354040012807002680300e402403448000380c4034080d0449458640b21000c648071100300c0f8405000d9440e0202c140c1d074481e4094044410794032000d415034801c4015860002d03922031072030785111300440c1060803c100c241e03c2403040d02c40d04d1605940701c960300c0580f200c01d040301 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 841931474 1250 841930224 841930231
    0xa0b0715150b0c010b0a06050403060c1202030c0a0905150d050405030702190e01060e0a030305070f14010b033d1b0804060e010606080105060d06080106030605061207080312 76
    0x40d41c1c68428001c070500400040d100104540c405095642c81c0d4000041d084a05c0e01585900c00c0001c100d041c03000a40c40000c1e40e0640f40d00240000d000791489800303649080302404120000c900000070402400e403030801920a00b103050701d4140d51503403030300c0070481d0002000c07995159104003170040d08075202c065080396400c42c0c0158140c1b8a004415000301e10740d050642c1c5040d828a001030030070000092503e10103401408249000140d0f04e246400051401c25984070240c00c220300440c07010705000068000f02c400c50303031005903074064800166105010b014081e0b800b81c4240200c02001c0100407100290144550000c1b81480144c0040354130160041e5804e00860581c95443c600540d040154003203034240c0c60f5454035045172518103860301070700b0740316080300541e440d9040c101d0030411a074108003442e065076401c548103611012074101c0d01004148952240e030203907080c00310020502c40d496000714020941551304841c03051803104103503130700c8116218040d2154000c0000e17040c642e8159048030381 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 841932724 1250 841931474 841931513
    0x1e0c09010c0b04110a0e07120e034b1e0c011503210e0906061c0209011806120504080405040e0c010221190c050d0302030103110a0b07 59
    0x30381007642e21003400101c0e0440c1e003101c3d00041c150282101d85803840300180140000c10a1a0b01440c084c1130043c501c070f400300314081d24146c84ea084204500c109209880c21a03055191410690035041c100c1100ca00c540007040c40b48000c28896080950000c3e00318019503103102012a180902d0650f4421aa00580101008806050040760000d540c207004210800640808480006040d41003a503282001000c1c14403203d40c4034482202d00680100020ba12071000725140900c5554560200360184501003031103003a0324542da0300a5090f4101d501801c0c2401084e038811290115001602c03882c0c51580c0030b120040380558a66106202c0c440e040705600520079024141056500c0000c41c0a40e00c4940740c201940d003044c0c00d10000b5503810400129103910310b0f0402492101c0b1950b8181103440780d02036640a00f003148040a800c94050302540c41d04a40c000c0031961504c0144400070000e400030700003103528007503801000340700b4a00400400c0544000650043c9011115030b149035044203550360146 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 841933974 1250 841932724 841932737
    0xf15010e0d0b06011701030c15170f0411030106061d01030e1903030609050406050402090a0203011202010c020d1407210309291b061003050d0c05070f0306020a0201051e0c0901 77
    0x14117800d1501014029031142e18442810780c1004120720034a00c46800000070816006115582042503804a5402c82400165040c20703803180d003030002148940302c22098056003459800508694007150000c954084080c0c154155882c1c9401101524024040790810740e0080f0005800c40500c0d8400c0c603801072190030300051250b40c07501404c05483c400c949c2a2401580c0c1c1e4200015400c09186550307000c0d0070074101f1861503041251402c0074425100c406410813031040204030454540c040c1d030034010340d0026444211030100c0e81d1881d80e070b42c0450159442051800c81020061000180c0100803180c3c1611012640e13418035441501d91514600f140303907c41018071400640c4501c04005001440c04104220040ca0301200b18625050001d0008102c50720f1007403003040031840101e038100103a00c0918102c603241ea07490400c54a40002a000b0340312480ca601c1c400410410944e0051103080215002403201c0d590b08141699051200c54880b06842d10000c00100300c280c0d4000109070601c4141001c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 841935224 1250 841933974 841933997
    0x4180b100b1e13030605010303030b01030b031e163506010918172104080307030209061b100c03020c1c02030f042904080a11040b090f15010e0d0b0601 66
    0x1e0440f030701c40341e005030741039542d800043c4185079242c06601141c030000e080a00c049509031022954420070704005002020b07810315241080d032018003045214074405a459810151200308070b004100920f03400c0850140d80440c05101d1000708070803c0303454400309014226a0b8a0a0428000340c140250a0000c400604401c0000a401e010400c43c030461420382640d04d41b130111000b0f00c4140800c03850b119500f5030001c2080000b451b40011a0f41c070082c1407801503240d0b50f50b1000f01c1c64501607401030003145114604d014800e8000068000010501c000e4140001414000c0075012881041481421030704021000790001c09034440c1038010703030340320b104482c540307400c54185000d16081604800d40d150038008003404524510b07030000e03601101c1c100509203024030f00b0440b039030390311440d013402040548000d521510a03a242e520107041502c001c1d011206902e402d12a402d00c2c0300c012682001260b99900c800459544039080c1c00c0f03001500940400c5002c0269103030a0400e040050456040160b0710b85c14 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 841936474 1250 841935224 841935247
    0x61505060c01140601020f03040b090103060503031c0f02031510021002130510030b0a090506041508060403080f01050d0201080a0f020705030c0f0c0616050c04180b100b1e 75
    0x14003150800000020b15069440b401420f004400f50416045510110042c0c1c80c00c40088116800c031108030540c2c3d540c4206480c016801381c40643e00080c0d1501011a00d850040c4280002d13a5409240500800c1132404084540049010607128120307100900d003102c0626080004082004018900444100c5404003002005a034441c54142d1801e14108804100038100114542200b86031414144108000d02011039070b080568807a4802c019145c0011618540b2168090b070940fa1581c03030510001d036210010305503039000a48003140050903a100040401e01d055030011305803407000308405260b14040d001101c07007540291070312800640d02d942203018034801c0e00c000c00380e00d88110091512030783c3e0f00001e0360902e020604600d5403500890101e00c40c0c0e80d11002280e10b8210700002d5082e8400460038818640300110f40b0282c0c01a19105041c010000c080024000c1d8501c04e107095101551851503641c01341c541c500c101180c01c0414080101089200e0240004000c281100c00e070500862000c0c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 841937724 1250 841936474 841936477
    0x804180902120a030e060c031603030e01050c0322030509101b03080106020d03061a250b010515070209151f0f201c05090423060d05060406150506 64
    0x1040100c560100f010a81055042454003550b03c0c411181c0038244020440001e48900c200c080922541e1f1000e8081010580203510802070412024000c001c80d191003500d20313455500980e0031981d104035003a0161030003c810001e03090f045501d9900d8500b81496003090005030f40100c4045814004000c51103400705010090342c98105020341d031001c0c0c040d494008068144103518854000705820244c051080203824070038015002d070ba126005503aa082c85141d64126241600480700c1020a0401c03001440210212903058820840e00c580c1d44409503101c114880c800d0440080d0010345040c0010080c2494001c01801c10718082c117141d000e00011403005400c4c400c0026014082920080707810411948200b84070f6142d614826010b01c05003104100941e921345a22401c490340c6141042940ba0074401c10030741c0d01c2c5050203882404445268032858103001207401061f5907004240c070000300e1900d09522075108003a0484081c1840d0740b15a250440074000c108860b074040c1540c2d600000701601c8480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 841938974 1250 841937724 841937749
    0x100f030b060d0203071407110f1f08241e030102040b160507090e03091009080106091a0904021509420901050a2703031e05070804180902 60
    0x30301c016600d00d4200e0002e4880c6d540c0801d800700c00802030003480001001c14030311290140c0c0c100e50b203110401341c2e0000150790204004814409076039039010200c80d1a001480d440c00f403280000707082c0007403510000c41070040071000c0c0071660100e0441c00d0800c0e03000100103200c1c1c0000e000750001d843d198440200421907070001d90ba02847c0c0c2c52400003102440014050307840903220107641840194403c8840c00d50b030f80107600f410b40c4108907682150000d039018150b108000d028410081c01070b20346c0c50b240b4000901c1ca090743d184074415017030300101880c80d2200d90544142d074010310100410b10040056851600010405904908868940c40106c0c0ca0b6620b0313070002600701c2891784040d01c05000c5844045100c1e60701081c2145050180d12500d0781c0180640703500c04800d02c0c00490800c100442d124103000034078035003034040d480d00c3c601009041e40180c40c408100c2e0740e60a41110081c0d0088111924403c40c0c1300502402e400744070500000c2c062030089131404060040c04580c038909a00061855400d50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 841940224 1250 841938974 841938997
    0xf120206010f080307020f0402161b170706020d05130806131103150a0b0d120302041a030402130b1815011b05071202031c050417010b100f030b06 64
    0x10004004101411000b040506041e0f0061414039003036034046030303c9036a00c40c0103030300c07071234002c640c3c5600640c104c050b01c0e40807500140140c0c0030706503500c4006490031250042e0580d00c0c08420009200c08070000d0f08004580703003540100b1661b041d83c9011150364001d03810156520b03200b1200001d2150003009200d001e100701000d284441e80c09480c10005010800c42114066000140c11800c1c41e001308500c40c0c1d001c8606030b030124031041d00c0c030005014041800c10042100b10820349041d41d0076407580c090700548508400313204d00510000300345117480c0070860300258000300c1c4098040c0002c849811000c2c210303074041c02e01060b81d0758554503c100030104684800c0c03040c1290140210a40e0701c41030080b610441404034042e0140b07652140ca848000c54001c0016000b0300c4100d040441d03c0c10449504002406420310342e582c12081e10091403607000380701321402c04da2003030760700328540e60180300c0c080492400900c00703103240c687e56801f910007100c003018200c00e060740e0311103989590310342100801c4a00c040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 841941474 1250 841940224 841940233
    0x30402011205151c050606060309240402040501060c0f0f150914010b040207170a0207052718210f07060f0510030b0c18040212040308010911040504090f1202 69
    0x5100380701c0c44131600c126a402c030014041d00d076404698013140d95500000d06840c840d41d00d545c3d41c00300354a400c2d10b0304001c3da00d5154506a44401c03e00740d00000307009078400c0718280210391b030b04c16048901003181c504c0581600740c14034001300040d14100107000028072a01c01484e80c443d210030040c0c11a54203560a4503824a41c0c012010003000c04c0c421941c500c041160210304140c40354070345425550b202011402c0c1c0060009015021a0080103600c00403c4024106044103150200c01330b1046000c65010001d00820b81c08255204070440c824584106513a0042500c008440e10f42201c11500c040341c0b000c258800c000b20400c3c0f40d005030040454900400000c121183c80b400c0007003c41d00024000b4104281104080c40056080c40155811010800c0c40e00d882e641445144c400c05400701424550043c80000d00514490820180307074411402030311011f1441c0e80c1c41244605680c044e54064032046401c0206000e6841d1079844000054003076044032003020b00503a2995880c020004010300507038003 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 841942724 1250 841941474 841941511
    0xf1b020609060c07021306033203040e0609060f10231305010503090709020414010305150112111902030c160803030c0702010c05060106031e1808030402011205 70
    0x101008960780020484006110714900142c0c0d24200340142c01009110389914642ea100c8090719411003009583c210030020321040e9002071801d1403980700d00d080b9038011b001c1d07400c00c07000c20400b10941c1d040303d920006505065580c00c040000d062001032915600c000040c90051454842c0b1142845000051f2608002504c0500c1c000040542004140920ac101041141441c1030307200d601c034048900c02e0a0a40d280d4955080303039400e061642d0085041c983c801305001404030050540760f0140d910a0700e00300226214001400c0580d028511460f001c105051246101140280d02c40516100a6403c80e400c00d000800c1c1540145200e0036075800580c00070408405c0441c0500a54a03032016241b0010040703450045801e407a070000400c20804403c0200c0d180b410740e406504846481c0b03038400c054812540c0c5407040900103106030b9800288000013692140c09030303c445d2081c10b5a403150000300b070794605880e6590558607800200128100300030320340402c01d44121030040313900a05400090465000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 841943974 1250 841942724 841942727
    0x2131503060503010e100915092f090115050705120c070609080615060f1606060b09090a0f0e03040e04120c030e10140708071a040b0a0f0f1b 62
    0x25103603044644642d00d401c0040d2140312002802e160096640e46d4041030b950f0f582e0800d181301441c1d0700c054040c01c0d8102200c03142004510544843c1091b90000d02c0340030210b21500c05d520030180402c001c0d402c244114010300001031802038075540038040d8580305180130000e40d2f800741402110b040240e0070080103e0704010115061080300040c14152402c210302e0380c03505604958821014024100111a24801e0303503107030300c0301c2d402c4a83c058004d940c81075884c4d000b40200807a1282d80142074820b80d18124020583c001c0e00d004980803c84018046099512422030007002400d070841200481030b61108031000400050014200410318010401d00914082c2055000d480c0e00f01c0c600b104001f030152503100041e8210504600c3d00c40c00355580d001c0101c000c50282e0314080540d20310010704401064150030044600c0c002c044c1c2900c11141075488c60503032800250a0030042d107005101c11301041c0058030b150b8160380b082c01d00e101004004076510010407031042c1290103021208000400c00110318201c03a = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 841945224 1250 841943974 841943981
    0x2811070b15090618250216060216060810030f15051b121009050a060f0f030b0606070309090203070503010302041b0e1c05010204081e0609030301060c050102131503 72
    0x1030400c0c2c0d401d9001c1d140c4000019406044d400c1942101550040443d01803600344504407500c11109030542040480990b01943e901c0c200060450000c05049010a280307201141d801d0540d080703c2485030380941004070650fa07491000f00b8284030b1114284002000c030300c02da03094446c1c00e4090824000344200301c2c400f090942d0350080400385112500c0300c140301c0e0301303540303004a4010b407100030704080b00ca8a81c4200340905140a51010080d1414442805844a490b50014040b5160b07180500e01c0680c3e901000c0c8590320183c4000ba000c0c621550004087d401c0c03000003829030610a10741050015108c10b6240102d030010344070180041c20100041c01181010300c5141d0407084451001c1e030203090194002044010751481d103034041c1b040c1c810790f450f1000200140400082c0d1090003036403544d0300e450100303580c3d4003039007844c01d005003181c21161441d4001103841805480d41102171865607003403c0d0140c8e4880d0702c0541c200c2c1c46660801c242c0c25070380000640c0c2c01c050700e580ca200400c181616000141075 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 841946474 1250 841945224 841945261
    0x20f0a090503120a09150c0f080c010605090402060a0806012006010e0708091002160204090f0b0c0a02060105010e0621011811040302040e010e190b0a052811070b 71
    0x90fa18208004d281080c2c104030390204a91007855103c245185000c400c64189010142c020140002c114185040081c13500283c009042908020001d095442c420442400300942d0041d411100070070080c0f40b0681b14030f032255440301c01810311410b00c000c640c00070000c08440350b01d55030080d00248010320080088a800d0f94006000b803820b81068100742c8001c40e155040b0b01c0f07130b80c0030003a80001d503000c0c1c107400242074606541d0028801c000a0039a42230150b10031078500c004451701400b41000036402c070080000c0e01d96003c0c090340141607503803c2c1401903440c3c545951225074011003e004120410351480c0e0805417080c020300d14041325514040c10700444030424480c0d00c144604104950b01484900300c10b48003100e804407404100c60351080e884a00425280e20222102c4c0242c110304d02260072148440707190584a07108941096580d4050340089500980707a1945000401d000c81d602150a03240601000321141d40014022501030f9038803829034441c6000f114990005410001071080b0450500d0340d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 841947724 1250 841946474 841946503
    0x91110020c012f120706110913090c051804111008040308101701150902040b0a0c060902040c2303010f1203140301080c040e0a020f0d0602070506072f1f020f0a090503 73
    0x2000030500000e09c10151f09410742104030782d9001c40d0000c0c0407100703001900070074019080b00c050200100000c3c45990b803c884c181e40481440490fa01c07182403007284d490941c240380d96800159111690110b4850901a0004002a82034940801e94080350480d825040306004000680b0048491100d01c1d108400d520a428a51040c0320810035889131104450074a0998503006104580504c1c0082c001e02d150305c0d002c0c0d085403810429161041e044400e580b07031010088255402200c08260a00d8a4031090040b1070b41034500d00c108000320700280354a00708103486400c0100389034a07109992021508242d11202081d84401c08440050070284905d06ea901e118070043c01d1143c103190089094046001a01409000f120030801c0a110140d415201440d6000066400b0360500c1c00e0020078280c2d40221240900749000d600c110b518560460021407102541c002c9c01450020303400e06929001d0b80c00d41d02c410150200442030f07243c2031001c0102102480354440080c0c850901d8203051501c0c802c29400d50b03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 841948974 1250 841947724 841947727
    0x3090109151a0d23030c0a080c070b04050a090e0307060f0b1203040803030c0a1205070e130c0e061804110415020f03030a0c0c06091110020c012f12070611 68
    0x8607039814420781107a88241403c01c0320044c1100c40c0c0785544914840316006004a401c0081080500d000620039135040c9002c070b400d0241c03241248401441180b2035998070549407041084969465006141c01068000581307081c101c46880740000d840c000e01c0b85611a41da244d1942000385000704d1600d0b101070ba00300047d420941030200c40c80e500d200181071054040c80118031b80340789a2144209040b080c203070780c2c1c1c280f0442c01d1185010b0102c4102c1026103104400e43c4a00c0e880405e12880780740e45001c0300c3da8440c20180c0400041c400c49600080d19020510700b03400c490440e6444500803e1010341c942a0410ba0701d47c03800030302c100211420001d240464100d1414801080000816241c00501c01d034030000352038407450300545003468006801440641030076407034400d00903190100030700514240e13420040d51400e0341c0c040362102c40355403003940803a4000140101480030384030312000388042864405d0300300100c00740c03540c0b0b402078400c200c102c103040c000f030b03c00100005402003181c200e40c400c0e81d00d03 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 841950224 1250 841948974 841948999
    0x601090c05120636160c020f0103020d0e030d0506090f0712060906081b01020601061215030f12020c10050708070501240501080c040608040803090109151a 68
    0x10202c1c801d110501d4030004000c00401d401e80e58031080025141c14810400341001019400c1800c02058203200242e642d0042000500070b01002502c00800c61a540c6c070414404041c0d8200b00103821900e04c0740b8105507090100e2580407410344100c8096002420046890300180c810780c409460f0010b00141c0103883d1141800726602050064980001d61410000c003100702461a00c4010101544000b128030b085c03003000034545101060b0303203c40c0c155400081c24003143c1100160398600d000c1c860840003444105000200c2c41145d84150300c000721008041c11101c1c2e9035251041c04454803182622200c02a900c520072040d01085450320200041d52405d41c424400700d0081c1060003000c41c00f600d06640010450b003000420341c0300d60242080b10400340c1d031016580703221a034001c01034040c45000c40c0750000815548031070780060760b080340c4da2a034502540380d443e5a40c602e81da4001a0040503250b4850708450001114002e8051002e245900e00207880390107101515105007040d9045409010207102c1d4 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 841951474 1250 841950224 841950227
    0x6011a0306010c0501391706120a0203030d060618050f0d14060c030105040c080f0c070804030816150c0c0b100302090a062d06121811030601090c 64
    0x5890348240309082800d00c1084a0505501400445506001082000b90340c24440c03202a60851a0103440c2c4094000d84d40c2165402c4c0d40251001c1c1f04802d5114502c4000303855071400010480e1608400000e8070040502603000c6440c1d50002c000000c40f15442d00c00c01c1c465654040e01550740300454403094051039103800f0100d040c400c802c00d0040c1c061442d00c0b4680041c03207103c00c44410688a41801c0300c20b01d103040303100d4017240c0d002805131038070480c10100b001c41d48a200780b000a006911000c485021f07a2030301101c070211680804030445001e00203003c0040031034080c1c005130500017030f214450750490b041480d11400300490140301b1001a4175001810820552115040c000da55202c1040107a07610380748144080e00500341d00003940503d42e80104501c05030302e03410500440340e1100da1410018800c1c040e121018503500c04041c002407625600300025071007404903001c0071016600006802100044100b203550601c1d0050381d41642c11034030303150142006c022180c01003e0690081101d810600c80 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 841952724 1250 841951474 841951477
    0x7081e010b0313121d1806060a030608030a0207080106051206282a0c080a210207120221180414070c0302121918050319020306011a 58
    0x10301e421000c0101c0002c0a0b1041042c450301010b80120b1040340308041a0402401c0100120094080403000c045840403410013204511004801040c020166600e80c800d20240b508040d84a0b002c1540350440001c141d04288001c00c904d010303650150000340e003810802c6007034a00c258080c0340540c0305a0102c414040380403070059009a0f811a04060001c406169029091078502c3c0b015056842d107403d00b1032012038001e402c0c0c6400b101d040000340b8810036a005407124141140e0141645408002e60801244580059002070900380c460791141070558100108a8110f070038101c0781803010420602d003950f0100308078a11101402c03034034150441802900003540c0107001812540d00b0030998a80c0042e91a5002564100900014000c2c5460216002030688640c41c4058015001316882098021035240484031101c0021102800c0070203618000c0710409907080c11111035030413107640495165030502600540b10100164407001116a00426081a01c107904c0100301001041840c07079100c00b03540 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 841953974 1250 841952724 841952729
    0x90616170901091b0303030b09090a0305030a020d0603080705010e07050120120a03090c090504110609240406030c0801140907051c0f0e0d0909270b07081e01 69
    0x224102a039403120003116015050b18403000780b460b600c0701010b0300203007144a40319045034080c2da01403200000100600c250500e060383c00b091941c11401c00034000c40d000c3c1c0300031078004201d0040186481c2882030414100c59032500304403018070b4001610302c2805800d00606520160080286c01e84500d4480040e00c0003240305441c0c40300302080c0b1240c219410b000e1107502140c0043c10007960392102c20b060010010b118204003214404410740001c01d40c40564440c85100e69401a140e0021001181c100301c402d4110040140c0e014480080742804210000c044c800d4480a181486071070b582845000b0301501c0118018a0030130038410010441114401c015540020080d59981c0407615840400c42d014480c2847e1081c84118140b001c0e0070480c2d1a50110380202004a8200030400b601001c0948a2588540709400214140020b10801c0065403000c0d0040b20080d03141d000c94000060160511220000195282502c02e020440503136004080d0560010b01a84800f0980000f45061417580c101070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 841955224 1250 841953974 841954007
    0x501110d17130c0807060f091809141c08011a040504021321060510030807020f04020415030b040b060708070809030c0409060b03250905090a0c0608090616 68
    0x700100b89200900c160680d503050700442c1c1071007826241d0042c1d0f0b60342c0310a413280e000040c100381c03404000c43e8410300f10202940d03c098480c01980502422090181820b81e100340c8089401c44034100480108200d103078449402c61808000d0320002c102c0150402805a111041c1041c103061019102c4401404a070305440003141d00584130260030041c66103013074183d0084007014108052030110b0405404c1020440c80c41a502449103607a1400c998801041c68800144848014003200005280c91413208449040181006040541d1501e403d01007451481c40d101c042940d90300c01d00070354200382c0540c0510f03400070b503403451400b403031551410340d5442105409851000040b50030b6125541c00d000040d4a8080280b00340503a00050070280c00800d560600b0701c0c0310303100f0307815590f80c503250b010781c9102d002e07020b040301c0790300c0303c0c03410101c00c0140c1401403a075100341c02400d041c0800104101089170207021203903151040361500e11952132038460040c11441e045600e60181d0180f00c1e9021030040c1402949 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 841956474 1250 841955224 841955267
    0x615130b0715050c0418020a0c08091210060806100e040b10120b190618020a020a060e0d0809030909010302010c14010905061b16110604030f03090501110d 68
    0x2035041011184541a242c00009402c200502040750074900180c0103032004009505c608508080e03200040784128441078000c5400036030254041840740003d0604240003500d904a1036032204107440c00c0460400a20308120794440042c0051070b0704000f503c4d1f11080303240e03e21100c582000d102034800200100003c00034842140041c22400030980144001c1c00d415076201c550004a14007071a0b1544c0440314a002803441751400811601c5601505048840e0304c40c0c4542500d13490007900b006035200303851100a510942d4041d500280c2d8a1056806018164018102c2c00c413800c00010005403000c1c040701c04c240d006109840d40c80c0e44148482c2c1c11254242002400c5003d10f10301405102c0304002041c0c07403035107000d01c0c40c03040c4400400d5880c8103d085a854031400c4540b0089403941d801180a01c2e00380d03054010355807002604020502c0b0740c030000103104070308095aa82d91150f00c1000342e02d0440006862005c00c002950700003441031380d03c29086018102c40780d1422402413444c0c1b003040508945401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 841957724 1250 841956474 841956487
    0x30c0f141b0f03160212011e020307091e03050729030403120c08060f031516030b06040807050102070b04120b04060b0406120c05060c0607031109090901050615130b 72
    0x810000400c40b0404001a26282c000c2c030322030007100448881c400d03800b4841495601c030344000706101380000030083e05100c0814101641095000350030003018202480300a00c00415020003001800c1200d101500b6110b05a50541c13502e1424000d04e03070b112104540b08204142505240c6d814650013900c03501d0105902d80d6138900742118114003855030748041c0362406110119043d844802913100d0181614101e01020308a010300d41d0740c00c03207004019250032815011681c07070821681041c00ba004140360106610900a001814640c050352020341213500202c000c100c40c0d43c041c04008001c0c004020101c0c00d181c03030119818444a0301040c02031240300c01500060070400240e000300200d04002c0d00822034541c580d031a01850540d107180565800900c5000003a031407402804481c403103c010700141003661641a4143e01070541c03809065190070050010301c8041d111116101c5c42860214000300c0c16003402018000c0b6040702030b0014a5400d404c000700c00030003080130b209800b11041582401d580f0074 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 841958974 1250 841957724 841957777
    0x50c030112061e0515030304051003020c07031703010303030b0d080906030406060902130311031c230d0204180e1b01050f030403081e060f10120507030c0f14 69
    0x40e0b0400e41504104076041180b0a81c003c56001c075100d89040b51900d214841020100740d6240076510969912071851314440c0089482a0050015004c9200c21904495220703620700c0c22410240c401035a0300813000c4010802c0c50740c10f002d02e008200090b14031911407000360300c0c0c803c81d92040304240c90003514004045010025540d110f14020407803d0400c40d20760b6000f07585080702d01c450380f0068410400e848540071181c0707004501064196640c0f20f8405840b4500c0d00d0950301241c802e40024622070303041c10103d0041a0701401030440d4a503131200181d84604000c401c800b0075141c0c0c03140c2040c0c50303e4101e046079009400110f035101254011410b240b5140c60300c0c0105ca0611400310f82240050001c024401019000180c01c0d0007000c81c030406d01c3c034041c400b0440810b103d4045501d640c0c071007030b08000132203582000710f6560702c500900d00c2c20340d43c00400b0451280075540103032480750000352b4400501050070350103502090319100c00c2c40c014141c0d0f007030750031340051500816080f00200c02c2a4040c080c0d141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 841960224 1250 841958974 841958981
    0x1f0801121a19050108010b0102010c03061809021302071208070c0203070627030501270b06090403030207050a1a24090603031207050a080c2106033a03050c03011206 72
    0x2000740001d03c101c3d81c69004542c041c2180c2d1003618055803c0041c00c1000900901516080d40e079681d901108410f042c0500502030042c2060a981011000c407107441c8256940c001480114014a005484903580d00001400b040d00180390740100701c149841e2000581d8007290900c2140c4c2c0514251030700c5449034a541c0700600d1450003120300004000400420230070113401903c05000c07036045442ca8a144151141001c0e640030b0340c0241219141c900081c0c10707143c4100482d80241c001c0c640103040c051a90b80e402d00e46842e0075421345508150030410054240b24409031075120003e02960101c0e070441040d224072022006080510843c0d0040006516850400035101d10200c1c8603281c011030305013008058019840f0080b003000281003400001c944d030300f054040b1070040d1000340c10194810078000c02d10054083c040c1040d40d01d400742d07503d004204064494185150190807080c0040401c0c6400303410302c1d00d4590700c5040306150030a8200031120072803d007582c1c1101d189008007081c290075031070444000d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 841961474 1250 841960224 841960261
    0xb12151201090605100b0f0a0203120f0a29120a0c03120f021605040b010e130e010e0c18070203190f031a1302181f0801121a 55
    0x328003880c002a680005400050103940a0720b801c1211351241000b800725a610313070044c024078040800c03006403071014040040c400d540e003501c180c0742400d910342e60755085440c05495401c4c140001000b4047c0c04040d91213205032141c032802448186038100521404034603c03000c2e1407840380f031801681900045090011506465002248240d0b0741d03224074110701000100412040090491040104503038000161100c0242032a032821b40143c3c40c00c0c081001910700b800042c0d040150800c00b041e07154071034480300e002d40f0748141c50100e01c15070080001c0303007103940140d080c00407940410301d00c100c00d03242c4903800b40d0003440b07000003502c060b9601c82c0c040c0c1c510711913521902d01481d40d010042c0c010702c0e80304894070610306840d5070600c01540e81d40c0303003e4003201d22581c40c10f50109800c4441d89200701a07900a200d44005c0c0b440b04c042e029030800008520500e002c40f98000c0503030311503007490342c10f41c00290070380500781d20110503c0d444499180c3c40200b5442d0140e145455841034041100d10170070f004610031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 841962724 1250 841961474 841961479
    0x11a0f03120c010e0f0a08030a020f0d0903020c010210020310121b06080f070206090c0112061d1b030c0304080a0504081606080c0a0c02040c0c0f2a0b1215 68
    0x98901d04094014024450204c40316031500501102c03150403100800c2003480f81c0d0304020b2080c11504c0741c255440095105083e03141d5282c00410071107104c00101d0084601060190300075050885100001a040c90755107071044060a1040080180a401c0520844203580c00701e0784019000c0c400d407420044a2031659001c40075400c070700100155203580183ca19100c1c0748410030b0000c3d17580312158240d90340c00e010f5480e0507890300b000c0071007100c40d48a0200180b000310120008110290f86603061942d80a071107000d0b0001400c00800c00031a9810070214002c00c0e420f0908207440d515156043c50f41c2400043c01c0244003100010341c40a410b0b105400765030182ca1142d0581d00280e00080680200081610542e004500001c0c0010285020a815070740320002c281c86106010300c0710390030840241094510b480a01c050005281c021a058803103a4250a108059524412022000c1c900380300d003183c00c4ca0310036407451040034411410980c0603100e0300020b03101e0703480b80d54035600000c00309101861501c98 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 841963974 1250 841962724 841962727
    0x17090115030501020c070911030609060a1a0c010c09050901030303200412020907031814030d020a020313231c050d0c0b1003080301032d08040512011a0f0312 69
    0x1042c03200660080030031208031412038070f103580c0c0c0e030f90b9500950310504003030030300b2150a00010f034882c1042c020080d80210000c2c14240050b442d068924100000402c070200c8541011400003c1014240304002984a207810201d00c103901e0310002424000b41400010f08068940e000d80341d07404903140d0b1810784c010b64840004e803520f460302d0105000b03d1540b40140d101e07000a00201d5606070180c411720500c900003a001c500e286220f6181c00381005400034024a407440104800c615400280c800740841e4000d40e07004d183d13681e680d07a41311501d070040368018071000c95444104848070454101001d0200105403000021a01c0300d41e0a0701a02c3c0030030030090040d010b80b0100e170b2030440d408624511514800c5c140389180b5180c2c1c9120f03183e6407042e800001d007010f10410040c0302159071100495860340003614440348034188400d203442041040d5008842040010800707201c2d51800c0c002005012003608001c2200e000c864450300f095004c19802140a11800d1009001c1501d05000c050b00c11190b401d0b580d07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 841965224 1250 841963974 841963979
    0xf14012702070807032c030c042d1508070e0a050a0e0718110c060c1c150303080f06100f090f03110f012c120a03200c0117090115 57
    0x141040354090070340035451a01c6c0d0031208055140501c030410503680034008141d41e03580c0209000041c03d40d058040004c0042d01540000802c10b4010b940b14600c0e00c0002282c98130820100b18009c441c180c1044545401658041c01064186400182c1c06103100c1d401146136140d20948034001c2010f44918483d0307000744200810418080b5400408010061504000030b80746607401c0e4001e40a000401001c0341c00c1a400709803004080c502401d00740e10444030000c0754842141c1041c0c21922081014221040d1404040080c5900710b200356601421011400d58203281c00d01c0001d25510300c40c1c480c3d005008072100e4030762400d4441d28140c0090852640c01540300c0c0e0712030800084c0c0e04a00145644100040626030b00b040d44210300c2d08220725004801e0340c100008200d81440640c5040c010f058002e0b41c1c48140c01991041080ba00c60158041d88030480e406410328040e42c24200043e035a855540e000b010125503e0740d0111000c1804c880e850303c1c0035081e0301c42035044c030f000d0000c15000001044414101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 841966474 1250 841965224 841965227
    0x3110904051512070b0403230316060f0e1507140408010b1009050102190f0218100f050d0204020c1e1e060709090f110d0f1401270207080703 62
    0x1e0201c050401c49a100c400714201c3c0d00a5a580c2c07480c021002d00c200f082c0810800224551a2043c42a07070244482e981c2810300140b5510310b82058a5150140e10714080f0031040c81100d106480e03051217a11010b104c001c000701c012556a2031004102091400c2400c0041d80041c4030300c2c1d2210b170008100d03044640d2145d031354a07450b0207088200f000c0d51203884c0032010348088600459020303049807010780140c08100144c40c5c03022054038892406803114a0300c20411401a520700740e806402030802450141241008820307480b036542d140c0c004a2041d66484428002d40c0c0c0c2d1000a04c0342c030350b412540980e8480034000010700344516802100b140d6001e0113a041e0340e400d07010401e4107900c007826600b04d00d102c6061a165588500543d607602c04140b03610400c0c011340c0202d401400004c01030202c081200b846c400403803241540f0455150b41c10a54640c0d8452180409002d658503400c14000001182e504240c0038018a02d6210039140c028151002c009082020980681e4500c9400080203511070381a800c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 841967724 1250 841966474 841966501
    0x30c051c020f070e010b030a0207152403051b2e2a03120b090403050334050310031205031611280615050913120311090405 54
    0x20394400341c0039015503007050410010700c54080329107005403001582d2818001e00742c0c1d41e002900840c02240c080080700c000c9a40e6540b283c0c00f03e025618005025007440c0e40d07000c1c000000180900140035114410004500006503100d0194191108004481e40c0140020401010081d10521051340c0b28100329860381c1e00d80606c1d12100190f180c1441c500110700701c031000d8a07a88460a010302d00011106804a0b11400b0400c41e95a0034080c0000c0d00707280103002900503102124100d0014800000f0800c412040552640506c0100400315004484c0420b00805030510720021000304000480003a40b410300c8401160011500003a044422000c0003000610552046400032302d2402e1649424100c1da20603040b281001c048900940000740c2022207481113150107100340c001013844041b0000c08521180315111f10402445117182c042c0e485d00043c4048188001d194051006088891030040b0310301c80d0400c14045c25518000802102c3e44c6150000b80c01802091500645460b04110803030000d0300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 841968974 1250 841967724 841967773
    0x10e0a09050f07081018020d020d060906050105040308031803090a03050102070308010e06060a03151806030b07020309090112032a020405100f030b09070503030f03070e1813030c05 79
    0x4502c20342c1581e6a200a481d003860030b4482d420304015010342004100503034600c0700002c003400304016240c49400541d10050342c20000300c00140568809040251104e10312441000340404c0c00c25038202459a1100986030200504064101c994045011003800081c000c8480218008002d0018140c480c10528000e410511049020644440020500125400a052050200070b046510341030100c94110b01510241e07581c0000556800000f0484010501000d609050b80c5100042c03c00e142d800c4c4030010400103000e038029134108108041840e11060f0306141500e804000b904082400341c0380c100c585082282c813aa0000040f01e400c19080301c02000b003140c10b24001c507402e00294983d0240000101ca0310320411143c00c1d44043c0420010340e809103a20f520081c00801d03600006d03030301d401290a6500545848100b05000420040c500c0d40201604c6001c00c400e80d2100324540c2c05034409c403103808000c2c1c41c04082206088012003058890002c0c0b603041076000040d514010303042c0d95100c00600055 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 841970224 1250 841968974 841968991
    0x103110a0c06060b07082d04091a03011a031c050a050c0f10020c012009101701030605041203050613090f0609290f040209060a0b03090c0a050f010e040b010e0a0905 72
    0x10703446d0506001d05003240203182c0c0047c80c061405282c60040380092609032508d10704140b04001e030114940d028810030701008404442200541c889000301810000d200700403003108ca6442403000c0700503a01c1820f640e03000c0f406003482d6039150301981c2c0301441c4c11410b4a0180603031142e01c030b020703026803444d0700a80400c1c80148000d2100b22840b1600d00d80101e441d006401003120240015030a6107000350704000c80039480c0c20880000811202c114074641002d030400d840382030701c450500c000c020b400c8095034264656490b0030401c904203100015001e41c045641070854a44401080017400300c540960401c040d8410010804c6102d1441c0c882e28038070141030058481002d40660000c0d20b5001c3c480144903010040c9001010b5a85031300b0800310010241c40540c000c4103010011a00340d000b4401103028500c05c3d002081e40c03500c10400c011011459400c40e038001c100f1082c508104d660000c61980d6884011200801c0d0000c100c00100c540c10240800f0b00e510262070140003620451f290310890040740703030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 841971474 1250 841970224 841970257
    0x50f0408030a1d0105070b07031806050a090302240126030c0d0905030106120f140a050c09070e1003050a151d01090b220f1a0f0103110a0c06060b0708 66
    0xf1006440900481e0006011000803c4c0025091031199102c03130070302c01800c1800440181640c440710308650b8100c402c048410f42c1d5030020800d050301004480815200c4403d40c402607401c03448062210501881056881d003581d40511007114622204009d4018407101140c1e00c41d0f10036034060b641c503800302a940000c02c02403000818642010300410085e100084a080205c4405a5031600c203030340d59070340c00c0c4c50045e00c1d461b8250100f0002d001103034146024a00400403040c0000c00c00460030303000f0702050300b480709603a44440c4079201c0c10900900c000c02e40c107002640d550740c18a81d1014140c42e041294100845050115249801102c00c4044a1120000c8001070303032030300b064408440705450030943c060312039000f8409140c000700c1d94514158078541e022410019000c00c0d007041e0390449001c0c800c8510346007607002c06810000c4502040e1002483c0500845142c0018514540304201000e0200080300103201c040c0900b64020030002c0000c0e002040c0d482003181003d440039000b0368101c0c00100130 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 841972724 1250 841971474 841971527
    0x90b060a090b010c0f020d06060b030103060501090614190b030c0a031109060f03101e08100b1f09080604140607032007060b0306240306011203050f0408030a 69
    0x4035881004203480040c0c6900c440302413661580300c810714a0040490307010b4005c6107000d00003410380c000c0200a0240880c0c0503200c0d4154075144080e150b058210140c142e1502004011502e803207409025110019103a07070400302d00c0b50301500410340507500700010303410300003092180f907080340380040c4010100780d80d003000042189680f07403080e8030400250070b61146c000e11007040d90200c48070040d900f1503484044001c03e1035032800c80445514030003165080e18083d2510030030041d04140182e414413003e02e80100113602248001524074190301c084541750020b0440d080d608a402000c8010190201800300d0b41070340760924000c10503914140840ba80c90080d5404125418000d0152500c5000c10301c5c250000500c090180c4402904007000c140d9005482e910481c0085d141801040e0240743d54155203081c1015040c2011950000342e405a070007030340084010018003103a0451502c00587c03510303009646500c0340000c4505802160444103480c04002000399a1070703000054095180801c0c1d0744c0449071079 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 841973974 1250 841972724 841972739
    0x180f2102060f0105400b010e1f030e030705060720070e190e060a1d10050a0207210905040c05030a0504140a0312050105030c150a0c06090b060a 63
    0x2842514907501070101000144081e107044000342049544244415001000700306100081140080704817071103040001c0c0e049000c82c468000e801041c1000c2c20604801c000c1d0001082800381d0144020130740b403510505151200b813107500080d070202440b81c220b03900c0321030300d0400c2c3c1d480d240f0a40e5113601050200051852050b02100c0e00c0c00780d0f90941014202641c80c0c10000c19440c80000c058030740c0050203c0c203a0103c1800c1c0c0c401c07070801c011064020141480c10907c1a002c80b40c00003c102100c004443d44150750084c0055150740d0b450301d0a00200c1c0f107443e1020000040d0180b0400200041060b800c010300c0c451301c0000e900814480c680e14180555038410038442110281030324039000410800015500c20305641069810900c51061100740c145081c641d50300b4810880c50131000102100160900054280541c80c05800118050807060044400180b00782d14001c4c0803500c501d0003c581009070f81d006d1440d40c03540f01d400c0942400608020b2074000344043c412580a0310490540c0004103103034 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 841975224 1250 841973974 841973983
    0x3200609031b01110408060411010801080a0f1a090d1407110d1704060e0a0503070b07021912030e0415030b0601210f05010305190203030409180f2102 66
    0xc800c0400954035040c451418001811072100c01da100541d2034080c209070120752030000b40000c1c54000081c0000e4101841c20700140b984140045041107108030040c080b00101003002d090103580125138105c954184d01e480201030340c504402d4421a10f071401000a204400704032a1780d00f13001030b0b5460719009441e040d90a481d002300ba038007402c140e0000440d008103090640745640f11601643d065009203040d890600040c3c2e10903000840000c2c47d880c88034403d801e1013409000070f8030301200034151541c00c24802c03d12a0085440c082d114684003004000c00704d0715100700c00003808140000382080c189034140a404a8038901c803140c001c51918100d4143c104106803201c040e69800001c54483c1e460f200d00458454510560940040d0059140403620140783e00c520341c10301919a00201d055851402c0c16400d20500350712480415081140c9803005a074040105d5007600c2c201000020300264100c6828403980140100a04041020000320184555080c240d08050380000f40b29500c0142c48000b2030f104c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 841976474 1250 841975224 841975231
    0x108010e041e02060903060c0d06060c0209041e1221090c0510020c090a0603020a08070f0b0a030e011802040f0b010c0809012f120a050a0c0203010b0a03032006 70
    0x50007000340b0903282200700c0c200b026030494002404d05080404800009081c00c41c01d8807000203040d00058503520321512802000010002e40c00e0140c0c01605607004990700c0440108000d040d04403c00c500c1d40b800104501d0f400c4130340d0704020100c80d500700003500506129000320220b40740294661900a254040e0b0003050720032507004c0c480501040c81d11081c0542d110006200720f0035030045011045e9551990024240704403003807900442c1c0719107540103010789142c254004200540040100f4020020400c0c0d24008076191004d12554604640c481200105804032020b07000c1d50801030050035042d00309141d04600390088a0411440d580da080c0d400460380c2d60860140440c0182c03c140c130100380d01401510010206060010442c1e00d900c264011a0300e1708462504405c02d03041840707580c14002c000d40301c0410541e5450324078000d4a441d0251490107041c11560410080e0f00c84503045440a400214100e003014042d00c0d2403d44074903000d002c02d03450005503034452034180d10b40100c04800080c842d02 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 841977724 1250 841976474 841976483
    0x3051215030d11010221061206060109210609030509030d0e0d02150d060b0a03050a02130e060a0801062903010303080615040b03160e0f030d0f090905070c020108010e04 74
    0x20040740c0c4002039a8403540361203080d0340d1303560074000b04541d0340d01108081c0e03861181c500e802416140c0383d420400b17800140c128654895000708108802641c11a4003007069a106090801c0e1034004207081c041c3c0000350100c0105a40d003040a400201034114002d441d5800041301901c0106000f0402200c0b40039100403080c2d488500c611500d80035052020007284100a04048640360003641c01003e0155001e035480b02d1801000001c0d2210b030250b141c40390300e42140701b0000235440c20040d146400f002d03004074064501d10310440000320381e0036070350b01d0182001041c0c1080288652a580c103d01c0b0f61000158060300840c0d40716034448160601c8503011a41030740d42c0f546820f0600d40f101070920540c1c0d44100102104040c04002c04030b5482034401c040d600c07401da008840707041c0110b51903004044081c42c4c0002030041c42803401a04031542c1c0031640d503051a40340e261000740803600040450b0403800715808142d0704c616010134803580680c4103201d80ca040d8001c1e26080b001d82d0340d83e1081d01000d070341110b0140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 841978974 1250 841977724 841977733
    0x20c06030106050a0e1e211b2701060e012a1a040f1a070c39090c051c0b011101181202070303020a02040b0d0f0305121503 54
    0x42d50140000c0c0ca0726640b2441e00300f254081d208003082e401c10030300c1840e0001810071203c0080da4a45030005a07182c0c0d00d00040c0201a406421019540b0040e01c000404188181c1d009521a51a8121508031030035807010912080101001e008002400a000b0301c0b002405204500020394092200c450fa8134003c250384892a11403110381c0300d844020070408807155498940f05030207100710414158080c0d80200108000f22103146011002e411681c0c0a00503000c0c0d20b20100402541c011020588075078201309a418503585905c440400c040314100180210107000041241501c1611200d0050312000034080003248050203055982c1e01800a6140340514120b21201e081c80c3d41d17410064076400181884c00351a200c588407142518030542c4d14052020035008031700e0500500394610210900140080c0c0070690a40c2c078000c0d1954115000a03020315120004030075541c171204052070700107401c024220001080b0780b500401a511002c4220380c4e1350400c2021503203114000c084106a08401401031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 841980224 1250 841978974 841978979
    0x415090804120305040806010b0306130c0c030c060b040f0b0f030a0507150306030c060201050a0f150512150403021f1e0e07080609030c100234021e010f020c060301 72
    0x4074491440b080084080080c107100015207050b0400800e4045d201ca5040315851b441c122080c8240400c0d413014075108035091038680110b550f041381c01d048013607806140000a140c00c1d03003499409880c8100013036400500d400750384c0802c03000710340c88079100c18402c81d40c1070b40220f10a4201661004201d00c003801a4224034000c11150f80002020010107000b030074041620b41c1c0e240c4070301c03010030155888100981d440e1400c005000300c091040303000740192904100a03407417400000845191050158600410580c6210614080100140884516182040700ba80c3c90b09240082d1908024080603042c1079060340700c0c2c11031210301d010740b15069180080306141122880d5045015003908042c0c1e420b103000344100481e00250078403603c2d100b4079940b0300560f0745548400d1140c0c50725242200080420703206200c507542031080c450070b54480c00c010110351341d40c800c40c600c00104075420f071120095002403240100e042507500d014110340480000d80724040100b442040c02e07030b201d00c1b038220300960012040005 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 841981474 1250 841980224 841980239
    0x80d0507060908120f060a06020c0f011206060504050909010911040c12061e090e0601050d0302030d0207060f060b03131e020307180509070b090d1e0b0415090804 71
    0xd0000140030702070104955006480b400f003d90f0006082c18651492013082007010390310081e4180c0c100c2d40650f2201240c5150110094860380c50b110b02903c103c040141d880516032055506030b00080211078100302140d0f55100141640e8042d10915000c0d0400720001881544103105030b4420a400188000103840b40004120041000210320000c1c010503c09800034141c062003103801400004071503140008400c01203c600c0300d074076484491034905051148068141c0826181c2c1110701c159400310b071006452505a0941c000c204980c4401e0344045000e0060010b260840c00040401413020400103440342c540311500d1000719894541002c1c100c18100015049201c2d06042c03217840d0780d140381180c409038006410b24265600c54a01c0414849041c61440180d00c81c10303030400498002005014900a28480702e8000d441c0b5140c030074420266840203006021001480c114070400202c8140c1c0f005190610062200fa503060740c000024480190100b00140319003c0e980740c0004603941002e1a001c00c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 841982724 1250 841981474 841981477
    0x3061d04080a1403090105091c0c11032406040606080403051b01020f2205030a030c03050c03090a0810050a02031e09121209061e0f181605030115080d05 67
    0x200b040400040c202450302c00101c00020390302424021300013045c241030102c4d07507525066801406544021407403031b0380d0b076a00e900074840440d403a81c0030303036440f81c0c5800c0000003a04000140e1810400f4990000000d002e510303181c1886031180e501282c04106640e00c0701402c4544e000101e8006020610410840c400315124140c0c00c140342000d2030001d4500000c2868480d100d030020341c41c0c1c41c5641c0049410200624040c501107003e00390680040c04540703940d4600404800800d60003030306101000942c4000e100701442121000c25001d491061255952108142d42d102080350b588121403600c404249920300c00e000b140d0090b40c07060303114400111040d91100d0f40d1100644070070041c2c07040e960907185500382d80c0301070892035000744400b400c28038105120300d080c140000c024100c108400c5c800d00100d5204105096003000d03500c1180a85035a5550170180712842c5c0800d8094248907802e03400400c1c000750042070042d41c00607002070058904020300300c1201c0b44a40034240070743d04555109040c0d00d204a0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 841983974 1250 841982724 841982737
    0x601060804080f07020f1306031401020702010906050f0c151602010b010e01050f270913080d09020d14100b030f43050a17150c1201090c03061d0408 65
    0xb0301b04100d00300701c0000034845042407460040415184c00c0d00b04144900e001d140c01d28a03030b10b000294034081c0154002801b036403c500850b02407080205603103452103120740c1901c0d4441c0203641141c202d10300c6400c43c030035654411031b40212240c909604200310f40e84103006501d000740045e1207070000740c2e41070001590a90040803ca00184a0920074025041c00440c95107190140f100c05011900c44004140320040800030710380001c900c034000103200002e03404021118401c00c10000000e800ea0144001050911424400b400a07440c5211002a45102288800b0034031130350300041100c1091401819110108118020801d400584000c00c1035051901c4904504003004485480054085242d0085031003840140a03ca80612414461410f00805003006444c42e034501d04440c10b05030420030303520103111801030040300114000c5120302c180030050300d6000050311110410742d1b850b1000c100041004215002c00641440b500043d0403582500405900b0f40b00c0030035903000e42d1140ca0300c450651104 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 841985224 1250 841983974 841983979
    0x105090a0c0e0111031e071407030c0509060a0909050c0108010801090b041205040b0d0e0c0109030807060905030d020f0c0c09100603020c0c2214160c020409060c020f0601060804080f0702 82
    0x1007006440d410710210503030350b201106d2050706451b0301860030031101e251075a800b600c1c11076004500c240085400031000c41c0c2102d50071504010242c6d66400401c005d0141a440b40c0c100a061070b00543c200702022546400000c000c1e641c0703501c00d03a65130b8100c070b081c1c80240348007a000011010101d0302042e02c100704d140c80380001c0d0030100d103455582c0e00c90317540d20360140f4100525156188140d035800702c0280640c9a0f204401d10f07110f00b50314115151141284901c540007030030160348001d500b0070084207100784c0f01d005100c040d08649840c00d114811509d5882004e2461b1640500d0542d00389501c0c1014885000302641e0004008040c01c0200650096000d007102c1005d500c1039448c00340c00c0307540b00300340c11803100c18184001c44042041a0507105503002004020840382d20202044410b002c2c0f58480c085000141c90303c824008824008100100300132140640314909056100b26a20b80004110f20b000345e6000485a0981c1d072140100d603c2c040559005040400030400020408071003005450100e000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 841986474 1250 841985224 841985227
    0x80d0b0d14011d06161d0901060f0909060e130f021e030601152c09070306060e0102010504081c0209061315081303080c0d06080c0102010f02190c14030d050105090a0c0e011103 77
    0x1b030b2000501c11a009922840c002442104804892980000540014460602c0a00400741407100d0002e1442004203840d001a40142064090291004001c0056a00600601501c10582085070410070803071261070b029210316000007464000b02c01200b10800015510205030040050a494030503c030488241c0000c1c190f040041000d5485500280c010f071007540700055007616001000d0546415117540c00d055900d80000c0001250b220350440b811007264604a0389030101c003540d180020301a4505094105401040418402d580000c844e401c6c0d852a0305417204849003a1022501000304407410f00c0d000d8015460040024050340c1c44a400804244015050900c85031100044a00d290302160056002c00604040c80d41c081c03051403c0105120015440e00003c1c905201c48000e2201d060b50400c040c1c04071070300c2841008a0011060100d10080e613565006003103407000904030030700403135200d107030450040b880c032900710300c03c1c3c82d025240f54590500b000412001550550840d10f08074099000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 841987724 1250 841986474 841986527
    0xe0a0e0715081008071e0914010e07030f0908071707111c06020703020a060b27090c180a0b060403020d20100201150909080d0b0d14011d0616 62
    0x5d0204c40d020301202401d401402120381d24009029040e43c1c08840c2480c9801070010f1902400640c250540d1603125501c103141c0c5401c00c080f001403104090310300030603185c4981d040030401c2c4900200340c414000d40f54040d60b02c60510a0141714402c0c9040280f01e041c0081c420082c50400902018690303580c0156041400d0668488000b030341e20160080300180c00a4002e001003004501c144500140141c68011b070002c2e600b40c045e0740d140981480d103a411441c01000510a8900b08021503c40c48003500302c0400c0b07001904011243d120903030b1100344070b070b08022125545007044800c2e01e040300e4000380744880d002d1072922030100c0741020100d40001841e07101c3c01c0b0303805078a401c0520040142150300008e48201c13403100410440c85181c011082c0c4908020161011903040b8003640d110000c07107000000d80b4103081d0009550f2240e451802405004242e42040c0d0140045d4803039140400015403c054100c0386287d81520b4450884071050f1400c040301c1c0c000324151089507107208000406072480308114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 841988974 1250 841987724 841987739
    0x203032d220c0902120702031801051b190302120703141303020a0b0405040b0d050618030c10050702100c1b080403050f03220e060907030212010e0a0e07150810 70
    0x1c040e8004003240e40d0001242021030301e1840c1c01941c0144e00e84051420024211149210007929071151070411401043c240c0f0080e02103550104460ba1100032580411800301c0d51a80dd542c440101f0740160045032441550307240c0c2141150807075030745943c8070110146545140c840d030782c000c0b210400c01c41100c1100440140c5641260f100648403005040381c0f19031034901000243d03007480c00d12a0090002040031000224005940d43d0040b100d1051040583c80008006103103010361518400c0c14440c108490b02c00b00c880d54002c03406120182d003640e03c4410030114803010754680c1c0088a00040a498145440960904100200c00e2003040440e1030270341d0700d4580710301c0d02c54403100c00c0c0b80307d400c000f440c60f481488010015104142c0b0081404055141c4110725017481c100400c500d0182e1014000981050b04c29030403600048211284134030b0f10350f1105450030480000700c8151100318508004503c000c400015054219607550503442070384044a4011125208090460076031110740700e00c00f10390031 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 841990224 1250 841988974 841988993
    0xd1214090c030d0201090c09110c0604150507020309010f1206081e01060515030105010f121b09080111190e03240c0703121d0d0203032d22 61
    0x5440391401410500300c03040030542801c511200d86025689003850f81300006464180542c1203841c00200000e000300900058280c034070a4003540c0d100c0c0c1c010b101c00c00003000f00d00d1300d500c034486d802150100300075075038034000b40d9492048089071400300740420982d65890b40b06400303070442c05a5031040422811fa6030921285000114404880e16150803100608462402d00c00e54000704800c07602800c1c88403155074075940c14401801040c0c1009140d181468001e4000e001744144103d040c2e60411819489103814901c500c0380203010000103065040010b000401405120250f140760940c252402140301054902d2401c6410300c003045c0311418012140d43e60b800d00032409200c040040f4080302281c00200303000080e10040c100894010180a03110200b98001e11000170042000c00c0081c1d0b200000110a031424400c00d9804030520401071002d460b207030301201540c00f4609202c407840c81144035070307820294043d030440c0b10341003083e03040300041c090708114400a07060070740c43c100ca2210340d086403180c0c0c020 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 841991474 1250 841990224 841990231
    0xd050c0a030c18020403080418090f05010c020d05251a07120605060f0a0305150603070f0210090b0c070c0e0a02190207050306070c05100c022d0d1214 66
    0x94080c081c1041000c2c0c800642070b0441083c04500c00c601d02821907940f8903050040c1d0051581035550800b4500500ca05c540c01000441e40000e125010350700d443c035100c0c0c0a081e610103190014003c2a0b00407550307038014000e540c104018144007450081410f8143c0415074403200040d210304501c0851010340101030340c04540031300102c2c0e950001c0c496420740103400b40c8080758001806030504025845c00691028240d8407100003034039000c42c05485180780003d800c8840d08500380d00100000602502a030405001c0d00c031442c55400351121110858040022221425405401c441e01c603030024090051050041003100d1150003000440e980b1460000b071100e0040b00e500308a00e0340020364032008040f50420800b2034102d4070080034200d0030180440e4070340c2c4000c2c0200051200c0d0780000342c100f000074490303002d074000c10300401c0203550301c3c0d180002e540701075130440f80100301c401e01210030640700e40045844090301c503000200b1403c600424220780d50840d15000c40c54956480c0101e11860a00400c000d00 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 841992724 1250 841991474 841991483
    0x8150106091a120f0f130f0602161a01050415080d030b13060f06110109030f050d140a1508030f070b06010306091805070906050102060c0702030102160602070b010b0301140d050c0a03 80
    0x80c4e07450300c06440c00d564240540610506030061210500184881c038015116580c000d43c05078403a440c400f0020840d0402034802011810f0581c20341600e100b1040c00c05040f10401c541c14060084070044041c0340ea40745024441d040d80060b94400000b5000750404141c07440040d000c40702c40e40100c0344841c11284940c00c54007080301813400030801658032a184649944190000f00000e450554000d420341c14020802c06c24441e000c01c15203400f544640c840f0302c1d000b20050031100c40740fa140328aa070080041141c04a45898480404035601100100755107118428001c106d241c90b8558951100a000041c80d26041640750200401d55266a02602d00e0020409181c0d100e140f09500e00300c1d0800805800c1a40b946213420400c00c40c03607134009589070b001144034115540d10456400824060f114001e0144c0c0c4200c8c14188400070031009500400d091350181c5800075040c0d89900c010f1a07644028828003100008000165046262141c00080713201c0c441c408492581480c0d102003080000c4560050b42c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 841993974 1250 841992724 841992751
    0x806010303030b040506030d0f021e032505060c09040605100f030b27060406080607111015170a170903060609060109031203020c1608150106091a12 65
    0x2055050f0085a550410071182480186400700120744d554040103681000c100f050104408075a0090180445061180400d401201c8090010300c1e5280c0c420388a514608254400755140d0801c0100780850482e4480060300e503d89034414015081d82045407110750269543d54005500e590701074403101f043c82503841d00b41c40e140d04090090211000c1000890280341c0304c06100c007450100d00302030b003d010b5281d80b01e803140f5110140824024452034004200d54854030051141050300040c01030540c1d8070103001c55004400c0b0000c01001d4424140d4081c04640c0c00d108103026500c0c1040000f468048800105c901450782c0c2d44910000d00203018542c88030f004005200b13142800e0a011140d400802510700007110305148000918042107440081c050317941e0400c5410440b0b1291b01250401014142203a903600b00508040d16201020704c6680c445105006c124003281c0029007425040740c0484e2500703ca6280360420f20200c1e000016402c103d15007080150280080c0000a040d014081380030050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 841995224 1250 841993974 841993979
    0x3061f0801022b05010305030a0f18030515100b041503140a02090a0b0319051e0c0a030e06062b08070b180712110d0209042103060803041401021501080601 68
    0x3c4a04800090304088a4200001400440c0f0004200e4040c2c100d9490800b600b88540d500482c1c00000704c0d10018a0041c41d030300e00206002c0005100da10241e03c0043c1c0f20030680b10b4809550034000301c0e214980c40044144010026001801044d01c1000000e040104d2032031407200c0104582107044526031005917010a0001c524240602c1c07a201416555403107a146040c01c901811a5141c0181c00b951510b4568000036044ca60034006204a10110000010981000a0240e80c1500100c60b0000000d00c1c0a08a50116070002085030181001070008941400d042c0380c0328000702035010449901c1c1e25060031100004120800030022a07014054283c0b0342d0601789600300030492110820101940900e4043c041005000b550150081d803240c800070850020701c0100b580300c1d00560019510000709000c202c140b0217121405070282007201002000c101040d2400d40803144680201107240e4001d00c070038003103200005a2003030148414011519084003420401d000c1c00301c00d07001044950002c4004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 841996474 1250 841995224 841995277
    0x206100306050612030703020114130213021e0a090503011a240c16150504150305040f0c0902090909010618020310050a06170702030901120c11121b0c03061f080102 72
    0xcbd0404440700448480784203940000312550b41a00511880030350000d05541464415410714140405183d0140d46405050340040c05540062145502a5007070a0611030180c02082503040c07003000040a500c0754581d4050f03074103125000310000402d4000d04118074084040100200610150810020001e10703090580c0c10605050000944060080c24002440500d0402d801036412125a14000a0b5a560760621080180c00208003800d803541c0c01c20045400b400030740040c0301805083c0c41c05900c0b40c03200a403440c00c88100d40300e0010130100b64907203070f0b2901070700c0d40081d500090b05102005a003500e420000701240d103030354880c2000c5006d4403555465085144101c0e94494064000765080040d00320028065100310b05030825101d03619464248400d004401d418178940c0d038002258414040c00780d20125039400aa83c1041d60b45901c00d464400350800103044a070100007030054003803911990207102603422039011145a1001024020485030000d10180440c441d6140030180d1110b1080003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 841997724 1250 841996474 841996511
    0x61b0a0c032717070e01060c030203040e0a0507031b080a0f2901081e04030e031501140a0b270a150f17040c030b06031203131202061003060506120307030201 69
    0x20066140c02255080000385c1c810300e1841d04660803800c250b444446240742c104e0651003282c0020b800d680c0b01c10140600e030129a40030b41e10030f404c01d840410401c00082c2000410002c403041c42c00000d14548009400103084d40c000c0c0c52500d80c40a80881c001032096820003c0240d088520110000c0341001541c0340d680c00700250360484d103403c83e000c0312004013101140b034043c4003c1000d424042240c400c4500b1707882c01c115107d08116681e0a0580e556150618160250072001d00c40748034011000e8007182310707003010089540c401c4130541c0c000c000701c280b04074900300e88442542e016440040e807800020401039900302036480745000c1ea41c0008034804c07090085d1159465030500786079002300b5410000064000071b0b074401680d0300419080c01c582e8550340000d14200c14400c0c61018400048280201011b50341031203644c482c460400c60300c1c60400d41e0802c0341d94840417a40024400702d0719138204085140e80d07101c0340c1c00150181850307005003620245a403459000007801c0300140c1d5a0a1489590001c216 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 841998974 1250 841997724 841997759
    0x60f0111030f30070f051b07090c030e0a020f0a0503060108160906060f08100f0602010f05060301021303080d060e090a02100905011710030f050609061b0a0c0327 71
    0x400d10f01c400401d803411080310040042080c000d100042d01200900c60040c402c0d40c03000c00606100302d81461081d1401e0352213441034410901e1071802c0400c489c000314080c0c0511150070554900408010506408112251405844941c4c1003070840d840401d940d00c0500c4258040d2000750010130035001502c194000c0740e141540400d203030b1441c4c040188521a40810758882c005031500c0c00303500340d032100d110740e0041c648168000f08017015030303001c0042d001d0f4042d0028a4140c4418008218903928601498207074131030220030b001c50151603641840015114030150041241001740090020b1700c0c0c091440781c0440a07520704000f03900c03e400030000c51030300607040c3c00e12400300d03c0c001d00014074040000e012441d142c8114025030781b1100020700c46210340c500c41001590014070400085e5503034140035807a40320076038031050240202d81c0080c901100015440c81ca42d071034215400c0c41c0207000034044409500f03202080701000b08031410046c84010003004c4400c0d400ac1c0c1140c52070a07074604200d40340800000b6 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 842000224 1250 841998974 841999027
    0x10608150f06030411090112051209030a0210050702040f090224030601030902030c0325150c03050a0e130e0c15030a0b03070b030109060608070e09060f0111030f 71
    0xd0050454075030020040190304191001030301d946031460150000030f441e2a1881e0021801c200000f5500c40a01c844015130b800342043d25104100c40c410503c50b4850094000e401d64032039441000141004100700f400b007942482d0035420404150700080c240c694580c140c9a020b40c03220f401405620300840308080b0f41c102d0f8403060b01d1034440c29590035007500008003410706040e69070034098195101030003041d000c01c0c0c0c014262810b070101c8035940201c00060101c58010800c3d4480041030910a00c00c075190711ba003580c2caa0801034182643d040768aa840360402104000714403e00340a146c444a00b45151406000b402003441005560fa0340c0c944a41c00c0301e22485000303103458480c100c150722007c4035001440303060003007117028001002c01e2400c98180d1100380001c80000000549491039888502946c0144d03540c003000d502d4002c0102d9130340300c0c190903403940920a40003054452038640c0a02e4510710303040c1099001030307032013280c2103017550454009158003140003c0c0031813441090000303a01e14203140 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 842001474 1250 842000224 842000251
    0x110406031406031b040e25051507021908011b0807021204050f1c03180f08060f0711030a09090609180b070203070c03110a08030a14250803010608 64
    0x3680000399102040f10540301318090100b0001220380316508045508440e103003c4482000c0c106138088200d40c500071902052134440c0c0008101c0380f5103541d48400310b5151040490070807815400304180d007902c480802c1c0c1d103441580000111032100303000702c1d81400c107580c201485108071058003a00000000700741108540080c1c80d50118110340d1401c0da01a03030300541e5400c0d403402100c00801e090042104000421a0820f505071007003550001070541040280c066134020965241c80348100c6809031f02030285950000800140c0b104a48050640e02c92814900301842d01031800342581154480103e000009040003014002d02d800740c01003000602e40910704101c80300c0840355030130300140c0c8504001d00070700d0400b0100f10064802c10075550829000104028415030341c0c030304600115964022540550310005001034049804010b684144503103840d002100300c811090000b10390703c100d14518030f41c45020716400390fa48402c0740103014144280b00b501e40d29418020302400d076440042c060a0707600e04 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 842002724 1250 842001474 842001481
    0x1b060f0a060522020c0303101805040f0201030c0e1306030b100f0b0c0a080d050f150a05210601080d110109210e0d03020d031d19030c061104060314 65
    0x803120390310840d4290392000b46054820120b0030f00c1c0a0710404d481c10450384008014803a05041c515451011120801d18040c100403070050041c2c184ca0007110f025190220042d5440d016501a4000807104951450721300c1900300ca80300001c0000101c4803422451650b140014400c020326008442c0d00503561103034600c170703031450074400a10f091518040d2a04421000c5030002012008201c24022598003540c00c64079000c185050700f0041000f160140c503003146810100f01070414603103000005507000303400407051070304140600070361110300c00c0518501c0c020511900668102400518060044680900400400100002c0200400702d070f103560146d26020fa0280000c00c0d941e60b0b0a001c000741110a240740581200c16280c40c03051140054009103088669000c169020030400032480241d201000b14011400c61440340c0324038503c8002c04e560003644034040c0c4400c5071006500803442460402c22800da159900700603150a0b400548129030007203000d0061071b4250060709442990000c85000070714 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 842003974 1250 842002724 842002729
    0x6021603080907060305040c0506070c0b0409090b010b18060c0316050d080c130603050c0d020c01142d060607050304060c1505040312110c0d05090411090d15021b060f0a0605 76
    0x103041d8456144101d030002403010801503000071000040800040c370030385540c1d40c1d402c10000b83c001e94004440325007040c40003007804110b40056402446000080e0086500c9074410710040750f00020003c03031140300c1440001c40c00ea192540c0050505e2054018280300b0310b40003000317400100040c08034112070301e0170b2080d9000f00b60504c000070100c0e030645c5070200e000e4a464041100901c642415880250700004001c10110015000140e5190f50514041156a200030071408402c6810702040c00194541c60a400c01d48c0c8007005080c2c1080707004203241d20307040390365440b1495a4019071041d40403d080324801004e0006030405251034500417001884145441c0d54000d04c1c1000030783d00c0c4043c207641c078403101000c4244d00c426a23111106036004c8174440c041100d00a05a03421000c3c0191041d07007400340d1202419180c409803940c400018007880c00c4c902c05a84e4001d500e0408640c607800103a8240011900a41c1d1035682d220031641034000344c09c560401e942608032051008001c062550b061040420194 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 842005224 1250 842003974 842003993
    0x50d02031009061503050a0309060206090331081e0309010c061a0a0617060301090b0f190507050405010201140108060c07080c01021b1c1b0602160308090706030504 72
    0x1d807000d960016030200e0514200303008002d04040d01c4a00c1115483c040304125000610707060540c043e03201c2d080d42642c1d8200490b5510342c00c83c0c1c400300c40d41082c840503012a260341341d10942c0b00d014600800d1590620600307500f03404a0f691101600780d100040c10100007080810305c0d1104030301d910186250102081c00681401940030008040a07503c9070481541d030080104590080300c024103042c0d54503903851000301026007110620450062900200c1d410780307014800d252041d503119a51004d00d584074a81d24480e00001004e6652205140e807084295000d6481480d10a0000780c5402c4d85031410080028219104550342c0300400306500010300850000242995001d8002c0f500c00b07a0b9011907242c154803c0c0907603188400f044d80013041030100083e5030b120211040c00381c4011105105280c0400c40c0346491850a0000440e0081e945440b22091000b02080b40501404016203000c81d44030400301204c01600c020740004a040050101c401c400340440d900414242c5028040e41c206920f400890 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 842006474 1250 842005224 842005243
    0x50108060603040f0f0503040f0611060708060316030b041a04020a0b0c0c120c0f0904031205180a060507180302010504050d03020a0f03050904060e0106020619061809020a050d0203 79
    0x814002c0300007010003050700d19500201c0d03442026240c1111252803c240e80350014000d02c60001e0100c5000318035248580201e509007442d01005040d0b079241e0003002d852007030010304400e0300360082c81c040c05006007014980e0301c011840750420be2642d140c00d00307001103948c0110b00c0e10850741180209102c05a940d02545a042e1006103105580c1c035003002315207926104140b2280341d0440f94110f12080b030440c0100d001601d40303500b0364108000b4070341d0000304034002c0000c46004001c5200010601d52054131617100355800494034000014115520301d040e8a00311090200300d40003a150302c00c000d241540017200c1c9165540300c07144a41d206084d580080d00c1800350b406014040c48850111a0034103208120014415411442c1c00c9100032407820300030305035030100040c0d9000301d05003000098908020700607141220001d9000e48002d4403921030905070360030b020101a030305944925001c961400c1031060f50303408914007803000600080303510521500758100d0703014603ca8414158a10050385000c01c01034075 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 842007724 1250 842006474 842006479
    0x9030525061e03271103060f10031b0b0708031b130302010c0606091d0d0c0308071b060e010b011103040e340f0201050604091509210309140705010806 66
    0x413600b01c400c0207401540707010903600b42c08083d0100e18400380302d00020f694600f11419400d40703106940d0413100940015082d12003601c400341c0b9182c10001300310781c003412020030500701c0c0403401032968644c0350a4440c1c1004409861840000052069001c500002c1184c200355681e001401c0c40040500000003200034440a81405401c61010080041982c4214081c0c110904100225030b0f40382c1c03181c1c4007610881851080341c07041e590252007e600039544969a164180c3d228842951641c100300d603c0c0c1c0710141604001c2022503142c1001404074080e204807428000c0000484903101000100714071042541a20150010070040c440547c41000311390f4040000d4020750314144c00a00004010300800c4104025484500384040003a54004030300f5884500c2a4000d120b240c0b58070080008490484000904070b1502e07000c400da9608940c1c01482505009800c01caa031010500a45400c47d09080c0c00540007036a034094240400c48000b181d00340001d402001000725500b45400a000b50001a1043d807 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 842008974 1250 842007724 842007731
    0xc01050414010309140f0d170105060c010207022e2102091507050703140c0306010303030f06050a0e01061106070207260a030804050d050f0f070309030525061e03 71
    0xd45640a900200d022545c0814204036214a20f0102500c0c4d4014060f41c14085c02000c1e681502c0724829002d1004550812040c8102a403801041010399070101079812201d5400b44218000350303941c1e0750018070940c81c403c00d40304010039007a0305d40030b449030390055041407101940350428690110100c80404082004005075a001c00100080100701007071000c4242e0b080014240040103801316803041101d1080d850300e00038405d4000d03081c0d01d40c010b540a1702d070190701035801080824030a401c0710703000c848001400120b843c0c4900120300c0d0802290400480c0d5403181004100003948142c40940308017041002c4d1480b8181075600945500f0b041c858428101501c00b525404034403012103603d800a45c103801c0320000c001516024104000c21201500c5c1341c02040c81203080240500c04445100b6408104280303414002c00c0b030007500d42c201c0f900c01d40401200742d03800300c005281000b0300302103c4005040c4850341c0d5000c4460380c001c4141a006802001b84408500c00048880002d10703407401003604011 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 842010224 1250 842008974 842009009
    0x50a021915020c040b0406060c020906060d0204030311060603010b0d12030f060e040507051c0605130b0106110106090b090402240310061404050607022403040317090c010504 76
    0x10505180c25400070150380070103480d0200907940000d554103080c482604d042c04298030380c4040204482c0540700f06400b044800000f08010300c3c0c00300b051544400c0c000d01150404044044400881c2c0080d007045010400313a0042000b10101002560f900400481c02840045445070129508010790304000f0305170f951540d0b070100080c1c081d42042a018503a508200102030f504c0ca500b030a01e01041e90292540d008591011419080c544c049428112706065a1000f00c00e2984c0c0d0301000344401400c1028580140c61100c2c0014080e040c07560007002d2641e6000980c4003050074540c2113840a6104580d203501d007816540c02911500b400c5580a80c04582c40d00b00030455020034000442c181e180010021400010443c1c10840d030036818040d1825a0b4440700000001400c1014500c110300405501000502407140103242401850129070340c4524015400c00b40c000018007941c1044d202200441c82403048080e0340148001c4040e484400c0300d0007800307400e10620010707225120301c0c0944201001e00b082c14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 842011474 1250 842010224 842010259
    0x403020108041104052d092a060408010603140a02130f0b030106180609020309190311060a320a020a11060a05010905160e010302090d020d0c140d050a02 67
    0x101000e0032070213082800545003000d000203003600d01100500b81103d01c0006501280e4450fa011407007408a50010107203030f10568003211070200c502505900503204806034210382c1e01e64801410040050300004200300381549428504c1c01d111030611545903210204080242c0d5030040e401000c1e900520300014082c0d02d414505001d4107400386040d41560071b143c07000440c845444c0040211101908040124607100c007180b0080c1e100a503032200030b03035200078200d40c02c0344080056045581d21900380784641a602d51011418003100b1100320032a00d07a112280c4e039021440078010001101d50360142e4036104484081c3d48200031000c4c164001c400d0b4042a003698003030085509202d064180b808031407040c60304040c160083c2000b4081d00309618103100c08160924400d00f084142c080c0c0b2511400842840580110025045a40080c2d401114403403001e0150300d41042e050341d0240240c64841805042240102280d100701480303a01502080480e603003c600046a18204141c0c1110000005840e5680 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 842012724 1250 842011474 842011493
    0x12033f04030c060c1116061d06070b010902071506061b060b06070f02240706050c0f0d0c110c0d1b08120a021b011d01020106090c030f050a050c040302010804 69
    0x2c2c0203041c54980400b40b842107400ca11100002c1c0200011610310800508022021a405209400108a8807203070ba0711030b820815100b622101c000317441b0a00700a01d503200d80c16130b0142031f84001741244d400030703160040c0081d80d03400c0321240c030780d03850140f115900d807000042541c5920052029540310b411101c808014030f40e0843c3c02021001050551510428100b40c2c1050b0300c41c210892082d0210003101c1f0140b91500141400820404800707810940396885400203404010061a44204104410b0404580507006030444c41d4029000040000d8014005001c0490031540100c040c3e1109140e2107841c0e0b5400b02c90000d06510220380ca02c0c8040103140080883c503560403c8900c1c0c02124962819461010b0150100c032115608440300c5404240d030f030f07004049500c2116400030b00108026200080020b0f81d1b02000316040c0700014109580304004c404a515a501031400203484982510038036440340681c076045080c9003001c00081c10711103500c09580c80b403440000d0500c00c02800090034800c0c5500c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 842013974 1250 842012724 842012747
    0x1091a19080f100b0d232b08150306060402070f0206031807090c0f0503180f030c10050c0403020411040b1206090f060d140c12033f0403 60
    0x800312552020b5140050707444110b80d42e6100c4070549482080000c52800c0303041c4030707051a000070500481c0702d102c9aa86182004506141030f981c812441085104881d08041c24428640c1c8480062070180345100101041e00241084a0174085038244000e20340d00403444940043c011500141c0e2000685030032001e01d8440000a5403200d00030040140244612002940444445080d602e860791240751034000c45660700081c00001d076001e010404424041c9004603009410b014a60350759a1061803001e20300406125080701036003020490521002040101140507400a54180500e281c600760542d894000e51001074030468071511499035286812084601414590841030b41c0c5030104040d4200c40402622041c2c00703482c0d944000741e41f41e02c0c11170300d15000380402010000e00d0000754403003540324041d01407021964000d00c1040d42c101d54841d000003405902034000b0755210200084d82c6418640c00030710703021002d100d0b0760440e60000a0024001031541404021080356241d60400b11250f00036130 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 842015224 1250 842013974 842013989
    0x621020318010e070b0414040e030712120606050d050406060806010f06020d0c0807020910051905100f0c03110c06040303030f05010b040815190204030c080601091a19 73
    0x5000e400031a103504440301121401c000d00c0260684204166119540e215805c2c0700c00041c0700c14802c0902100e011600a0001000800c420454502075400c40c0c0c0000c20403204007081d1480301e102c1c0c0350062412100d50350505000c01c0f00c1d44c50280701820601c1426036040d0440c0d80e4200140402c907640d840400940b00d0441102c00b01e60311192042d0036450103006800143c03040703420981d040c6215620444082d688807010508012a80e420710410000c003030019030320a020b1600228140c1c50b5011540c2d051010056403c200b103140409200e88144e1480d9176400f0400030754040e90941c4d401c204c503540310f03590600d004000002e2046620341006081d581c200d9114800050001c14954150070404110944203810840c5036602c0c00d40d11a10302c21441224600c1d0030031b030030700d028060391408034660050380b10410002c600c01041130a01240c0c031940003207508040152080c13200d1807041140c1805050542000c103d0420400b6529405440c0a82841d100d154101c40185460f0241080b0100500c0c41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 842016474 1250 842015224 842015227
    0x40021c150605250f0503270f0d0203010f1a090f040b0f0406060e0106050301171c030911091e0106020f031207020a06050a020a0e0607080405061e0430050601062102 72
    0x40d0700e1718940f6030380040c00280c0c0418003c1842c464240071082001110900100000d65412180092144464803500c00780d906560729501034102d48201d00904610707031010f0000b40c45100c20710081040c0c0080150002c2c0b80d6903050010000090b40d10a102d5801c07580e510400b41b040d98452a0490252049030803e00c86184180d00005100b0741201c0558181d03a80222402c0011180c0080242c4d40e045d00b40c0c0010400d50f0342011048118007aa00c0b4040c582d000d07040c100800f060305030115504400c2660942d4401c10030b002d103409401c0c810300c81c043c0501481d04c05049104c0903080903640d203001d81112100030130004400300350160b008100e8080c0140c0e00c00000e110078a018540100213411403d040e0011521311804001e8902c0c0400490304013660028540e4145400d000a111154201c1070322041d10800c011040125400e030300020304006d001c00d01c0f2124115000281440d103c1c0c0e18043d003c07a2442c0341c100d10070001000490310905480d19450044101c0030418110000c1180c0e249126695920 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 842017724 1250 842016474 842016503
    0x605090307060f1406030619050703110c07081203010b030109020a1218170a021005060303040f1707050a1202040b0621011440021c15060525 62
    0xf107420107200c0c59240541c4600550700c580c213142c1c40798001c1307602100a000e51060741211050540c8400d402c0b452515001a54170138540c030640250340000c1480e0304d217602a040410400f00b0400070707880300f402d400c00c82e41d0440d4584401c8004500044c05040e00490300400d019030b020344030342402e840201d50180e080c004070348003110b002c5440052500c1680d80e02a1130b09042401601e03001128540003103903004044e01c140401c980e20041201802c62503060000700700c00644014007040351000340003035001c01c0d016082c03041c040c070340740000c65400140104601c08003009050340303070f0016a45040d011b60300891103076072050010f0841c0c03051440c0c840018618a94130491117905101c00c5040e03890004032043c0f44188281080800414200781d64081c007a04000e988101c10100500c4a82842000850791100301da8409001660004200100d002d052045100140101402512048824102500c003080d04002000786688034421458584040244c69040d03a400d5980d1150b54064004800103641c02 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 842018974 1250 842017724 842017751
    0x708040605070b0f0621010902060c0303010609080105040c121a130201020105091504030c08040f0311040b040e0d0e130204091409010605100e01021608060a180c03060509030706 78
    0x401501d0240c40b500c0703100707000841544200300d000e4001c10004160144001d286c20960100d40d07031482c40151155280d0080200507100c0078090590b404e50311000e19140c0d0b04003034000303151102c1d0341c1c0130400f030780c0c10302003400040b6140500200a449102008400341000785c10070902c00844001400d192034641020040c80124544002100038400d90081c00107032207800b06c02e035450562904a001040500000c0740c006402035600e0301c030300c1d442220340c03900302603482c0c0c2c840a0501e03180c1d00a544091000700078a4052078188102c44503c8001c03a4200320008035102019504e14203048c002d41441194884074401c2e6541500c1c080b903410390004255500c68440c0140009400c00907100303045800c0a40100310100e9040c0110000c0d03039005040340303040280c4a002250503038810311800c0c0c19800741c00100190032300d407030b1a00c01c042c1944000610745030030052040c1c4100e80412680c00d155850307010313180c0002042880050100c03074100701c01003401d0301d034503103c0390441c1706a0000425030341c40e022000c01d440 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 842020224 1250 842018974 842018977
    0xf0b10030b03071215051003151d0f0d05130302031207051218100509030109110a0501051309051510080103110f0607060e0309120c310c050708040605 66
    0x500b903080c0c4141554520340d00300c0141052100402900c45414000c040010395805a035116a400607098102540c0f03440d001200304050190105854544501e50001e5042d140f400349201c003d00000e06809458103051516505035140d408100400000c540812903080c00c80f0700061038008090b14908040030018841c01e070700c004411107450040200c41e02d02d4113000b83c00d444c18142c1e5800d5010380d43d1010020000458542c9107200c045c410305011700011900d0034803c1010b401e00c18074142c5903604101040200320540c55101504120080001800e0340d4050b60b1080221040c82a0109058850084010081801215954024144090f15121039034400350150407030340070b00034480c24407119000780001c01032222041e9401190802030000086c0d0380b43c1c003440741318007402c05030b0741400708200004d00300313940c0c490001009074050038103d50301d80340525a51000d4288520381d4010703807044c04600c0000c098040c0e00841e691369908642909180121f044503052948404a580d84070344501d009440e6 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 842021474 1250 842020224 842020241
    0x4021504060306170304120602070201170f060108010e06060d051b0f0a030b030d080c3603100c1b0f080f07050d02010b0328050706030506090a060e06040f0b1003 71
    0x90350385131200c800f6407201108540555210b140e900505c2d1449071610406035228030412410000901d01d084840481d40d000c40740110f035211510342ca20304140d0001072101c81c040e0003e070000003800c0244441903079130380e0898001e400207081c0450b46a80c0c1c490358440d00c226a280451041200054a14480110a000b0000f21060343ca04000c2d45d485101410303910949109508040b034401004580c4240c02e103030240c9015002500d0b0808601c00ca3341100040d944001c0c3c08801e04025400110341915007845141d141d071510f008100804444c1d64001080041200000009902c40c4804101440000e0380b06005294210325000c0d640e10303200002d1035041e03124038000d8030f050040100c5201304034410b02030355680c6000140201003d00410500040701c3e81c0780341c100210000c4103810b140000f007003840070400911980e20300040e036140c14014442e0070003000b441c640c00246007100901c01c2c45440200107800c20001e54000030814003900100e80107010f851422070f804900185400340c01903054109800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 842022724 1250 842021474 842021489
    0x21030c120316020a050d110a060e0601140904021f05070b07082d06010e03010b04050406090209010503031303061d0f0616030c020303010510051309020d0501210b04021504060306 78
    0x2c04028018201d840f00d80c0288010100d410484902d05410304c542e20307144110700c121044c3d41c51050b482e81d84008039032488440c1f4125801c4400104040c9072401403088002c80c081d41c031203040c0d20301940025a016a0f40c1040c81d48203207030a9131042c48074401c0d01502d12244e07115108005608004c0300c060720728181281d22805000d00304440344082c1d01201c00003440380318507151340205c50710750800644491409821035a0107669a41c40f0003a03650300d5008880c0507038001c500c001801c030300303a006204c100c06058011502030303402003011040d5004100415401c403900a14002a01012036041200000c2105800c00c0d981c42100300d404201200400c155018050110f01809200404103090f4141d551003c214005a0000d100400490400c80b19102d0340500c40e10b443e83c031382038121040900840c0d980d008801819804118140ca140c1203118950140c4a044a95291504103807003182c0c01b062440f00040110103010080340854860b032090f1901d11050600e40c9031669103400d802001080c0c6031007200d4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 842023974 1250 842022724 842022751
    0x1805030c0d1b02120c0409060f11040303051602180903190f1d040f0216122307060905010c03020a12050c2d0304081206090621030c1203 60
    0x852442c09190855070b075540c0b00d84015507401c100d400300000c0e04040009029a8050700300c0c1d020090740ca03489880c01c4070344101400242007050400c604201d0b9030385446c1c3e104006040000788003090700070050b0b54041d800c0c0031a22803541c1c03140c40811a1070815401c401c00c04010401400002400031024001294000e840e01070300c0c004e61078080340c0003180b80c04100c000ca01c00010b07182030b803400c0600302c0e841010054004566051503c000078100e070700480c010a04003040e08410b4042060108070b150401490f071820700040444d25602c0b4441c15003110003000c040d000081c22104010036a00542d0806810200810084103485005030103903021101800004090303081c00c030406c0d04248551401804004400d500f884049041a24491001541005400e80751280411069075010081d8803c0d803044401e503440702010751500360b030180003074180e0748142915020055a501c40038184460320b015240320b848000c40b40b080306411480303080e15210b8240100030b060344004140c2300043d4016a441c00280 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 842025224 1250 842023974 842023993
    0xc1218010c050c160302130e1e0706020d0c0c0509042303040f05030304031a071101061202010f050a0c03030b060c241008030a12181406070309050c040f1805030c 71
    0x4002038085e0000a41c0f140300700412450020b180c2e0720292032490840101e4051304800006d9031084e5104690001076031740440b10501c00c20b030341844404c5962066040000d0300c1441540c030f0050010b00e078000c050081801000003000d105252807000c00c02c82d00c3c110001506100d0745117447c4c403a4018090b40c2c25082c400000010b01e0304000044604680c0c100c3c03100c0394003000c130607010641c00c1030182030202000654417800311139102c00c0c482c0d20018221103080c800d0b000c1c00c920014041000c19410300d03081c4903060001030160780d0030040e000f280c00c0c0e00d07140000346080d0b00e100140c010300030180850000d100700a001c003040d01003c903034001da500000742d1044e001e81d510000181d001d0528008e546d501e80050150552042c01142d041040510805000c1103100754080c8014400d002c5810903205003850203c040c5079001d040c80002c1e000f4403503103010701c00901152140780c0d50b48140311a01e80290796400c1101035805550344030070000384120040c20008242030400554940018840c001c060080b078bc0d28 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 842026474 1250 842025224 842025253
    0xa0501020c06030a090c0f080303340e03030f04170c0f220204180f0b030705030c0910090603050d08010b0301050109030b0603010912030c030b090c1218010c050c 71
    0x2649007820000c040350303d0360780c4000760300c00075002c07641040b112143c031228080b80c03045825891030041e000b800300442c0c407850006810024038402100e60a0001031404450b800f03000342205402c01e070481414114080b45a1030302191a5100307007100594468000300c2c020480c48081110009080c01010846588070510401c000710355004800043e4440e1450761081c0302c04126410403040c2040c0c0071401810281d4900f032644011140c2c1414461595880a0040d9201e09503c143c0c04612001d900034015141010042956000c1c00080144116102e60020780d00010b514181030241c11419800d01030b040d940e00e0501d0755440380329218000303ea0340c3c80000c601201000146e904a400c141d40300c01c141031664441d0800d92034041e000c10b0f095500d8019042c00715803100c80b80020704600b035800048600700000f0082c11140c010158a10640c5070000b0300011034200b006451862008012985064640701000c1d0001c00c01c0404110240d400c1c5a0314042c120340110180a56480c040e0540b80c103412041071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 842027724 1250 842026474 842026483
    0x170609030a0905010f0c120c0201120b100e060403050d18090506061b030d090c090e1c1b120c061b1403150909070f0501020f150709051206060a050102 66
    0x70200000384101004100707540c400d8003e410380200d01c0c2442d5007a5103d5440c0c4002808607a25400d010403283c292460440d46d12500c2c0d02d0100d20080810002806448001820f10b44901c042c0e4003085441101c124060f0382e00000c940007560300c074040310b41340d074040303c0094100c5480010907410303295004400503100c00c460064a201d400024007132860030030294100314a140345c64418409070700c0240200700015005124111015010702110904285005030160554840380ca089a45070090b4401584040f91091620103102e050308000542c1010742044401c0c98103628005440346c3c160039100203065411124807490f440c02035005000058003681003000c0603140e0032440000440c0c094004a200c9054005160414039042c84000340800034070010340915000d64100f1216080508200041c90301041c0c1c02001700800e0000e8485e103001042c02c181c440f65060303001c0910103038140000311014825074050000d0100102080d0704000540b00e102c2c8e9620701242c01074012840b01e40b01080a600005 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 842028974 1250 842027724 842027737
    0x103060b03240910150507050d0815120703020d05010209061b0d0e010c0311031314031507051801030605041410080303090a06020f0c010c080f0f010509010605180a17060903 76
    0x10301c2e028444c0d203001203481341d420800048000b000802d11400000980610100700041c2465440c00c0c254142002008050f1906c501f041d4803850703418401440f0451301291070001c80381c040303405580d00f82040c24003c0c0a44910b907900d0350700c1100007030010f61030103030304250781441d03a000c0c02103480840c10f0100984152021071402070210301c0d80c5c0080c0000038031518006250541c61002e49051071404286c015202c07090760000c44003001501a11044e82c102004005d280a910104080c640e04222401134018440d42170340741000440112244900e900a4108000800024000704039581044140c042444015215070042c0e807290580066401c00c000250ba00030400070f0098290002c190342e9900003540860200002c528040c414464424028070644c011503180742c44420301c600d81010344c001c01d804001c06280a40c500303800148040c3d00d520030250b05484a600301643c0e140da015298642c0105160b0425601401c0c0400206040300c00d0715000c0c41500e8500100d0f20a80c90703581d221526802940c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 842030224 1250 842028974 842028991
    0x11010606090e04030905100929071e05030d060e1812071103030a03050106020708070b0a030507210b0301230a0c1e1d01050901090e060103060b032409 66
    0x1c10500ca01d801001c0750b190464030a050001200f5914404103850070080c1005001140b58103404101900d0303400300926010f004801d000c44030f0b90661841c9040c40c01a090090a07101d041e0744070084020801e40c81400e40b40c0c100013229200c6410803c01000392142d40a415100b01800001c90342f03913034100c40040300300401640a45200d5031000324242c055000303a64107460b1103031010030605140d00c0920042482e68826074000c01c0940c1081c801074913100c92644002c0c5035500a5508000148400382681c907007034410300d004903a544810000700c840300e501000c100542403c0446c454484d0f10b143e4070801d20303218107800a00000000c2884801d40c8038100c058038641405070030000f0804d40c80e0383e008900c440b00505210b842c00328000e001401c2000d01c0700308400030038540441801c580401285608180c8130900c1e06e87d1800d0826070001f40303050041d00c0307010100e42601002c0780081e802a04444054030030683c403292249002080e4903c6100156003111181800307028046050620b6243c19104807800b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 842031474 1250 842030224 842030237
    0x412020a0c1a04050a03060518211c020a0906021b0d020d0201140d021e032509120c18050105060412030201151502100e10110409020a0503040311010606 67
    0x14007a041d0000e54a240c1000b11402c03041102080325a071350440d06000e14018500003c0c10b00d000c2007516094809241281c01c0c82e41b142c041800303a41c481502e022440c000c00030f8095181c2c120a0303140212850346a0000750702a0005c1014083c60768042c410310120b400d00e07400c0300d021006040680070310001c2c40e010f85400032001803400025041c4509080c045510600d440c1c0c001c0010201d14036041e4100d402610b40700361f000905c0034030b151460340c401c001c02c1d0391000006140d4103011000e4100394007444400d0040c031440700c0c3c0702d50303c0c6409451100020a40907220b000d007401c15141003400700d0381c06c1c060380100e80b60080961989000714490f15041c6c6d48080c211a1901d03042081c0c0752018019080201c045649951194092034041135981c0c0040c011000440202c0046902c0603080c0f00b10f031014a81e90314500b88080e40d407a480094907181c21615000000b50312142c0c10321000092082d600702041d00da00021300b02e07002981c0f010085104501a5880903d410203165403a800ea50b01c521410b800070300d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 842032724 1250 842031474 842031479
    0x7060306080d18030b1015050a27030c12060f05060102071208160f06050601020d081b0903030f04051c120807030216050d0f1e050705070f0e0412020a0c 67
    0x34003103c5810b8000c424004500c1d555956400180420450b402070039800340e450100b00c4d0b8403032040d1022080d846400d1050909030108002044007a0100c80c0c071003440064034400034401c441c800001c0265412a4142c0e01158440b1404040308114100c2116194a42041c0c0d4910000e00c0c4510b50080308160702030510a480c02100c0218616039010031703101d00d8000c021880c601c2002c0301111004a1049501000041850500000320380000309443c0c1950003150b141c44186074051180c0c2c2c0d102d054040c81240b2100b14041401890082801007501403000042c10110740c0b8102d03018004440003100ca43d10403070341da2818401460010003004040340441c40c40d56400c00d0084098940c00720380351500500788498840820540000308001f1f070f41300d030001e501035204198022291111401f4908081301440d01c409001040c640d45809050104a40400d01c0810480c003408140b00408280c8404000c0540302c1c0c1e05503200c140203031401c880107120300b480801d0150000c16200309090700003955500403803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 842033974 1250 842032724 842032727
    0x3330405030708030c04080303160f18050405130605040503030a0b0d05060f180a060902101701180e2509061d0711030a0509040b030625020307140d0207060306080d 72
    0x4c00250174000000b40600c00442c0d5003104201440c4a92600c0048200d4007600705000340c003588480b442d4600708102c0340300031020400101c241d5803c0f80d44c166000189680c450a440b03025001781000240341a0409081c8070030b101001004c0c5009500c2c9480801c180ca0ba210704200c00b51061010007071031a040500001e010b10501318500e03070b001d000350200d0003c03042c0700120306040000c00d5008503100c90340c60407004190705000c2980021000c0c103003018108501c40d07010080041c1030510030340103000c8140c1440410420305030003100044a030b200481d03e428070007600c041361003414501c250100a0039882c00090018060141004840d160014070210800400100c0007541d401000e03c001e10420381480c0c105203808000401c2c0c4008146d40b8540c42c1c0b581801003000307a4001c0713100c46220364407204c00e20090702540703890401e940c010800c1500702d05520b80b0f002c4c2d0540c0907583c0c0113010200b03121820710316440e0205000c1044500d5a090b0f520f1107499103400d800701e03050350084402c00e41c805201c805205 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 842035224 1250 842033974 842033977
    0x702010e01350a23130c0b07140c0310090f020a030c14030102160605090f030c0309030708150105090711030a120f09110d0f0b181608060609040f0203330405030708 72
    0x94580c250080660741603480da0181448250701921000c1000520707841807000c40411255601c40c027401074041400034a00003580c841d02030311110303452956841660200040d0f256003041c0e155014010344405641e80c00c104036234103290300c01d103400c1440d00100d80c1e04038501031080b42d82000ca1000000072201080c5c58000c000c0c0001010700b0440d1048801c0c820802800700080c1000d1003566006541c1e410040e801d16003002c10740e51241039540d01440d0120702c0c03c0d00b01d05140341514010b807048807081e036481c04210b07070340f1001290180b054080001c0d0840110307480018403000d840415000d100c269541c07500d80c0f040302c50b4840b024080c15448503400c0b400e440e00042c00ca100f24091405a12110a103031a14180e180303090310600203003084c0704203e03201c807001846590004002d0040c4a051249003134411034807400700901c407612400c601c00000d030400142c00100c01000c1d80140c00c0340d113140b002c103042e0100401034070b03a145040740b8140c8840d10300020b04000e4520540d8824050340c20200790340c0c2c802140703 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 842036474 1250 842035224 842035231
    0x6030612060e101e11090a030828020109061a0f01050315130605150c250816050a080718020901020102070b1306050f0106050702010e01350a23 63
    0x80340a855540c1c01c40c0082c2d4010650b4072244c500b0680c03591407045044100f1942a401c1c0348185080911109065a80354601c08040340c1d0011180c07650390003c1402011903110070701440b58501088070300804c94036415400451440c1c41050100b00100301a408038040f070207920314481e40a2119051550107520840285800012025501c0c1d14003205030009044072002140f00c28446640e513908100e5460000454070a24607a904000d03c0c00407040c100c1c1c1e480302d2103000c11705001c0014050204000191000c100020300003034003030340c02c2c28881000011884c0308034481e06124100e410300220314107001103104001c0321104003200c0c2c011000f008103000650050f001c814199582400101d01003480b6203402407003844003502244000d059441c00c541152405804c95481000383c81c014803480d40c0060442e8200d9409080503906070300311000480d0b038a200200c140707030340c12082c40c0c500c0145582c0b100c10020b0841003407181c0b1490382c2c8100541d4200e0b6001000140f61141e661100c0c0d0701c9001c03080e0450342 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 842037724 1250 842036474 842036501
    0x120207021f020709060b0c06070e0102100b0f2101150b090904060f0912080705030105090402090613110a09050607030c150b061c0e16091a0409080c070603061206 71
    0x2c900d0384da4011441224011392050284841c0000e40c00160340d024480c081d88031141e41084048100d1510000795240381c0042102c44059a1b00140750755680c60b403040000f000700c010002c240d00b00f80f810414190354955090310504d50300740720b04015581c0e190010501034440301c1c0c00d03443c00c00e4009401c11040240103001a94020f654201b801c0d1540c2c22030059104003401401c1030400000003240042010500514400402c00140014021640e49801c129005901203031704d0881c985602001804408095075002c2c10185442c281200c0c4403402e80203440d91260325103441204c5952181400940d10076024024000b5040003005c00020764901d0a254002e80e080d80c1c0060841400c0011800070761240c0706909402442c0c028865480d13600d03002c1d5403004040d800191001e061000305100050200780240d480d069180d13101c05158050f2403841c2040c6980c0103006006601d03050820091960007070702e459509020700c0001056150080c0a5030044902594015064440720344522008040c0428940d1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 842038974 1250 842037724 842037733
    0x9090c10030209030657131a030615090a080d0e060315090907030b0106090905091c050307050d1d0f0d092105010207060e06070f020c1c0c060f120207021f02 69
    0x6039040c03206138207101b240055040a56510040d20781c0e51000c451503882030300000900d402450428444806498004070203945c203042171f1801d4024030106026804001e45c2001c5080344c002102d85001581001c00d102948401c00d02b54000c600b40595440110340c14043d0f01007400c1408080d0a100c40001c0e030040844e000d9510080c0c4a039100c060509080c1d00c24000210a541e0500140145100d41a0045820740090508006d030058801d203c0749158a01c0003401008000520032901403011030300c9003150310408000785506441c1c1c29101c06184484200f06100f010540703250f050700003444801e9007495440311080d2503d8000010504a0b00b000718510721200c05050364002102400030b0311056124560204d80310414005091800b500245150200100020512809900407400d004051401d40c0c110b42c2c00c0c060040c103c507082c0816200146402511807001036542e81c80040040d41008940c0c65850202d0484030344400c0e8080c041020b036004065054010200c683e60000d02e40d151407900548 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 842040224 1250 842038974 842039101
    0x1020f070224030c090102010b01110c01031a030a0602070b2d090a0c180f02190c260c070e040305120a0e0105130c1d040209090c100302090306 63
    0x380c050f81c10907282c6407161003010810354920742e028056030f80000801c0c0b8041d0495540e400c07001c0d13921a4007428041c10301d9075030880507031200b0b84211003852504025080b905560001c0c03912034005d40c8048800d4804260034070200704a24021102141109080c00880380b00319407140307403a98484006010005117203d004038080001e00603007117020052052218908550208a041c2d40542d00341c002d0080c03031035104100c42010150440110b04100c1151b14000c503c008a900c0c16603e0365402250b8000e94000748440c25010318016070060952078281004d5070981955094151310f03a200594008012070405c2c80942d01c00c07100700b80d416074070038102200440c5e8480400451421900251069056008100030705c00500c440160b11030000d00100190301020088900503040841d000b5200074414802c1e50007003006203e00700080001e11707038004e100b103d09110032900030700254851a409130090140b50000344443d07004070041603c4883d8031039003a440d031004254045190b050740340440310744211035185 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 842041474 1250 842040224 842040289
    0x2040903080106020f060c0a2604050a0c09060315020702130e030306040606020303060a05060f07082b05190b040e1f140403050403120e0603091005060301020f0702 72
    0x620045034001c0d140c40c0c101d9418180c0c001d0904052031070b01a07082d4000410b000101c80050111030001f5954030f0034096049068014107100324043c291800c44409600500080c03000228100500320311400365103401d16034403914001607070a41d110140a000041c10340351070800700ca40041c80d01c6840140f414030a080c0b01100542182c2c9024007008239a400801041044c4c14244162006408103000660840c5404000261043d83c107000721400f412001c180c002021032804283e40000b075020b44e42540324401060310540260042030881601c0481a18104549005228282c06400940751590840c461468070718050400924203076001960740c2148502090f0034055081d03800380031440303004007551800c15602602d03126080d415000076001c050000107a0461304603803c9030390140003415940e50403032094498045410f591900007000008102000f0000b244490a030100403e040016864403402c0c94201c4c000c2c15039150200c44200052005850070740c0300c0e04202003904000400b070306490100e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 842042724 1250 842041474 842041481
    0x8010f03031b060e0a0507080c18010308070201140406020309030d0309030c320109110a08031b070b03010909050f07230a03080c0d0206073902040e0a051501080d08090102070204 78
    0xa55894000c080244230404050003100a401422248000c40c1d24668030380841c0c00c10180f0004021000000d81c400459000b10803400e5030140907100b0f240c486507190030280d12a0302280c001c920900420b203140581c54007920907030b1041d80d0540d4500310a201155100c280d00d004207840c001c89109103440705903900c0114641e200c0c0a8081030000f00710401d851070044100d41c809404ca80c07051103900001d004c61000041641c0c4150b0400007012044130389007107014240641504000c20400e4000000308111a4513001010b03100d201c2c3c1e0403141030a10058955884000c18000c0245001d2148019500e040301180c40180200005101070300c1c540d900d5072100201e51065054000c030750090741c41d000c0c0058040c08031560042c45404e10010502c0c81a05d5844d0b407240f480d068820403a0f07407444403032001c0a5121410b100700c1e4040d108214000f80182c000c2c0c1d81d15030000c0201c4040c0300c0c034510312040c945041e0400341210b0b111002040782a81d1034a090740c880c1d03401007210348159420702074400035966500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 842043974 1250 842042724 842042743
    0x1306200102030c0403031202030c03160309290912030105040f0b030a030c020310020301050d060207050c09071d01020c0d021203131d160e0f031504050102030708010f03031b060e 78
    0x90b0366990703580b85d4a0058801075105e0180500c0300d10600400040742401021030b13030700c13080f000304564a02c00c0303a032015001044d901d00060044150004020384000056500d5100c840403485002c085a48408582d0b07603404005241c0c1d0300001040c00104a1402c01e41c00c69a450882280041802e88a500c00700e85007043d1454240d00285401c9900019810103122801e48405400015455581044040744080500c64001081164002620030600900b80f000b083c028100600c0c4c844181011540104082c13000c400c6401c8441c03068030322611540c00010802c92064001d00041003007101c9400308105d1002c9032034840002d00040040480786c40641998a001e012400941181510001241c440c8e03800f0081c0b441102d01c1b038202c034900c100c42d0810080b072040714044400d45692805000402d080240102d5208001c41524050000700306041d000b071442020669240142a03a90f8540b038400610b00d84400b5020400700400c403200d003203240141c0c481d0035000b00404550400d03d030740ca203490304e503051 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 842045224 1250 842043974 842043991
    0x30e13021c1d071202061917220807060624030f020313061104050315010518010303050f1317060601021e0309010c021810060f05130620010203 63
    0x8262800000034415182c580036020010301858a00180140d6128002e0003240954122148144110b6031450f048070001d4031103540c000c44005010b40042c0c1402d6201c17144900c10202140091050080041880a08220080f210020700001e07190750500c3e41c00f000302640e01c1d07600c80d400810283c0311624a11251900542c90040f10800440700a088940c04249040114010418010381d82900c840241c4160f030064400101505440d40c0d03c1d90520507a03020940500803a405008128160704500e4120340c000d5450305603006ea0b1740075599414000b400020003098050090100c5c42032000b0180c86100354080b040000306440700d8a403c801c0d405101d00030440d51020b4104856940e0500c514400400a100314150902c00c01b45c42503124001c0807440c9041180581d01f20f010340d61010250061514561207194040c1440c0200105039100c5024442c081410f20058200982c81102124288140c0d01c41100c051400c0c00700488060041b00e44d03c200b98028500e000e06881020b1000754010600d0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 842046474 1250 842045224 842045257
    0x9010e0a1502100e15040305280c0b010909030c0807050703020303040306020c010b04150b1809090d020f0606060301120f0b0115020d090308030619080d0806010e120a030e1302 77
    0x30191040191402c0b036a0484c0c40e508034280300320040403541082c41c3c006605040031515540900402c51444a400c3c400210b10608080118880c1740c00c00c84a504007401110b44010985e210850034060fa100140000c001442c901601c0020a01c180301600c611445402030307031045039803500000e285070050f4105035152980040c540070041424814048110030980302031220180404410f105620107105011000c200001c522400c1e91603007e40305000c41009001c9000c1c1e00b032143d01e50707564010a54040015200c1c514000c000c2d03038400900d4512444004141d40c0c03441c0e00704112a034121201c5d803003c40d244075064440b0b60024100c0040179010741120b2085da0f13200401080003e1900303480c00320200620001b0001071004c28a00c50032254811019640070041880ba0703542503400746000ea02150b158060300301c52809040e805401d490242c07401340e0307a40c502130401d04100004081c0e000c0154a1a50080c0180c50002e03001e03903440c1d0401d0100030284035410b0f00c50401034040e07038003040100000d01c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 842047724 1250 842046474 842046493
    0x51e0108031207020c01081b0909011206060501021204090b0a03060c0c0507050f0a17070f150e04020306091302010e030d02011d0d1403090703080712030b060306030309010e0a1502 79
    0x800d002550f00071102d10080c4806648240007801d000e90180440c581d9610004400c0b10b03202d01c05046907440003000d401c0034201c0d0307034074004030b121401503103011600c0c2410442d002889610006010f111280d41d460020301e0546403d8040006124000840e508030b4050b580001c08900345d84900050814103440c2e410240420b481c050741003a00a0300071a2156290368001d4040d515804819016241c0c02d221402c1d0084030011114500314650f800300400304951030021640d2154407010700186d81c0a40c540c00034004090b400c00091b070000b16640f58100c801040000c56030340b40e00018844407401810700115000e10440403c2c03c1100040d410805170b0f440d00402c0101240d01e0000c2102880400040e044459201c0c800410304d49124908444024011020509a01080c007504000b160b00c910501d646e40382ca4900480c03d6102082240046864400342950504000045900c00e05008018520b000c0403403005603901c5d05030004035904800c0c2039001250003081c2d0700c0c3c000e403407046c40c3c6c00030103851030b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 842048974 1250 842047724 842047747
    0x16181e0902071a072c0f060a020f0c040203011401030c030f2309030901052704091103010513021f11060a0605132f1215030f0604020d020103051e010803 67
    0x280c003c1c010070100072100160915005c1410710190f2010b200180300d0440040c0c81000031a0780c0181c451040c0d000c400042c0340c0d42200c1d00003035001504c45410f0f0030750f2040068082000124002403181758103400e0341103498000c66110b0340c00705046146500300044d54580c00207000e0b0484511080e80112121001080561039603804421070f0312030301903401180340c1085440002c240340a100c0c984400c8200d003403101c0a030f18201c0084103204150261003000501d01702d041c100e0a80200c02d01881c000e520307120101340000040705980f810315030080d1a040342102c001d40800d21030401c41c007035107040003a4a258036400c5041448014081c0c40c5643c00401c4040c1898100310361805201c03200074186191400104240569074000903000c1c1c030b42c08024581e00c1c7c0c481a00d5203180b0075103010030b4012240004012900102c91030b12261385209a0031501c0c4082e0a100c020f640e42025034010354451500d0558400540c4250801903110300c0180700c502d0101c500c01120612424203030004c0740e56030004500240c40a = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 842050224 1250 842048974 842049023
    0x21e0a020c03010203040f08090112050705030f0c030423010f02161109041a06040b0d050a0507080312130203030912030405130c08071206170616181e090207 69
    0x2610124001c6142d400c6c26661203035818211600100940004100159681e00030000112400c12220091040b8600b0303500003002c5070300072100c40c00e40880100c0882c00c00b8030b0800c01d0742c0c13046500c180004500b07c04c2000c00c036240b20740401c80840d251349510f0f01d40c4c10064217001401d902200e0081059003510701e441d141800c20214440d55014032240300803c0041822016121405454075050640585441d00403901400300411459045070f280740d6a0001c100d00080c1e0099414021340940b80d4454642180e41e46a00c41d4007020700d071403400788000c40e602404264039507800c58401000c59103403105c1e40000c10660ba00320741030310510f600b02240070031050a2201c05111305200841041040c1c0401e0b94000e80814400303040340042000b80c0e0f10f2240100320903030040303000d014030440d0b0040e00001789110998a81c01100c1d099010b0660907003000702c1074082c0f0300c0c10818034401003201004a0900780307a503554001c1d1204203444114030f084002042a0705100410581c3d00408004120210710303482800c02 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 842051474 1250 842050224 842050243
    0x612241b091003050702070e130b0f06100e0303190207090c14070b0406090203030d0b040e0601030f080708040308040f0503150c18190e190b030a030c06021e0a02 71
    0x199010041100260b542d1152900400360b24280081c254071020340c01c81c0340a00d90740000d0302448641003032002122002c80113040251027000c0785040381d41d400070500e8041030140c0c1c5030398101c50340034481082d03d030007104401041d00000c0c00b00ca040041950001d00044110784002000d070b000310340309001c0b00c00346000c0d60001c40d03071a00b00a00071079100301074000b4521a415001d03146483d2900820304102880c0c00103040f154000b0212510b4102da41c940783c00030311018100a00c01c40c94205080104800452610b040740e8222940394542d51094640341040c0d8440c801c2240c40d42400c02010000480080181004c0c2800c92102040c860421003494034000b2113040c04444842a0030400c8100c0714800100e0f00540c0140f009070781d2415401c0b010410b1841500d410040d001480c2b0b80104001c000005002d00c03a40070040080c0d020500200c2c030800304d443d00f99400d50103400541400022a00400c00000440d10518006240403541c89041c842e50125030700301c1034101400101001c441d0b5042010104 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 842052724 1250 842051474 842051521
    0x30e0909030403020a061103130306051e040503030703020c1203070206040b130b07120209130b09130c15090e04151b05090d0c0b180319030206061224 66
    0x50b160443c0c00041500d42c0510a2904121440b4503100c82c015083c07090384d5040d10f41c07060039000030b41c49152240142c8421102400c004060b05940705c150f00d00c40781000c2c0619081405140b840d150808100d01035070120402540c04d129007100c19009484450003188034078641c0d40a4040350400d03250200700500050010504403035071141140c0407560201481740c0101d4070b800c0c1050121901122400030340100400a64000c449100141d0300c0c4016030010007100808076070004213651904103019600800320400342610f542c49500f401303103044042c00511182c41600f0030750342d0355980b0390f00c0c420501011507080721060040c2c21994180302c8d550103141840d0300c100318409004580184c00610900540b410340c0d101c0d02d60b5550150038441c20540c030f88060612000e000380d0f107864402964038a040c0e07030501c00d80644504080310000c0009081c0c4100300341e0780b40d80501150b499440c03c100102a48d88a0101180600c248840c17244900e13075051241d2050a4000c440b00785045184200d032005100384006 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 842053974 1250 842052724 842052727
    0x604020a02101e09030e10030905030f0703050405041b02010e030c0a02010806041d030408100203060a09150b18010206011508012612070212070608012709030e090903 73
    0x5a07401180b00c000700888603400061564159046140211800303110100c0c0d02d181c1082031061640c400c05170b4801d12420f036405036816848800440481d14131035000b4009030001e008005a0304030040007402268040d152483c10306490790001411500c0348003c000e443c040080390105801c1c0c080c0185001909840c002e03609001d040c4445589845c2580c800034100b0100c000003c0050355030703600c0800d00c2c1e00d201c03049418001e00e10785100c0e80e80e406401402c0d418880c040c20b4541d080214004c592089901414801040b482c114041d0050510020f4502d1910074005020410f210b19001910214480d0140052581003000c00a810036906030480801c0300c80c0d0755240c11410350013241c40c034116a02140c4404a084c0c91040281292081c8104a41680502003001200c82941005001030a0081300c14100c203406c076040c1107903102e402e4811702c404038034602c0040141c021b22100003085810b007003090124521290140c10111525064200c002c140e401001d6112070400d282d08a61181011000b035 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 842055224 1250 842053974 842053987
    0x90605180c0405210102030426040303020c10030b0414100509010f12080c070b04060311031015300b031207020907170406140702070b040e040201030914070e060402 72
    0x7004500c610700a0f80c0c0201d150501581c2544d4558034410b01c424810b500864581c00c1c50710700031003881c48a40d101c0a035400c460207a0507152000804a07401c0360750540040494031418400c0c4500c004a40400d07509143c3c0c0d5441c0c0303038003503181c81c001e0b00714510004481c280d5a18000040691080c502d030440e501038134107840180084254400c2c484291349280542109091041c908034005124074807243e00ea80c01101d200003450b07042e11010384107480080c0c609122100d002e804400983c00100c40c1e403180400d0002040041b4400078510020465151504110010089007006081070710199a50051980c0a10b16071502c001881000341d45181203007c0c1c00000800e01c03040001e0700400d00068841d03030032031b408079020600030012000c0807008410900b2103031416080c07000c0100f510009001c213000191300003c050610204200c0306488114148a08043c20002002d01c5480014070482c149582c9420810119490510406103021620001c0c4a0581001800605180301400c2a8011070061065 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 842056474 1250 842055224 842055241
    0x3030f05070e1c080403230c1f0e010915050c0c040e060106120b0a0810060f050a18020d050408190f1707120e030706060506030705190e040609060518 66
    0x83c1220325508280140a5040604003502944569800200390500441240d020f085d02d030329444900805000135074003800b60140a00580d0f211402e621106600040341804506010b441200401c0b40c040c03511500064903030555102850a01c001d601c007060b008134800c00c4041c0100841c0f0890341c8140d030240b1540482a50741c903a9424103029460500078202d072070100c054000c0c0d00001e8540e40080080c00d00c141d403414900d494a0102e90030500e02da08103140482e6002c05625524100c0c0c5014081503c41e520308240314000200110f155180e1076000c2041804401041c0100c500031800b5040065a8448103400c0c0000c0030301e221000c10a01c0702d4205c041400c81d40000c030030326400e450100144242c0c6d82d440021070318880c0da4041d190301c03645448030a50800b4000400340034080c1c4640000c01c410b0752a002008840d00044890700001101049255403544800d142d20740e0498490074421491403000300010301f50381150700a00d904a5403404200f203d4607110a49031910780764903050b07400c1414011030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 842057724 1250 842056474 842056489
    0x1306031103152205030d0501061d060306060702010306050a0e07110105060f010f110d0806040b010e03100e210a090e070914030a020604030804080624040b180403030f05070e 76
    0x140700d000061402c80b0703402d401c0807442072010a44c0181a2a80e5072586060500181420301619000a070048404440003100740031402c52908010300107402c69417540c0400115500c200002ca04040d1507100008842d200c2c11060000f401c134484c100001c0b8902488010003c20140c60320380c2c240d81c10403061181584401c860364043c61002c2c0b8094221412007882914101064405805588038801e5803594560380914003e000c0c110840c2e0a005458602c401110075042c808081ca500d40c02440600382880d903150301880700342c403148054942d64a012208016041c00030741c1d104d400044000b40301d40c0d00d41c0d480307001030000d00300800044000f420000305c0100f10a1440c050103400302c0124518038100e64080041da80c0311a402803065550325100d107008406500103106051982c4140404545002400342a1403c0c0c02c41c00c103948002d42c0d903494100000342650901e05908a81c42003900380c80399207210841c511840c06034a0215040c8200b003010022224010400750420840c130542c042c0302c1d0f0311084d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 842058974 1250 842057724 842057731
    0x915040e060d02210d031109060f0304050a0c060c0c2310030f0f0615080f0a0b0a0e1f05011806120b030f07080d051908070e130603110315 61
    0x1c0e03a04001440ba8400b0600440100b10040c3d685800030381e1140030710a000072920144c20a0b95428850b60310707040d0b0b40c3d101e02c0c020419115032002040c446000c00c0c41c11100650303480340c007803011500500c8082d01d6031281001113403c4280020710348084001441400200b11004101c1c0c2c20a041181c0000383c84944000e03034142206100c0d256014240344140d1080d00142e0115103070301c404010882c00041e1000007010785200b640889010b200580020a0080c0c80d641d10072588a240404282e4400403060700030801d00d84a40e90056030800c2c04900420340c1c1034490300c240e089941500210b5840741c28100b01840701e511290400c00081c2c4440840701c0381c0d454207402c5132258249207480440613107640e030280240d0000c158140c810011490804200011000d080720f01d640305880c10140d01c2001103800788910740c1c2d003840346030440c0c1e0600308551007030389207961016171841d10300240c00349140054117000007894035101141d168002402400300340c030340384640028220028032203600d090c2c00355040d029008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 842060224 1250 842058974 842058979
    0x905060a06122f0a030509010b010c02061e0d0b04200f0c0106080a05010207140c03030a120b09010801020c01060509060a060e01020a050307061d0f07140d060504080915040e06 77
    0x2c1d044040101c0902d168810310110030900e441d080d1003110320f0040d41d60046601680028284004680c90b80810310410320b9019040e5190000700840d034081c0409980302c11170b942d107610b07070165900c3c0c6440c0d0101c0c0603100003803054001140c000070070f5003044166100d00182c004d1000e280c4803d9446040504200c031040303c1c005050b280ca601800100074010002d0754004002030007605400000c001e019402404003e21504e13240844250303e0170141c0e1740350100280305030581d108201c410b8446000c1d500d42090414040004900101c219001c00d8101c5400e82c401030f500ea4021135011100402030045030080c0800f80c90400261502d0030000d1040e021600c100030a01243d07841c1c4a41e6640309000c0c0540d0a41c104040720f40c1d450581c81e080c001802c94031509000d00441c2c940c100081e0201103110101d490043c40204202030070440d1b5000050103052032694404071110350340000a40c0c2d401003d100345d020b00c004903181c1000b4405d102100108145102c0010302c10030080c0280c0406500c0c03181c100005 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 842061474 1250 842060224 842060231
    0xc07080f130b2b02090319051606091818050a0b0114151e16030206010b210604020405100831060902010e0406140f2211040902130905060a0612 63
    0x1207001d10005d01c01c10110350b425010700b441ba2541a02940720990b62140300700704403616aa88510500403034009402400009410104200000d04405c401100c0704240c22000042c000e003054140c040c1168212012590358020116810a008020507032600404800346039905c170381404400540c000141c3c4030700071510000441d0141e62040b888143c160348143c65485207684e101403015009022400c0c0700c1c2280148901c1c0d0000c038002607500203440003e45071440d03503c2c0416040034a211280c030010040c5c8e810540c2440001010781d0781600c00e150940641d2103030072840c00c03e201d607200d8543c0b01e54410003440d072081182004404c40303800552540c90300504002424500c0788012070b0800c24100c7d03410743c400e081c5440407605414601d00110448030450b10301a541c40c8a8003440400a0014401074510f540d000c50500b5075201c60b000001107141d10102035140c5522554048107d801152845810003500716060100c0030040c41841d402507004c1302c04801c500d00c3d00e00c000b482040c6001d03050344441d40703 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 842062724 1250 842061474 842061547
    0x5010f05012f0a0807060605010309081c0912090815150d0606050d1202010b04050903090f03030903030723010209060706020f0705010615030f230c07080f130b 70
    0x106040d12a5451005029118103d1080c2800031094100c40b1041e1582480c19100181a60191007a048203c0e07200c48101d04200c06003070f981e400c401070700c0c0500041d81d481e00c0c0070310001010744a000c085c40100b620303802d680c207040c102114039240c10308405503101c120140c144150703041100c500040e0503c0c00c940c51105604503113480d00c0541019032026402c0a0040119010055040340008a075101940204041c0f40013500f00001d5a80940300303121143c008002c04c80050402a4610303600c104041c04880c40c00c0c90020110b03103035038090002981d0b4045c2d030a10f2102480620002403241d40e40c144002d41c24200084001100c030710032200c0c0140718a500254400b4282c01310710603a400e45400070000c1150039909c4032a10b010504034102c40c00002c0c5041d000c800c041c0190310402d43d215170078031601001340200c4c40b80c0d486141d4010f82400c840d88400d0260800088011008004c42c0b4008690310b034989807285411641280180c200388207010042c09070000c83d05e40441c60740b641802c1e0f86007034001c644 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 842063974 1250 842062724 842062787
    0xc011e0e190f03231903020304030c02090c270910080d0315090c0c06052202040b04110a11150c121503161d01060912021c120305010f0501 61
    0x4000c2c21400c00705562251014401304a08042c2042ca00c00d03080081c88803001d943d04500700c0c40f0455005001c1b43c18008d02030050f0a228495551100100c11114038200f80009115001d689107940c00104203541c07204001d40d41021080c50381c01512914028500509003281c0b6a256800003041100b00341d614112000c60742c100445480c000c0040038030801000044520003480c1c1c00c0031400582d030850401c07000c13502802c10104030040c01b41c810641d80300a54130a5003000b019010401c441d0380c0c8075844003840c14608480d840140506080380c1c0780d40341070340210010f06007040200d0b403400288030ba0340010020310304105021900802d4095416680320358a24003e140404000510580c06218000316144120340781c4c043e90081e2880c3c11040c01071060b02d003e1040c5800e009008160028000301c0d0100400c80841c0d40255507184000c1c511801d08403024200101c0c1c040b05082503070341040e1045607080c03c6415109a5000d1b241d1124110070b03950500e000039104072019111740855640708160360b031880 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 842065224 1250 842063974 842063987
    0xb0306131a040609050d08060a0b070813080a0b07020c0d0b1b0c0c03011d0a02010c0305041e0501030b0306240102161203110a030c060209060c011e0e190f03 69
    0x1c1c031140000003508290411030014450310100302c60314850848031003045030080e080c0701d01c507003402030220b1982801c0002c2407042e40c0186030704491004042c004045c07810146035440002d001e1780702c000c1000940c1c506001c205080061701c844190342000c458850355440c0d20000014190704041410400d440b8448410a0f070000c030702d9010022400890204c981d4800441c40b59190b4404900038403889103d840305038801024008100410fa024081d0280154010541c0705511313070207401c05505081ea0340700302d40000655080c1010350f9004015003070109603018032030325403114416402040703140303404410103142d00910408640804507044449555a1082011a055100354007000d07040c503554100149480c18402c4040780422903600703039000d40c407030006400c50b07660740c0640d144000c111858075008000e5000b180c40c07681220041240015001d800d000e1100f01240210000d88254001d0500d002158200d0b40c0784195601f09160b50b05040303e07007601c403c000c103810021a8030000320524096612 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 842066474 1250 842065224 842065253
    0x2090f01031518141e1207031b14060703050a020310031529120303280207050a0308060118080c0f19030c09061403030a030c020c06040b0408010f0b030613 68
    0x50a4101300e04065410000c1841074640c4046250b01c2c052001c101c2265440d1401c0394000044148244203140120344510f10b14103011054080c281e0708020300741c5403841504041c54102025034010414810341961503c592179110100450441c21420106400c03c0140c00a2201420044c1181c2540c0c8030001240e0240080701d0b0f05c2c14100c40c10605108440f11000403100d6520310580312810300c0c00841101008a900c10072000128550400f00640b00b0290b15620100e28071034241d080c409400014810001004618000d48a5045a1600e07800041c461090b220f0005210880000d0130082c8001c0042c1c181040c1804941c00101888110045420315a541d0403940c0c07489442c042c00818002900e2941c015900c100505016040d1180c910365121040c00c5421500342c1d00812203407032601e02ca64070403028088070b40b06985092104900080031504650800102c4200005040000074024821840d4450942c030013488038040c1400001d0701c81c58003c1c9450815904e40c2459010403c3e00104100f4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 842067724 1250 842066474 842066483
    0x10c1104110c010504050c2b08070c030501051006020706050706021c1b1724130203010b04140a050307051c060603030e011d0a0b13050a1202090f01031518 68
    0x48501003082c840d030103000d040c1c07825035030f901400383e948000342460860a21700d960150f000400c05010010a0000030340144420389032000284440c0300011f003040800305c01140910700101d401e0500a1405a1603e0103034020703003e540c0000c0741080b000d5040401e4444080d0080700c0142c94142c4010070f6040c20400c0000b5400c0b851600c580311003000c81c0414821110390031a03079205c100f1074425600030000182612030503d001c0044440d44e2040303000c91050304c502d0001a04014000c480608071200740e1700280c001200400d0049002d1100c514204051450000d0403250781c0c22480c50030300420f07101c452a0041a01800300300c0010381010700e503103484400650b4009801c205240d0790307040007008501c07445250f0f80010401d036081140f440c036049642841c0b80000703240c0e04986280240d662000e9010410a0303501e032800072400a05a0f880c0340c007100090440544c4c41910380460310400c41400801402010700b4541e200060001c600b001c1d803541100a40400c00044d008000c000c01070f0b40046a0320000c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 842068974 1250 842067724 842067727
    0x32703060e0d02070603090206090906030a020d050d0f02010213090e03040803071a010b1c0c090e0432060c07060212190605030102071106031e070203031e0402010c110411 75
    0x4540480050351a9002d110341d4240c1d0545512100c044041d03070550f01c4c0281d070021060210601528080010a030844001012903c0540c400e41c085020f00000301419103450308015805242d06422006901c0c40800c544001c6290004240150040b8140c90141401d4195103040402d1070407010411180904480002c5a844560720701d07010960134080164050350b5020200001a019004005e81e17210540540e10a11210b00702400140200306100c502c10070400c8100e00016100151900a80507502030003a404080c0350b10301001d181442c401e8062801130070600700d41440381d1404242c180c2c00254500c3c0740b81e40c131081c1e0b0420401070301a5441c00d0281e8080541444220f4a102045c540203a0842c6c1c030901c200e41d0b4881c04c00d4201d00410801401082076601d001c80c807894031800444e403088054030b0702c3c1c219080511600800346e0044803d0405a880001800603042c14103120f14002c101f01d080380002e510f0315074002408078044450040c094660400100084d61701c2d5080020004882c04030704d0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 842070224 1250 842068974 842068991
    0x6040f080403140f1e0303042006360a180906020307030902031002160807020a09020a02030a0e03070b04090c090b0c160905280b1305040b0609010303270306 69
    0x860300c03001d0f52131100c602c42c82184050319040000355420200800c1c1000554116901c41e200c8a03004c1940c0344487c2c8184c40303200c20610403682e5050241041c07201c0961540024441c003003400f404103201000254006044000007030302c5035503603801d06081d079601111003a0040001020700e000f030054603000401080c00442041290381e0326600c1800315900860031256103001c062a003104030f10491a08502035400d40d0b0084020416140c0200815031018240441d1f03243e886191400302c0e00300360000d00060700000759130402d1650240c02c04011600480c00750034918640a04030055114600c40c03045491b4585075507600250140c100e09004040d50800681e591749000c122a03252000fa00c01e032403403150302a20120f440c50315445104d210310845005002581c1041da802c10a50304c40c146450714060f16241c0131400354407036070314105191800c900042142d003040d00d0035203c402ca0080405010308100b80040010a51144074400e1030354070b05440b9940c2c0c1440d00b0415074051400d4001405070341c200041d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 842071474 1250 842070224 842070263
    0x519060f110d0305070f0c0308150f040c180b03010506030a18050d021e01060e011a07061a090906130311190f03030b22020d020d05091b0d0506040f080403 68
    0xe403017412543e40b03025296004100030384101c0340441d03000e0001070040e00060444c1680d004014141840141040c06610102d4001410745054001200024410019210b425580c1c84c80500182a00b50070301030540d0f05000116680340001805a210b02d034403000c0f045040640c0041c00320003240c108081d41c40e07035120010065078030401c1d149c2f030903000764400c0302201e03913010103101d40803c1c0c4654858041da580d02e015002e4076500000220903400b00800c00105000a00f03511440744031482d0704940c402e0245142e8100081400300402e031504a410000400c62541c1078109400e01e8a5803600700302100e0500c03d102c4a241c009401840201078a05146044c280705030203080600071440380c2d03414020608408280306a890425412a60706440001d2020910801c4d1f006000d0104400e80010b0804c0600c214400c00c1d1801075603014a55040f841445501440340c01c08450481c10130b40781d03001d100010b40d844a5850000500c098151000019028100282e2804a400840d0000e0030a12541094401e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 842072724 1250 842071474 842071481
    0xd0c090302063105090610031b031e02120f0405030405031b0307080c0901060309050102090d080a0e0906061606020702030a031101060e1e070306081606020105010519060f110d03 78
    0x250700d07824050b01d607084045144a2640c1c00241d80002d4542409511000c0c00e00461440719401c04090544400189c1c0c5030722100100007600816568002c9041f200c640403002e941d400360120000a42d004100600c1000329000c0c08075000340700c43c41c026a140d41e071ba00308030307065008681016515001d50f0701c040d40c4102c0300d55400e48503117108400747e410041ea03134a0b403030f03136183e5031101002d400005140c01000224000e41c0f00140385030160001510f008410800504000c20040007182d203418007080f04040641e000130b07001c02048040e80c1c2c0c0d10007820a0400685039020f2200d036042c1042a00d9204400c00509405403039020381e0150442d05080d480c1d16010f010311140c4c0c01440813a41c43d004001455003410100580520040c0320000c4d032034840f004c08010207120081242d814551104800a407541c02001101c0e11901480f006049460920400a0a40744107a0040b0311481010300310307061074840f0600210440700780e03040c42c00c1d0481080b20203960011210010854070700a119820816a41580 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 842073974 1250 842072724 842072767
    0x12110a05040e01080705030a0b0a0204082407031416030e16150224060415030b10080601050312091507050c043e220602010507050705030d0c09030206 66
    0x25a207881c01e80c0c80d211102d5031000e980c42145e500d58040040c235000f0907031000c0c81580000c041e42015117040c0d00c07124050300d00900c09514541340e0402c426220310003080c107010703d0340001441c902841b2001412015940410000d030400c100d2411200c21252001d0180e800f9510700740612050314403400000e070340d0b00c06070030051203401008000055030084140c1301049102e140807200307050302c1c1044410b0b046803000400c010000ca0f0000d541e4483c021501a10164100c001e40c402c0e0000241803404450032802d10b030b01580005581e5201d40c0040c0501d5401040003906901c61490041e12004404000381160b0701d0001d900302c009000007195418810082403003c0b04c441d00b44d400b481500c035105030b05415001d00d0901d0041840c42c03103014180007000125200c03822041c0800343c2d81400800d4809110a4018135880c6400d00c0110104224494080c06480c0d4004c10f64103040d8200442c9071038007901d92050b11a0084026a20340a00280034010300f007440c044e40d0003810b40c54840c0d1090801000c91320101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 842075224 1250 842073974 842073989
    0x6010c03080c0a0c21110706050a05130e130309050f0a0509091203010303020c0108220f141204030c06020a15050709170d030f110a0e060706090308180106030c050112110a0504 77
    0x3102c043c40480000798030340448d14103960703503480c0410041e0103c44940201a4000d00b86442e0341000448070740464030b0502910407815000700104e03051401401208156014034000c2c0303520280500135945e2081030b00101c0d50180d13800003007a640d0fa0112414000c5441c42001406130120000c400e05a001604a182050070b0301c4d240c00a84461130103d01c0030040d902d4086140032a4401c1e80c00003500007001c0c404081c0704074a002d10344204004885e003082000204000300240200d010400c1c04038060360440200500e00182c4580d1420b0b031180e03240007003a498145501c50b100c6000c20005c6100380c03441c10052103c8660710855042040300719442c0c58502c0381c188006400d00c003480380c010101d44100c90340020031941035481c1206483c2e007600c0944041d009182d00c0803090100601003402405815040c0d4860303504c01c076041c0b801294840020005100c0f10301035a00d0500103100041003000c0100c1980c0090078951101c000082c010b40c00380441e0300c40010000b1b00450600401ea4101c4050401d48010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 842076474 1250 842075224 842075237
    0x607050c070b2a070b040902120f0103030503042006040e0a050603010e0c040b0a09051006080c09030307030e030313090204090c03020c10052706070806010c03080c0a0c21 75
    0x200e5120403014059518040100c0e201903036446204456050494883c018000650303618641c2c400048500d40c000d070b4001d04c102500010b880c44c005200300d854607405840e4050301000c3d5410368500030018000240010810104420341040610f41309400c0039080000a0169554a03180d04113038070341c80002d85003159454242404a000c0f850103006840305200c5040c01400c5c0f801620b010000035144005600342c01000020300490ba800e01809881d1041541d042d1101202e0300d070560040c0140002418804248018072034035520b40c0d008421288181d0701454041c0c1c05c81684000241144070303400c41c52070360f244420130009103446681c0261046036180141001000d65842c0140d059110b1700d40900d0041d004400c151540c16046d60003542c021840270a80e0350201136070006101d83d41d225070840c4c142540070400700489558440780540d0310000c2032130070800b400c0e200ea9001e0b104e090081c180300540000031954555291080480360580d40c2c010000d4007508180f4a0225030714080d4640300c8000520 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 842077724 1250 842076474 842076479
    0x4030f0204051501080c0a03060801020408150601020a1e11120601031205120a0203070e060c06061c1a0402011e0e030d0302031b030c16080a0909051b07140607050c07 73
    0xe20700f002080010040e16880c946a49010103500303142c0c05054810185503903644042200542440544040c1a03080c00920102c82d998140d00f405000080502d41150300020300c400002c2d03843d00c0c628603010520b4500b0905000e00745010040801120801030300f100300070f0007400240c0000141181240d0141e2804c0040c12803e01080b6040c0c411007406291040c0d484c40803500c00e0609074005c1d68000b402d450700c0c440000715500012400d6000c500311140710f034899403d00082c0d10f03000440c04009075025942255808942e903d40c44009101c025200c4003068038070015003564045e03120314186c40002606022100200b4501404245400901501920030140c003440300c03901901c00c5a014003c40400c0c14005450082001c065900007003201f8051102400149800b11004181030f008a1207400000d403600c615180050003440186d00040f9070754103110500841484180e0038107800d42d03000380207070f60302e6026042c03001441030061895403040c4140001c000c1500da0000c050305e00100c0304001e94900a0307 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 842078974 1250 842077724 842077741
    0x403110409020d1a151c02190e0403030510030f020d030215100e0603030c1c12050109051906051e041e060812042301020a0b0702061803040f03080f04030804030f020405 74
    0x51741c015196040180b070b158511300b00071600d03140312170706200903e20146003c03100c071034000c250301c940d02045107140c0da001440109034040c016180d1040400d01031070b080f41c2c40c40d02c91900020030668040d0185c5107812046050604c280700b590b20380d81180c0c1803110207003040744e407100b00c2e4070f0759100c0c9801000389038010480600e8040212203005480c8001046400d100d01d403840161001c3d90345000c2803220400040001c5412800307114028802860009100d00c0d02181d015103404440e40040c0c1080d14099041c03243d41e841141212000302000d0035842610348807404100282101d990a018000c0ca58103641c2800e1402d42052099a08100540348854004010a0200d01940c0a00140d009000031201c6051071141201031036007105204540c4903450030b0b1100440500c040d105500141c02c03800c1007060102d154003600081c0309482c4001c40c82e0a107410648112040f20b40002849410006960103e84200c1c406540255820103070751035072039a07240303482c43d00b07103440f030508a00440c02c0038000369070394 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 842080224 1250 842078974 842079001
    0x1090b0a0e27300405060a09080a0807061b080406020a120e0c04060e13030c0f060e010e0c0a0303170403020705091608010f0506090904051608250b0403110409020d1a 73
    0xc2c0f07004080c4504103030a0208105444e040302042c1810442e84041c00110007000300032800ca89030141e003030141d403000700d420b0440c155080c0d02c10122240f91544c512600b5254410748103917110b50400c43c01601c03640034200407100f1250454282d40b1090603c0250744107094040741249032010112001c00c59555107142444602c00c0840380c1c4585514500000302c04240186c102e0240c1178850340c28007030859001c2d6600d1049642c084c100080b184e66a21078034000da001081880d1030441c0448140203180e25580e001400c01c200300044200c1c410f02c0c100030a04142c000c10590000c1e003c002c002c0101e91400000e40885050f1542101000940b081d00000b1400d82d034913001d4003a601c000d01080e00e055295002c0c46924000608101c8080c41261408110600d80300c072080b01603d00c18010340f44840701d005511802c0c14484a03607030401002d05a0800903440071100701c5086030340c4402c0c1d00100e503c095000500924074000c0294100d16200300d640704005003404a03e008007e82000342200703442e20b44003403520 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 842081474 1250 842080224 842080303
    0x30e010e0d021005150d061a0102010b06041e08150f060a060509040203040f0803010605070203010b040e0a170c0d20060115051804111201090b0a0e27 66
    0x541c00640c0f40104a50700c0d5088207500145521202141c41c81e0a00455550001c003941501c601c2e541e003402c144150424150809100d80c24402031103c00ea60800080c3d56200d14850300c400d0061520240140f60086055480104000001c0c0c51841c12040341e03594100170211410843d071502800000e09074586a00c4580944110780d480504081c15801031200a5101400c01c0d2450700c40011000300181c101d0000394040d00042d034449032940c40520500d820741d02d5141d2441d10403820a00c00e049030f8000015007155513500041401c2e408000d83c11094010310440301d0411190140c5400052a1908441b80d100d00c10f242c40440380310b03007441c80111501c40001b8040c04494542c2d92050949840c03240005c0c00300200d007150292403845480d40020122481d204032500c0a0001041c00104000e5003c540d50041003008014811651400c0000b004a2510f00904150070091000704611100082c04448442032041e6580c11041459007060340e140d25510940491054400d41600c5030003000359038800c1c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 842082724 1250 842081474 842081477
    0xf020a0e0108010f18020d1812020106060509030c060901140310030c06021b060a02150406052205190807061e0f020405010903020f0d051b190803160309080a03030e010e0d 75
    0x40c5c442c1304c40d0b401c00694821515040360541340c0d282600e02c10410803c44034540d106004000700c0b10079802020b400d54800c2c0d807045084c0704040c020101d907514003041c1c0103c1c001c0111400e40d0703034000d02001a61940721440180710400c602208111300003545003144002d99000f02c0800020b9540c0e02412a80c13541a010540b0744004070a4040d07641c1e06001d8084e00030f60009006590030b1829000701d10f015a83e0444003a01c029480da01071090241c06882c00710300c69800703280c86180c140496220150789540100d0701850060008a003401841141d07400e980c00035601c01e0091006809039041007226180c00710310603c4842c685954401254800d02c21502191030686a141401d46183c081000d01c503031240000c3d801100c03032218200002d0040c400105020007805142c3c3c0d00000c00e00c04d00c42c080b0001c40d441c032800484000b05008520000065401d98a12074000840941c00d610381160103180d80e074040b1750700e4440c00341c00c4808c0540580110950556580007040401c0001c030010b5914810460f2240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 842083974 1250 842082724 842082749
    0x1e1e0c0112050c190917061b04030b0f040c09140906180c010c02060717030411060901120b0414071110060e060d08091c020102150402090105040f0f020a0e0108010f 72
    0x2000411381c4202e603070103640030b8104140c1e520741c1c0c2c1c3e611100c4508a00c10381c0c0450b801040400001c40c21858041100c100b441542c10306083c01d503568004040310141c500d4030100d000074000b4080051445c0d400000d48408070041c4074284e840700c0c495a416a0940d02c500d01c40c0204800907100c484040558120800c0860040450112040c01034130b0300035240c64147c1c0c11040411031070010861b40400102d0401e00c880c6c900c5c0c1d4900c0c20741800981000302c42c15041c4500d00c1040001143e82c1d20110450f604296802d0001d40c0c0c0050100050044c00d0540320310203041070940400102035002601c0b001c21100d4402603408040103841c1010460300da602035003000b0208400428890b0070106812446144201d044a18280340100020140407c145522582c0ba400e096a1800c559040c08180354880c0104041c03001f9052660005419400501540d8010740d600c004401d00800d45403c9103d04600004045566000100d402822101d1351010540411481d4000083c5008903013047c000300d03501c40302b500 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 842085224 1250 842083974 842083987
    0xc01031104120221060403120c090b030618040b01060e24030712110405121b01111006090204030501061502030a0305060111030c0129031e1e0c0112050c 67
    0x1455481e401c0e100a07a04407621900900c129004526000d1803404d240d002040d4a1800703140003450036500c82d0781c1d0b5415a042211094042d5007144244042c0c440c410801901e0b503864401280d4411a110003100c030011030a401e12050205c800c450f28140c0e0251f503140c4000ca40741d0403d1240395610690360001850808403003090300414117002d103800c40105d00d0690602080c0203603c2d026100c00c480d5901e449100040c00700b006241c50002c1540180d0448013400041e48004544c5c02a003401000c0281448441c5020000c40d8030148800000450244070412080780c982a010f40250040e002c101d030303590301e07001000ca600b04414591110310390859000714a08541094100c0140c04003502a5050104107949032000341c0e400e2003e02440b4492000015064000e050302140b050044140b00d0003d80f1000c01000041d18040b80001003c40c0d0f20402001a0000c105845e18100110a80c10420000c215000340404000b03e09000440760076030320303460400041e804442c22143c080c1c604681c4041c040014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 842086330 1106 842085224 842085239
    0xd021908030309100c0e01210617010911010309051b04090609060f1d0304030201031e02030108071e050d0213240f0e040c03080f0409020d0c020c01031104 68
    0x580100c00c101d9001078044980f244c02100c0481c04906c11900230300e03542e0803043c02080c414201c1301090400048860007010801e400b12035102d104400305c080c81d8464010420510f8009019012205e41003100301500d0110001c802d41194580500402045540c1700c3c84403480e0140c100070520f04030060181045031414040008403290140c00d001480030008150f4040c0d07035080c2400100c12050103256031030240c166507240545070001001050040c8042514411107405203000100012084a070202e40c10700d50050b80d801c03040c8241c1b10005860302c440e800403401d109103000108066080b0070005400d003200c180c3c0e04111135041e01000080107030420a401454a142107400505003641e40707018100306440302411401010400840c41190041224011712071040d0855480d02c0d454a0f5101501a050140c2d0242c0210700419805500901130690001c206440c094501400c00b0074 = true := by decide +kernel

theorem cover : BRFrame.Cov 841906474 842086330 := by
  have h0 := BRFrame.cov_init 841906474
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 841906474 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 841906474 ≤ n) (h2 : n < 842086330) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
