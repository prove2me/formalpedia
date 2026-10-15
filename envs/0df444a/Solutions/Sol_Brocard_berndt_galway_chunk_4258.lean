-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4258
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:02:10.911173+00:00
-- url     : https://prove2.me/submissions/2ae19317-c043-4ce4-bbcb-7608765c129d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 765647482 ≤ n < 765827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 765648732 1250 765647482 765647521
    0x6010507020f0d03030c0216050105090415121214031302090a1118030f070e0f1005060a030b04050109021603080c19020a05100c140d11030a0b010801120515 69
    0x141d40105400d51600400074544518441b005005080e80d4004990324041520200c4034141d54449c2018040402c200c024002d60190031503214800c0c40000c5d488400b400c210403854000d041201c103040d0305c8200034042c3d100c1c103907004440700030400400c0800c0b038007035001d08140340c0c0580383e8080c2e0f0750703a40e20014010081c0d92071040e2034000c0420501450b0a01d81a0b8070b004110507400c5c4c90614076801442a6602001d01030303c041c01040c2c01c000341b900451a504a5400b0400d100d185500c0303541c41d0f011400b640d001d9403486001a40300c0606c1d01301c81c24507011301c500521000004507d460003d1130071600201c2180401410000404c0c041003041a8103425a482401154104a09104003074000b82d0b40d840c51000454040c0509012043da14440740f05a144250403a1035644d03003c02c1e4040c5c40040e6900000e0f8045403595518041d5103400042d03070295100b0f00c00740c0f0f030000e0804034400014045540c140e000c4401400038064010010300e02250071040b1406c04410002c441d22030404140d00d1201c03c05 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 765649982 1250 765648732 765648739
    0x130207030e0603150310140601081e040b0114011e0e0607080d0509100b0f0111150708010519050a0e041401151403030a0f05030c0708040801050601110d020606010507020f 75
    0xc140890040b122454140c541812000c503442c450942440300151084070150b401000c0c7e460f40091159401058170301d500a420800702c111280c00c190590300391400944003a40c0c0c9039900c80040c007040303d0106c14001840824207108402001c3e400800442804561101d02048071781e8070007580d50384400d010b640f080e0b64854010750b1a4010113519000401c811a60014248100350415414411038840c9040300040900298070140d440001504d00b01c0314641007424605c01e9044200c0b200390070000440c018041c1d41d4402506515000401524031107000c400c1016034600441044181e642c0d10300c40003110000d03086120296503d00b0903c408003034854040e170840d401d04c044001a9542c1c08600d00640d141070101041800c404014141c1d81d000d0443c0c2d980104070001c02140105000700c0c0615803140120001610300a001e503030f88100381d00641d01c03102c420380d1140103204103036800c08203490450031800000c0c40e083c42c0c0500000c0d0381c0c0c6000b800031810301c04001207800071340d20350b20311032400c050000e07 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 765651232 1250 765649982 765649987
    0x6030e15010b0d110a08061c0501180308150604030b15060a092c040209180f070510030524030a0b2a041404050a020408120408100605130207030e06 65
    0x51000103202c3d8840d200406080d8a0302c1c204d0103031801c940064540081c550f0361417100701c0c1ea948041c0300c00900d05031200030028010480d07020014609006401d0181c1c1e842003004481c030b00301d00d0090801c0f10090310300c400a55442040400319290f643c103440490342c00c4410001e00d03498005086102d51004818242c000b00c00040d104019500030b60194100d940707140c8001280c00c0301c00a818107a00069441400c0c003030f0040049005454114515504501da407025086601d2942d0741031460701400544001c3e6540028030300f0031441c64950840c1000240d01d0030140914a42601211008401802c1e140e00403017000242122580b000c010407145503501078100011400c1c00160a00c00c1c0748100c8408100b0751580691080c42c5250009035811518510005420342d50000104405444020a9801469424000012844402c10610380780c8403140071407640c0e46082042250030010003410000115080190810464503068460300c19211034030801030b11000c2600d412520384020340021507020307001 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 765652482 1250 765651232 765651239
    0x21804111e07021f17011a160201022a040b06030402032d010c080105040c020d080a09080c0303011401140403020d030c081c0606020f0105040b060f0607060501090f05090c0a06030e1501 81
    0x2001300c610b1500b01c15071781400d6a0fa200d0010a640501150303200890324107118085142c1410580e4600052050054a16003000c031001e03080032480810007070000e2131100f40034001c3c90a044c4200e2524090998402e0302c3c52038540c0200b607590b01d644003241c1c0700c02c4e410503010500400d045003407032540244a00a10038400310b020010400d09080c007401d071040b8a00100c83e1000e0340001a00300c8a180c25407078039146c0380d450f034014200802c2c3c0300340141c8800e2810130000d088500140001c5001c1c0c01d41c003c0483c50301032500001002c0000c810703205100408104010700250380c801e0340407072045915150040c10a0071514000245000c0d59140e00e001e0303401905174158040b151b82100f4191041a4216110a03420701201d40c243c03041980e01a05c0801001c2c0480c00c5ea0601400028048102404940c50301800d5038070141100c500b6809100120fa454110074410700f40380c002c0a4000e00440005c040b00401c410001c1c00305a81449a42d00385903840d001c405140c0d000340b186000503107007010901039a60b034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 765653732 1250 765652482 765652487
    0x90306140402120303280b151201050a300605090a020f240a05090306190b150318010b04110c010e0303090304031b09021804111e07021f 60
    0x8080c0c4080748204001d85403401c02000000a4a01c1001c60014800b280c0c0c9106c0606000301c020f04560007901620f0b050b01e031a0380e07141d660b01407003801c4589504681d100f001407011515840182c100504c80c03121440c3c00c01c091042c0c00100035104076501e0241000b1003582045803031091010328002c0002d404c19080118030710740441c00740415070090b40c040b8056501c072410058000654195800c0121001d0a100030140c2e41d02d000d001c551440d4184146001c814100091070000116201d0103a02d5001003a91039840380d60044000d0700a042e2824121179002a000c001c280c000200811507080c0d4201030703151507802c2504400d07107901024000308001e980d40303100d20761180e01c290034614042d07081c180303105407500000044a00c0740082001031070805007165070301e00e1210304e0f0240c958004401c0581c0482d80080343d200600c85d05009100043e9101068824481614600703410410285014885104940f20015000000c418200f40c401c2d0750304064800503c00505030f1410800b04880300c425041c01c0ea4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 765654982 1250 765653732 765653771
    0x6091a04050909101a1021020403050f1603030c03030f2c15010f030323040b0d0b0906010f0c230c09090109020d030804060e061f060801030b040b0403090306 69
    0x1410b850f0501460003185c1c01c4031140503841007030a40103e8039142200c400703845032460100e07020041c101f00c81e0500446a001c81a6003264000303a0b5160005a03a1125000040091200141440e00c50084152564401030101c100c1500084e00303143e1030382100303e243c040c5036201f8102c003201e044524204181246040710359503d2000d640e101442500d403c13200c203920084215040b0780510300d0400d01d032400c564044074000c81032900200000065030700901d4281400f006440034042110780c94ad101c203000708440b01682e01401a242c01008020f045c03000c6030340d00841c081102620f9040000c1394044514100b111040c000216000340080390300340c10841203010072891000101146c0040882d21000906800c03500c2d1500000d5001c0820b01040000034041c00c542a03219015210015113903003030b000010304020b030480d0035401c030740c802040c511086900380303950602900d5a0b18046180707604640d109004403001400150000b4840300004080511802102002d560722038801d0185c031421034007454040 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 765656232 1250 765654982 765655003
    0x70b0d18173406020a050c070905160c050d03020901090b18010306080304060e0d060204080d02161d01030f1e0803101406030a0e070503120408100606091a04050909 72
    0x1809840c0c8103401e46050525440b0550015400039100b498180d4458000f5070207011a5828414140800942c054080c00100010047c1c0040498207280154040c030400c2400040001030001071410b0ac004143d00003603a6840301080d08005a0b10560303000146c1f80a0704650090404000020300e80d010803425460403d21a00c082e00e040c000d59840c4e8080301d40ba0300440c09400300050900d0400c1c040ba18090b8850700040340a81c0005181c0340e201e807650317810301c901c0b89508400341c3d1041c41c15254502d192034078503004200c541c4c10300800c4610f00c40283d0b1b00101c180f102a00c048034036441c180502450322030781420805981c0c1141400310b984d00d02403e040c3c00459103442a480c0c5036000103a034902250403000c0100000b01020f10b140e5030041c8080082144441d00f00352446551000318031614208031909050728103440094035640307054144e5180140c12421400388a041c00001c11081d50040c070f2420540e80101d100841400c01070031498141c1c01954401a40000c1107800d200040401180d4140c07013 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 765657482 1250 765656232 765656257
    0xd1403071a01090e0a11060409090b1501180512011d16050604030807062c160f06140d0b06030a0219080124020304030f080406080702070b0d1817 64
    0x540e0740d4043c484200e400000762a101a0401d10080000030892462055544001010607040680340c2080004895900c001100c81454102c14464003e0885886940c1a0b0007460300c000145103a864454140718548602405101082c00c0700c41461000c0d0041e08800c542c0741c0140a40d804000e00003592070340c01c0820031000d040a0b100102d0281412000c65040ea500415080d2901d0b0466417034000400c0307220984644038040c03146082070000f11120a0054420303410061034030190401c0110300070482a03002ea14602e1003110108180e035001820a803190040d588025210144201084003038400c01d02e40e5940000004104600804140d014080c074101840019200d10f40e14007040d11655800c1c010920811221100006040c11a201800407020244150390525549594041e17200c124084210f4564101040c103020310f90340000101c6c0d020b0038610050000524020a001583c8070304401d000c0c40741e40703c002e019400c100e00b45e02c3c054641d034000723080111007850098950654100c900c10404 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 765658732 1250 765657482 765657533
    0x60406051b0a1a18150402060c07060e0103150f05011115040503070303050c0c0703060f02040e010b03090c01092d171005070c05190c0f03050706030c0302030f060d140307 75
    0x660407001d800b280705030b03182d01e002410350f1a40081c00041c2040001d000302c2e40301008114200a050307080c0203030ad0040c281c90700d640884030448000981a1811000403007101801c800040040906051a031403c80300c0c00e08002607281e500011a03410500c07400ca420711403881c14402e0204100340080200921070080d42c00300308503120b102210041e44580310940c1c00680c020f03031050001c1146503101c07190000b4070741c00051038260f5400a91004420903408841055030100c2003000700c0c801031054401c0101d0918003088103a04090005070000501000d4900c044d012034040100340d40e07002c0e821406092000040841002c2c015095562415807113203030301c44e240c02d19010610650091400520f0320b40d101001d8581d20320514440740520001e10380603a05928480c00010340040140b03000d4001e0340c0294047d102d01800d1103805001d403051180107a04140c4100200440001400c501c41d4002204591007118174050b0304010340104000e403640765030350100082100c10000008241c0110070280c071082e00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 765659982 1250 765658732 765658741
    0x170609060705070b06210a0308013b250306090b03010b010c0f1b08010e100e210910050703020706020304050a0510020106050303030a020a0905030309150c0a0507120501051302060406051b0a1a 84
    0x2502d0302e00203e10024074100c8900c8107000e4050201b1031980442d8533030038442c1e400f0005015030b04070307035080d0715001c04246d4071a400d1004c3c540c24051004000030680003888981d0780b840000b41004003403900905000408907004013041a81c030001c582c1e241c000035001c0c4905032078561450090034000da01e601c00340320b050710244000c2424003078900804015800381045440b40c6002c826074543c03510700500401c00410110381c5907910300384021140550341e621284c4401c0c1d030345400313450064640c01c400d0541d0f005100c10401540c0d0004150192502503400640a039420359042c0e014010039008075506000100c104483c40e041640500a88211584c81821a50340c40c801d141e128800d441a541d004001001404c081d620504014a40115080c0490761281c000e910b07000c3c20034a098001544107408a0240b105000c8240550380d040503d030b03e0a082907142550000b0a07500c00c901c941c3c0203001021420010541c45005041500481a02a06c44000b4946051200d00c0c80d100543c10f450b68606004c00d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 765661232 1250 765659982 765660029
    0x180f1a1201060e060105090f0301050903130b03060603040f1b031506090212060d1e032102160215040b1602011704031b0c170609060705070b06210a030801 68
    0x10202c03801e5860003d0a61101e00c011075580d40400c8815402a0001c5000d01103600d01740b08491090100f0800307191500b4142003240380c04052540101c044020501c02c0c07000654491044076009541300ca140d00074051a8a0840e46203100c0c2950102d2112094000005100d08000c1c03410070000c1c03124080240d2501c0d1880041240909a0b02c0048d050106000a00d03604050390002c64a6004682a00c4100013442e1008230079880610b01710002401d03000b520000800100341101c0a4204d01c00660409100c20702d80364120b50010340c0a8071842503809922580f041d604c0c1110090065a54800c0e6030303540001300c0d54401e0404c800102d00240002c1c0000c0c500c0c40c0742030505d074011503043d070b03507200c030680c0306943c0c4203010380f0241040d00c040040820000340300d8440040c00c52965804000340400b89080100d1a003007050043c204420b100c1c040103401e000858030040c80340e000e00f0440345490b0501181400e00407241c80c100d0341e003085202c0c040281e000e0503008941c55048400012003040300384600000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 765662482 1250 765661232 765661241
    0x5010c27033c030e2d28091e0209060d0e0319200c0114031906031b09140c07030c0203011503020a051207180f1a1201 52
    0x1402c1e001c00304460b24400510030040c5a0100707071038030394016a035510365501d0091400030303801100440e1102c590b04800f400c00e000c00d403c207440001014640034100c48007000555550781e44092043e00d241c007009501d81d014020703029100c80802041070a158542d40d0410040a0482100c25424420580044000d80600840b8050070014003094206050340c07500c0c1024020028168801d80000d12100010041c24162500300481980d9441030203208508444c100d400380b190340c4030f46500aa160304032640d0708014900c1114100c800280d030b0fa581c651900d20600d02006c42c403c182c0304d060880001c00d1003910041002c5068185885c03c0401341e90707080d608102c80c280d008924110400500190350004075401616031140a070402140400840e0f000a0846108142d00300c00503c0010080c0f05606140b050580945410b55a43c181400c05c40d4899039030326240c1c821f036510600342210000e02d04d03009821a410b1204e881e0800d103d50003c0301c0c002104220f40c0071803240106004150000f140005000c1d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 765663732 1250 765662482 765662489
    0xf030b100605160312050a0b12010e0309060a09050d030c03120c09030f020402121906050105070b0a0e1006091b020a030905100e1c0201110f0d0806040905010c27 71
    0x100c103031900703c802540f803c008000880603428060203405a602c80c613450701800c1c3c803c0c0c2e030f540c81c00a50340100100300701d144c0c00c0d03040c0c143c40e842c4e141005a80c41d01100000310340c07403813400700c0c0e0300340d101c2d101001c00b1a0080f11a4010a0300000b4140c00303081059006081c4c0052207110352100500300440b40c81040841d130500400b20001015201c0410216412a03c01b140040c000350025250290b00c440c00080c200007510200711655502c82c0c00e0071548202d1180c5009404246099494905503840b4045480c1001c1e01c1c02001a41d0f5aa18054994081295801104265905000032991409814000d080d03c40604800801d14848010514400b0030188004ca0389504c5c2c000d44c481c00c04091001c407101c0c0071191750901c40000c00240c007942d03a08035201aa20340300500c4001c603041d07034400180703140c424038a072071456400700002c20800074011854074010725082c9450182a6a0f00e000130303015086814001d0300c254070f0118080191039101c045145a1500344181c1142c0030200b1110100d100c2c071500c0b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 765664982 1250 765663732 765663737
    0xf0503040204110d1a0307080d0c02100c050a0302060a0c080106080a0510081504020f0402070c120f06020c0c090609190506150f03040b060609060d02071b0f030b1006 73
    0xa00145000e070f009524182c0b041801e1814081080c80c0e040482e250040c00c4025084907079074000ba51b01e4108995405000e1000c040e00141030800c4012b828103500c000000e1180c403843c0c0d14081ca03644600300f00080e0315001800c840c4040351508020351031303800a84142440c24200b00074112903e008814190403100c007662940380c41d6403803c030808020700c000b5080c3c041880c44018009288001044440c0c40c040c0d9411241165040c184104240351070b880c10f05a00590042c015080818401c0c0440340888450151041d5000d2851a00944080c03007030713200a21091012400c4051f00100082c1e030040d1907410b4510228070b0725a541007284080045a03d28464001d210b041080381580e80c12442e045030018000d00d80e203000e20000142d0342d0700300030321212180d1800320400061011320811a60426020b461391407500301c2d0800490031500c11b80d07030f000802c1a00000c10b4020001c402140d009010f04100c10000269210a080d0340d81410510040e00c00460b1600071405018510030918101c4a03243c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 765666232 1250 765664982 765664987
    0x2090303030705041502031905070f081c060503190b09010603021c0b09340e04111912171b011a1207051c060218121902040f022a010605010f05 63
    0x5010888160b0300103102283d024455210be040003408902c0034082c640700c0700000761251159042c0b21002c03620280c2c0300e9842940f10200320a20b000d21144212203158000000003400c0d6601c40001d0302501e260b41c002500898103000c4140d0014981d13520740c4e202c3d0b00c6121810400d450382100c180e41c558140300e1199290b403130f1818609a00202d9a8109545002210501c0060740e07079101510706c0c000101d5058540d40c00503482807180c0e1509481c500c04200080c5034210300b040c10045c20b9540e4400d80030001700b0302e003104052100b40d0384184d029100c1c0d510344d014550b00c0184860146901134074800040411403201c00203d200d051030b080660001142030200100031041c0303400f080021200007405a84240f4040d40410008945507000030011951208914012508548107101101c8500c0c82c0301c40c488c0e04039148007a004c003000c04488100c035404a0b004110201e00507080e100911500036045d0501c000d8400985403901c0807207040726880d014000030400581c0e103000643d1541204132642d40041c108 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 765667482 1250 765666232 765666277
    0x1a070c0e040b011809060e010f11072406092405180a1d0a0f03080606042d080f06100b03040f0b040602090a140301060b0903030a120209030303070504150203 69
    0x1c1541100800044d000705804a50351030720300441c0d03014000d035002c40e51101c0b1240107030040c5011300e0039070240d4842c465107040d200f42c031900c0c40501a0f4020080d82844464010141400c54210502828085174100712071052503000392840c010742400005489521440005c00d80b504041a01004034422215400c0741d0300c03e1209d80060a204d85103440345000740e010340850400c01c0040c0400c1d50712a044500090080c0c0c14050704e003440c002c1001d44140340c02c00007031040245508040c040d0a55296550440141900c6840c4201c015900510401d109265201c50000b0300015014000c1c8280710300e003a0140e4072142040d80c9071000f1503001d010100440100070010302d000252a40c41030080500600b0300050350006410454140c0c00b00015441995010020b4a020301c01c07040200a010025440c156041010030380300d00a40d1944401d008001d40c911407114481e0701180e0000000070140c80d0b0703a1400000180040d0024025016415020950a00780e240000110382080d03007041d0040028955 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 765668732 1250 765667482 765667499
    0x3070203220627031a040b1b071101090902032a0a0e0d060906021c0f060602070b070201050c15071806050409020315040e030901020f280c1a070c0e040b01 68
    0x1019200000d65450100000001c00d078400ca201c48040c4405c01c522080d41010b0415542c041400b501a841d846509080301d100704103818119412168004a1a0303048000c05005030f0340303164158080d00c003407400041001540c00c4042140e0f141d40070b46000c101001c80e012007a101c13280c02000b000340007080f8070240c00041c900d410900440c5270707442950080f882e40030540e20700082c1c0c0c0115140e07125907110500d09082e2052540110f5100070f1440204100340752400400130f513a050f01c1c0c400c0040181c400200d60041d13902c504120380c6410900d0742103810340f014607a164040b5440c11645000005c524404152284a50104020454400b541d95904007814000844001d600c0580801c40c803002d4103a00c41416159400760441d80d4801d43c0180d81c8805c030325400a81050406410148070b40c0040914055411110b00c4c8440716800d00c80030411036075217500c2c10360394016171500251703000103113641103000043c1010000c040701d9118542c1668403d9803643d90585c01c0300b00f600c00409a4a140006100e00c85 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 765669982 1250 765668732 765668777
    0xe01090f15201506010929030c0d0608061509040305040b0901030b030109030c0b13210504081b030d030b010806040b060d1d07150203030a0b03070b030702032206 71
    0x611003803840042c42d00c4240d1900340410b48503003003007030207204000840d07800800b041c009090b90501c07900e91a14501140c1380902c0c01c50b000840c0e1450110100e03215200d0034041e282c007020501020001c903501c034040943d898104450941100300d280200ea41e0500780f1580780b42c02a5850346521b400e150800303904012903001821020304143d44d1b203070f6144596030240148110a4065168500c051316541810102c21500904014145c810680c5400000300c9051060f804040c021601c0b05a0304682007044603d88500d50103405503100341070b412000f101c841011544070300c008500701c07518541403510640c00c0d102070000b01ca003ca07410300001003040c14960030041200d5402031000e450a0b400050220803034650f8044030904584500962170304400c100b04840240c04441e9102400c42c1b20440002e5892000500340300c04152074124850a03a2020000e24000d0103044001d5916841d080704029902c3e00400090180100349000100201c0740d40c6003424185c031683c2d40d501342c100140304270f115440e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 765671232 1250 765669982 765670007
    0xe0612030a1e0e060f0d0501062307080c060705180d2102010e010c0207050a05150f13030c060507060f0e032d030103060b120c0f10020c09070e01090f15 67
    0x40710102c080300c06961303820014181c2c801c400c0842d84d1100001068030701100c405800c030009000c2c80c0525181c10044441d0b805500031050580130303a442400c3d180290b114014828035400230311a6400b4000440e401401500390074458044454414180c7c07400c0048035001c0c182c0140682c6032b0114800710030b41c864015480c0e10003d0740008121100c12a408c2403c5401050101006070800c05051100e407070244c0c0307403100802c809c584d0240c0b0070b608404001440c1c4154140409a20300005144180c8020006040d0046410684540219982d84409481c95100035004c0f1441c925001031040103800314460100410700d000021402c00302d4828403078401e0184800c5024003075103a20303041e2907003e080300e00550181d4410140443c070300b0201c4003070043c03414103441040065000700146892540340d00101c0001d00808480074880d00c038100d030090341021400081150040050f400700180d0940040238403c01c1c6400303a8440c1e120982d5078050361043c001e00e005400441211210240c50b440c42201d01c240c40 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 765672482 1250 765671232 765671237
    0x80d020c2806020c0a1406070207090e060a200d06051f2a02041506030c020f061f05060a081503070b07080a030b090405101409151504060e0612030a1e 66
    0x1091541b00c0c8032a0f001c040000128517807022040200460341440003000400350340b0414008401c405035440d40700c00b0300610302203050303649000d401b58440c8564000040d00e403001c0142a5100034100c0880040c0406024290240301d810100400e13030410007610081440d600d070341d01c0b40a248107081c9200d503505050050300402e060040d880004d650f9500c10b4041541a42903a040601e2030300c0400303410368000310440800d44d0000708450003900404503002e64001c01815240c000c0d00110b0f05901c48512840c1c110300c0c2c01483c0400d403407544a8010307060314010100701030f80d142000c90440815a5415403805500c403400c8050003804000b600d03040141410711118100800e59000702000724104400403034064440e070307110343c0500c100c80416200314603406811094508491611032405540c61003145061034102d200c480014040f001c0b901c00089104030b00502c103100607984c0f045004410402074841c58800c407030a05142002280c00003c540001c1c41c0c1e52245164480ea5080c81e4200e1014081c1e120300313 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 765673732 1250 765672482 765672493
    0x1401060905070c031d1302040902040e0603240604020409020a03090203150702070501030e0102070803071710051f20072c16050702030613110108010b0d18080d020c2806020c 76
    0x3038800c42e00140c0054035007649c005031a9442d02c4001c1d40c0c2c80c1c90262219009420241803081c19483c1421000d01c042206443e802e0207845690105000b07200e41c0d840f40c6841ea10105819182c0c81d8035800c0010170710b000b01c0480e403881c5150381e050201440261140c03000340e0302850301040a54020382280e420700c0d50a0000604000181d102c3c14203039803003101c803803000601c07441c48038900e80c2a5654413034000d411b03900c0382481c00d030a040200343c00c15014610681d6586951203000640d0340b0600000002040716000c808480001c40c4000e035446c0d0940c003c01d03249448400c0307002c445400740384c0300e4002c0301d207410b0318100342d41c0354071403020080340740605400304204007000b100300580c40130020b89001d911076650f150440d0f812800e1240200e0310150070603040010070001008250381c80400d84a80a0032081c00140b4105040c1340b102d81c0c24045100103080b8a00070032005042c09050380603003460010081628203080000c0d03110b41d04001003031481c11000b00c21036144c3c0007196555011b00302120103c8119031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 765674982 1250 765673732 765673759
    0xc150318031e1b01020f030f091603120f0509030304061b120c0c08060609070e120f061e040f03140405120c0a09020906180d1401060905070c031d 64
    0x7100708042c100c00b41154400510348042da0303d54140062000b0000000b18140341a207001600079200150041c201101c892002c0b0380d074010706010740c2280540c1201c504c02200d5491400e24a0300082c00070100200b01400d40418599014004503905428003d001d1860182000c0c010b1324009500c2b107074a61605114124040040c0c2d04010415030540e21391240314408035589842455102070345c100b50255000301003488034944800c404160006242e062001c8407860f21004542e222101c0c1503829414401c002103446003503000f081d81e9003d140b032092502800c507c4106c4034100c80130107071002048040600d40303080100c0c3c418000c024803a04180780c28ac0c9000c0da21400144403494110140d1781603040070403481000d1030a400c1e00d000401d0b1641040d414003000d000040c0c01b81c0510700703044407006900a02d079503290b90392a04030780c00d46134840f42d881e6402c0c2c3c090300741600170700c81805200a554540404160124092101c10b81f02d15819074481908802903102c4210f20407041107499045040c121142 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 765676232 1250 765674982 765675007
    0x3060402091b0d02041e06080f0619061d010906120e07050a0b131512090215071407060507200f21060c03091c0c0b0a0c020c15031803 59
    0x411008150f042c01503100d9051210b100500070220650400b4078182c2441080742035000740032107034454190b090002c00d40d640c0001141d45210042000380a44040240c0401e9083d000158115880c50b00d082c0300c0100390003000150340c030185c58003c46c00880c1900ba2126584040c0c0c0d04000c1191101c8001e55690342d0369507000c620100d5076508001e0040c0c0011450340c00320a00806024002c1030b003501c1800c01004819005403500c900b0745020148035480385011010b40d19001201180341c2e124070540382e0345054604140100200c00c001082060103211000100f2138400e038180e420480e080072681c0346400707840703e0030b4050a103000c04141d00112100d07050040c6039100740325000c3c1d0f290883d4a20815080e55144076090110080280c00f0030f80b010f00612140c0d403400103072098200150025401c08100360001a10060030401d0700820300c13034080e010845c0300105a0001c1c040b00c0764036004c450050140300100008002d1440c43c072060740750300740005500100c0c040c96800f40c0302c107010181d078070381594584103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 765677482 1250 765676232 765676237
    0x17030c070303120515010e04020c030903030a0306170102070210050a020c1305150904110909120d020a090e130219050d0809011e0e0603041509030f0f090503060402091b 74
    0x5a022031403d0003c80300380606401820784c880120359070720f552080e000b00040c040b03104406000c3d0240780d01141c9403000080820841c0e504010082c03c42e62074800b24140240682200e024815144810b05c2d042940e42d034050080e0b80f00d50340e00410000d51003a0100044400360071040c6918118443c0340c03400c0d203880e01c802d0304e030006e6031032114030104a03440c4c91030046ca442c0640d180010f000e41d108400b00004170703420321140000c82200315011400c42e150740e007145280000d2036034604850500012240803600d2183d0003490504041d03210081d020307039680c0001c00d10701001c8620325401c49125900c1b00040c6000c59400c41c0520545a140740c2c01078450021076517402d01c40d01c003100c0303001d80050821144e40c1c1140010700c182c001c000007d5002c442c0c07031a00410740075010707030304a01490012000c10100210400341036540f07921274038200f10443d51410010180c03404418a0700200e1070460440d50502d125140e03080a1b2800507000780019240c0b542401504c0c02c0003003c160842602806214490b4a000e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 765678732 1250 765677482 765677489
    0x4030f0b04020f0d030203030a05090f0601080c010e100806040507020f160504110304020d080c1c08100e010b0405091302180f10030b0708130b0702010614060a080117030c07 76
    0x203403808607140c54414020f08811580e4035620030f10145189900003079001003180d50198030140041299114400b40c680743c041c00b6400e004a50050701c2c00441c29840c0060b148a04202c00d0343c5148819005905101e210240c66910100280791100060014181034001903004003030f61044500c403c2a10303517142d05004042005840000d041d44007000030341384c01d0052605002640f0b07071040c59800e0641c000340301004202c00051000c1e002050348084800140013a01c2c07110a00e070620383d01d00f00b010300004c2c132421046500003050450f050000c50300024211020381a540c1c2d85202a141606050030010400f070000c05074690282e8907090540162202ea14207040c0d41da030309a40c16a039090004203403141c00002440f80300c164514030307000c001050300307070013403980110042c00d00844c1da0b1640f03103003209006c18030100541042481014008604c0d41503010f9004ca41c17503000e1400c100c680700007c2025034411800c3c1c007030000f1100b000504c00841050300e400406204141180e242000301e4060504104182d40b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 765679982 1250 765678732 765678743
    0x50f0a020a0c062c03030906040b220c0e0907140103110d02040305031209010c080a0507180b03010816120201080601170108010b1005091f0207030506090f160e0a02030a0204030f 78
    0x50740005040c049130f403040220302940083c60540ca040c0700c04640d124402132010301644845004991000f4008100200030202c01d4071855007107019007008200031240e441402651240040007175903580c2c001c2142c1d015902c814030715a0030415100011070207850410448001190100058810102144024001184100701550b11100842ca0500c0d9651000704082e8059052829031200c0769400f80000c2d034032611103000054aa00c8054048509400d00d00755007441c05903240010400e406840003a6048a1280b4209c80f004040c16a40b6140d07020188200e2480200c0b00f01c400d0300660007000b00592125040c0745c01060740c8001d00d0031100c0e035002a400380007d41d65401d1011090300f8004800c80c010425030610f240ba040c880004500000e024a034143d0007540e01510300d110752803007800a01c00440d04801280d040781082902c1d2a10f81002242e042c0da644900c03141d88035550818403591040708c02c01d4070044c00980da0030003404040e43c001801004019170170840400060314527a1264080c80c003c4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 765681232 1250 765679982 765680021
    0x60f0303170723120a090605010b0702030303040611191107170d030f0e0a1a1006080c071502070813091503020d050c030703150f050f0a020a0c06 64
    0x6040c0030306580081c1c5034003080c440200341002a41d5402002d440f00103000c04014010400c0c0b00400c4008502884000c1c3c1c1014a03610103021500e00d0981156440e03d004001c1044240d0b625002d14526101d100d1000350584c02c00d00018000c182107602c0f045284c0c03801d4120070700e450420b4014900481500c1aa030010650021500641903000c10010019000b40c10b00010400c0b0152201e50352010784c400c42000301a02c0d40340410780c11103150400000c5019410454030641e9803850410124034502c00d80311800f801d0080061400d1000f40c49510403280951210200742d11a03080400e240d610090040e00e1a90070100280e01e00c16240c80109605401028241c0c1c0f117160f004042c3c0c1031101c00d075210b00310507821708070903400140002c0038000450340d044560008150300c62030300340d0800c2c04a869441d4940101c180001c00d001c144608000c7c0081c01900411580005581010440d0010b540c40032400c0d202c81c0000d0010150b50f07000f03216550315410480b4004006650b482c05541044500030310400340d4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 765682482 1250 765681232 765681239
    0x22030f02010e0601050604050d02010c17310e090a021806040b1206070507060908030f270607052107120e0106080a0f021f02031213020d1202010e01060f 67
    0x2071082c42108001500070b4001c551500000a403240500c4c003c3e11310803003660b19810210f81c09915030003000d6500c180444002409889035040d01c2d007040d183c6001000c0c200c0001b00d4014031280060640000100b5502e001c1d40c1040020519064000c100c6c80c01d911076149840d0150351026042d0441a8000403004038918240040c042a02d80d00b00905008005140d100005c03040c021a1440e480b0b481c51408948600b020301340720000c1d00e401c0001400c00d03100042441181481d80d5000341c072801e040700790f0408031124000c0316050407443d0902a1402d82110000c2143c0900c190b009243c00c807880140610302d542c401043c0e130b40c03548c015610035021032541007042100060703a0144500c1c0310364610017040014544000113440b404480002418944906821001c6541d0307004c1c03a215960b40b00004d0244680744001c081c0d6240d0103941c40b24680c09480d400110075a2803040e200146035405403198081000c143c0d507080c0c110842e040c9038401e554861303551006040d0f0034850301d4004c01181c00b0240c0050300e07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 765683732 1250 765682482 765682487
    0xd020a0905060309120c03040f03120806061303030804060b1306050a0807080309060a0504080a240b1c0602310e011a0c0a02060307030e0609010501060c030822030f 72
    0x1001d40c04180545014020041c4140d404074401448400340e80030141c1e603280e00300e01c0301d09611079034126004500c2c0d901c00c04401c1c8103c1c0c62540088640544628803a43c80d200304101d21409045c1d101c400980c9450303004d00000e44100f20940d086440b03250049004400c00b00001c11400320540300000e8560303a00401c0002d440c141d5204c20040000c3c42c09041c00c0c0b420b03c0c801d03030b803a4410701d04220300400000500080c0148220110b6001385522015038041d0b19061800116481201210141c42e900c3e40681101d0100340b4412540e44000c01040e680c1884032015030442101403904041d58081d40c01e010134605070314511018014680b49026800f01c0c0c4140d41c104415100300c5030000c450380203020f0010310401d40c46210342344403d08980c9400361911740e0b0481591600c401c4008c029045000841406660f07030709500701040c6041c5810984040f955203c10f01400c1303079024030400c40011025045440424000d010207070f0008558003040002014020b03440056550b0329004500040b03000142585055 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 765684982 1250 765683732 765683747
    0x20301141303033213140d021b0901060f03110c0c2b02060c39010c020319060204050307060e01080f060901030312140406020405120109020d080307050c01020d020a 72
    0x1646425201016001031040d00103022918036840342602050020074020b0340b40d00349171078607584d000e06086102c040442c1a5078495040c0c03030071400903114045140700407401400303010000c101c001d8030300b220682c40c100c001c0350803c41d805051400d0554811003010011009401000e40000c900300404a0162542c2400040141002d42c4401c0042c03d40d04403440040090350340e06603c0d01211011784510404002500340801e404e1108001c165483c803211490540240010100c103481022004034100c2c4401518840a4940001c0d03160300140c2451411280c103070343c40210380e4007a03c001414117449401092030040c071034010070085601c45607900c0d059039112144650050140303803d51098100340010503d42c5a040c00003c06004400211a1908129600c825064580401031201c1820f0074100b4900a40c0107026860080c6110034207041400014001c498101e507016119400204440d1590115a00054044010050100940c0d0320000d424000f070800701440b09c41c01a07540352042c1c000360496 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 765686232 1250 765684982 765685001
    0x21060303091a030903070f03181d1e0f0a06180203181219030f05041505100608060f010905091e0f0c18010e060c1b060301030c090902030114130303 65
    0x401c010010441982400300036902c4003644034020600c0a0074074901980e08034800620303030544810030b280003d52a05103542cad205440c0200401ca00e02516100205103890043e46a5980002c142c4008591590703108520640d001040305400600c5a854410401010001c03909020710140c020041c41800c008640091428900d17140003130052008070707140c07015103018600100c64005c0c0044040e94203513000e03420004074044044410002e0b40b030546441c000c02d42202d00a81c505500c1c1200150010141c281860142c2c0d185460301c0c0701e00c2d03403030038100300d1030b041c880c510305040208104002407591503c1c0c4129014070840564012988071061100c3c500e0400140614044050281400100340030351040341d145050030007500c0c10904c0c600300160f0307944c0e905219a940020000406000c40c4101281c0a11b040480c1c00807000840614410001640006e020280141d8407010701085070103003551041c032600b0700c094000f180c07aa50041c2980200101150080d07a01c07000c1007004800c040d41403150400e231 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 765687482 1250 765686232 765686279
    0x804080c0f01080f0a020d110a12181b17030a0e0a030206090d020a031e020310140711121602010e010f0e0607050309031b0a14102106030309 62
    0x784440da000240b545201070102181000410f01041984406804039203040c030008070140b00c2103050b12200802e80d40b010a13100c00040c0c0705002c0b01c25500d000e001e0184850700c6207003903a4240900303884401c50102c941704e000c8006201000c0c009104010340c8010340c1100300c5c01c00079580f903403420f000c05444102013030012481403084110130f00059540405480903a4025240001441a03030320200e02c8440b2981c00140144080e27220f858900c04000c0700b001c401500c01d405650600000d04d451a05440c5c00305003581d400030284c40012a4184104801403075245500c04950b18101524040f00e203580c450000f00345494036100718903017035580000c6003008100d820b20300b07402180180b800003048030801349110f910a00700010f80c1c1e42404020825a001d8410060683d4031481c1100c5e500c0c880c541510407540c0c041c4145010004080381015101d40141c000038295410b201a03c001c116001c10400090106d038080002859044119610813000a1031280c0c0b1558080c500703001c0e104084250140e0080c50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 765688732 1250 765687482 765687499
    0x9120c130504051509030406030b120a08030709090e100e031216080106020d0c1707150605040b09040b0a0b0d0b10060905060c070335040e06091302010c02011b0804080c 74
    0x20405c4000221000c030755040c500040e070600c030701d40010104081c999441b4014072030000d80b034003130000001c0210300440b0540c840c0b20a140d502c0000130103440b40c8030101c0e070f203039005204c1e40d051420158103c030b03144000441c1070781d161403120200800100f1055464004030321605200750713a41c0790000c40351400751480d80000d100b0902040340c01484050b41c000b0042c09405ea08000b0010764540000360342031107038005000d400001d5080b4001008113001c0c03060920440c100000d103007642c14401072150003160050800ca81c10355400e0400c00203441c0c80c4100607080112040790001294441900d18007030030940031002e81661401070001e085161030780007280306190411542207034580000b03010080703036840710149000d4844c0f640c0f0760036148914064000c01003010318060009014160041056680700f02c160b000d1a00e5036030901c19000021100c0541483c00c18148202540c020007620f102c1c6c0c0d01c1494443c48041000800408040822000f200c10741c0380460180700881c4144410b01040c1c1094a00e0315 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 765689982 1250 765688732 765688741
    0x60309012004080d0f0513060e03070e04020622090e01020c0f01181502120403022103010311040e0703021f020c06120c0a03060902070b1e01050609120c1305040515 72
    0x6844d200007809203003d1002410540c040280900161601400c0d079500070110180d6490000d00115114140c0d10b101c1d0042510208040c8030794021240038640183c040760a00032040d04010a040c2d459030024060103100c18000b03004030181c0036807100403103554009a02c030800d404070140b401e280c4000301c06042e414000d00f4a80f15580d401340d61402c4d0340140b998044010714290610081c461041031034400701920302000207154000031070403e2600c4442203d49a100c50400d00b1303407240800c0c00020703c2a0302640c031214141c03806802998601c00f125094500707451b600d90005035450281c0c0c003138401c000661041c60079425014044248200e0003034401c1449c0c06400541e8480a41c00100362042190010828042c96032180d4001005050740d00821942d81005041040024000711112940d211400041b50281d81d4110485412104064401c0307092100c03440400035142c440103419400c0d8859400d1414065031120700c8040f215441580c00126400c10b814842e00f0329409100f200d016a00420600 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 765691232 1250 765689982 765689999
    0x61620120d2f0d021b0d08090309060306010c03180e060a0504020732070306140a0b0f04020306030a02090c13080f060121120306170f1504060605060309012004 70
    0x104807140840d200b00d903141e9050700600c000380103100b2500d0110b194240082c48007200014401d8204040340c8401445a4981000980d240718100840f50094002c0c03020a00c02d5029542d00001940b103401c0003440c043d4041c500c500b15403c1d0742e2292000d412880280040340c1003840000001e0300098030b05600d001c5c0c0c0346d126440f45507440004100c6140b80c0344a9018060b01c01e0001e4030120a400303083c1c92074183e40e818040040e0030030b0901700504136619004140d844006109044601034058401082044000d0412000b500010002601030103003030100c000580e65100110f01c501a8903002c07a466081c0504600720207105504a942e0a42c42080048144030001800da411030b0300c20304000d4034030300346072003900d5140030024401802c40010b946445c8106030150800c1c81581c546c00000000680855000ea80c2c4e110122904441900054060403201c01144243c5a02500071000416180e50310740200e08250b10460340c08400c3c2c0d540d0480c0c4241512010b510120340103624410078101801c19455 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 765692482 1250 765691232 765691301
    0x11090303030402280e04050613051905010b040207080c010b0d0b16030b0405070309061103010609031112030c1b0d0c05010309020103110a030e0f061620120d 69
    0x192150042640c0c1044001c44000c0c0203d00710110049044900e5170303007500a014076030654044820380601c400144061800b4810344103280d810100400c901070b4650300d03645140e094010280c03899500c0d016020030f142c44030300040c040d01e407141080c542d4902000204600715a604c0340c10754420314192007100e0201c1c400078505600099040d0800000c1c802202050f4000c201110100f90410709040403c4180350309a4082c1c0745141c00340400b07210704c01c060780b80c429052009015110229180798814030202c0d15008801c8101c1d400a001c036149503041001c00c40c5560030210040d5000d41c03045815491503441d00c000d03179028400a8a00b07801e040300640e50311502d80e019004071410140d890072040d055a20940050740c602c0440448c4580d10410b03d50000e000d460982d994040030700c00c1c020249040c0d41e00054061161002400711003008001d00f4007110500c400000081e0005894001c0501040092248000044102e504640e9441c03070250114255400101d501c155021011031003e41501d2640c0c6 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 765693732 1250 765692482 765692491
    0xf0f061412060f0c16021801080d0f0f1833030c051b0a060504110301140606070204181212060b091810120c1e150f090801020c0a061109030303 63
    0x10300544030a10914504001401d441d40a58400d00e000e004c1641d1f83c0001030741da41641c0d00d10084c2c40003003003602d030150303950080b0303e88a200003205404410301c118416590f480c40c94000081021481da503c80b940d80310621141c0c0003902e0070703800ca011400c10009a4030711b800c1d422203034103040c8800e41e08008040c3c114020141c00701040d00750b503694104042c0d424090440b8081c0d001c1800c0003039082c00d0070308018038911100b146009600e0701b140c00240c0c03084544024495080104100d01d444415824000a8001c031100000d90b8030480c8540700000c0e0000c013440c0b0500d82d20350350b101d41e51000c54071108241c5240d0b5100c65030001040201e42d00f541c5504d09502e0401103401d06020641d20f80764a444c00240c09648001c0a018610f8601e1080042c0143c41008640c4501e5901035080c0141c1aa545a440d81d48914000185c004500b0768810340500200364181a0078101181e101e03070b4450b2000e0980c0d1110041103034030380101030008108200c900c1002902080080780342d04144117040030a80e603100180 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 765694982 1250 765693732 765693751
    0x4020304150504050f1b0f15070f0b060a0e131106090d0804030c0e370c081801020408031b0304030f03050307030608010218040f0f061412060f 63
    0xa0240301000c2904181e03110300060800280c035050400c0341e156842030074441c5c400e0003910031045884078a4150002800001010441b100300044200860040300308090003101d54180010b1003ca070700d501500030b02d603000e408010781718030380101040092052a0003401d072040c0d400e02840040780b500f840b8a4078071644844292403800c4440c00060b000d0003800b1440d513101090460440820020f0009401140d204400344402c9035101d001200c400c200483d400d00f80c01602400031911410860a0701142c4030001c040e105201905c00d40003400c0c0c44103c00e130a004206035006114505480380002c20223004443c0c000c40c1080d003060040c0ba164402c10000c20b9006040e01040ca00060301401210b0045030b00525030001a109450058501c0e00200d843d000400e1400e44001400c1d401802296200386500301048840c02c41c0b6420030000b40355028210042c00d0f0348644041c580e21561190344003804205600141c1d1000843c204001ca03260070b48155201c0d0400000e02031881d1f46180d1b00d036000102c16 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 765696232 1250 765694982 765694987
    0xf03030e0f040b13020414090103050d050f071707030809060403091202030708010f140c040e010303051b010c0509030c030c15031b1303021f090b0309010e0102192c0402 74
    0x901c0020050981c008501e03900a4243e07024040c0c3c0c003c954020130032200084030030b1044001d00010001d05000c2403101070030540182d4100c0c0865440386000f07020803110b00c540c0508014590315040f811803a6580d0509410900044081c14580c105086e640d1188290005110914256030014116141d920901400480682c0a401195828842c00c030203892500e0007080159420100f4801400c1a0002031080c001514081a000c49000c01124181e0741802001c0d060f6920b0341e94102c94036404100c074030190500700021805107400a0042c20720700d5180340c1c0e446440c0c03194881098107141c260ba10244c0700740e0003551040110340b00c4000c842c455500c204100750b200e603115030030300c0464800441c2c910688000010840c242d4900300c91590180e0780203075146070f2100a18205c40c100041c101d0b500c1400b00f80740b5802003241d42003001c01140d0211030000041484007007900c0f003d0989e00902480422840c200f424803060b180e10680e002d08443ea0090400e4440390350180d04d01205803e0380c010340c01540c00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 765697482 1250 765696232 765696259
    0xb100c0b1b1833030604090210020c211507030207080403050d140c15060a0902040603200301060819060312110706030203010503031b1002030712060f03030e 69
    0x66400c041045860310388100c0d55030020400411039203260100e02e6106075081109000241c201c8040da0b4001c00c000a06241c100781d0440d15503d0341c0d04001e10700c66110307485000310070051b02c41c4220f04403890714640080107402001c004104403000303589125003140f010a03960f81e00e10940001d01038012030713046106000e19114030a0490103840303004800352528000082c00010090001078413980d81c2d010340d442449440b048020f0700d080d8494441d400e8001d500a01088400392105103405801410040400c481c140d81da070918004d0341c010381d0010b00860340e10114683e06a01030902360226011444440d85150305082e0b0203040c01c1c4018196207520307100026400e05179240369009401654006003400d07800e542c820b00c02840c2d852030a050200c50b0060740c030000350b014020f0098038107031880200650f0401c0c1d1902d049420801782c4501241d07542c810380d43c0d4821150701520095004611958800c0c00c4a0440100c1304203549039030348600040c007042c400400119621001c00c4014035000c030344036920f55a8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 765698732 1250 765697482 765697501
    0x1020c1003090215040b21040809010305280b0301060b0c1c05070f0b04291303200705030f06010803030a022b1b0801080303040f150606030b01030b100c0b 68
    0x40303942c8000404400001e0114103a4011401f0380038040128144120300307100304040760031058003510300400005080c0700714100d96002c0d400655219800014640e0740c9401c164241080070380164481880950310f0781e00d006603013030a00465020740310130300143d4078000b02445c10581d5642014100300807036500c000340051407481501142c211075005441d4120090702c500303000c0000942560210b4403a89519550300c1d6044500518800004450b101c04c02c65940c0c0c0c4141d04401c03090b890088081004001004005034080403403841141d00001c01042c502d400c090505140c40200d40403040c0d690b00c14001005114070000c100ea44c00110504050780358611240c055414000244540034411450ba49a201000c038680c003503c1d0005c05034403010041c0c103498100b554004420b008030303403064104200080c04101444104c1800c580310b8074004202c0c0c40d00204000c00c5480799080f21000a842c2c104e800c1032582d05010b0341c1034071081202d0000280f0000003000c0c2881070a800700074503816000b00000e06054 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 765699982 1250 765698732 765698749
    0xa0b0c070f03030906030f05092107050102041517090d0e01120e0a0c09090308221b0f0e1302040f02090301060314010f02040608180a0c0e09070501020c10030902 71
    0x5030300c10070812480d1030380341c0a00491030031301640000a140c0420190f4281d00b07806030307502540098001d000d09600001070403c1e214408504180844020403040000a0003440180000c101c10040e0101071741002074001c005100004c940c00302108180180405110041000d0303200c2001800c1906d505403001005840c50b4280c503580e2a80140342103c4035503882008900c45d1a80c1d440340707486403001500d80300040e0858140003005000952240001003281a540c40584c40e64459a1140500c15001d551303202440940303420044120041480200420b241c01101074018000281805440b89880e44001e90118003400740a4401d5456101e02e150045d1a035040303c04611000c2d00901086480e0304000c040751224808100300f83d0b00c1c109180140d440c07544256001d844159443c0c41c0243c888031881101010301007030700c1c50030b802181d441c0000a00104074141c000e0a003112000710ba413170103000c080d007040e10382d510a0741035403c40d080c0e1787c0301c960f00c0404205011165041c006280380c240e002294441 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 765701232 1250 765699982 765699989
    0x31b071205010e010b040e10050c0d050112110102060424090b0106020307020a05192c04060b090f06100c170705030702030d02120409050c07021e15090a0b0c07 70
    0x410364848903606016040d0010030410034040001d00c025181d00040c0021606550610011500841c40d00042044a0b0b00290380000e02a20b1490400400662000440f18280c0c82000015101014001040b01e029641e04040c0c0e0240003501c45880e00d510396080c80c0e1100d03d0031441e040301c00c83c1c400610720016402000e00a8000710800000c1d83c40b000065607903800355100380d210f002050000940c902e40341d58885140c0e01100d03442458545018140310580440e140500318a2512440d107a14071044610344a10071401920081291400c82c400d2111281c0003508201c2c0d540c840b041041134030f0325001c40b1030004032010b00d40098915a50304001c0840c0d1803148504100200c00520f6509001c0c0000280107854000c42c00d0742c1c80880b60781d4099a89600f401c0801a520b80203102c1002410b056901c884e500c008034801452401000d03500141c20000004803015140c02c01c9140b1036000d00303048580b002044030103240145000d140200148216607984665207400c0000100216207210078032414008 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 765702482 1250 765701232 765701249
    0x302070807050609010e0f010e0304050d0213021207030b030307020325120f03030606021c0311070b07110705220902030a0c180c08010311010c0206040f0905010504050612031b07 78
    0xe07418032601c414040d210004a03100d06d8410040301c030329401018415012080d14890046152500d08824041443c00816040e03901c03040e040d15010302c5601c2d41c001003540c401c0031032008026141c0450043c040b07441c1c1038179142c000c1c0c0c0305102030340068500041c103461109903507141d0403841c0300c21005a4000005c80d0880014040c01c5011002040102a00c2d038507607901c2600c0920885840e000104e0f500c0000ea0115603408003500c42d800302c0240079034002c401062034841101d00c0c0016a4071000290f000075509480028001c40000300351810a1040501030101107500b8031042c04580820800c2c034040c00389840703000b0758035000d003001c55508000100c0d005902070801000203a4036038812801c1c05201e403504c2000350400c00c03407500440c40fa81d5441c0c1130300c5d44519840600040c1800464188003d890202d8200c14100705c0401e107001ea900c00c074030050015210114082d030404051000342d0348064559405011003000a05400a011040e41d1b82031740c03c1d0031103085401019111515010f0b296203c50750 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 765703732 1250 765702482 765702493
    0x204082a03120d0b040203163b031e030f09270709090b0a15090e090f12071a070302040513020c0609060105090a0c09170f0d0e0d03030207080705 64
    0x1001c002c1c2d030020340b1400701200070030880204c0c0d64062105910045840301d1071555411103855125001e20115100d9003680c0c02800360b22400c140c200d9208000e284518500d0640c82851103016142c10060203003a000002001140c041d0341031104d0b030766406009030156a049002c2010078040c0c41e000554840c17201c40b0031303003682d10042d6820862460407094615800281507110003184089a50203591005840688200502c0786050754403802c4408074050b150801003d09000500d50410b0707859140950000b030040c003403241503840314900e82000c40142d0c1b245504148036800206c4d01d1a00c441c028000d280201c08020350302c0703000c104d0007840fa580003ea80030700402c1451203c200b040d03002d05030641c6100100c60440c0c0380d8041d1b4543c0c401091042a038400c0407100002c001d00798582002120308000c0c2809240700e6129414920950162001d09107158008a060000414200400d0704007140b031341401011f0702021001f040d1804c0d41d00401030305041e0002800f60801c4030389000c54078680d800c481602c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 765704982 1250 765703732 765703753
    0xc0806041815022808190906050103080919050f01111009110907030509060402120a0f051c0804051005270d0807050a20070e0f060a090204082a03 64
    0x600075000b000d000c18504c0c0d0741d1403013000840030003000311203c03074425181e07401a580c9401c60070000d26185003c21044903200c03900b800016840380100c0e07018612509180b521640c0300802c2c409080007081d400201004c400004200035118805482802c020a181c0700e42c0d205481540107181c405c6900006000916081c0c40c6801e0181c080454059194110b41c450b0064480360011001daa406039070489640c1c0000e0003107001464100200e9142400107030a55901c1683c90300c5603a074096071070805a4441d00000140c540030000382c10800d03107500a40c1002030503800c190715407603a510000d40e403c000c001d541b100402d0819070b8901c400303c0b103800740c24011b461041a00c0d602c2030715818460220000302c0c8201002c590b00c50702690994400704581e41d44e024803005510070400e013121443c1d01c0f900390350241c11408030315007102c0780740756104200305240510b4a0400000b80801403001361320520005e44140001d201c58280130510361100405c001c05504454060a044200005000046545482107040c01c6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 765706232 1250 765704982 765705023
    0x4050f0601060509130203190f0e0a05060405010501170d030203070302040b0f1201062c060904110a0207050307030336080a1e02061b0c04090c03021002010c08060418 73
    0xd140c5490260340740f08017010307401032810a0340400d49042c0c01b0540030451220500d091644080f03003043c000080898610040c500d003904001c7e0300101076a8a40004041001384402405941c2c0141240071b0780318062402402c2860310f95003001641380800da00000810102d5101e078059401030f100e4a04500c0d640d80d046035200381d080d8014038500c0400c240700c90002440c14018842d401043c0d5401080030514a506411402c14410000000c2c0d8400310a00110b2040d840d588a40f2024007031110402e5034030f081401010f40b0341011a840745100c0d40c01410240002035204404107001c00045201401c500305000c556003404140b00100c203c014400da50009004070300041240c0003c1c05144084c6c200d41d4014246220307804040c3c0040e40100d010001c24012410a1042c589400600c0c401d0701c50707005d803c0c40003030143c500c2c0000540c1c00000310307503050040d0300e031107070b0002e10082e400c1c00208101c41c00d0141c058041750004000342d2084e696070700c8100c55000c80108100380c059002d105c9250252400d41d03074 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 765707482 1250 765706232 765706237
    0x10506030420040c080f0711071202010314010905060a0b041401050c1e0304060e030c1c050709140411041a010e03032215050a0905090c04080115090e2404050f06010605 74
    0x4507414441e0510104900792302480c041d0111000341809004000c0c1424103c00034502c4206080b410559180a2107500c40344a50855000e41000403010070182000c508100003124a50403205860700100410029218007003404ca54036042801c2c400c2c0c55903204400182028000889070003151840680001c0c910301c00310042094660399100c1a403018655402c0c99503901088140320f0300095508030f80080c05070019002034509105804a91500b0345401d0414251400c0500440070211404180020002e00d0141d8010070b290030b903010031030000301481d11842420740185c494103014040c1c4d011041a103081c0219400200c049070a820712040030301e05014000801c2c030907041070341c00c1004104c20881c450011510355a00f190341e02c0358003500348001c100d27220310040d1035211009010007000403690000c0c00758418418410f908001d0442c9403181d00801e0341d005003010980c40e040406103109a0710f18541c4d120a84440003450b05155030750b441d01a00d42160f9200038481031207003600000d011b40d0310100 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 765708732 1250 765707482 765707491
    0x8030d0b0103060f060c06090528051209280b0c0c0a060c0b0a020a21150531091e051212010e250e01030e0303010506030420040c08 58
    0x81c20004180c4d541500e4007240c01c0c0d802200d00003204850b810303001c1261600b007404014062415195603081d400c090f02e108420002c0c1c0c42540c1600e40a1000c2449024810b02140c16128821240b60050500019502483c1b0b24115012010b2000e00a0311800301d960403107028001c0a07a110340e84100303101d0025031b20003503003240f18841c200346e041c045543c070b1180024060080d4410302120813611035010b03510281d00300d141d9507410400c91441001c030403042d608218455501c1b140c4001610400c4c21a599245e55207504801d0050401050048420701c249041e6001818407110310006a01c2c0d415241c0040c0048030030140880d4014a02c90501e14000744902d0b2600744914225807140541c000100802d003d01080801c1d0a001380b0010400314150b1101d017075011010b800741c4030084181055101c540320710016038100090907200192065605440707001003003441007005504640c540310009040e0305c8000c000403d19070b00c00300448110604210b00344802c2d20700400500c0701d6000d0b0384006014840460303 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 765709982 1250 765708732 765708737
    0xd0608011d1c170a020a03050a1e0902010e060310080d0c0506061e03070308130807050d0305090105040f030302010504030e0904050d0e0111060a151508040303051008030d0b01 77
    0x240761040503003070210444000d000c1c6401030015801000100380501c1082100b400c140110446a01034064008121501c64807910200603102c0030600c00080848500500c0e1005044c61315a41d400c21121040c5856601218404080703441011403004850f0210ba00320b0380c80c3c1150020003800a1a54400e02c0c0c2d0066500b5207044401d416480d5400302c48015031400090140d400110100304182422031964189609111055405500010209140144647c829110040e0108010302001440c0054000820b5500003c0a000b070030000015061a0202c0c402410f1113800a8454000c1c0d001700c052300e00900c00b41c01c10180150380c905029011341804c680440018600c64a0142c45180c80705034140665005001000c00c4039469100b51400110356820750305000d40345101c0d8110a40401140c1d1150329801e00c0442c4c5405903070710500e50044c4640010904100762000356009c00d078807a20761584150107150109450f26880c0c01c8030074000403600f0000340c602002562415501c590b4200304117981c001c2e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 765711232 1250 765709982 765709991
    0x9050405100c05120f06040e06040605090708070506040e070c020a15030f110a080714210109061a1309020414090a0e0703020f030f0f150f0f04030c030c02060d060801 73
    0x80704035024481c0842080d40131a800011500d450304c203410b820b61004002d040001d46444240c10a03284c0503049808955094072281044040c16051250000070881640182441400d260000c1d03454040c0340505a021203c040008203124031850340c95141c2500a407080b17440b9911420740c0d2880c50782c5461386001003802c1148161041c80306e442100c1d060401140c0395410680390210445000d01c0240a45040008030320745d00a40142c501d00500c40c021007840140421500e003d4030701444881603002d1040180b80032010003090342c4001002c039205100d41c0c003066462090010040d600c0485401004500b480401d0200301d403000c0084000c0b02400c01caa0b1140d0301d550b03682e050300542d1040d01c00049182c001d0041000141040d070f50507416100020107640ca543c2035481c40758030f071010080207030030242d22000100c1c251414401c2020b810001c2070b59590003d00d404034030a41045000f0b0001030812010421400515101d003015a601603401058248c1c5c81d49075025100290405003d01034955281 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 765712482 1250 765711232 765711251
    0x3020f07120c06180b0417060603060906011e030f030e0120071a0405100c03180807061103071a1807030c0611030408010e0109150b01020c13060905040510 68
    0x107696003580041c0d00030580c00304141000011500c4545546002e141d44000d803c000c52015504005030020700301840d06010307150464504a0b1a1010280c01540a5000135050001c0c1601c082036103810b4840241815150040840c260380481400d64130142060035001d907100d081644c894400c205c0d802d4240d0f10b00c0105501c0030b0140e0300402000c0402c03582503100c00741c100101c015144c2c02d8071680081250181c00c00e60703100c0c085034008108844030300c00520520729000c101500100ba14411691580c518410740b41003c0e403542c1d1301d210034000c801c107204000d8828000b4007070400c11201103907808540440451103180b91000f852005881c0001d100411a000c40607460002801c5022240c10001d11210306140410039204060072480355a45800104008904014240604070710b841003100005680360317541c100f14550988006250040c1800d101c212041c507a4000f800c03080741c080458903448a048900300b242e00410042c3d11510f810b6040c0401c04c4140400842e410007035025902007400103084 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 765713732 1250 765712482 765712499
    0x317070827100c0c06020d0603060518071a1606150602120f0c0a080a0e0916050909090709060605070b07020c010c030c061503060f0b10020a080c01090f03020f07 71
    0x1084040c41c1072503401625803600c0d1500e160000c1c401c5505604044640401c0303a1240c006a030b00100c81c140c8a540c0760001001013140c80e00c21954010b0607200543c0b501ca40c400c0605846030176500c41d80001c86801d18450500512840c100c400119064a100b143d2072000d1900c0005005254400040c0640800b0300250150010841081d80c0020805039858103010001c070400d00c0c2c0015aa1924903c100501040090045c5000305030b00003031516038200d90b0082100f0091031150041482d00e4000700172000c0c508158010064810a107030031200d050160ba01c44c1c80c1c81d450b040e2103522808495040000014040d07820070002c2c190a40902801800c59603070300740030380c2d0b81d5144031034003030004401e104202d02181c41148140c400c5407182e88041060750310070889900e02c0b0040e810581d100c40c1c0d14620344802000c248030710b07803010000395000d550504c00c4100203903c80301d180700041d00d090302c00215140005000c0d407002400980c011050b05605449080085d500c4451601c030040510812001060520 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 765714982 1250 765713732 765713791
    0x221011a0912070e09060a1b080403050912010527010902010806090a0906150510080c0d18080403030804021e0d0201050a0512090d0906030603081603170708 69
    0x28800e00203545051484410300c46499024800c0301240d00884001080200f420240740d40101014401131900e0f0408101040498000c40b40078440071100501c07a03400c0c19040040300e035206405003001034607005508003287c0701c4030b01000350b01465482c00e020407602e50380f44080301502e0110354a02080d01c0491030610b6007290b0208001902240a040024545140004400d540240701c00c0c03000c0f40e01a4550b840e00c003507070580c0829043c1441c009a050055091452020100d4222494252818101a07180007024446d010340716108030b449120b281400b18488011501e10750b40648899030b44d50307490400611003502914100c1c41441585501ca22a6500c40010007007618024450a8040c0b465801510240c0c800f007015001c0c4942440301904108844080902c84d004141c083c0120b040d150030001c10300241a0003031028580303050810300c0841c205000340d9020140ca08100750619030300d03040039904007205501000842d07200104106006500c151100c0c015410076070101c90804641980a0602 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 765716232 1250 765714982 765715019
    0xf05130e190b071b02130c05130f0e0604090b0109020a03060305030f0301031103060c03010e18010c09030201080903120612031317010b0d12030b15040b12010807030507090915022101 80
    0x10390b490a8000b40303140c6da1f070040d10400301c13a04086150041419609142c4000f950000c0400208400100012948080032a80c080030841782005401901e998040c000d00c0c040c080c450000f0b50200d1001c20180c0207520500207941c0102c01c59407101070521405000354000d0204030785c8681f2180c0085c019003000038969000f084810302d51803c40c2e003880c1240901c3c4000520100d50f420f85052031003604c501c02e106000c888046507580424844c00d5000160440b040a00b203801da40d48108141200c004459007155000030f0220b07103449400c0c0b40a4a86499030184141d000003900054800007a110b014201014a03042c030980240440780c50842049110520094042d00442c07001080000081c480c0e8090744d00031100074802080c0e8851265080c00c103070400c0e00100d0007600700080c210183c040c10120a0f0060015030000e008981c119030325551904130070b100743d6110355103c0c11300c1401c00c881d048048482c410002001c648071802040c40c0c2c41030703440e01e03142001343c101007100104110340b80c0c40d40c24145 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 765717482 1250 765716232 765716239
    0x60b0406050a03170a3b010509031b270106181508090a0803010b1b07051f050c1b040c0314010b0a1103220f05130e190b071b02 56
    0x86810002012005c1c0e0116100c60200125692040c1010030103444405030311788070031404200d8004443c21010302450200c0954148002400b400c81c00340d4000481c11460175003500100c2600303035000042a61201803801c25600c680b44100c11002d01d0300c540e20850704946455440303040c50b54039401c4052811031203000d88401400401440f4624500940d191900480d0803802c0355101c9450b074039102116082a0000b1200e11000140c079407040d4840d180c1118484420000340518600d04000141404050404046030314071822148020a029100340c03060809000166a8200503000b489580e0001c01035003144103514100395907102d20310038840d01c070000328181481d50701039007000c0e0141c0b1070340c000100d004100b00705101c040b44403800920140c42c8184540d9640c504107540c90000303420358500e541200b0003890b006038041140756241e01c030381100c90040f41c1000403180c104002c06400c1008040d00d0fa15850704021100040180eaa00994415076250369148851000320700d91441e0841c1c00c402c040d50 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 765718732 1250 765717482 765717503
    0x40c0f0f060507110a0602030306150913090c0f1412010209220908040e100510020606060d06051816030608030d020c0102070c080615010f0c1b12060b0406050a03 71
    0xa260042005040a601030381324449030002e044d0002c0c5e545100703500700c1c1c40141c20200500840e400c000c1002c045002d80802801c1c1400111000704420019166614440e07680300c030302c2d110a000207514140c01510383c9140c0800c1443d180c15007a03410700300c5e014100e4041c10b916484543d1000040c401e4901030136005005209540c4a42c030000004c0540c5c0d20310081c0140c0d5451860006440200240700810703e5020740c46451901c1c410b01c00149100c0c1c0d0101d0300a02050360f58000455011654540c0000202d07001605d42e050400b1420061085411054000003c6544040304030017100c1002d12032a82c0b4103500c00000b44001c4c0890940b0500c0c490416198014400340c0d119076010b07005401894040340005040c6401925001c08140303031584080401d80003c1c043c42140da01c420311450000c1000e00f464061129000d03002040c2d0301c1d03240c0c00506007a555402c1803400072100b060000003400006182e006003000d50a21400070040a00b03080c1c031441c0381440009107420b04500100890340c0100141c1c4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 765719982 1250 765718732 765718739
    0xe0a030e0301020408070e010302040b010809070b0c0c040906050405010f1505130f060b1b060705040302270702030d0e0a02030d050d0b0d08030601030b0111061816030506040c0f0f 79
    0x803840411056201c1e4155000c0c0000318811808020510040c800540051020f51460060004480c540014541046005070401600c408002944400c8458121a4603680c0804107030781390038280f4408943e40c1c442e0400c0503600a00c50260840c50046014900822005107004940d80c100c82c034020701c0d06182d0101441c100014902003d207089400c07803030500464413040b1054400300b03c4940d900011b6990f200414440121000d901e802180c1904900040c006402c080002030414011444020320941c00c00e0300c2e00c0b191404800728820000542182c2e441a4105064081d4580d00060401d5664518000e52610009000a65880c5c1280c000d4054041c40c106020102c8459120805c0c8000300c94880b4068000c07a121644038605143c0608486512407c1c00400101076800141c4410f04100d003482a440c3c0d414008a1101d400610440078140900c10b440400c90415503040c2c0d2112500d403251800105000000c01c10720f126074072503c91040807070b8844810300403a01e8903000307000c1c1060034001d061 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 765721232 1250 765719982 765719987
    0x1b06040201021e0f070e1803040620010b040f020c16050603040f020a03050604151a18060301090f050a03140316200a1a070f0e040b012606130e0a03 65
    0x7022041c143c0b009a90505120b00e0500d450008103a00c00c0c050f0020007030420800e4944a000381407030542d00d1000d10324140c81e01074020b1801021902943c034941d1030b0380880303074455025405044441d0000d4400d001880111800400a401800e054200c5000703154050b81d0760b0b1240c440400a9440007482c042c15511680c0740c00720500403103d801c80c2c220303141130030100c04a402000150b03c95881181080c40b8100b09590002c15901d84020140409081d44043d061950f6100310769207403103800f2905650325a6910340028050040c4400103454440c0380c2054100348030001c0f484810090080e00c41a00b804080891401144030440e8040303906614400e20f0000c4c02c0c0f113250a04965240921041c1031005900e10b05820400d0084c0d0882e11105c0048100c2c02a503892030700c1e15400b5040341030520400442100152503403405054941c4125a291a115400d078020315820080b10203035901c1c001c9c20201701a030b200c4999400d030303145803189540e0131a2612580d000c2c094001c550300088003030004501a564107 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 765722482 1250 765721232 765721273
    0x14070f020c0904060b12120918011202121011070b01120c030b090a08030708070314100b0c010f02160303050f011a0703030b09071d1e090c040504020f1b0604020102 72
    0x291b41c40701000c500c40700d091504004203050006480f100c0c0b0342e2150700300104075040c03550303401a250051701c4e500100404804000030020f9035805454448002c502184050304003112001c0b1800f4013490310000050f480704840282c400d040c4980d14208059072078241c038520680040b0b01c01441e92084100620006a60415254000f1b414070204e824411003a60b400700142c0003200c1000014180d08100311059130f05004d29443c888103010201110700301004290b43d4206103000310030303c0340000210380000c440258014010000700c900115150380d801c440050007500d6803182600000c1c10880070a0307519484002d0241241c0d84080b517100e20030f07080403d0000a070403108043d0181a81d03465031120304d071596000940301b48800d41e684100d00070080c003040680b40290b07136868024011003086d60b9040801c00324100b0050000c07290040711b0742d20042549142e100b65013046400900118031880303a07040c0070018082c3c2d244000199091944230043c417950b1000220b5000e40107a01a4980714500c4000160 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 765723732 1250 765722482 765722501
    0x24050c030f04120e3604032007080601090203040c06050a0207050103090609020a03080301050109080313140604120b16110d030c0e090f1e01140603130614070f020c090406 75
    0x8103203001c807840c00001000e820384103420b80e602070380c15148085c0f1100d4142880311155030a00c41840241460386005020041d212083d101c808441d020400c00d8901c20401c030350040c400c8204030703003003907840704041c0c03029400c00c3d80c04503001d4415140109299026100342c40d0390a000f0790080906501d440d0044024280c00700003560019030343c040c20000f41c0c60301001c0002860280c0400c41c1e42354941030006003400110f0380f098103180c005008860002c81039020f42d00440da000c2c15510b2071900b5203800910140300b07943c4407803288240324440c042042440e038052845440288040300c090a80d0000503619001038041c4c00585804c540040700c000c42c00307648110204801c51802181c20810782003c181800000c3c0c0f07483c0c526010728402c0140c07400e0f0820102160050041202d205545409a03240208001d040c103030384504004000945034500c078010901c44285c1140041c0b10705100407108115121042c1e03038140001e06910441d100d0f2500000b0303038a0b00fa40d4050840c0074299140c0d1122030080c8020315 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 765724982 1250 765723732 765723737
    0x30a05042a1502070b0f0702060c0318210619110d02030a2018030a06141005011805041a060406020706081f090b0d24050c030f0412 58
    0x3035505051922100c140030440c9015003220464505000d482d1011082d402c1007102158840714040c88000340e0074081d1411a92124811502d4041610000781a40181109020740c0d00c4042096400709009140702c202e200819120080c0c0054852603003101d030402086420460303400100031480b4611800ca18049148003008000740b81805c4801941d46a03211301003007000c00d07030040107016031002d580c4100144000d92040050018800c8407144100d40a0f0081c100020864044100c4440d20140301c5c061103298403c1040042181c1005034002c502425944000003030718003500032407254050728605101d5088100d0310040b1b5490b000c01c00000e03180740301c040316150f000f0b00e40300da12a440c0c080c05440075110326000751641c18100b410007000c2800040004086074069600000c2002d6516888000d89004040c040307040c05e1507a0100d5020340c4003000082c000c0c5030490300c800f01070700d1100070000002883d1a051046880f0015084c60300c0c002a2507210b0010080303004140001e0049038a5501e051290 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 765726232 1250 765724982 765725003
    0x8211c1e050f040b3702071e020a0302011103070b04080406020f01052a090310060e0a230a021603090501030f06240207030b07030207020f061602040510090626060903030a0504 77
    0x50405c03218840300000f1010259008150701040003c500c101c5540032810041c03407035018103541c0004842115a200103410b211240501c80442d2100b84102c400a03508220f0340c0300306003403519052078194014800e01c001130091050b4482441418029a8040c01c49544141d07850000040036481205a00000018007101088000b5140e18140301c2402403510504000503d245811064800303000010441e40c8c5040c070304040c40d20f120002c2c9050b410365251503201500207503105100000240b164003168418601d075148904109948641d004058541c01e903424404844400041c10a98501e07000d1044c0311480711105e83c0c0c14004e0300b40c0075101c50720307a03104a41810356251030b40c1450800540715040043d4001402e18158108809503002c00c100070340e0280d24100d2158500c1400c6121000000e01c120b0716070001c16006000c542401d406000845030412505944004200b11200d250002c14461800e03895080b10202c008550340e03108202c410003a44c9076555048610005000044c0100c80350f8104 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 765727482 1250 765726232 765726301
    0x200d0e061602011d060118090204023103050307020d1703091b0a0e073b04050108072405071a1008211c1e050f040b 51
    0x42020300e01a6410300e000e80055451500000c1c291660b01c80e52207001003450203043c5031a040011280e04480f4280740c0c81001c64088801200640000d1708003070b502c40e001040c00c1180c2606030709003461103440c5c0886801c11940c80c01010b001540c140c032000d4040e400521022000d410110f6003510300343d03c0380c0c00005606510304034540c442d4005582c060b5031948103500100080c2e04da04801d41d9001e0046505043d00c51404c14130101e2424014075080420410106040d0322840c050900c9000e902069030000310300a40f0152404106500c43d4103510070307030601000140754040894607000366505c6e503564416810591004000d400964000c20040101c1044403002090301c10b203441640d880d001e0389420036401c01c9148610101007640040590350081c40740320041c0d000350f050b640c14042080f5030b40d80e01c45c440f0000d40c940c11980c5003031a00165080180344100200c0910380c0c3c400007591600700f0811504c0c0d22131818004601210010401548080840c0b5010280250582c000600d8480812400742 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 765728732 1250 765727482 765727511
    0x15040308070c030f12120b06030604150306111315020d0c0f0c0b030114041415010903080a05030106020d0305010f060e031903120b031204090522030c15200d 69
    0xc04d0040c2c40b070240c900d00b0340891550088508104040ba14000d01821003c1c0001601d1484058103091003076a45030300c54100c803441031040d20002e6820400c00c0180d00070040c48860182d101c0e1000404240c1500b1000c59462500010100c0e042102d078010310f0350041e414020359001c0001c10b02034031402d40c001c24010020354034503115000343c005480c1ca50303100d515103c040551011981400340c80380b418401036480c51142c0e4001180d1103e040920320400310030040c0183c6402c42c03070340c0010300503120004505404a8100700203604a413170346e60844840d5038000740128225071082c0101e010603104c49000300410b910807082014402401400e03175100008a072004c01442c0c40d000741c00c4001ca04880d110445450503449030120f240e506401820124a9076a00540d051040e400380c0c049003a603070f0340450000020458102100c1404121160b24a045402d0180c0304600190040f18942d000035030142c0e07021424000c080031050f15000a034003a44d82c2c402400ca03550814500316140c940e031107001401060 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 765729982 1250 765728732 765728753
    0xa0207080703050d030b0117060f0409020a23031f0b041e1410080303010e09030c06010e010e0703020405010509101b0c170a02031c0207050a031202060615040308070c03 74
    0x5103c1e900804042038410406000d45803600d6505041c82000329088010260321101c2c9640301d4022550151007050080c0050000d101e9040302030741000100394082410492542c50344c2c021b00d0340001c059050b030389410170556550036100200303561a14079050808031440710b4014100b502c80050000c1401c00800c540c0042040d90540c89003844c0740ca400600c5010682424000e40240c00c640c8180c440700d0a140181d0f0340c03840184190384802c02c40e000001c0c00c003807092054460340500c24094540d6540e407500b0128500e0802c7c05203040c060740c620042503005020f4400c8504030740042c0c40345e80c1004e2104042000980c00c8034a4502400300141ea4500c403201c4100885000c40e1049244440c3c481c1013500d01405964426400d8442c0d511004045001d80d9002442c903945988621071840b4403402513a0490601c10964016904555501c1c001310800c40d940084800d170a0341c0b0f608031055030751400c040000c0902004000c03480800108000c1c004070351560000d15906004510b45100345583c8d030b48400d00caa = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 765731232 1250 765729982 765729989
    0x70c061a011206061d04020424120b01080c031e0c1e0a09050d050313030f0b13170d020f07050d11030307120f1808030105040b0a0b07080a02070807 65
    0x228801440400c00390b82011003814000700c5903008102460410502034043c0c121410200c0384014403400c1d20007140c0c2d0300c0c1c04071006000100c1140d000300d16002c5448588040f81400702c7c010819000c8112040c000520031604074030016503444070140c0314448050041da00250031040000345070301100501d1b01c3c007228020f00400500c408a42e5907850581e50854403e811a0600640442080300029031503000286500341c4204441405403011740703103401031952107902c48411102242c007500005000c1d500c946140a1402150b4104190b600d800c181e103c212a04540100b414080d000003150000c650fa02503c205404440c00511744842c80320110a1500141e808407800c0c2d201c0f103800c0c0358170396204204240325641c0c00011415414405409040c0300c49005030300003020355070361805144080d90341288140c00c5840e502c841000c00c0d2030820100d668001d00500d8011424004110320900303080b241f8404071606100c02c50300313054803aa60500641d0050055908501c46c20300701040301a42880140b008 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 765732482 1250 765731232 765731261
    0xa17070e0102070501090b030a110c01180c050f0112020310080a080c010c0206010e13020112092109181508070803040303080a0203010b18040f09050a0632070c06 71
    0x210481000280f6290882e041107041040304541009420302501c2600e8210143c14000314060b543e11341040454003401c0c1d00c0c07942647c01c16000c42e040ca02009108040540204030901c6160389800c1444040b40f111810140007070907600e444c045001c81540a5a0008428403032000542c0d0703034540c418a0240c02807010b40d23800b00c0015a40f900240d0074410b20030060598000b1f412a5807502481107640800100340780300a40e24000b2410445e03100e40070040d991841400e0400100d0315500304801c0761065143c05202d031001008216801074019403050049880d00c1c051750100c0c030020ba4981c80a03003243d11181c2c5819404810104021000f40090005010094006c40d1a41c1c511700b801407860b075024008035905441080140600080d40c01240c4001c0d5075521200d8160640201190003400c4580e04090210b01d808411001c00a002c1801040350b030140c4000d000208050f106800c0c1d2030f900d00e40e61500c1c400e800815070488a00c0e4820b1a0f802200340c14030300f40000c075548420701a242d085514054 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 765733732 1250 765732482 765732497
    0x5071e03020d0f1817070b070804020f06160809040906020a12050601031802102007170c090609090312070825300905070503121305060a1707 62
    0x88080103100742c1e84440b070007483c28071042c010400507000b00011803d02900d1074030b8205422901803038040440301c00643c451740d80822450070303140c000c1161800b0358080b48241d039103442405003440e0104c00e482d2031440c01e00614519100c1c964444960780e104421150b0415120014071001c50304510203007264401079203410344d084048104200403200c00409140c1070614001e4134041003410500c0c0e0a08650741640c0c03028503001c0000e0107480c02d000017000300c1a8004048031030782d07180401241620844100120000c42c0c074401d03040841d12240c040b002603800881c0d95000070300e146440c05010750022a003500343ca150911425680070300c0c180407501076000c1184c1109100308084410740e03141240c00305050b00181e1031004440202584964003110414403066072102c04144085410402640345140007040000307150301d419921a0b4007849034900c2030041c1010901920010300c02c9601c0d00120b000000c1c5c2140c2031908214186c0c01030346002c000c011656040c6a002d40000c561103000c0c0b07070140c4901c034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 765734982 1250 765733732 765733747
    0x902010e0603131b14101e050c150c1602120a0615050619081e01090e0c0307060504062102030a0f0c05120f07020f03040303050d050a180605071e0302 66
    0x70704c503110341d240c0034150040b0400c401d402960391400100c03c00c4030240c00b20342515004a0301c800b21070012016441021a6016440b07070410024000d540040065a47c4d444514940c4c0e41460000c03203030100d60640070007041d500045182d04000202d48020179211019108403a00703407410400b16000c031910b61740c4515518401052041c800020801154a41c0c5005245a202a1901e924080150502144102107801001c803403000b82c003a00c5240c1207180ea5036039200351010207882000c40c900900e00540140e0000703401d0200d540030542e01b207521803a16280c03525504480349402c83d0b41d403030000804110940c410b0b0041d400254082c080d00d400200f030080140b0400001c132200421620709012007000072807150030008803210740c132602038030014986689848040e81860794184d080465804001004410150800068100b50940d02c8082065946142848003250403204040c12003c2d4080400b00029805401c0340b82d01c4402403504410f1b2000c00c90321060b480080140001c0801d03008030740070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 765736232 1250 765734982 765734993
    0x30702060108010f090201020c0d170703390b0705040510030902030115061b17070503030f0903090607060f2009150906030403050f1c050103120206040809040902010e060313 76
    0x13607140d1010743c0000c00c0340315102e5001070740d0b4020541130240038166034502c01040c4006124240e500340740681c00241d442140346001801032082404200500c00f11301100d8420140001402d80b0700382940c10010309252043d220500d1003107000381104200301c800c01010650340c885030f100310540c10160328040346d010304901c1014291401c2e1010480d0040b43c141080011552040303400c81400c2d14007a15001d074110f94141000c17042800c0c0451518140d000500d082008000070046100303003c0600c848482e5100c1c600d120b0b880e4401d600802c1e61183c0140700240102c0d4207a803198103407103404038000403040c108601c1c200c0c55a413903040001c0845000724804109007061003074a0f040c05580304a0b10303c0c4c4044200000e401d804081c00150401101050300b0400080000c1201c11110801481044024103c0391a9003d024240401c6490b280c0e82103101501074000501c0500603640031080504005943c001c1c040100540402681088240b41c0500003030349483d001140110701c240c02c07810f061f14150504 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 765737482 1250 765736232 765736241
    0x10503011b05040506090d020a0f0e131a060f030d081f05030706110703080d060311010c20190e160f05190e0402120f0705180d020a030803070206010801 67
    0x120180320080010301c0c0030842d407040032181510700c2151001e032034552981c0890803a120b2410001c1d0401c21008000c161014680c03d104211000c5891360b9060396520043e241110510390f80003044480c48019030132041483c090002e510080203442c944854180c1c000082c41c005545007004040b4851200b40600001e05041e03101c080d40080101d042d201e0710b8131001c25a90849c80c030074201044410f01c031a0344125400c0c400e201c0119000024903841e81462001040200864441101c05c080b00c4400c40c40154010034010311400d0300805000d02c017005075001252048a803c80d01c039030200d103401c1d080f000302400002d1600070702802d181c03115242c5440800f03247c0800c040d070072500c02d22044189032f401d0540d105045410f01e100702c502c45d2a036072034940310541310440481c5c00d081d4064004202501c201c0e0164000380d22a584444050b40941c40d813060658491141449510121400751200041414040d071040441c07131028084a640d255291642c6c074180c0c000303545050050300480010003052109024 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 765738732 1250 765737482 765737501
    0x73b160908011a0d060209030307050127080d050415020705010902040b0a0b0307030b0103090c030f0b070302031608182b020105100521030a020a06050114030a0b1f060801050301 78
    0x81024403106200c00101c220f00145080c802d05210801d2410017500b80c05840b51400081c048a49500140c5400c60180118206c401e4180003030410880c0d0441b10281000c2000da00b00041c90720b00452900c129019080090041e034030030703510b001030f507011020300d00c020690580070b2000056030302035034810031007650001c880e1544241765403082032000c17003800d900f22500701d0781ca4140001c0c80510800144c1c06010300b1080a00392074a4100c001041c843c0820400091034420030183e0f4850390307074107825012800306594545070f410020640301d02050042141d10780110480c580c11309490291103c9901e4400550703480003950741300070420126103200c209281d480c440103000070300152500e41440c0301e000a1610810b0300c0340c01ca56807a0075031045948560440c000e140d1060341ea5036405070002a6903a00100b1085400f145040c0c00050301c5403520509443c401c0d0014060406414644c13a8804e200300042c024588401c0d16400282402000e40c08020052009464101880d89020708050071107035240b1 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 765739982 1250 765738732 765738749
    0x11b1701050a060e060703110706050307110a08180d020d05030915070807110117010602010e07080a0c060302031e090601031e050a0209070212040f1403073b1609 71
    0x2020b1120b180c2008400e041d4500549041d80c1b94001418200c804a280c1700014256001c0c03902d02103496a8040020742c422103694541d40f40141e03580101c25520070000c0b5011b0104001441054001c4480c0398421000c8400186001c3c0000c0c0150001544042810006c031500d51000401404a060507c040042900c2e5100d01e1810f004c1c4645902500f80310380f980082c150300300054807001c20303802402610790032005003880314881d40c0c4a220180c001e02030080118801d1280d5500000c110400282101e00141d2194140503a2843c04205801035000074085003255801031005691486440024a110b10310b154000c06440d451814810034480880040251040d500054000807505c00103440c103009038152110200d6955070340003282450202d04101c0e43c04000082c0c0082d10302400182881070312190b513511468040b2440070940da54110b0711400048078000700c0002c7d05100e084001803030404500a52071100034400d161070401403021182171031f869150a4000d6003044d4020b600f03d01821020 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 765741232 1250 765739982 765739999
    0x3010f08070602240606121008160b070b13020d0c0f050108090a030806031903030911030303092e1806060f080a081b0d020f060906010e0a0c02011b170105 68
    0x8400c0344880c0c0e1100388104084d0484513002c02c1680e01c443e03044850040300303005444110b0070500a0040c2e8444548244507040c070074002d034200b00c080492000e0313040350441a012440c2824179900c100b000341700203000b4601110100708400150303d40880510748103110300e034001d011a05050b99082d480309180c000504200351041004000c40000030b280402c80e0305400c08900d65581c0c0000245003d0b031100d5501c1e2011002440d80003096010342140000b10311801501481032902d80915950340030807200ca40e16580007105403200010924160707110300380b242400c0920700e4810223005041c1c2d12405400201e006000800e50103001441c0b094a002d05020001c040a4138a0102075650f501c151070806000e11a000074407401d80e02c43c5803400000701031120151081d403100d00c02c02a444000216001840c1d000300800244080c1004c2000c1d030607a0141d0f03c0d208007980303034507400da001454007154100c01e565071102c00c14880c0603030110b90341040300701d983c442d07442c10034561100340c465206901260040c5640c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 765742482 1250 765741232 765741253
    0x90609141e03040f0b07050a020402041d150a0e07021207210207050307090c2106030201110f06130302031b010b270402040e071802030f061f050c010b040203010f08070602 75
    0x113a0203820031601002200c0ea2030342141d0825504040300c100000754003920004000802428894402d040803c180e000032816a031002e1100010b0154a40c1c1c803907100041c95001e200c1101900c10a07a0406000d1045440d14180c0d01000c00c1c440c5d2100c142070b245500c883d5080002c1400d0b01002e40b03c260b0051018280c0726103888003080c0d941071b4034051101c580e9115808201c01510907140400807400905c0800c281079031042da214000c02c0e55000030303030000d2a104e61901450030000350845001c0100c100401d0380c1c1d80e84030b158030010918840d0440c2140800c014a070214071460749a91000f205003000000c0c40041002002040d05e1900181e6644030144e0241d00c0c07a0001c100c0702d0b03946c0580c058070081000d1103045420b9040c0340080d0401c911000e8090b072560095582c076805036100f1003400c0010039090701da000c100a5500b0014a03485000e0186684007149648200301904110700441d0000c03270700300b000e500000d0036600260800741e078242c0140d80802003e1070820011005102c58006041c0c640c82 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 765743732 1250 765742482 765742499
    0xd05071d1c030806031f05010e061237140d030c020c09130c0311010306140f1e041a03010615050406180302090411040e031606090609141e0304 63
    0xc1d01006018421040001103290f1800e006d0304010784143e120130340100b040e52406030001c107020b01a00317810840300c0001540c41d040810740410150300d48001042c01c0081c6607181c0d042c43c90201da4049504060b00030040003103c0d020b82070560140300c2d08401e544009594041c1c2d107080240c0c20644101800c2c00100003051340c01007080f4074031280c15100040b503955445d80c2d4201c00090410014820004403800005101001d00700d00c080c003000b640e080c8403d0341c0c1c0340080854003074036140f40d43e80407903458a010410315000005281c0c810000d030280f40182405c00c00981191910309446d060390820b640d0140c07492a081c8601c50103401c2e90b107000e5502d20100c003c010814040e82c000c40303040c4120400f4030807401100800040045500500e00d213501e24151034a101ca002c0305002080c0a2030800e0b900380c0a0183c0801590001c1804014070051188281c0355600034000015081e620340d90740f0000b030000325100340d1201004525600043c003102e4802c0c1c205007550b840c0400340041e90380003407200303010b140c9 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 765744982 1250 765743732 765743779
    0x311120702010e0a15050d0c1d060a200a05010b1827011d010b1509150c060103050609160b0403170919080d0201060521030d05071d 58
    0x507020b20300341d404450704038003003003416415401091448000600c4009016442001031204d0a0000030a0100d00d9074a00c0541c2e8400c000f0f480e102c032a04001161001e28240600644215000c5240200800c0000c21a803101103041c15981c6140d50040d00c1e4603401d20000340984610107000b030340c07071042b604083ea15042d500c400142480c01c90b070701c0c0e1580daa00c1c0c0c0d00d1140018001d00c00f40c0c1008001c0101c821115008044d841d00c0020502e5080556003090342c9440c92503919070891b005501858240028204031705600c40035900c031100a42030100000540c1e040043c1c40c06144218001c00d00c609045c1040c80c0707020a44803171903488440003a814407142302a841500c0c04c0b641e04c041c0a51800c0420400f8039020302844a00380d80292181c0c012201851882200200b03d602c90300c1940d817040ea481200b242622042e004081d0040308642d412417a60400390384142e607500c0d124042d13034148440d841034442900d070140e44240c0014800d6028030141c40c00d00401e00300c483e0b0112a0921038882040c050f280c41c8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 765746232 1250 765744982 765744997
    0x4b070807020f0102030d020d090c08030a0e060a05041a071a090a110424050a292104110a0f0e040b0a1107030c060605030307051209180112031112 64
    0x151500e10716030b08641d008100742c8540030740000b81036480c5c0100c40c0304070004103201803040e900300400303d90002e207400e004800ca40064902e43c2d50405a45566014403900d503005487e0901003007002c0200242003080000c2c14001e00d11306d1156540d03202e40c681061599014000f0711702d40d110b1031110030700800b0440080c5860406500403039182c005c0420b80005801020032407a1009030644440404542020800c20101550421180c10b100143c0701c06419101503000850400e044000c0800d80200344c0d800000b070145603c11750741a08001c031201b04504c034900f4040e20110381c1c61114050040b110f1030024031100c09450f24202105a091403c81000d4000101074400b0f011982ca2a000c0789001116420402c881c0160301581940d43c3e03464035005201c5410400d0583d00e00d458610045000d15000c82140c1c6002d03001002000d40d460120542c01130b0b5400307103040c1603011030344c2c1c1603201120300b400b0b04940c001c11845a00e5904040d26080291000128107101c210940018400000c810b400405403800d0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 765747482 1250 765746232 765746239
    0x10080f1b03012c0a0905061f05010c02041d06010312030506060706020903070302220e0d050405090a2a0201180b0109090614090c1005040e0c4b07080702 67
    0x1080360040041000c20101140c2c101e004030746200f000131a20054004001d451712801c2129074581d01c83c03c401314001c2054070903c0c082c90881900b0400ca40c4505108220b490004100040010007008020390b4135a501c440000143c1090004005105041098071a5816207040900151600c2c500181c150701c5a0b00c0c0081506502048280403910100802d03809940c0c00740122207029408600400d0601c441001d0480f118200022a94007000209208112080c03036261541041e08010400641040003813503a022280c3d40d003040549803004100e4201e41e960100680c402600c3c114030020700751556801c9507240755159009910000b074401c60740d00d04403501880001a030f072290780340c040c000c5d00300b4110340040202d843c41408006080480d4804821208440011801c0d40d81c1c0c1d030554650189200b5060004200800070f100304071090000c000710140c1a800e01000e422025503101e03000501e04010b007503050340d40070402c0d411204400c610200c0c0004031540c1c0c100038641e510b049091040c020300900 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 765748732 1250 765747482 765747509
    0x11030304080f070302010b030d05030a060b18090414010504081e03091e0a06050c030906130b04060b01031b030c0305072f030720010f0807020a030c05070510080f1b0301 74
    0x4e05100713601c00c4240b90802801d03141c8404020314014440e4200f40c0d050511140b5060001600071640c808588000800e81070344e0101d4140b00d0100280d6842c0244260341e4088061100c1c0701e144c00a20890f40b0a51140d003007103445900d8a080268100b002501c1c9141144040060040907800022440b100901e168003e101c0c80254401072400c1c174002840007005a400c0c901804a09103a00c40614410746440e004c95000307075511183d07a800b8455044024000180c0000401e000c00c109130090880a041070401062102000d108185075100c0c2c41d08200002c2e035610509402c0c0780e45130140a401494170314201c40550808008402460300c07900030354080001112005820481c00e00a503074000340c10520b000713104003184000c80711000c40014068009400006510040c500811060340078122a41c0140b0380d43c85c0c40d91b0255121801d1803400c2d102072090400025841d81c50002c0d03c0006415513a0301c615034207003241440380a0b035003d08045400014008803140b50b04402064a044442c04454040d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 765749982 1250 765748732 765748747
    0x1a0607021c0311070e0103050d020102030f070305090a08040e070e0a05030c060c25061106010303170a0b03062a03060d0b131e02010f0905030607030c030b09130311030304080f 77
    0xf14060079403010f100c0303103006a040001d0400f881e641030030b049900442c16640b2803c40b60300308908030b11049920081c85210303100840c1189110703038003083e07010250008035401409551180b2007650071aa00901c4040f8a020420842c95404040080780d81c0d02134980701c07103150800002030b0b180e4980002550180c00042460004100d0400c04a0340038041040c044100c2d01c030960246584006070300803a404a40210b03419491500c0c00a0304a04036a0182c1c3c0701000844641a20b10320000043d01000d005502c2d0008404165418070940340142000405c691030340600000300700f03156a40c0c20164540f90700500c10401c498680f407074103020180d40302511140c44d40d590000c01403c1a120000900303038840007a0200c0c40c5d101d61482420002d4002d03240d030402d10855a10454020500e80901038054010501282070a4000d41203100e03a0300060501080c11a100c8021502c8540b085a90281c243c440d564080103054108007513003464000d100140d49186031507141c0e11100e00c1203160000c4c3c03060000034041c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 765751232 1250 765749982 765749987
    0x2030615060d05090c010206090705010504031515090203160c0210050a2001021206060712050a0903080c010212180303012106050411040c020705010804060b01211a0607021c03 77
    0x162415540b0000c2086542005040c01342c0d01c038030000509000d44547d501207440c1c0d14001a481c411182c4c16529246000d00315690b084c01485250000100c140c2c075600c000c0f08130000003100c2d0014042d03d02006807030b40703020030001916500c41d014010038850a18040000358845d04041c2ca000380b86800c204d03a640900910803070f1403010350500c1d440e11062013061044144010f400900c2c01160b6650007003030640307850007041140c6c840d6600c02080030780b4000c205041180628064116440141000172002c1e035240c80d0110745500c15080c502a50754009011200000400b0f07900303802400ca0310a01080102140e0015aa480b06014452a58001e002c01f4038010800c0025100303a40d41c003103800d00c100d04140c68503010100e0880700141c8518145030500d0306807440010381d40c0403188141d568052503101ca440c2e000040c00405803082c10001c45102402040d1030301c0c0c3c880b0b0f1080c2440c00000401104061204e5007519240e00d140d485a04100600c0c00540c0d14041c2c0348111400328143c2882c24545481c06 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 765752482 1250 765751232 765751237
    0x60b04060e0c0c0705130b10110c090a020c0d05040f06090605070b06060d0e0c0103050708060a0e06060d02040b040906050402090a0e27010c0207150516080c100203041104090203061506 81
    0x10740e6100035a02c01c0c502e000b031b4072508401000d107016125034903032503618101510480d900301880d91251788a805a90002c1c070b040005580c10055641005203850810140641814848540040407d000080804c0030301007c14520b0b000b032000b4a007096095040280080c040d1040c0c0c4c1707010b465402454081003441d51010b0031200b0f40c840f00c49080010940641c05135468407425001a808039180a002400b10346c01804200c0c0b26140080c0307c1d0b15520b0070070024502e517560140409422803010300401c028052644002c00c0605a403080560301d940c5483c0c0d051040d581d0541246000ba0b00522980d403494a605403801c082d2900001d5000c52a660303100c5850001c58480742807504500c9080a8030050031041d403100f2a0386855500b03407280182c58800e0b594043c0c6003410310310300107141000b13029070920f55912102000d07032003142c0b01481c01c00300000c110b280c9241001c3d522030b01a400000d020400085080c8180a80c006403000d00c01d0003660340004c0d40b01c0c00700070404403580c04201c4c501020f5a848404 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 765753732 1250 765752482 765752489
    0x20d0c080313031a1b0c01060f0f0e07030e0a030509040b0d110a080c0a090e0304090606080f0a1514040906090f030215010807061209120c060b04060e0c0c07 69
    0x112522500203541c0b459022155200075034078045040072203010702c2540260070348070300522003245128250300144907495038416112044955601c00012481178000f00040380100020700940300710728101b0740e464507204800380c240707028540f5280100c0c480d24800300d0142c02ca0b540509000742c6803d50113012902a00680300d2842d44160011408001c100c1d00300002c410000007607132016039250325181d00a581d0785240d000b050340420004410800c172001c0750494031284600d0015030307003001d5803030142c0320603a440e58000901250280d010000700840700f8220ba035014040b00000c4c01901c6689104540c02142d074011070b0100f42c41e808580c0803545854021900d081c3e4000740c01c100364412405c00b680b8031103000c10110300500401d035280c0950080e6419181c1621130700c1c405002103d1a140060744e10b0480400008002ca88800c120070105200b91b6420b00c001e601c54841c001c1110f501c0c900f00048070b00f0007010600c168541790040c00a502030031009070380124182d0223180d892200035440da240a66590 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 765754982 1250 765753732 765753749
    0x5011d090a0e0d020d140904020405130c020607170a0f2003190506060412110604120b060916031d01092f0609190f06050702090108010612020d0c 64
    0x1401d010407030071603910008002420ba81520060b060000c0100d0b00d0b0946442e44030002068102280c0d007048048000380701c202c5008000620301645d8001041c8501000ac2032044495510140c4498060301440b89a074040303114603010403004041a00451100c1015100200140d6521075600007030313580e68088030580307420070092910500d56030001002c0c0d90040300d0302ca10f0000e02802d2140d0060f81030054078025000140700d40d0419041200743c0361341750030f44041510508502c40f0380401c541c1740c8400a01c0901007059885940801d0b03803d042e0001a00988424002d00307403403042120700c01c0c0106d07800301c080c0d6062602003010f1414001078007010844400280955207044d0210041246007a002c003c0b000182c900031200151700e4224901c2100318044103074211904204248591501904614140000040c40d84180b40c50750040300e180c040740d070003402c00301d80002550700c00c0d0302c3e240c03034131500500c1c1150007071010908220f804c1400c445d169100900a1424205110402c844011810040c0408a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 765756232 1250 765754982 765754999
    0x3090b19170108120c070320010305090f0c01140702060a1e020c01120b01110d110f2109120313030c090207110f0402070501020408010914061005011d 66
    0xc03801400100c048100c0400490000d04204445030400125141240e42410180c050104111003080285e44404910002030041c07840100015208601c119400f0980441c9040c407008148005000c03542c001c1c003e602d203075100701e540000295001030a01a012000e181c070103621074100078003844500032010000d52000c2e000c20f80000f0181c0c03000c6004560710060707074092140420300c88103036122280006014001a242c030345c03e0340f080c181904169070640041c0f41286400c2451a02c9034145046c03165034000003101d0803611810741c18200504400c005080001e0040346c51040400f448421203401042c0b0b606070702041d855219665803850491841040081e05e036190300f1a102d09a2541d078a00040314131011610307000c0340c01e500360304c243c600711075004203618001d005a40c03c11003c0c0070300700200d5902580030003400c000200d0a0020300010403011002089104140c50801594030399000010019170100c4100640441a865030b00103c52003801c2c13018000c280201c50b0380415244002054019940 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 765757482 1250 765756232 765756247
    0x201090b04050102180d03021203070c02041401091508030405090a02070f110907030207080d050c0c0a150b0306070206010b0f0405040516030c020d020705120a0501411303090b 77
    0x1034006009000c03004905c280c1c00b40440e4204000805204005001640001c00c3d00c014080000000e64010f4042d041403c00301102e50300103000d6030041080107401d040d04000400c00100c1034010a84030220746e6000308403036820702004666074003441c0305080c464803440c80400d0a89519a048601c4c0c5500141146c07100d50060511030706040c442c1c2003a6020750320040000c1c2d203281c4079100792100c10358400c0e141c51a140707a07803200c2005054081c00c0907052a0007001000c80e0148200210050305125490f04e8004050b0207543d00c040b00c0511013028080d421200c1080b854503408108039054441900803d074440f26808504020b03130249402003504503151070305125441d501000000d103442d009907818801c043d04072000300d031038030241481c410269000d054184007500c0c1c1429000e556500301021144a00f00c030740c488609644004100481c100000c1100740c00b10402d00143d2072001d004041c100c1201e00c0046441841a20010588080503084403d80d200700f5105141c85d42c0145024040f15848186 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 765758732 1250 765757482 765757493
    0x10b0f12131403030f1e040f052b0e030708070302060d1104090204050906010c0c15110d030603030909050c040612140108030d0605041506050f1e0a112b0201090b04 72
    0x51716400d03196546000010058000d01d9040c564140f4030409440c2c0c079840e03075034450362841e00340002110203004520104090003512000c1107c00034641c030190b45108417181029100302c400c000213034080c0c0c004860900408100284440449a05071503080d900c03510182d902c0028484030040303040d0307040000b07000202444241c01400c1078880c1150b455083d601e070180103513001003140318000c100242c580c0c400c0288181002800001c21058100303801c00b070440d1002a418298100c403c517011942c1c444090007855806202d000151258010810141c106204901c007d40184e00c40d013420040ca800500c0800c03011030308081c0d01003401e040152101e584400009489070450108400c0851500000180900d850b008140060701c10010561001e2300740350003184e8940c003070181c07100046003c00406903800300d2620040d024400c2c400c105e61302c94002010081c90080d100d5550b00c0160710200d03d40c0c2d005880e8008000c1d541d1306100750322502c0981c1c074106034054299214084e110b42d5252040100740705 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 765759982 1250 765758732 765758737
    0x622050f10050c090d0201080a14011d0606130905070c020603040b0105091303080402040911150901080a110a030906060504020d0203090106080312130219030602070b010b0f12131403 80
    0x6201c0401401070f590b51841007812030003074500680d802011030081c0d101550148140070f4202c0e81e544808100c02c02d190340008280c85007a84086000c00b940b012078600041d603446080d4021404484a500d481d41a010503e2400d085000d104415980c80c4041065a0b006540013000780d54090b016640301c3ca4a070400300302d500000d10a44d4010b00c41440021115420b00c90103e26460f415251120340ba00e0715000e002c024072600e002100c450107464811071282d038600b85056070200d205404150f664941c81300040c600c203006056011304506140582e0303400c807460420364440511515001960040030704154028003100e500c409d4015200062010120500b500150300c40e0049600905c81180d84145040e6288101040b540c001006080071940300c0000d8201c4403109400207000300e44007010403040c07041102c005e51045a649600040c400100118a0f48950040c600c08154a06068589a100c2600d1081c8244081c140c83e0650005682e400c590a6610b01d69410480802c1c1c0200c01030505550b81c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 765761232 1250 765759982 765760003
    0x1d042a062703031106070905280902040e070f080403080112061e0c031d15040606030210110d030b060a051c0509070e010f060509040c0c12080717090622050f 69
    0x117010b104001101c003400b9942c188120f520103040c0d0190000c901c20b45900d0603030200ca1000c01114003840016108006001501c054168103c0300fa81c2410900f00c007030012840c0303801a034240180c050802011035041500c80c0d0450382c01e90201c0d640e904031441c156004181c00400b220404d941c01c4d0720a52030003100d0744540d0f001280c0351010054507070156082c4800b0220131028505540c002080e0144026110704207a801510402c0041401a120384c00502042580d002d003500043e05249100d000c00e004004060304000d0904040055a84a802182076403041040300c00c10720800044414103c1100c440d1071030300181c8014108114204100c0031038417055280f280c162612166000810040004100e51088031200e450b0380c3c0c903013041c00080c4006004c10024400034001004a41000710300800204100021966240a0a03140c10007014200305035030400007840e444a00f080260702c1100041c00f541007141c1000101480c07806090b0003c0000403000000c1071070045441041c0c030340c1000241170282 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 765762482 1250 765761232 765761267
    0x13110c070905011406180d080f0f07030816120e0a05011a090c0c03070318030f110319050c12071802070b06042c03041d042a06270303 59
    0xc0c560908100090041d06c1d2203403143d0000182001041c03a1100c40352410500c6800702c0e5060007180803150302260086481304180d030a0008511041560185040d5805003504108c806402c01045001341003031115000200382d00e0380c5a07810050078400708050b18013103074854000c2c0700b160703210000949074600710030030240500c1240c40070a0440f00c60905441d540c0c1c10500095003026000d880803943c000944e407241c2440c140e0b088000c0003180030501084612405a41c0902144c1001400e040c68014071442c0d80f941b0702c07600c01000c000168085070f1064182011900800d1440f00011282d00385907595111050174001092000809a4140c02030420140a00500040d43d600d030014030081e5000103d4207400c02d0f981100c02030700140d001c2c0320700d0f006540c42000c030ba003840e4039020015210341109031250048240d8030304200410416240e541e00351500b290080402200044484191044900501d030031700607a0f0000d0400825404958204103900c54140f0501a90340d0030060415401da4010614 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 765763732 1250 765762482 765762509
    0x20d0e01050105030604032f0a03090f0f05060c0c0a18050610050a0507030e062b02090f090405030c010207200f060d0c020304152a0213110c07090501 66
    0x1000401071095504a076405806007005071780e2a03504843e510804d14503000100d881004540d5505885501040b68000085c01403003462170314200035000511580c440a174130071a90b207082c4510661091510110b4900b501c0ba030340c9540035554800d051640041c0516040302e100c6500062942d80c074001314000143d2003d08006a856900070300000000030b00761840414000c10249140c144681e004000307043c06072604030215200000083c000d03501c01244c1e440105139500f4070358458a0880480075403901c040104500d0101c10704041345804840303400840c80385101400090900c03d051084951030340525000b10740d281aa0300c4c009401c0c404400c03035100208440004424242440c840e0804820001882e1a082c0745d9070410400191201d44138480441c0420320000400043c3e42c10392842400d03403038480508943d007100c900003410b0001c5000c6021151481c04000158480d032202110801c0e0800020420031018450300f0414441e507040e00380d1612451000003002d04095010905942000c040900c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 765764982 1250 765763732 765763751
    0x8072a05010e060f070204060602030c121206060a141620031f090506190b01050717070f0b0f07080705090105030f0411030307051006050a061b060e010c03020d 70
    0x26566502803a4045105045800d606140c818094109140c0701d05489142100c07590100e0180ea480d54403100c09170340080742c2c03081440400d2085903800f0744400314030f9007800301c1454134000480c03014140d24001c1d40e00007a0148400e104e02c0340b001031240343d5107043d640e421910300315098595440d9070a03940101c400d0841019200b014440e40c0c1c2c51a0010010800b400f0051070000808a14036903048000b650b80c15020000713103041c003020788503240c90b2182001840c0003001e0701c420380fa41c400701c50303041003000c200240c0004c0304142600820302000d841191244030625040c5a401440d01001c0c1800c15541c0070031400f03114900540d840f611807542c3d40d8004c0c1e25501e4050305d90780120000203000c65820300008034400100301c042a8014014503031609200720240100741581c0c001002550340c1c0d00b02403000c0c0c1a54801c7d0040b1001807100b9a41c40180a00d0b01038018903001c2c00c0d071902c082c83c022540394082408907a41010840404690082004581c0b0402c090700a5100302d04200e219800c2c0240c09 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 765766232 1250 765764982 765765053
    0x90e0a110f040801060b19031e18020a09060b0a0f020705120c030c010203040b091e1203220302061206190603140c0f0f16080d0b090a050405030406110106030807 71
    0x403568005a80302c0407020a1f000d040903405068142c080070b010590120821100851500408a0a0410700184000d0411a005010b420340150300045490f40c10300e00d0411803038012504449110301c152030509001d40360700c04202e00740402a8800e84d8003032000c43c0c0405400402150b281a1a0811070440d000d18030f0580040e43c80e4092441840d6a0040134041d9000a00306411500f403143e034411941c8a66444550000300c40104610a40d506c691001c01e9040034005400311200c4589200800c01b45403510315130024646104405d0000a6102401d0101d081e5460707000c400e124200c070260f2030700780c099100c0c2c5d0010000c1c1003030f4042035403119150700401c1034284000202d4400d00320201d469440c1c108a00c450060342d6104449040c0001002049503001c5113448010348140640b1820118404088a08111401c44040c08203010a07281c4818070002070b0f00001100d00f201c805052100da440b0a000f00c5a0040c2007070b51000d80302581c000b0b80f05041000780505070b40c0c02143c400c170a41c10310351140321a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 765767482 1250 765766232 765766237
    0x908072c09030d090203030903031315020a0206030a2a03050a0f091e020109030f05010b0a0603290f1825080a0f11120405120a090e0a110f040801060b 66
    0x8266036400812400c0e510007181c2d0002001300d07001030112403034040c500c0b010030301e55481208415501403840100313102c8503a4189100209480e81c0c40240b580942daa00059018480513114010040c2e980282141400c420008404580c0e810f00e000400c807040054050090403040740e035500301030310b0320100f801c40c9140c40c0f00720442148c200500404c00c5d03880108a56500d410128160b05000040d0380000015408801c40358644c0c1c420340001c02c00c3c1c075081042c4041c0000f5a04030000b41418240d030074212180c0740d1003412706c0010031a0342203400f80c3c0d41800b04030f110f2039800a0a422894891a00306c000e615003032458016030b02c000c28402072001c5607003890b41c07a03100303648124002402c10b0082001900300e07400690308422602030000d1181c200071074000c240d50000c10820709221005040009016052001804011402d2809403402c410400020040039560052642581c51400880d441d403c01d580301500c5c14080205450751001c0e41c401c010441d0304584903000da25030801c5001718a40c0c0c4d10070300307 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 765768732 1250 765767482 765767491
    0xe040516080d02150403090b03010605070215160209040c09020d060807120812310b0703020319050a110424050a09061d040501150908071d04030908072c 67
    0x19000c00113000c03071491034000000e00254104050030501044021101d80254004e2040b0f44400740c0d100d00a105220308142c05074214841740b802840f0181040c1c1c1001e03c3d411115a0443e00e00c44c007a43c076854098000d5400c0e07080011102d10100f800300c0c880341c2580c00309066402c07101c2181d549540d40c0071301c244001c60752500107000b9541800301451560395111007070307040170000010449404681502d0710034000c4c00c1c0600300002203162400010300c601a60081d0300b05806140540c80c62070180304201c00602080c00c1c5000381a40c1d000000c4030740e50341d9440020310080504030140d80d150342e10500c050701015000340312400d2020b101000c2085008a08803000001c3c103880c1d2120403413501000780d03500029070088100d2010840c0d499801c940c3c1c0c900c10b0902030b104844901d44c030300d00201030050001705075820141e03099104c00014400340f00903844980004101e045214050f80d180d00e81224011441c0d4001c4000c1d101c0d01001007554011010444501c90115201030008400c2c04e616505000c800c2d903 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 765769982 1250 765768732 765768737
    0x706030b0a0e2203030e16092913020d051302030709050f0609040219030302100e070e221403091305040c0509090102040f080106080f030c0309190e040516080d 70
    0xd8000c40c3c2c1c000c08080b030744428000c0c20b00107245109504901e0a059401c80303c90744c030004403081803101e0f0106104000078815050120342c0003000c082801c0d0250f1003a030580b184508401d6541c2e1440c625107804684d244000001c06101d10300b4814a00c032602090700c03000302d119008042e00400c10034458401c4900c40c01140e403540c003d9898041c1445241c9002030300a0f42c00589864801c5142c0c2c1005c1c110750b00540c400e90061961400034240d1000f2128481c0d8200003d80001804000e0343c2c005140c00c5070000512012925054452508125002c010f100c006100310000301d00004000e80202c09082d40032025619404108401c942d144200c410880340144100490720040c030450030304040d130399440785c8176000052a06482c2d6000041000103540300d051560745030300003801588818400700c2071304120280114280000384521540780d006514800c2e00031348100703a801018425010000340201030f41c03468a05581800d0400135140c031010000c2e41e40e501e4070f10200165180c4002480560141c165 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 765771232 1250 765769982 765770011
    0x1051c061805010203190c0527280f05010309080a03050403050d18020315040c060804020105070f110906100f080406090b01180c020d050306210706030b0a0e 69
    0x564480000704050107007050440507090400300050003d10041d80074130310341400c3c100400d07100038210301030351120a2044100f18042c030444601d050308811400e01c22403d44072465420148402144a880c1c84100e00c1104c42c0b52600c5990b62001d0014554050307405403c403c00721b4603204c10054055032400c0400810020041010031030451195022640191003850102e1400310317034490400648103800b1920315141c5d03021202100310300c1c04103c5c002c00b8907c148000e2080d860240c60307070207c031801840b03140306000c031050000c4c04680c840d0b800c40701290341c0306410343c46445403030034a810b24504110f0024015000240030135224a008100101c1000c1c095480c0d00d13800d03528900454070080090821110551142c001c01c00241982c410300703010340052010b40150441c4000744805139003003a223508003550004210f590100d0b034040d00f12680301500350760030a04c41c0c04050506002c0c00d0640b2010b00c05001e802e4001c02c10580c190082e05255008450655456450340c00b022504c080c29200b030406030707100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 765772482 1250 765771232 765771289
    0x4030f140c0a030311010915060e0a0e0307031103191e030e0c040b0a08030a211a060306030f421b040e090303250806040e0705040908120105 62
    0x5d04540032400402800401c2c4081d00b130b903c1d500f009540185488a440c3c44076001c0c407485402180d01d40e40300c0ba45074410b00204800c0303c40e95450703120700c11010302041040e808400c011401002154461200e02c00a007004030000701d0014500d00c541c2181000b810109100d80c007280344240035416482600c080a401d911415100f00300080c00b0b00c21205800917103142e000200300c45c091015080e8480d050702d80007041c945849032600035104411030341c0012441c00c40c107002d20f418000039501c501c18065900c1aa20344070f540001e1301e0410300c407807000c100f40b080d041510100305078041c440c592810041705203007042c0d00c2024016610f01020821203448698480001c03a030220303c8508400700c00e5040501440c00352030b9000700c003041808940841d0298400024000c00021210305001d400e480240f00c041c441c01d800c240140b505c0d0014122038803d075112508004813603000d100c20002020b00500421000c1558602000203402c0f00000c165030200041c00007449040c20145a00c5c03044041c103590006112 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 765773732 1250 765772482 765772487
    0x60d11040806250c0210050a0e0310060302040b0a030f020105071106190929030a0912020601140904121d0a03030c1a07021218150c0c06190e0f0604030f140c0a0303 72
    0x1a140d001c00010100c801c1182e1022f20070308500450a81022402d203041d401031000385c0c7d04000d40380e0f000d500b102c00d040001c604030703030098070001e682440d2569503040241044c0400e1600d00d0070a80e806600090716012038400d040a84241003d56220300311032566544404441d500c40c06015542904201e0116241401200003180d100000b90f03030001d050042a01c407a2644d140210451004d43c0c000c000500250448400b0b40c2400c1c1011100003405280c513507503130016800c60700007400900007003114070000c00000041381010950080e046400103a43c030300b40200328034201e04050b1014070131024242444841c03114101d01c5110030303400500f902c01c031a406c0305005030311140c1745020310907014850700400d698240e04800080801041c1d2030302c840410b10560704042142c0ca80c00c0c0700d81c1080185070151008d00494000c130940d90704264451800c0b00011950320801e00d04141d910500006022040245403480450060f01501c4a40d1588802c11005070366400c024210992282040004000003803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 765774982 1250 765773732 765773737
    0x91707050405190914070801020f0901050d06090e0d080c03220c081903020d0206100519030b0703020c0d170612010e060702100c03020405060d11040806250c021005 72
    0x3000f92040300c400c01040025002220800401142c5808460030604002282046a800a44400c1000318540000030208410300d210700030a09040c0a4003150000d40060706a00c10001010f07001003d000c01a07102034840d03201c1081041c101c0101e040040480da981540d401940d114803e00600030020300da00c000100301170000c00408a5400040d5407011603180421701c800f0306e06048529510280881515000c0d06141c1520011401c651194040240721401c0040e40c0c07088980641d0610071546290011030f0480d000c540018041e0058502400f00d100e0385540100359000e0810b080d1200c16100007422a20040c115200001144c8100041091854082210005501e03000000111a910b82c3c035150306054007142d00f0030161304801c4642c074803600d0500031a0184015450214a13103424031001400301d0007010140b8062690318120b50f120751a03550102c40c0903165141c102d869500d002c4031807841012400020b842040380b40c40c207855209014410700b50b1141d50082102d048007100681c1181c0a8 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 765776232 1250 765774982 765774991
    0x72c2404060302090d0c120b0109020715020d0f11030718060e09071e12061a0f0a0504050d1b12030206070c050705121011070510020a051c0903091707050405 69
    0x6042c0400b460000d00119002401030044540c1c1f0384030143d0703d092040300340405034088034a4600410203031002408440d180e00c0c42c040700210042c0c0390500c8003a950010564070507422034480c0b800c249045900c0105001e5407180489540b090a20400c7c2840c0ca07803a01880e11940010602840841c100b6150202000794001e10900d42203800200c910340380400850b55200d01008540c0b01c041040c0c0850040c0a400081c09040c4070100040204404002461261100580c9510008611500007a11070b004823801408010000c1d41000c486007000d00a681b003418201105d0703c444080050b0540207003180400741038040d0090045903075100313802da5504900c424200c400e17014031000850507030f030b42c4085000c0403481c1c60020319116008880000c21914403500940c8404070501c4440300040c0001414051601403007405616031003010307000e0b40c041c040d0040b4200b07201055100c2c1d15040c080c6911000c0b00c14069942c00c1455030703035a240b90554220300f662080c22900030000034401c606042d00000d811 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 765777482 1250 765776232 765776239
    0x60601110d0302030a1e090204240e0604090b1801060501020a020a1412060106030e16030f02010f02010b041d06160e040b010c02030d0302090307062105072c240406030209 75
    0x509006c5503140e9450040340d4165030203980e44010420640c10544107820411042c546c04090f2248558215541041c0e03500c600411620000c0c001806916240c01140c45964811038500700c1c0d080215140000a446041c803120b25071800c480054158400640e00520ba034014000300005410300c0242111103042400907a0000703021aa80b03a00020704000203030082603a5074000408003500310a0306e05141c03842003044054581d1030b00500c04500340c0d116084407a85c0c242081001c0c400c42c10030503405092500c11442e4000d02e03058a481d603088103042c810301e0524004069860301e940d000c2c3d10f00c04076011401c0c0c1500060110381c0607900e5080960080d030514105041c50100c00540c0c4d40040d00c1d0000c1c1c03204d001d00103600441e83c04440d00f400c20810002d4034440c200030980c030000e13001704846400680788006d8a50340b1880803d640038082c0d001007142d6990101508260740703d6007400d0b82d01030489420a806803c0da54014400d0300c80e0003003d03411a00c1026403281c500ba24120f0210082d40111342c4e003d90 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 765778732 1250 765777482 765777491
    0x50409030c021002061803040e06040c021903020304050a060201022b020708070818060a05160201110303070207150302040b04090e15091c03110304021905031608060601110d0302030a 80
    0x140c1d0718080c4000d41d00000b13600174146480d10000e01c0844881d035004c407810035031050106102c030314140550380d0f030302942c2950006080300c42054100d00e804219002c04966840c0101b10300706140d0701200900a40314256034904045644d643d049080f07208800c02010f1198000320490034059105d42a103800c1c110074103000d4248151030b01e030080c80794848a0111100071000440d40300700400b16aa180c400309080303503454200002100060804c5c4254203480390580c00c08004001103a0042c0b0070340128910380d02c00c4070b40f81d141504020b90f60300440e00658003180401d1080074040d5119000311010385107801e9025007401d10b8103c0c10b401a25a11400c07a0581c041e00e005d41007000c8480910600c02d1104100030403000c011005850000e59030000140c04150810f082c6034151000d03001103e0300b1039030540e1141c6540000d032140400c007540c6074001543c1f600601c2404101d8544400c0c1000030741d500c03082510307020f440e004010355002c07240600d11303c15504625a18140c0394026400345a00038045180400e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 765779982 1250 765778732 765778757
    0xf03020313090f0b0d0b041115041203030617100203090312070203070c090501051f020c060a0203040801050c030f0c0d0b101e0806031b011209050c09100303080105040903 75
    0xa8681940ba003008001982e02c124000349202c040c059020b01c42d80c00c0d00e682014140c2d42d114881142c00082000c0c12180c0f2110300d00304140c442c1c041c0080790305e6542d03c80c00e03291611405218180c0615010603800030f0b09004001c2001a280048184182c0c903210041504901c4c0740c1083d00650002403c411080c0000c0c030100c4014001c000c00c45100d12410360142d070361780c081c503d4854200d840c1600700541e007510f42001400540c6030310507100c1c0c42401d800350358089454500d43c102d107000181d0350090b03005080403a545000a40020140c016550000001d028565504814000703501080303d449080d2001e01d008519003591140042433900061100411384101040115140a03a40c0100c800090240c10410070042d41aa683c0500b10f000c902c2d02600c3c906200c8002a51002004500130729420f0422300c03244143e020302007200c2980c048180500042d0200c1c10110344942c140c0d01c0c2a4020003400d8005041c00307580a0982e8152039043e01e5018035a42440b041c00002c10660104400b400100054074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 765781232 1250 765779982 765780007
    0xa17010b030117010f0c21050c0f160203070311030c180f04030c0f030504091109011409060405040f05070201062c130b100603110a050d05040204090c15030b0a120f030203 75
    0x500e811b4000c2d26804000d0f10003400d148032150f004801041024901000c0c0b1001151034422908007210000b90b407034803080800d40140c0c4112440400039490321952000000b042040d1a0700d036280b0000f282034801d0811502c0074803041c010030350100d5000113402d10000d40e00842d1101d806400c40d0103890050b0010a82d5654032004c11800c800c150f01040011900700801280c0b80030714508100d0901d0f0640c00c12404900280200b0b000c0240003070104000304d103000c1c00d0348680d02603070000d0400038024401c113840b100410004090544210b0015424100c0100f13034107003100d40300d120355100d242d04c201c4c6600c01034100d02d101440150810760745141503404100402c0107180158047c202010803c8040d901d002006030440303600040c07175036814006100c4480703019002001c2c1c0d82141000f290200302075480380700249c014000040000e100442c00c09011412800965079082e0740411a241080004800d01c104600844140304115500e11030000d10f0001640134024403034004d100b401206d0030000b0704440d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 765782482 1250 765781232 765781241
    0x3140f07080c0f0d02010c060906020c12040f050312031305011d060604060f12150e0f031c0501051c0204110d271101080912070303020a17010b030117010f 68
    0x20110716440040d41140b0741c80c0903e800c000c04102240e507a441c04107181c0c0060f040007030348100038100c240d0380c80e00d800c14400142c046403c0c4940490548581031400742094500b50060b001d0b014003407042c004041070904001622415684100e00511705564420401412100004804403101d54039280c4180840c40e01c00f050081c10015003020f852685010703000d20003100c105070322207114402503403000c0146501c40c9121980d00754204510300347c240c4c07040503000c010340002c3d58072580c2485078161782c440d285402b10103401d40d40081083d10960007483c040344000e48000f8010241c0c05901c0c503c1410110240a540d10750051015001080205036000c4504007504180d602c000c1e005d482d0000d00303810300c2e0036000c404441c62003900180f0000815071522142d11324006c00a6040c010396001064105a0800415028500c480c59583d40c8150900d4014040c2d0045603e40c40480c2960044201c1d001c0c03a810114113941c1000c2e2a01d05680c0b9081461f10090704400080c407003556a100c440e280520207018 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 765783732 1250 765782482 765782489
    0x60f04050607230a0b130201020f150103031106060303090d110406091b020307200d0602070318060c1104050a06051503040215040e070c06020c010507021f1503140f07 73
    0xd070390b150003036814480b002d407101c0c160034451103400680c40440002e09042659810001c04001000d80341111f20042c0d282240c8040540c0a901c0385410000403d01150303034941c16a4400d644482e41107400790b1401b40e5400040d650b00c2d82c981c0003404482403905142410300300d0711f800340040340340e401e030014041000c9806a410846400361a01519402c0244036011000c007051203100071480d10490741c1310051a21481040d08a1612500940b418a9a110f46101c046550000b40440d40e43e44c1c141342c0584100e03440c8600c103e8004000c000016114001e00070759101d079400164807403080060380100700c010480100359820707450750f800011400e81c0710842480903480000030782903079a0503d4010484140c8190313150300301c00401003000b071001a10005c0e000380c1050303260814000407030143c907015010340100b20851600c2d40c600010044031710790004051b01c40884040079903d206158058030400c5d60403001d01941c2041102600f00005800000003021030310030031017540d0f59842215046424280f1591 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 765784982 1250 765783732 765783743
    0x30209060c0f0c19030204020903030403140a05070b030702030316030e0706020601031a19180f060c27060c1505100f050603070c08030405010e071e0906050f060f04050607 75
    0x18510380c0a801c00042502581c11590f91404082c40518140c444da4180002400783d9008a0400045c0d102041501c014650089804c628000350885140e07807006c0a41081d11544a0707180001128034a04003140e00800c0c0c56806580b86995202800e42c4000e11000300030101980c031011110600e0007808071001510503a4060a070799455801d10f010309800c50900301c03403448000c40902c152524000403000c2c0e10544034001207450040702c0d4103000c080c0c1000700003401c2c0c0c1c0c1104181d10200848e9501543c1d003440540c607100700c071002090700d200c541c0362104c1101d260840014418041d540c000d808000b0712a100d240610307604945415200141d42091314100407021410406120300c503030801149015200560f11903042d41341c902e01c001e2203185101c1c4083e050203000070204050000a40052800100c100d0488040756560003403c0c401840203603404111070300340507000c10035071b007103020300d00c200c1d04000c12001500b2a200100000c03030703101203080700c400041000006515241c0a020b480d5243c003c1c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 765786232 1250 765784982 765784993
    0x203030a0f0315050d0b150402030c1c0e280c0b040512160e040f061b120902151c050c0310050102161809140a060b1e010807030209060c 60
    0x81c0c00074098544200700c00f2107600000d01c09000f1503e400d083c1800807078001c06000f0307158a400500c00754010b00140c0b03080d00240000b00300f110305c442d6000240100303808ca80c0c50035040003045580c02c00301d6010141507016904404c2d500708020310400d5500c000b6110641071240d904e4a95600c064000481c1c0d40428148800800c0400540ca08116102144249071000e010820a003400c0380e030880c4201c0c016005500020004101800074103040242c80c2644248200a00c04680c645445642d880183d0440094954102c401681c8024001d038a000c59024041d10201d40010b0141041a005001d03511440c42000000ca450b41c50303c2c0c0652030254002c181c0d620380d281000c1e100741000d202141c00c82d505540c4100c0003c3d901840001d42c207000c8070000380030910320010700c02c203090151090078409003108411a20010f2000d0011030041941d510070b0804020004400080c02600b405400160020b190340e00000341d01940100c036119231002d014070f80185044440300000d440c640042140712500e5010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 765787482 1250 765786232 765786257
    0x1002120604050603150703151502101d0303010e040201051201030317070f020606130f1a120106050102030a03020c07030605010b03041506230a0306090b041a01050108180a0203030a 79
    0x20310480d41c2080d801d5000d05050f02171299000380761080609401d007059030b660045000416043c4407031000e07144010507400c0d0510803a400965516600344d94409152a003841c2a00d110b501800381c01c89918036402550842e8a4840b940721a104010016414000304105000e071035071080c040e5a0186100346c50301c40d0f0840c00c4086082c6c02010003011300051022842000c0e07070850300001e1007584807408480c050b00b58102103501101030004501d4010344a81400d010341c1610030084804051500103845e020000e11007080b20a0917190f4920942d4056002004003503e0648240c008010100034001151100380d640d40d101c50880d40d00740d200b8982844044103000401043c4012000c4501006106020f92400d08245c0c0b25540c5218860600721130f0300071080000c589503000184006c6800c144204100440303030a103030108000840d002c031001e0b0035075444e10f0a140342046985044c1c07401a03646260544e034000100c04800813440e440200340c45040c0d00040145c2d4200700510b00c4c0d0641795201250f1084 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 765788732 1250 765787482 765787489
    0x1020c010c060b04243f02090a0209030c0301150e1b0a17100e0705070f05030a020d0906050a0503010b09031912030c0905130203041505040f0b0c07021e0310021206 72
    0x2515004080c002550050140700f4102c0c0d0130000d800c080300d91403018032000c0b00c900501b4203160040303402904030300144100301c0c90b40d407580c0c050084480c0c250180e0b03a1066420040500725071114029134201c0c44d20420034021104801c00310b60b4015a44c811500c0c0803048070300b80c402150400003c4900087c120305d01c00c1000300311b00c10040e400856203070140c140345045c90031500007910002c002404001c004a1a08240142410003020a541140c2525901c00241034000d4440880c0d0315031a02040040000180c83e40c8075000312640c3d18000d580e614203603400c2c410300441c0790f480011059030610660301283c40c1c0c5018251058040c0d0310608205614a42d0300d440070781030302c80016808041c040608003c010300e8942440c000005568101c1c0145e9036030311880c2c90104d10394040d01c0c403907013580713030004001c02c1211410b0140314250140301082a41c1e80c138003100600328450280c000b9007043e03420456069030030302481c201c50301340e400905951080d0300c5032024208a0300180701c100c2c003604c5440103102c450b0030f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 765789982 1250 765788732 765788801
    0x5010906090506030c092e17060103081c0b03010c0206040209010f031e0309120b011d27030903160509010504091208091609050703050901050601020c010c060b04 71
    0x22007050601c03051030306070000313502c4a1102e40b2442c068140780001500007044080d01e290014440c401d01d220001524550041d2280103008006001c49200110700c0782c603200054980c100c0ea40400d07481e01d4003281c0c41c20132074a000c1c202c894403529a1104048081590300b070003146614141da80c0140700c0740c0380ca40104400400180d000c110400002142840460302e0030b82080d5401c041e800c0d5003404583c0d00c3c41c007100c00c1d00042d80640022145408507504002a503500f0030304a40303608607460102111301d403d00000c000151603000900c420b40002c0107101d180c08410400040c0c2600544c0c0c10000c00030042414070300d0b120005132040c54543c0003072009150800300c0501600c0151010001c4501c40d69030707101c3c000302c454500c0f003c2c41480c0d80000d0400b00d0802c0540c000e20800031801c0000e564800c400e4002c0e02c0d09a0b92400400d0400001603100d510510815203d183705030f005103040c00e462801510321072803a800c241d4045071141210030194441d402524a4219120261000b003180030003001c1414 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 765791232 1250 765789982 765789989
    0x6060203030a05060f0f06160204060303120f0212040212120c01060f12080a110c0a06050c010b010c0305030604020d021213020a08010204030c03021302190e0f0315070807021e0105010906 82
    0x550380c440c5c4810741521141100d40c1003541c2a1f03007aa0341c581514002010802d841e003402540a420414003108244d84245036132a81e0702181014458140d41d41036000517400360145070300e41100e000002801510300b040c06903030041128420355040e003c002002e0f402640c405c0c508050903030346940c0c04010407121000c1c00401001c4005e80041c8020055580d45218072540401c00c04201d00303100400041d040074440c20b0f43c03101c00100790809241d607500c0d0142440e0000903400080e035180c5042c1c4100c070b50145201c0340d0041d5040d40c49528554500003080000d40000d40101952a42441811004403ea01c135a900840c41c003514988018001d01c1001030a08054020400782c0c1d0040c40304000080ca1042c2c0c0c02d00b80ca50480c1c117101000178540d0310500900500300c907100c441c2c3c030810340000d03000e801074203021401c041035031400c0350518243d0a041c0e8070759255106090f8903030480c0008030101d204a0301c65801c0402481540da0000b403180940101c04140b402095817655070782c0040040d03402c24030404008 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 765792482 1250 765791232 765791239
    0x16050706111c0c032a060f05070c020111010207060504050319111f09050d090509161d180a0e060114180601050d0204030c09110304082b06060203030a0506 68
    0x34224800102c450040510300b4441c18403c18000c080f0401d80200c118000c0801c050440d1031908010401c130400305518100705035000c52500c1c0c0712884040450140b00d2107002d080c1c94020b1044203590044403540d80100d54107001d55400e000f41c000090850160034000c038012002140c42c0d408108507100101d1002e4140c10520803804580c14000c803000c6100041d41d404102c0d03117010211040c100c130015000f803440050030b134094079042d0005550460703c40c00aa481c00d8620100702d03507440c01020f81c400f501da851880400c07001d222540b040850483d840140f148050000c10402921101e00303016000d09603400714206481e40c1c50903410400030000140103021038403a0b5454098494003107002a090310700710301280301d4070f04c00207800c0f41d000700226040d0410b1100d0466032a542c030309000700c007410b050080c4e22805040501041a0400502c00da0b4040c40d008411907291501030086070001c64074107412800e154a4110b441140d1240034070074a8000d00c9250003843c1d0300d00c0c080c00130500f00c4400030101c911 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 765793732 1250 765792482 765792493
    0x20315040b0417120108010207111e04051b0c150a0c0f050304140601060513080a030e1903051009061803080c0a020307020a0609081506030c151605070611 68
    0x11991000e41c031500160843e07001c0214000e103802100c5070380b0450008441c4070134807400000c1d46000560003443c40500170030780074035000750040410040303481a52814017180002d00c00000d080c58994803098020041d00c1100500d040b50b9802c4034034036007000440844a8201c2c0c030070b02503250030001102ea8090718114041000340c50841c030203040005d642800c00100301000c4001410090404005507607500d5030030440d045583c0d80d840007089030b403003440014884129104009107007000025a608110b52644030342c0500300039402440700d1886000c0c08d9000d07601d000d01d4000040340d030034044108560384141c00412441903508068042e224552281c0322140c8402c1514070209601c01001038005c1040900f06a403074a584004910b18040c2d0400a9400b1864541c00100d49801490200444100c3c00071381d580c264548001ca440d4600442c0c2d8144c16810110340c020b81850040b04000640324000b082d03c0c10710810181c042e058240381141100c41da4403186042c440150807400f98140d07a17a001e0014038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 765794982 1250 765793732 765793741
    0x111060103050a121701031b17070909030c0609110a1203080c030a06031a0f09034906062a0209090c065a130801050103020315 56
    0x2030f500c09a009010b040c801c103c40320042c0c0c0900c80c015150320380409070000f0810303503142d0411100b0f12044000c4003034050305d119400038054819882c1b0001408440c1c020700b583d1464110040082d01210000300c007001101e84d01d0400061140c4514800a80165a881015415903080c064440141d400c0119046105205000040e5110302c0c240e40c4000c25008403601c80d00c50050040150041d0b810040c1703a04028107014a121001d82d000c0c030300c29103024032400d803240c035880c400684030b12801c60802c0d00100c070070502400300c8a03c0340c0b114a0a01c08040324000010030003044152a00125802c2c05c891921034400b0000c2603445070743c03a60320407600803038600e1100386085111034010b1003550090140c40c0c42000201078040074031070400e0b622006407200341d4074101c00080b03441040301e00c0150215604080c42c43c0d249030703001d4000e0b1039188401c000503001000780e403540c120b02d207010710b000070203075103820046840240e4a4162a03001404802e002180035411403040608140c10031060460a000c180c0801 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 765796232 1250 765794982 765794993
    0x30f040201020d300e0316210527040f021902010506130e07081507090b0f0a0809120d06060e0f0904032003120f130b071206030215090111060103 64
    0x1c140408004c3c50702d1010f2207a01c000060070a0203c440c0040c0804500f140075002c801006002082c07040130988020000800c001840100306000d00c030000d40c1c20710040c3d10030039400c0000c0210420844000320412200f100040640740703524039034040c01d03070042086401c20300c103a11010b8403c9094002400f4518003980842c000040c200c0c0002001900c0ea0813002c44444188240380103041d0320f0040ea0f1a024800e8402c2c40b80b200c050700c620000503800040010004e086209071010744036240d000740d01d440b80e228412942c421010f01701a4142c080e45075200c001030b81000003042103100c0500c022034014900300c4c0181101c3c2035a46d1080c0909004403404440781c0d0380010807a8400ea0504041002606aa14070340c00c080700004080000c0c407001400030400c041c002c103483d120301c2402c00c83c02065914a5030030340ca00300c01403000500842481d004070b14110701070451640866911000012010365035000502c02c819080941d2403810000500d191055a1000c07040d1580c0c07211301c0041045503d90703030742d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 765797482 1250 765796232 765796277
    0x30c020d21060b030c0405030706031a100e0a030b091218060307020a082a0f0a120c0b010b120c04140f040b04020c1b2b0512030f040201020d 62
    0x44a03462a401c0300c190701d014000d0b80140c0240100e015903540760300d0310f10b200c2030700755000c3c0c0600c0d4800e200d400b00000c3c0c011320174018851810b07840d448009440d031503c4184000ca0f0300d058011800c1c00003948140c40940c6400c0d252900445c0204d036804d4842c104a06058141812200043c2c0340b036a00b0440e400345c041c0c04010202000da025242203940381c0e11108200d003030407501c40e0014151040014411501d4040450081c0702240c14005c05414607408040d40340d4411000b1210b4846030080c6c040308011948841c204c1c1030340c03805070404202c1040b0799a01d24000b41c07001d0300411a0000041000c2c0c0c0780000d09003041e64002241c070f004601d09410b14902440c4da030601000d1b00e11030024000c4448040c0c8a64204061105000d0400c1d0f45401c3c8400e80103469404c4800040c2c500001100c0415162034203840450702c580b42101903183d440020305204600352100c01c0c06130350034890703130100e044c2d5645404021481000d81140c194140d081c41d100080c1002c65140b4a5070070045101c028101c01422540c4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 765798732 1250 765797482 765797507
    0x1d03030c031f090c080a0614040b0301060b0a021506010e03071404090f06020703030b0915040504050c0a030c15050301030c0e150a1805060a1a030c07170406030c020d 73
    0x990301d0769141c9100702c038600b021040e48814000068800941919181c000c1100c114081d10b8008441c0c0d154400001160100e1080400b1200c030384d101000c1170b00b82907101482c0204c0c09000072030359170746601d0b5070411a4080001100183d11414110150301000d03444950451400d107044189110300300300007581c5062034000c45030028808070314a0203070f5840c1c0d80b007a03031101e60000c1c50000407803040c00d0000c02900212415804030342480460785141c5082c0d02c10611405107000603242c45c90003c2c0a000c01800b0040c011102d88c81084c0c0c030882150756190105000b10300c15450701403040c2c24a054032080d0080003620200b4400d0500051001402c2c2c0d94040d0140c40100e0504111641c0b501c0796034010000010a898200184590100e1602003000442e9242c10b0854010b120989400b805e10045e407000b071040001504040d0040c16490b05044003c40d00030300c40750b001d1810120780e52212500c2c041c1d00903005010200c001800c00055416028074043c0410b00c0c00580007568450102070b20b000290031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 765799982 1250 765798732 765798751
    0x180709021e0d060503150a0b01092709021504060f020105250203070b09030d06080c030d030b0a090c080a0c053c03130203160602030406180b070b07031d0303 69
    0x54011440e540b41e50001000300802412a01c1c22444c04070034007840007080d1200d48485007803241040c001c0d40503c2a200440310b121005205100344030558030600600c1005880070360b0340742d561540c09a40c482420090b00402032280581c0e45143c464040c0c0640f0303100f41d2030801e590404042221809032140c0c20380245100c0000d0160300304805034101d04510031603100801c1c5d089410140845c1d04000006049460514101044450344414040d40d82d0b4002c4d008569160344400d03480001c443c42904400340101014161102d1183c68481010955645400c40d10014903241d0410008000a0241054000d8141081460711031009821210888080426060741c1c3d0042c4cad4408042c02e2a0480680c0d03a81340c01c0700c5649038285140d9408181d1101c4030168424428041e0441c07048258284103000c1b00c9040d002075141a05d405401c1d940ca40901c00d40c0003010a02d510300003440c0300900f00400c0b1840c8100910005450140c1d0702030708659100241104040e144040c4d41803131340300081160b42185240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 765801232 1250 765799982 765799987
    0x2150a14160c110607120e030d110a060b030313031110080f06010c030e210601050a0807090903031e051e0601050703050702030109060c080703061401050403080918180709021e 77
    0x803c080340c1c00d0b202d041001010001d40000c4032848507409a14202190007c07800e03035034500302425040b54102c0022a900c002c0d600314810050000340706070700100701c4000c090281e905000858124503d081825407090b1000c80782c80d06145103a25025447c4940d41200b070418500505100c41c8407412648c0013050300e810304ca808a0301c0c00c241409403204800d0b4400040141070840007000516010910540e5843c00c10b02c909800400c00f850301070050340955020000030035000c6c1c40c040440f8050308680300103a080c1640c40302d00c20b041c2003000c2e0700a0400e06250f1000b1030356003062244440c140110164941c840c1d62540203101d82c3c0e0780c0c0300003120415038041c58082e80b60505400020300400100d10010b2200b80b83c24800420307507410100b207600c0792541d91001c01140c0d40e03421445040104101c0b05e1030000c0c2d0204002d10018400f07202078a442e0310050711410b0241c0044002d031150507400c1c0d4405080a803000011f159041007040908040c0041404c298100140940e031440040e0a2415014011602 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 765802482 1250 765801232 765801263
    0x15070c0302060147160213090b0718050901170d030b060a273c0e0403301104120f050a052401080613030f02150a14160c 53
    0x5102c20803214613482e010656030389148181c0d81406103900c0b2002c03406107082141d044524952071091301046500600702c0d40c06980d4070325044520341d0f001c0541c040d040000c141e0108060300c1d5140c0c114041d0108040780350034a030b400000300d441c203e900d410b00e900301410300c1803265030381d00c4950680343c100c0c046041c000b03000c0c2c88021484072400c511252080f0350b61100d440000d0609000c1d02c50349001680141080d41440000e0461600d0b049081d0b42800311581c00d4204000344260b0a02040d409030081c6407440c0402c0c07030054001180725003c80040c0c905d041d000c7c3c003052000000d03c95100900e418040d8a842c00e031074400c10b400c0c4040300280280c400d0710481d180300240b08081c09030400307456010040e2625081210131002403441035603000c90a00901d00004140107000150381c0d4010030307450980541001d15903804882c00c3d010340030700e10114082c148114130340ca5421a4598002c1140010100d8005218011801012001001c03850341900718105001010303000003441c0e107000c1d00008070a070032018 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 765803732 1250 765802482 765802589
    0x21215031c050702030109080315010c0b0c0f120f0105090c18040b040b0a12030905090c09040f1b02030304260a12021c2903030904050915070c03020601 67
    0x303e040203074142d42021a01810401c04c00d008500c24035031a0440c0e807910300c40c0401111080b24004c80140310740c10410200354a001800042c2000c03d02c2030341528130707103000c4550b9000e20003000e80701e90218811910041c4010f103800f40d40160301040c1030b9582c41c1004051b20384601c0100c1407161440c010b03075544040f8101c0e516540c20035020b07500c0241c0855a820307652803800c070000303080c25029000150031749004101460004009802043d180031060b090a0140040000520604144014080c0d45420303c440e1800303c1c548107040c00e0b00b2074016586034507160806c4005000c0300d2142c550004446c540d10102c1c2c07030140090340c0d029070052405600500d5500741c0c1c07400038428030034024003921400d14403907031480c185e030042d1058001550130110301d010824607203104065a01c171242c0d450380040c010070341c4600301035100e107a01000807801c8600402c0d0b110082d828220080e1444400a1a10480036040c1038040144900501e26006402c81303c8881c8102d08c0141118000400c0b52404c0c481c0f0031260154 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 765804982 1250 765803732 765803737
    0x1415160909230414010506030106030c030219030605070c1b050306010b0d0f021b0d08160315090c02010b0315010b0306010c230705100c020904080705100f021215031c05 74
    0x2a041c2c0b0461154205401c01100406500a10b0a15517080400048050030103008100850307910044210026003140c0c20008808500004104031100d280b40000108040b4007a8a0003252a0f440c2c40c1e48990b02d6061441d140035070511f82c80383e0384254040c1003146440c0007c840e41192581c00e4a561504d1041e4a6200904000201d201c05140042882c400e52010700c4e41100c7c2090034102250750007280290107645c00b1400b211591890315080403400070050094108106c4c5107581001a04159199a00a42280c01d81d0b0903480050795911032440c1507040401c00300e0038181038030300c0b483c3c03040d03240c1105e011452100802850422038521441400c004900c40c50b0040c4600c80c282e41201c0748062101d05685130a280b181074450228640c0c5000b0250003141e203010141e0300541058403d1369561544d405a6002c2e44080312544280100441132003040d00c2008100c204001c40941d840a0b000814507540c034014000d01524400008444944e55002071164180a84069865106130303a01000380c5150 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 765806232 1250 765804982 765805031
    0x1509020d05030d2a09090e0c03060f040201030e12040302130204030f0f020307060905031002070314040603020705150609180c0d0b041e030f11010204031415160909 72
    0x14400030071260b00120054121213080f0031080c24007003210714102490b086413216482050089480908140000101030300455070383c0e4a15421940c1d03000c0703048003191038544200c030558200010041408110340e814050920700015201c01480b0281c41101f000b8041e100303600c4000d103e800c0c5022010030030456601510002d50704101c0d00c11070f0390300904144c1490211818101d00c41d001d8034401042042c01081070500741c0b1809801484960001c820300d0700254000c1c101513050090703041c6109403401da001e00400140840e40d60260b04c0c0c401c03a103080d83c41d10070003e9050021140400402c07269490750741b030795680048241404280445881100790800081061183d0072565404e00c030b030103008030046464090707845142c4a21001c1d0b400112940380c01c803801c10050010391030201c0b00b00c00500c6480003a000d003242600051034255a0b40d01d00b03455200d4800c4c6230b4455040b075031514883c0d05100d05a550302c03401d180300c04203000c0f501200013400915540108840a0b90b104e502212140c40b041c00308420707 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 765807482 1250 765806232 765806243
    0x1101060f0815040f0f302f010501060c150504021003020715060605070b090a17070606050319020f010906091203110f01090b0c04050d030f02030c01110406090506071509020d 76
    0x3043e10b64104040f0301a84280b40d5038800620358443d00c0c0803503207840c80c3c60702c06199981d40c1800c0a03407045254030061031300b890003400541800d5111f041d1002841520f0081005071078104a03100245003285001d00000303540c000c3e0034541410440541c4505ca280c080b81c0403146801030380d500e507610340300342d00c04a9003240c017200c11329000c03000c949160850000c04810380151a07014003075880300000740c0d82d40c01041c4010b0003254110001c0003102d0661000e40141c602c50314000c0317416038135000420b1401ca0007610561101d02c3d90a400340540c00c02e252600c80b03244083c03030911803890800b28058100b40c914441e4040303030003035802002c0906229074504480b588420b0103490544202180329406000c4450003541d503980d5400201d200301c0784c0f0a0895044890213400e060101680e40c03019905150710501c3d10042d4003040007114080c0c907080c443c0105062001760410b8507503040c100000e214221a4010f1400380d00100300e80d00c00300d56180109643c2d80400d61012440182c3c0f0f01c0425503080810320010300 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 765808732 1250 765807482 765807503
    0xb0c07030807270e0a06050303071515150c020117100b0c0c0904061b050403110405100e040c1503090f020607080423100c030f0c02010216061101060f0815040f 70
    0x549000000f802d81c000c5000e05c1d002d01c0100d0b02e40c0b003090f460340324045000b440010b0007101e10001c10703896081400c50511642c01c012110359a032856540c0c90b20055204000580c1d014000411580c00c442c40c1c1064205586012031a464613403030042c1020750034001e002c0c10b000045407102800b2400c101e0101885006000c169075814180340c0140070f00240d01c0d000c00302495800060030414824803d417021a600301c0d1011250910f14401c0c08000c0c0b60140c10340d502015600d0b40401c01481d41d48071103015511070b510b81d2241d249403090340c8040c50f8254030988201810410124045200c8400515015070121001c2c0c0c0c1e038043d6890015664466540300e074042d0b11252841640c4441c007070001c82d040243c04c1d111150b00904440c41294507042000004001c500080e416842d210700c5107904d500414410700481c0c00c2c100d500801007210085540c40000010303071101c0d064400745030a005410042c4a00c280c10714006040c404001d84541012404c076402c062a000004c0501a4104016001c00e070000b9a610 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 765809982 1250 765808732 765808739
    0x60309101a031b060d1a040b030f12070804050a060c0501050702010b0a170319021b0102010507140703030f1508070b0301060f0f050d020d05162d05190207030b0c0703080727 76
    0x81d540c00741b290040b0b10640c50280015458100031800c0784280d04424041c01040f40c02640e0041d9a4012074001d480c511018000462252100040341c0050306003511a80200340d0b040c41c200382910b000030702000869041c00200001500c68805007070907141603a81c654090340040c142d040c654001c0b800a82691242c07010b078410025004540e0a00220034500c080494100b00b20040e0700342e540c140c5100b00016100201150705000c000c025150240c0719103000304069103041c44140690b51a0400c00c3c204120500c070412050404000b0800140f150100306402c540c0341000291200000e12060030a00208040011070548690f080300c3c1d91200c550011074441c410f1140c42c20090804841c2810a554958502e240f414050005000038402c03203e22400440101d00c1703000ea0324807070101c40701d080c410140082e036022074084005002622295000b03019891440c24240c02166000d03240c50340b02507003003003000d000c294042c821540c80004c0c0c1c107001a15078000444c0c0000400605d558428000e40501e010 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 765811232 1250 765809982 765810011
    0x4050409080d0c2d0e061b0a0b0610110a080304170c0a110f030c01050f090a0e04060b0603190c0e0d060606110c09010302130902060309101a031b060d 66
    0x901011642400413a10300420a190200d560105118040030440044498040e03250000c02003022810035111f00300807219404046d40303018105201160603540e100104101400d04489480015000d0320308082c0401c01d03c1c0103685ca401c0981009130034242c00100280c14400700d40004074505120b042802e0780c5032980080e02d61214400717481202d5901005906081c40c0c985954040d1201000801a0004288510040d00d00da071000036000308813402404845120340d00c0c070b101140100340c0011480d1140c6000d00d050812260b14000d480d00c140414801e0111981e1141851040702c440384800143d00c0c60b002d4015169008090001079106240c030300c00714100400c0750440703000c40e901c91300d481002441000000f5196100b818840b5000034034440100f01504d0000ca0725440c0d800d44000c005244001034002c07844c181e0040b100b1a200ea4400e8080038110b03034040c81800782881e24840e05040c1c09149800103601c51004a144114200340d5403400c0b2503541d0b0303410403100e801130070260421841041c100c58 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 765812482 1250 765811232 765811247
    0x914060405101401061b0c09090510060e040305030c0c0a060504051506091b03060d02100f0e1e01081906060908060109060602031204030c120c061b0504050409080d0c 73
    0x200183c1c2804901e889620030315811070f050364032684840c0391014211382403000001480000791441f07940a10001401c003400d01c2419443c40c0070340b01401415034003800310000e4890642c000c04400d0390f40002c120200780d00c03805070fa41101101001d1641d07410102082c601d07010480201400151034a0144020028005071042001ca002e00382c0d501156681c0081010034402103c40c61284551204640da507043d00c140115804140100f81c07000403065500030801d6100304015050126030b249144000460f0400d200383c4000d20200c890a03150034130030940c0e4140c1c0103044600b030706014055020402d820214489040000366040f0204012651440c006008100901c07810030180038483c00411200760070300030034042d03030842d400a5141000c02603200c0c1c4c040800410981c108000000c0c9a40022016010102056441ea03125040c480b01418030740100c40c1c0d00c1e00842d141d103061580c0407540356002802e541c110f5400303c4000a400555052640c45481070314080030b81d65250400846041d07170054070 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 765813732 1250 765812482 765812503
    0x26030f070b0601110d030b04110f070b010e040519240f0c050f03040f02182401020f100b0103020d0513061b0207032612090118030801090914060405 65
    0x291414280c03902c0e0010341c0c2084c55280c04a50a800a43d040d58101e4000c6c0c00c820087d000140000442181440041c1d601d9001214010503a82e0300050b0401804070200c480360141180c000c2d0140141042da070b43c1581c80442104060007400e0000c10b54050041160882c00c02c44501c6000095901a800c2288001c04000340c0c4406154584a84416082c0c800c006403445405881c104d20300d1602c075070700c40e111450412041240e004130b50958034113141c41da62041600503030070f0403298074040300110312080088071548050350440d072106032420380004001944c1c100e00d200d017580000d1854003400040700030340b0504100540990501c0c2c2440000d0440800081c0c4180c0248030070810161081c0581d100c060303101c5240c10050b40030044c1800403442d2124040c0c0f44900041c0c42c1a030744000111050181e401c110401322808110800f0131800310301c2805130543d6100c0800010007415400e0390040c0002c04180901508103556815080400240b81d01e00d0600d203156a04844041c80d0600d06140d03141020781 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 765814982 1250 765813732 765813743
    0x6050303130302150405090c0706061206020a021c080f07030e070b0c0601050405101418150102070602071a220b0403062a03050402130e100501150203030126030f07 72
    0x84444e40d5001e2070301c00d4500f640c0000b050a11180c95021909886070420f030790940e500c607515180001d00640360f84514240f00d21038035015840701d014200c0a070030151403042c0362000543c40c0840d44482540300840395441600c0800116407900c60a504900401c1032085240c501d20940c0c1c00415404070480240800444800481d0410303a00d481c00d00095035030548000e20441d25680092281820078243d0b8080c2c01030240c01c010b0100c0008800b2980e482c820784a500b01120010b120010a5a06100600240c40d140c002008418913010000720140054024807640002c04644507528881290102ca0440b06021520080765141d030a29440ba40c041d1004131a40c502d01030503075115494001d6650303031843c0118048540700b0003244c0c056004c0c00000744103c0c0d000c0d4002d00424110080f501ca2182c040a40304002e20841c141090318100f126410781048002c0f1004942d4a048164000b0440741594501400d2824440d0400300c40235080d22a4106030683d4000852f00c05002c0040c2006420560b0155 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 765816232 1250 765814982 765814999
    0x503190605180a021c0605012309150d050a050d030219030905120a0e0a0605040501030f020304050a080715560604210506160504030201080a06050303130302 69
    0x1104100a5a40b188424031041c2c00c2001000d01603d045101c45500760550b107058070045440d0798a0200700e810981100e00c50070541d0444c4c0790400c0791a0000c000c1e000007601c2002840c141580907004541d0b0b819081ea12583c0c1503119402005000d00891030615882011035490a00c1000098042c0d0032404811a9181c06450704c405818403902400c441c1c940c000002d0040c150b500b00441981e680811080340a016100007008101d4403003000b14001040d00d036550584860405000400b582c40c0d4566065280e401841400041030001c5000743c14564842c10340c590b00c820500e8086c0401c80d941c07440c0d01c2410301d0100c03403021a000994000740c84401c107a18050090034500c2005030414a202010410900481c3c070400346042d031661403003407210700204008d00b00ba6654081402803135a5090600710380c8160040881049410042d00350007041500e9542e281c4001c0247c014250301441c44041d0410203460b010031400c2050b940440c8c0903000180580f5a00c3c2448003484c00c0303003005444124060800c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 765817482 1250 765816232 765816241
    0x30c091e190b0711040207080a0c0b070302180f03150703050610030603150b01050f040f03020414060306040609062304031d0607021210020703111c050a05030a060503190605 76
    0x1010039009407014411180d040c095a500d40c1c4e00c4050704400805c0e0015401c00450340031503404406000030744c106036502c0d03082c590309180c00c88a2910140400d005d0500501a1244204204202e401800021780f213055101c40c9a000091034403801640040400460200703208800f9816040644103030403c1c0e5a55603502c5220f101202224490322001d003007141d401d1109803da1940d03420503650040c05160031824113000640c092a950310582c040c16500d030864a040045083c1030103100002c0e038450088026074038050b0007003520b03060000e00007004140e5454041040005d0fa0303104401c0b500d001c1c000843d5000c50b6051803607013044261015008900c140d440056030313004520a007500d000020300054240082b45e030901400080c40f01010b045030140903040e02c0441c12920213020100e001e03580715402c1c1c08402d02918149070000e0482d203024003040000b40e808642100c2110383d401e0140c0b030902daa960715100328900800e160b4007c0360b41030252201c0090b0500e1100c00925080c0e0103424200900e448 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 765818732 1250 765817482 765817519
    0x80c07120201050a0f0c120302092403070c030512100617071d0a0b0315190803042d080d031a3a0507030b09010917030c091e 55
    0xe0500009001a0040100c02c050900c40c2101003503448031401c284a4031840d55540c2c001c0310304080300c2c1311300103540452140450324081100b4030404076900d014241a010f0000200039920004001078203204440c50342500701441076086503040c60325006442c8081c00c0000c9903000b10441d030b00c01c00b400180341b08281c544148000d26103601803079182e242c80c0b202c1c6ca0708852440c0d10000b03610841d0750040e0010f80002d024280e25008603c1980c410790181d0b03d40d001c0004210b9503a414030420724141e800c1540c2803180450000072282603a40a9483c00122030055030f0310b40342c061002c0650300742d40301c00d40780000700001c0c0000d481c0154590ba440503c05e0200c11080000954410300c02d41e0b03485100c10445014924a02c1c10700c1a00141d40a60042d081c0800e8601e42440b00d035840c0215044d5102070b4040040c0410008440e4000c181003009000461290719122400082400c04006101000010501036140c003001c44180e450003801c001102102502e0700182907034909207aa02460a01225040c0101d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 765819982 1250 765818732 765818759
    0x405060c1605151b130314010b04090c060809030a1202090409020d0f060b060703050706020901090f0b0c01060f06080a0e0c030d03090b0702031603050306190323070f0603050a1503080c07 82
    0x103901800d440c484038031b180c80f542d69209100013181c966540e503403040741c9951100d000e2010b6843c05010b0b03824105241c4079008000e10030087c04c1c070b20541c00c184051100c203a4096050140800075140c00341c1c80d20130184c0090000e28407910004e610280302001101007150a054520009001e0842002500071501c00e0000501c1492401000104100203e90010b0310725405070881c03041c1032414141090700d50f00d644440d00740070741040600310b101054190350003509000740805080c000600d40c2c406450001c0190107040060007440400d41c0703400030b0540d014410460080d202d040181114548a0500c0c00580246000c401c2640c0300100c8400250300c5a0002086403005014003a070040c407041207440c1110300e50030280c00d142d400210007030649000d6000554040c090740c0283e03112140c1d022004000d041e0661104c0306051143c00a0b08100503110130550014112081810701207443d5031000d003281c0060261841741d644d0014201404000e1200701400740c115020807404a59200b500d070100e060543d0b = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 765821232 1250 765819982 765819997
    0x70504020c0a02010503100801140f0a0603170912190302190308040b09150f0906100315020f0d0504080405011d061c0b1008070201140405060c1605151b 67
    0x180d01480c02e003001540724000965010305e40d050351400d4151981600342c255884810480e01c035a5200092103480d40c110224070350401119201000b20030b195540388281c4500d10310761890741c0100400c2e810110f8032010146a280c03000b410075190094841950648034152810081c2c0040c8244091178030019014614220850303010740301d00b06140d90790703a02d00c000d07aa00100080d4140c003c0d108060100301c0700c000031070f00034031050484000a2034909a00d928104004002c49892400321904001064401700b2240178180c0507180541d80e141e1780d01c0020028445c04003201d081f540f5010402040c003141d4130152043c0d8800342d9400600700722a1349840300100f0035540c40780e40704400300602495014404601d03c0c3c4880d1951002c10003c41c801d0000f0784010300d040700700c008140703800304003c0d4455080c8110030240b011030407505c1c000d04141d1189551102c000b4074941d030003800007500448168010344102c0c18140d1203022a180380a40350690580c1020540385000311641c003c6500c840719001c801602c406 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 765822482 1250 765821232 765821257
    0x111015090c0c0f030503010501120b090f060a05030a0f0515071e1101020a0e0405071b1e020306240406051e060405040e0309030c01080c161a1807050402 67
    0x98504019998000704000d204610070712840000d102c0010f50345403030341c4040c81c1c080d403244e507100e624210025140d01c9445555030041440c1003454200d0703a40c2d000c4100c4d040441000c0750403541d940c040c0418440c0102c0d030841e96051142944c08410041074410079040300384a0400d95000a140c0361a81104178820b603032142c04240c0c1c180c40c100305512015001100a0044d1401116124510911a089901241c6041c001500c5002c4030203080c03c0500a03d5004242e610700303959080450a000504180440d03070040403026603400241c468024140034841071500102a0390182c10b11017204502c0c04502081d404d1000703007545505109113001d1180d003040340c0303000d00220927171009107103007170301c203101c0e215406509c20004d02000c0340c2500c3d68890204844881001150b4600c134244c1018a00f00c144554241003004010030030a181908006940d40d0f001000c80042c12940e4501d05200030415102810444010940c01c2001505030307500321030340800c480e0094401701034650081c4002e80c414007189040 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 765823732 1250 765822482 765822521
    0xb040c05031e1b0a03030c02131406030d091203081005031221100909050f031c050108120405060703050d0f0f050702121e07060905030a08100f052e1110 67
    0x800d01840003098054402810096868007840e40e0100300c1cad10640ea400d032a2503000c4100003603402c00704031645940b0360718100009640e00d081000681c49200d000000c04020a01001c590320504486840016200042c00d4810b09400d00d80011030642124030300040502003000c4002c4440560051075002b16016608004240d05245419003c0d101c0080c0440d030070320030040d031303890700c144144041d0a004c4c1103e00c0c200403015007815131005403541030300b090100341c0199506010444481013150304940c0e0179514a612100c8c1814103860700d000b01c0901c0d0024500b44078114410003451b80c4101002d0f18041c8040040d6152140700f26a940141c080c104000d50041041002807011001c0041c545455403820601d0000c00f5a9480f0650b54070f690308031016800400c5480d07030290800810b6600c1700020303601c0c0451502d040b862042c1c010f60791040d1405030400d408a002c3d00c1c41040450305140b002d029202c04111200f41e40240013007801844544c00c0d0081c3c01c070b016400c12440c0948070340006282d03100d50 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 765824982 1250 765823732 765823739
    0x3230619140108180609060603010e071212090b040e010f1401080718081606090501050a050a0c0303060308070c03050d05090a05090c040f080c010801050103020f070b040c05031e1b0a 80
    0x542e526000340803190f00c0f0b81300d01c0075040c0502e020400d40d4820f4000801402003824013100f41825141c04191802440d00b2480051140302c030002c06910900342c2240c0800d0001c8904c020079100344c25903802c0007001c1040010042008404100b056040701d8a8201e400a0710750b56402508110007907046040c00101c801020400c1d00d03118500045880b520b04031110001742d9103580700c0c0c0c030301400e00503540605054640100f22483e009003441c0000d00c403e0800902d00946600010103e2207a503d110341803208140002c8203041c030a0340440003440e0301c030f2a81c03a600c0099003000403850034144030480c1c00f03100d00601a2001c0c2e208205944060401506c18036074103040a040140d2140014103420000c001030000046106412039190000c2043c83c000d401144450b000041c0b1602e416009541410300400a40a100c0071440c1102e0b00e0f039810058440468545103462a982c4080fa80300c283d2503c0f401c10001c0c624102181c0c1e950500092104980c007145000b9000c00300346840c290180d620484d50030080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 765826232 1250 765824982 765824987
    0x60203070f020402130303021617073f0b01140d15230a0501060c0c030308060307030206040b2203020d02060313210f171501032306191401 61
    0x380741d4801000542401010356081811001d2a4020f03001030740710715010107548200941e110003034902e18030030501c0c1ca0200c00c045030b40c0f1002031180044106040d82d00384850014460450030741c020112030082e1340401d4030322581140101001c1500c20303c00103000003c100705901c0044401b41c0d400303490b46510007007685400280a400020700e003079050b1075850005080c0d1101c000f00704200c410312102d298908084200704204d82058003c1b40900080c3e50401001c10000c0c0b44c21401c82e90715180c03500c0309aa400010074103100310766000942007040450003040d6250490041c00c04486040080e21900304191130903080c0ca040c903c006504071102100c15809810048011548011a2000c0117180603d555612110f28880107002c17213540303042c05140f0303002070388550424107810562810460703844820b841515589800340620004501d507484185031a4000d8006000e1000e0703680040c14120404018804070200445440e4440c0c40080c0724200b80c05012401d400c140c41914245480051125005 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 765827338 1106 765826232 765826253
    0x90b0d05091c142506020309013e040b030f06010f080601121a0306010f0f0803120112062a1e0e10172d0106020307 51
    0x55107a03c0b018031120110b009480784da440000410130404001c0301040240542ca500c1c1c0480e05000d101d030f0155225108031f5000b8407a01c00c28002c54560002030f20b1403102125200110801e900d01c2402100b407030711005146a40c80e007621640102d00d1508110b6008c200d1030b02031780c2082a03c1d64003110540d810606401c008005003090000078104541c0e6140034840d440c0d071114448641010585414400500901918203c0d61260f20b89240d0f03040c00e00609c1410341c185070300040c3e052000001c5070b030041c02666100d030042e401c003040c40c1f5040c91015002d0701c00d40d8940c8481003810a102d0020302000d07c20f0200e0000003010411701910854804480c1401c403407854002c5001c0a0f040001a00541003c658105410b0252901902c0001c61801030305010030995013001108000c045501c0c408802141d0300b10984038401e00d901036190401d0040d0710041e08248490000950000714 = true := by decide +kernel

theorem cover : BRFrame.Cov 765647482 765827338 := by
  have h0 := BRFrame.cov_init 765647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 765647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 765647482 ≤ n) (h2 : n < 765827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
