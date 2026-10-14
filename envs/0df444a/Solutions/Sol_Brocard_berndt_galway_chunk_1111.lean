-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1111
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:17:19.745892+00:00
-- url     : https://prove2.me/submissions/3b4041af-15a7-45e9-96ee-24933785bede

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 199640287 ≤ n < 199820143 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 199641537 1250 199640287 199640291
    0x608240c091206010b0d0c0306050d03081914010e1305070320030615150f04091e09050d1101020406141617030403090501031a0f030304080106081515011e030b04060810 74
    0x703580e00c42c003274011001141c2004120040c144a00c4c0c4003652000d4000380f00c42e50003207541070454103c114074421922410440014166158100b003480d2540120142403e081141d280660000149001600c0001c0e01d600c40001011001c107081407a2030305480041903075050090f40200110317034a9032544c102d00c801d4100c800c9140c86486100a268074070503240e140004c000308210500070075200c3d810800620f401851141c0d00e044c003000d001e0b01103079080d5100319030f20341124200d0440c2c168010328065000002100071882c00745440d20181c0700c24a80c250401c1c0000c6c0200e01c2a034030008098110000d903170070101500d4001404800e0b01041c2c1d0084400b100444d44500002c28507503c21310540e00d28144180c0040c0c2040c0554040014021038841d550740d051000700004261000c007070140070020090f40c801054505841c20319110300c04001081c0c0384c40d4601445902d54140c2e48907241d03410114061003d80c0c44042012800c4010b00b420754142500035080ca10001104000000e003d04210882241 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 199642787 1250 199641537 199641551
    0x301020927060603041a090c06070803101406070b0c0d0603051e0d1d24070204050901020705070317040509011413060b0d020a0306080a060608240c091206010b0d 71
    0x800c0f2050100f40d6000c4c03c1801140e06400341d092009a0300b6410860034400c85039020100310016116500840d01142c07241800301c244081045d1008501c0c0103440400c10300403020290710f000c01c4560260348806040d186100c1c3c0403c0b03451015004030303001030068003030070300c8a03d48a0a0880d514400350007080300c1c2010100600d015100d000c14a00740140065540350902081008222581da150321000703a0f00c5141da0940d15042c80070390f40d083c1c0d24414044070700c0e82c4901050040008440004101c0c1c00264010810b1000090010441c181a03d607ca8840080b2030f503111110401030003150401034011001e8070001c41c62408034088424140411181040e89140e401d1030790050780c11911a081c4902000e00907900c0d81d80c225005890b121500d850005803035995130300b23020f242500b0200140d03040c583c1c0c0c19062201e1031303050140c45c031400c2d400320b21000c46290b001500031400d58000d0800284900104040c002503036003a112000c00300d02501259210f584031800e0300c01c564448044114140e1070050 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 199644037 1250 199642787 199642789
    0x20a090b03031806211602070e0403080c0f03090a11030c090103030f1715010f090806010e060433170303011203050f03100608060402040308090f030102092706 70
    0xc0e404908901401031400c0600440c016503100501c81d0001c1d5100e88240078005c44a480014030322004020a11400a241000281d5110b00d103182c500d48030864001400c240714a41645610b260003aa25243c2100566103440380034011f8040c02c0220f16802c00700105000490300006034082641c0d0050008810410080d02019540c851100205800c444507500400c0070900a40031028520418102109180100030000340600c034220707420b0002d80315400034440d4a59101200351300072000c600b04112120f0428400c1a0346d02e00500c03e440b0014107280000d41a0340390364104801d0702d540403072113444108100700704021346c90001c041c25000140302c0c8c0000420f0441c0368022280650b0585c040c510316420a07405d400c031006194416020700c20100800c4540c0203015004500c01c161a070700c00196142448001400f00c000986014481c6006000a00100300000202c4000c55005c45a80041d07810f104046406401220700003944141140707040c0301da41900318549040c82031550703c820500d81d1900 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 199645287 1250 199644037 199644041
    0x1020d0905030d030509010b04060807030b060114030f0c1905030612030307050a1107050307060224061309171b010e060708070c050705060a050a020105070206010803090f0625020a09 80
    0x1105465042d030119156081082c0030b03602054000d06c01c00008212502e042000c1070503626654002005640725020800c14001e40021451f04001d092808244000d1000c20a0100d404040c0441c00c014103540003050301c3e80d00c1c0304200d61003120f11900031407111540c404054003941040b81c0007070081544150003640028040122445034a5075190242460343c1500203c590b441c3c034001992070761065240205a0f99403c0000310001c00c2558000c1500d401c02051b20900c1c1c000c030f10f0020380094408024481c003661452403040c0f007002154000180e10640f0f052644801464504429110b0310000313000003c1c441d0643c110008100d818003d010800585011540d41d010072074143d00003400034008208040d20810102199902a4044507002511440040c900d035002040358030203e440080c0c0c010f295502030103803d078004d803c0c5c00601040c0d85070280c41512441555041c5118440b00c0740352008654890055a485269003050000010318100245040b6101060107a12541c001c51000901c50741174 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 199646537 1250 199645287 199645289
    0x906070c020109230306040f031b03020c100203120703020d290f22020706050106031416050c0f0102090103110421061b0314010f030237090b01020d09 66
    0x40e982c0e0308405103082c4020a2143c8144e00010b01d06050708640c3d45281d40c1001240c0c02a4020706030180801c00700d14004c1c140b41000d01c801c00309800d016030030401283d00403500712020380c01580c07510340b2000600c00c100d08500c078503142603100990140078004d41e035601d03a001e0424859882d908002d010076869250b0742102c02c140d0402040c05c40b4401001090030310308801241000702822604100a045c14109036103410040c1990f82c843e40820000306206d400d015031350040c03600d400c04004030034102510b625100700092084140c0c004200c10347c03080d40c2c401c0d070860704840002e4040d24030300440d180800c1c0c00707940321000050004e42007110b0103038035189800468040b44c0368034100c404100d03100c400c0180031640315001038401a9031800c55000740b0203400c608402d04c141a80c2c0000307100c0d8035440d152171384802c107070444091070145d00c0d006c1c001a00c1d60342c0e01d44806a4410b03e0039901194402d500c042400c440c0c1103d84212002c2d540002e079051607a003000c2d600e800d09030280d80000401d441c01700d6041080d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 199647787 1250 199646537 199646539
    0x30206070918020d1103130318081b19080f0106080607020703120c08030403030f0c41040f1503150e0a06030c14030c03030c1c0203090901030303050906070c02 70
    0x70302c00101500003860340c020011041111070208440c1c0f04904d056005400840e4903481d10070000002000309a400940040d512000700e10810b421810703c50f100741d0351800080803040141400d00a540b00780d036240301c0c1e05290384d032808020300300c951251806504e0f240e001c20150007a42c28040d01140c80200828143c0c4203104a0303000f09440d9185444c0d4804004408440d5010302c9403d0890501051038040110700c224003e4401041c100707070f400c03401b2045600c0f403a28a800c020315280314014284080c50059101104400c40e54100600d500080f8039a103881d154000f0202800a0009000c0c6082900501100c111694400e00b140b1450005c1e800d440703208001c0350313014241490600008078109480368012071022400150304e900e030743d03401403508003503042482da4000030300d5220504c2c078040202c01ca800000f07034051402c113040d4000c80ca54030700c006a2000e080500b10040240c05910820680d6865200100300c0903165a590802030002c1c2416200d881c5540a00b0001070000b81c003c1b1030345400194 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 199649037 1250 199647787 199647809
    0x614011803030c170d0c03020301150c020603010b07050309030613052b050a051207030f0606020c1c02031002030a0506091303090308090d020d0b010f06260703090515040302060709 79
    0x20743d40300080c1303918114902c00303040c40c00c2c0702c2c02c05914044e1003046000740302c40c1c500603500d50600010071140400a501e07103003088000344071a401030b05c4001c00d80341103410350040b41d80c550555140050440c000e840c0202e80501c1242d0803c000e0451048011400c1c601840a0f60b03500c5103060b0400702c80d00c400a08181000d0412078110a00c01c0c8103900030f140342c07400392805038286080791440c030326100401d0303c13014002921480280c00d180e5080c0325000084c400380c0010904c2c0781607140071400c0b01068000700d19030b1000040c559020754030140128181400302c038208541e42e142003501c100c0208801e481c105e00503681d15000481411002c101c00190541640f65891190b01e5a501d41801e80e22214030640c1116148000c00010703119080c1c07a8048030302c1003c0401c1607604010482d807419082d80d1041c01080608841c100382c50310f200310910986c01c017210410b0850360b203020301600038008400b002030080c4609031021903c5d905812034203000e00c2c807907400e0b994540c4445000312450080d85c0551380d9019 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 199650287 1250 199649037 199649057
    0x318040b0306150f18130302120a020712020a0e181c1707110a05070315060326040323010605012a050705030a0b07020f030f09091009061401180303 65
    0x201d42800e01910112004001c0003130150011707105120280103407407180c1840480045101050f80520840104840d0310300171500341106154025a242c015100d840c488001c641800006e540314900f0f00406060703001455003a41c1003070b160a40f0403603502c403000748103030188100740b14a0304d518461000c0c4540705903545418034584c500744601880c0c0041d024000b030021a1110012240080c4489005140a9005084001d1540c203040e01403508203c485245103241c01070900c0040c00220200072400e0070803070044c4e50700300200d662054a00c02c0c3c0c3c1010304070102e040c90000e80f021900b10320101440b113a030000d2081d40d583c0c40064071101c960010a07000721051003568002c014aa100030351041d030143d4101c3e011503907030301c02007030502103001c00585820227a201000300803074041007009425105030b00110302d400e42c4480900918090810958030aa401c44086a000450112030034041d02d26000200301c1c040d59803650407103221452002c2404038203103a104c40c02c286c03000e12541089030b406813110003142c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 199651537 1250 199650287 199650289
    0x726090103150801050112060e0606011b03170a020406030c0c08040b0c0319020a0c14061801020a060c0504091406030709020306060c1603020f101205060a080318040b030615 76
    0xa00720210350000c07a0018400c0c0012a40c0d000d01445d03000b028104179080c1c0a201608101054402060160742d072580801d09221260340c0c0b24560145c400142207509140e4000d514007100c102c0b0148040d000003640d80c9040c810003c415500800481d031041d1000c01010005400546140c0c114180c081d11040c030a000070840880d02c1401070482c1e0410b00181e034540300740465018141d03002d555910005a06c410303003c90801111841203806840203519562105034907000082ca0707403048003d03007240d120b48005442400d900030440781c0c142950250381840103842c1244003c00c6a0464400c11800714105028048100840b0304540c5c0074010103000381c802c0c681442d038030344065440a05956042681081a180c8180c0305001c10403e00700e4140d10170685502e140108140f2128085460744030300c0e4001000c1000d260850300b07034049000782c1003000c00c0d9a6200300005203121015441502c49020028659220349201d40b81c2581c0d2590455081017410844814599607050031611400c4202c00e10034140d400d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 199652787 1250 199651537 199651541
    0x20c0307051203070b010306050901180b0412110f0f0c040c020c0607170d0515010512061005191205090109050a080306041b0c02010e030309030a0f1b0b0726090103 72
    0x10041841c080381c0c44d19101c0d07565400c0c242c81c268420f5a08542d243c2c10f02c108107500380524001e00a9005c05107200540365144c503000454080c0c80205503042c50140c03c42c1076402200204040b800c180140c862102c071940e4015140e01100b140448907005d920005200d0307192038841c0d5003040c001030b402404c01000640c01d01041750f000080554506017140607107000b0040200081412003c0000d000c0307a18103216400140f00a10800c2d0719040c04810300015020030b0a501e0125446082210030340d4a11003400e009980c1c510a85140b070381d450010016100480d03030800c611405940310341c10204466036510006070b003201e80d000001030040e00b000a40c6030102d51205c000c1c54000000601c0041d1014007140c4c52034110800c041c4000208122081720025513810514980e49040306030055407400f0342c0d50001a44a40180b20014508030405043c0410710900410002d0744115107083c4044440d240d41144001c0d810a02c8121400807580100c1442e504454001940740e0b4120f4081500340243c80e001900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 199654037 1250 199652787 199652809
    0x2190305010e2a1603090603050a0b0d06020307032004030b06150415090807090504061406210109020d03090315230c0d09200a1d041401090c090c020c030705 69
    0x5003804050020a01481090741c50010091190729210b120a1a07d040a0290b49008041c03480040ca0705a6010081c0c9a03023420410b481d030302070401030f5a80d490b1041034000300214110f65840149019000c00046440c4006005680c0140b152602c1c0340c1da0801003040b80031344d5500d078070803221051000304406030550545031181350b214100300001c40d8413442403506d403401552100b0003607510b0310284801d005071889450042a10558100b2440c604140131400b060082c1117480342c100c03c243c007010001c10b020341c00700048a0f80208100d10051072800d0051012340700b8001500d180c1d100c1c3c0c44030000314910f4441d00700d0940702c4901546003221927000d640300c0c441000744600910340d13082180c10a021014450815064864803c03c1c407007442428550401d1410407100da400354603192000c0c0070071254228055580e401d0102c42210380e641e00d1424500c2030100c030001c2e2280d0b41c00c102c4504200007030403044906035604820100540a00070710101d0b41d44100000c01501a00b0440742404182021003a000d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 199655287 1250 199654037 199654111
    0x115050f0f12060a0c0f0305100e1f0b030105030607020307050a060c05070503070614090703050601050f011e050706051003030c0b04140f060405010e0606030d050c1002190305010e 79
    0x70140b0848046260401c030007115042480350703854010040c1c007a04000600c200100a1030700700043e24020303030200c903008424051810424682d80c00948111a0300c0c100e02d90180a1b810301b003904d5a9204151f08240e08203000705407081c0504800650003900c008159a00c00d50460020180c00c680703a2180c00007450b2a595090802000b00040d00120b1010002840064891280010401440394440100032800340c40980c880c3c01900080021400016182d81500c10480f01d042070300c00c40c080182c0d000c516140781c84e04190850b022002500d600100a04007850191100788100c0c0d96583d034800d400c25050200402180382c0c1407020010860454030190701c02cbc400d40380489864005010146003130721440c880c0c00c480e4812010081000350a000b40003480420b44020441e5003132640000c0c1d00d03200080001407c00601040200c06c6041c2085a4885004216021903580c400c91250600c24403910b0044000300341010000199500062a40c512809070610441d266542005a1141d007509a043e40303 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 199656537 1250 199655287 199655299
    0x40803130201120e030306010810050d081612020a03020d0c0f14011d0a0c090603171305060301121a07200a0c080601240917100c0e030115050f0f 64
    0x1850680f5442d00c24035658400c5030b8000c5071a49000c2000402420000f0502180c18501c2c0700c0800131502d51010128076250300c907090640715190b6400524017100f405802070002c205989122040680214420000c94042d50980e030400b50034030415201e007860100020004002440c480c40440c8960054211081c0e60000126a581c010501e840743c20449013014a0f50740c001c451404c041207544090307940282441074050080904d140c641030801840310031080e840c10400500e107501038440748000380141500404c62070320ba5844020b126803034022104100c075000c0d51b0b41c20344500d007507035110650700c9580c05a03aa01c0d803410b100e0340a10314031182854040050b22502d0214400602004640300c0604401801403807150301d00f404010104000d02c60355468004580306032120030340c0c44040c120584400020441600c08024800c900d003900501d110189603241914182a03a0307032110300010603040031402442045101d040c01d41d100a92440790540c4408600f1a0018504100c0110484024000c0c46 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 199657787 1250 199656537 199656557
    0x30d0c030f050108031b01150e07020307290702030909040201033602031e0a0f080d0e0706020106060207050d0209041a010303020d230d2c01060815040803130201 71
    0x10100070b49900780c005603001e4001181011000c0e0300c8004510069034a40002d200a2111400c2c42440ea001400b4081e112100400041c0c00301e4002c1040b6100780c0c0d803089504031034403030040360849400e4100d8004101c0d43c00c801c01240c406403000050f52900b24008145100c15161b40e80150014050140c00b881200244204080f20301d808003816441044d4022100d481c0c00424030405041c440a12074072010702040001d8201c0c402d2001508141417a403120100171241118200300c8074500681140d0702c0c070031342442c0e611760318920b01007030210450b41035030001d2010540320402a40c0702d011502074140c100c40d0444141f03000d445d0590aa582140c06a2540781c00e10707030046110b400c402800d800580143e80710085400302540d00c40d408030082e45001e052129182a00c02c6441c40c5c6100b0b659440302000d4035a460140442c00b41305010041754402010120121150460700d8041c01d01440780540754051804040150a00030581c45d1081d80c0c03040d11030b032666070b804101c030780d0400c500d1000303904020341c2d40c030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 199659037 1250 199657787 199657811
    0x2060c0901081906080a030e03010605121908090406090c090506040612020706020904020a0807140403021003020a110115060809030301050102030306190810050906181009031b0605070f080603030d0c03 88
    0xc1b50300da91034000d5a40705600407a0701c0c00d040c00e5036080e501c039501a20a1200380704030030740b01090b8510802d14030b800c40352000c00c0900b01000280a1004103a600501e0314100040c0a00e1680c02600c2c1d200c0c00c0e4a440840c02e6036401001114007843c4661008189100c0700c0b02c1482003594024081e0a04c14440141403180304400700302260010318030385c0082030100060040381a001152042c2006d03804800503c1c00381180d0118007611400c601c50414550081407006100d0f01850020049042c424020001303018a5000c2d9504052907220300400700702c0640101702c03c20303008400c6074103985041c1c00541c511749421050241103c1507511104c501a01c406001c103810704207101024041036400e101040758203000044508213003000c0d100750044130400c5100503401c6c90116556107400c40485000800011501b000e40300200c800c25414012103200140d5801c1045aa00c1540143c00c559501c1c4a254401d482c01e444048042e0b460316031540c42031121000058843d003021400b102c182c83c001c500307334030951 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 199660287 1250 199659037 199659043
    0xd02030a0c0902091f14030c22140102030301141225360f0905030d27030806100306050d0507030204150f0302090a060b0c0106050102060c090108190608 67
    0x1e00141c2c0141c1e0001540b5510b0b01c2e090300c141039520050861024250804480501150715201ea050f400c07107004000a4041562101501c000c0740740114407500b4200fa0714498103003d0030034014195035503603035002c40e12294800401d80303050750040e00d0711a03610780c440780c108404140d81c2c00e60704200340f00303940920300c1c2d4020b4031480081030941c048030060810f0405040e0f072a07454032442070b2806030412202580062181e0f580ca0021202070406c0007900e0001100c5c1000500254803010f4480e110008049007070303400e59889111480141184846141801c0007900c0c1c40d84110400940002c01410100b5058502440c3c55205101542400603803190340c1e42c0800d80c840307080f0300c017a52942c0045000b00152304041c020112016920005a00801c1c100071000c0d506a8480c0006402a03011500192601e80f4660091380500100401107031951150030001d80070340300d20300490380140203860200b03a0610080080d50808003050711920302e956204c0d00b44a0f12142001034401c201900c0d098002078400c424 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 199661537 1250 199660287 199660289
    0xc093008091002061b0f19110a030e0a0503010204050303040e06040b09130c0602010e1f020c0115031a01060c02060a0201150b07030810030c0501080a09020603010e0f1308090d02030a0c 81
    0x950082d04c00c1d8508164408040c0d2100f0b01084a694020480b030600d6000c203408940a24004140030b2201c00100c04045808070090300608840d8440d00004a05168211000c640f002c182218070600d443d40b120249801d0740990700c00c2030781541c01408188500a41100c01503030041011300006600505140010130307420094030202c4d466001012804203100c03440042c8800303420140020b1005190085a85548082155002000b404089245120520075404641550340e211000780318441d030b00c81c0040104100c130b00c0101c80c0812140c0c1041c0c41c1c400e0100c045412954151910302080302640c080c480e055102407510001c5560b01d1500c1402040713290301c02005040e00808103500c8090600e0043c00e548001341110070032690030034041000490012224040d10402e1800c1c6446840e5001100050986a58002d61200c0301100210f18040d0302004d4038030803144c1810f840c0450311075945091100882603800380903003a0030880b540d8141400a00f002d0541e00c094101c030002a441e8803603403207410117 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 199662787 1250 199661537 199661569
    0x103080a11100209100f0e0f030703061410060903050303040602030c090406090e011d030f0c0f0a11010e0904021503100503011b03060e0f01090f0b03100c09300809 72
    0x1001c19040090705100900b5030704190107040130324401c03003046d0700070381100e03c2145010711655522556604644041c06290000c0d43e01c0b55050040c01c054a508030f404c2e1600301c0750408030320482000007070017511400701d000c11240c1000146165031105c0d2629406544010a0940440c0c01003060411395112485410001e204400c40041c01c4421489080d094401090030101c2100e00216482c031842804011910380c4c0340080040f81d5134103010b203c021b04100d80340c0000384c080d0180055000034080300402c09052020240e888501d42c15130070040040b0b840054602940051140c0102c2c8541c4291100039a00140e07007050320b1b11a00e80c0c4100203400d4561400074014042c04001d618424181c0600070480030703050f00103601e041361802d02d0503490305000500c20a2002511f4503100c4041d801c1e60b41c01801d1491024054a94a01c2c0300d41090000d0801007884000042460800081c1081850340e0904400c0d504a580582a02d0703c500b80c4a1031a141d070340696030707508208150030942c1da51810390380d07041c18 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 199664037 1250 199662787 199662791
    0x1030b130617030a1e1b050601030b07080c031302192d050105030a20031602100b10032c07030b0609040305030f04031814030c10080103080a1110 64
    0x814048200e00354500c07081d0880c2e0b998414000c0101040d04107249060755803130000d10440c0340b02e000b80d048810200140d80e070360651015001c07003000c1c4040414072a0680c1d0081c003401003c1c0d10f8452045903c007004994081440005101140031019620000307410f0301e00007480513200c3c510b1340c0c0d00404400c07200e81c03042d42140343c40700c6030a00420100c2a2001c0e240f8072031481c0070750755181400281292000400d4101030aa441d100580b00f4828046801030041c10385074055224504450039516134503245100300098071030b00000202d04015402004051040902914100c1c0c04038082600548801002420041c0c000300b000c3c880c1c0102820260304440302c2c07000602d405491360404201485010340068000c0c0d2103d8100030200f50414122a00040d141110103c03d640b1814100c3c4d040c10040c81d1840c048141850000d4162154203401032880c00c00c070140c2e0000044041042681101500980089191440108041317020ec802505081303505040c8bc07901c000840010f035042c82101c036240030036a5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 199665287 1250 199664037 199664039
    0x41112150c0738090d120501060509010c06020c0a03110f0105060604121a040f0c1418071b030f0207060e0901150c06020f0d0623121212010302010e0108041e0201030b1306 75
    0x17603400302c020490b119180f1810007041d410444010990712030038414a041c400300f0600c800c100495079044884000a002c15501d92070301ca031034014281840880c0c0030321f40d44200ea8982c007481c60180704003801004003e025519052030804010501050323108107840c0b06c040c24604440c1c01c904604a00e108510a0b2101e0f00d0b4004640350541116495400040040300741c000c0d900d4094540c0f000c0ca001a0501140010aa95403501d003140c9010f80b240d02019011244001c80c0d04240e009001c001205031107800351741c0380035201e4a0403581e101c80e0450141c0d100c03181c4c90042040400f907440f03100c1c100c0714600e401000c5a40351f44030301c8244d03030084500c58082c0000141504600e0420321641014100808070707070b004522040300c0e00814401c1034102520880c90030810720a09903003003140752014004a40f026494070603010300f4823030072503003440260f01158038403888040c150b1160f06841d02c280d510411083e20180d503030741170b10a8407680100407410302d66644070b00c00c03296440130b44003034a001c20303004041042 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 199666537 1250 199665287 199665313
    0x10e060f0703020412260c0604200409140f0102070201020a0f03020f12120f091507050918040203010e0a1509050a02092e050315041112150c073809 65
    0x1403200190b00c2c1b02100d014003011524107804501a07401c560030520076003960458a2048460b4202e48030300d682d02c58034054101c410400f10389218a5100400429500040201c92103682030780b280c0c400080c0141c1010a00d03000007411015403c03410b034080d2046824440c0540045880c1182c13050000e0742204000c61100001d001040510f584041300c0c0c0c100c4040744c28040307841590381c0f0401120040c009403820008058904c1001071b20601c1000520b140b101301c0946a200d0440032007510182d000703500f4201c00400c042c5001401c11015607020010200002c408424103006201e8808101c0e2103000e006040c2000d6520706000350701401d08a0045080c64040740c011208100040d000a950f40c2500101000141d130086064501007540b6210300f41c1d203583d94508a1042d084440314503078069201d00303d040b59444002821010144024480304082d00c50b100c501c1c00c107000da03100040c101ca070080b1103001406800412140804a1500c8170101c0000f800c3c004140044100c2c0e48844650028100101e1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 199667787 1250 199666537 199666583
    0x309070b070b1518070c14031b010b0303030c0304020909010923010c0216170c040f0b01020d03050603100f020d050108160f080c06031012081803010e060f0703020412 73
    0x303400781213401200c0310628110f1000c0008005050f00b0910425113400710520869054640c500c0304120241ca40d00c140c00e580d840500000300e8030b40c10032580707801d00c03841c61810000210f0780a40c070b030424800d08543d22135082040802c40100443d469541300c101c584001182c3e051201d50134085914000d030006440401142140c8020b2003038000c5500550109c0c00c0100685480000d0380e0428100035949050080000c3ca44181e580c00f581d0424640714510062141c140e03c00401e082090742551000c0c43c5000742207042d603c054031441c3d415080310f4070b1258501c2ca59842503548a140e41009400d103148101c0c010200c0d6426809504141c2010314148050062488428041c200c4883c540c01d01505110441d5500c4c01c5c10a40c03903025800c004049030301b1142d512005001442c03c0c800a4402c3d503080d181c14070146d081031040d41c2c582030b0300f5801c5100c0f070718045c01008074482d41400281402c0d600c0ca01001c06145c0090031403010300d642000003258a031074491081d044c440c0a49400741e181e8001900b2142c0d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 199669037 1250 199667787 199667821
    0xd150209150702090712200d050c18011b14010906050a020f0301050d0f02130b090105011b0f1b0305010902030607050307020601120204020d050a05040c050a0510050309070b070b 78
    0x3040c1c1030401281d4010fa0310006456080f4004c1d180044100062821400050038940c81c0d090b0800c1981030f0111002411000410600780000d41c144026160750140050300c0c000c41041801c00107100100710115485001d8076185200c240070000400ca03255200d0708140e2181c0414080907075121400b94003405054008e10342c011007098002c6150503550050103078180011301985118004440342038051088404112003201d4000f0075401408d400d02c07603030400500051140c5400740075600700004256006401180e4181c03404d01110350020309031703552244e081c510782c032080b60088082c101d0f0740c6400342c80359401c401a5120b000000303042c1e00c0038010549040c0d802014030041000400400c60202e40c00f090741c80c11030340303104001454031400b4800240613019411804082614010400c0740707024040e0000b80c02540100313002c4013821740f20710a008134030529005894210340039114880c00b2902c42c100550b40305513064162840d450701e03038486094a9104a0b800c1d600310720404144035981c403411403c11 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 199670287 1250 199669037 199669069
    0x207050a060c0f0501020c01050903041401050901051801030603060606050c2b0c03020a020d0b1915051306122f1c0f05070b03160206010e040609020d150209 69
    0x216486180600061800c1d140b90002415203d0350300c0080c0400c58250107450910409200a00c01890401841660380e00144035141086c8140070505603113501650480b484007034181e4444d8074281c00e075070607090b06085410309075042590b192800004103a8520600c07001d8485603451940c0e0749004483d15140c503c1101300d128412404c140007ca4001516400c103680020500303108040c1c0c4541c0c2016400c085681e84081c0d001031036140b5500c104800c0e4001c45105401e2243c60054500c411110403080b1249807000c01c05400a00e0300c1400145030408019542c254684000303d0380c5510348a02011801c02403008841d60000300301802440d00392402c580440c40400c01c4502c4c00c01c600580081c8040d40e0348003a0085c0409001c0c203a0702440324254045030000c4e0840d085940b1281d54a8100403030343d0040f50486841c1c80c207502c10092080c40400c42d50304882803502c9156890b01d03240c40d81300c000d0440000c100da0084403003106200040805040d00d001c441c04240c016296546d00303082c0900035840035908 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 199671537 1250 199670287 199670299
    0x50c04050726240a03111903060203160206161d190603110f04030201050901141204050105060a0f05060a0903170c0c0f01210609022703010b01080106030e100903050a020705 76
    0x812001c3d142c90101c001120380106040b54a551006d002c10a00c0e2030030051840044c803120f0011003400b0543d002140181503500442d0b60f503002c48001280c5880c0195031070340400019104010546114034411810300c810044640c4d1003c4007400015051000b00c0f02c1c0c2440c4011f087c0c01004015018840d071124038402418241c500810803002c15803034460b500000341488804560301c40940d2259840248401d07450104603910f240c030b1240da0a10003000c5400300c40030740c00e00000514a003809041401241c2040308801e4059007410100000ca13004110098204180c940002022841030251402c2d1102906145503440070059103184c01c00400e00626402800800c10050b1030342d80c0024005403401518110300d512100d0407800c83c0107400c540d404102c0d424000700303803098851030154039460607010b20f408416a20b5602003e0500342c0f00d02d5159580890f200d0001080003500a421034500c4c811258180c8441400c613981c47e0045400c4024207500107000452032000e070079010450306018290031034203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 199672787 1250 199671537 199671601
    0x6040914010915180807060e03042d091503020103020f090402030f010807050103090809040c02070b0a03020904050603072103110d0c051b0619140a0305040203100504050c04050726 79
    0x40c20303817144100980200443d50755814a0a424014015500500001070140c103810151003000c00114450f18500d0400300000c0700d0006403883d00d449103000c88464049001303021441c50300150000e4212444115640038204028001036030b071440150311414841400440035414148064a0411150000b41c10f161070001c000340418004015203420710011500410101c420540490400c912540040f100301c8010030354007003203509074018140c6c0c400c06840820040d07640c3d6081694035216486103102d020401e42006456144428640c1c05290007402c00c001d90020314864280f4007800c0c1035402c00050081b04840302003000502000300c2c8240d61583c0e100729403810303400044c1c440c801d84800710794003005091000340c0280900a02080c04082e0210f4a440d0001005c3c00380140c101123404901c680030312640f0a0951580c0d102c0c0074002c94000d001005c451000c40c05000c000c00c40a4002d109100d040c01242400215081c4c2a50807980d42e243c0c1290300e4100b40043c50048100c3c0304010550b840c402c50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 199674037 1250 199672787 199672793
    0x20909010f06141303060b22060513060506180d0f050102031902070b010b0c2a0102071508010308091c03030b090702011a0402030c1312120c02090604091401091518 72
    0x4200011789400820004440c51401e0010b008002001172090031008100c48503408240c1503805542110820b0b910306030750705928519103080326224010380e54400c3c010b018956007007a041c415002035100180152040002603200c0d8030355010b41c1d40702110541e4001081100d40f0300c000740c0010340c0b081c0c0c9070003d60070203c469555903001d031414020b8560811020a043c42020000c00181d0721881f4158441441302c1c8030480c1e0070044113000f502403805881458800644c0030440707201d001d2a200c4507a10840b0303a07420b507030b102c400e6039209050940d80100c2602e50640342484120101d0b2031a8400d48000502c2244503040c4028848010140303010369250501694801c1c04404001d003204000301e80050f41c07956900c000d03000e01d0060481d0390742c0340c1c00315500114500328004404440d4500550805030508006901142c0c40001240000e410000f20303404600a410150054040c9510587c0174811040d582c2040030308581125805580150030a603409010f600c0302c2c0b20301007800319040403000114030152 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 199675287 1250 199674037 199674067
    0x40b0d14010b0405160c02030c04090c05030d0504150e0a1a1b1f09082803271202010e120d060b0f0f210705121303020c0103020706020909010f0614 65
    0x10011009106d00b0503c101b04555081c070a00841000c002c0c000c0000c010141401c0d0001e1049006c0c5602138401ca9006051f41401103064904076090041840b440c020002012110100c1307100f040c0350000d2448001040000c0041c492001c2000192002c1c0e40354203030f8416405005000d10b2401c205504000c040e1030780070442e0010080400510200402c110300c00349028402d41c4903242d00c0b280784514030800c03949040e8603e1500c51400b0459641400300708070021044400c072203110403403150f143c1d00460070300c00110b078044c04038180c007014000095441c120b80e10003424164001c0c3c8019040000255404100c4000c0c4582405072400402d91410070382d403a28160301500c04c889020103907050204107659040d5034510810712641680c91403c00c03500300000003030119004015000c200060701400180c1d401a503010000e2102d4240e401440e08a4220f00194001e40c00b10700140c901d103401704000201921041c0450b4001c11070b00300c400390828644400146601403000844641d0b2104229030b180c816010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 199676537 1250 199675287 199675321
    0x7050c1605090c0f0706050709061805100c0303020d050c130803133501050f0105100e0915030303040c1517191803030c080105010203090d060b040b0d14010b0405 71
    0xc0c83c0e210382c2c40c1c4100b2850300842c042e44030000e0069041800b00480e040e4424200300032900c064540000182c1010040e6150001078050503420044400d428420640300748005020b070b070700a040040c6403402a00143c0280c80b403c803240240b0002c009201e5428040100e0424020540503018605205000b00641c000503000e103c2c0a41507040901058580d9004108091012000070b40c01c508010344820800e01034001101c0c20065030014100004046c20042180c3d18444034079601e80901c3e203145001c00035400005051080c0705800b4031080c12a6403010402540564010155285682e1500c1c0c1c0707900c00214501c09003030030416003c5103240c20390144111142c0010070340720030b80780030b100130740200d0000d04110704003c1100d42c40340c42c0c400c11705406601c03000c035070241759a9401d141da88030030059030b4030320508040d643c2000c15840b0380030100307034107a020f04007a40000f0004134684c0e4801c00080c21000f290641501c0348600d8000310501c5610900c43e03140ca101094030f080c055450000a09440000c032 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 199677787 1250 199676537 199676551
    0x150d0504140d090b092b0b040308060d030f18081902090703110d020c3306091b0c0a0819020721020907021204120c091103160504050907050c160509 65
    0x901001100d96842400c11544036006d1031240f280d0750010b09140c180c0c484190f5094006c10207000119140e0708180000c99403041d0140c640a51440b8070660844502c0140d000103403245031381e003038013041c907a00900070411f01944024601d95a400180104119880c018080c48107161502010070980280101503d211200b03082c4010b0f100e4009030a201d00f0440d81c408406440381d003080c010a00c0e400354004455000c0e03103d00f0030010300d86d500700c00d01c180402c05841c543c1024000042d507180038000c84000300342102d244020784081c02c10030b0b0344810442d00503450350340406c0715074003c1184403607040100c030317004145160659243c1e505118004214080603d4040d01509034000000c1a050080080c0794400074140a2550395039646c0840c803400501c00c0e00101c80c2400c00e500b000030303601072501400c00c3c1985a045120f00d581c1701c001c0385850024031840744609005090000042660790b14114510036410360b02d90f103542e54950a0154280021442851107401d03403940244000d031035040207680d004070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 199679037 1250 199677787 199677799
    0x1080412141603120e030301090207020d0c2409051003270813050a1d0402150a0e0406080d0f050a031d0102071a1302150d0504140d090b09 61
    0x15038210396111000c030341100c00d038200290500300100781c03041040d036441c060b0b039400302005030142200d01035800c003409290460b030007400103021030410380c0c3c01030031240d00c01014001468216601c0d0b159071111070b406800c555801128548a183d42c41103400030300308192070460301140c100340000f40d9031b51814025800300342e41c860051004414020f0070300482c02c0c4855002d924200c0500d06064a80d0006100707a0703800b00c170494006400c2c02d04012800a80b52400d004140c0703103d035406a403411040060003641c3c4010702803d44003402058a00600005282c0d954080044c45550305000c2501c0a690050030960f11115800f26901e900c807540c1880c07060103140245d075440903074000710058882c40c694400001403a480080565070154024146280301b83d42d004841000c41c01d0050b410b003400c5a0300846286440c59520051802081102c2450721404089080ca139940c2040c0046070000c0707508452032048010321100083c0308000b049102e20127482e186042d07a040204c1e20f006d500410740c5a6018907 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 199680287 1250 199679037 199679063
    0x90f010b0f1602090f0709150801170102040b030c0d110424020705120703060f020906040308070501020706060806101707050f060409020a020303190b0d03050a09030803070f0815010804 81
    0x34108a07031000030150000c044620707900748691794400501c820307100c00303000c107007814400666a81d20000c42c1498111036290301d00160321b40b100c0f03402020001000c400e40b5550800003c185480010041d6000310800403541c0c0e114010400d5490454101d010b80e012000024003040201c10b408803202d014035403094502000a40c0035810603071030180300c4d40010381d1100380008052144d01c40080c00c0822039000c2c2da000c2c00101d001180310340480c80b4900c1820b0300b000d0200310600204100c80c0040088038400c0c00011325156060301c801e4105d4241d50070440722a00100e00788808000081142e00c09040c08000340406000703850303426030740ea66441c81103902408a081e280e417542e6417480d080c0c030000d265001c010b540d11034400c1d10081d200e50045600030501300f402c00281032005100d20a680041002070f180510388a031507102a5050b40081a0510400c03581c080d0200000d4a01e401960044250751a490341c500a8500c2c044d042d424000d2500c000404007010380c2c981e90783e008030010380046d04110440605 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 199681537 1250 199680287 199680307
    0x302160f0b1308011803020613330203070f0e010215010515040b0a020a0c0806010b0409050a020705010c031506050c0a080a110607020706093203010f0f0209090f010b0f 74
    0x40c00ba41c0e10180d5907528040d0031103014031080ca0005a02ea220780d081d1980f40c0daa80f1403a1511103504100a170001020b030480700031690030311031000c2e16403030030300c13080c80407032510700741c1034060744d000701c0e0204c0015488200c40841039810035a00140003209001920a441e0000040748200405118807440750884603a51b50000c08900122400342805c00495a5100d60300d400196407809540e030101c0d0100803008000812620202d5400d050f650003402c01885c1074600f880010143c070010b0f0030810415800c01c040c00000d0300900c00d03840300401a44000c50124124480b08a20b420554001403d000c1c041100600b205400b19241341c82541c401c40d01074491090000842c0c0800e501100f0411602c681c2c3d05102d041500010f01c078040b50169603400e00b5040d180d419078400c40d000da500b00c003c00b80591507501118000e44004070340303031140a8000a50548456451000c4d656400080c1c040d4a900003400101414561b076450f40c0701a04c01c2558441c2e52600c10400418842c0040c040c445000c08181c0c4031b41 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 199682787 1250 199681537 199681567
    0x91e010306030804030602040f0510020d2a0303090c09092a0b04090f060909050a02010c050c03010c08060a0617070f050f031503060a060f05060702041d0601030302160f0b 75
    0x10b1500814015100c5499180c1070009520a000300c2c9a030355910000007d9600d0001c1e0403060f100190303800b80403c10711404050f03c2d00070b60005000d81d40e0b002c80b20b00d19400790f1001c0350500894000d5a010504085500b0b0581c070803a49a00150040c9092841080c04a00312130210701075009000131016110ba506056001c007175607260001e041c01503000030b002600c030585070482d01020301046c0e070801c061542d83c0000c60846032108030050040e04480c0003480598028100007111030301031070543e03849074802e900107402c4030042c07070741c41c4c0c080f50401051004504059003064050401402d0000e1135902001c4030340806040240b660041124800c2c015100230310420a4035150702c41c560503a9100c1c180292200d102070b0105a8240c000c1c4a00400180000700c08c0c004e00c400c440d0301905403a076241c10103003071208a6000d42c0e4260380041e251080811014202842034117203da011001d00015411460001d003003881c420f41e009061101520b061121807444905581122040760781555550000e20100705 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 199684037 1250 199682787 199682789
    0x31a010c1502070302031801030c0c021309140703060b0303070305120c0705030a050a03050f0103021311090a09060f150e0d0302010905120a0e0d0b0a05070903050609100f02091e010306 81
    0x1c8254000f007a150101500040a0035122002e141c1000455100500441c1120b80415490000482220425026050114040d002048114000308520b405912250340da41201c04c1202419448140c00304240902441240b00c7c0940c1100070318600b03042c1d41c41c024050301030740b9011080c841052011850005a1400721901198002c0590f81c0324820b84101034044c1d00a0441000030a0901c00001e603002c003640c080506988d40200300e81182d6112410305001400c2c144866012020104140d40b40344d074410010f20000c0440c5d190126205041030f043e01d2822860f6400b03c03c4401259003010911a0800b081da00402c0c0c0945003051000b249060880c05806041005030040c041c1084540f5500080c1d8000c00740408603444030040d4480d11410b02140d509180805010740540e00c01151400300c0c40d80020742c205030345240602401e512521203a081076000d69511310130f64042507032102102e4450240382102422140300314146051880465003507804e1141b201c10a030700c01c001c480b0b982d03030081c4e018070 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 199685287 1250 199684037 199684073
    0x60603130c090203040308090102070c030803090c04050108010c11030c0d0806060d05040303060f0501020f03191403100602100e0618070f060302090315060d030e0d06090602030a0c031a010c 83
    0x8074116aa03441c440c002540252001d600081c40c0000160041e0b04c1402214035041e4030200103d841c61958545210380c2d003000d04821428054581e50303d4060744c03036019140c00381c034030b03140005030b1142c4868028020740d05103404200c0b20742090101d041c013000c0100b034241c030800c542c0c1084025682d4000c00500c40b03104440031280810718150038402410390562002c0160b814540403022191340703a50040e030391041c1c1440a108280c2c41007080c100300c0303103011504280304151401c0150b040281c941c10002190000c80c4c143c52441140c035010070180d0741c100080d1101e24030000040004418103480c0319211400201444101d201045080c00741c3c0804214400c02004000c4100c503840e0781b51040200651b1040c20750324070910400c0440500441240701d118003600d0000c0440c8013a40c815a03043c0e44088848040c683d002c210740d4034100200742d00340070303521219108050060356072030100031f600110b500b08040401007500c0d1612010b81a40fa82001c1586c040742400c2690f00000d0600d004954442e45100d00 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 199686537 1250 199685287 199685303
    0x2010c200409030806041a0a091802030102040b120a0510361a040e15070c150b120106050105160503041e0e0702030a080c0715050414160e06060313 65
    0x1840602d81c3c0000c105001e8a01280c0030b0141f4069050b8041c020180c05507400d501081a100801c8003d5040d408524111541342d0606459601a0002401c98000740d02034400c0b00c00000742c1e40c1091104490040d4003220040e420421410191440130003082a40910b1010200203c0c0450204a0801c0400000042d86140304a124038280307164001d02040c0d0740c201c0203023042016680161509000b0f0980e030410366801011001440181420a07a0015110000b0f00408500210100c3c090b50406089280480710120301426030701c048c8000f0451041c0e0310040f60345000024400d580c0e00108032a0740801d0303111401d190040303030304000d41076100f1340d84141c01035400070106004840e01c800c08202140c200d4454454984d866103001ea132240f140d1300301e0000203030309900080d0b60070042c14041d042d69400365102c0380c4600c1e12429800c00b1a103040e82c003951442c3e01d208a05029680c100580035105280ca40a504410301d0200104040035020300713003511500380030000801c0c099112303064084032a080026 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 199687787 1250 199686537 199686551
    0x3220501061503020304050606010806010924080105030c0108010306051b04030b090c0a140108040311010507090f0902040305060f0624090f0a0332030a03150f0302010c2004 76
    0x410300910252280382218a4001e02410500f8040d200780c078400c58021016241d1591040300440343c001004112605020800301c001c1016980c80c500028080e0030395122034014500c1c240302810411050b80301502c40d5010490922659030b2003d03009044962000c404201d6854030722040c40b102106002d480804000480d002041c00b1071884510700039021031013514020949401030201c0c5810714000c3c14072103103803401c0d40c44c079a500c924501d5500a01074035100c51000815414a400e50301c3c141c840c88001440058180b003000410108a401000512030840c9024a542ea039240c682070300521b048000b00e08007000441986461010720101580c07403419412001034840c0c0d130925508800d070858081c4450320405561824195001000c0e039400010b2900560764a10700f04601a1881c0d040740c0c8229600d001c40e00d0013000c00c201402d400e0210382c401240c00c201c3c982ca455601d008580c0700404080c4c94031010005070f60040e66800065401c0040008602c03607001550344113240c210240781d003007440c1c208 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 199689037 1250 199687787 199687793
    0x1b120b090111070309140603010509010e0402010e100206040b1f09180f0515060402030103020904140c1c140114041502070c030c03021f05090f0a0305060f01030506010e07140322 78
    0x20171000f900c07001184841245004001d1160a01090081c141c001c1ca07200b005009215411a91035440340c814541803007810032013800b00c0e01081c40c869542c00541c5c014018031003000403d405203680300341185a8100111041c00985c008085684548003100f0394800f00b104840250105003500248c1120301d0f02c40c00b101c2c0c0e00d031982d038a000019400d1942000174010440600d002c0c002c6a04813600281030b40c0c40c5d41c64a0301c50b407030808100504000c0d588904800502d403074440070a00c410881d190b4003680e514042e6800c0c0503221113603402d50038000f07034908000c007507494002911030f58001c1d1304003411006a4550740c1d4104020f214040e40030f401512030710310000c01c00981c225003030152071082e100c2112400b08242060200150031000345e0120b9005d000b50a51420102d0030310050341c8c002000304440d19134a44520f410800d05a40410b0b117421050018428004200311007401004240402c01e05807401450003844004124001c0b240c0d40b1000003c00c050700c1c8059605500c1820507036030840c0500c418030f = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 199690287 1250 199689037 199689047
    0xe060a02030a1803020d030f0e120705010e01030504020a0608070504080708012a12020c010209060304050d0e121903111902090630030408060405010501031b120b0901110703 76
    0x16681c1c200040340c04030145900e080143c0d51804803039003e00415041070b850398041c2e03056446170000c0f004000c0b4905030281190344000b148441d81c41281301a1084070b0422000601c94055071240720705041c102003d020040e2120320102007191503515211505442da038900300c9907072148be40124218423720f400460020419489000701344e040d10728520143c10003006031100c1000c81244a00420f078040316440e18540d942d00182488904080010711b020703a0040042d515400542d0140d420b540b14040705581c0d80c1c0c01c121864a02c0c04212420300f201c000f540384141c0e4815000680310801c04501004100b0140200d03841010b010842c000e480d0004400041072010b0a00744400781c1c40341080c1c4c4040783c22410180b210320304d124528280303c04a032a482c1101c0d4040c0368421040340c0c091004000016041384103000d00e41c045c1c1d2044001040552440c180070741407010660782c40d8405070300100b04000c91b0211401011880e81e208460b00305030790312050440e0051042040300030f00c50340d00080c4d141c00c050b80a = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 199691537 1250 199690287 199690297
    0x603090f060106090806060112020c0a1104111216030f0e060405121e0912070609090b01050301060e09040c0323060a0204031e05030f07120314091c0e060a0203 70
    0x100201d80e62a0703078601c0203d58842c080e2145d080303550019000706806510400003000c0d484502803000d882c00002c04101c51910031182029590030100041010040c98140210002d41c44401c0059044c40c50a060103101d130507000c0c1c41018488a40000000c01d24065003000d50640030744a410403040c3c0d503400d409510742c441190101d41c0d82c029014124003104442c000e0b2000319503481c0750b1a2000c1c511840d00f000342d0b4400c120b0713641e014030850404040c400c1c0030880100541020381e00e207045c003458013084109030360754031006606100f0b041c401404550b5004074501010002194030b820580c03224103200034600c95980028200c514000c248120201c4554000d2a010300031600322007403a614908010102e0046000c002c11084210400d00815150610700d148032500034000c0e2480d22410034800f04c400c1e4407485085030100c05420f003030410581c041c45400c0c68a5002128941c081c80c2541c2d12540314206001605d036046280409003803000c2c404d482c90403501d100a040c2955a14140380c0113076072a008 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 199692787 1250 199691537 199691563
    0x60a0e01030b0a1a0a031b180b070210030f021e030601020c1203120c1303030905040b0d0f02150405090a09050d05071a1803070b010e070314040206030a0209060309 72
    0x82c4801c0c1445030900302c5000c01107078034034507035500032408060f403003001c6901c089131410402d5242c403001c016401021144418610854844031044200a90402c5400340c440d80600c0c1d9000d010710246e805a101d01002008105041c070f8005a0840d102034000000c1c01504405030445200c00801060707030100303000640c080c827801d8080725424000c020401a04824030b0885440e6074100b03004941c0210600d00c50300b0780104040da00241070540c14441c401c20139940768410f13000100822003c200ea41054466010801d90590b041e413044001d079103d10309a4507021030f00038043c200170407801c422400c007002950060503004010240303d04044400001800d1210b5040d500350080c03141101c1558019411100110760001000303c110342044a03510a0f001c009100c441340240c26100402e420300f0510041404500c107a00d507040341d50403c0110041e000005240c8414186400c189030b40420300308501c244d000b607040b600c2d031f507a0380e440b1013007140a8003685c1040c81d044031300403091265411000c60100c140c0f00c2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 199694037 1250 199692787 199692791
    0x13030801120f080f250b010603020306011d0402040819020301050702150a050405011515030606140d0b0402090d0b04050c030d050403021c020901060905090928060b060a0e0103 77
    0x10300e81400d01550001590000c040e10441c00b1444001003203103001d8100c207129000e4940c1448042034120003c41420f000c82010358118034254030070460083c01c2107014009510702141986003d10001c0c005260001c01c4130041a0206005000b50360323290103d4024dc218402a03480e004260303192003c0c09007504104030711035400c20b40000c0c480c900c005590210041400b08880254499400d46001004040e0007070391741d5525a66400d52055540b6442c0303000b444204811050802900002003c0f6807540d0485001c00c074030240c0c50368000701044c094401c0c1e04114080010b20901110015000f4450a480c07503410402c106084801e000642035014841d6010300d0549011f20001401c050b16400c92550182c04a0018841400581802d5400c000000310740c00f505500c1d0449900003070f0f07460b0000d90282002440e981d00c180010304052101030b42003080d400041441e10706903007041c941d106900c50081000c4004030f0089c01072100d02c5d08100b05056000c1c2809131b46030907007040281044407401d01180824 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 199695287 1250 199694037 199694039
    0x60905030d0c0f060b0d030c05210901050a121506091d010e060f030f0105070f0507020d1101050706060b0d06061716120614150322080c010513030801 66
    0x208000c1450090000150b6034604509541d56402ca200e01000d0015100703159a43c00928842e210702c844d41c01114041d03290800361030b10703d2604a10b0013801241080c00030300108500f140440b00b075020b442e911602400c1884e117078006100201e4031070300d110700403801050401481080c00b200718603143c0d00381c403440d6584034046a01e40c1075014500042d044000c009076031401c01040f09411034007100d50007403030045c4648100541ca0000914044089507403c041e17954841c20702c19240d4012002240c9618142401410081e55400260f1408034001d0040c120496841c40b100d03480c0e12482c00c4403000c40d809403081200701d40783c0c0002c81540d0015405484045d240540205245000b0822112080094200e90380c1e903a9072a9200c5210a03201c901c1300d030a000810000c10103801080c0121000342440f00c405501488503441002100c4003245180641d0080400c24040c02491030060507580081c10000b0500700402442c00c00c695201300041c10b1484d510304024010008031441034044464041e50314142e460b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 199696537 1250 199695287 199695289
    0x43503090d090b0d0b01052209050907051507060b0d06020d061a090d0c050a1e060305130308090c0d0302060a0b10050405041e050408030103120215060f12070f060905 73
    0x10360b0a80c0920703034124000388030890200c8555040394a400c6410302d0480d05048220700c61490111031b4014081000707041c03003803c3c01548418400c00341c0c890310320300003022440e02c4c00300426640c02c0d01e9400c1c60380348100090040140706460300001a484e00280c580b11408445c0d09140c0000d4111960000383d09080130320006061299444140c000b0000030a0301d40b80001c41803c200d94114100c400712a400603141e00010305580b0340c555080282008240018402020302004131003c480f034100e01c086c5864001441280b410340007481502c1545400c06000341c0d06e602900038500030b1040c00095000310b214240c003042507808200c2501440d00300c4820f104030f150f20810085000400d64000c00000d400380010822490142c00c1a10840301d540c0036542c8840d0820688800d41d20100d40c141ca274031200000401c00c00010102d581e110fa9040d101414900600860000050002800442c8151541e140080715079851504800140201310102c0e00368666404a0054965a074070941010588a01001820f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 199697787 1250 199696537 199696547
    0xf0d020606010503070f1403010b12130803010b07030e04110d0e060f0a0b0103020403050d030c080a140109020702030c0a0602010c09080102040819050327090c090108043503090d 78
    0x140e207058483e5030071541c5800f000c0b1001d91000c4500c1c800c00a0740c3e00f6004032400c0300170080d0701a103440d4511581e00c202940300c808101d8400f40c40c1c51400710380200d8103004640d00d001943c0c1580e074030210141e0364428a00701203400088001440d0351040c607000300450300d17410040041c111143c980034140301c07082c01d80ac0c0c6251a9039040b50003141040040300060280030082c0d10120605005040050902d5104c2d1240380c40c0440350f0701a00042903484100440e443d80040c410390380319410724802d0044400140d121020305506101c1d400d6155000701c4c5160466406101024041c03602070050506c20341d885500a001e04030324002c41e004280546804103040c007060007141c0030fa60305403008241c400d0790404883c40d044e0b4140e500b0703103082c001400b50420781c2080e40c0718154290196642e1842c520045001c0101c1c0341405000d000d201c0d6010402d8030318a0342c00500096200d5000300b00314920b11950300d000f1082c010f05c6064401c2d00500c0088965120204c240607500030281e0b07800322040b01c00d00c00401d50b0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 199699037 1250 199697787 199697791
    0x4061107051f0e1c11070f0506030c071a060411070507031e0206130519050d0f021207181401030201080103080d02040e070e040b3a020d03020f0d0206 66
    0x40764018403400c12480c5034040005048001c4900d00140f11020602c916003031081c0355038000c03568500c4561150005500c0007040410141c0b010190400610340154140c400c0c48074400c250040700c0200002c4da003003109505a9501c140c002101e98400c551f080000c0e0700e10241111502d1045281002d03204075845a00196040d09074004001d1280a040d900d8000341071211040d02c2000c2070800300c0130340c0180c4402d0040c28003280c08031029030850b81007200700404000070030001c2214141c1c4440803c045e6a5401e800d620042e00300b81162044103442c00490502d10f40c140200c803941c4124807000504103821110105600340d030355001c002c610816203195000407020300c0b0290000364030b200180080303090b15006012002d041c01005181c155100c2c0c004228107421106140440e121520b1204142401d001d51840c0c0034040b00c42118441184107500c07004050f40c40e41310b0001207041c031240002624a6501d030340c525001460075801d0007030351a0003956401d1103c28000a8040d42c2c2300810301600000d40c040c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 199700287 1250 199699037 199699043
    0xc031927140615060904180803010602010c0203032403010e01150306110910120902130902010206060d0309060516020307030b010620060c0c0a0204060b2a030406030e070312030504061107 82
    0x24503c00d456400700112508000e90b015846903503044181d20a101d2001c1c1d084419201d0f1404646941c5030010207802c5803080f513503610a54004100704a00401640d020b03110829145018901068165010a00411107071041500e198038002c00c600c0b04000c00942407044030f1051005100140c036140145000d8083d4500580e003012066095103140c5010782542101e0064951000401c0ca800d90000b41340e101d24911188006592030701280c041d0359050154a5100310180c5640c41081800e582c020300840035031007000100000480d55031580c0403212165250142c00034101e40304143c40303091220036000b007803203248003181e0b10002c1005182c8642c0d10038005103d00501500b0341e0384d110840142e02d0ba1041c42d003a03a00d0701070f6812800042c0c1c0c40d441002c01400002450759151202c245100c02040f4500b0b0180004032018542c0d000400000801c81d0203440c0e9500d008649030810200d4185044460341008100d40c460340368082d207071540740c0c1c0420321513405400709100e105152072040300c1921a445000d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 199701537 1250 199700287 199700311
    0x1b0e030d032f030402040501050607030c200d050d180308090105070c050909071e380d0213050103050f24060f1c050c0319271406 57
    0xc05900a5001d482d254000400c1e070055034111104600c0c40c4450360415081210001c014842907003020310829000d810b0946000f0302d4000a41c070064150554179800070114500322100005012255460714401035004c0c00810018071a0700d8281e0719411003400a00000c0e61b4010074003800d240c00185036003201d0700720030800e140c03096060045803542c1c840201034443d0114800c001a254490420b000d100d084000702601b045410140d026513644aa0340c0d1100c04036200350400c0c07280e49294400a07043c4044840302070315400e11001d101e00400c4170040404c0b5500c1c0d0104c0c0c1c034103003182c517500144071880340e6601c00c4482d180c40f000150106c2e0005c0e581301c404a440040001d03400542d400704101a44001e0744c51f51130420107240001d807507621032000080c0003140410300300e8070900320415402110040e00c1d8148442c2c5810500c811660100038008040d00402581d981031100c500c3c0c2c4440e220303440c01400c0300001e00d100b03a1019942d00ca182401c60340c0105640c0d419a404801040c914003034524030602d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 199702787 1250 199701537 199701553
    0x22090b04120f05120a09080c0303090706091a0c1203070906021027050a0203061306060909020d030f031404081b0105061518030102030a090215040806130609050f011b0e03 75
    0x2031180f00d07101c020566140c0d035135111b0958000ca040b0030094100400680300455592821410060900307445a01032030134480d50300800e1010b035108040d100120000074480c0f80e01e89154800c0513140ca0020035402100d04070002c10b01401640c001451000e8891940845400c040d00704a00000c0302d00c1107240010700d180140641c03041d50359586044140e58051411101d440c6942e030000b07410a402541c0c0c1c184210800c910050270004580146402001a0002044501d605030041120f540e0b00078001020072080c512940b026501a900c9036540c0c241c4440c50250070b1030145070405240e40282040006e1002c80b444018012405000700380c85800050910340301510710000b24202c580000e601000f1a40c411904002e0740d880034405503102e0300300c40c0c101040c100e6440c01480342460840f4203080343c01d0020402400043d000184d0700c5c2d04004840b02654a00c0c51034102040106103ca00003001c80c0900d4240590100054001c5014210240c06040009003044015558140c5005546806400c045c3c5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 199704037 1250 199702787 199702807
    0x9080303090d11031201090b03011a24041809021305060a03030f021e060a0e06100b0318010c020c04060504060509010b0703020c030f0109120804030e22090b04120f05 73
    0x3466150740b0f540e080300e0070a020000d400c0a051400d0304081a041d9442c600703030510f1700d4240146035500c110003414801030100c410110300704902403810344d80900311030380806030000d0022049400400d0b00160303803010602000310a0300034200b4004243e204401c01d03443c0707100016943c400c0c2c2d4002c503401400346c800f440c607698050316001c062000030004d40c0140340f140b00000d6460400c9e901c0440600000e8070807860010040001c440e004003429003d80e0100f000c000703528045088602c161030038a0143ea44a5980a01c1800c0540150003500030b40e50800d2902541c05400144114400400300d905100e49911402440101c89080c03140740d5001c00707602c004010810f489001400518060b105685405640d00d003ca843e1001030305001c6090381d542c5111805020005102040c2d00a01d45031401050030f0039100144a044200d044920840004910f6582515070b040c06603c142d8242e0014080d880c40e60500443c1244126003d5510b02441844000c13158410234940449000d00d13203d10b400c180b0081 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 199705287 1250 199704037 199704047
    0x301120f0213020a09080f060919060902060c030d11090102100509032104060c030b010816031410080601050301061508070c080f0a0e0a03150207020103060b13030309080303090d 78
    0x8102660450412015103010b0400c5000414901080b030b118114014a40b004803850076003419001e4049800080c00e220a0a1000c140c1e6403240001a0750051034100c1c2d410054010410540001d502c144000f0341420004008400b4202c10038541408110b4039442c11003040b8144510900103006800050307040100141e1580a20b8000595a04a03410030081c008580480342050070200144001d240030031040000a01401c1080260340c030341400740801c2000013a010000c0980403444004503040700e00c0c0750724465844aa52700701c518828801d1800c1104094845002602508116000d0113001181c2814140102c2d01118908402c481e080911350400700d4041d40054071a400300031403400000c0c042201c0314058900e50b40d5482c035203a03031a40c040e80b02412000c2090415401900b02c40410800308201205040c220142480050382e1030714240300480042440307810070802140c02250008070f4021503c50341d4103503440b0307440c3c103121180c54001540c1c0d1b0740401c45034035485510030f10448041a10032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 199706537 1250 199705287 199705313
    0x14010c08090a09091506061d0310050a020901031a090406150b04031a0702160506030c0c0f010603020a1d0112020d0b181e06010b090a080a03050304110105030112 71
    0x10300386903007026212400603106180c0b960007449184c2e240c08801040c4001d0040002d01d080800780100803071403800300d01425030b60100c03820400d4410848009904c50302c0c04d011a16035a0b038038510406c403604c2c000301c03c1c43c029000561ba517030009251000c2041c010384e075826024000c0c1c0004001714103503a2140d6a00010788500520f81890f034246140001c0c0600d01e1001404c041d62003a000c502041c6055604030031010001081c1c002190300507545400d1120030548032106a0b6001c0c0e5107240d8076524502c4010940c4107580107c03c0c3c0703200ba460095011030040d4024800c0d01d00c04c030350302e8142950712094485200030b8005809504d0078200010001c849041204004141c0701030000b0503c0e4030541c440092810303040300d140c1c40c00350181a10000b1003c01b401902440302e032480485d010816269410b41d51140140900e000c17030315000400c000d866545807440401072003800304a401002c0c45103401040ca030410381c0d0464450b8402c8003900c64070340c0501c0640e03051710045c0818000448107611802440004 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 199707787 1250 199706537 199706543
    0x211a0c07020604060201090201080f070c110103060f06090806010605280e0904030e2b060906060e0405030a0206010f150f03140c040e061e0d030504051f02010507020714010c 76
    0x10400080140c07650005800101305503000000c1d0303a0740a000142001300018400c42c0912145c008120946410813012100c4c00e40009002599044042c0160000c1c0307082e40003200c0c9034214080000701558880600f1041d94048800d884860b41d850300180c0b0a8001c964903690110382c03041410082800c400c45440512601c0d1912529003001d42010030890401a28168009500ca1010003d1401d065a140350781c001c1005a4410b00c20484801d0b007040d0902c508001c0103980c4506803c07003801082d800942c00740c40359000720f01e118106460502d0381c03944442d0485001d8041c000c000940f2404200007001242c041c503130010401500580200c800f41010015201495a503a00c2e80c90983d240000991107044da030340706941e64600700740303095482c10230040c42c0c030b403103031684801c01e1480d021902006184c500e81540e40c100c6410051070195072a01454000c1c540081c4640b58040c50040803d0385910684802d030001c00040d22505000ca031a901180a050250300e03e40282d8909548034010525540780 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 199709037 1250 199707787 199707811
    0xf031207111507051803060f01270204080a0c140108010905092109120105040206090d051015061706100509030304031a040c0b0c19080f0d06211a 64
    0xc148410311010b0544180300080c0e8003045002501e08403095109420800310f00501c01494000240903400b0f40c14090082c00c245441d80c0c00b0f0310503038104100f20320f280c1841005e541315621001c41e03555071500b4241c00d40e0300040c111070004200741444d2814000300e1069640a5807a8203001811004d001d001d444100c2031f1040501e40001c02d084d01410b000065181489503503540c00080410070100c0c082070042c5050b901d80014071005944460881e2840041500d089001c68441d0600c24109038040041c014441c0c1010001001c2014405c0d0074000c0d224640c5841402c0b6040c04e50503125644200c9015800404009048001d81d000e82c0c003510b14a400101102d181503181d5032000640406c02110551b12002031090008102002074580c0107402d1040a403030810890030401650340400c200e0220421105000710030610455404552000da0417030b8245549010802d80d20307004003024442e40706c0c80014405c501c0341243c001d100c1c021390503030031203000007088030b4031004034440010143ca1540d65032 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 199710287 1250 199709037 199709053
    0x90b130504090c08070f080a0f0201090e07030b1305090604020f0a0b120108010e01020717031306090f0201020705010e18061206040302030d0f061a090a090e0d020f03120711 76
    0x99901e01a101e44103200d0520f41801500e0031591030700d41401604036440721400c1031014005e400b000a0146d442603004822040750703010500050300c1c101c05940098000300d48480402000342e4042e0000c08400000355aa05009000c0d06019011940281c4141c001904020045405803a01004c4858103141c0140b00300340540e03590100710782c00d40c40b04801d1040a05003c2c0100202c100030f2259001c2c16100740000d501e00040c9a94106011002e80d2020700d00e0100800440e0a604100c004141d485a00084c2000076184505110b03c8000d00ca440885c01889040408a02e40d44101621118403e000d40f03210101500008008404080103000c2500500d5459101100040810101c0d02890194026656840402c0340311800c0d00e0412226003800d41c01c24000700180742900052000c42929001c02c0d940b600e000c18005074002c2d00700e5000c2030105042c44008805c020011070102092826034003101c00341d983c20801700380c90340203819020b00c1e110a00000151090301030803901860b0300401c42600c07156 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 199711537 1250 199710287 199710289
    0x61b01060f152609070506030a09050609071a030c121816050901090f11030403030603031b0203030406200a030f0905041104050d0201050c0a03091a07050d050901030905060a0b18010303090b1305 85
    0x30750804c8541119aa42b00c100010511000784000c5403c920490007600f10301c0c1c200b05041603683c813040d4005c010440000001152810840c0a5031403c41003401010121b0a22a00310030f01032a91209140c1c0038043c0320000f0100a5051001d40c00300d1b0b10242c01003070961320706000c1c20000c0842060300050242c440c0700c8038401c0740e0380344001c1d40f29911070b441c0040c1d00c03425130400505011562040381d02440c4054070300c1c00542d400100f5134003140d1a0340790041d0981040c04100e400803500b62806420362041200da0070806801c1591000440602c0d5a00821655900200030540d4012145852201020081030219062055014002c0e5006040045c508040c44d2075061030001d4641042d00001e030b000c07200f4080300e005071015140040107081034509042d01c940f2a2030700c23480e442c050721003480307400103800407543d000741c1040b8440c44c0c000c4141c07412403400441c00c0c0080d1070104000e61007030790000b26080c28061010550740c141c036050b80c2d59104c00d40c10903107100300961094100d00d171294010307040001e00b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 199712787 1250 199711537 199711549
    0x2070501090605010e0906070806091b0a03090b0a090215090a030812060a150219052a040c111203060109030c080a0605100501020c061b01060f1526090705 68
    0x40d5620407a4002151341c501011a28140c0018045180d150025018000102e03809141035400c43c108880020040d1072314901d0000c4185103044c003150f00180410110f6126406510a100f0240548a00d14059443e0041d00003140c1541710300a5000380f0000000c18080c40200107000502401341206013090740302d482c0d140454000c1c21a51940781450810400f4030309201c0b8900713000304081c4200d000411201400030352078400fa446c00b4040d0850701c3c09080b0501c6801c004070103414841e0002400d4030315081c086c0c95483c06c00c3c5080380d030042d0b0800b96030302801c922640c8011260b403074113400341c1070f0241c0180e05c140003640080c4c151810066010301c0800441d40750040d520082055600400c0f069085245c02000c0d180300426545903041d10510410182e41c0200341000c0c0f5410886a4035a89e0401984d542c48041c084825041c1542c41d10380045030b03012004080006035658a000441c2c10180800c0465105d2001c44501000180908010702d403114a0303068160442e1003041035413200f54440b404191 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 199714037 1250 199712787 199712801
    0x31f0e0a050d03060905070813060603020613090617030a050a0c0204150603050a0e0d211a03060115052a01111b0c06070b060a0e0103151a01020a110402070501 70
    0xe0310b038000e4000c200d41c0c40c0e0584140c3c070081088440c10b000c40d103000311001e050044010140801e11010240c01c00c00c1109640c0807c000d1980200700b603071900b441820000c00c4129a00400308400d281201c0801c003d010f03008031078001e186d82d20007903141200c07010f000c03602d94000800e08424012a5081c400050340c607801901c82c050008658140740c149030100003025130724042d01c901c0385c1916201c030f00d800c10400450707030f4031000b2010f05200d1b40e840100d001c10f00340300c03246280b182e08075452700020b46802c0b40721205040d081e080c124102c034110f1740c03161036001d101021080b0b85408075404003c59408660006030350f0541d07804403d5000750107c09000a5800d540d940200b52481c43d2000a801e408455410100e8006d00a0200200a54440840403074014819000c000e4409900400003410581e5a56140780c0601a0306500010f1545e592a101d110100409041c400710350a044440005104545601c0c171103000590040040c89035580380d6a030304032040703400390380c00c00d400f002050045030090003181 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 199715287 1250 199714037 199714043
    0x5091c051513170c1015031a040302060714040302040513050a030f030c0311070f080906180102100504020d0f0c080d091403062a041802071a0105031f0e0a 68
    0x907500191442c06543c040c0c0e2005180801c05401c0c403103403041c1100011002d8180c990080d002550b00d6075020300d14845506940024410182d981500191080e00754030b543c06603110b40c08860154881c3e16080d60744c0d4001c0d10071a0740595042c40f08001500d825040039400c0206040003510710700d90390b1580d504046008070260046214102076010840e494419400e4030415031508010541d288800c02e9001d120761000681900d0880901c4400d00103c00105c64142a004100e140e540301001c6078400d54990a050642c058001c4007a0b04000500c0e60188078421a8002d000300c2c119a81941c4241d001841d01006503403140c03400e134010401c0b200401c901c3d1a078105030b0315502e41d040d00c0c002c40551561103401c0c9081c0030740c108a05114a402c103c203203400c03846040020901c4007030080d05540c419402594070541c1c1048128000501124450313000b0f1041c60700400c4201344021403580c8965910400388550b540543c4141550302c204e100d80d000350024a004148045100007a40ca580da10f0324004600603 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 199716537 1250 199715287 199715311
    0x1815060307080f07091505030a060815010f090b0904031215090b031002041d04030e0a030c1409040203030a1107030203011401051206190b010201020c070b130605091c0515 75
    0x48010001042e141d01c3e4007043c07614140c2110340c207204031501b031105250000c100380500170010820f0309815410903000f030107211003140c0d406507080c030001881c240203101c1d981200d00024400b28007641140030700380030350901420071304071522150b5044402c4403140c1034007560b0b59500c0010400c0d40319201848001003071a0707500482c40c0c0170240201424000280e4080b03007854810442000b04041c40c40381c1c1c044049031070550400c10340c0e40d802d05842500107454102e0740000400d101000300305102c00d40001f915510803404c0c5004440300e05001c200038081e031340030f03600d58401d001000d802481080031031a0300d00c6079400d80b41107640d04e0b4082801d69403810300f042042c03100341005000c6420001c3d00009000d07a081c0080040782001103080c440700011802044601c2c2c0c039040d94005990003501259440b0600008135038840381d80e02601307003440d00040581d600aa01d0030318000703a0148100c007501c8030701c1ca00800c0800c204003414244a240c103142c581c00c0302c0e0390103100680440d0a80c0042040e2190307410110b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 199717787 1250 199716537 199716541
    0x30b0a0e06030114090c0108070c0501020c030301090b2e0903061404120c17030c0c0d030623090109020309071809050705011d04110d1107020901050a0302181506030708 74
    0x301420354440d60813043c11040f00c0c0c000c00c42090400500f074100c50b1003e08246210707468500c1c088420311801c0c40040c0c010b43c0002102001e803400000114102d800300305007000b90014210800c50005900681484502c00041c4208502c1c2032607200343c48990324604202e561243d480e901c5c0c100365140f040350100004454420801408460010120780100d00d1921988400580d9681c040c0b43d0356941440c0c0d031130880840090720307000d201411071704120460411100500996200200502000c1c020824001071858011030300c1c0c0d82c24a481e41030264000c0c110703400c42c0e082c10316100c02500010f05003c128800c0170000100f15801c8601070a2405440344040346000701420200e00e00b00e455408141013000308100d01082c9105030301070030742203030089402103140340300d0012003c0f0500541e24034600301d6250209c0034410602c2c038002807001c544256903489040e17130737a0401c00803c07404601c406500588a600c0d80d0100d4000345d051581e0055280341100d04c2100f40700049010398000f03d601102092200301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 199719037 1250 199717787 199717789
    0x11010e06040c0e04150b04020f03090a2102032203020d030807090b040e070f0e0415030201020f0f120a1707030f0b03010b030d1805131508060403020703020f01030b0a0e06 75
    0x11950000d4605a1124a10341c00e140e0784145d8940d000e0142019016951454060150740356012208040d2014002e103840c0c0c1010744003181c0300c001342c4400329082c1842c0140250040070b4070014201204154000c0d50030841d241c203041181d01005650703030103840d0b01c480e8003000580d10715094000d021300035903451202d0b1a1040d00504842140c0e007200c60b68101c140000c00c202c2400228459112034145070403d5086003408040d10f9425105079225401400c20030031014220702c012901c0c04030390003642290016207a00e0081a1603614400f84e1991581106250084492421000304940d80d00c40c90302008070541030100e1141404203032901e0000035215842c615540d00d0a0050025071070007100200070015284001960380c14801c050341c0180145605001c0190600c078045000510b03000e4076161b101020245980c1c010300380708041c440045018440800c18600005505201d81d03070680007440030a0942d001c1004402e00303445224100340c0c0303d079001d1082d07440d4283c0a030700500b4004112007090500d10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 199720287 1250 199719037 199719053
    0x1091407020a05030702010311360a080601050613090e0601090608011815090b15120a03020a0b0c04081c0e0105070201121112070504031217150111010e0604 69
    0x1034404011503001032025000304030b01100b21000d8a6090a00152a04010f0900c00240c003904c0b14004814240410141076810504400059050100c000e000758581c070008021075612a8083c14000e640329400620680c00c115000b01440440b00d1a0b2501c400e0751180358400b591420395028200b50440340c01013000b010280901800382c48080700038411610345114403900000c240e10b02030043c1d21101c51415000905900240036140c0000381c001481c80c0042503424400c08280707580d03000d0000c200400e6010f40d008a0f02c40e01090380343e0301070000c001e00c03902c0340a5102c00c00f4000144088040000185112040240e40d00c06203200038048008164002c018200c540130350f1509050160030422000103030ba101e2902c0040007010f10001071411550f61198202d8090001c40e08030515206091048040e040b1014200310392041c0c4203501038420b2003204455000c034640354441c0a0300741c2d0020512205515465030030101062400c220840e2562800c01d0940b43c1900c00100c0702d41182e414803062003102 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 199721537 1250 199720287 199720291
    0x20606040603081207030b1002060609060607020904030f021005150102120301060c1401060b07031706100f0c02220c03050c0403030f14070c0b090301180803011502030c0303010914 79
    0xc0340c04001c0503140da141c26989118051500f01d8084260002401c950300960152409034000340c0354407035042c01c0b000302a6459105803101c034819100d840014009103003580840300d540d9406442ca604035210350b40d09a0300404a8030581003540140001e051070b0300380d68803590f407280c1084480d0320302000062001a003001135541c1d201d2000300003040140440c40d0050f44000d079903540810305104070402040d24600400301c031b820000314401c00003208801d040c0c1c0124086900c940c40401000c007500e4260030000e8150f403a8802c80003080402454801641c003071641014401e0000d8008056100c0c2c0c100e400e400120b0200c40c0c81c60584d6240420200c0c80e50611031070f9804410410040d103002c4c11a02c024001146502c031755020064042041d40e1481d03803030003c3d04c032107030b500003032420ac100d488003c0c0c0d450355002880064000d610744411240c50070386103050b24442907001240c8600d50b900b01125220105e1078555620250f200800c10202401d501b00020b5009296659001078406120403103d28210b0b40 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 199722787 1250 199721537 199721539
    0x13060e030f120c010e0f0309010f0512041e0b07050a09120b04060c050d0f0614030102310b0c0c0301060614030106050a090305030d050604181110050f0415020606 71
    0x400c0018640c540009540030a802d0850103580c442581001c0a409010654000450307030240368010a0320720b80010103400204801d07254802140c840281c2104c8030300480000c1e2041c81c16400104020511340d0113001070140c0c0141c0c061000d081aa00c0f410410481a901c2000180d400503151525551103040c41d070260202141d900749081e0706442e41100c000000d01301400c0140e466081080641c090300c02c83d142000044400d02842c840301442d00018603143c441c5025100c1c01040a0400d0702e4180300303c0e015043c0060a00704111607280d1a401181d03490004a50845009a030124044044001820103540440d008104158041c0145070a4070025800700c1c0901501103015580c2151360415030b41500e41c9131805503103036562150200c41082e1030f40d02c050b0190200050101170288184c020741c5c8200780546013402508002d1602400010700000003514102c41d881e150380080c640001001c48081c000e00d03000f8108035800c000003030b2030f074082d5006160a5840801c1609a03075014050543d1040c4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 199724037 1250 199722787 199722793
    0x101d0301110702060a110f0309241e0d090b0a110f030c13030803010e0f010b0405011d0d230c190509190e01020c1c0e060d0204030813060e03 62
    0x1c85114040a41d0150000082c85180040790000710103101e00a4050103d0035401200c0d020b00c01090071540380e61202c4860383c0144104500c11303011584106c00303500e00050300248030f071800852100f111400240d201000f64080030400c140220714500b8007405020034000c0784501ca80d41480940c060464144001160320071005101c01c4000114600503240d0080b103902c0015500c44102c02d9114450840f5080240b064101200202d050103125070b85031300c101351007031a186070f60340c8030040600700b4007a501c142c0340000d010002c880340484800350a0890280c002e4050360041140e55910088949540b400b0410141040704210400c841002588400d29050f202c610310701c03484551080b10351031240107081c010303207000c408550705504048031840000c13042c8000708071188613401070502035401a0307401c189520070019021074404010005910040540d142c81080ea00c1010610010341c01803554500e04c01c0c2d00b80300000129003010014501e4a948020032482c860808030701811949800c02c446000c1e41c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 199725287 1250 199724037 199724051
    0x5090403080403050f040506070b22051e01061208070b0709030b01052b03020102040617010b0a0810080a06020a030f020705070608090c030708011b11061311101d0301 73
    0x80d00724400540080d05494095940c1c580e05600721114402c590000f41c12800001d03001d024010b07440c0146011740c66918135100203005400f444840c03454464005003480c2c102030b022a0300c48612018842c0440d960300c0020800310f5075034030903521110051106841045000a2001c204018205140d41c001041d05050031118255125075400e10014080c0c0360045428184002420303003604804c115011000c5040801911b4524000707010350440d1081d0400719140c0341c1424103442002c25403506036603c5101c4c0c50300340444100203ca003000702030152101c00d0044140400c18100a2021141d0140901d1026a403110075581c01001c80d540181e0446445206002c0540003c0c0c0204026040350900d2901c07000f652070f40c8001303034100403070440c02d650b151141c0000050030352819081000d43c121120f020140001c804082036524100c925441c03005900108c0000c1c031441070000203d00e00c9070180404a201c0404040810300c804150b05045000c0340000724410b0721100017003418088150240d000388184 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 199726537 1250 199725287 199725293
    0x8070915080c06071e030c0b0604060302130203060d020a08070321050d09030201060b0c0f070b070309060318021201020c012d0b18010b0406032315030109050d021006050904 76
    0x14110b0910040c0c880c00d800110030f070521860791183c420791101401980d58072030b2240381c09407195140b508200c403080d8400d00000d46510307180c40b9a004907030300a000f0540e10724160081d00002e5000034061940010b00c4c3e48180e0241c2c0f01c8404c000003a00c1c5080040100714110700b01402020282e80941d04200640002c00781c0e1190300c0710a89040c0b141591001c039904409280aa01509051300700e9040b8a10118003984280000950b0030310b850f5405e02580c0400c3c0c0c07689000c18981c490841c0140110305440003c01c440c920950000549c4603170718200f084520307007503800150b00d03501d003002e1000384c1c0e900071601191140d828400c507c0f00c10304100844030715859440a101c2d0307200d01d06500f81c21040d03850103507250b581c540000f00f00c103010796420440e6070b44d030f10350801084031b402c50b02442d00082d00e048541d00038440e8460048903080c0e110360880b080d503622020f040d034a25021011441e015503c2e01050400142d0030441d0a42080c1150050301160202d140c80100310303403007a0b0296208901e003030180008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 199727787 1250 199726537 199726543
    0x6120f05060d0318090e010f0e0d0509060a1b0b0412020f060c0f04090f0504120809030702100c050f0601050324060609180403050d0b040509070b0a030b03070807091508 74
    0x90398141080040769100a10b2451240402e1707000010703da040402c80c850440f8194040c0d1011842048200170316030300d4101c7c01e60f43d15103030070503d40402e02c00c0103c0ca4191800102500403000585050303410103012a421001c212008003044a12000c0c42050000300f0204000c2640025401d100074984241003880641d03440d003024100c0d0345900740018100b501218002c04580103403104050600c005507800c1000030003880c040b1010764021541001c031009040c820350055015030ba44000942c02c242460f020810250060445ca01c240f1104000c030400050090100d04034480d0b068000e1f110035031403c400d150410303501011500c1d04111030420f281512044079500e98201c1415180c20b41c852201c1c0010501e440e001041d0800219010420041003503403183c020701941c60025028464050540c040c4001d841c000d4030443c865403c80030b000d204c112220800342103205694a00852a4166200030034280403068203d49000c0c3c01c000020300000501d406605030038048000c90003201403901306440c1e2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 199729037 1250 199727787 199727809
    0x6050702131b08060a0b1b15040807060506010e040f050115111c05040b18040b0a1809111002010e0123041b090606030b0f0114040b2206120f0506 64
    0x2c0c8500040413610589422410348080c10303004820b669100c00f100321091100100c01c10880d098400c084804d169001030301402c0d4015944145690b040401d03c0ea546009000300600d480d04201c5800c481c4151951140500b50380500402000a015410841000c01c08002e200e170150034003d000c800c0341e05c1c4c401300050015600d4154441c4110718203160358116a2407080e58454080150f021402401340400301c5001b4a8117002150104820740680301400305041052145c0c45203041d9110f00f01da00310409400031200b90340304c2d0b07030300d020600202800220202210b0b45403e0050f903481d00e008103060024071030b80c0c20b001810741c030403803881e00b00d10301207032110030000d1004052400d01490052100d40c0d8106e0b540c042d00c1e030b84000b0f01c106600e03104020010300c40006035a20400c00b40030050020350003204401c11a031200c1907001c0c503250502041e40348581c084d0780314116a05d203c5e2414219081c00c0c9070394002070031259451110881e13403000e1b810151440000c031049018605001d00c030499440c2c1940725 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 199730287 1250 199729037 199729091
    0x2010507090609120f060e0303180a23010f1b0206011406030606070311060a140a060e0a020906041802030f09010209130b0105090306090319050f040303110f01060605070213 76
    0x1403a4400c54030340b070a440d14002800404403410300d0b112207e102d601102840c03247c1003c1150045a45241100c280d272080c02c1c0001408140c207005000300200707d01d4a9840000000c01c0c004a40c0c5c04140c142d0600300c03604442108803622200100c01c482903414032009006040ad400d150001482d03280004540384000341c405c03403180300c0001d121000c040c000c0c00001280c900761030a440340c0d442c1103c00300340070340340c0114400500e1050100180d2a00c039944a040b0541e20a030040c50f03190382d201c0328084001d51142e100558032071014000054050800038035184804503c40c005a12400c0c02c0070468000400600f07010300e02d1340180401041511003540400101000607408900201401d0044c1c4103440380081158042c01900c04000540307a000004141504081d1903c181140700c030f00341203540703009035588400f031510200000c00100b441074075108000c03242a415151482030010704a03084601581c007000214501284000a52800080247d6045010781d400c1c40200408581c40030044da60309010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 199731537 1250 199730287 199730309
    0x3060311010302070318030b0f130507050906031516020c030304060f210e0d020d09050108040b041a2a030114040f0216050f0d020c090f090c041b02010507090609 71
    0x40b0b02454440d510780040391900496460f00a500e23400c0c280d655601c01c0302c220540050310b10219404003244d216040640b5007010240800c0d1381840204a200c940207090141e040c0720700140c40150f505000d0fa401d00030100400e012000d4041040003a003000003070007003640700707400a100c02c011194001210001e0b0800d5841c0c8540307158050324a185c1409480035030b8154161030610a0a440d00b00000d000f480e083c815000c071161001c08500c00c65059445024a80c001014480442c0c001143c0c000800c0c0c001d0710800d55608450410a040301c160101110000129245170504100d15640c2464100c0d002e18140c0d5040c0c91581044040490140c187c10410300855403500184803100250341540c540a20890800c81c0031926400c0c0030f0f80e03420140d05180074900805034400c0c01c0da4000140b413840c0d4540501050300c541e03191f0400303034001c50b07008120300203a00410400c1e1100d561203218070b120064855030441b130810080c80c4001c0c00c5910040081e000d2111190050140d01e41242601c41143c41408603 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 199732787 1250 199731537 199731547
    0x2010207061d033114090105041806050405010e06160e0405160c020f09010f030308010f030201140307020106051008040320061302060c070306021b010c0c02010f0c120207080c0103060311010302 85
    0x4c2c00072810882c00528a080c4625440407441411a0300e600745180000c54000e03019989440401044a50009030340595059060740da9001490b10b030000350303105000c2d80001680c00750041c0814101030f42200d12886460880034002d4809400c45201014003e0640d4200a586080c00529005a02d03c90b000003d01040052080031903560f011031000c6c80e1000380100c40c403960b4420000b208494903003c00c0f070104170502c1c00483c0404001c5c024000b03d940507510941021420404401c0301c2c0d00250030b0000315500c402012999483d15030503108020066642c0d0b52052809050050031032050b8800e2540d4410583c55103c1686000501c2541041e0300f940301c100b04202e02e200090407841400d16030040b1f4040c050001083c4070042e40500308072882401c10000070803808041c1422150038240500c04a80c440040344059417003a0210502c61520307003001c0104174919183d40d18a02001071040006038807605040c40480000c4c44421042030081c24103200040c15035407003440001e01d208089040580c0414 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 199734037 1250 199732787 199732837
    0x90b01051e0307030501020306040c1407021903050105040b271e030714030301050a06260c0d29030a020109030807230318010801050112092102010207061d03 69
    0x20345000501c4014116aa03060707407450414040d4000f01d078a2032289181085041d03a450056040c0c8a0b819000029540380c50381a50821640200e000000e8152002001c4080001502440b40301d0041c1d0003000c0050091802010340d413414226a1041b9104032001a10105100000141d80c84402000c034002036a20103100c0d2090302e10b000f0900080c00110340701c09131408101c0c0c00f00046050b5842034401001054039810242c40c084140c140ca000001203180c498021802c11800080cac04c0700d5580b107402c2c541440b401607403050780e07514284082440850031200b2180d89895440c0b01c5071010940c0a081034200e0398001a016156620001c8c01201d4005640d60410181c0428070f0b036503140c982001d034001d0103140c0c440ca07900d030818402041e00c0440712800d0f520300d45c003d000c440d0407108160740300160480d102c0303000005404004411503208401c3ca101700e41408010300c40f069400f035242c0c001a01c4007002c1c2010380583d00803d0506a0044503600c207686111404000c481840100e0801c600100c11600 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 199735287 1250 199734037 199734079
    0xd150b0306091504061e051f0c030c0b070e130509030d0f060e040309090e16031b090c0e0a0f1d0714030a060801050a05060a170a020603100e010801090b0105 69
    0x61160f03125107004808640000018642e18503801c5a402c0c800d01a51904c0500034050a40c6030740c2c8c24414006200d030111135100c1c4004104c0c41b440f83c0303400e1444040c00d98407007501820594a00010503141c0d40e03502c2c0241080c0c200c1c44084540341c10180054100b03c0c2c1c2094a03441802011ba800a803541c03000714402005070040340080020a00c5a110b520340b81c28020300ba440e4500803049000c1c2000b01243c00000700060160016076800721100b0810325590b240304004442002c1068015640400022203036041d1148005040b526102d6004000c1f86404028080a1580051182c907130902800d0042c180040da030301c0310741c900b036400d240226200d800b400e56101d43c03030360085d08044200100300318902e050723604850b044030a84c40007803056403290004079050781c408940342d80c0c000942d006c0c20081403400d02d240302c02c0c07001e9034400d4880f600d040d0307004074070703541c1c000c0f1854501b030300d4892020022250740102041c01421132038000c00100c55036544003007007140d042c032a00e84580c4c2c808a04030044001e413 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 199736537 1250 199735287 199735321
    0x250c0b2710020307020f0604050c3c010e01021504081303080c0d0e181f0509010b04080705060703120b060d020c100b010203040515031314030d150b030609 68
    0xa002118451808280c192000e50b000701c070001c00502500c2c21b01c44040e81c00281581c05294083c002d003048036401810700007074084500b52180d0326100300303400113041c0c5a1a40f102c2c8080c4016807484c1810640313000094241c40d4420000c9046510440a141c4084905104103030041d03072103e4070a564801c0c403210540d64091940000d806d91500150545101d9070024209444e42110780b101088031484204002c0300c006d8804100340210031503000100d191f04440101c0b03607410b41610500340126280c4002c6280ac08091308203d00d04100081c0c2130008032810061200104800c5030340c1450030015036070040601c542600c00c0006c854444022200d560764110541e200e40011800454076611416078842e40d441c080b0043c190a60301d4180b1001c0c0651012003210b050311009840c0001d9011418119500342e0f10043c14084030701c442c040200700069172082c0c64410046800010340d12040003448000844071142e0b540441d1b1500000208241500c100c02c1d0313640440101c540740559911900007100340d0440c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 199737787 1250 199736537 199736611
    0xc05060d0b030d02061f0305150723070c09020903120a030603121805060414011b050a050a110f130911060f041802030c090d1109250c0b 60
    0x400f842032440d9a400100c1030310030880c4940d00200224141d02e081c41d0104035000c05011500481940c81074240443c081a40118041c90310010680c1000540400a01070118580b03000200041e040203010a046048000e80113141045290a1540b40020303500c42444699000c1300740041240320000e402680198010368014600e20700324030f41108014041500040094a0746460f500080740a041204c140c0381659050b103499107441c3c1c80391005507140031070700b51a504800c40110000000400901c00c2400701d40c424002415204507924081e40e070311016001e9180244110103242d004c40d510150150b002100c0098001040c503914107001d040301c9030144929400c80000501e03100f5080c0d2940c020000c6824030900801400b03c840000800e0b444140c1d4001c01c440c1040c4001c00044c50000551002d9030300ca00d0b21424101c1a41010035000383c4219048020080c10120800b074850410414200285803454080d804d0b219564070a805400c0142c0b004201040c40b0b402900e50b440303000520303c0c2081c1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 199739037 1250 199737787 199737793
    0xe0a09080a03062112050d020d060b0307021011040515090a06121103060a0b090d1a01050a080307050d03020f0d02040906030201021e0a0303020717120103020f0d0c05060d0b03 77
    0x702420042e01400452146100d100c007413805030920a4400ca4224118991004c03007400e40842c641030031107158000c10250709030390358200100000c118031442035030f0003000c6c500e0b1003a84901e000607011303040c00701d81c400c441e400c903050200001111188000312002e8030011204003448424400b4480710a00540d1130307090304000380401c0840c209170040205407184950340000c0c4182c030140031400c1650b0105851164104003580e20030300c03110070b40c00060010410050841400c5d03152075194800701c21980c5024600e204081c400611243c1844140e803000fa0008500951820b0170b00e07500c040d036603410300440b0010594041040b00074880018211030040ba52540c043d900d40d600e03142d8840003030005100490152003506500090b424100c0344c10002c0d0503240010f071002a589480560203076012000c115031a4000e5100c0c40340800e0040e002e4000301c0c151580c100c0066055106121159840282252107050078000c0d40000846140f600000d072181a03d21a031942510703a40c0d0009055912800ba40c540 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 199740287 1250 199739037 199739047
    0x60c0606031e0b01060314041e150f0b0603150d020a080706020f07050f0604060807020c09190506030c130b0303040b0a1d01090311040506120f03040303020f06100e0a0908 75
    0x103155100514005003d80340038201a66a0300054045641d82c0046014880b207020001d800708590f8806c0e01e03d920210001007600c101c407959080d429013820080c0408040d5101d00a0414245030300c0713441c3c0703074000581d0b059186090140d00c428189901040242c0f0503803002c50420115114448200c00411107181150313041178480740d01035140d4080080100b1244285000012a40b409040e0345101c1036000e4200d924190802508480301c04000300514258411501c52441d9904c41c00c1f2000e00c500c4003400020030602103509003409035071026240d58442d51103408154903d540c1d41e0044d0100c0d4401c0d540026441c2c100e0070202c0d08500681e8004002040d0120b05c0c03d12660700100c021480b00341c1c40800480b0401e64200541e250020341c04003038044a0324018205681c20164055078000000900300031150400c00c811074509100010585420341010404004040e01001410b0702c2c3c1d0800000b0740424640240b00b41c040182e603101d40f0500300080d01c049400f02110b60b204030b0419401c080820380d55 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 199741537 1250 199740287 199740323
    0x70212120409020c0c040b010906050a03061206020a020f0a0803151503090109030206010b030f0a0506120d110d080c09040923061510020c091810050402090105030303010e01060c060603 81
    0x139001090510303800d00611a800d03040b0301c2c1c180f240070150a0146c581000103410041c2c00c5611390800c00e00141415601c0001145501d020b0160368119442142e0140c2e0311020000024245034901c0802a030f158401005080000d202c1c0d010769030301220390324002c580e81c404100003400d0700d40251190350403010000207100740c1160641202000034082d80847d140e69a0f04c080c4942c4500c0110369801c442d04c8401e0101d84402025001990000001000c459021000c20805414007440384003a101080c18940038680501d018131001190324005e08208100713191079480d152091154008591250340e0f20b034004410000b10204407041d909800100301400401011015501d030029140e007040301602d06440c41c2da0345000707402552020700344d80c0070300b960040309800d11039501c801409422100c48260600b180c6084108401484142d115a0224032400d260051118034881a00014040d81007040107012104445003410f04580140c03801d880d140c82c0e1030030f050000704000d0700000d00c2e8000c5984410a0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 199742787 1250 199741537 199741541
    0x250e04023a060f0303080a0902120d020607030515010c0b0912041202040f0c02031b071203090e090d0c0f170301060809012414040f15031b0506070212120409 69
    0x1850180201c01c014440e21502c01841c0f003003191000034001032108001500d01c1180e904041002c0c0e20240010640c800c0c100d02203803c04050b04d000d9401680702000f0000000d074140101a00814150003401a480d00c0c000001c180340300525014003070484c424003142e0f01160400c02e106c274403602c00c01d4854466840307945122149040321030071b074841c609201038401c5500ca03500c030f2179154449a800840c5000b0300c0c1c4003020444280307038018040d1406540030001d203034000c03c3d0100c0c010034030951f1000070150400a08003d20f200c0500144030036442107952110203500840c03a4032002d40c021410a24a48880c5804000c12080d42548040305a011000180013a0000c900c00e00902403480207218030b0010f901c2102201540b54072030b480340d5100b18020004c1142c0c070820712071207000c060804201a07601c4890801a112601c40200c212140c036042042484050718500400c111100c1e884c004607840c3c040014101e0044403800ba1141c5078070444407507120810044111549111078030303942c550740d90341d0100b00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 199744037 1250 199742787 199742887
    0x100608030a0e1824060c0a05010510080a140106120b010603180c060509030109060207030903170a1d01051201150306050301020c0601030f03020f06040b250e0402 71
    0x4007195a0740311410407442c100740c3c09829502204044810380e075400c0b2009920f550801c082480b01c14002e0701422003500c4141c020b01a802d101402000e91440c4c6241031401c41c0e5004100d000040103070070f0240103081020a94a00464000305181285011104c1303040c01890780b40d0060500096240d50007080040c0610a40e0403101e05032020000500000d508400601858100404000141d80306100c41800b500150212286c003130f000203800141541c448003240d0202d28190b01140480004004007c544802020134000d110001410117503480005010b0a60000b9918040ca61407110400c550340301e01c051380d11010010f82000e110703581d124424034104c040e502070b1100180c10b001c2c0125007801c05000b211a4903943c0001800d15a107140c66aa040381152a0304408602030f401c3c03000d00030b88041203220700803401a407403c1954200701c0c0300b529080c03044200b01d200141504101c42105030f003214140195110540e40543d503004010300c00e5001c80c1c3c2d03003000803540072a030009841030550141a580 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 199745287 1250 199744037 199744057
    0x50105041109070f0f02030f07060207050d0f050702041127040509070501020a2315060f01090303320d0e0c010903020a09020708090604082b020a03050c10060803 71
    0x411002009414084000c0341112007102040559154040b0617104800003a1040a90310640e810b0440c0304110b207100780c4c0310100694031250081100d0050280078400e60185000c1030908507403070004444050414003852502a00c650364500c4000d1040110a045a826081c808910612040c1025113445a90318005010703000314074100c0026040e0070002000026140c05800518100d980c540c0c0306400500c2440400c8404129110780301d241400410070444900b2042e201c0c2c0c000ea19107482800f04007011003014904000c401001040841d0300040b100042000c0d085030094820b445200009140389100000c1c8e40000e000503641d2440b070340a40c03007910038950807020348040500000044400701c80780d004c069030081081004005000456004080617440745500c00d00303121a0800080300c6400c03079408852550003001c41007041d0a2080b500155408001708030000e18484010002d54907210700314024144200080e040340b0340a400c000c0c940840000c54000c1c0305094581e160340391031742c000c4c000031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 199746537 1250 199745287 199745303
    0x40c030f1103011a0306060405150d1109130c0e0604060309020a09140106050705070b040303030225030e010309030905030105070f020622170d05150a060c110405070215010305010504 80
    0x140075418401d10440e030407a121912401440c120480c03210780d041d4009030603643d1000040100090546032a15001c01c0d103e00e140103d40c4420541d2484010f50f428425092541c1108006045503a40e40c1c0c9030305400841500d400152590001c0300982e6000c8484200c50b90094000c070700021103a83c590400130010b0300c241c89a0f5409903031181e14205451010700c90034a0340071004014840d00c1d01c01c5010744202030246046848096440080182c99802a00141d000940000b008000b07000d02702a0140e5040074816806018031040d10b004100088030056281010b44403603d80f03082c0b40c411104070028140c000c0082007035081050303001e010106015908000f6004040028004002e1005440321203a09003e511141e41e09590700c810000c802c0d44000340c0c4031f1406018101041c2c200d441142e00c0f810b02042813444004003541004480d201c90350120080000c00a240320000b83e03150070403141001e05407000301340d0f0b07100e4034000c4e410110082d0510b000c0f01400ca0000041c0041504024020350044040e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 199747787 1250 199746537 199746551
    0x504120827030129040b03030f0c0d0e030a020a060f090503070905041a280603050303090c0420121e04030215060117040b1b13031502090109150c02040c030f 69
    0x40715045182800c003102c002c00100503003107a42c01d06400c686da52000050590b40f60002c086500ca40c0c5811112038514503910245914441e280c2002c4030b079088640840003000c0b0010a0380c00030718a40c0090060300c08101200005010b91401000c80c100502002029103030080c0d2505200402020b00700c50985070301074190a52440d80550b150701ca800b4008801003c280d0103990710035951f00850b018080342c82207a40705c50000c00708c0d0051003d9401030030000081d1211160000c20881500d0356801180801580420b00f10144103008040701c0c00d4906d80c0401094aa558021084009005a400f0384584070580c00300420103502188101c104074095002d004161182e0004403803070072502800402c484580c40100b0042002064401d5110b5109208000c1050411540303a1091f0019034917800d01020052061080010451580103442d2001508500b44541040020030a00c258486e00460880b500400b020686c82208031301206a000b901c1440002d04981c0000c0081c0211000c08540500c0c1c101 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 199749037 1250 199747787 199747811
    0x202d0105070b0a0506181518010b0d0b06090402030403180b12010b0334021005090a020d0302010603020a2d030314090d12030207170a05041208270301 66
    0x161407045801400e80000b5030341e1030280074010540030703040681c45000742c80d04002141444d009548640c04290034488540e840800b408001c00940c280108940001d00040c40030707003001010349500f1f400f042808510114032a010504031300c900c505442e006400003041109040c6c000c182c04010003000d0509a502da0340e1180d1503200b030300030310a0703051428011400412190044070003647d0480401c08250070701856492960490644c80f45205e03104c181c085180e11000c58041c4a0f5080c5901c2d110700c14041498100e250399140c076803d8000034801c030750294914051501c00d5020001071540030346242c50b400e445414516000410b00d040240100b0b0380e110365040d06550f8008101180e0f8192160702078a003404401c4426500a004025040a00a0021408220507081803154600c1d00e440c0140d0741c034403604008030b09c413402034100c60030007104001d40340021350b11108a60488442c8800c1c24446c11062804110718070a121046054000451601c480d080c0c0c0b81c018a00e08840450003041201c10291f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 199750287 1250 199749037 199749047
    0x10809010b01020a1112060a06050127031403040e0c09040b0607051b060906071203060e13120e040f15050102070b1611030a0503030f060f0d202d01 65
    0x2a0741a005803c25000c450008000c44071002c40d1030300003005040e50740400b900403031800e00120740b01c01000d41c40f41d82c00c0020703580101c40425801604a400100d0041d2a1041101c140d420310000b03041d1040611041c3d51a44240252005014481d000341da19040c1200b413100d694100c049840e00c80c1d0b1071328074070312100d2a00e40d00715540e1607800009041d4507074030b240a4201c618501030003150031803020400c1d1182c5954000c001d0400303d00c038070f40c00c207000300302200d0042c1110400d40001d02009031100c1449408881d903104107202d072fa405001c0c2c04540324a038030121940200c00c3c42c455007240c208035004c50294880e400029050304940c802529130b81d0341d06c1c01283d8a94081c841c11021070303400c010140e110384001c0d0700d82e4009030048a20000401c1c00d0310119280030400002942c0c99080401070010820848600f16040740040300c0403564030305800005460000305080040002da8034040142c4a5610b90804400f040b01c002d050020030250100c0b481040104064110001d100032080d0401c03541c00b403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 199751537 1250 199750287 199750301
    0x40510020a17070210090302060109050c03010b25020406030b040215040b09010507020f03190506060904021008071e050406030e1207021203070c0902090102010e010c27030804090b01080901 83
    0x80e5a82c2c000e0303001c80351185001108054401021801442411100700d102e5000340100c2e280701e03038010b0442d5817400300403408444c4d010b4003180c039003901000100300340401c3c2e03416102c0f58910003103808002030a180030038620b0707429040c000b500b00b818000c0000c04d110f142d2000d05e2080d4020b4030030304981400307039003008201e22450085510f42c86d401d00190f8165403150025141d00c0740f001d84911510b10b0310b0000241751580c0100900044420036060401308031040c4090354102070166a0f501c01070500b6030002d00c0d545134034194281000119000112050f20a4180740d001000040d40c0a040e000801703001841640036000750000700341401000d62507100c001a608034240d000582050070500e26601b00104c0b03068540c103a600c284024040707500895001c0c5001c2e0024480d84a00507660019440003a007940c801001444480c0d1514180030b4295030419a40c0c00b20602c07010070703198407075504c4000c90340318440390700045c00710751010401080e245641d41c0031504407034003600c50303890a55410f42d2542c241c641d4 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 199752787 1250 199751537 199751557
    0xe0c0301050708070c08120a0603200d171c1a010c020603041b0b0a02072318060303040308030c030906010b07030207230d0b0f06040b0307150c05100504051002 70
    0x220100051389a03200c2c20a81c91914480c3e0f0a2130700e0300d010032100402e122000d803042d05626540b19020130421000310701c0c84031a03881e400d0a04144c4451240051810b0354007070310150411503010700500c00d0840050440d4841412445604078071801c0143e10b200a007000303a0040801c00c2090310403052580548441e18400f603004001915665450703503010840c04d0883c1d008404102007010115020b1201e801400d404c0030a03500402202d41740106410070a500084042088000c0e494948126111980c2898251115900c6065503407913540c0468039510844e030000c2c4c21104003106104c0e19070040c1c0c00541c0501429400c98400c0d903251241c41e40d585c8181d1800130013580c400c1c0c02c2000002d414078917504400181030781c000f00c00b201d000d0101c5d100c41d0703d260044035402c18102c200110160000d203036542010b001d86081102560781c0010039510707802c602505440f80720302004558498400ca000500c0c180e40b007000e070381046c684001c102003c1c2005940407075aa0040d0b020800c032400d8076200343c42d80407407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 199754037 1250 199752787 199752797
    0x1150f0b0301180b0907020d020601140105032403031c0606024201090e0105090d0e06071b030503070c091116170a0e0a0b04030b040305160b0a0e0c03010507 69
    0x460074000480350410091110b08140c0c5130001148996101e90200c0c0c0300364001d0f00034282d00c0c1e01c0392000906000058100070319040c54241d0300000c0e0b0b648201540e40c44800980c50000610b5003a10040740c00e004d4a1646c0e500d48000900c0c003000c1c26001a40040d0213480c680e050182946421080e6242c001001c0002a01441c01544191544010307209242044041e803015405181d0101120b41c8413102f47c0114007543c0d203800d40100901c1c400d1103540c0d031002c4910013501509091200050090800d8550640700301008100c00b000e0025800703003003802c1200418400011a604e203092510307604002020340701c170b0032004800640e5411768020f656801100ca010146400e400350b45211004040800c04e580580310040182c10841c4e40c24021310310348842e070301c400800d000480c00304000b290f415001301c40801c3c014882040003c00b0440c00a4025a1504259489800e0368084615002c20020050b110440d070905104403280c80381e000d118140d00c000244c911b13503003202040c5401e03039900341d8034000018 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 199755287 1250 199754037 199754039
    0x60c1112040506070b04080c0a0b180105060a172d1908090d05010e0a05060a0c0c050a11120304060302030a050c03090c0405090f030d0b0f1f0c110d030201150f0b0301 73
    0x342814a1710b55100707210745003075400c041c06c070220305260400d07446048030013440c16000d100818000b042e04948600e02d0000a05c0185030910224083c1c1156100b010345880c1612045961a441400030250040082c100c07445051881070010905e0510645664018002c0e0303000d1500c006039101c244a185504440c415162155803814008024150b0800380c619559036203c0240b6080280100540c1600560042240d81440540e41b4115003c40000c901407000361400000021408107a13800d030582c0042160100000c1840800c401c1142070035401094080010003045940d05036000d580078030481e08081003141d4500840c03526911054400700308907401540394804518040d0005a80604050199241c450840301081c2c51a044100700840e03168440328002c0c000c0c24003042003c01640202c40d100750329000d00984035070640d4400c03120340801c4000302d20b4801740405145444030041340030f48200184000c508000b4001c04070700c1c0c020f101c00d1004407400182da2000040d84003d0b00d5200c2e03045c038036607 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 199756537 1250 199755287 199755293
    0x40303150602120f04030f0f0506150f0d0c0e070f030f060302030c04050903040f23100c0f0c0e070201051603020a0e01050318010606110105070306150c020409060c111204050607 78
    0x44d000743c41d80c21074401d010800800003900741425400600e2180380b4148820305a442e0080c10304c3d034010400703410b00300704c00300104440d61009036144004209075440002c04001342401c1c01d03514403603006518441d810740140030315180c1c030200d15000b0411940e01005400380000030481503034031a1001962560007141c00c0d42e031600c1d150380aa0f0700b040c4010304480c03a1a640d41c909169800b982e41c04036003013038214001007400000381c03185050f000c8022601141500c142c0e800c01f81c514a013251300604501c954040c00c00800182c03440325400740c03c5a80c8207905a04d0507070002400b0f0402241c1e0b94400c3c1d40012030310300003d800303802903904420303c83e125195034502d10b80044442d1b400040c103500090070240d182601c0c40400381720b408060082a41e0b0140301561518283c3d0941d0130107070142c010540781c4a0304010008400300702d4502c5103214070f460a40d08070a800090041d104006001c0c101a1910081303840440d00800440c00c0d017180401540c40a207225091040340c0c0c010703032159907007003c1304005507800 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 199757787 1250 199756537 199756573
    0xf03070f2901060503100f060f14040f0e1003080d1a0312030a0b0d020406140907050702060a03020307030209041401060f08220215040f170102090109030204051305011103040303150602 81
    0x203c51265606c0f12000c5903504019450740ea481e07403003080070038501074950844030751003840100c071a104040d09a203050324081c2101003015a40c400e551100142c8004280400d5924200800440d00219002d4548001d190b11600804c4c0d1040b9040e00001c0a110020703850030f011411070003850741820303004c3c2103594400640307018201c07000041d90b001291202102c0180d946119140103400c900080002800f500002c0c80001e00c000790a03c010300106105100041c0c0c0d80c04100c1c0e240120038500540ca03500c800784298080d000310320b183c590042c202090720118505501c21641254040c0d074803040d24088000094400390019141c15540c0c43c1914034004c441060600340d140100e1000e05196140c41c00780d001345440c0d030001d8003c20301c40d042d002030410110b004012511132902180e8000c44c504440800041c00a041d6803000178043d0380c0f00c00014007642c0244030004007180c1c0101c000d01c05000703540c40891695004039402c07030100e850700248064881a0004003001d4454940040c00c01482d01c80080030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 199759037 1250 199757787 199757791
    0x601080c090307080f012003010b040504091a0f041709010e12160b030105010f1b26040b0d15050904080f0d0c05130b09010c020f030f03070f2901060503 67
    0x1402d071261500014005608000311850513100b24000518140300040608410461000850040c002400140072094240007150200c540c12500041c3c100880e1030050a12031070a1801c02c001408101000864020548800d00c9503102d10120401ca480300b01c0f80074601c1c0030301680700b40051409210094641405030b018400186480f0884684543d13031140700d11030041e1034005580300754010004201a58100e00b030301601c041541071000031000348059a4400400010000d030211046d40c50781180314184420f0000101c914030000359550b900c40111614a03030090b00306a80c294a8032040b00c0d102c511414070070040c1c8000809400c01501c4071388484400342c01071250700428440401205142003200e12a822000c04103868040e160401ca801000059550b07a0050110701000c20050603e031303900c00c15150b40ca50703044403084410060000800d140c00001513407040d07180320000c0d080c001e00074940340708806e441c03141c07003404000e0b100c0c0e4801c0c41c10706a03019015800c50341028018051140214060342d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 199760287 1250 199759037 199759039
    0x5060f0f0d24030501180305031513061401020c0a03120809030d15030b0703060305071a0409050702010b120708060f06010e0a03080c071a030714070818180601080c09 73
    0x300700d002c03080ca4060300030074074840d003420302800c09074003003007000700a00440e2000c05c0408801006054280c0b4082d2040c80004c002d554071000d00c003a501c58980d00c54400c1d909441344030008000154030341003180c03e50842180030714003501c40e8600c082054170305040184d09480c2c1c00f074a241110079181005503544280500700c00040c0c001030000c0c080b20a542c1c400c0035603400e40b10f0200c00303103c1d00e1030519420803074001e0079101c20581083c03400d10219100181d840700300ca965401c4500c5052a600741a0000e001d1500440000b5003003100340102d46605400605825401300d0300324985034018402c55075108120320a01c81d08e42c12480000d00c48000341208640c2c02041810020004a40f540029000e000d0540084490310130120380f1f81c01c01032042003039501520b04601c0e0815031982c80b0040881e180130040041040004900c10050412504001e8455183e03001300d2240e107443c030311020114100101c0200c0740c01070b9520994414a0860f1000e22401800180c56240c10341d00e0324407400c01e0941c09804c5071 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 199761537 1250 199760287 199760291
    0x308040c12060c0305070c0b180307060f0209030c180703150b0304050a03140a0c022106100812030103020d020108060f1c0218010810092301090c05060f0f0d 69
    0x1441c41c41c24218405480c440c0c0b0300000d6400c2079140241c11640090080d074100f01400c2d2044e000503420000b0507400500502c02100301c1e0501e02c8048ac03a6101d80304000b0051810414605e000c001150050312076084100d081d241810282010704c46110040380c47c0915082250010444150190703100151001c2441900466a52200d2604855034402c4d54203c0340e503031040d41d00f03000340f43d480900c00b61659000c0a2080c03902907490b400509981c034899019203e0001e225911102c4544080040c068010003815070346035160043d048480c58069110300001d0380910284040741c0c201d058101c0c2d050303950040044032036270707250f4004440da41c0300200490342081050b603401c4072695030031072072141d011881071140c01c40650600c18460ba1001580a802945001500500150102142002920b102d0b00d200041700400d0342007004100003490809a0300e0a00340da074158481c041034020490040c0561481e02c000c0c0d40e6034041c0081c612505080c41504601403101d05840c560060003004c0600c480100 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 199762787 1250 199761537 199761539
    0x30b04150303020f011a032802041d0c030a15090201090f0b070c080105041703040323070201080f01050102030906180324010605090d150e060703060f0b070f0308040c 73
    0x84441000c200c1c0c0055025034007402e12004031860901401001c040c43c42d0003002054201c50100755240b241880c00030f12400e0062129001c0080d040b0a0400703190000c10500c00417117254442d0302070301d05014400010340100c0c48042020b00340002c06410941d800761a403001e00f500710704403000420460700d049042000f454000107030140f100130a0405406003040e101d0355aa0b80e071070300c5207800e0f4682d44400e40071b90500c000c00c000300b2621840c4143c042924200b00e81d5a943e540350840d144509903160502d400401400321001d10141e0010b40151071007a01c0e01c09290f21121108203c40c1000d1150500607881040105207074100f40010301a9014101c2d5454035122200000909211340e0881c1c2c200d070407116040002c0b60b1342e81c00700441d00401203810720b94604400d05010a1114000351005001c07895400c24000342c100036030f40016100051402520010b04202c000203014000e45d200d090605021011b020513000b06440440e011260302c26141c0d2101c0c003942e0741c00d50340d00d103000700252009108410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 199764037 1250 199762787 199762811
    0x20604060c051606020a02010e0a0c0b1b010c0518061602100c0b0f0601030b06162d031116060918110d060501020706090e0a090521070605010509090d030b04 69
    0xf40000d9501c00c0801507203400e07004e04000e007121042c40c4626019070100402601207030303941c00c2881c251031100c01500d60b50070000485041102e540c4611100540c42c3c046038070b454617801805052201002043c40c18110b05078000c2203240d00508030590103d49400c14400010b03d86004401650985030a28629150032610b500703035114011900d40b000100a1020402c40750307418880e023034880800300c034024180495411858110040041c0c028005202000c0e0038482c4c0456280c5441c1840014034000244403071490010031f01500d00d51450000d00c03407940303a0800f000745c05c041c000607154140c5d1003114242c50110840c5801c0401c10482c0e0003a56256030309240341e620340000780345000c00304d1000f0401c941381c0000280740016a03401502003041000f0140001c00100c42150341041d200140420714025500780a800e110502040c603401c442003503410b9a0b2054644081c20383c450080c41c042060746c1e6181c0901c01c240000311003180b80c6070007100308100114000c2d845000c80300006800080ca080400c2 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 199765287 1250 199764037 199764067
    0xb011e080f0603060403051c0212161d0d0b060612010602070e09060112120e06030a0609050108030906070210030605030d030906050603010e071202011418030d0c03020604060c05 78
    0x119058001440c08810001100c10302005103400030302c1a0000d200601d0640c030010701c80e00440d074040c810301c001440d02203001c940e1601940d4548880040144490410901d80c00100040d0360f0010041100303403022040c0d14103c04104c038203800780641141d00c9440a69144440e1314002062168007060601c01100c4121360300e240d4602801d03064004054080c1041d00c0101c4502004014500e1a0b101030010b00c40c907050b6030b05480030710364092090408034a1002040c0c913407291000185412810120410801d80081e40200c011250280020480c1c0d903201e00e0815242d00c51510b880d5080141000480c0040c03c0006405450005514001500c103880e500020b062510912082001a89928446040c40017900c80c007030308240101c0081010f504580740d030f5519020944038004110403c1d040c05425640561042107088612012003903a0380d00741c13940c0019240c0c0c1b204640d07010f44035150f00c21400341d0264188902c03094140c0c000302801e540d55511880500740409544041001c244009804c0d0b402c46 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 199766537 1250 199765287 199765337
    0x813170721020a080708010e1501030309030305070f0b0a02030a0c0503090d08100b12040303060503152d01030f0606270c05071407030203010c090302011d0103110d021201090204030203100b01 84
    0xb0760002c1056845a00c2c040e1801000c90727850744041040000401c0007903048405075044030b178542401d0352545d10500f81800049407c10019214107060010860390f00c2450740250310819044c4030400141200c4901103070b80d400201c515102c55448081145852800b681d169507101e45199003002c0352a4031403140f5401c94115414075595008003200b070000f056094002c02026020540c0100707137a46c1008006201c08074081c08082c5c050300403140c1401803000062030b4001c22011021a0082703940d4928003120401aa90300607a81030b40343c928046000a40b0990814040d009000761081000d00010104010308030071140b101440340811400d000202c1005554070350705090300c0503041a91a41c010301d0300351503041142400708040400c0520050780c010f0900d0185041807000c400200d05030704010b900401c003c101804101102003050a02c18029030001d000c0849101c0e11b50700c031030340d0f500803001c26800340740002175054006403901700d41a801c55121a4005e00149864417002e918440114103018003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 199767787 1250 199766537 199766549
    0x9040b101214070c06050a0f0606170a050609150a1206051b0406050f0c0a1b031407060504030b09010b090a060623030103140a0813170721020a0807 65
    0x35014041c0582455482030011050507000354240d1898000c1005000e0b0340c80c4034000b4202035076103000c1903850031f80f60b100120541022030100046525400c1c003500368a500400340406001400010b000944540a500c1c0070754005441d000440e291030a10f68034651034021000d03084051000c00103418803464a074680c0c03860041c000010b03d810320030200c003040d00c2800703e14488200200402c009045d404803c44205080c01001c00d6120481d950700302c0c0c1401240c40d405480c8842100c0944d680c082c00001460441e803298800c5566640102d00c902c1e2200050b10580e00810410705c02040820030721061650310a84030710002441861880015201c07960560350304c01d00c50b641e06414402540c11458202c032500501064071121810742090404a110500008003481e4603d41d510604030020800c50900740c0c0d0003030105403a41d0441845003401d812034403031898403010001c104170081001003904000e40d0504800007641c00a005505051500200d400700c0c0c10850404000030f80c014140404005058 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 199769037 1250 199767787 199767797
    0x10b0403020118030201020601170708010624020c0a170f06070513050103020708030c0f0421060522140c1906080f0f0703180812010e1006021209040b10 67
    0x3066000042803860340a4000040070241c2c0b00500140c1e07000509141121040b00b002c00d95003845211150800010b6071000a0a60808802051000003860304040c03508050880c11510105107000304e98aa0060b00707000d400070346901040c454900d41c03040320791038007100b241210116600f07080242c0c40c01d401100d1040002c5c030041400b0004401241c42c4400501003440d082d800d0109507105e40540784400307400504c108100040b2a40c03851440d0302554010035400149018a000700340440b13154500b603d20454500740307400005981c103128030b014032007245208001014004041c0c2d403080c0a690504421840300c1c859142c060b81c00d03030344405000c44284412030165200520b0690081c00001c4043d00a80b480007e610400641c40d8565005550006403486c000c1104980f00403603580f02114402d019241c48070024514001502140c100d504980c0c202d4900c2e1a00e50707d9030503036485041d10b40a0f210068003d580414080621540a4402c050004200290294107000017900c1d01c0030000864010032 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 199770287 1250 199769037 199769039
    0xd180318080d12020a0e031906050f09030919080a03180801051b0a09090609090c060f0203040e040218040b01060e03070501090905100905090f010e011a010c0501090803010b04 77
    0xc020045554001d0801200070b0425184109015040b816910200f40c8119400302d0341e0a40f1902c624114880c481d400b80c1941d26854240c14441140010402c05850786400d04001c07506c1c420f0b101c0744481c8101c2d49280034504195030380c810000c940542c000f03408001d001c01000400d4a8401344079082009200340c0b244445000040c07020203202259134401c2d482030741340c5000c0110881c1000c01c051043c40804140341e0b690f000e03000081c0e030490000d400003d4201e141c814089951801c03035000707102d42409000c07484c4105035203180840790f00403144401001604240000c2180070410390740c49800510080502e084140883d44015100030121803c2d80e0f00c40d03d0030010804240c00690f040d000c04010380103091500e00f072a00107070841b599403140e80d512503074880010b548070848170003a4000c0d0404072802d0009041240c5001d039206443c6401c0400c80d441d02c0c1541500742414460200c031002c0151210b2000c2e140680196102c0a552038203940030f54903500c04000150800e0002d5018109200c0007584031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 199771537 1250 199770287 199770317
    0x702040f1e090204050609010503150702030d11040603050610091406210103140601050603040b09010f0e010b10050c07060e060706093207090203130f12260c0d1803 72
    0x910b4000c0c04481c007d12008006010940b00032034110780a804400c0c64441a8986080403403962250100d80c65203d46040003401c0205030000c000c0080380c40302d64061090b234884204101400042030740c10720206180040c01c102210400c2e00030361646800801305070034401c05e8a01e0346182c5000704024541402480c0040c800c004100440502030102480107100329030500b00440c03c58480900094402034000000403d409000d4021080e500d140c09003d00584c00414982406006a000b01070302c22952200e0011a06100c0c006a4810307113441401044031900d0700d01e0507104000c0d44085290060700401c4440701141040c0035003051103208440c04a1200c241c4200f80551512203212405065403000000520704d00004200090340c1c0c40640c016541e40307c0d170740204e003405c1541c10014580400d17103010b2024001d40c0b1200080030f283e2500c0c0d1401c03020f05038180070984608026509100300c031410116104040310f40141a4000d1854000100c0394032201e4030105140c10b07808210001005034000c4205 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 199772787 1250 199771537 199771541
    0xd0207080909011203051c0902030a0b0a110c070b0c01110310080d03091101030c111005010e07110307030c021504030f300503060402210405010b030604080702040f1e090204 76
    0x40956654901c520301541c0c2e1700600e507200304101c0040b00c0c0500c150042000005500045d8003960003000c81e8030f00000c0c0d1070100f59100c0101c0b0910f0200c2e152084081d941d40d2048120707801c5170510009000c2090410301908010b80203034201e00c03225941d0710741c0322144603080c9000b1030244e0820000684414901072a807403070700c070b500c4028800301428120004009103025101da00051024240824004ca00400c101e134841d0000348107038820701c11840100c0c8a000079034031017810313505007100080359641e8aa10944013120a854401c80d95401000f41d440400d204104800070288018041040e01d041c081200c1c1054026810541d502c1c004481002c04201d240140312003c055480040da1280c02120303080010039100780d00c40010b101d8000006280b0380c0d1158107c1d60107071580102120900668240380c0354000040758219425807034500d658a0500c1d0004505200f150b015498038035240a650a000213080b4020021001c40e46400360030700c0060500303840780e100310144c03000092040c3e914010002 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 199774037 1250 199772787 199772789
    0x80c09040c022109010e210d2d0503040803070c020402070303060e1003080a0f0c02030a0501060509240609010c05250e0c070f031205040308100b0307080703110d020708090901 77
    0x9850f01040304007103d03604554103c1e0303100000c4a40c1d146000b11f50000b02203421095030305000c103004038105144910f80088500702140403c0c04041074804140c91008250704071010001c2c0421420300003c0d00207400200115170000140c0703400501184154003040c03d80e04030000850229484040038413032081b102c1e809540c0031001c1c07890700c01c040d40b0b1500c0305e0605210309007503070040001410700742d1400c5014240c102c1101e80d0190803109980700b9420400e009142601402c0d00c14a02c80300030a200201e8102460000400c40d0f00070350404c00e812042151581c045180503060046001c151004154103000b10049020701d0711a2401d080c007150b400c0060a4050b40009142c80d2042d4140a549640d9000350703060541d0101b0100705405460406440100a034800398880c1401d00080008146d800301c5000c0c040e43d220740949050301d40f074500e5038001d800f007101c0480c0015480000200014402d8219802e1840344514152602c4091003090f4180e9000e000140c92240c000241c440543c100714a9040c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 199775287 1250 199774037 199774093
    0xf0801051806071403070201140406020703031b0e040b0a090e0606031204031a070c050d020a0506060f0d0f0804091d070503070f0902070515070806030d030606020d080c09040c02 78
    0x86064a4103034406054413140c1c8000004400000c000169014001d6110420700f07501303031482c003066203002e00e4082e020b54400072048000908142d541042e011024030782d1102c500c2c0b240c61700e65488014905120082440300e0159030300004040300040d80f02d600d8820031020070340840141815107030904c2071501e0803200b040c00032024581000204007141c1503c407180111041105045100c0d181c4001c129100300c802030300a4100c0c003880d0380040540d1340000d140c80302284224242c41030ba80e40c41c010044003490400c3d100b80c009072440301400000c0c8240580100b00c1c2e100d842d0702810251903d48540858503d0422001245031158402c4ca9200f0204059001010b044006082442c100700342d140711015140300d0b03240d03041d4007c140b40b000c200b01401204900c00004400309164a00b080008001e054240d904501a01656516802c400c0c401d02540d030941324681c008040c02040903d04076010346004102100241050203600400d0b61213005a8400c1c26142d0f0082000440da000c031060000030b618014 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 199776537 1250 199775287 199775293
    0xe0115032a11060714030c0403120809011116020d0609080309010c0e0a150f09030614070834090e040309080607020f0c061c050124080105030a1101090f08010518 71
    0x22040c41d50011184d000d440c01c501c16280c60f42c0740d947c02007a0300d005907000200740e83c0c01c2c10701e00e01c0750b15403021135103204201900c000c0c0102c040e10781d225075143c400d080711520900e581c00c1103000982040754110f40481e1141d100003030b40c248103490f0003140f41c03c16618a01c3c940d450340040d0800d6036001030740c42c5800034100d41031100549003454442054004046401c14000e804013818601e0b80102c0c00c44c0300554100b0000e10918003103034003411191600716072100c040358803500400d24103015403003480201d01c440d964404451a0440c1c40d02400200752020b0404c00000380700200d200c4c285240954000c40c403175210020800e0601c0015801d12034002d01400840d8010800718102c075400040d000c0c4203031029038200e41d507120304054095407401c102d441c0c85040c5040100014807002c1c10302071400f140590581c18444240c80c11011102c1920a1141940c15400610f8030804039056040850469505042011308255510901c402c0ca1a40c2d902c5074199035518800c1086228003100c07a01c1c0c80035192005 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 199777787 1250 199776537 199776541
    0x10f1701060e0a090212060909010b0312030c131401080619050f0409050607020c04060605040308030c1303050a0317070807020d0c050726010f02040e0115032a1106 72
    0x1405060005124003410004100c02c00003440c2c84164041010b0280100c1c1590344414100b0b02c2e5650788810344030a4021100e4500081d018030040c801e21185500003400b402030000901e03061800c1da003016107c007041801c00c112445003440904000d81c01494881c09a4441c41c0b0503000250071f0200050106005481c41060301e1040c06008003508103940040b42e07403209010f04503000c81c008046074200103260784501c4007030000c515000500710256040454050040d2074079a101100c4500883c40000e2402c54144041074101e11100090040790582c100c1120340a543e0342c90f514640f0701c42910130b07002b14003680075180c41c1110341c02145a10054905000c002800c054900a6440a4104581d0100a10088820f04000041c231200d0010300c611031482240a0282011000c40950101c210348c0c550b103018034400050500b80242c0342101d645480b110700d540e10f0240002c0364041100503440c10199111000ba4100003040d4040d41011b0503075419141000d2042009480c060128400c0c8459900c4901 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 199779037 1250 199777787 199777817
    0x151906030e07060509150c0c1e0307060f0906270f0e0f01050607060e01060801061404141015030e0102030c0408060a090209150f06040303020a030210020c1b0f1806010f 74
    0x800031b424007154110180e0b0340c181380b603001401c00300244001648190350354020390440ca40c404813940380c030394103c00b03a901070750b501c01040e940c041843c019103010540080b4104a054040e21000501c103000050180c40000310108140508007107030095001c1c040420b00c18802c280341d450406a2003803125034000201e504000006009002c0c403140100f090340c54841154036220301b900482d00801c9000c0081c4100c940390001001d02c0c1503603090090044c0c0c078184000300c40144002d0654000c1d00c41060341d1603607506100c0c41240d11150300110805158507010f020f91b90007802d01c015403080c480032582c2070301c85040c10f46090500c18040c0601c51101d0130686944056640c11860582109945a20030141c10811000c105600c02c083c204550015000c0340000a040c0c011512002882c0300750b00340c2c1c1d50500e40c1021002240602200d091456001c03200d08010300c40200c0f41c00a41c00002401c4200c4180c06800041001d480502540d5003050328100303108103560010800c50307640106003003a00c007071a500d20b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 199780287 1250 199779037 199779049
    0x308070810050321070b0108011a090402180718060507030f0302031522020304111801030503040504110408011811010f0e040b0402040806090102120705040509151906030e07060509 79
    0x101c0708500f014400701821013202402c200e40030f0301d82c4082c0076607456035a00c4e0202d009040e003015003a0708441622402d161440d250034507920a0782d00900702c050802c1c0c802140b4000c8000100064203001d5401222030000008001c2c040c01404c4031350f151030f40c0e9141858020b00760b600d040d41c40e906040c01403090101d0b855a220f5614001c00c02600c1e0304440303c0d20418070303030101156403084804091002082c00103004c1c000d000d0000c801e5043c1d941b0154100d8400d80b08101100c00d00c8007a085400501c0144110714060f0040d0101c02c41130304034103040544a09480b0308440a01166154019007014005c00300515220f2040031000f09081c070320300b45244030f60041c02c1140c00001e9070f481940c0c1c94a480c0083d540c0c0e6416100030b0b06a040498440c1d103000009907000b58401c4a180c3c00720000756002984441c480e40c1250140c0340060f00380d0302c143e140d854800040e5110345c2e05483c3d001403000344c2002444141d803e16401401d1980c0c01140c2c5d4480b11240d00c2c20041543c12402c1000401c000c84100c586980f = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 199781537 1250 199780287 199780303
    0x50402030d03020c21041d01170c03030d02090a03170703180609140d060c080906010e0402010f030203090a08030901060320060901210f05010509070206060109052103030403080708100503 82
    0x1742803821380300300300c1c032840b90268403982d0400020680c548403512208812520450305841820850007141d03043e1003062640c4189103095294541c1c0200f115a818040340d40107040154001f81012034059265500e05010204489002c021100c1c041032140c1810740c4a40510980307400c50150365951420301c1001420300a02d80203a00301407002411015494540d031285001040d00482c0400c2042c0d2107a1001f40703c00c400392201c440074130501d4000314802c5014051180030703540c140c55445518480d042c00390082e41000b00405910700805442c00007080c074007402103105442c04400003803001d09500d410042d800b410f100303040240f0162280500b507602d0b03800440302c1c020001d00b8401d9081410700b5a01d0b2401d92079400d00c215403810019200492811031300194107880c41103600c188180d48840c803c994800003183c1c0b0600151030030401704802d060a146020620b034003030100c552081403640510785558010303a4100d001810400402020342d40c8505100e8205000458144520b442c0c50002a960450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 199782787 1250 199781537 199781563
    0x102151501110f01020c160803091309020d0c0905060a09140c03042d1119030b150612071e1d041b020a0209150d0b0a020c070801050402030d03020c 65
    0xe0b1581015103800c10058039000452590017959035007101a00a43c031100c1e0303140c0c0301c1110f1080c80710205030200040140c60140c1005020a450f6410b110001c01c05440008070580c0c0005010180c000483e00e1201c0206c0a40045c01c00402c850a00d403045c0155940c40f0f51141200610301070045c04c001c040d00c07401c65004214240016201d45950802c1c41030180028240380200183e1390307010b00d01c0340788246c81c103050900550103000a00c021000303000103407000c04501c0c2c01c21000403800b4000a801011242c1e04640c400e08005400d44442d8007180d0305520840120241003a41c90804c159550b0103200034502404451441c00200e10040010300007503810f00310700550566041401a039500c071a4450b210078600600d03004540400320a02035200c4003815408c1e40249144000a1110f4041000751142c003100a030200705002c040762143d100b099006002c0d00310740358003003150b51180c8600300301200281840600008041c10503204140c90300f070705014042e0505005000181e907120340810074580182c5 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 199784037 1250 199782787 199782797
    0x1809091109221505100b091011010906050415060315180218090f0c030a0201080405070905090303070329010f020a0212010e0f010b100f09120803060102151501 70
    0x4030b04104018000a0900c03501c0200c0d03180031480144080d18071040d10039020030800300110303200c110070407410031502c0c060a103213000104052030701c908007504900035440143c9008a890b40c40030001d9801d4440c188000c0c0c0315240c42c1c4083c48117016012000e003090805e0944108826403441c4d81c0c2400712040d0b07030807000d000c03955518580a0400040c20f2040850343c01031069402a240170003007100564265041d103406e00c00d0711124084030400080030490004010010050a4002d80c0111a07802d0020000c41d014080d000300040c91440038043c0c6c0707009144041c05191603103488403009040306d10003820a800c94101005200c0c0e00510075103003002d0001d00b031a101c039058800708416458447d0381c07000250840035484020340e61110651010810715035540589603c90040e03400f80c0d00365030a524100764000c0d91074a1729040c1f40e00a00c101d8282c050305050450301190389410902c44032081344c81c25034000c51b00008000d441d61781071181c0c080c80d803030390280c100150920306401c1c0c022410443c40941481 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 199785287 1250 199784037 199784041
    0x91205010209030d0809010c0314161101060308070b0a0207110603061f020c0f01052a0f01020a020102030f010509090703020105031f0f05030d0504140603130803071809091109 77
    0x1020a40454120b62030140403a2003103240500001c01800c02103850810795485c0100298a0780c0c413034083c002006070214041d40d419150200710640341e290610065051241c07014240101c6030b000e0041d41c00850041440d50385964a0f070401e02c490282c002c11052590740b0410410001400144400801c4c5005545044c4c490b074451000c0703504010304030051207000760442d01d1076614650001d0a6403900350140d9040013140320303490055039a40140058801020321503002e454200806900c92071014146008451240865900d82030880c1d003c0c4d00700c4001030b5000010040040b4015031000d005003000d0710b035079946290070132200c0d0303c66050303003c001d040141c00008a420b020031010b00c200a48203850f10391800d140e4440c6a01101d401078070440c0e0103401020040044103000d04207503801c980900d40c5089900008604008040d84020104800e826641200802140e143d0020718444d041c01c2e00e40040c1c1c0f401046460030507084c03980c0a0352149050810460000b61005802940e0b8081500e4094a075 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 199786537 1250 199785287 199785293
    0x30c060f120f180c08121c02071e060608060c0901021b06090a090b03060604141f1203080901110906090d0c050402070302031207050301030201090501050919150201060b0a0912 77
    0x19000c191043c01c0c5100294070f5010a0000f20006201280c1e489011101e4000355070742ca02001c1d02411080940307a801c0040d108108622680003030181901c10f5030440b545940d410158061000320090a0b101c40f0398405050216020401640c0d8000b03048000e564200860600000d5a64044110642080c1e500802c3c40c000303602c445c03003696030305c00c030041c00c40618580740c0c00781000400c10481502c2c0b00c3e100300c2c0007140ba942058400e0030400010080b40700095034903c0d08501c8080364107082c2c660784109903480000d03480148901c08260074880c1d600c043c182d040c0201687c0c00c1d03807140e402500410004001c1e000e43c698404080b200314020a980e05000440d680c1014210340100e540b10390f0700180000703001e0003050307404401000301e12121020203074940c0b40c52404544600090100901092171007405016030b41c0940c01500c2c10300303001131581303080c2103d0800c45228000994812030040c40402d9a00b40601d0702802541d01900309640c1403800e00060f002c009202c09810b10030b0182025203000d6003418 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 199787787 1250 199786537 199786541
    0xf030f1e010b2a01021b0613020a17101b0806030610090c030b120102070c120b07120b04091b0e09060a0c120e03070204050105040207020d0206090301021b07030c060f120f 75
    0x2d102101d9000310349445454244841d064015004086c407070103940c00140b0f80d410462002c0000a8028106004940c204402943c601011008240840c07080d035221303d00c00039050042c1e454400c603078101a5840c00900c18040d0402030080d142500c607420445c02c001d0704e100c107064075500b01c81c41d641021038050046c0d0801d074003e100940c403c581041104c040400c80310015001000198880c81c00c42d801240d8410781e00500c288034050040c003000d51400404d448034030a0306040c007402d4185100203000d84692000074219090303440204e9800f07203007100c0060b0002c8846c003c3c50050841007492a4186480704080b9143e080080c15500130303680e2107001b402001d1091040d5a14181b810104025035022001c52664a400c0094100d03c03d0703040100208250800d0300a44401030380c080c0c000403084070194204a1560410010790f5050b641c00d10a540f00d580e01080680110141c000182a40c1d606504050b151540c0315000315091020f00d141d50407425a126280f48d402810014002641039050502c00c00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 199789037 1250 199787787 199787857
    0x10c0201052101080105040308061906122c010509030c0a140c09040b0609060f0607031223060906010203070f030806150d020307020705031906050901020f030f1e010b 73
    0x582c80c0400e00001c105540c056004500480c00303038840f4201c80c2d4404040200c403c500007a0801c0080d0031b000c08105060082c130100315640011000400d0b03140380890482d21103814020410100018007568200d030b50001c1c420b46070450384507406180340001550901c0d645503a041e00003050714840c0c03808200401010b120765203c0c2c660090045c0454101420800942c1d6020f039101c910481d040c4d00810400c0c42c0030030510141c40d030b01070700050611041d1f0b1002d0300c5108502d0002c049103511901d0024107400f8507039229030304450000b000300300c5003081020300442c01c10042140b0b040d54400c21140003c10410340c982e43c000c2e03925181c0f200c40e0b42c3e02c0c9404500d02c80c425005c1d0f00542100030541c036010f0081900a503219072290350881d4881581d0700105680c52405004070300b00b86000d89d0080d0f01048568001917888540741d80003519080207280d1101d0a5801103c148d245965484184040610b0140c0120102102611120b400b54141403c001031446405d8190b54800c508208941b00903030f942d00042 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 199790287 1250 199789037 199789087
    0x11409030a0204182901270c0207081002030105030a02150c030406030e0c03060f07030f0207050f0d1214060d14120d060602030c07170313120204110702010c020105 72
    0x1001360380803045540950403502c00121205c0181240e84480b201c036421150b00881d00ca08a1102c069182690103481d421151004450807403a2000304146400035001d51046118181e00901c111440c0c511a1402c18800070059a4083c4c01000108040d550000b810501180c04941d41c010801c1c05840456091041c950f0043e5680004a000254107805500c560f181d10041c4082d540300814140030552145021240c40f0b002030704110204450368400e500c040381c41a2094001072410219854861404880c2e90301c1c260168050804e044006902211a00701c040d13010f0018809403a00c6180c1c0ca403401c000502041c0246400b4280d80c050120b121001c064001518013a50078084c0307020400d0065a001d550007230a158140b0800042d0244000100c441351645000038100c0c4508144c0c02060701c0541461070f61652000344000e05542204109220081400600451100c03303940706020565011a104983c0316005104080160741c0000f18072071415424a001c03561028034500308423401d425020b6603 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 199791537 1250 199790287 199790291
    0x6060a0311010c1b051005030609011e050406030803161706090403030906020a02010f0b10020c101103030f01051e010503060112021b0f060a09050a08030405010f0e1608010b011409030a0204 83
    0x40c044454840410505030342090310f0181d21b04a940304107a0740c52100b511442d0300321001c040100030f61100043c3c140c00d00b41c030b403000b801e920030b07074030b00c000760030b842c80b03900b041e110a01c00106021030b049244a41e06040f01d52414110ba0084440b100c0340300c046001810756000746808800201010322030360154100303642c041011500c900541900a000f08400c48112124914184480c0e03002e250990201c1202c0c406079000b09000c00180d0188200034010b140700c0f42c140801e20107240d0f602c080502c0554400c0d4038039101c5088640c501010403802454500c1752081e002d05c0e104001800ea680302e0201e990000082c2004050311104440b40300082c410b120002861443c14150514010004256501041c81c1c0e401101d080e6244c1b03010840843d00c400b00010826800304006000081c40e0b84040d5a000e8000c030300020750868400c0c0010180c500d0441c7c142d00340d42180c1541e495140c80c07030f0801e9010b8200c50000300500c0d48801e001070404c1e08414082c0080d040d011031401c409607410000d44d4151a406041 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 199792787 1250 199791537 199791563
    0x270c020f06060a050a03030c0203030c06090604110d08040b1602060c030d0f14070f050c010c0e03060702070503100b06072009090d050a260c0c0c010206060a0311010c 73
    0x4000c0d00c41000c4200c2010030302680001c00c005150032a042020340b90b00034116000d40e881c69400b6150940c4200303003280c050106011081c0025801c1c00068803078a04100508a04c1c5064508a901c148124004501c699043c80c4005c0200d106c0c0ca040d0707401e4440014899688440c2c404601c0c41c8401c041e100250301100006a42810540c040040c0582090440080c002d102014103107906890309500c68820f030450b880300084805124007410024402e15062451424000c00b82c0682980c0c0c405000c940400d81d4120545800e0500700130042e480441c42c07025080407400c000c0020740310f0048400211601e5101c003588400d9903180d404590040340c0c03200e60460800c400c0703020003400a426210b07041c480d040c50300c001002142c0100b640e003020f0410307230f0b15945031590680040c1c60820791143d8480004115541d1103100e9001036010501a8615080f160f03141c1c0440310305039140000b82c14815046420079401c2c004035072602502c49003620761000b02640901d050000403904c42802c4038010300944858030b8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 199794037 1250 199792787 199792811
    0x23030a120506220227060a14190207150c050c0f04020d0525080f0402010503220f020f0a06090e040816030c05061b030f0a060803070308010503061f27 66
    0x4014054072917a1460f01000320203c4c1c8002c401200304141c400d400c64010412050302ca44515900c541d55003e002c1c0060516803072500031500d500c070000011003d680210000d001580003d103034446d031501140340040701030b101a0395140e150300c0c00f4201175005100900c2400c0c040c0d95140c040d40c00c03071115481c0420091900000340840b03603507490b1440c0d1260b2a11812a080d0b1485624400d12404012031139558603210742c0c3c0112944c0d03000900da0302c0400d88085202d00c2402408ac0703a00a107034011030303c0ca58100f206004001074007002000c03183c403c0308009002c120b415005000d0344215180ea02202410b81e41d14185a40c8500c2100e081590445d0061b00035802c2542010540064171301500840c0c80079640c4803010030440083e801452865007007440081c40d141d03039142c0d0b42640540d0002003ca011036450f40c0170b81c80c44d04520001c4004c5000a070041c042800d0400400d036020302e00d01410742c03d069061002215a03161800b555440c100310850320f241c240c00c498480101c0d000421400c01181e00808 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 199795287 1250 199794037 199794041
    0x90601020f030a023319090210080a0b190320030105090708010f0203010f030f020a09054f030e1302030106030c0207050102100903090302040923030a12050622 70
    0x1104035050083d00c040c500c43c8070049110b172a0a16180080c42d080300c2d4940c58580c40c40490007100070364466845140010040e03e803800021111282900c51220313a0070b114903404240e4540b0403005020754468201c3c4099110f8282d480401c49400082b00400340d1686500310b83d00d08a140029074040d0b0a240500030b81d2400024610708a82e00d1a000b044031080400752507090744001c3c410420425196142480814202015002e5051004007190001a41c5010340c00070b48604903902999251035120741c0000480804804007049681040d100124011424221000003039840f440503e0628a103d04200f5018071046015000002c1030141855419008034020754024080c03c40001c0c1000400c03800140000784040903501e050300034100c01e00308a0400c10050800c17081c150100011044c0010140e1507038424004850701036940400c03c03521007109102060700681001c045a802045521030066101c5102000711002a00128190f00e8440014001035004826002d101d0700101c8104000e45c2c1c55 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 199796537 1250 199795287 199795303
    0x906040b030612030313080a110601060509010f21020304050a05011406011101090f02010f140f0702090c030417070c03120801050312041206051003080a0e010311040311090601020f030a02 82
    0xc48a05420301c100d10415500d0f07000541b400c10000000c4241000012085400f9200040541c900004060070030300c00d15180050a0f404000030480020398112a540e01843d0701201c400e42d400c1005042c0c904a6030f2010b0309150303407041d910543d40031022030204142409090038003600074000740440c0c0e01710110090700620980351240819862807420546000c1800f40611113a00310250743d0241030a600191521009040004100019030380c030080c00d40c40520240c10150f412107031260301c801ca0351052005204000d400c241781740c04140b08010000d20510211211107104a0401d07441e0642498068044010b941004060b0102c9070300d402c04142c2d1000304d1604030380d070071411601103034400c81c1c002e0709500c620b0244240400800030310001181c140d800c41d13500014003040001c0c0c1541e4a480d000307103e41202c540e100000d501301138100250340c0c1c0b6000d001c1280c5145840e03e0314061079540c46498012001da98a40603d19100005000380c1c001e2011101c607c0760401a04c4d55404c010000945a13807003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 199797787 1250 199796537 199796539
    0x604030308101d04060b0111070e0105120c03210d020f030406050106030b01021510170f010c091d13080d0b01110f07030b0417040906080c011e030f020906040b0306 72
    0x70070001d1044181e410300d206100118043d80403980301e0362200c101a003001c1100e20305200c422003040e400c1c00000c01850008096040c48030b019035041804000006008510200059224503a4911555008152001c22800810408001003035901e000c83c42ca01403000c18502c4d90b0304c00304840e881401120000e51127143b2540302080941c1c1c075041c0c2a0f00300d4001d60a034600690069100781c0300700c4804c81c416500400d4140e0103441c0c140e903c01c020b1804034001855421280c01103003c0819900090207841c10707022440c00e003844c5640c1440100b07a01c12421103850440109030002243d0703d00701d01035482562a401020701c42c0c0c0c07040b00c4805080500b000d0745a190008850a07800400420046802445020208040c10400d45951154142500c010b0000c1c0c0304482d01010380c0195100c0c0c0c82c0280002d11141c103001c11141d1421650a007001c0110100505200c4d003181c004098801114201c80507075080c1c240081d42d41c900c2010b04d0000e000c0c0070400303600980c0018010425001c0d01000c2c44c41440 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 199799037 1250 199797787 199797811
    0x2010020406030608010e0f030912010603050d11060f01030317071112040f0f030b0408030c0d0906061508040c030b070221031f0e04060c0c05031218030408060105040c030b0604030308 80
    0x3d46d08407416543c008402c030200d030580040c400c1e14140e1622800b450030504a100008c034070300d43c4a8840c80c2c100000d510300741000c140f049564050b604d1082c0107803a03211007100310780301c070640c51a1409420001070000c1524100701c658006541d90740141f80300d41c0505034040454540041c018014003a039030207801000c0480c04c0f101030001d540c004400144080e280d00009502c003d4886985880c00ca41001d80050a00c010030b201d400145015840745400fa2800303084086003040ca00242440aa42101d003040200070040b02080f001c2019401d0101c2140e50110f010f46c43c5070341d620b03012410024400d0008018000d80180381c141d06845202842c0101d907046480d11a0740b0306d903402e9442210301c51040904d4820700c90001001f0075401c0c0c1c49480000d0035030914005207145960ac403419a400720040301060011402403280000242040c3c46142056030300440c81c0c00d0034441155910034051144910890310b400848090522a41010031141c102508441e22aa01c80c900601a62011140100161 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 199800287 1250 199799037 199799051
    0x7030f0812040c26190204020f0d02070204051501020a030e012a060b0d050703031b0804031b050301050c0909060312131401030c05040b16020312040603050603060106201002040603060801 82
    0x2c520102044e146180242c0181018038000110704010a55a0000d80c2e01c10750902105901c992200018151007108010041e0781c0c14061041004494025049800d192031010503040c0c0e030790300007a4100842d509420031040764a0480012581c59000e10800341d6001820680011440000308000b40024840d10040c007000e000071b42844a000e40040003d0420360203140c1c01c0000c240108010800310f400b002980b0b0740c064003070315020420f6000760300403240c0201420700c0b04641008030f807400c1e0240c0341c101d0090084d420f003008901c15900a401d5024071034444000801c5440d41c0421001c410300d24200080c80e21030103045440c00001d511032180302c0749070710002462102e942c4207100d0070544030002c4d140c4608260414030a0641b58024a0251110481e8180c1c01c0015075410440c02d40070301080340a150f40c40d400c0c1480101525006070840b8025070040006202082e00100031550754001c050002c0e041c441c00e042003501e0b109420034108061071000030045110741e495005001540c4054009004203 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 199801537 1250 199800287 199800329
    0x4111917040c050d030e0a030c14010f1e02150a201306030c030209040e06070906030209030303151507050d081f050907020a020405191b0207030f0812040c 68
    0xc0004460007006030400c00002e0045240940d02108981d0007454100742e1529280d000c901c2c107182e1078000355100c08056504200b0300c0d18100c02e03800d5400303003840d05080c00c0e01640c0e0041c0c01000c0034042055a0300c0c0074000d9003100d40c82042040c200740c42e0888016402d00f40903510b000185030b003401c03201c1c1141900e2007241001c1130200844050150b02c503a2440c00f24034001c01200101060407558041503001c10110103507658a010b00e0ba560500c40015240303506042101030a164102d5004d5000d241c018000e8400e07a98011050306d6000300104845811090004002100c0c812051000644004041000c50038014005071083e1200701c01e85408100d0340300c0c0c181c131761011300d4550442190356243c4002804942004440326422580c140129546807516a0001e000c3c1d82007194103006000240308004560321044c0101d00b81e569641101e01e001e1442c140c0007e448090501002c0c120764941403551040022407401c0b01c10032006c20302c8210080c2002c0ca031480c03040e0b400c0d12824201c40d00f5841c0d04644 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 199802787 1250 199801537 199801577
    0x3100218010504030822270b0a03020f041817040608011211120712060e010606050405090f040213110c01110c071404140c030702010e010b0a030f02041119 68
    0x15260407000709400e01c0b0301100940d101390301d0b603140c18215610418001910041e0b1410b150804450f00194841c5c40c04071442c1c603400c803010502c8c500d22402c110442080135890b40c40203141c00b840142c40c0032503115110103a5100c0940d500308020551a01c640400711260748580162080e11426915a800c41e607032941161805118014007401d20490000984080d1030064074400d420030140d025680200e603551030b0b403200d5280404042d40c900e030301c48810020510003072207100050242814402d04090074900030400c0150b005060507210854100820705642e41d042c0401002d0300d00103800e201340d0f01030444014080d04040c02c002055800d1030041e44080128106a42800e48a0300c000c05102e8a062032000e2031184a000258100b95500786c8403401c00a003c20151103107100e1600c0070350328100841c00a0860b40c0c3c7e90526592a45001e5044250755503040c803000449030003180c400e00300042e5000040042c8404076500900343c0c80007503900d003141c0840c0780c1c000345c1c4c24103903c4201420012440c0288 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 199804037 1250 199802787 199802789
    0x6060108072001141806061005040303050a0e0d08070b0f250e0402030103030306030b0708010608010504050402030c040c081005030a0b27010c080a0e030a0f0f0e03100218010504 78
    0x700e5558210090000e4010309400d0158050a00210b0700680c01108194051390503103001c442d400640060540403001005420f401035820394040c100c882c421030008000c0d0140d400300a080080000b0104103880c0308800902c0c4100000744032131112081440c0039030f0240c1c841081240c40707024160000d82202c0e1100d80303141c4103000211003901100000300a01da0f03041d0343d1250300ca040c440081c4900c0d0894440c0d02c06540a18826200000c00c036080d405c2c441c26541300100001d08100010340144a240e60040030241100c070f041e0b034007041a0700d45100080c28000d90248542c0c10501e000c030021035a9900c1039086000b1410031490001043d103840a0644902240c500a03101480d003002084884607c80422904d420581002d01c0d8601c050704000d0303096030303482540f0400045000d170901c10030003000c0c4140d40039214088011403070200f0a26000c1c045880c0303807503d0000e21a01d180074520050040f0100e01c0c040c60f008081e180009405d452420003500562100030541c2041c00350005c495004000302c0e4 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 199805287 1250 199804037 199804051
    0xc031312030e0906060d050408090a08030f0a0c0804030506090718020702010212030408041a0915070b04020f0111010c091e060c060f09140c09070819050c1209070806060108 76
    0x1081d22140d62050000c03c240c00f13446190840020032072922514114401d041c0181c0c490b4041d0fa95506001040110b040d480350401581c80d04200f201c0b0380031900070000c0b180c5004441c02d0050300c1e25421308181d23005000d654005040e0b03020303a104114010001080c01c1064920410030310340100125940c9038101d00501b08001e015034084681d43e00030038840700103180e10510a000e25440c050311441c084558a4100d258a5420800800d0082d800d04d0514504a00e48215142d103900b403207107a885841404001034000380c0a4410141c80c00081d901c500b54900e642c0030750800901c86910541001000d001507803107a041000d80403070f000e0251503181d5103c0c41c110380c900d86c1d07481c5000b03e00fa01d4000c0108010882c40b06420703554000030000072545034100110a444c00050b10301d8030f20f0300c0305001408e08010501002c01441c5800c0100509849207608000e81e00110009020b03a02e1101401e2903100b01407440243c2c20320710081083d0f409000406100f0364410800352046502e4440054030710b003000362000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 199806537 1250 199805287 199805297
    0x80c0606010917150907091121150402160b07090501020609340801090305030601080a0504050d110c15191107060c02011b0b10060203030c0f130b0c03131203 69
    0x104000152208138181c01401d10f10543c1d092542d540d11072000c58915070035003076400702d010801040900750722005145401070311092212924000d15481d16034185540340e01d11541d40490414100341011804100c6240e0106038103195040c080d401604182161003076a0051283d0000141e82401c00300d184204918140700440382c1400e102e052103044440c00900280702c01e00c400000840000034010411080d0094907056034a003008000100781c40401000710341c2540c2440103120009800140328862486a403406502c1010002d2682d81000c9a07000b02a84c401d0700000102d0000714100d0050130202c0a5000200307050a1242040d250b41a070000110038a80002d10300700305c0f079809900c070845c21a10514040715001c9418003540c2801c00000b13001d4800c036242c4401c1043c611910000403015041900080d070841c60329481016052180c0300204202c00404038401112031040d40d00000984810302039070b91121035030250160381340c0020101c3c20f1411401e000010302c000341800541c0030142c241e5a4 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 199807787 1250 199806537 199806553
    0xf0d110a0b0c0c0d050d0605040c09060509011709070501030e060708010303140d0f09060e031614070810020304020a05100804030c170a1805041125080c0606010917 72
    0x60741040490040004280b4041000700201c0800b00380701c102a142059200d07240c407400307406001c1c4110b400c0e603000240110726100d0305440007a0000c513481304488051504a030b541401c480102d84004134117045005402c1c90b0b07010310601088c003140e1001035407401c4c0e9080024107540595a682c4480a40b645801324810702c005001081c820030030040c0c40c000c440c20700b0b0701d4200b0200008044605060808a40c242e54031401c404002d02070050948201881c0000c42c181301e07401c0d11520794040e034030034020040d1049081001c0c0d05002071140b0401401480d05403034007950700e210040065071044404034481c045c00c1501040301d00e8845200c2000c0e80f02d5645894196845030340548440c1d00b651010b45d070325540501c540600b40c111100800b4110b03d0355035002d02c04118a04c1d0600d04500c0c0740c001c42d01c201d0a245984c110320400b203080d161002c01003810b40c4a52804901c210307025100c80c0a0140500e140041c8d01c806594000502a00905080c2e803002c0459964031500030310360007500c0c01c0001640000c40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 199809037 1250 199807787 199807793
    0x90607050f07030f031503061d07080712020a03080301080307030909110327010501080a0b0c0a020303070f030204030506012d140f0a05090f010617070219030e0405090f0d110a 77
    0x313103c408407283c1c02d0001d240c00503815400340c403004960040715015202c0c002000104400b81c03c8030341a90081c0010b240355420041c03883d880b10003d0103190000500c841a44003955a6601c0c81c070b00450b0400300d82e503540c0d61a240c80d03a40b03a6006403402e5002c922a0700c400101c0b9440ba00c00c01c141e40ca07160007002e0460f02ca0b0f03010001080154030344000c2ca01c5150700311445540c028803440e4000c09040004025030a854a80150442c0d4003c0000703122110a00810661503000f100b2a42c2c004071600e41440070752128041503000340207980000e899807140308004a0a141140c0d032400c074203e0f0343c1501c030304002d115000d06124540307a13000b156440c2c40032040b0304c616030415280394441000e0080424520a4441e0003180d0001412070f0903511003440007004000ca9030300f100d001c0c17090507a40801003e5900e44207202070f6540040200320180c0036410528103060500c0b41c1800012481e00510511141c10301e040300c250740718001c501454030b6010317001c82800b183c0e00401c100d1140b82e039480003501c05181c1640f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 199810287 1250 199809037 199809047
    0x90d110613060906020114010e01151101050f1801090f0212071701050a0608120405100311070c031509020d080703090503030c15010506070b0a32090607050f0703 71
    0x10011038200c401444100c0d0712401010340c55000d0030319a529480038a1500c00300a0179540c515076113450002d00480140850b40e0702da806a410b60350507082c1620070310714031442268208400700d8210565440c2405102aa84500c0742c000d00811510654070202c004143c029822074060003001004002c46034143c01c014200742006c00c0b8441c040c00251002c05070340e6500400c0c91a544404031446956540812a903144130b44148805040340b20018070780f155001074010458407480c001c0c0d03441003040c01c01c00390038544280c11480220f028440d0751b40d154122071900c03000500c0703107000882d5101d0010400940b0340c0d90601c07560b182107400409000c044855520351701195403000744254100070b9815008551790b20304000070400400200001c1c008444407005e80e140b041c0301a0000751162504000c4140810130382c41016400183c0c0100001d034021202c90035144584040030403413415007240ea0b020302c43c4101d1406081c82503c0040540e003240e500d901c0b04441c148140440403142510500c54140428811 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 199811537 1250 199810287 199810313
    0x901080a06080d020c150304020a090504020a051017070503060604140604030b0f04050d1b0b060d02031905010b0f060a0f05040918140a0309150c0f03020f060c090d 72
    0x103400154054858244504040c040d40030480581d100900f1740c40c00303050400b01030400c494902d1500d4107504003640000e000400c248260f0661070303203403004501035540314280344005000080240014442d103500240c40d450510620803205000c5c00c000907207960041c01128415100104000e25003418030038030020204043c0d100c19000701c13043c840400000d403c4020070b4010b0394000380c039502d00d01e07003440c00c545040c454a88800400c0043c1c41d00303c40074155423040f442460352140341c3c00290303078070701003c0f40e851b07102000b01039070500c200a480000c40340d195103600071060281e0000e1144210400074080c00703000948803140c1181c02000840104c601c50a0030341d99a03076980c5400c40c07500703681d03c1414044c1d0300d040001d14040801ca0401030f0421041e00200e900d10b1050b000500380c41c207240d440103802d00555100701c11600c0c4000203e0b081d0144185000c6c00020340c400540130b107401c0c640c100250395081c0d042e92244144213240102c0c0c29041810180c4503a40d500a090b02c42141a41e41d6101040700c207 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 199812787 1250 199811537 199811551
    0xa030b1801060b0a031b030b09010512100501030b060a061b0602070c080a030e010905030619020d0b0312030105040c090b0d021e0705060609061504050d0f0218041b0605090108 77
    0xe5008003084514016000f0100d024860341c000c80c00c1100d100024200d08818807206d014185440d2000c10103454200c074450460f13000b101c0c42807951541030803003428001c0318240054000d140800100c104a0800841c030702441040d1040c40b0b0b20380c2c403040c1c00e5858296980d51681400040040c10000039025001041018031440030008401c0da40c440e00ca18105040f0000c80100781e40f2201c54a9950b84021300741c005040840003444a803c02000c01c94003864000440c602c00d0b5000140a18410b0301d03070300010850301e0701508503102c3d04c0d100004135109410038000c040c07040e8140f40b00b001c1c1461040c1a0f40007540e0a01c0310391403406c410b02c0c603101c00a51110580c0c0c4503228040030301d4807081078030801030092240244098025403902800308085080000d044c54481e034040c0078500e00f00d0b1100c20644003a00d1058401c161100d07094285501d030000020002075000454804110100c90b06210280c00b652140710f091200640c02d03c003802c40041c0c18019200001c0c030911070802c5540c860100c071900101 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 199814037 1250 199812787 199812791
    0xb060303090a1418090606030111090d0f02030f25051005030a09030e120d180b0708030a0204120f15140f130b07270e040f060612030c0b060a030b1801 66
    0x2c5001c0208213007000f2038144109401220801025040c00e009021414040c02031507864a0100c0002510603044118050034a1002c00361100840d10108042d81c4d88091600489039078011455540c4a03d0302003512040901c24810380001d002c0c1010314031344080ca1540e880b1103046503110804400186491003080d020800d1000a44110392941407050006403210700192100e244034040181001d0820700c0e95000d60030b401d0306c0800c00020500c0c2030308d84941d8040b400380d50f01e4a40c03004400103401682c2100044542c0d40e4107000c00c0002500c0b100c280b05114440c18442d12010688800803039040d041314103e01c440080000340c10744400e20509920204107a2001118599502c846441c20300c2218000c0c081a120540e580d0520701407034085c044646000c1144412600b0142d10325084600a003004250b581c42900940402506404c000b0151107010740311600d9410a040081016640a00c10f54050321210003041507801c00e004210141c076005a2030b0811074880741e580c20b18140c0c2030300344c08103195 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 199815287 1250 199814037 199814059
    0x10c030e2e14030114060d110a030c0f02070605030601110309090a0e0f0304180209040f0f0606090e01050604031202030f070317010e1b03060102190605060102070e10090b0f0301050703090b060303090a14 89
    0x100d23805d0040c080784140c59030001568604158040c00001401c04d103d01035500480c401c00c00a45e02600312540a1001e18142c01614a0000136030b1441c00f4400041d81e102001d181009003a0245911000d5503032074001c00c03a060f9a50440040d80c480c072580c00b41603041440104d072002070031020b8000b811070343e02c083c0c07001900c080e410009a0450b0391420402c0d0089841e90010003041d60b0200815015080c40e10921a20707515100004000744182e1100a19140e643d6810000845c020b0041c0c40c644444011906e948020034980104002c00300450ba04c40c4018400021941c0ca020441a5104178607210b005242c1c3c400380b80840f16540c000a0045045204094401c103d50090884200b5254840c500100e036030f0800b100064201901c58010501e510b14027420802002e241110341002c44480c03440001750900c015010510300340e0015035054141d030904080c44025076240e8807404801d8043d11003a441d640f1140105600da02c6401d0183d0b510225100c0300340f001d07100300c00c0b8003a44100010081c0141e0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 199816537 1250 199815287 199815311
    0x1150806100c0812010513060501021509070305030418060905010b1605070902160b0601020109080d090c030f080309010609020c030a1d0901230609010c030e2e14030114060d 76
    0x80c1d0b01031422410000c815200410550a03d040b1480ea402c40b950b805104103809c040000350344440c20b4645200c00101c41000c6a00341c4800e000705004ac40e08403068036600d586910544041c080c20030180c440c424070780b8000140212051107800c0c1640d0f5008006442c010081c5c031300e03002c00c400b003020642d003d0203810000a01011148010f10b403618607024800102503250920b46008000241141d0559040c09100000620303080112001030f104401e001601e1800c50070314241c585207a4000400c210003500101040c0315425002c2c40c07140300c19074001d205441d1039880340300907409480e001ea070030756105001c03079815903025401c18a10000e02c136040103020300010001440c0b9031003e074003100c511030030300c0e40d13044031030712014030104211505882d42d41c5040c181400080c03e03102c02c00b50140070032200c10030801d030316070720710500b06074403206007140280380340b40d1b0007111307642d01e549012840200d5007864041d02c0c0b040e15541a40d040780c664624880c104041d00c2c00b07103c0340f0340c80700c0300898446940d060300010b0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 199817787 1250 199816537 199816553
    0x50d0e070f030b0c031302060f0c0303040f061a1003111317060a02190c020d12031a030105040c09240608010f090207050a02040f0204080a05031201150806100c 70
    0x2848400904003109255041c01e4000d040060031150144c0e000300108030300e001c0068080c1c1506503048d81ea083c2c3d2a140c0075a10300883c007480212008901000040c002400715068076421403501070710301005484e11500301d5402142002c501d0700d40103000d00004240d03060099114156188643c140c0c14580b0f2004101c3c15050707611034000c001b01c0305d94001c40300c8000008014140d0f000c80c0800c000c5142400010800b24400e14080d42d400c00c025030340c8030950031511145400160150b00240c0310020f41c1f50600058003412600d40081e10039030324500043d9483c60305004680c001c94005c41c00d002c540307003010b15680141c01145007641080c02420416007180707140441c410014907040d502e102007541090342d00d003d02e0400c3e81c0189802401071041034040b91003c00c0d19480f42c0d42c112400101c4070106100344c4068000d80e8000c02017030041c40c2c01c05e0203001e4040000e0008250326100c400d0140e0700c4151000d80e4401d000030003000034840c640081d4150800345440e0f0180216410000201c40c82581d031800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 199819037 1250 199817787 199817789
    0x106050919060b0a021018080c01050a2004030f021816020706050c03181906031b050301120f050307081b0d0f0f0302090a03080a0f020c030616050d0e07 67
    0x40764401d0800c03503114280180314000150420707900941c504005190700964680c1001e17031018185a0710f900e400b804143c46101101e50551049015071140410403415000341070486500c1181410419481c02c20600c0550150103056440308042c00c050079a159070380b01411165080343c02c5601403114495008850018a105140d1458a84240c0070703403450003070400d060303a84030b4424041c1c240442100c86d000031003540c000843d040f8000110141d1030000500c01c2e040481c08100407030900700080703030a0342c5c1900b1002d040c60220b84450b4064103407031400c5800d44400d21405250180c003480390710001c6e0040021000c01402071044038100700c60b80d01c480d051075014058043c0400c555640c00c03448800180215a64007a040c10001c0e81c0c0140d02d40c010346901d0707061949604240d03001440010b00e6079012000b0b03001d550881d0145440341000e9801078013050030161800058440c001505501c1c0c900054007902c075614100120490f15458203003a40c140c0c0010002c0c1c031300103403200d07801240e0880030000c0308 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 199820143 1106 199819037 199819051
    0x210050c07090f1a15030721050f061801060203030c0702030a050304080a0b0115090308030717100618140607030228110906011205060301060509 64
    0x1401c0ca86150002202c0c2c9240000440c1c0511040d40305411100501c1801108001060b0400a58105982100907500b00420001b016284620800141c6111240b5034400e0008050100016608100c03103000000311200100203152401064540c1d280040d0b1005031103e5042c840000d4503440f00800070545000b0018140302192000c0040d12085e541210039a500c1c1c5072140d4800d91505413084050340d1101e101d100210352845080907201c40e503455511407000852450390b031140183c0004103018140458080007406082d920901c41e8401c00700d0300c440f002d00605255002c0c040f010203480d01c145411540c2e07420301030740341510400a80803008550281d214900c40c0340491400b21961401c282c099914580c148801e0803001102c05154070a81829250407a2141071020840080310010300159081d400c0da00704502d04e9000f107030401d8001c0d0001c1011a2120302094070600d09132411 = true := by decide +kernel

theorem cover : BRFrame.Cov 199640287 199820143 := by
  have h0 := BRFrame.cov_init 199640287
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 199640287 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 199640287 ≤ n) (h2 : n < 199820143) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
