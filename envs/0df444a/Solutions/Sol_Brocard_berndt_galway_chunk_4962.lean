-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4962
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:17:55.466153+00:00
-- url     : https://prove2.me/submissions/102b233d-4a72-47a2-a580-eaa057ef1a6a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 892266187 ≤ n < 892446043 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 892267437 1250 892266187 892266203
    0x304020d02010309020904081908011805071106011d09010507020c0f01090b040f2c0103030e06040312080f060d05030d0504020a080303040c030b2202121c050d0c02010c0c 75
    0x189032004034040c00418100940000741c6c1c80511040002410107000100f402100300c0100300050710044810709400d115140a040760301050305001c40c0150b00c00c98015a05242c1a501021282c1c1d01c1c0789408020f0f8818055035107031302d5071410506202072666401410b05e20080c8960304142130000c0d07840d4414030466210300d208201e8900d03d80e0080c030401004080c0c04031840d445030707514805840242403501c01c0050380d01c42d80701c90404005d05141520a064102120510184d085440464404a544198503007001d01044040003190301ea6040c60f10002e02565403030383d1450100c02d0b15191000182016024000c4504903000190f00441a81d2000da1715010001d81c41d86c0c1c038000901e00c4442a805800d042c04000b05010512525025450580c3d0050b1070310011a111440b01640240d2020603200c8a03008909a01006160003590181141c1c2c841c4200c07140702d150f48040035001e030f190001c98804207100207100d00c1c1801c1c2c43e004203561910580020030440041120280c43d02e0300d1083c0c0140002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 892268687 1250 892267437 892267459
    0x12050709110d0c05190525031b08211503070f0b131d10140a0504020c010b030d03060317120c0c070f03080d1b050906090a0806130c090b010203030402 66
    0x15120300c0640d017450424001e07a440310400f488010741a640300076a40415000c8000700308944c100b42090700c01a565041d543e01c00c040e10907800000c001c0c1850041110f02540c104054074240a14840e030181203416490a001c40782031a0420048500c00603071070f0350098109400800a100c403402c00d035021129118582c0756945003607030260043c102c45170082e01420be02d1540d4082260340050280b8441c1003180d2003101e0083d01d440f80054046a011445039201c42c85010920907420583c001d082a9002c0c080081001302c21080001d00302400318494200003680e9080801c144001e04113042c10f0b850600310203e1030041e8004901500200091002050120004201c111040100055002441e054403034124840c0c80c2d1504503c40d9001e2228681d01e207043c894140703210074081540502d22281501c0d01454481131100313003d0182c110200d00ba074480442240050f03400014812107210f1a1b0088040c01001154a401c00704600c8507008045518500b040380e42c0e1716600001205c0e00b09404a404503000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 892269937 1250 892268687 892268711
    0xa020f041a1519030e1e0114190c081006030c02030d0504060b100e01092904080c01170709060e211b0414190902030712050709110d 58
    0x5100c04035203504640714250b81d40d09110b08501401c2440340110b502ca40000d0410340c02c0342584d0603038007074940c107070003505100c00840e03d0184d8003015001c01000100f41001c20890070131443e90100c6d0301101c5060943c0e151280c1031050301c1074210088031814070501500301012054460b070000c0c000c44061690312101440014020000d480205080f4801488549800e2501001402038895250b020341c0d1204c0600c1c80c2c3c180560158005240180c0d1941035841c40d112600c80540c20b20301680d501007100c16902941c450f0014010009044200002d002c68030103040018020303024080ca4003004c20504060107411a804620b1004460042ca080100780f4a84030001c1c1d01c1d2252018040882101001181e0b04a0004100d041c43c110199002e5045081c1ca00140403c0d00c55000c02d43c082c41103100c0001d90300340050800302084828031240020503141c0b56010a15001c0650840350094645a0b00b0074108107003040400f01030515480c042c80741c1da80b06030926a1034010f111800c04126100c2c0b81c400c80d1 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 892271187 1250 892269937 892269971
    0x30c050f090d1a090a020a12050a1203060503100605030c0a03170c160e070e0a1d0c0d02070f140a0c0501030c1713050f0c091b0415050405030d020a020f04 68
    0x4603e809203015000f401d01021907960740690030400c03030041741c01000c0011020b41400075010400d80001c041c104c8404140e40d84500c0d40100c038003940505580c0c00012440c0e4408010300490b412401c0b00002e811410502014540070001400c207108604d541002c0c80000c02000114907502c80032104551a94203070703900507080c40c07403080b26001c2040c000840003e07103000701c0c5045801000c0c2502c80c0e0310b002c407501c070a019224440b0b0180e407002c40301c0108030002c620351005540c2d51060500d270121b801e004650160b00180c3c0d00c00320b800d540340818101500305000050310300c000410003000c010a40c40505540308030042d10140325141c141640da114400303986009031150051b04401000c1141c107450700d0a5042d0072942403000680d59481005600d0088020010f10903950034001050074902c1e44e64944201000c854541488040c2103090100050301e4a074030861f580804855120f1a841d50305160902d441c00c521201c0103011540701ca6410009611a242d2000d400142034030003140d0001d08002c0c0700c007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 892272437 1250 892271187 892271213
    0x20703030933030207062307021203061210060b0909090c030a0b1906030309060224010308280f0f020606090601030f0b0a1820040e070e0d050d030c050f090d 69
    0x81b400d8140383d034800b190040e0801511a0079060184040755484008040341d0f20521031840f100c001d18100007164040c0f406807501c0c1d420712900003c44400461580700c950645d949503000500c050804030385103400d0b240000445510800080081107142c40c0c175000207940e40401d100103414019010041000c1c51440c140001041582c0d4406100c11592490024614100c910400005000d03c80d01d4000c0d00707000201e1044204a07070a02610264255200d03140540d10409045015800c01c0300c03113400d0201c041e210300040341482d480340052204a840d000d01010461070700003086400507003c100503540c4000d003c0303400020a20300000d010f54286261030041180c039000715072100c030341440022a044014041e05908400c001d051003d020281058003050140c00c110407a40c0409003c180b042110400754140c1c8400c1034a04480401e80300d0700403034490700e0800c10a84050b08103d81c00303441c540d054020340a012980c0d24040e80b60031901d0715100c00d20700480700703264401e001410081060207808400e0030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 892273687 1250 892272437 892272443
    0x2060a0507052505210702040b01020a050601080f0601051813060e0a0507090e0c1806011206122102030d0f020c070f0e1012080c120307020703030933030207 69
    0x41500f40034000003504511000c0101c44900ca110304e150210040b010140f84082e811101301820046030b0b50800010749240c1680904600c030342400078020404c100000760017000704002034024407168241d500d060100503000b550003114003440c031a9a04214041c1650700000f42119600c40b5403042c90001e0142141d560402154410042c00750103004020980c3c3c0201d40007180d04200301c8801c85940794844090702840c96000c00c00388040ba0900000c0b24956034410700504d4003660280d540032a010480308103420600484c0034807205081000418844190032600500140781c100c5172000000303589201e41031103c08141d484a0364501c0401c429019182040c4241c000c3d00c142d10b4231040080715254551155042c0380c075607080071aaa01290300710001c10303240030580d414040100c1c2d88dd8080c980d4001414400d141c4120000c0c80d0391121064083c40c085e984690140402c03074510300300240725000c6a00f2044501c0000c145140610000c226003041040070036415817800824250240c0080c06110009 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 892274937 1250 892273687 892273717
    0xc0b0406030b09010f031a0a0b04050408030f060117012603030c0c1204030302070b07150507080a0c0311070b1b03010f210c03080f0405150706051602060a050705 71
    0x400c40c2505600a4400c281d4156060380e1180c2c1e81d0400c0140c000120b101c043c0540c00007881c500a25945001c0303c95010440c5600031814095a00101e03044880803101980c94200100c18801032410107240305410041c00d2a2203000100260300d0340084142c103228255400b03c1400350341a0807907600008050641106041d05d4503440d080302d90b11031582c4030040140160040d10050841d5001c01403d6400f03803030b019401800340600308001c03900641d211100584149464140c481c4032020389025051140d4004e540c0c102660400d1000c03107041d50511800c180905080c028030142c0301c0c1200c0c042d500015080034a000c020748541003490100c3d07140c0c02038801d95070000400480c241c0719905200d4121084007040c441913104540e0700c10708500e90100000d04806134840300f000814410700190101101c10020b0707600c0c00f13969500054110f0104a1904407511001c12810103020451007a290f0001740d00d01e0035224841c01000007510341e04014046103070b01d99544041112244120243d8400f00070b2504c00c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 892276187 1250 892274937 892274939
    0x60d0b0c03130c0e04110901180c05091c141209060a090e010e0f150607170d0207060608010e01060510050a14030702011e0605010e0108370b040902060d05040c0b04 72
    0x4944082c131400c03501503414440016070305801e410b19400c080d04892920701c1c98a82601010b00d0354010700a403488a008200003844100308582c0d403410f11803010549004275241d54081c500e01452081032424202803960030100150208030015801c407044443d04440d11541c4828424055404140640208182d06801c01c0041052104009281d010b1890084d00144c41c1d41c40a18002a00c44001201a00002c0074007180f000103c02281380c84001031b402c5485c9081403d50040c8000b00d070030051003034403134545032901040f882c6030030300c51000034001e81002841900e003088045014070315400c0b110410003100003040c10303a251240a00c04076107842c503520507607030303003407100009010304400714010181030005940711011034900e200301e41c100d0783c2c103840e01120704129100640d00b4a000408410004004040180300c8080c442082010301d0010100d00024006000f001000c95094442050140b0b15010012001d699403000380c40c03241801802c003040503907541c03901042030b42090b072040d04610300101d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 892277437 1250 892276187 892276199
    0x10121509210206060d0f0f0501091707061802031f020702040603121d150a0905060a180b070b130515070e0f0d1a06061b030a08060d0b0c03130c 63
    0x724221000c072056007180c001d40c988000704000d411041034028800215a4101400100c048244120b45402040002032050b0b40e911782d241d140d0104145809901c90002d041c004000240c4141040c5901c042c0c1c0300115941940d010a5035400f410840c0c0d8040501c1034640c1c604000c081d01216a0b003607000c2c00900032580e8916143e410001e40c58072010101c1c07030303c7c024545010100b0041429020008055600c42d07510106205403035800807900104101b5122004241c0c1e81b0380e000203014a07005941d030502c0c0b00840695038544021190080502d0007003c000c070101051044010366000160003c0141c1609094a003942c40c0140000d07962011541e040c0400860b00e80049400e05031141c1038035020703103014a174020081200401d5600401e1070104150010f050302c1c2d1048095445a00640b5940c5803400303c0070f11090501203118000403d62002400d010440d0303100412940100082e5140c110401c160303a01c0c610b25900040006000768404000038410b01c0384100a221000d40188086098940b10300c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 892278687 1250 892277437 892277483
    0x7051207080d0c1709101817060a0e0304080a021e0319050d02190b181c030c0306140909030904060305030c01060605070206030f070e0a0b1210121509 66
    0x101504e000d081c00c041401c9528500046407828070b030041002030240c00f0081c090b188500d1241441514050103440468440b809245c1ca407580c0800780010310441c0760120402c0103030b4200c0922000302d504140004c2021103000600051206e40c111952074044140030420a804190503034210f61600c200300703501c07400c1208442081402c500074010b5030514075400000f666241141855000488902000400850340542c02c0c16013005402000000407401c00d00b030189401680044050403011902c1e000c0040c0390144181201d0310400d04080c8441d03807810119903001c8400c400a00d008202c0c0701e0000e64030340000c3c81281c0442a00a2003044426201c4c10400d0b500d40052414007510740ca8003c000c103103980036000341d5035141da00406452460b5104044015181c0003e000c0f175040c0610002941c50654400b0294400750a902d85c2131a01c591411030750494400014049403010040810240700712442e450310314041c0340d0400d07950741c40c110349c001345072008110100002d40000541d5002c1d0a460b01d000e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 892279937 1250 892278687 892278707
    0x3412020a030914030c0a0312021e0d0b0d0b1306060b0a0905010e040203010f120311100c0f0806102111070302160815060103090c060201270507051207080d 68
    0x603c05030700310f04110500c510740d04c1c4500403e40392a91b01c00e01d140e40000c0e1144175210a84103d550300582048030b89007a44520025195410490040c00b150580c1082290321031001400f104030703040d190070109602c81d4150180301130001400b54244404810901800e9000900201465007144e030355800c0c1e20070000e080140901405000034102d0200500901c1d2500030741c1d068486100205140e240f81c8160915502c00801c1c045041c040d86a401d07001501c001c0c418068050881c49020034248060382c00100f503c0f07654480f007010b0004007403d11196459500340d07484880f8441c2011108169006141c0c0001110405540812410136203404d4403000d5160240199512035000c881c4442415004545880428040c0010b80e61040012040c0910310340f00e0580c11003818100041c83c511261140344800c00260810310140c0e44688600110207003e1507189000d4010f100b03038844061469270f034035032290038501c14544154150314003041600000d00c00c0c80000d0410a00f1192a0440704002401c103840d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 892281187 1250 892279937 892279943
    0x80a0b03160915150e0d080f071505041203230c0d050c030c0a051303151505040b01081b0f070b010602120c031608090301090f0b3412020a0309 63
    0xa001d554055420030081c188152100080c010316071000c1c060044460705c040031100c81c1c0c448683c0c1380c11004903903400d006040510f1201074031562800503007010f460b0801c4942e03020000034603000c100008950b076201481d084240c00d190100b81c81d51541c41c400c1850005a00143d811000d61041c012001c40c501c0080c01c042c0400328043c040ea40da200138007901404111401603c10f981004146000c0348504003d00d01c040700448409251620b07038846000c00c0d40d80c1c1301440e1043c3d96405e80a591407072a050440010b10b000c590a0040c280d004000800c4401e0143c11001601002c1500c54207100412080d50201041c0907d002d84905850a01c3c00c45840c00b03124600240c01200480540203a400089983c2c42005900540c5040d0414501041d4415400700944403c3d0b4140180700040d90f080c080c220307220b4051603c02c03400c0400f87c2042100c0300300140003103060004500b410344800000000e0004020070581008210300c02115098413107a00310108100b07001e00c001603a00030b039500760b03100403d500c0c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 892282437 1250 892281187 892281191
    0x31b0304231905061912060914060405130b0402060d020a080a0614061206041e0e010b040b1c082a0c1005040b0a05090904030512090c10080a0b031609 66
    0x390150b94401d40602a005113078101004000681da0000d10712613074a60340d000c43c1380404440e22842041c8048031580d800c8018883d4a0f114210725510212040d940c21520448041200341880324000440350402c0c0c8008190811240000341035590390410340349805421001990750740ca9213030005254900072200a03c2880ca00000403840e075040b0041101e80c00c50242400c0c0c41c0c6042103000c80800d11005041c01d03441901c8007207a250b03c281100081704180c0204601140c42d1280c13690700307403c5d40c01070049507000f540b41154504035070b0303110344100a490080945480c1401a28181407905100310784240040c010407090303d015040f4843c040103540e40744802503500c020100d40c108680b21240300241c0000403802d00c02405101c0311003004001644090510354500700c00000031541040301200c0c20f0300800c1021907101030000c0034018885c3c0c04840c00e00a00442110702002909580c0b56000010030084d90100142d134441c1e0551003c0a2410014100c400100500000500222481c0911540c4038 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 892283687 1250 892282437 892282459
    0x803090f03030c370305160518100c1e021c0b0106080601050d0e100b0a0b03040f020607230c19030803040c0f0605032502031b030423 59
    0x24002005032800b030105011100d2602451522504050804220340c013070741d40c4c0205882000b110200341010300c103182620302050a1400400c1030b40c000c25003030f40f05c82c01c0c000708002e5480c1450300c070001a0160b4108803009000d030302c100c0304111154490380d80f0041c01c02c480301c0c41c1043d0b09007244446010840c400c82d544d200c0c841350303614108580b081c003c0e030040ca0020f02c0d400501400b4000d0a00035400035040c9031007801c04c0818030480003562060381c48100c09800498510b8850440c5019070001400b0544074500740034038000500031148002000030306583c228032100c5045658120071150403d0301b2030081c001a203100501c0c422503824a041494143c452480c0c686400e08241007104100c2e0203088000c0c0307070a4903603181c103955a40010300403948205142c101049a4400c555548041c01c641c3d0b1381c050312840c09030307404442c0001c503c50780040700707410a0388490610740c004101c8404c1003056110b0600340d901600080e146011f0f9800c500c0702c001030860514030307280001000b50121041120715031180 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 892284937 1250 892283687 892283713
    0xf21071d10031110020f1603021509030a1101091502010f0c140a11010207080c0f0c090c04060c1703090309041b0c120c1a0103020306090f03030a0b0a0e04080309 71
    0x240c605120040030401010b00020007454088100801c1c50742d94010b61b5051161a0002401c100d000140c207038214405480500650410105c04521108540707400ca1400da481400641e840d8104c04006103844c0c500440490325034400d251040040c207404401481c1c0c040b0040d8040e0107401552021064580b404055010852088560540f100d07402c8803c1c5252034030030355003141d03600c0303030344d080d5400070340d0200965800070b40210010a0a54810000b6040c0200c01034201070620002d40707116445400f55001f4001c0402d0b034181103e013164000c4c10408501c04040c42c0000d03d10b6028007104810388070100811100071404030080407021001c40d0100245080d0702200b01140c8110f080e1103001610004451000500040390140400d01d5800e01c2070000d015a691144a40c0000d00484200f47c2504010011801c041100a420030324840203460b5000b0070745102580c1e400000d024500c015114444c040c556200c0c0c4020304040c0002100b08180c502d803a05001d1540d40c03041e9a2202c95125400b184004 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 892286187 1250 892284937 892284961
    0x6130e0f0906131203180f080304030f210509160308130902071509031205010b1b030a080712060807090e0d0504030c12080408010203091e0106050f21071d 68
    0x60144d0004a401200450481c2240201486117124129242c04218034000c100305072001b01e182c2d4481d9804c0d40d641d14180c50004c0040b002c450032401400302c078006010401d40c258107141c020391040703417001449540d250802da284c2110010410314884401d503001c81404102d100070a0744407000c001c010902c0d03a568070000200c3c80744d801d018040c0580300e1030304002c41101b030304000401406890802000c208860f101c0041305c4080c1d01040403d80009001221442007c00a481c0c5903101c0000d035050034189140901560401080541085004201c001250781e00703500c404060000602150f40c12030300d0340c0c44a0003c1107460b0b06161180b18440c00c402d5098800d50444094a034000f07000d5107042d2420ba03084060103410320040313903050414440401c05941c00d2025501c03a28407000200224040d8440f01030781c46c11480800721036a41030081c244655107815103203d05070902560f90303844030148000040b21101d4031180f526082e00030580c001402c00f200301034003104c54000703280b13840c0307103407551030407406 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 892287437 1250 892286187 892286221
    0x9140109180e012403060506040e030d061d010b0703030e030d02070309080637090602120a0b060901090b0f04030f030909140f01120f0c0611060a02070201080606130e0f0906 76
    0x1520054030320500c0011b10a402150700960040d001241d1208602541410743e00112051190135541d09002c0204403400e500e1035503802824440745503194103050a5071002d1107400c001605040c3ca400e41c004001100300222040310560440c21502c4540d2450700410f8026284540c044034803a8501041e44010b103c00f01c2104244210350f000c5ea50070354480d0050a16100c0050041c00a03510031644020410302c1c001094151540b5038106054a00343c5964030846903184216070207a4000e100303500c1a80d030400f2202c016200129071882c1c070740f595580350104901c240d0b00001c0107413040103c600c00f0541c010342c0484c25140038081c1401218007401c10002104000c60b81c00d01c40250003001002520351002407040c070b00707000fa1900c40040181d911441c0c2180d6040d800030307001422001ca000e4980308284003150f0040b9661109616280607900002c00b000d0024203401c1c0308500004104030011480c1e110000100140050030b000c42c64442407807034110100311075449260207850f0010300303d113084481d080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 892288687 1250 892287437 892287491
    0xe06090606150903031b0d0906020303060d060603060f05040b07021605010c020102150c181207050f1c03020c09070806151803010203100602120a09140109180e01 71
    0xc5541d41d540000c020003a0031010211030500800c1040300c0b1203807000d200030007503044801c60b4040c5c140302c400d0200d860b2804494a00c02003240c0340f8400c1c80030316404000c4070307001001120200c0d8054402e0038400e00a081561000340742901d44a60f0007031aa00300d8114500c102c0c0100050a01640c0f80401030361944445911182d400740c00303003400d001e90340c000c84600ca0900d0041c8111080f000d40da040400c1728000a880710482080c010585085480300c2d6040070b0180c8600341d50400081c41c41d025405e582c2e00980c000c0ba0b20503201030409071182d4403107500350070f50840301c0c1c41590f500096504001e52a6445180d6050241d1880800540070034040c405060084401038100d81d00c0961801030140c082e004140844900e198210909140f90340900240d4051143c90200c20285031815030040d02e4402c80079202e401c0f652040c80300c030003082d4000801c44101c0d08601e107541c13190320344840106d0b800109600046210201d07410103400a14071076021030080c45814000b0481e00024040a40c818485041c4c0c0d0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 892289937 1250 892288687 892288693
    0xa1a130c080c070b13080f1602030609030a05040b032805060109150f08040507090903020c031c08041103010207080a2001020f161704060206100915030f0f080408030a030e0609 77
    0x45584000d5254094a045006da10040d04140c200105604503902258800c1d145010152029040d454144101a00260400c0c001d514000b0400c5003d4810b010741d10a040003020080001100ea010fa542c542100b2031411030b0803440160781e020f07003c00a2100381d078154002040e1020100c2c149402c1b0042480304043da07140c050714151251411030382984020320480b29405010300c005090710080c05050740540c800e4001e030004114070420304d8a0f0607074a02805070030305648504000d465070400c00c401d8001c1d03000b21401004400c01070100e030183c4200f402c010b026071000180840320302d6000303040000703403007010440400c0e9617100c04c4050300341e01640c500040880008c00003210304205190b00b0050451040381c048000c40c900c01201980c5800c164400710158008030104041010425030107005088110b00810036034a8281d40d02c448010320b0300004040180c070090500034080b260b25200003441d030100426980300e8464484584a4100764401c1c00480d0514119003010100030030281d100704c01860007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 892291187 1250 892289937 892289941
    0xf09050108160c050d0f020105060612010e040611121f0513020c010b031e16210305090a0609050310021602060a1b0f020909060405060a1a130c080c070b 67
    0x1030805240e41c0403051080c00441c43c44100043d2080c00302400c101c1040e01d64448010503000081d094600c0101818800c0e50304000003082c2c40212020b4074107403052408a000d555580f413a25000608403d164502000404035515516803403115103244100480c903e28201c00740307283c60004001015016540e03001c3c00f07894001000c00e00540c050600609414008200019031501080c01c009240350541160100c0d80c40000c1040400c02030f0050346100c811042034024540010550390ba45056100d4011041c95603056090610800c1500d2548800130302d544001560307080d003e001031403584544c502038000c0c2006512140340034400d980e10422000d10200c110001b036402c020a1754840039521701440054800c40400c0c0054100f40c1007014400c810040c106c01203030042000a0750000c0c40480c80703510400400002940100d0f41603004040608041fa0726a000c00000540802e03035084283c00101d42c1c4060607140d802c40c2c10541c05500c0075100c1e040c00f515841c020708181e204090380034000d2514600 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 892292437 1250 892291187 892291201
    0x21602130e280c0b1305030703121d100905030f03090f040f14100306290d05120a0302070b060609010c030e06070816021e0d02120c0d120f09050108 65
    0x402d160803014000225105400381d41c884403445070f2130b0410840181c0118600100a040d210060f0260104070300400c041807555840c520003941281c2e241c02008a10120381c0c4611860180000740c0c1d00000f0f018028900341600c0041000c0d5140c440c0742c1c42803260b4520719585041c0030044036a200b41c0034118000c1c4010b000244006001042a23070366a241d901c03a80b070b030800000e207010030b40103520070a400e5180d24a103050050564010404501c80e0070400b014061400200728814014120300381c50041c1003450500b800c07030900d500001694002c2e900000c61802480d41766005005042c840d101c50055a1104007d0012900410a1a5012905890301d04020a000e100f01041040e8010300310b80c901800d565481c1455045200c1ea004280c138030b40c880008518000000c2d2480010340d5070341d00345a1031600c00155003402c102070044c0c0600c0483d401d82103484018030442c0440e08002e04108849411860507082101100689200003111380d0f51940c203aa118881d03903000c03900141c1d6068410b803941c203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 892293687 1250 892292437 892292473
    0x7090807050d021306060507150b0a180b0a14011b11120102040b0a050c1005060f0d060b03011103060a1e061218050f0111070b040305031801021602130e 67
    0x81e4040e64403060081c9144d443c10b43d58080e00c030152030700c0d50303490751904940d262001c02242c0280340d400849040c111b1442d0b294580f060040304403410f40010340e03200b10001c100300005080001e051034020042d890003041c807200940011071280000c1c1e0340c0701a0b0a0381014120880d0102c030000a1001c50750060291041c034000c07040b10070700411030000500c1e0a94440c44600c071a480325030b400c80491000302d6200c00201e01400f115100007034910046c407051400e580003403182c4c1d800d10380b0380d0320a880c810008018018260301580042c5005802000100208102e10b0059003044440310301c03c180d509404640200c0f2201c030700300c040409101120040c2e003480350903918048ac00115030a2203607a40d0f12018003100c007410880007a8091400380001e40c1041011034255091088481441d410030004840000c41c503880259004e500b610703065440f0b4840800900001c0200c07030803090740b0341c0041411038010620f42405400320f071080360040c00c0803105190b894182c9001010014042e0003008020071525984 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 892294937 1250 892293687 892293709
    0x609040204050c040909030216061806050a17040f02090c0c10020304030e060304030c03020c030c0a15170109050a06060806011b230606040e010b06030106140f0c01050604050709080705 81
    0x8150f0b4141042e40b83d044036000c54044100c00d40c0140d03c458600a24500340d0860b00c0003801d00c9143c04401d20340e1041d04400404040e00c1010108440040e900740d00602c07c2800281c0c8001d00c03402c410a50409061000007240710b104180d104000400101c0c2c6d50b0311401c8111480c01d48650081c0c4050960a0109002504010000d400b4000b020030020110340d54440218800e911035103544010708120301b002413a1101c80384a417030003680010301d08a803a960b9001d00e4011502d8803900c0c1e00140c00d2104040341c1c031b00f0566201010705054000081142204d50700004d21441031074100300036056480408031134481e410b84038140400c5804130484000f500880c000c24070180075a0401d0400141180403900b4400601030035403070f1390002c2c4207010440c84c10b8010b07031850510502c028030050540c940010300c0c40c44180302d00c9061007240c401e442c01200015080c0c3d032940245000740e64448118a01d4036020345400c40d509480741d450003001a511500941e1042d00b0707100c03104014400300b4200401e01040e810b072 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 892296187 1250 892294937 892294951
    0x2091f080408030402030703020a0626010807032603090d031401030803130f05120a030510034403040204140c09060a02120a1107060314131a090c01110303060904020405 74
    0x11f40e06000c000340c1c4415001400825056840075859011486841000c0018590444000d440d0f1801000640000900780e41500e400c444080300e000c1080f104031a80c0c400c0d1039141a51441d01004010740c51002050004a00c1c40e41d4400f03000340ea00d140300003000c01c0d609000c002c09007203042c40030400ca01090f4905a524601c1002c0240c0c00150944405290074413202c00c0490b44030000604100559150180c19007000d100815100c0540c290b640b94800c401403e4651006180701c01c0540c040b20000608401541d001c0c40e40e586e40744d81c01032004c0100c42e84103c40c240d018900b0108000f51410303410721a07074411410500030504000c3c0d0b803000c01a241d07211341d83c841304610544100d28101c8100d500109140461034650100e0b20404c255074504141856015105152824240e0042c81c3e520842066010f0520940031004400c01e10f0b02d401e00060342c8405425504190007041072116000079000d828a070240c80d000503e054007030915a407484110755060300108003001103401414543c00164110003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 892297437 1250 892296187 892296193
    0xc020a082a090a09061811030c0a03150e071203091401020303041a1b0d052205060105240a030501140d0c050f120d2a0b043302091f08040803040203 65
    0x520303203107500750941d86c0300301950342e44002c4441c00c00c0d62408000c04640301c00203803040890303103155884100020181032954054961245842051044140210700280109400180c0459181e09004089040d00d0040e00c0100c4201e44121b9495800041940d103d035a00c1b505900480a80c0a07103525500c0300644601190008038401105e40200c042c0070f80340f032034900303000042d452801c8031400050075010180c4840002c41e4500340004140b0101d15903040d03610035a040c40745e4440c5007a02c5451030400d001c000c000f508022561103035041d4141c00980c121000d15010880c1600352000300f124100703948800a1202040e000200464104812180069800104111126180383c40d4150030084103440c0c2c0f0300041d5802e1080b815400b0848140355442480341450710300c4820036902d00c3d40084024001520f0340c11100158900000103200300b090602d005070b030341d600302040c8d03511350301c00b9402074444184120602c0b81c42c80a03815604140724500c03000c030ba89603480c503102c2d5126081298800ba00c140c1e0180 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 892298687 1250 892297437 892297451
    0x60d030c080d240b030c190c060c0f180b270a0807152303310c0e10230d0c0512070e0105100c020a082a090a0906 50
    0x8000380b044218001d480001d20540300d0314a2580f441c0140d4a801c02c0c410007070180f05100e008403c503002d8440800504200009041c15000181c0315002d440400034403050400048142c040e50029883d400c2071407540311003680c090720142c1342540403076a0207200380c5008144140d00300c00420300001000d280050600541980360000030030012000ca420014403070307129002c20040d80341c4201d100b91400e9014030345401400c02004044844401d0000100301541d030110105014070703010788a64008060f0740c00c00d900d80d0b00301c2d440c1040d01086c0190b0103503940c417900b620024610b003450001d03520600100c0000c02d0140d08000c03074000142c1225002e5440740303860038200d01c000d40351080d41140c4180222041038000d8504000c0003490780001c2000340094000180801015000e00180c0381903400c11200c1d00081d111340350040701c1810780100069070010111700005484400429540140946988041d09a2000f2041d2100c60034496072660307041200c0780c0016000c204590b100c903600130b2240c0d02c049a0f503 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 892299937 1250 892298687 892298707
    0xd12060b0301081e0d0c0b0915090d020d0c0b0a1808070305130915210503030415150e0c0706020d15091a030601120c0807090203070e09060d030c08 65
    0x240d0401d803c04121640030003040c000440c181d0300d070701c1840880600104034a0241e07220041a082c1c40c1c1c40010110202c2601054110381c00b41b000340280c0c50141107000c00c0d490100400d40e91420740d20001e8016000702d4520812103403192281844082d00310074040300c141c4481100301d0042a60925840740c0720700381c1c402c504c00107070414018520140203a58081c3c88960311200703548100419807080c003544d4503040d141d05036041925180011a403080c08000040f2442500c040c6180400708001030076400008100300c200304d8201c0181440e403d541001704004041da08038035445425070b00071125913518010018540c9840d400080000354810755000d070400e810301d55000251804414030403203012035424140074003011071082241d071150742c1c0880040e040b981c8000c681c4644040c0206c0e85420996505502405001e8051100174480c000880b40602e9030386400c880290010b0307411100140381b016200d03c641ca00f180c0843e00610300106003100400c61664190384021034040c0803980c031041840b444c050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 892301187 1250 892299937 892299959
    0x1180b1003020405011b020916031b174f03030c02060624070f02150d0b0a03020105120709150f11210c0a05010501090b10110d1206 58
    0x5a404681c90140e1100d0501001509440d13030480c0d8210b18141080800c40507070f0312184c8458000c81c000b0300190300343e440580c089010b401010b4010034050b40c0301c0d6681612584c86000800780d5051b100c80102c2070345030b0340ca100e42c0001c0d4045a0418041038070383c0c00e4081d940f009003883d0100c207004082000d20080121105803070038120b03030240c01090303071071020501a0760180401644581d04540302d8040c41602c3c414120041e850399040004003901054090420820140200500360000c0a00c20490010843c00071240c0c0020301c510003160521181d003074181011590701c402d9a605031512420300c0424440110b40d088000c20354010006540000609038001ca0302290060825a4072501c2107003550780041c014920600d0b0030701040e030018440c020720840d14848018800039840c402652201130b02c02d0945410030603a030250007075181400009983e10300b036218485405054071440c10b401d0f016142603407041044114002e494001c101400704052281e404007445103403107040003c69075120b90441d40c0c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 892302437 1250 892301187 892301209
    0x3050f0d050a09051c20030d110c0d0c020307060e0d020a0b092b030509010c05031210050d0b010506030a0e15091908070209070302090d060c0806031501180b 69
    0x240f55a030b165a03040c04020b0040c5210514510707900c1054240000005083c0c880300440300c04500081c20890791b10300d03020b00490b6100e00c128441802900b0901d0502d00072940052810b40491052030603c4c1001c0740102d48100d0710940040c0504030092402900351400420030012551210448600c040142d49020116010344002599140c460000c7c40a1007150822240e04105201c015400c2c07043c109a0301016480315981454002d031280301010041c1c2d0030f0713040050014900d01020036501c5120f0603030036405100d040c40e01c0c2000d0945681d41d040c08106d030001076016100901180042c480e90070b01c4001540c002c3c82c20800002c60600c40c2e00140d00f07006e50490302032507130b80030300083c08102e480400c59806070304028419403d0101640d40c45412070320400340005d014005480004502c00e0080c0e040d10758614024240c091000700074a0400d008090000f030540c003107000032002c03401c2401c0c00141d603100010200c0140c1043d03400d064400a80c40d4021001014003500d07039403c0e0100d42c484e800401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 892303687 1250 892302437 892302451
    0x9010e0a0203100308070f050115030506060607110904060509330402150c0c1509011205070306120b180303060f0d06061509080f03120406090302070305070f030308010f03050a03050f0d05 82
    0x1d84040d07860014291100d41d48000071401e0ac3c5c95062010400c00300384260065401c0b41e101c0c3c0d0b0340b9118501010008510440d9940c4202510100802d00c9450f4200c00d00c10020481601c03020102000203040b503803040a1811416260910707003840c00b02c0c000d08941c0d0054001824a5001d84000380c1140c0c1c264810b503010217492300580b00e8802035003400c01014003c0111004058181003810000810b4100e000500344030251f01d030030100b28050b000e03074055070250030440440140d280e6981031000d40e036802522034a801262444c9800ca199502006480c041d20004290380034a48001c0100303d0603960401003035403104c0d694070001400015884c182400c080340c030348940000c5440c080310242803070b206a004603c03c1c0c1081103000c403c0035503204a294050781c450304c001111120340c14101d14002003508000e1082c450400e001c20350407510760104044900c259140310a45e80c9480e040c100f085000e1200a20a82c171602d800c3c800240208064a51215486002402c014643d40d4030020b60798191012 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 892304937 1250 892303687 892303703
    0x80106050a15080f071106070c150b0a1a0415080108101103240a06020616020a112b081b0c0a030204110f0c01061409010e0a020310030807 61
    0x411590030709440d000014075002d030501520390403042d00544582802007507044a0801e0300001900b545c0540d850300d0a1022a20440d00c851516100180901008800c296084450260784402e004030074012205e141001608008001c8e03e40340161102ca0107003040000d2000c0103207c080b9a121a031200f4440c0c2c280b06a85218055140010190a112080e015240c4960030320b0303406c81072200f41320300b00d0f03030400090000d10803d00e940d01b03601040d81d100a1500303980b06010440004005030700040e0f0078041c805903540480c216141507000d1341e44d0000e904006041402d644c07044040d500e004261010402c000c004210030b115440c05000d0080916000300b100d241a0205a14154071046603080002514481c02030100103000ba0000d8502c900610000744916203414041d8032240403182aa246c0b01442c0c1c0701d207030301c1d160380c0101d8602a20581c060300fc08140b0382000c40c0040e240c10748109048412040100d6019100c1d41420350103503000800c0f603181c5aa00810000000e40488018a0280e01803551 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 892306187 1250 892304937 892304939
    0xc010e0f0106030311060c031518090d1b0c09090507031a0115171501050c1f0b090c071b050901090c0906030b0609060306150415030501150c11030f010501080106 71
    0xc0c180c842c8454107111741e40e1001c01000410001d06007103d81042d541c007452006010010002112030440d858005405040301c8240304004030009201042c00100b511400c40e0030031015074903054203018500c0980002418502004421a9a4003078140c09018409403010152251550303140442e80004442c83d904110004102600075200c201203003082e0b038642450401c1c004030b101c0c0d00d0044d0251505041c0c1460842250071a801203040750b500c2005142520302c901012601c00340d070000c5026998408505144a06980d850003880b072030710070114040302500300096610380c42e81702404a03150250501c103c80c0041107640c1d9107114cca0003040ca00901154141400f0002003114075540d000000381410121410201c0d903840041c0c0e142c0303100c20b4403a25141e54075000015031101e600d00b000305c441940001c000c10a05604604071401900329201480141d0740d070b070000740301e14919440c0c083c00560044071080c0000c070404185251310500030204d8560942c6106000d0031100c080c1d0007010140e40d80c441c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 892307437 1250 892306187 892306193
    0xa02030a0e0d1e03120506222403021c0209040807050f01020f091906080c18280b040e06040f0f14150105030903030c0f0f13050901090e0c04020c010e0f010603 70
    0x11092802c401805c06000c1418a0b0011a42610b01000140140307804080210301040e503035444480c03007030115003900d80c0300581c102045c031101c00e25002c181d01607110402c002120620040800791046c0e0301a0030341a66943d142c0300c2c0103141d0010081111075009011000000c03d5007400031705400b04207038406e2a80c1d003105204012502c04900e0342212a10350040341041410f030007061403507125580781c103907a6a40c0c080d0317580080f40714101011a0b602c00048808030545030524585100441d20f114100b240c03494a40010f01098000c0b0b11441d0303018035100d0001030301c070308180e0013140308034402003030114800300e4070113900056400110703a10a000f03030014100014402520340c1300d290a803007030a2070342c594200880256100d1100412102c85003d00181c254100b0084804032081010703403003295a10b444106101184110b00f038891148039000310400032a10900601ca4103402c00c0c1040024000c04070030b0030500010350408144064155030300c050115841e001031000342e221aa220f800060a00e08602d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 892308687 1250 892307437 892307447
    0xa09050913021806010e091806091c0c1a04061a0d030e060313020a060203030907090501080a032a05010e010e060c031f051f02070b0a02030a0e0d1e03 66
    0x90021005038011210400540c8503403181c0050343c18001e200350001c0d654900160781d0107243c0d40ca15500507000d1b0702003000c00c02c00c000c1d21564128005042c0c9520b034a40541d9035070b072041300c000590515404049004a890b004112800c0540d1040c003020348418807188006048910441e02520415190002d950030703030412502d103d0040f602129000307404505520010401840080b030680602d50003c04240d2420003c02e41207a1340f9402080d04007482e4641c04001d450b030304180c8051649100d031080128060441c0d01619060310311983c0100745004403603e0840c0d5107007419400d411241a0091102003011b02c0d0600900e15a008000200d00ca0781580c41c0b07942110041d01994129030800e1007032240c1400d80e141125000341c00b101c18031035030000d1104009a800700a501440d80803001000c07048207610440705010220704c1c15002e42e40340682c2c0c0c20300c920603441034160301c00060f0800c02c81d040609020f9007180100b81c1e0040c02d842450740c1e482d91030302003000c0b880c01e80208425202c1401c01c00c040d881 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 892309937 1250 892308687 892308691
    0x90306020a0c020111011107080904060b04030807030305010f050108070f090e0702010207050601051c140c04020a0905121606051612090f0b0903060a0506040e25060c051009170a090509 81
    0x28020090030240b07100d5031f20b003406840740007840f00400040000c03690b03030b0300d0b044000a0b25146044950347d50b641d1610b0101580700d65400c5000ca41414000100c100e041c0c12084111441038440441940e00c403c1c0445400030041214000d11413600d41c00320b040013141120b50311405640d000141e40b1a001c0c10702e94500340c1c0507403040c0d105584810a031260b0712041000c03c00f0942d800050308020038a011003c505164481e4217854102d480890510030341e07544400700c4001c581040e078440300d40b5074433008450f0300e818040380c201c801d40105110070000c140c0b24400400000310601032040c003007811a41d803013070500400030354132000840100e0244202590740c60044010f041d5400d0f054500120440483d0311044e00a2822031510b5a54000032070503100e9800c00d81543e607040043d0b4a45a0112503070000304a10240d21102850f551600424901c2c01542400101c5411000400d05412854445405002c00340c82c119000725011031800003460410001d0724044101da150b07a85464100804d0044040e40 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 892311187 1250 892309937 892309967
    0x2130903051c0e0a0314040b03040c050a082b09030f0b01080606010c05100b010302040b0d1401143a080d0b0a061b060e0a03021c020309030715090306020a0c0201 71
    0x182070703d40390b11010001036400e05158541003880c13903488171200d2003a0034011548044995403000040004102030410308506845045801665503902c450000360344078003810b0303013158418401700951402d080030001e000c204c41c0303149040341c0501c0d201c0e0360765560150042012240e1400c800010300195000f40300080e0701501c03c0ca8208103003101d03507c0320b1b030b07a07150010445060180c0d10760b43c002c10b9074401d0301190090000c0e030481c0c503a20b01d00381d18074800030030681080c00351200250002040d000c499a03410458504000c003901120341104040300c20340e01442c4c10103201c440680e00640d114120b14000880a540514000390b182d0a680c0c0441040e55011018144582c540001c00e00500307030002c0c040011004440c1d031608216150785450700c000c05c81c002000c0c00e0380c450805090101540001c003e40f12420b0340c0e80043c0c0d103c90381001643d59000d69030560382d142d001401d00b8081c0700110000244040081c1c9001284a592501c540003280d003c003002600080d070100980044d540c20480b40c414081c2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 892312437 1250 892311187 892311191
    0x41809021008062103040b031806070323060f030a0c08060606040f09050612010f090303150b0a050a020307120c1a040507170304090e010519110d0902130903051c 71
    0xb6182d00002c07121403094014081c44c450b85501c0d0a0f406204200f9103000c0c2048081e2180d9070300300b000420040400103078500c10070b0f100e400c0002d9503552003800f07250460080100c40f10f5034861034080c412041103000745030941081900300080d06541e000c02c400c00340903000e90243c0788290300304180c29040c00c200401540c080c41041000300400c5040d0407680301155580c0c003002a1a40b2203000003030070305c810300903200c1c119070070300e02180015078841d888101d4103407094504029040340c0d242c0806d22200030b0711680c0040e80d0309100c4034051501070750040c4840d50702032043d20725081c000d0f995050800720300f1800c5030000c0c1030382400208011895126002d10305002c20641030307030318007955003603038425090191130b5000c5040c4210020a18042040c0c4002e04002c0c3c1061268002da680900e0003008211200302643d410a001401c0741b406034810b02005110130000c0501c1d01904582e400003070968104101d070841c1c1200b5004015122501c05c0720f69061203941e403183d4564100b10b403003101d0710114062000c5e0034 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 892313687 1250 892312437 892312441
    0xd1b030207031202070f050f0d030e0703080a26010b070308010902030f0402120a02030f0d0f05040609030b0c0904090302150a06051f020f03030108070302040c0e06030a050903041809021008 83
    0x2c2d0421803c00658448450144e0b0380c0f6100d28014400c0c3d510148004d141d0310403d201500c01c2000403c1c0350200440a03602084202114607006a44010500c8040c02c140001c00074071002c0c91042c90582003903182c05081c05d924045034a1100c051030b0099104148603500844d26004040c0d00201341c5004280c00201541181411201d0700c050900150000f0f101d40f144c910307201701601d0240003240226400900341d40050518003100354540d403180444000007852180c4c3c284c0c045000d01c050750183c078101e47d582104075041d5a12000a440301078604250180f00380802d10840c0c0c2c6034081d2038000d6119034050420b108205010601800001e04824415804c0050a20642e1980101460844507a080c1d1801c9480000d40590070810460346440480c0800400454004c00000300314044910130b0300c04024100d542d0004885000b1511241d550200080022074015203480d00155004083c80050300c0c0303095640d80360303202d08042154844c801d05884020150661522240090510b4a6820311505074 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 892314937 1250 892313687 892313693
    0x115110d0c062018030c1810050d0b07080601121a0102160b070803060d0506010806010e0a200a090b0a030c080108060c0304080d0f05070509030f010c02030306060d0e01020d1b030207 80
    0x540076103c506803c1c41d8458200070504c0d0f801b040703400600d42d00a0705600d03000015403076944450608807900d40d030344981c0d1800002c2900b0426010030032140c100d0030381145c41c0c075890f008849500c0068a0700d41040182500c216415000f482076070a4100c5802c0c81d01c06415204001908014116190b80c104d000d20701010417814410108503120389070300405013540c0e0b907608000100d203e1401000500a8840e1000100da644400240035050b01c91510854103a50780d8807408001743c854607401c40003140750900b2203802221104d000750000a5141c10a40c0100d43c40b2441481c10781c119003280e40000b80c40c0d0900900b0950000f42e8140941003031805440549850ba4051b2854400540010001c910001c0c404641042541c407000c9201041d24090096080c0b500c0020659008030610701c0c801d004044102c0e25400052003041e180c1c0415401560070769841c041001450b0308030b0091308265680b5043c1c07201e5050406e1000385902501c15200041c6842e2001042545000304100c01c000c0c50b00c100700040c08 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 892316187 1250 892314937 892315001
    0x1303120c1d0109030804080f0f030f0403020405153705030a0f021f02031905070309060f030906020c010518211c0f090b1e0115110d0c06 60
    0x100e030006404829400c40741004890104260f4006030802e04041008a261400821841600e241e200c6c201c40412182d107020780d86030700c1036209214201c0302c03c020400040c103246c0c0000b03901c80025061040071403c800b01117046803c0310600007045082c92081c400107229800c0c424014120107020608007141001e001c80d07078455102030060841c91424050808541d61080b0104401442c0155152042481034001c0d50303c3c5c03c0790304001081802c0301850112544283d041e91500c81d05940c4401e0214601302060710b605e005c0307203203050030141c0328481c4401080160005010f81b000103000001c441c80d100300b10b503075010b517200c248200035000300c20555940380e250a14210008851000d2580e5051002c00c11084007484034100444070703041201c01c4160f86010f0f400081c00310701030b030004c81d49945c0700300340c80c0c2c0100c0b510f010304d640480c2c482006000c1a01c80000c0025680c80c81c0c10060740c07854080740c07032915110080c10304100060140501c1000c004444c02039410b03240301014150410321f90325140c044 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 892317437 1250 892316187 892316207
    0xe041a0901090b0402040f0303050322120c081b0c03060609041208070e090108060f150d060923060703060e100302120109021908070f0b09060c0c091303120c 69
    0x2c2c0d00c0c0e103c2c02101d0680d030303895044a0003018062003c0c0b00c0c1698919004c5d1140e003084540d806507141a400600032005000c0c10503a00c01d6120101002c006103400040e80c802c01c1c038200a5035094803d03c8040e038081c05c0d510314025160b8108004000a6a03290704140c5003017802809240a1000d410511001030043ca9041582c82514244081a0b5a60210488a500d00110703131a40c40501c5000000d60141c021030554041c0c00303801e901120303e5851110302004113020400243e0048a6503413071b000844d01c40c0d4442007405104400c2040c04407010200701c107003035007000341d08441d54000ca0203008030103805124002c01488030054960032468466012040281c15100207401042545481d41c1485420342c020140154000c040c440e038100c01d2110b910513504680100c1d5124494010045592500c601410003110b1072070750701503e09000c06061000c2500040d840c50b1417840f6080c40c50103140d4400ba400c3c1e100340c030320001100710303450300d0304008083c91020300c0c036912038030314020a90641c43d41c0500440 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 892318687 1250 892317437 892317449
    0xa03020d0813050105010f0501020f0d02061b0f0301030503091914010f0216090c1209020303040303030b060f0d02070204060608040b01090e0c0904061d070b031f0905070e041a0901 79
    0x4009652100c119030015100d10b0381c014025485d0100108106160507003010035110207038222013540800c01003280e51080382c440300c0300140c3d20000015007042c201050803209100400010781c10225184800845608207810440d82c9400100d030241c5203050900080c2e85041001c4460045140b502d10a035070744804041500e8100460803651900090080204000000c441c03003103020300c60b60b106650b000400102148600040b103201ca00f1304e0f410303240e016002407181c000f000ba610785841c6560960041a42d48a1290450070a00810a86060100103407800310042440544d840110b441008221100c0c0d400c800c090202540a21001c0390070700c1c078010f0544440c0d0800090841240105518028808810a0b441070801c007c0008012454011304050b0410075280d2440e0a03030814040d03196040380c026403400790310620020f0900c0c01283c1403200004042401000384540742c00030001520f200b102c000d00411300040481801d418907208a22252003102000e42c1c080b200400041c04004045c1b00b00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 892319937 1250 892318687 892318697
    0x61804110315060f0903030313020112140c0d15060f03180f0f020f1023030c19031e150608062119030f02010e120714010603080c15090a03020d 63
    0x4d8044007000402c860300410010700700da42300e04c2e00c00c4801c910a02c410303400b01d000406407403001c1d503818214016003d10b0030202e12502d40c4c680e2102d00440b1075070091041c482060b602c8244d0403234580009001c0030702a11869581480e03280303043c0000703415100e50800c10010320207045040004145d644100c820060740c07107101d1001005882c00054100e280440442d03a2008903502414001500b014a14a0181c00001c4002d6095804402d00e5880d0004442c1281c01030f804201030302c00616881d070400303014002410300041010b4451500c1e42c007050b004d4040407030140d072800800441806940305900405e020300d840361191400c0c00c0413850610020f643c44142c220301c800501c07884031040c09490b400c408240300c813051030100c0d41002410000c01c4800e910255180c000301c1c1005045c00f142942d41410718403074003440e0a400740d50f00504070000da11001c905568880740403001074101001400d8640310a00240321f182d8802c1c58044185101410305c09550780000c12980000c1d4001c00e841f800b0950909203 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 892321187 1250 892319937 892319947
    0x3080904110a0203070212060f042307091a150f16171c05010b0901080a0209121b01080613090c150c030e09042d0206180411031506 58
    0x20502404801010741c089001c0070403440c0c0000d41c000042c083e824000c840c100405042c19442c40d45454042d5400328001484000040204402c2c41c030411103520003032100c501c1107c1c1041158180b80b016017250030290344640c002050802171424a40e01031908542c2e0700c0d410010a032200200344566511920480d001003000300c4021030340030081d4000c82e000ba0102c2c40031500c0c0c1c000d400407030b8408600f2400c0445699160b03906102148146130581e0100300d4101c0c9480d90b19001540c40e0800100380001e0941c00300514882505da00c06540303564400351009280c0d41d62501d602c0f070800011403028a040282c0c0c8402c000d8035580700e100c581800040c0c400c002604e11114104603410515a0b004800801906030148a0382680420849511806070b0307201a0460b007c1c1040210007042030764080c1800301500010981181c3c1c100022070541625071040c43c212840d0f40c0031607402e800c41200e1100c860910400f4414508060141c081140840c01107185941782c11010081041074400105d4052000412 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 892322437 1250 892321187 892321189
    0x70e060702060403060507080c04060c060902130c0e310b06040b220b0705063705011401020129010309060e0109051b01050403030e030709060f2d030809 67
    0x215140c054000d0506a0340325102d08000c00540410359030400000c0303424000940f41184c610a4a00b0342c1c0d007075550300307c903000c064036264007030301c00e00c402680e2004c144090740c103007500c0b184035403a1908855214401d001c4960b0007003056014040d50500c00c01d0b41d00d80c0b1011a01c44440e04001656901c0c1c2c1800141240c8450105981e40215045001c81100014608202c0c01e040180700c00d4261421180250107600c81c0c150f8600c5010303506000305142e000c0404141b034030b105100301c540b0311030300d40f91001e58400220000001c42c10220030700c400000c0c0d03030b540188040c94500c4c2100385002000c1c0000e000e41c10480d59021a5a40076102542e01e4082c0d48210b5213035070384079400c651009900701106004003c9485c14250081c0010311040b2810302c42c04e1030f061203c0e40000d8601d03021000503101c070750a00d440c40d2010307541481c40c610380c1641406201303400f15040e4194810720000e0098140022402d0342004084821074000c04054211820304c5510140070201c40c0402c2c4050700d40c401110703621415188 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 892323687 1250 892322437 892322449
    0x15200a0209090a05030c0f161805040629030f0c0102030f280f0e092203021908030403201b01020c03010603061505060316080601170103030c1118070e 66
    0x105005285010000382e41c0101c000024840c00e042c2c047c60180c603040000400e0705001e41625205500b1864600c03294821800300030380c801c96009005450100d81c0c840c060101682c4007094403401100c004502c0d540b1006030170100001001a468000200106034600d40007039640c1c0a90b44c4c4000e0741c00700000c0d040d41010494080240c40000c1d2805c80d001075214007602400d80460302d10500001084042c0a000c0b61900c08090340c041d5052914225440107a514850000b60741c00d10240e042d80304045544107010080302e200501070740100161501c0c1d04241c64000d080402c2d202180380040034500c1ea650510001142504080d540d51403000d40c203041420040c1e0620081c43e00450785035281c40300020500405d6000303c06120400c2020019040d1550304219890100b1740e14010b401c802d40d90012402c03806082c0268001d0b00504218030320310704a44070b00d00714090980007100002c1e4115419820007542c4174882d00b150004613101082401c0f418032030102114020000d404101880d542c804581e1540 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 892324937 1250 892323687 892323703
    0x303040b04080c1507030f02190f1103180a080a110405060a2411010e1002031f08071a0c0a0b070509040207240b150f1315200a020909 59
    0x10b00a50b50700704c00d072404840c0e92450072030307003100401d040c01000220312103d80f084581a101c20f030310341880e099201c03000310340114006141505214140c07450204e10142000074041c0c035000c00302050001c420903410b100b1501c0461703001c10041e43c00710110704000381c0011140c4c0d07030481056a0000380350307881c0c00000e0680c9015501c8001c111801c95550110708200c1034407801908c0c1030751210308003c481c0d0300409003290240b0040403420303000011540441c0100d034004540104040195495581d402c840071040e9402c65800201d80d80e00c0020b0801030009a00004188030f03811003113207410400d604200c0c6440d240f2008005040007940000181803e01480a590003000040c20440d00c0741d10a203406100034049076940c2c041c5903141c078000790702d440850080740c1c48100c003d060084090041c589454403504040241d40e8500c10601140a00b4220f00400200820b03610000781001c0076490b001601c0708511030410000301c8200f804005180b40006a6070003480d42c156030904443d5100940d550901c031036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 892326187 1250 892324937 892324957
    0xd0f050c01180c0503301e0c06150d03140417330609072001060503010509030c070e0921120a090c050111030d0903030501150f0909020304080910230405030303040b0408 74
    0x52501020300c7c85c6255002e01542a4100120346180c2c858034880060a84000c0c1d804c2d62002600030311500192144000c01142d00800712180d04154030b9404a1821410681032441c440e4464071a90810091845281e12145860318074031804111200700c03c000c82c5001003041e8001c80c040f00c04219114445c3c0d00c9800c0040440110a03000d8070100302440c080d00052003501e21a600345804a254002c1c040101d626483c0f292000b003955a141c005000c00c005401031040d890b034010a030140340c88801c87d1204181c12004178403910340d11031001e4032100c14a00042d0405508600c1c00c031351803000500700308440e002c5d07800034200b10b080e40004a110b02c3c0765204001c4052002c50600072280101a0580c03c640c0c141d80da0302100d04030b10907403540704440c0d10341c0032840c0b540080c600e0306007001000003507401143c0050280b16110315100041020071030300b0314440080700002c1c00881c5e81caa045007240c00003006804c01e0b64411882d00d407502d00003030f644c3d00000d40003820b5041030380d01007000c001680089520000c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 892327437 1250 892326187 892326217
    0x705030a0921050c070614160201171e0c210a021b0307110102060f0f0402121c0e0409030c11060412030c020f120d0f050c01180c050330 60
    0x7540400040450f005102885505c0c85000808100640107003110150000d02c440c0d15400c244040140c0c1600c016144000e906000c102542d98031107a00c5403c002c0d204400e610007040c0301e4100e8095150100c0c1c40144550b041c94005e01503801c40c21a4214403031039601f000000843c9a880e0b10b21800001d00c07600e141403017011a03c21010510740300101c05000180e0140c44581114034100005985511040f41c80307451a001d401c00180c0525405200583c200f030014000c544c108101020007884c14000c590040310036100503c08640140e804800b006030800241e1701402801035070b54020b402d80c11029002040c1d035200c8007041401c0c1d02e8100c2078500078500d1202d01c101d00c03401c03411f001d00011281074080e4000e401c101e215518900344a00ca110700c149112008001908070074004541c40c9084c1d84e0395408015040103104100d910901074510700881ca407115202da20050f1405101100c4590b0015029030004400c0b240c1d1540448000000b10083c890101c0321030820722800395152040f2890000007030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 892328687 1250 892327437 892327493
    0x15090f150d0309050306070e060715020909090102030a0e07080a03270e07090603140c092d030f16150509040203072a0809040c120e061006080705030a09 67
    0x343d402104041141c8050701918010745510700e085032440c1105110641202080141400040603880100c0241280200041c101903c10002549184095403003445c00d070b40100501280742428031540310030303020030802050260318201c1e803151640b040200c09014055002c8815050701c4084905c1c18119000b000d10184580d241c0d01c019011500c144d0f46580064035008001c649030740644600e0071104840f15080070f032a0b85070240c6001981c001c104086e001861004000c0c0070360225882c40c3c001b98030381140070b15042107620500d450210000540211584401e04c484804801c1c107410109841c0401910405008440d40c181d601d44202e880c035582161000040100c0142c1c00300014910300c400c051607007049070381034660218000840601074401c030400c025201487c0f03010341c451510314181c1d09007500c1c50350300c1440000440c1d8010802c0403894100c4010032803081048a1403d01508483c280102c1900b0101c0c4014040d000040c00c0e14912a41c4501e01814010f18a40400c0d4020440703280d00d44103 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 892329937 1250 892328687 892328693
    0x309050d061b02030c0c0f03010213030b06120c0f09071107060f0f210b010c0b09010207120801030507331119050c09060612040b040b15090f150d 64
    0x700310310300d80407444014280c0d00e42c1c03003103102004403508802c0200050000c1d5446204202c0c030500010001e0f42e1642d8202300d00d08040664082c1040114080c0120b003610346480130038491440340501e41c414598010400f0340380f079940c4010550710107410507101030000c0d03510b861003599140079511000340940320700c510004003d5400307100000c0c200c0c0e1543d103110400312814001d42d44014810001d0080c8a14101e1550b0786030016402034089500515201c400d840042d01d450544020980321010565000519101440b070300d90b030714901e408a18034045042d903240d900c440b6101c401034003c084041c400440009400354542210b568402c8542d24031310b0050701040d50250a10210b81c0a0350b000b40900c80340c0041c4143c080400c40c0240ea04040903044896241041280081008294590162051200030002c50b4440c1186100b280700700c04620140c01d03d0f081c041b0720500b0040030f030016030000364100300464071103030b10b0941c0040007081c0e0618540c039900006003290000d4046a03800a0040c03902e4018 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 892331187 1250 892329937 892329941
    0x8090d02090406050a060605040312030c050f0c030309061005060301210206210604020c070e10031e140c0117104b0605070317010e1e220309050d06 65
    0x30359000d1724100001c0f07a4404040c0c0d42c40c0610b12000e08500b11a84000c16524001d0300400c01890703c502d000340c41c1c0001102e03045000d400a10080f85642d00100800861034402c21000c0d8004250b0180b4015503803401000450b540b105000c0c180d0740c0e505006c1020070b2005640820900d20b03900500c00ca4940520003480182d20315a554012282904180425040d04051003100d19540840c805442021f0420403032f4500001c01615407000e041403407000102140e21180c04075543c20000c940710701c0c20304040c20054101440c146401c6007d800801000c96140c1c0c01100c51050a204000b00788040d99603030841000042032640302c81d50351145400403140c40344c2d0204003900000b2140700140d6804c21a44454089189914441c2c0540c4800010a000c3c0c0f500890150040310322a141250088080120302d0070081c8080e4807450402040f8000d0090464058402e4110b1100c20b181e403010383e03d400180c6420940c0301c098812100788080c1030001c14980700302c0720351021b000080c0c11021211014585180 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 892332437 1250 892331187 892331191
    0x13080f0d09061422121d13060509011d06091e040809041401081e0a050d08180118020f04020706180c06090311042a020f0706050a0c08090d0209040605 66
    0x103004403034203d21440d28144c2441c240c28190032880d03c080b440b2801e03c098031035804002e5160307076002c07600c00d80862581c1e0701010350000c900990404102039140c4418000580c506070813042c40c00f240e0258180c50245004501c81d80840100c500b0450b0761a1f10320501c0f203003c204011a481e8047c014100400c0c02040001408000e40560b002c205044c804c1c04010340340700082c00744942e250406540d480c0420001c40d0781d010001a00016141124a240da60710300d0a0020a1040042404c0ca0304201c0c00381035440401c00840c14110081c4003810060744040614110654000c3c4200304840b00070200361200d9060351540c40d4003480410009417a8a4562003034041848103c0d0403444010011828900c5182c03031800316a480130007079196200b00c4040101504035007030314080d100f8040d64602c00b01076007442001070854003130b00540110354a6410b5241083c5064002c0002c1c0f0030300b002944070140e4000d1205904541040155803101c00342000036090307036128800039501c01030290610052161680c80b10f4 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 892333687 1250 892332437 892332451
    0x2040819031404030203150702160602010c020705010507031b110a0807050a0f061b020301020915070c0608010803070f112d040c08070c1a090106030b13080f0d090614 73
    0x21102c880100102035892080d0b01000350980c000d140b034801400f43c01c81c4200d4010b5114015144040a41700c020a62000035620804c0140e449551000720240c05200f801d01410003883d10307516084607a140033f0900c1d01c0b2040284422819018138005010b2902503190f0b001500038280c00040395a0580c1c1c50b9544901c6c0a458420280d04500069a84549080c1c0044458645500940c00c60807006071041010707075801640c041d5005c10424000707907252200c04201e008882400754652009042407000c22070b40341c1004c010300090800611840d0070020a4503510f030780c890f4191402462901c1c0020300711180c90440e9421900829407581c8000c003504040a58107c03011040015503003003800c000644000d56a10742c046010400402c0d240d0307114586010b1a80d00039000303000a508501e450054003c07080b0780700c0110782d42d20b61003401001410401030f60400b805891510f060700480d00c0d42e00551190b551803001800e00001e8841c0009240e03040704d04510340015081060401c45103034024010000c403a48 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 892334937 1250 892333687 892333697
    0x1080702162619080a032003010e0a0c021905030d06090207151514120f031815090d170315040e01140406020a050f0c0f011425030204081903 62
    0x189007803040010310003407070241c0f00009045101d0240c550403400d40c030036943c070f80c100b5444401107484004006030042801c02c1010070305549615102c02c00e200014041d022580d1181001501210503500298042d8040c8011127a028580c03028504140795226181e1030131440c07818054001448002c80c2d001c1e010441c040c80c2003061444120039440111652140b00446415856806004032030034640090380421000e048941c80840002025141c1402c05003100090380c40021001c8440c0c201c2d10084101704c01c00c4d91005000e040c1ca440c524070300c0c000c2c0341c0d01c1c2d805122000804024441c91280803060260042031096403030030300080100c100b515806046000d00c1c02d245100340b05800511800440340c400c60320602058540380e40b00c00203940407202000803c0001d1111079007019a04000781498010640100030322055001c07031600703691a40c03050403c840601b00030070000140c3c01500c0d41c82d010440494910b60171105005400030301030354111400512a8113002d224440541c020114a14065259 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 892336187 1250 892334937 892334999
    0x21503060d02090f09060603070807060f14180a09090c03080313140609060c032205010b040c05040806180a030c02030109080f0a090e01050a05060702040621060f09110108070216 78
    0x40c15580d140320310641c13144bd48800f808001d440e102ea0004c0320400c1c100d00d0240350f1441d5902143c0d28036001038080040e8040340030203840c0d139407a2043c91080105080c2d1418808048152900c1c04524142d00c40607004080c0000050360b200b14100c0780d100d02640c400d0554000c136100054080d6200c404803841949845108041200c1941c1030040c1c0740b14880124403214140d80d400b4003c1c140100702c6104403507a41d2034440900c22a40c0e58000d4071101c0b00203a031001c1e00d8528180721700703250150242185c40098100d0309041100d11011910404a075010b027004100d031000361010a005040e2481d001c1c0c1102c0d00402c030381c0d0131072a08000402c400e088507074411402580301d10030780d0320201007841502d0f071041e26950100a203003001c1014014680c002080002c4e00b569078540708103600007222807140f22010740e0461008000030751090310354500c520002000340f10610307600c0001c00306242008906100d0b4510004001c0d42c401c0120304000b120f03d05800b020996581746041c092480041002c0229452100b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 892337437 1250 892336187 892336189
    0xa0e07030c05180609030106091b12090201090b1803030d0c08070e0a05010c03020c0607060605090f0103170c0a051204090e0f0d0336030807030504021503060d02090f090606 76
    0x199442510181d0f03101c4030401ea50802c00c409580b00c011081c0e01552140c1000a000541d0301c2000315080082010f1814444403040051480c0305141590010713600d4400b002d805070364089da450003600c500c161940d80d01c1000c24460320b0b0040303012074141e500d0300c80042c904881c2c000a030072103591046c02d915040015103840e9402d584e0000401c10340d0390880e403c0c5500f04115031245104980381030080c0161101d8100b40b50120702160300a450a40d0059101d02d401c000c1d5040100000798000070114510200c2d504503a01c11980c201d0101c00e80c045280c0110340400000401e21401c40013a5105040351070461007020310f10420340080c801c8040083c41c007841240d4004000c50582d0400e11a000a4152080e584c07034184d00a0424103544844c09054018210400b103800d022421325642e9500b0303010440d44240703801002100b000b00800c04042c20507041c0b01c01a11402a001401c00001d000c4079160741d0b40101049203903100c240080e5110202da0240400c4581c0c08002074040c44500007911070741c2d5a504 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 892338687 1250 892337437 892337447
    0x60606031e02090916170c03071106070507060207030504090f05010906080708060a020a030b120325050c0d08250c0801020f040e090307020402040801150603110a050d06050a0e07030c 80
    0x50344903030004d01580004181c0440715861011011403401c0c91201c2001d450300045202e00c084604075000c110000512900783d800000b1202010031210040103280f4103c0c40c000c00368011158000c1180d1340100f000800c0500503425600a080d001008000c104101d10744103014080c217105054419280c004086004107000c80c00c0000da98001c4010032440c0c03a0a600300000b0f41c080381a034406c1644c0e40c403c0ca80da030355454036424100340b401380085881c1d10600d030300454a02d0f200104070400982c00703e11140050408155030208074012100980f0344441410840f026124001b50b035200b02200090f141d00c01400d401505520030f01501403854201c1e1203545281c202e1041d800001011300003480708008103840c01d40241d0340f11000205a1341016001e50100f8141d0700540c1144840e0b03511240c00c0c2d20100f00182550008254514050009014509421102e4410310315a0801c00c40700240c0840c860702141c01000060402410000c034140c0c0e1618415039058042c1c41003030000e8101009801c21341d102e2 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 892339937 1250 892338687 892338697
    0x905070201053301120605060a0f020c0a0311060a11030f04060822080c100911040b150d0f0e121903020c030307080711010504140705030105240d060606031e02 70
    0x400c1001040e40000d42c01522880ca800410340240c60301d86e0404682901c0c0c91000c2c101e86072203031b11f032010003028644000c0e0801d2803550410b4004c107081e00b8200040390f504618240d85400643d54555149414402220400450844c0c0000307448001171010859032030100a0040720b210341e49043c1a600c90446c00589011400007003244416030f148900c000c584004000c250704418281207402041a85043c40d00f80da030754080a94001004c010100f1103400c260003a9404d12504840e080e82d0f2010121014041c1d0058030843c441070350f942c5008609901043c4d02521081c00700c0002c0750b4690300e46510441e540c1c0c1c01071201d03403410442281510403960103402650030101040c0701031400c55072403070380c1154440f4004040c0c508010201d080c8400707482d4280305d058003030760080c81c01d4507102610651240c605161548024000c0e8504010840c0321030301ca03021007071013401c4016581060b1484200040c0038500c0700b1006880107150540002d080c2e900740e4401c00c0c0380d1510b0520000d0b05200e50003804100e000f0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 892341187 1250 892339937 892340011
    0x3031508160608061e0a120c0f0605120411030a020603040c1d0c0d0c05040e09010504050106120b18030f030708060102160605031504021c09140a050a1b090507020105 73
    0x43c00c4000303101c1700c0c80c802d401c90800602030654021240e94101e4650316100d500320a03070b00400003c0c001c0c001e0350000302404029002c14100240b800314462084902c18100400181861451802c002496502405810121500100465100c0c1000d0401e1800d00b4494842d1102d01c00f803140c030040303014000340b01a40c818403040c0000c90520311000c0070003014100c2030709000304101c0b0030070011400c18101008540645401030001a030ba280c03a18006007141d815070081443d480c800f0448034009810011000c0e07100e81c0e540181c1802d80c5030480c2c141d01d10300270709001260408005c0100025140c6c4540280e2141209a00312882c0c2e194103950340c5809a0f807030040d07034001842040064205908185c80b941404405440185013000e0100c2a15a01700b03421428445c5641700c205c40c005020300e0103400752040403d400034000c2d00700a990303034590ba100c071000018241d45040090120a8aa0100200003440749040610291402c234030b000b80241811600c0c01c5c40e0605082040c0c407181c500c210380c0315030603803 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 892342437 1250 892341187 892341199
    0x904050907031a04110406080c03010b1e0d080903030c030712050909040b180106090c080c090603283b030301140a08010906020a110114070c0303150816060806 70
    0x150031003c1ca40002c40c024000c0c2c800c003482ea4a108217644540c4245001000c03079070042c2141845010800d400c1d1740c0d0030b020851040342c000a040420550f9003922089001d000c444c80300e04c3d1501481c02e04c070700d8002c0c52501e940c580004160355808003408001803003140c0c402d812014940b154818155502d00401030354903001302a60300042e002500740840e642d0400d6030781450710341a0862407020760a4a80e1500000d8503136450311401501c0790342003540c0a400c50300080d02c05041c80c517513402060351408014211710403500c50403424004a041c1c40d1092140400081080c4000383e28402c40606c040d11811030503c45c83c6010440c110b00c2404a0624400701e214071014615507403920580a07400c4010081c110740c012881c00700003440b0f1909109a10b101c6106041c05a1549100072020348841c598913a00030144e4103210400b0405440948165072018003402c0644a406003030500f10024241190502106003407003401044501000903500c0c03844110701d990b40c280c0c6803244400c4030804000d452043d00309c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 892343687 1250 892342437 892342463
    0xc03010315021b0a030207090e0f030904150f090203070e01020d120e07080105090601140a0b030615070f0b0402030d050c06010302132309010f061202090a0f11090405090703 76
    0x505a0001c0003c0422000d6040942d210003a070a81000d043e654100c0240c0d100d0102009218034a0060040c0e02a003c4081d09103100c01813845500c1e441001d0780c2c20301c00e994404c07521020085d02c101d00b001030504140d03841ea85a440e02100e0000b91f106a42000c08102d43d00b002d529650701c000303100350701c191155640340c90300307504640d10b10042c0c141302c03040a88e18001d007880469000c0091140620810040c0000c2203154508102541d03d00c10100c0d14900403500070000f4040c800114007146d4010308103540000ca20098198243d4143c011020014240d4a882d074242042c808107000790f0b40614000c17410394400041c08001611188103000041001d504180010009481e20030b4030744030201e1040e0804035040c28501c0e0701403d000400000148415501001c1c06400f000920408500750000d80d401c10815083c203084410f4602da03110000d1066400000041d140d1240b030700168403c0c511260b05203c2c0e040c00d00c1c0d2a002c141c2140440e503024a181c5070005080030400a2164222904608410242 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 892344937 1250 892343687 892343723
    0xf1b0a140909011b0909060e070206160311070b060406091e0b0d0b180f0d050906090310020a05211303081f0e0901050901200a020705040f0b090c030103 67
    0x40310000d0040070385550b20f0514400300c42c5044004520400182e850015503428806024107d502940140018908070010000e83c550000f030040d801c4030000310380002c841c40e81c807411000380041103450a005040415104200441003143e58051031003244e00380481a01d0301403940844507000492481c89145d4200515500c18a6001c109004409040188003d8458507500d074401c10590768000040c00520609000361018002d01e46200e00f030002074850901080001825401505c0c00e039441a02d000441081310b903001c12007802050344525040d511074002c1100030f03103941c00000706c803501c1403144401010580d0011003c0e502c00c090340903d034410900c1c161000c44d046c18005025840e80048090707180088a10081244000c10340300203003141758500b8045190a440c405001c00340c1c10b81c1001501d05c40410310380440001002a41d54164954690003012490910b8030b9000503041032030001000035000241d081440c1024050382d01c6502911107092007403e51000744001307808034505004501d12 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 892346187 1250 892344937 892344949
    0x1050f06010f2a0b0405060906060310050c1e0406090915062604050604172703070e0901240609140d0503190e030a0f06050406020c0f1b0a14 62
    0xf034565118a42e0b80c2c00401c071501c2c06440050f000940e00d01d00c20034104010014204002640b152001c40500708900340030001c030b540d03111783c1d0401e000126218070009106907070101c00d480c03540304011900304001402e155803a100b035025000388000208522400304d44600c490040311a5964900f0442c58050701d000b400311004104100e10002440301d201c3c5000120348a40c0e00c1b03d01860142e0043d110504091400c01801481c10001c0c0c6803a180c240232100c030050281d020756404003801c0c84414141800360740007908015540d0011607030300680c1420f0220044055200d03110340091070110380d801c000416071400406000744a80d000003000c4000034410703032140410b1001d1044010b01151403548080c3c0e5100d0554000c01c100500c0030154040751090b10b68045016140808254080c203181c2c42540c40381c01584e00143c0001d070880b9110004201084003070390455200043c1c203c140c6500340b041000e1103031a49980c242c0c2c00e83c0144441c03049030040c40d002c01c101c01140c401d03a102440c080258028424 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 892347437 1250 892346187 892346207
    0x100909020a0c02100e01030b0909060402040c0e040905010608150c0a12020d0219080105101718070f081c0f1d04020406091e0e0c0705120409060801050f06010f 70
    0x410202d1071001005031501101d5103440a603a8480d1554000720000040c11a02d081d18600d104805010901100301c0000c0ba000740c010360140c5011030594102c000945000429000c042d40161802219000b8041c0660111003a1010b24058800101c601e45204000c801c040e1b418500d144020800d0544150107003405854108540c2c04c00741c00c10003600d61003006c9070001d8102d88100c4904204e0241c005500031080341c05032400300c6c0c2040000020080c000d0400440704d841d644a00c90103000700b503e03d0444c5124001a5101d101110b5540740c40e141043c00094503482809200d00c0340001c40055094504414003a4146a03541c07a50381103200041111251040f01d2006025240c900810f1000c0e2914001440038001c82e03155802d54500d0001c0325211070955989040d140c4c04100018000f03000904103058220020740b0040c1d40743d0325642015800c03c44003041d22200440c0014000840d800250030a600b00c4044d44000c206076614014203072a0f400c0121005400200c140006800440c0100e40300d507 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 892348687 1250 892347437 892347457
    0xf021801110a02130609050604200a09030506100302030d09060f08043e04110306010c02060d1806050a05040c0506030a0b1c05010c020307032a0b0708041110090902 72
    0x9880342d240c0d50003054100340e80302021180a03032900410b02c4161500d0140c1d540080c41520200100d41c6106144e40c4406440c00c00c071681650300052007124140309581c070708051074002061b5070881c00c140030035441240071480103c0c024050703654407408003405914207108540b86600d030085440a0110101d0345050003c0c0b00301d48170142c0613200b4401d51040029080700c8400660802c0d03480100c400c030341c00410710206801c3e105909107025410340030102025250041c40238280707400700041c144000340c481c0c0a060303000c0001a1800c0240e03003c400045440c120303811302402d01004152120007008040c2c580c2150080d0445030005001c228a041800041d0750004003210001400b00d00303400020440c50240c2c0d480c0100112030144e034000e0120a109031510302a0f0340c0001c500e449160359001d000d03c0c044901180424040c071031141d0403007103510358501c1c401398000e0b951035061a08000140400d00c080d9002e450b103002c0f0741e643c20301505040c10207940080c4143c03105a0070074034003004d001c060f5219003055 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 892349937 1250 892348687 892348693
    0x6060c0f03140d02070302061b21040f05060a0f06090c080621121b012a180608041721180a0f03030506040c091205011e0603060f02180111 61
    0x45258102610240036510701c1b0360f0183c601d504040381411040800c0106103100900100001d294000d110040125070212044561919580318117260712140342a00e400740c061701410040080d042d00302c0d404404000225030080052039102d44081c1c04450305141c600c40828103030300208260f841d011350650952081d0003444d2002d031010500d001e08000002518040160f00440c003a40342019403d03270101000c40040003000604007072006071108075207a461201042412100035100c0300d10401090701c2400c50300d8a000045035603040c0080244100329020341d1b03082007603a00010303603002d15002c440f50350200c191104804400c0c50381c3e61044190241c10b4062038101c0ca03031800e0001805000c04440da5015803000e81100c4804d040180580f440240311074400c0c0d103051805801c0784d4114801200707640800003455540a145d15085004104e496041440001c0c0c0e0300850410010581049060300d2280d881845142c050b88030b880181d01070481d400e049684030a051401d29441840410300340c071840011 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 892351187 1250 892349937 892349947
    0x4060f082502030405041107020a0501080a02041d040302010c11070b090609030a11011808100f14042303070c0e06030a060e0a0c051008070e19080a0606060c0f0314 72
    0x1040c0c006401d100148800750b0000b060400c940d00d0144240e00031014070210300c81c9440f0f0540d001845d5480b40c4d000e6035041c0a00301d0045a00b03d0340c030b40d056401415140d0142100c00b19503a404002c4bc00d000c0b1000c0300103609080000d1192032082c0e4049034058401d00c000c08100b4248005006240c2210305400e40040d414051001701c0d035420010f002c01203025800c0c0c0004150100001445101b5100d07400c1c0319008003074001c126103507000030311400041d040080040d880e180c058504029000e02c3c140c850340c03885440244418804d00950030a900261b40301b4048410445114980d200d02801401400014640d801013004c0402038404a0f8010b4009003503c42460040c0c1d5040215050810851040d52102ea41d540030086d004040c40c010f0241212005d103c06000500100044001041c803401c002c0d0b02c0341404159110030100c0b8a15400d040c05400c80d491320307006099500e001c4004107482190400c24000383c030742e014903100108141c200444d41103a440a44099641281e001e110305a040c0301000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 892352437 1250 892351187 892351231
    0x60d0b0303040b041d0403051215040e070e0a060e130311030d020405030106050a180e120a0c061406030a0b07021f050405120c0d080c040801020301082104060f08 71
    0x2000b48007034410903071000d48441c10040c03041030400904440580e28a0040d0910011079007000680c1c00b41000c19802e8551540e070300c190040b603c14009181034006040c00c000441c0c0c0b107008200391054661440311800269181d0348260309603a524420b00c8000c10304000480c030035003002e10740315078414040c0c141041d68035580010030b4515444440c0400d0240d5010800380001d240c28003d540003010111051803480b820800c5011406251242d42a0441c0d1748210f91240210f041c07000204940080700d070309440f01d110003c0139104990003c0c1c00c0b9490b5240c42d000d03c4000c001881058090103000d002004905003c3c0d481c801e8000d0302801e00c000354401c0c803201380450b01914000340e0801a6a8901150500f000c2c0f800d18684007030500000005071080c0400e12000070009008404055140741c84481c9440c1c0310b50300303105441030b034000003003e500000000c0341071100000c015040f190f2620480c0090406482040f01c3e5004074003030500010701c003600415500703100300c0c0c8864020810f1000c00218800c500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 892353687 1250 892352437 892352443
    0xf0b150a1a071b0306060b0403020f01080a060509090c0315070503040b0702070b030a020a020f07061d06120c04050a0f05061207260105040606090506030402040903110a050106030b1311060d0b03 85
    0x204030ba4030700800c0c0743c10b01c1006124004e0b1070007000d081c88031030704103800e5600003030314407940302449410040ea120000c0d042d00d0f980d821110040c0005417032540581050429140ca442400081500174841c8110040484086a011520500203030782c0b00c0c0d0541c0c40315920110f420b1009001c0e00c0451042d1f1a0105032640c1d2580154001c0800d010010398840b200d1700b0103410708404140c0400117402c20038003000703043e0700001c4401c58440c80e20307201c2088100c2c0c0d00000d03006008040c170390808000f090b001c10960031503802c003e00585000b11042c52826941d9025588100c84a02a89030440400d1102030f484c005003400258020310300e4180031556003020303201e490102208003100206602d003140100040c1c109441004080d002921340744900c9400d007008a40b0500c800762000340507e035180046403c0c54030170064010001001700a03207004a0300c50401d43d010344a81c0c002910140d00d40c801181c00f040d9400d41e1a039196a0005480c00340300f017a0ba040103280e42006007501030070f0b07440d400b00b418107079418 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 892354937 1250 892353687 892353713
    0x32209051003030327080c030c10020915030112020402030a09080a031406010c050307080f07020901090603020117040f060e0c101106090307211206030f0b150a1a07 72
    0x115041071020785942002420780c1c010240b0480b0801800b02144c1c0485003024034a80403c0e0006d501a170b540240d002c0687c5984582c070340b001c0050207400c9580380403000e1500204400306007183c01c540c03140300780d250071500f178070003842000004000f01880704d00504254019590146c0c0c001030014030254503072101040341c1e000c0750004001a580b0500c40444141c03640c03483e60441028a000d241c0801c0555410356288922140a0f01d6004013050303c00e4003108400448038100d40c05801c20812b56514001c1601506d00d40c0022030205183c500890002c1e001512241d108070342208840e00a103615480c0e0300002c0c194181950aa4020310005569940f05c40708006030290719607884500c01d00015910600b098009848510543c00400491000c590180c000003035144002040b10030110014030151504100450485a881d0409500106000c0700d240030f000981d010b602d0f05901955041c42c6858940040b44aa907840000c2c21014058031a0140a210885010154003843c000306510b814000b0b0541c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 892356187 1250 892354937 892354951
    0x4060908070f05010516020714060f09190311010219060c0225080f070f0312090f060c050d170109020901180e010f0602060f0c2d031b0c03220905 64
    0x645051122a406c10b050a0324450f80c144040c14405080002c0302c80200a50302a0521a01d0042007603890707880c2da0b00448440c50401403140c04028081001d0780f1103845140300c00d90301d10140d503d12080743c1d4000f04520701005500160b9075690310081e03540400800003480050300310311801041c900709078851080c002071101c16200c3c85e5842450f242d0400d00d442c1d800600b00c5c8468000703200801c20344c01703440004002d40e64003014011181c41202022650b8003000e6005913940034101900240260700460444e56581c012019943c500c3ca8061040e51440c05e50100000c5c0811401c004010119160f406403044420500d01040b030b140600e140c2200464440d04a465821740d0070700100507108480100c0002010140054561352418030710700c040d0850001c0001c00a0384002886c100c00b688001c0c0c2c43c030840b0558158082d00c42d0302e00008030b15607400443e000329110214800035402c4202c200160358451030440000c510f016071040f0908081d0641c40c1054829406503040420021420b0007003a1140b01 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 892357437 1250 892356187 892356191
    0x10f0203060a0501031109060703020a0503040f150c0c06080603070e0103050f01060e042f0607050606120a2607020307180b010504290c1902040f1404060908070f0501 73
    0x20701408110101e1160350059050514121669001c1d100c1d6038156104c0003000c80e03460352034501c1c5050590501101c0c0c140280540400200845c0600d43c180c5441e0a560800da076a0415006028041e44c0c000200a0b024002e8030903014208500b40c81099001c4d4802405001d80b003209a03240c3d0140054142a04120f855420090010b111a0402d00c01d410082240d0403090713075641030035261640c1c0d100c0002c4c04440304164400b00901040c1003100c68400a44019107038070740d50481760820340d40720710301960058030031402d03181c1c0b0104103070300040e101040076003081d600c841c1da0034207811036040c0c0c1c21181585071800b80300748002c5000d660240014002841c0881802e100f03011070284560071a920071400c913041c0003050009104600c0c0c6a401040c00740039034a148003001102c61101c00c1ca9029444520700c0714400e00000701420362000415000c07451080e075084c400314003441295070944104109401005601c500000c0c00300b0595040400c5090046c9400361070010640c031400700015200784296800d81d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 892358687 1250 892357437 892357441
    0x130c23031006031e080f0304060b030f030306212112010e130213150f0305060603010515010f1101330302010203030601050f0d152d05040c030e010f0203 67
    0x41000e0007031896007001c00c441005441e086a892050415080e910346280711035881d0130320108600d5100f01c4d0381c8041c0c49403443d5260703c0c16140c400e000c1d11254842034003e002d0400c2c0c11035811000020390b80601002824914190700c1400406400001d001010100d403061002041389074090218100d5100f55000600f60b0707d80c1e441c00742841d410810380c02803c0d101100010041c1e69005450403400f41607045a021020341d15480f0300c0c0000d0a80c0d0350400781c07888160035000071100c44211102c41203c5c82401642c245a0320300003014202e4404851114a00c41c40c201c0e0201c071503103d040d4103583c060b01d40c2000c500080070f10a42d20b0844186290235200300c008580c10b450482c5425030700b000311240c000d54520801e81180d000039281d000140106042c820301081852495503000196101e400b50740340c00b000b0950b6442ea0342031440348a4400c4490710b86103032058060075a2501f42d202500403800251070182483d290501004120b2020401304259840b0700d5412101402c0c0104200d01c401d040d4056128 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 892359937 1250 892358687 892358689
    0x50319110c1e0f030d020a02101401050f0603040b06010c020d0812010e061e0906150712260c0d110c0d02070f08150a1506170a050708130c23 62
    0x11021042c0ca080715900c080d40d03a0020850000854041c41c0509002588a05402c04141d01d40b00300c1002c510700b0207081035042000b5601402c8100d040300c1c4102c900c0c103d480c20403c00e1020520044d1005402d80300c40400060480d4001c902403450284003030483e2207070340019114103900b60001501c90000d8800580104021107a1584c1c260b00039104903420781d03640c0a00203582c12001c8512606134000d1070601e000501940e5612400c00300507040d0b9500e51340d074929505d4440d403503000002280021649404040e035061203101c0100c4200110011005100c0d1604801c09401d07800c42c0e07c1108520343c403200d80d403d15a01d003202420646500000400b80300c0210344001e070034044d840c3c11409044901c8003040180001c00035540d01d50708043e81451105443c0c40b19404050041c540050b884070310105000103095a20105d0004118905804808591680a40402607500035254000002e1400e0089150111043c5004443e2403003035102070200380d5503c0c603180c010a02c5000b0008170005d803440400c01 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 892361187 1250 892359937 892359973
    0x1030201080c0c100506060d02040303030b090703180327120209060103020c03120c0f0301181512080901090512030706152d030c090e0d0906050319110c 67
    0x1540b0140141c1048040402e1966400b030a140c009502511100462140d44078030084a040ca100140150742c3ea9890b4140540604044003126002c0c0032100c00240c84540319208900c00c0444481c210081e4210310f80301114540c004140c0c801081c003455200c00391004691041100800703140d001482c03105080c1c01000000752005002505250042100900d103e0010040342c3d1100c5800350303501c5d088e072a2032220111a0140124410601c8000000800c4613840c2808000100c0506881030050b41c4500800c0700030a546071050000c030800c007230050800590444050b21b42444189010a44ea658801c0003441c54105c210846000d9080007520409001d45d50056085d02035940303440c405403502d008403409e5070040c0741368000782e2000303405401c11440c50301c00001c00046400900c0b14100381d03291803a80b0300500340070038110305078030450035800c04003030050303242004941c03190315050304542d141200c48203800b161054a503007082c2e030741410011802c981c03006030103500c2034030b40107080308803800b084805 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 892362437 1250 892361187 892361191
    0x50a17120304060e2116050a0b0a06050a08010204080a11061e1b0a0210051c020f091c02010f110f07030b101208032d040f0b0705040605070611070b040b0103020108 72
    0x85900c00c04401701003101000102d074030410f1204018070a505060070107034100510700a0003000302052000b40010070078146c211406460040760740505403543c42940500301d04c030700e2044c1e009581103240031001003a922808040d265001802041ca00740c4040ba0110003880d00728150f20315503101180c0c140c0040d101e40401c98203501654014101109940c00051030a00c01d010340f1343c1080f178001801c00360f42c06000510b000c1c0181c0c142041d52101150f2040c2911038221191840c01344c010703100712000b202c5250b8211145a5010f07103650840891421040350f0205c9020b04c0c40d18144115002c140b5501410000e0750011800380248a4042c18060a041e509612a07848452009117005a64004c54408030459801402d4000c0c58180080703403010140003507000101d141c0d100c141c048200400d1100c80302d50b05200034445c8142401655a0709015259401a400317900c00041c404d0010000040b80c1e0ba0040890a8100e42110709100c0304c0c1c0d40e80490204100d034100d8041c141d01c40100210358200036419 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 892363687 1250 892362437 892362463
    0x30a030207091a04020720220e0c100207061b0317040305090604080c040e06060901171c1115010f0612090501090c090b06090607060b012312010906050a17120304060e 73
    0x71804040c0703103c080808083c1d0403180c8c074219603500f501d0004d8820800c07518201490150a05800070301445d0301940340d2140388a0b40011484400c4580044000aa080d0001c954180c0301c0d4203500803400c20207041c141004000300e00b400420084100f042e038802014000500e0b241008104000100c8244000e844242c0200f034100e0b8001d0003401020b6941c401d0040c15210182a0599025100641c852508100850400201c5001d400d030200f03440d4030003c41419442e00b00c00303e07252001c500c0e40c0e100c1144002d01c105208105070741010b2001c54820084200d450381d1284000c01c01c04100d44495007110348200e0b0849450f450540208035001c2c180c015448280d0342201d4003810300b40210702060b810301c2051002040700380da03804985105d84c0a00558500f03920940c80300541185503116441103903000304250803001e40000d000290b980c1440c014841a50b00243c025111b03549004008003441c01900c100c0c0b6018010754502d44c4050000e000510302c114000d083c04200360358415841400e082842a6503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 892364937 1250 892363687 892363699
    0x3140718020903030a080a0209090403030c1d012007031707031205190b1306060503060301140610140412050321100e06010c06091b05030a030207091a04020720 70
    0xa0401e42d030007200f55110070403503082046c40e640c0d80656583c020f104401e10590b201040c54148000c0c140c0c1a071001e4940031060302c4418040d00000a466903204503031559034001195600c0806001c1c10000508030303c890043d0443d1a42600c903500c50b03a0000070700b100f0229100c0045600400d056101050700c0402c0034041c4204001e0400340c624401880c5e40c00c61100310251601110b960a8480d945802075071310018808100d401c0c0c95020040a59006031422032081d800c1c074850240c10b40200c003215018020041084000025441d030607110a14640310401c1e20307050034040001c03042a05000081e00610a1020315a03407241e801032580d010784441e0307120306081c00d09800c00c07140700b003c441404181d078200c4840203955030300c05004a8550a07960001040c050401080700100300c59126000703107a0705403400443d0502d49a10074190342e08466040500142d00a8008100c41500b1b40e001780622b05000358150b0344000004045000d9a101c1d8a04a80d0258070007046104600c000d0040b901e001030885075 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 892366187 1250 892364937 892364947
    0xe0a0b1804061d100f090b0a0b030a0603200604140409120f030501090e0a060e10090804030c05061905031f03030507050606060f0a030216020a0e150108070c030c020a0314071802 78
    0x182c10b45030754042c006c5111701075645414406070f41e95040100c0003000ca980384184c0e21704d0140d48482c00752200c3e100c111620404c040f070410149023501e480042c020700c0035164504040c40c3c038640490004181c1440c40d007003130341c56480320b010a00d504410040b80c42c0c140c0f1403070002d1004140083c00c070f8605921580d4481d00d03001020743d81010200380c0011254000342d020030940c803194161030030440c0c985081c504040c90003c1503400c001ca103101038821240906201d903100e80c3d9401c240b1220340b140d01c50a0b1207280d540a084480070f80120081e5800c913208040c440c0c85095010210b103841c41c41e40c2c1041e40461070100e010b00400c4400c010003580098155090b038107041618096210b80c0c080c0d501e11070241500442c045c003c030041002c00b034107429001482c00c1c1aa0740d40309420003800c502a1245012000c0078a65191319500861080c0e008000c17960303c9100036156500c0c11500c41075030b031504aa00118421000001c07424400000440c1c41d0f0a001030007089261001d0071310004034032400f00840c2030042c04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 892367437 1250 892366187 892366199
    0x10203130b1e0f07170703090201030b12030f1e030c0d05100e1305100501030c0501080901060b09100302070501110a0e0307050d0308060109120b01060806010e0a0b1804061d10 77
    0x411550805003c92000b041d5848039001034525030b00c0e414028000c80340c00c0d400c020b402507168000a85842c000e0700e003000030710301342d0341805260303021803003140030031760040001426504001009046c050004c4241000205011468640c0d42d44242c421052154011030500f0149009215480d04402d41070303282c0300300f00d14040504000c0b1000804141415007140a40300501c00c0a226940d034003504000200f01d01d41e160324000010021600586001803400400245051030500c01c0038240d440c074004590400103000100558441c0c0591001c080640903c2200300045003409401125894045400d4860200eaa001480b180c0c0e4903142610a60000404000c162505003000e85016014500f16450303590b01300050395107041503802001c0c400020585d0b201031040500e4018140c41890b5038000c6652111001160050410000b040e409090b440f01045042405c40040c040d11f40c10590042e182d0301414005021a8000e41c80b4140d20080f01c1858414014482103480c0d005651540071351845041003 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 892368687 1250 892367437 892367491
    0x506060c0c01050c0703050a080712020f030306061305130501050f0102010b0105030f2d0106120504051f060506040b07020418082704060314010e0d020d0c14010203130b 74
    0x100d06810f0000000300249168014041c1740c000e0354000e000c1300c5204001e4a00007070180d21400c0c0984090030070148071120b103480458400c0e00e24903184003c1d4291b481e60701c200080d6510040e0140480c04074070000081c0d5459209002e50780c07040304c40d4005111b42c504802e00541c54401c1610a0440e49010b0310201ca40c1c2c0c0050940ba040a14604190020750b205050103090781c4107000d0403110717210141c00000c80d41600034900d0b030680740c99944180c0d00c4003200c58044140da030b0607a00288a600b11100d00c81c1110020740094130541c4e012030000c902d4590310004111190f000b074000284041e00000d440c1b083d410180038100c0e40d0006518071980c040d05985860b8246d0003021000c09000d82d280b10307528000c0c4200d40e008030106200034410003115559207480f580c0242502281c0c5010b50800c03000c4510034002040c07200c108641600134048182c000c8104482158034a030040742c0b64504035040440080092018500c0390a80b0342c00003240350602e00307003110390010040041c80c5125000c010796030860021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 892369937 1250 892368687 892368703
    0xf0c020c0a030b180628050f0a20031005040b1509120a0203010f0902011106010605041e0810020301631d030f040e06030307051209040506060c 63
    0x4224a0f0298403160351010761050a00c4203841c803407040d4000d0049062184410620040c494002c98414800241101c0b080c0c0d0811208110f02c0b403040300015000100356000155491044e9468001703207519004205110340040c4e5a00c12081c02c1036005003c1c0381417911951004000c04ca403078001c0c85000c0086007507036208010704540555400503003801d0702882000250350203513006001340030f6001c0c484001c000a050144099000036894185001c1000e00071440030706841840e56031519090820529461070440074162101c810034071107000a4040d02401000c44805d1001e1001d41d613949043c5414012040f440407010408601c01d000b07444a4451b42c1d0400300069840c003400140d40048400307007030624105042200030014510500c0a1285681d1080d030700c03161400d000c035013250051401d1607503d00071060b494400d05000c11040c09000b15500c401a0300c64001801c4074138003030b00d69940c2d504107990100401404a004a110885c0d81b6150144580c4910309031017a030b04100c3d00c00c064540e5070b070203 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 892371187 1250 892369937 892369943
    0x6120e0a030c05070806070e090a090b040209071b0c14011d040903030906240603140604090c05060403060c0305060d052109031504060e030c1e011b02010f0c020c0a03 73
    0x5030702c2000d070411000380503110003400244180e81c0d46107022103016061025250030540320303d50703041c00521805640c1c40707900742d03441d00512a0703440d940c0c41da0300f03100d20140d0140c110024410401052103c1070f01141c1c010300c009128009070868903240030800c40c0c07281c61940c100d605100c15903154418480341203034000b02d41c000c1290049442c00c42d80c00d00f58018841c3c0400a044141450b40d0b1054114025410701c02480e118410030803840c1d80c4010403002c0b12030b079921194101040c4808100030b458075030407168606000b0244603101d56900c10000e10594801c0c0d00445810b07440d07002c040c80300c1d034051252650120301556900391501c00e541d206c40e01e829040c509004601c140010b10744132260312005850700040040d0864000306040d03251040d1105045a0440780f050410f0341600384840044141c4e030150204030024406041e41c001440428140700304400c049641e02e40700c05014030007403860300804450781e400004400240003a03500079691900c03184c0c4195880306d003214a4940358002070500300c9070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 892372437 1250 892371187 892371197
    0x120213050411040f02120105010201050712020c030d0509061e040b0403050c0115060302120604090c06050d02130e010608060109080714040b0d03080f0117030a050f07061506120e0a03 80
    0x5150b10307142c9441d1000140e1107070098034010a5031450810342d8014a259651010304036a90b82e40d0b8070049090703c004449034800200804d220340064080d9401402c0c00d0070507101941e0401c292540d0020889004403105041030703208005200c0390030044a003032500c482c0d04c80c84e014268905030b264035641004c090002020440f000880e10307150701d001e61026141345515401c0d00171440d500e0030014082d401542c840b040005c440740100c0e80c03034038151140b540703000c0e885030314429030174545502502c554200c21850f942e42c64081181a5030f00c0c0004402101410020054240319414850001e08403034005000d0360602c05005002c2c0144800024103500301c034064400d200e81c583d00c3c4804107001c0c2c5515140c0e10b4108401d030603101c0070190000040ca2256406c244c0d4540c1c41d81e618001c018040200034035038101034004003d40219284620014001c0b50300d00340c14180313089034079510001180d504142801040500402c1803000c00c0d8080c00707509500240e035000344040000b4541135501d501003a800201446 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 892373687 1250 892372437 892372441
    0x50a150b12072f060a1125020109120f0303050603060f01090b01111e0d0f0819060e071224120201140a0507060b0a0e0604090813080102070c12021305 66
    0x810011100c03030a61400301d0005042c11101100c9035913200644039450b01d10b00b4822401c038203d40e410b0a6584120040741e920700b85540800c0080d4410301c84200a0f030401407010008203008400902000100340700c1d00400c4d000f942107050080480c0e202400c41c0b4441e810440601200c3c1084000391030540d000d001002984070b41c1c100040c0d8020103100300c080010701820f007404c101005014450b40c0410b10b105c040d60712074010b1250485040c111500c1c0040407841605c0861204810004100d40c0320203003178800100749440d0841030303001c0e002c200c90394000550381c1c5c1040c03142c00249024501200c00c0541c1801c4d00102c40212401000e0014010010170081c404003040940e885400565003001042e0b00c640d58400650358002d0443d4401801950028108540c500c41c0d8240070a0910448012505845070380c1c560504020280c028408240ca218800340041444202040c0407013004000c0d0b5400182d84400700c0c42c11460b9203040b5484005c0c50640351a500d4050313210000c20954a00340707440002999 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 892374937 1250 892373687 892373717
    0x3250f05240d0e070905070f021e0705060d02030907060e0a14040b0612040c0b030708131b0b040e090106030503030c0a050c0a080324010e010507020d0204050a150b1207 74
    0x500500141c6025a403e00c20f108a40d108045601010342d20022003d0043c2d50780c1c0c910a46c2c0418081307200c1c10069010301c1e0007081584c10070051705107600c0d1302c0c801c1e500f41d5070f691000200c05030010141401070395400818010495000c218283c000c0c105405e001c040c0088940002c4c0070103030703113104020b0340744240c40514550f952583c3c45010b041c1801403521362100e850300d1419055001c02c850031501d80f909402c022401455820940707124450b00d070303600003d96545411040030a1100340c1c00b19500c0301c400c0102d02840120001d8900540a101c0c02c680c6c580745011400d50514101910703100300f40c0d24205003031001ca6800f004882c1d004807904840d90b5141444c0c0811100c2e88100100c1c014030340690041441001152001035014881f205a40000351460300d424007102000230049030f000c2640e500c284c0503070b035000310090900036000034024194810706801007021303039908072488400c03a951080824108216040404061702c1951255800d003150814610805036002c0c0c0a6020310030880300340142 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 892376187 1250 892374937 892375009
    0x30705010f05071704030623040819050c0a080306041518050606041e180e0d1b06110a03111e03060a030f051e010b0a030b1503250f05 59
    0x840c1307045110b542d51a81d50341810b200800640c44804046045c0011003092138040c15401402036400803041860200321382c62002024002198140900006003e03c0f840398106100140000e401581913641e40e02c1c03c2e004000454251000840000405403000d2101c00c02030010031001091104000800351604000a422800303564062504640941d0060443c0d8072540390980850790903d40380d00070005510200d005030341804849401e198070815440504501c6540b403c0c03690080310314105a655000e8590f001030303420158850f000a040002c1210910754148a50310317190500802040c10450214600d203207040445200c079150200100100c0d42a07600c105030100113641c0910300d1424141c180c40c040352a203070181171015030130030702c0650740c14012010700a504030180e00400001d803282c1950780b1154100f2001d0326504a05503440f18080c00c0e600c00308400703030003c014460b0740e003103610b407403054690500c040744c00c8806020031040301000707a03454450700d4100240d60352400240c011002e40f20f44203 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 892377437 1250 892376187 892376213
    0xf05010c0b18011b050c0c01050f090d03030b060c0609070503070e19060e0702010911060306060a0c050a0209011e1e0303030c0e13020c0111030c07080c01060816090506030705010f0507 81
    0x40b22013020b541030060340d038024008040c0c541d0041c056801011111f401174a69010750b40040c158048100203024a500c1c100c1300e0004558800e0400154441000020848940090f03061558070b42c8200248108d03850104050740080800b140240700b00f074185044141c2e10300000e804942e1400207003076810030070340941d04410064644000424514035100700001c2c042c001d0b05509403000e881d65490019107040c070804992142d8070161181d89440c00c5210115000500c611050303443e030007101a0100140c0c0e49812a070b0087c02050a080003441e03003001c1c501850001c2e40d02c6a80c0c00c0340105900d05a01e00070110b05c0c000c50f6014100010301e00f02c024025651580400c0045a02c440c0440800106012640c05801411034a0740208940c60b0b00c1d01d101c180703a10041e41c40654124013070000304005212040104400d40f40040045280b568603890795207000341540801d001a403001c0740c1805035031418813031035520040407001811803a03d0000042c041a01800b0460304100300040c03600140219644920 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 892378687 1250 892377437 892377461
    0x21009080d030506040f0605030706050d180602120c03071d0316090c0e060322170304030807030b0102011401090518160503071215020a03090212070f05010c0b1801 72
    0x50308030341e107600004000300700c02c0350128881c41ca86024500403e02c0ca118803030070780e480640108042070a1081c10398094003c04004000035480b4007240040904082d0f5007039000b48644800340e140c0003040040c0f61025402041410f03002c1007401000007a5503c40ca032203001e4918280340d11150700007000441d0a25110381c0c5c288a07103900d440e00c001410404d950050f96550825035882603602c10010800c402c42c8401c0d02c008445e03e02000740341011118540059001d5440b03000d600d100030f05011201107007900122801c3d07011600c208108400181c150149070000301092000b0000303803182c4440c0c059140f00c107004422106550700002030403820380c226040d5501d85000100c500301f40d00712124a01800c0c2c1c40c01281d000780101400040e40178010203500543e44c1d44000003214804101da5000c0c000d4104246000406440f031080101580711825020100030000001d400407074200845406450110b9001c641000200b40121020070421341460303400111024100ca00c00c01c66542e4a405008814050 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 892379937 1250 892378687 892378693
    0x7110303040b060f030d020c121c02071806061209110a0f0314070f031103101802030f0706020a0602030a110a09060210020403020d1113050c07050f010b060702100908 73
    0x210003400100701c0da080c4a0700040780d8500d132400d02076041c9034a07420540701e100056407004203032182c9458001c02e01c0c2c0c440c0007041f003100c88080c1d000e8070341d80008030b0b03c645180140e00700903018014807448594203920091541c02c188407492522000070312102c041c0403c0b032071007a625400081048952500e0412058005186400142d2140e003041c075040900d201c100c510480d5400c08100302c0b0b002042101c1150b03040807040040d20b02d951140c080940060b5440340d414010030041060b50b84442c4101c18030741e0070807120078100b05c9803403043c1450044a404000810340c40003404100141e40002d01c0c51600382c0c032034005a1aa122032039908050314507020101035186000c5543c0085e01d40c0104a01d04990180d400c03241405111080c4100328451400040c1d0007212010116001c01c4200b000003129a5004d424025821018502401100c0084d601300c2000440024090705002c401c0003021581d002c0c00b8002c04c9010b4200b00050080c2c400d02c18001c2c0074000a41100c1d103141d004000243c0100208020307 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 892381187 1250 892379937 892379941
    0x4051c030e0307320a210b07031b08010b09130902041a01090e04050a06050c09030703050f0114011d04020a1518122312040905101e05060307110303 65
    0x34078155134000444a49900200480031001820124071441d942c00a020071610034100400f686c0b81c1d03008941030065070400003202a00080180c010507200d000c071a90f000800416000c1076240c03840003000ea11003048040303001800328501d000d0448024060031251001d00c050b4401100014018044010b5402441c002d911010300000d41000c080c0b841c0241d0b610300c03062ba152a0314160863781074030040c0041e4014281440001c00a0380690340020300703c0329490400c185240064a000000c1e002212107030000080c0380001c0c0001d00074901c105580500461082d03040030303401d68400c00d0f2030324400100555900464159252410040058884100d02d410318281028000e040442c07461000e004540501e080007825416410700380362803c2e800080d01c4c03d80d0140482401c0c0c1448490654181c1d40650903025400300c408000a0005100e4840085000d150940d1a040c0f030762000d0380641d03006503440e40040c03c3c5006400c0c0c83c1c000c0d1001154003a440b0f848400b42224501407181c0000918800001 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 892382437 1250 892381187 892381199
    0x20c07080a0f0b09060c04060c020d0b09370204020f040506040b031909030507021e061b010c0206041e1e060f06090b0102030a03231801060602010204051c030e0307 72
    0x20030441854001c036400c0803103403240c2140305d40d5070108440c0f4001482090005002442c4103100550107680000c200b003c0c0064103841d01504018243c03141140c940c0090a404549855441045513200c0b1040e0204209070b444404c002c682503010b2030092045600140e200d4010910b401510b0240c0406048151101c2d01c4808640845c2d00958034111035540c400d00303100000c0c08034042d124029500d90707102410603030710b03600b030141c0384000d2844110441746c44120350301c02d0b0f19544060071706034580c64450413041c020006c0c8542120a289070110440d04010f0400c404502c0c4243c00c02680e0021240d41c032150051801d000c0c0008107031400b003043c1000f4141950b000c0c0060f680090a003107040410400080795214210340442d0340c148606400b6800074011108410701a50085080c0c8003d5410040c00030218156250090303001c1341d51300c010f64440c242c4c1c4440f1308424481c10b0003400c0c03580000c6142606000c000307040e52042c3c07881c00710a82c0881030480d040502c5100b0014000201800316840c20303071500 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 892383687 1250 892382437 892382453
    0x111306060c060e0309220605030607020a0309050913080a030f0501090204050f0307230109180c0207120f080927071211040b0f16051606030c02070603020c07080a 71
    0x160040c0d0300c16040440c3d60300d280c10003000f1142d00704d20081842c101d1410100540b5426050f05007010320650752841c0c0043d003920300340265441018503a01600c4014038915020700740c180140c0055001e141143c0801c400c4c050050b041407602900f100d4246d40740c5103610300440140908000b50100c190808000284450b080d8020703006a031000c4842100001c207074401d0554501c800c1c49480c11302e070500e00040720b001d10366041d80443d4a00600d4074029198868007400b01c0300c200e24444031a010345d10b4200c641040d905100c00c02c0600400a001d031101d149540b00c14040362608100507003074190000d804001592001a80d04070112841c0c1c2c03540902800e1103800800c5c0f001100d071400403414041402251525902c1600340484007800c46504060a10862144a0f044800c0310355119008000c0c41d001702d1418600030014502c20380080494460080005044d014154010710505044c44c106d018415004035450b0142c3c0c506140042e1210340140b02e591510040e50300c6050303640541241c1c0e4040c89128 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 892384937 1250 892383687 892383707
    0x3020c160b04050a0914180c0d080304110109060c1b03020315070e010203040833131208062413030302010609150602060403081e011403010c080601090311130606 71
    0x31942802c0495891488034141d44404ca80c1c0c0203c802c4010014942860500c00140440d2065040720380a40c1c00502181c010341c1e42741810341c0c41d80804801c01c0304005804038401565130081c608104d0161901002400c1010904401001030590b002e001103620003540d5038000031600102283e4001c2c3c031072a45602120429a2214002a140e03ea404020b500000440d000c846141c4010f100d1100c11441002400191010350f00741907500310150011019850b031140d001368081021200e04445a2400b801d842c00102da2200a20161f002004083c0e83c403c0e590207000300b401c0711180004075803c04420243d2080d00e00080b10800c83d1080442403650561240c03040e41c1941e1010000008000c03a07205c100d40580c07144400590000c2c00040000344101c4076075801c1035500c40041c0e10790050149041440800b48c0011041a40205400e078817480e00340101000c04215080c00c07031050a0580000300300702158003010f400342c11903010381d0800784c0782c000c20300b10b2000981c0750800c40e103912068018016884 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 892386187 1250 892384937 892384939
    0x6031e05191b0c031404091b09081501180e010213050918030a050a090b0739050d030c0b040b040b011e15170705032205030a03020c160b0405 62
    0x6060303009011401210094100c07000d081d110310111030084c4e5401c80b40a60542030f03a103071800060000285581d640d000b0500e86607031300c40003c100c010454000400c034421a50017180303260301a9400000c8140f83d0340249054a4580c1407500030700000605c020301800007144032480707642c80003a48161507081071100340180d4000300c40644c8103444840c00940c220341e03501801e0b00a5042003140c1c100141c000c40c003d190300d401d0f034102507807a16620300740381d4256003040074281d500b10030051500d103030b80c0303a660f154510180541c5e42178031144920000c0d5036801611401118007030401c000344e0340d05150180121604e12035001c101d100f101d00d45031400410855080d00c00b101c0401981e000800c00e84520740003803030484089010740200910b023161207000c200d000701e07005082c80142401440c201c00000040c070b105540a488081e92424107401ca641c80600d010402218401c10713580c0f6100041000c42101e5580c0e645140140e2503144100c0c156041405a03540e400d403200309424000b07034100682000e4011510 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 892387437 1250 892386187 892386191
    0x1050702030a32030f0702190b1c0e0d180b0c0c150304050607081305010c080105030712171b0f0105090c272511010e070506030106031e0519 62
    0x20905041c00c008030003144101400c1d80050000408404080000e011030f6030004000715488c1c084125448000072013a000840e40c890001124186c040901d8580350201c00d04c1d00d420084110701840d09910365030700c0035014042002c2580ca041f403200048a5003c0507003000c1c0c402c19500c44821030280e03510020b0611060084c40e000341c103540e5030300c4a401034174032035500070020713103001c0c1d5074054122008403004180d04014140341100d2710200d0024403651038000c0c00b83c0c803080ca1550400c0c08051070041d0503031151403030320801401c0d00e000440f4800c400615203034408ac002d49408007010040214103580c1d0001200d48912581102d0750034054003c4c50007800c02c142625080d41040c0d00340103c0c122024000c16840d0f2054080d4028050410391640d0311554030f0100c550613505820030202d500710710382d8034400090245420031542240c207100e08415080c0090080400301c0c42d250108141d0f0005100b02003c1c10b03515081012030310080003030f1005011071403800f00407500d00400c0002a010080c4522138600b4 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 892388687 1250 892387437 892387493
    0x702150904023408040902070c0b071104060b0f071e02060f0406031401210303090605010603140604090302070e0403110114010e10050f10051317120405100e01050702030a 75
    0x550082c04280382504030345013030328041c20440640c000c0e501c0703884129462040c01200244c0982d481015022844c0b003001d211842580c600200025217146802140d1200020004011003036050b104880000343c3c400030031701c1d4145590b030703040403070251102d801382d0400c0001405200c940c6444000300b0655074551020090110101e200d0b0340c50032024000c203005458090114100002d400703075051110382c82441d0104d8030051075950725054510031391221001c01e071a903841050191300b640b65aa880101070300c040140390407a40b0025a5007405100b45203421860102107028544140d02c6142c21416a400034000c1d0340100042809a9001340314624260b0840d0020a045031044502e480490750001c125000c5800c040d41001a40c2c080103084509205c803c01800c1c0c0344c070401c1400827000b072034040c0c0c6060021101003c0c0e40c1c20500c0c0d4a90000b6040e20030030003408103658081e2403440340740b581d140403543c5504282c0140d540c0c0c450f400c0007130761500c0349040e0700c01000007038082d08101c01c071502220a082 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 892389937 1250 892388687 892388767
    0x30a020615030309040915110d18120f050705030c03121e0c180405090109020f061207080c0403140606100c02092220030d0f05070215090402 62
    0xd5210010a0b626800410a082070780ca41604900180f901031941307190000c0080d24010b0803204103210401d0036890224000c2141016446800c80ca5a429850a10094481e555144a07201d07006805400d1190203002d400030316118000b91480303650b001045a9030350446010791a035079040300d40031151000701000001e41601d9120f44174071103060342008205050700c0300c1410826540010300310007038501480c02007038045c0d6150300503d40140b00c00000000c120541c0d00501081303015060205004401c208003030103030101e0400c8a1360f0f01c00342a01c1c129102da140c005814680b44190360010b40081c40d00b403080d500920700852031038005e0300101c0e40130070300050300801030391054442c240c0a540201070f0000690030703000c80b601d08010040001102100c000d2195508074410041014041e11704a000300540010304040168001d0740c00c650400240c0c54120720f8000702207201d4200000c2c06100c425480101a0b8180307801c6d42c2c030f81c0300002c0003076403181500710501e03585100c4010107404851080a043e002 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 892391187 1250 892389937 892389961
    0x50102041e03061b05070b090111070308060a090902030a060903020a120e1206190f1d0709060e01052115010605071a160c030908031201080c0901081b0a0512030a0206 73
    0x10401c4c0c180c46071401d104942d01c4504030048000c20081040d501c070100390743d4010145005101c00c0344079842d03c00c2a4144203042c0408205190019001d452401c0da20314090ba40016108841390751000300410148802d240803400c01c0d00024000b0140d00d605100f44c00c403943c020914010800054a124120304c40710007250369a01c1d0300b0380300c0c0030518010144515155185401500e4004024070740403401410034499080c1ca0302c4d84070403210880e007082005022420300b5020f000014400840c2e98850365042c980080c20b0803080b040c4120008003260340a1815000078008128100c2180c003a02c2d2503076940d050301400b660310621040b203014403141041f4641c1004149201d005042e540d10b4071000c8458242e0651313000c41220f40640920011076000036503800104000c1c044e1406102d00100d5a5140900b41403500b2400843c840c4103494690060082420010f401413001d07a42020200d094042c243c0454400c01658118035080700c040351004201d120000b0060800303042d280d00300d41407940c03030a440a00b = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 892392437 1250 892391187 892391231
    0xf070204140c1e040503060702011d1b0402071a28021204020d020a1701061503090201020c06160515160f020307020904060e01020a020109060507050421050102041e0306 74
    0x242c4000600501c40c2c04003c1010303180742032403030400f001d19040e00e0383c0c002032404400722210360050791240f01080c6c80b031017001c0c03200010f901c8001c010510000b0a100d500c81c000050000315000d9540814030350103000144650781401c00c40794070085400c0c20904c158140071010000c1c00c0294445074003c18110302c04520807601c2c0c0f204034100e45050394940ba401c014005145a0741607911800096020804028010000000312104000021b1803840c4c008941e5484131039890201c14145416800005030740c02040c24054080203e44003552000038000c402075064000784040c282e48148800b52403c9048504040e0043c61910b40c01c072090220078208490050703003121040c00582040c0034920060608102081d0030611a040200703ca600301780700301d42260002e1b0034201c01030791503141480c180140b07071250300d400c0940780c901140707801d0500010310807102d4030301850f00c00303060901c104206000003941a50054804034038a820381d00003650039200d0410090000342c929529241c1c50314a07a0301514010a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 892393687 1250 892392437 892392451
    0x1a01090f0b09040c05071e0201120c12050a15060206152d1f020d090806070c0201050f070b180d0801051807030e07090606090b04081f0b060f07020414 66
    0x10345031000210603c4003400c016011101482014050f0340000b0710841d41e200420521161031a520700e0a0307000060005910031050000350380f40c43c0d00c800856034440b485034a401400d100104240d168154000d00619900c0590309240507040303004200c0715408914a401803407010107510803c2e001e4400c0040e0070351307030f9111215444a86e035003a41c6500300485d000c2c1c1300000010a01c0020600c0d000c100032081d1101d09032000142c1062114401640c0c1003480503010b480341d0b8004200b90f00d094400581890603281001c0e05001001c00d5010392080254100c1c0c120315405002555141020b0403103a009c444030380c280741c05600803200d01082192042010354100ca000400341c00003010b06401100c10800d0280040d800c054460203480f0800c4030400902006003003c031b0700051540c0c07802c44018a40c1260f03410091078090200310410402d0030001311149030b1144a9400e2541003007003500c2c1002040e44054a50300418040303441c8131144075110142070024003d68080c031000350900e40c460020242207400f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 892394937 1250 892393687 892393709
    0x180114090f01080a060f0f05040f270203031306030c0f0c0203120304050c0406030809010e01023012010909171c0e010f1a0111030a080a1e1a01090f 65
    0x221801e5846184015013002440800294481d110191070700314002c0c039003000d030f5608a1034004001b1030900d403156241150910400300141030300455000d050602c140d5008244004250390001550f4091007201e001b00000120f105550f0b5551402902138052140c03a603022414455421081b04d00030080300194a5004000d4100c00030019461541500041c005030b9a620035550000e41c191110f215402c003541c01598165203038550440010030780c0000d40001030454114002e007001d00d0b5000c0369240b250482001a420304094140c07041c04207030043e0461480002c4025000140072401940000b941c907009181c44040f107014040c1c84c105030b11490880780582e01d160002c461070007a1301d9000e407100107404000403501030043e540040598043d0300700815803a0585800c840c9560700700c20b981d000c00c41c40da4095420070f14402009400c0e000018101100107856020403281c0481c0b03801041c960a08405040001c0e2583d10030107034550f440c40c1d90090229440400100b00a40d82e07808040c121284400700d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 892396187 1250 892394937 892394959
    0x30d060501200d05031e130b01210803060f03120721050912070b1308150618102c071119080f04080f0c01031e0c0c05010218011409 58
    0xc11200c652000380441b544801c0c500180031582c2e0302c0800c1e54001c4000500940a03640f01d414850201501039018401480090aa800403000032400390343c01d0030780001520380c5954944000c201510410740340c00c2e5050041c00800c0030310380e9030100581a03041c025039103281d410074203480038442e41c9030600010b07005c80d8091003440e803c2c3c9064041001d840f00d055081c0d402e01580c5400700b035129080f0182d242104030071480140402e000400402d0a9000e480c151448581004400314080017030b000c0d240380030035129000195460300041d03c1c43c0d0050141a582c14224451042c0c82500c02c0702e11404400c01c040942c002c41d01c101d220341c8140d1100711440d40a070001c0015980c1d1248500b0b006682111929401d21901003500140c00240004203001c0029044158111010b10300341103400709424185031800703140b4502ca1444014041141340d12100000742c4000820040c1d07880c10407880028007640c00000c000d46030303841011151955040c20380751480a10203010a200440c003605c08455000709480c0743c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 892397437 1250 892396187 892396213
    0x5030403060e010c3606050912160e090309030d030e0d0801030210262a0f032205010e0c10170a0c1b050307110909100e030c030d06050120 61
    0x300117181104102220918618641543d26181190b684a600030410205a182660038100c100b40800c0c0a0f610140071040b0050142c24076206c006d01400840611410010741040000c004440d81e40034005c01711040d106035008020058840f502d01400140910300c0d80b50301407401482d07024140ca500a1842e00c01005955045444072120b40e08032062040030000b80d0b140300e5600a0490043d4140702d01020f00b0106240b245072030910b0102c140c00c0d10001005002503034039030103050300e400800614058001d0341c01d8004008800b442201e01500380e5203060404101401c4c009408100018180c0c3d40d5107250303580784c0041e1075401d801369031240c0c801078060006409555541c0080c42400e11401c0c06480551480401e13060101d10900c21501340d4800075407035081c00700f22000386c81110030803901041c062501c0b100064a0760b1074485e84001d0640c941141440d000007d1040d140401c501d9005c980c0c5078144416820f010303019510526001c1200381c8010000700010080d40380e504e5007550300030994144525 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 892398687 1250 892397437 892397477
    0x60906160509040e06060a230418020303130311120a0618050a0302010c030f091e060605060d0501050f040c0203160c0504021225090302060d09050105010305030403060e010c 76
    0xa42031010003004012221a079a5a0b104001100086000400d5149008414040038030042d40021070144004201881e010030300c01034103403407040143c502080300c0100c4994a002d45007d0900250301d4080400d569030440c0714000071f101180c1c0a04410545080700c0818011000303888a55150190000ca101c00045070140e042031644688900700306c3d80d0002d0a80b601420b241c95164203c00507515864100c49072503050254000325240c09004001d0340f030b00e55075583c800d01c121220400075040380c989800c080c080c26a00c040020000034080503a40c210040769800200024041d051040080c510102a903040c14070402044034800d400561610041d801c2c8241084108002260218100307040071800341c84e83d0014158081509980720598140f440303402e0b10001c034009020074022900c2c0e001198032940b01d10b200b0b04403a01a01c0f01030b960402101d070017018048001c3c000e0459800c01c1c00010800c000000280b0441c0c1c080da004100c0c030250801d020b407e9840042c980400101c0c000515000820b0760 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 892399937 1250 892398687 892398721
    0x12110310060e13021c0501060905060a21050a091506050f060f071505070201180206250602181008130204050601021005090606010e220c0903051504060b03060906 71
    0x41041c071982c680010420103036400030114180c5e010444c4168402c2029a01800d80540010708094000c1810000410800d0242c00452400c102009540c203007902000090b60704d40e84003080c0240094900a051940988030901007101e00c42400400301c0c482a2481c42200700780c8030000c03c100c00b030994507010003186030080b0001c5800f41c401080341d040000d29101503200703151080d6001091710310700340310042e0840c0d680700050301d80c00c448016400d00596406086034080120580b04803620710400130107019003444010018244e9200003500307010310ba200000800d0400040f030307500c481c22440031070889800c2c10903101035101300216014280140792941101da031151307061044409001c08100101c05413402030301c0e000d075190818802d001c82564445004c1e00948815107184442100303d4003031409100070b401500e584540da038035070030742d04034816803041c8000d58005040702e41b550005c12802103051802d440c00c840291400c107900c1144d00317020880c81d00c150981406080c866a0b030380b55100654001c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 892401187 1250 892399937 892399939
    0x2060901021002031f091b030218210c120d0806010c021c062318120403060c0219080304060b130c0801080c0405040b040f0203011b12110310060e 64
    0x2d803505544074040e052000e14801c0c41c91884a040740ca94241801c007080320650800100a0b0401c1300d034000b1a046180078054160701c9240050307645076180c208a40145062801c2e42c0c1c02001000305801207010942c24020150b010b100b912000060b91003000700c1c4480d15040109140c2100b440443c01c50301451748554000c4043c10311140e000f4250307000079081c3d005d41014003481c8a104584c1c0007406450300c01d050031202a0b4400c0c02c42400e42c8403920102c190001c054905d408000f04a80e40c2c4c00f5400e12003800603100c3d500c0031546858481c9049009048010801c800500c03c2104a40b103000c40340994802503a0482e040c1440c41d01e507a2608030141120b0031165401003520b5900405540359845411503960059030385540c0e41d41405210307800c000003458810300c1281130005020118040100c8650420752100940720309401c20f2002c03e002d0500302c1d6601c07141c6141c01644028094200001c88844480d045003002090400000c1000d680001e941820303002d00c440c0814090107000c0c0039a25a0040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 892402437 1250 892401187 892401193
    0x618010204090507030f0f020319090c080114040b22110f1507030815150a0c0803040b091905031e070803010f03211b08160308060a0e10030206090102 66
    0x42c84060207400da90044d946200001c3c1e40c0d05444124106c0d92160040310703403503050706519609000303050070728030030303490a40180035540da078507040c1003000c03590120b001490f46000070b1045850360019502050f9044401396102440b000000d4108140b00b000103a035951031a681c03007080c40c0c4584402c501007031480b10481c0c00200415520340c180d42d581410002001c0300700d10007075641e243c600d002080390b400540108048800d00304070300342c240d0725480c44025914501040d540c65144401003100c0403c103c110180c031940000007400240910001c000f442000190126646d540a400c15101c480001c00f1015200e40c00903c52084404101031041c0401d000c1005464240050b0740c4607180558800c1c0c1c4451001407142004000b0030240c040c001c0c800c030042d69080a01c0780e1740003802400100300180802c40c03003250346407a8010000d110782500cac1360f4100e24000030a0003001d1710340039003c100e040d40c9142c403401031100c0028a84a61240c00d0f48a0880844045280ca10b182c3c01d0158541103440001d040d40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 892403687 1250 892402437 892402439
    0x21212091608010f0b01030b03030d15030b09060f1501020c010e1801150e0a0b0301120606030f0506010515090109122603010f1521060b070b0609090d020618010204 72
    0x81c01c0d69803840082c0100d18000a038410166250030103e030400380c3c00314181410705000184070740c2d01000340d40b544400342c48042402c2c820b90a010210310450380000b80000020001d11042580000c1c081c5e21404410f83c84903142e40703800100c0340704001e00c0e2900a006a0044045100c554400c030800700b501c001c09050101e1001c0100b00200f401c901c2608000781c14170786032a560841550000500150324025a0b1000c103030703410600403180c2884140950814910141c4180d400c102081d8401c00065401068140c0301032290725100d902c0b81d4003071042c181f040380c40d042460b40103028035040701c04804d0144c54480640e464200e48511040f07030340b4010384a08150404001501c9a6074244c00c2c0000c00ca202290b54030340c103085140c54402c1d490f800000907500c6d2542880c41607904007030181c8041c891242d590f00700207080d80450300909600e8200c1d280c2c080000c541c00b0f01300400114102c0c01038404480f07403000340c1e8a281e07c5e9542c81d11355484c02d400691102000c00c3d10020703905a4000f00b2005480058507203 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 892404937 1250 892403687 892403713
    0x1704170f180418150e0a141e0715140a020114061f03050a020c07080610090510050402030405103605150c0909070504080d02011a0105090102100501030c051002121209 73
    0x310801c006c0c01d075040c00c14200310344100310b82403000880d4884882c81104400c0c031500f0089070744481c0d500410b4140b5981319400d0f141c1d0341c01000054001c01a1130b801c2c941c0c80300142c000034040c007042444080f11403204e03008a249840c0c07003044e038a032019500802d00d45009001004a001e018090070700c0c01c99a5081041000006003800240094070b0720300000e0015013480452240902e075254441d40d261031411052005101404c403405c4203d40080314090b849c0e84807801d2250820200c004509001c52a100003071144110021000e101e00100b12222025110590440083c44103260b00c001c00940094040101500026291540204004084e00e0038959000080303032091314181e03282c5012610204040000307800c2000021500b20041c8000e0200020b46100c2d4042400c8012803a418808049900d0010381d1080210844040d004d40c801d00465942e410211100140fa00545006a10f0021042d00c0345000181c032480050642211602d041c58280d482280800003a041160703d0056024442038 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 892406187 1250 892404937 892404943
    0x3120c05130b03010e090303060a0306110d06080f010e1c0c0309030b1312020a0f11010c060f020703030605030f101107020d0506070305161704170f180418150e 70
    0xe0000007440903625410700d170940b000164010607030b143d40c1d4400c00070000203844001000040382c2c5d01103400305401d00f0790402900140182c25410140924294000074061000220880c4d900001002044021781422403240c40740d4000000c010f05c0b0340d002c8484a03d01d4414841d0008040c083c2c03030518074076920780c0c0d02c01d4011801600c0000c1c030949620303480000c3c00708030401081d8101c8a40020200c045c455682c89580b507100e210040c00c1204080703000d01c3d0503409202084580f80d440b0340704002e01108904808000d4101c050150000b070b10f0450f001c5060305000a40d070700b015942500a00c00d018840300c491000d070104641000c0301c10000d101d8117005844114034040c40500c1754025010520303026000504440d4002e02000e4207900000750000e001e904040c08102040d09044110800e40c0c42c2d003440c0d2080503044050340c0c8020301c001114060b030720840c00584a003840c81c9200400e00b1044108200c1a079500c0700400040e0f04408001500240c4002d0340a2180c262001e000300e80c00c56030b210940c1c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 892407437 1250 892406187 892406189
    0x30a1709030717181e01080402210105010312090b030a090302070e19110f040519030c0b030a0c140d0b01210b211e0a050706050705060a05010303120c0513 68
    0x20040340c0410745000c04d07401c00321010102002a112800801e481907025241c078800e118004e070600c900780010a0030754072a01004481c07110a111403061640700c03c21a503000300000d2100351490b07408589207034403592150b07107080b089800700200d490643e1144044003000308001c1c042101507104100d03001074039001c074010a0307104681768034854943c000a60056402c0c2c4464640031410000c040000007500914003080ea42540c1013aa400002da404400003c80e8890580c0c20107404850000d2001544040640040d8403030303650b140b010300c0010103a00080c0d59181c00a646580448410b201205240c002580716001902052601d04580c84054a0704415800b003100c848a03a035450748955003050400c0384500d2aa10b180c0302a00e117a10100030015501d5500c1c1090100c003481d503075840c40115000030880003624603044001c0d18410360b070399400907055134410344045440e0b00468002642c0c0300030f103200e0281200e4154590251302520780750180010081d01c00000d062140500101c21082a6044038030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 892408687 1250 892407437 892407473
    0x3030703171302031501060e3c0a03121d090117160b090102010b0d020d081303141006150903030807020f07090b0306281107020409150e030a17090307 66
    0x78495410078400401d0048400d4100c4d000e602c1040c60700b540707000d00d10380c03102c809d0002c818820b6800d44c508603405203030182002c0d4240e11404842c8044141722000d240000c4400068440e40c0170b407011800b8000c40890041051944505140010082d40d40011500c2503a1482e10b02581d01d82c010182411202d0305443c2c1114840040203d0f2001b01540c0911665084000c11144044210035542c00a400746280d00002000204041092035007680c03000c280d0005103030301420120602045651181e643c948610045640500342000050005d0048070304c1ca1500754590340c1c25520f035044d500c040d01e50a001074a0041140b140040382d0580b100c0030304c100d0001d4414100d0204001014100300740c9400ca000e8800d0b195000800c428181c040c08844210160588540c00070401c662090308000d403601a00300c010350018140900c0400b041a003020100d60b201d0050010403402a203c415030303030703280980005175001c1b49090384400d080d82041c280889d03004503c1b4080342d01d010100d640340320b0080c01d4612a1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 892409937 1250 892408687 892408723
    0x30c110a0f0c061d06130806041b0b0a0e040b030f011103041502130603091a130204050a060b091e06072312040308090a0e0907060e0303070317130203 66
    0x25020011800c40c00b0008044034030b001001240e0040054840030a119102481034a0000b8038060351102c03211a0700c01820740d1001d803021032034181401c0c02a12a100c1040031005803100010079042c0000d02a546403002c29614444401e00c3c903810b00c00280588007143e549403040c0b000204d00070000740521114030414007407640c1c40342410b10f0800d6142a00002c00c800c0203006008054184e110000000c00311790030f40c42d000c62100654140555180c100000d900003000100f0100061100203d2400d4101032003506c0400c4242d40303400086c5e0854070240102a1012020004c07260709107490f070340746040000350071903075600399800c00e00103030051344408021100c00034000700044c2c8c42a9103080c540c0001048034050110344412508003940740c031840c00024501000840c8001c00d0f61a900c1411000d800108404816424020046036445265100b5140004c800f1141d0015604020003075455440d45521070b880b8121003003083c030000540042000c244400da10740e440740903030340c100400c8100d25540245 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 892411187 1250 892409937 892409963
    0x60501020f150c030a0e06180d031407141312020a1a04151803060608070f0531020313140d1d0607050709020c2407030c110a 55
    0x1a0401e40e040300510682e400441c0c41011481c402200b140c0d01c05011403c0a9890b6503040141c2e0040c00000002ca5070791148100704140210602c1481c445001d040c02168a514503401046080d51503030380e0a01130754031100c0c000c40c1416015203c0482e03001207000d00b850600c06116188545464654070050781680507031041d009509105e14400050156203000080c2d1004c40c001ca5019807050f4440c51102d60088031542182c2407181154860008149050020a5030b60b4200782c00941013900032401e05000d07070000015001483e60160003192030140c04107000d51101c0800c80ca6a4246600c20020303600e06080c1000b0481d11480103600c9802c4d400070000c0c940c6070600b0310603c0c0740300542e22291a6070181c0c131303422002c640061418049005640c50760115084a60109510b409007003001003051140c058041a0042c0607009401d070352200000b00e51a05074004441a405404050020030b0803980202180100388a50030a03c030301202401c0c05041e10401002d00d500c1c0c0031f9007050a6404942e0280 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 892412437 1250 892411187 892411189
    0x151e0e07020312101706041e0c050913060f0b0f0f030c0a0605120106170f04031806050408060f130b070311160203061f120c0306060815060607080405040b0409080d0605 74
    0x30f41c51740c450b00700c0009140514003a500c82c02c101c1d844801c142641c1303030310101c90f1081085c41103d48001d231001612030a92400c00d983c02c011419080704040b03c2d00b0707017006010804244c07030b449581e51030340005040400c044070782c0c010301074580440c1400c0d90b01801050b1042040e0b4030b8400a0000a040c940c0c1c130035940d00c0c0c50012403031802c001a00a4001c10004043e0000000721810766540c202d406004c5c0414252503520701502c01c4403071001300389100000d40c1000900150001c0c003400440b51030206880042da108120b451203110216803280c003033181240791001041d170224180ea0b0041300784c200007a01d02803602500d40d55401542d6920201e02150014808504050040c0798005a1184440d00041414a034820f6800f21030300801e000c441c0c59103022400d1201040c00c00000b143c01c40c40400803681c541c0e4030292201d52031b1a405159003000c0010902c20300300780c0101ca01058003d400a0b00703080c182400c100182c0800081144d0050715401c1120100310b005005001d4101181070008083c1e02d088 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 892413687 1250 892412437 892412459
    0x40908030c040f0807030b27010516350903040e0c07060e070303050306101202160c060504031a0a020712030e0d050c0304030308060102160306151e0e0702031210 71
    0x1412884054100c1781c41000020340f0a869150401050221100149017040b03401b002d035030070009828a40c1d801c203020f00504140019404800d00e200795035800180003ca403080420442d07201c41110003d103070243e2400e03000c2c6110203d0b41c02c030701404256864103680704003a19200c2c03019514100c0d4a000040c0070700420819126221200d40c80102906401e4650744014013180030091004c7d004014800d50407804911404650b0301d40c1ca9251000c540314100c104c10880312503480b05d03040700c500380b032a0008142d083c016801e82d4116544490010106032001d045084906805405080815002d020080000c0c140315401e0b20310103002d0340c00207407140c1d43c246a9450680c04114110a010703003041400b1724050003000311000c2c0c07500f60034108150385810004070725026080030005d000341c052701030102c01c01200740c1209510b007080c6c1b0780203050340d5116400f0500c1c0d010004840b13954220000da041141d80c0401545540c4103006006490500810340041c5100d4182103800424140f051001400040c40d10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 892414937 1250 892413687 892413689
    0x1809050a12020607031a0f04020c15010308030a0e031804020d060b19020d03060f03020402030c04050607080409050c0307320408030d0e030702010c030e131803031d0c0f040908030c040f 81
    0x200c095206c10302c4035040442d003064000120725019640005079810341e0b010070000c5c000d6003601840744552540e508d0a10005a03002651100025420b0000364032460200005580e403044403010000c40382d07840d07030040000a5214a0002c02d941d9240c0100085007100d80b009814681d00a41d0041d850001402c0f00a00700b0fa04034071550700f851714040d800d11400d64210a0102500ea05540059403503ca07029110918011b5602240d404034000509804100185010b00110382040c039061003643c0f500c00455030b40d40000c541d5040000c00c4000f00d00400151007160720f107403030043c0f403208501001c240a800e110f58001d0700800f095900006503c509861305110354100341e104000a1418a49280c5c002000e4154000c0c010b400c2002c8109000406c0e9249884601c42c401141d80030010003003060740280304a00120f109401092a1003042c2840007800a82d6000c2e4540d261f018142010101c41000000014039400907041907031504c1d000e0004110800950041c440c440700700d40c507245451307044c03114181c131 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 892416187 1250 892414937 892414961
    0xd0c1401180b070605220309060e1c02093c09071a0a050408030409050717190c0c1407031b0308041403011b08100504061809050a1202060703 62
    0xc803920400c40c640900c1c003034a142136030010003c1807070344800300d01c1d001021082c1d4140d0341141040744000101a003100042d02121501d45401007442d260004200303020215041c540c0c404a09038145000510700f41c4401948404e5058040781419100c811000754500780031601c029800340542840765220384a12400d0b409100d00b00200005401c200c515000ca4103603648800100d0380105030842091300400c10740d0003078030300d00080740d49403a5203170340e03402c00380009803031110202e400c0c60744416502070b41c145110b210300c058850404401020a035405c0007441b40702055010085018008000190301280320744000301000c004000035425801d0071580e100c0c1c20419070b840b070340040c2800c00014a01200783d40440e0441c0c600105000c00b00000b2038098000c0d1981254203c1007507108851380c40c4c0210465004290244000900300d8a03081400220703800b42c0180c141090010900b030540400d1600800b02a40c42a0140c40d40c2065540d0781d40f64034030660000c900507030808010401119814458000f0a001d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 892417437 1250 892416187 892416227
    0x3070b1b0a06050912071a181207110916140d06080a0210050c060402090c040e0a0606090b07050703020d03180b040e0a0203011d040c150309050708071d060d0c1401 72
    0x80309590700210551003008440181c21540c0008e0680c030000c40390107028040d5202540c01141d00b2030080380e2698008441119a0b89042c0710313040345401c11015052041748166406100c60b88440c4040d00e13624203000142400c403504010302c070b000080c41d00841c0014a0b2410042020084510412402da9021480e00c4100601804148940c00300010030076001034060f1203400ca140c85149107140e01e07101c1d541110070811b2020050189400b0154051030883e1099565455040d4507002483e401c2d1091800141295009030b4090000d460403070500090309109080c045101040450b8004c01d80c03500794403030b000504002c0340801c0140301c1d0003019a40002c0341041103146604003c080c1c0e0031004001403c3c0c1c4000e03c5500001d041264428842d000350510751014900418260300c010050a9903e000712014028120001916500041c0b9a41562038040e030b03400002c02ca40600c0ca004080040550740e1001d2407ca6150102e04040d048402400400c21582400440200050b001885120070701e4003502c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 892418687 1250 892417437 892417447
    0xf08220510181e11181608011a090d021f030b0604050604060e0d0602270d080a051c0603030507210206060112022208060901050603070b1b0a06050912 66
    0x9500401000502d0740414020b068030091420031610340107010703004c981c0180344003006400c00074070f03501954402d00340d515001d140345141c1141240c40034020f100d8aa441c000029010018650200191080e07007009008801d103515a9000603691741c007051804c200d0194440714081340c0d0340d898003480a9581050303504504e03080c03820002c04ca407441244513040801c030403401c54a0090f900e40824821294100500b9134590941d0680c2da4280c40e011100b100200300b80030b030004000d0805411041145400c0740080d401d00c141001c2c00c0d0303500d41c01041c100140c018900c040907130703000030361003070b0006907000b81e40e240e843c4c00d170300d160150740b09800701c0c41c004541403190303000200b09078001011076000000b840c201b01039449005201c0041c2c004c64078104001e89265032407210b09400110b0482c00c0f203401c1021940c1302e40360544418200c1d24196141905034001400500c4041c40e0031300100210545000000389510b8280c07074040c1010104001201e440d40c0343e8051002c480e0082006441e00f003101c6625070311700 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 892419937 1250 892418687 892418693
    0x301031e0809010e010c020a081606140714070b070b060f0d0b0115030204050319060c180b03040311030a0206070e0117040b04050a02060a020102030717070f0822051018 74
    0x54010b8106441c1040352a480702c0c821644103548040220303a001d4181d202042d104c04002e0380fa102c036603100280d610341e400c00001d40b680c03241210883c0705180441071850b02180c2d0320f4401c40030390708030608101c40c03040510001741014213070010641c25000d14000300207800c1190421110080d6490000c0c414000b0483c18030215803040400d6044850354171860500c032011000c160007a00456100c81c0d4140982070712040c0042402100307000c0742e0301c01e950400075010516400c1c0c440c0020a0341070600794003e1181880044600c000441d085800b80c101003c0441c1000700507480e42e4051154070b001a0031140c240203040e9040700701c0086c11042400c04060181e2100000d288104004002816002c0e030400401c2c1400410302040203103030b801600381c40c0c0d0761584507000fa010358010780c0c4510019180038409130300d2000d1603d0440c0550b500341d4031800e0100308503204480c1d1100c068400c90f50015200070b2903140c0c8611030150443d1030310a0700030340b80c180322894181048441440138024178800c2c5904103400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 892421187 1250 892419937 892419953
    0x90608070f08090c06040b09100504080723280603020c101107060e03120c070b0a0f0e0601121a09031b030403080406030509010b0414070f02011b050301031e 69
    0x5a01c11407a00c81e0103641d4202100b840e01000c40c000700c0d040034001a0101c6c6908030307032004010810702078905d40030400044070300b140d5510440c03103800500c0c0c004a00a01080c0b03e60024400001c1480d280c1990b0300c2d555000040c9140d00710b00320403000301d003001e04c00c01c08004000342c4000241400c0c1000c50030141124559510b802e4900044c0011658407034070340580e41540c0303003910b00041d08040304001031540346d06200d541c1d5001c41d0601c10050804400507880b4140e501c102c40020360b000c41015640d803524400d601c0640070412000041d40d88500e00800e03030107420088139000302500c5004555014080c145080d880c6030344001107088402c0d10003007083c0c451000042700e041d590042c1007010211803442885055005540008124070000a000911594035401c41e60180601400810025071030904001c125074500403080350a07214000040e210030701507022100100071600010a0081c2c040358084d04200c0b58519000c04114044014400c0c42452590172410051402907000440c03102c0d122685 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 892422437 1250 892421187 892421207
    0x1309020a0e062e0e130207060203071b0f03080601120c05030a14040c2d060203090a05180103020103180f0506220809060322050a021e01080c030604060503060c0a09060807 75
    0x144184003200c0139044d02c9081c0341503040c100c02c500071511400c2c1132520030042c3d401524000700080c13a104000d090f80300f000d4441034a250b48680400755804043d5800c3c2c40d06500100001d05006400c850502080720728040d0741d45056003070752440c1c0d403840e124900c0340850341240508001705500c4c00c200400604660582020b80741d2a045000d42d2145819031303074041c0d26400c09480010440754500086184c0c0001c050034082404a5a484031980c4071000e10071a45801ca0b840c0180d41c00410040003d540240d0011400c5001e009403500c4030002074443e41d1700303c00588401c50340381c0d01003410802285507440f071440c81c0c02e40d9400c08401151846c1c0390285540600a5414480c45002020614401c41c01e0540c00c19280b04501c0c4640e408514100603803103100c000b41c140e004000703007049a074606103044035401c14458161983e01c410785400c2445811500001c0549400c544d41320004211654100001e901c2110620b001c0d603522091000010700f00c00d45035001c801444081800d1014aa0f00440700c0b40c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 892423687 1250 892422437 892422529
    0xc010f0f151403010e030a030e100203040b0f090309280b0901020604110d02100c0201030c08090304030f15090f060b011e12110406021b030703020f1309020a0e06 71
    0x107100b40081d03a0002c1d00424220f00070f40f0140c0710000d904188180c040e000660222184020b80b0b2071101c4c16aa003405900c01120018592110440001d003880b88440300c01d90410381050489042841150100307450307408481c0e101210401200302001403c3d5030707400c80310161020b04003241c105144000040e54900f40074200400c0f03800b42c805a81460303101c1c0c0400303084d0550014070a14500d20400b001400c0f86403580010b0703001900700041c000c0303414000d03039000380141c1507000118609031441e11182031019501c941140c94420810f142004020240210076040b800b44180f011700049603d40003084415985203036040c080b11100c0b8003460148110b4609469108d81801940903103100040720042c01c4800520780d101c0d00104000c030b40550b000a07101000e280310070505500121340400c041e5038820743e200003544155448081c4075103041045000000b0381d46810b0114000d200c0b0303400188180e92641044542e80208010000103262805100354508240500a43d1494052560309402c1c1584a621 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 892424937 1250 892423687 892423709
    0x20f0708070f02030106031109090a02010e24031f1505070209041b080616180b1e0a020a02010e010e090a0b06091906170106021f0f020c010f0f15 64
    0x407018030a224084607025607000b402004100d840e450f01103c100b0000265501a80040340040c3c0c1c7c41800183c80135440e50144c40d0450310740442c0c01000803880078000c0860700241e56420350514002d0781005075000f04450000706d0b28080460350310300d507602110b42c020030030103e4100c50b60603856000780441ea000c680590344120700d41da4a0a000b079152403c0003205240ca0141da0001610520108031540a8071103083c2c90050410303610421075940e100d0210b0300c03da80203c00030422403d8448801071814114055150492035000c03007085606401c013541600140c0c00c581441c0c0b0440d070b4040050007a00b0401d00781a0780f4800741d1804581d51510040c140000555250088079243c0e8400094810034500200072012480c04266030404904080c483c42001c0b944d942000c01510f007529446030b0507226194014070a80707159501171005c000c00400b800c0941a0fa44600e81c1514415000074119110034900101d5805600c49104044400400700518401c1c07400c03803000d003c0e100c000550700844540c0441 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 892426187 1250 892424937 892424947
    0x3081b16061e0807051e21093421020301110c03160219090b030d0309030f27030605090601060207050a17071212090801231302032e020f0708 62
    0x3400907140c003e9415012031039010450107c0120b421035081c50842d8401ca0b11035080e15001e4200360f8031400701d4070784451032440d105040d024005500f51070005241e001c85042485948009000342c2c4035415502440d21a80f401a102c207500302401207484518180c030000f803804070b120703000686030302444d24408681011107d025042d0f41c1e032004c7daa0340c10025100c0003d0340b84d070b98404800050496007999030007400b031001180526402442112000d40d0507440c5c6500c01911040304507000c07148442c9260000000000142010030080e19410145210b00c40c00606030400302401854044168010340c00c5500c074a400740329a46480106000f10303100c01c0000c8044082d400244ca00b041000c1d0410140910305a20345014002c20f02d04c414402c03911911400c8034203460350388007400d0310101240e02000705800242c60038401840d1000f16032018041d114041c56500e154002800c08540b840c800c08080c0040c1c46074124a0b641e00540300380350810540451034444400d2a9201c40d008001c0301a01c0a100410 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 892427437 1250 892426187 892426207
    0x905010e0a03120f09080c090402011416030507020316050609100e03030a0f0f140f0702030114090d020d11060f060324010f0608040c03081b16061e080705 68
    0x31500d07016540c40200d4091103200e0710001130226110a1441d8001a2240d0000541c94004907403c0d10019028150141690b83d5400640b41030300301c6d9580c0c806a4030b04200c0b98040b07401c02d09400b101c10340709540307065031480b144c0105481c2c1a03039038035801d2103440501c0707042081d682c80004070b07030207201c0c29160141c02c4204101c0580324031041010360b54060100240c90b5220a40c00012031501d0012a1a00080a074510b18104d80380c495403c07009124070790403c100c0c074041d4082d90141c170300310380f00a001090b00059100040b0380c10005a6140c40140c1c80958000c03d590b4040c0070440b403240c01c0e80b416521002c601c042c125510700740a084403030100e08050124019480c107121250b9201c42284003905030249d030394031070100c010b002d20502a84440148010800b144105c1e125409241c000561410300d40c103640fa980c6042e8805580b00e800b080100088005c461030a0280a0f071121140840d00082071428030b0117486401c000072070000710081c19400c0710400350047d004540149183c90a141c9680290f0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 892428687 1250 892427437 892427449
    0xd0e01020309090415050106090b040504020d0207080a12051b1801090f33170601180f08010b0102060f180a20030c12030717090a150e09070905010e 65
    0xd05075403c510300703070200401d00c0001e1080900d1038146042c2004a80c0c1e95000440e07007a200c900803250800000c010403c4107141c150003912216044040040c80c2450942d1011a00c8d40800300400c007040303d00b000001c0b013079024410554084069241c8405182c1501d08060540c810b548040020140c0000d005100d0b912a0365454040c00042d8488a030950f100c0588460383c1703000f01000c060031000e0031004249441c05052503c1041c8d00d54544100c1e5040002c111400880300510540c10006044449001c9125940021005280e00000300449900300407107907080d603102c80d070b50505541c015000c2c0b010f00041030313003481e6022501804001000341140071042c142146820040e1400360b503000108030b208000001c0ca50880c808504640c00c001801c01800929510a0000049070300300b0301618002c5226240c030281511044503210b031404a00f0000940d123803600343c0010800d1120462200c2c0e02582110000070320810441d0740000d2450509001000c2243c82d001d018100401400c03105001d44401d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 892429937 1250 892428687 892428697
    0x70302040f06080d110712020d08071406010902130b0403020a1511120315010903080406030c090305011a0315040c23090906060a0f0b040504110c030307031a040506030d0e010203 78
    0x50316800313055502c0041440b0000001c4582602946c0300000b00e440b54101c1e403040d0181d02030054070181a564407441100d80012100303445207202510300c280001c00900c80f541c003804c815040141c07580e004250818408090350885024502e08000074005a681d0458240c221003844014000010380c0c184111001013680754140928400d504004c5040c400c1c1d41d02452050006000c401d070000c0e841c400465130000d0a10000d000254104400d0003494861b41000710545050f00740000c085a0701c1d600c103800c560842d920101e0100ca01c401822480c9400e00200000001c80007104c40c00c3e041a803588101c501c4c9a01c5009201c101040030b00306000c2074100c00541352134008000c2c0c0ba20307150940900c0d448050803240c45100e40d040f50000722b484040d0401100a94100802050509040c2001d22000b03103000300555509407001d0002c0c081c442c0041008600c64500c541d008504800c0729003201e00400048a1030512580c140010002d1645002038680021681c503e0000300001848005170300754420 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 892431187 1250 892429937 892429949
    0x806060409080d18210e1c1a0906070f020c10120e06060406080a050c0d020307051018050a08061927210f08190f0b040f0608070302040f06 61
    0x10985461380c00500c00311504465806058405140a42c0c1c0d12640240c002181240000c903c0101ca07082c4070b400c110441c500b0391000c12010440c0b54032203480c1c10350f444400c0400782040d2801c6d0410132603910300510113140c00c032115081c81401841455800794840c0644800c850050303240d58180440b00b40301c0c1c000e200c1c2c44140ca8204000d074420410031251100c80440d00c1d640100d0810a002400f1140001c1500d02240c1104c007520ac046054801c010740088038107070036a818841d10360007207215030300d244d0207100000d0309403281a4130560140441113554170f0b0b50b1005200b212420020400c2c05c030041390b11503020f147d041e01c503a540d903501d00550000b403059006202e4442100d28800440058185003081a1f41c0100c902140c500541003142c4400209885820300181c0100da5405500780030b00b880036013100070005041c1020103214500d6007181d4004950001c8117440328402010b0381064443e03e05580b10020060112070701f00b14031180e48045610000380255522159420b009a1550110b005442 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 892432437 1250 892431187 892431191
    0x406020a031508031909050a030b10050402030702030c07122a031b0e010f03080421060507031b080c250602120711030405030c1203090d080409060806010806060409080d 74
    0x5103400e03910341d89401402d10940c0603503014511400c524001e05c6101c1c1207c10003055614241d05503500c43c1ea080c000504011000761148002086507600e5001451060361980d009503113811041c03070940d281c1402580a00c0c43d11842c0305801001c5a83c610751800c40d48181c81d140100d1000194042c1d12000640c0e0014040d00e074169000740c1c0c20020a80707404200d40c80038444048903622003904031540c0d12548401010080c0c100010440e00e2a05103003885c03a04110320b030002c080c0c0c030703070b0b13101c803c16100c1c2152501d001036030b101d0410000c0d5208191400e9115420b240001903440c1c10381081d010382c0300d200f0080d41c100c1c21012103034080480e51034120f8503159201206548460032012801000c02c1d06650311404541c0f45d03079584915002c0001a60101d880050003000b43c0d41120003400790348001c1b0519151a030008020304501707915440c0c810b10f442031048200c142d84501c0c00c41024221000c5410203080ca402020040110a80000380241c01003030840e000a5102c0d40e03481c1c158041c0c4940c0504007a00d074 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 892433687 1250 892432437 892432439
    0xa021002091c0b07121a040b011704050d030c020c0307050111030d140a200409112106090618010317040806070905010f03020403050604060902031204081609060305060406020a0315 79
    0x510f19496409404a80c8440c40a0f03007020325140b06503070500900010455040c80200d00518190700102c03440c14041c113010010074031484440ca900c8900b03c80a6441e540700f80b0240307510551503c104400300d07000d840078000590300040020740381c0c2802d2040b1810040c0c10f110a82e1582010f03c211203c20b5032454042158050b001c9038112155400c90302d03001701e070b4580050b81514500424420440c2003801c1d070b103035103054200b498501c001c16440d04005100c00d014030124803144a10b031220013019600f08400c00300e91a00404102c0e0f9928010112400780c0403480901811000c4485c0740e5065960141d58840d4041068082c4011401994040c600d1441038005018103190404d81d40000e440742a41d40b440909018041541680300728840100240c0c4080d0000340410050784c002c0049600c01800e40f444203603181e8851030540c2094004e5002500520603000c1d0301404454480300070001c0c01c0052104502d11380f2410380302c0b10010000b4240980010720b1080c1244254030003d00e2800c3e20029410302 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 892434937 1250 892433687 892433693
    0x51909030c06050c07080703031104090e100b04020c0a060b030c0301020a110c09040b010512071a1305030a02240705160617090714041104060c0b0c0a021002091c 71
    0xa4881150a841d07680c030f80000704281122101c1102c106603000420b00340780c105030390b030220014003443c170a40881000a002c0480d8003441c9000d039440c0c004919000340140350b00d8440000481d110007084620451042080d010300440101c0c0c0c200c0e0440d00800000345a540c0180424241030004c50f165500d03510001e020950380e82c010842441c0b440c200e80071200382840c01014000302d0001920041c000018285c010030a5203410380341203001c0c480d101c09036042244c0c0e40c0300d1416240b0810352403646010012840008002d50780c0c04050081400314001c03ca262072a402040c0b1807072003d0304890100305400040700d001c0342c0c94000c56184507440811141d4480020256808aa031039010304800030701040036488406410140e064041e40140021b0249a0310b4050240c80030040d800c050342d0056100c000d20039101d001240078000078812501c4440303403485686088100c5040c01480c0c000d6601d024412049800e45c0011001c0b8145c8281e240144c2d6840b03848001107050b41c050f88a80010050480d0f02010 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 892436187 1250 892434937 892434947
    0x10060e060424021b01020c04051e10050f03210a0c1709040b01030b0f0909070905090c1002030301030f080304060f020318010b37050d0f17030c03060405190903 70
    0x1581d00f80d095482c110400c00442e40d402414a10b601d0059100c0003080c82c00c2e28003a031029421600360750049140486d83d2007214000f04007180d0740c02c040000740c6030030803060504c1c21410704a00c0c000c9014000c55181d002071002c02548540c0c9240c402c44021030040e61150282a514010941014024031800e24100b01000c881d0300142e0706902603400c20510380183c3d402401030f0701c08500000c000b103100e6400c0c40c040c4980b1000042c1001554401d0707201c00150104203118107405002000040d045011301d000502c06580d510b00904002c41d4003c10041011039900600c1110590b4050780d800d6480e184c43c1440c1000d0400e840321581400d200105010008511010f2945c0c95255071000b40701a40c402c1040105140c21507030303d007511300e842009000d10904c0b8144003032005880c1d2501001c0300740e1590003141004200c0c00781180d0709030070107544200740701c200c030807040322041c007110420700d076162100b10542e5a001c043c000758000c988803004120800003006000c110440140010401c0c44818180140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 892437437 1250 892436187 892436249
    0x6060503010605040b1e04020921070501140d090606050406090b011404080a03051b0106060903051216110310240801061a070515160e010810060e0604 66
    0x8030039840d1210000ea541083d00030300080f043e0050000100f041c04100513a9880302c031451541e40310798200100c01503661020340e20005210b40721403c01d400401c1c022024034040c0d090b0807080c18400b01c4c1c804c0d030311107030503241c2121603d061980340441d04580c40d14102020384040c1c0c000c01c0c0c2c028108103011030221910ba1150382d032400709990750007821100e00a5915144528011005140c01c07542c0c80304007080c012001800c44085070021a400940050354960869280390055000911100800c10910404004505488208550762480c00c902075000300c4900c0c646680003043d000c903800100c3d0341070b80c00307100341c4210b000b07903440500c0041221001c0202c240354104200d961048045d501048400c07051180300240c68809030206c4003084a825841070a0300248002c49007403055001403440c88200d11303046406050340500c404205511502c0c00f4004203c0305802604200350f0400700174204001c103404c1003c503842400c1150b0b6104038003000c200144220381005e14040d0003400141030320348554101c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 892438687 1250 892437437 892437439
    0x4080717010b0d080405060a050706020f04060807030605180702150f010501091a0d02090d080a080a0501090c09090c020106090203090f060108191509020d0c0611030a02060103080a1407060605 84
    0x100540c190002c00902120640000d1326444c4c00b48028003075410260300600c8082110304044e0300307254032a6509004da03840403540001700e420200741000a41e8105c0032a0303401c10312904080c0b103201e04001c04281d588a01401420002601c040482d05041c006d00c030b44d0003030400c071507040181c500e071042c54469a410284030b546c1c00242e2a040000300481070b802803c50741b40200d220b0501e000c880d0000340c4007035003144030710302e50004d0700c6800100003c4601e0010b1040304600d46601e0b101e0310780500f0303080488da4142e10100e0b40c175040c1400d600109503c030355240140d62100d100010f580a42e000b04038014105500f1110760300c1e01c00800d01c43c00325000203c0b00340c18411881100c0190385c0759201962610392800d080240340894420080010360250703805078035100107641c0090300c50030580001e8141401d0b1b107015210940b00400904c0615400b040d20800c0c40c00711401140340c003d07031540095650005100c00b40034000d0102d00d825405108034080c484018901804944405290800600a0606100b09 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 892439937 1250 892438687 892438691
    0x31b0c0e0702010e07050607020612071805041107030f031803090302120f030301060e04090f200a05010e040b04060302030604080a0207090c0905060a200c0102010506040e070312050408071701 84
    0x901c4061050040c2d22400c50200054011146400d081c0901c41d0000b140882e0310081c10312a6203c1c0031000566584140e00c1c41d0f90740e5020038550240c95800b804550800d0b40150b042941e50104080202c0c102d4542a034540f8040000303400ca9241140200140f005c00004409003140f03403424183c1c0030080400b501e00854100d4001b0b403902024907564001000d04049a410510040003024029641c64500c030b00064004181501c1a0381c0302020001d821800300d40c020300c2c4040f04040c0d131041035011200b9040980740385807004c0c10b0034000b81042c0c04030098244900d40301d5070352084c1c0d03449541104004541c0502100c08509141c6003801c000d07041801c140005202e001000202e82890740101d002400c2191695180d0324180424880260700c5100414140001000307400108040c180b882a10003030000042c00840d0303000301c0020309540001c2c050f41c0c81541055003201c001d0101190280481c0e50150748501c0c0c50b43c2e1841c0c19a00c601603a0b1140c07a0318001c254000801e014200e00d9005501e40203402 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 892441187 1250 892439937 892439941
    0x150d0b09011d03210a24060e1002100f0b1003140702010612060e01140a150e1504020705120f090109050d0b040b1f08070828020d031b0c0e 61
    0x183d600d02682d0b06600c90702c000810801c025150806480d5001085110080f41070308680500050302c1c070345c000410007113407a604001c0041d150700c0b0740904400001165000c86210000b20700942e6100c4000d24501c440303665110202480c1d58a50218498000180546035520340e0040c010780102071403110610340082c06c500245a4a1042c4114000c2c1c51143d5003a0620b4221610399030b0081207140e02c44a55507503982c095000b103000c680b548034841c2a498501080815107242000c91820441c1d0025205000c07880078000c02c610400780301107010205480c01600c03108142807071072800e0702444c40e60b034100400040c0c11800b07030244801412800001c0e214a031a0340d40c1e8800f8441c0d014043c0101400f00a0701801180c0007911410700d80740c01c04800c006a000030700310300042d640c0c0701c1e02070341c0201e405500400c403c220004051000c4a8240c5540f118110341139650b03188a404000c2c003580c000e21404550a01c2004c00d40210790140d0750814404401028090314036119581042c10b0040806140503100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 892442437 1250 892441187 892441241
    0x8130806040302120904090f0c080f030418090c0b0406090918031e02120409060905070810150306090f0905010e03180d1403130e01120803150d0b0901 66
    0x14030303074051685a40100f6002d00c81d980c1c5600c0d02e400c44a0101d134443d4651042c0c1c00412000c0820f208440d011383d40c2424900d20380b2106074549070461107485015001484100046030107440c0080d05600d04480200d001402c62504035407461490300940c49a0394040782c00301380309902550321800d444d02a40300b0400c01050616543c007420044000800241c00c845140c801400005462301e80c4c0000d90040394400000c0500c51100707500070742c000310172450b41c03050200304488041c02200c0c0c10001a0400f104142040b050b0b00e030184865001320300f011031a00200c050220710940c0b104000b000303414010803180004011203000f6208840c01551a9801c08107246110324020040700c80b045401842280f19156103000d01180700c0314408182e5150030000300c5150030b00005c0c8010041c284146d82041c4900d405c08030311030074034a41070704003e0408450710b1541001405a50441e5000440345070901c54030046c1800003550b0b1181510003c112005d030105111400c07c0540003803000d00c003203141a4056141c001 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 892443687 1250 892442437 892442443
    0xc0304150507111908071202011815050c1f0e0120031f0315020405031510090f0b0d031d011106181006240203030f0f060301090f081308 60
    0x21400f5140006031050b803070f10f0b840c0a00103000302e000d441108425050380d6481d0380341030901070703441b02c510b8001a43c0c034042103607400407900510780c038000c024a00741c500300004503c0030710390512800d040c403030f0000703041d4078a20302002203150402064000a00102c5142c0d403c50103000440d10400d2290308080e03c0c07618100c400c01a400b0018800c04501e0305580e5a01c0e04480c1a4903c031600c1d6115058114000c80802e0104071800d905a002ca000581c0d501d24110a151800c150800e000ba0160041014003841d188582a03078030440b1031f40c40740440c410840e445500000c0c014502296030200500c00f420080540101e40c24482101d40d14080c00c1c242496801501c510b0518004403606400890006810507100011120301c0e44614003128400c0e80c24414500488070070380c000112000074030b8007240d0f42c0026201800203140c29480a17500b503086c444c00300504406d01500040e01c00b8040c4d000202651000d40c48088103070740081c6018418006401c10b15a503600c050f50b0b00d90413400d04400031405032000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 892444937 1250 892443687 892443697
    0x806090d03150302030115140a060c0609020f0d05100605040b180901200409050105040207020d020405071e050c06100302010c0609060b06040620300d020c03041505 72
    0x9901600c4400080c0360120000e16140c0100030200340c00501c04000341e2000d2042925045000700a005001e040c08104003500000701d046a20400f0042000d20000b40c0c024450744005a1021340030507103040c14400107140c4680720f940b041e04a540314242405018000810030070950054000b04601c544030410300050310204a00710b90000c109a6980321000d0140c01d845034802180e0000041c080401d403018407921030441b44a031000c85010400f40112622442203500402c403c980441c0303840d4055020811008075240e020344590f9481001454076400b5141d100d140740b42d4000b03440110516198050959000700350146041e110390400034910350100b0060005481d0140c58000b0350b003206a031540040c0001e110110342c2c65840c0e001d00c0700030b9216540548043c0c110750322007112903841c00d1a000e00d02c0d0b401c072034542c20b2a071100003090b1444004402280c82d107000c41c40090b2803e10210170608030380c401d2100c2001480d1000030846504600480513105a0322568040e40284091110481e464091 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 892446043 1106 892444937 892444951
    0xd0c050705030105270307023d030e011d12030c09031b010807080114040b03010e06090a15060f060c150e010f0f09080912030d0e0a0308010806 63
    0x1818002040702c0c5d480d00040d82004c0142d00060701029031010003a01e82103010a179030718440040040d84110040034010600c40c505100e20003801020303035088500555180c030700c5c40a51001440702510505074290000d2000c0704010810703000036400034201100c04d1078108810310041d00d01b80961840d0580c9050102c4241420b000090075032880101408104103c4d0301c014088101c0482072026040e034261070003e00c0d04c0300140480d00608560040d040c96105080c200302c0c8031000041d5a040031807142040c89110070044604005840c0326000d8603492200c14807040c005d90b4820140340d0009030141e00740e080300e0052a03500208443d105501a0096516142003144890641c0981385519840c80c2c01040a40f44031b84803844a8001e159041e1303c100f85011420507400e104006903900004e20900c10020b8401051740c8959544001800300d01096018000041401010035903601c04e81c1 = true := by decide +kernel

theorem cover : BRFrame.Cov 892266187 892446043 := by
  have h0 := BRFrame.cov_init 892266187
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 892266187 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 892266187 ≤ n) (h2 : n < 892446043) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
