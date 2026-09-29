-- Prove2me | solution 1 for EulerMascheroni.P2.gamma_irrational_of_arithmetic
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T00:14:23.398266+00:00
-- url     : https://prove2.me/submissions/b36444a6-de4d-42df-a443-d1c92f980ea8

import Definitions.Def_eulerMascheroni_p2Approximation
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Filter Topology
open EulerMascheroni.P2

/-- The explicit missing arithmetic input: an integer normalization whose
scaled saddle envelope tends to zero. No such normalization is asserted to exist. -/
theorem solution
    (hnum : Tendsto (fun n : ℕ => F (n+1) / fModel (n+1) - Real.sin (phase (n+1)))
      atTop (nhds 0))
    (hphase : ∃ᶠ n : ℕ in atTop, (1/2 : ℝ) ≤ |Real.sin (phase (n+1))|)
    (p q : ℕ → ℤ) (c : ℕ → ℝ)
    (hc : ∀ n, c n ≠ 0)
    (hp : ∀ n, (p n : ℝ) = c n * (P (n+1) : ℝ))
    (hq : ∀ n, (q n : ℝ) = c n * (Q (n+1) : ℝ))
    (hsmall : Tendsto (fun n => c n * fModel (n+1)) atTop (nhds 0)) :
    Irrational Real.eulerMascheroniConstant := by
  let v : ℕ → ℝ := fun n => F (n+1) / fModel (n+1) - Real.sin (phase (n+1))
  let L : ℕ → ℝ := fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ)
  have hv : Tendsto v atTop (nhds 0) := hnum
  have hav : Tendsto (fun n => |v n|) atTop (nhds 0) := by simpa using hv.abs
  have hev : ∀ᶠ n in atTop, |v n| < 1/4 :=
    hav.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/4))
  have hfm (n : ℕ) : fModel (n+1) ≠ 0 := by
    have hs : 0 < scale (n+1) := by unfold scale; positivity
    unfold fModel
    positivity
  have hL (n : ℕ) : L n = (c n * fModel (n+1)) *
      (Real.sin (phase (n+1)) + v n) := by
    dsimp [L, v]
    rw [hp n, hq n]
    unfold F
    field_simp [hfm n]
    <;> ring
  have hlim : Tendsto L atTop (nhds 0) := by
    apply squeeze_zero_norm' (a := fun n => 2 * |c n * fModel (n+1)|)
    · filter_upwards [hev] with n hn
      rw [Real.norm_eq_abs, hL, abs_mul]
      have hsin := Real.abs_sin_le_one (phase (n+1))
      have hadd := abs_add_le (Real.sin (phase (n+1))) (v n)
      nlinarith [abs_nonneg (c n * fModel (n+1))]
    · simpa using hsmall.abs.const_mul 2
  have hfreq : ∃ᶠ n in atTop, L n ≠ 0 := by
    apply (hphase.and_eventually hev).mono
    rintro n ⟨hn, hvn⟩
    have hnz : Real.sin (phase (n+1)) + v n ≠ 0 := by
      intro hz
      have heq : Real.sin (phase (n+1)) = -v n := by linarith
      rw [heq, abs_neg] at hn
      linarith
    rw [hL]
    exact mul_ne_zero (mul_ne_zero (hc n) (hfm n)) hnz
  rintro ⟨r, hr⟩
  have hd : (0 : ℝ) < (r.den : ℝ) := by exact_mod_cast r.pos
  have hrr : Real.eulerMascheroniConstant = (r.num : ℝ) / (r.den : ℝ) := by
    rw [← hr]
    exact_mod_cast (Rat.num_div_den r).symm
  have hrepr (n : ℕ) : L n =
      ((q n * r.num - p n * (r.den : ℤ) : ℤ) : ℝ) / (r.den : ℝ) := by
    dsimp [L]
    rw [hrr]
    push_cast
    field_simp
  have habs : Tendsto (fun n => |L n|) atTop (nhds 0) := by simpa using hlim.abs
  obtain ⟨n, hn, hnsmall⟩ := (hfreq.and_eventually
    (habs.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (r.den : ℝ) by positivity)))).exists
  have hZ : q n * r.num - p n * (r.den : ℤ) ≠ 0 := by
    intro hz
    apply hn
    rw [hrepr n, hz]
    simp
  have h1 : (1 : ℝ) ≤ |((q n * r.num - p n * (r.den : ℤ) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hZ
  have hbound : 1 / (r.den : ℝ) ≤ |L n| := by
    rw [hrepr n, abs_div, abs_of_pos hd]
    exact div_le_div_of_nonneg_right h1 hd.le
  exact (not_lt_of_ge hbound) hnsmall

#print axioms solution
