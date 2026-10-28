-- Prove2me | solution 1 for DataDrivenNV.LRS.theorem2_improved_lrs_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-27T06:27:02.308744+00:00
-- url     : https://prove2.me/submissions/f931c3a8-a17a-41b6-a393-2dc3344c86b6

import Theorems.Thm_DataDrivenNV_LRS_lrsSet_subset_epsOptimal
import Theorems.Thm_DataDrivenNV_LRS_propEC1_derivatives_near_zero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory DataDrivenNV.LRS

theorem solution (b h : ℝ) (hb : 0 < b) (hh : 0 < h)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (N : ℕ) (hN : 1 ≤ N) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (Measure.pi fun _ : Fin N => μ)
        {x : Fin N → ℝ | ¬ IsEpsOptimal μ b h ε (saaQuantile b h x)} ≤
      ENNReal.ofReal
        (2 * Real.exp (-((N : ℝ) * ε ^ 2 / (18 + 8 * ε) * (min b h / (b + h))))) := by
  let m := min b h
  let γ := ε / 3 * m
  have hm : 0 < m := lt_min hb hh
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hS : 0 < b+h := add_pos hb hh
  have hB := propEC1_derivatives_near_zero b h hb hh μ N hN γ hγ
  have hsub : {x : Fin N → ℝ | ¬ IsEpsOptimal μ b h ε (saaQuantile b h x)} ⊆
      {x | ¬ (dMinus μ b h (saaQuantile b h x) ≤ γ ∧
        -γ ≤ dPlus μ b h (saaQuantile b h x))} := by
    intro x hx hd
    exact hx (lrsSet_subset_epsOptimal b h hb hh μ hμ ε hε hε1 hd)
  refine (measure_mono hsub).trans (hB.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  apply neg_le_neg
  have hmh : b*h ≤ m*(b+h) := by
    dsimp [m]
    rcases le_total b h with hbh|hhb
    · rw [min_eq_left hbh]
      nlinarith [sq_nonneg b]
    · rw [min_eq_right hhb]
      nlinarith [sq_nonneg h]
  have hD : 0 < 18*b*h+8*ε*m*(b+h) := by positivity
  have hE : 0 < (18+8*ε)*m*(b+h) := by positivity
  have hDE : 18*b*h+8*ε*m*(b+h) ≤ (18+8*ε)*m*(b+h) := by
    nlinarith only [hmh]
  have hf := div_le_div_of_nonneg_left
    (show 0 ≤ (N:ℝ)*ε^2*m^2 by positivity) hD hDE
  have heq1 : (N:ℝ)*ε^2*m^2/((18+8*ε)*m*(b+h)) =
      (N:ℝ)*ε^2/(18+8*ε)*(min b h/(b+h)) := by
    have hp : 18+8*ε ≠ 0 := by positivity
    change (N:ℝ)*ε^2*m^2/((18+8*ε)*m*(b+h)) =
      (N:ℝ)*ε^2/(18+8*ε)*(m/(b+h))
    field_simp [hm.ne',hS.ne',hp]
    <;> ring
  have heq2 : (N:ℝ)*ε^2*m^2/(18*b*h+8*ε*m*(b+h)) =
      3*(N:ℝ)*γ^2/(6*b*h+8*γ*(b+h)) := by
    have hG : 0 < 6*b*h+8*γ*(b+h) := by positivity
    apply (div_eq_div_iff hD.ne' hG.ne').mpr
    dsimp [γ]
    ring
  rw [heq1,heq2] at hf
  exact hf
