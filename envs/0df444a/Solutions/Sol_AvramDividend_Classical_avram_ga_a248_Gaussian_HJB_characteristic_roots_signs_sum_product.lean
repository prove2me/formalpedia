-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a248_Gaussian_HJB_characteristic_roots_signs_sum_product
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:40:44.777971+00:00
-- url     : https://prove2.me/submissions/81bfae63-f1b8-4fb6-8c05-7d5f71a0b5a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem solution
    (sigma c q : ℝ) (hSigma : 0 < sigma) (hq : 0 < q) :
    let root : ℝ := Real.sqrt (c^2+2*q*sigma^2)
    let lambdaPlus : ℝ := (-c+root)/sigma^2
    let lambdaMinus : ℝ := (-c-root)/sigma^2
    0 < lambdaPlus ∧ lambdaMinus < 0 ∧
    lambdaPlus+lambdaMinus = -2*c/sigma^2 ∧
    lambdaPlus*lambdaMinus = -2*q/sigma^2 := by
  dsimp
  have hSigmaSq : 0 < sigma^2 := sq_pos_of_pos hSigma
  have hD0 : 0 ≤ c^2+2*q*sigma^2 := by positivity
  have hD2 : (Real.sqrt (c^2+2*q*sigma^2))^2 =
      c^2+2*q*sigma^2 := Real.sq_sqrt hD0
  have hDpos : 0 < Real.sqrt (c^2+2*q*sigma^2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg c]
  have hAbove : c < Real.sqrt (c^2+2*q*sigma^2) := by
    nlinarith
  have hBelow : -c < Real.sqrt (c^2+2*q*sigma^2) := by
    nlinarith
  have hp : 0 < (-c+Real.sqrt (c^2+2*q*sigma^2))/sigma^2 := by
    exact div_pos (by linarith) hSigmaSq
  have hm : (-c-Real.sqrt (c^2+2*q*sigma^2))/sigma^2 < 0 := by
    exact div_neg_of_neg_of_pos (by linarith) hSigmaSq
  refine ⟨hp,hm,?_,?_⟩
  · field_simp [ne_of_gt hSigmaSq]
    ring
  · field_simp [ne_of_gt hSigmaSq]
    nlinarith [hD2]
