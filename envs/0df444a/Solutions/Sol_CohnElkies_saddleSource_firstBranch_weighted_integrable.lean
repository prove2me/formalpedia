-- Prove2me | solution 1 for CohnElkies.saddleSource_firstBranch_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/28f444b4-db28-4c5c-a527-ad39c442adfc

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_nonneg
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_gaussian_integrable
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_exp_abs_integrable
import Theorems.Thm_CohnElkies_saddle_exp_neg_mul_min_le_add
import Theorems.Thm_CohnElkies_saddleSourceTailIntegrand_continuous
import Theorems.Thm_CohnElkies_saddleSourceContourDamping_firstBranch_min_lower_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε ℓ u : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a) :
    Integrable
      (fun T : ℝ =>
        saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T)) := by
  let η : ℝ := 1 + u
  let a : ℝ := ε * ℓ / (2 * Real.exp 1)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hgaussian :=
    saddleGaussianTailWeight_mul_gaussian_integrable
      (div_pos ha hη)
  have hlinear :=
    saddleGaussianTailWeight_mul_exp_abs_integrable ha
  have hmajor := hgaussian.add hlinear
  apply hmajor.mono'
    (saddleSourceTailIntegrand_continuous
      hε hℓ hulower horder).aestronglyMeasurable
  filter_upwards [] with T
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg
      (saddleGaussianTailWeight_nonneg T)
      (Real.exp_pos _).le)]
  have hcoercive :=
    saddleSourceContourDamping_firstBranch_min_lower_bound
      hε hεsmall hℓ hulower huupper horder hmargin T
  have hmin := saddle_exp_neg_mul_min_le_add
    (a := a) (x := T ^ 2 / η) (y := |T|) ha.le
  have hexp :
      Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
        Real.exp (-a * (T ^ 2 / η)) +
          Real.exp (-a * |T|) := by
    calc
      Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
          Real.exp (-a * min (T ^ 2 / η) |T|) := by
            apply Real.exp_le_exp.mpr
            simpa [a, η] using! neg_le_neg hcoercive
      _ ≤ _ := hmin
  change
    saddleGaussianTailWeight T *
        Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
      saddleGaussianTailWeight T *
          Real.exp (-(a / η) * T ^ 2) +
        saddleGaussianTailWeight T *
          Real.exp (-a * |T|)
  have hrearrange :
      -a * (T ^ 2 / η) = -(a / η) * T ^ 2 := by
    ring
  rw [hrearrange] at hexp
  nlinarith [mul_le_mul_of_nonneg_left hexp
    (saddleGaussianTailWeight_nonneg T)]
end CohnElkies
