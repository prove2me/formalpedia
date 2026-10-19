-- Prove2me | solution 1 for CohnElkies.eventually_saddleSource_secondBranch_weighted_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/7ce6055d-17e1-404a-99aa-d428d166e20e

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_nonneg
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_gaussian_integrable
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_exp_abs_integrable
import Theorems.Thm_CohnElkies_saddle_exp_neg_mul_min_le_add
import Theorems.Thm_CohnElkies_saddleSourceTailIntegrand_continuous
import Theorems.Thm_CohnElkies_eventually_saddleSourceContourDamping_secondBranch_min_lower_bound

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology
namespace CohnElkies
theorem _root_.solution :
    ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ∀ ℓ : ℝ, 0 < ℓ →
        ∀ δ : ℝ, ε / 2 ≤ δ →
          Integrable
            (fun T : ℝ =>
              saddleGaussianTailWeight T *
                Real.exp
                  (-saddleSourceContourDamping
                    ε ℓ (1 + δ) T)) := by
  filter_upwards
    [self_mem_nhdsWithin,
      eventually_upper_shortCutoff_le_shortEndpoint,
      eventually_saddleSourceContourDamping_secondBranch_min_lower_bound]
    with ε hε horder hcoercive
  change 0 < ε at hε
  intro ℓ hℓ δ hδ
  let η : ℝ := 2 + δ
  let a : ℝ := ℓ / (8 * Real.exp 1)
  have hδ0 : 0 ≤ δ := by nlinarith
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hu : -1 < 1 + δ := by linarith
  have hgaussian :=
    saddleGaussianTailWeight_mul_gaussian_integrable
      (div_pos ha hη)
  have hlinear :=
    saddleGaussianTailWeight_mul_exp_abs_integrable ha
  have hmajor := hgaussian.add hlinear
  apply hmajor.mono'
    (saddleSourceTailIntegrand_continuous
      hε hℓ hu horder).aestronglyMeasurable
  filter_upwards [] with T
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg
      (saddleGaussianTailWeight_nonneg T)
      (Real.exp_pos _).le)]
  have hsource := hcoercive ℓ hℓ δ hδ T
  have hmin := saddle_exp_neg_mul_min_le_add
    (a := a) (x := T ^ 2 / η) (y := |T|) ha.le
  have hexp :
      Real.exp
          (-saddleSourceContourDamping ε ℓ (1 + δ) T) ≤
        Real.exp (-(a / η) * T ^ 2) +
          Real.exp (-a * |T|) := by
    calc
      Real.exp
          (-saddleSourceContourDamping ε ℓ (1 + δ) T) ≤
        Real.exp (-a * min (T ^ 2 / η) |T|) := by
          apply Real.exp_le_exp.mpr
          simpa [a, η] using! neg_le_neg hsource
      _ ≤ Real.exp (-a * (T ^ 2 / η)) +
          Real.exp (-a * |T|) := hmin
      _ = Real.exp (-(a / η) * T ^ 2) +
          Real.exp (-a * |T|) := by
        congr 2
        ring
  change
    saddleGaussianTailWeight T *
        Real.exp
          (-saddleSourceContourDamping ε ℓ (1 + δ) T) ≤
      saddleGaussianTailWeight T *
          Real.exp (-(a / η) * T ^ 2) +
        saddleGaussianTailWeight T *
          Real.exp (-a * |T|)
  nlinarith [mul_le_mul_of_nonneg_left hexp
    (saddleGaussianTailWeight_nonneg T)]
end CohnElkies
