-- Prove2me | solution 1 for CohnElkies.saddleSource_firstBranch_weighted_tail_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.217322+00:00
-- url     : https://prove2.me/submissions/ed7cfeaa-b7c9-42ca-b4f3-cde113a1c12a

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_nonneg
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_gaussian_integrable
import Theorems.Thm_CohnElkies_saddleGaussianTailWeight_mul_exp_abs_integrable
import Theorems.Thm_CohnElkies_saddleGaussianTailSet_measurable
import Theorems.Thm_CohnElkies_saddleGaussian_cubic_tail_integral_le
import Theorems.Thm_CohnElkies_saddleExponential_cubic_tail_integral_le
import Theorems.Thm_CohnElkies_saddle_exp_neg_mul_min_le_add
import Theorems.Thm_CohnElkies_saddleSourceContourDamping_firstBranch_min_lower_bound
import Theorems.Thm_CohnElkies_saddleSource_firstBranch_weighted_integrable

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
    {ε ℓ u R : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ)
    (hulower : -1 < u)
    (huupper : u ≤ 1 + ε / 2)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε)
      (shortEndpoint ε), 0 ≤ shortMargin ε a)
    (hR : 0 ≤ R)
    (hquadratic :
      6 ≤ (ε * ℓ / (2 * Real.exp 1)) / (1 + u))
    (hlinear : 6 ≤ ε * ℓ / (2 * Real.exp 1)) :
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      2 * Real.exp
          (-(((ε * ℓ / (2 * Real.exp 1)) /
            (1 + u)) / 4) * R ^ 2) *
        Real.sqrt
          (Real.pi /
            (((ε * ℓ / (2 * Real.exp 1)) /
              (1 + u)) / 4)) +
      2 * Real.exp
          (-((ε * ℓ / (2 * Real.exp 1)) / 4) * R) *
        (2 / ((ε * ℓ / (2 * Real.exp 1)) / 4)) := by
  let η : ℝ := 1 + u
  let a : ℝ := ε * ℓ / (2 * Real.exp 1)
  have hη : 0 < η := by
    try dsimp [η]
    linarith
  have ha : 0 < a := by
    try dsimp [a]
    positivity
  have hsource := saddleSource_firstBranch_weighted_integrable
    hε hεsmall hℓ hulower huupper horder hmargin
  have hgaussian :=
    saddleGaussianTailWeight_mul_gaussian_integrable
      (div_pos ha hη)
  have hlinearIntegrable :=
    saddleGaussianTailWeight_mul_exp_abs_integrable ha
  have hmajor := hgaussian.add hlinearIntegrable
  have hpoint : ∀ T ∈ saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
          Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
        saddleGaussianTailWeight T *
            Real.exp (-(a / η) * T ^ 2) +
          saddleGaussianTailWeight T *
            Real.exp (-a * |T|) := by
    intro T hT
    have hcoercive :=
      saddleSourceContourDamping_firstBranch_min_lower_bound
        hε hεsmall hℓ hulower huupper horder hmargin T
    have hmin := saddle_exp_neg_mul_min_le_add
      (a := a) (x := T ^ 2 / η) (y := |T|) ha.le
    have hexp :
        Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
          Real.exp (-(a / η) * T ^ 2) +
            Real.exp (-a * |T|) := by
      calc
        Real.exp (-saddleSourceContourDamping ε ℓ u T) ≤
            Real.exp (-a * min (T ^ 2 / η) |T|) := by
              apply Real.exp_le_exp.mpr
              simpa [a, η] using! neg_le_neg hcoercive
        _ ≤ Real.exp (-a * (T ^ 2 / η)) +
            Real.exp (-a * |T|) := hmin
        _ = Real.exp (-(a / η) * T ^ 2) +
            Real.exp (-a * |T|) := by
          have hrearrange :
              -a * (T ^ 2 / η) = -(a / η) * T ^ 2 := by
            ring
          rw [hrearrange]
    nlinarith [mul_le_mul_of_nonneg_left hexp
      (saddleGaussianTailWeight_nonneg T)]
  have hcompare := setIntegral_mono_on
    hsource.integrableOn hmajor.integrableOn
    (saddleGaussianTailSet_measurable R) hpoint
  have hsplit :
      (∫ T : ℝ in saddleGaussianTailSet R,
        (saddleGaussianTailWeight T *
          Real.exp (-(a / η) * T ^ 2) +
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|))) =
        (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-(a / η) * T ^ 2)) +
          ∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|) := by
    rw [integral_add hgaussian.integrableOn
      hlinearIntegrable.integrableOn]
  calc
    (∫ T : ℝ in saddleGaussianTailSet R,
      saddleGaussianTailWeight T *
        Real.exp (-saddleSourceContourDamping ε ℓ u T)) ≤
      ∫ T : ℝ in saddleGaussianTailSet R,
        (saddleGaussianTailWeight T *
          Real.exp (-(a / η) * T ^ 2) +
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|)) := hcompare
    _ = (∫ T : ℝ in saddleGaussianTailSet R,
          saddleGaussianTailWeight T *
            Real.exp (-(a / η) * T ^ 2)) +
          ∫ T : ℝ in saddleGaussianTailSet R,
            saddleGaussianTailWeight T *
              Real.exp (-a * |T|) := hsplit
    _ ≤ 2 * Real.exp (-(a / η / 4) * R ^ 2) *
            Real.sqrt (Real.pi / (a / η / 4)) +
          2 * Real.exp (-(a / 4) * R) *
            (2 / (a / 4)) := by
      gcongr
      · apply saddleGaussian_cubic_tail_integral_le
        · exact hquadratic
        · exact hR
      · apply saddleExponential_cubic_tail_integral_le
        · exact hlinear
        · exact hR
    _ = _ := by rfl
end CohnElkies
