-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.lintegral_comp_mob
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:58:31.46911+00:00
-- url     : https://prove2.me/submissions/af1521f0-2e74-4b83-920e-f0e03c22963e

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.lintegral_comp_mob
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_measurableSet_flowDom
import Theorems.Thm_BookProof_OdeUnitaryFlow_volume_compl_flowDom
import Theorems.Thm_BookProof_OdeUnitaryFlow_hasDerivAt_mob
import Theorems.Thm_BookProof_OdeUnitaryFlow_injOn_mob
import Theorems.Thm_BookProof_OdeUnitaryFlow_image_mob
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (t : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal ((1 + t * x) ^ 2)⁻¹ * g (mob t x) = ∫⁻ y, g y := by

  have hderiv : ∀ x ∈ flowDom t, HasDerivWithinAt (mob t)
      ((fun x : ℝ => ((1 + t * x) ^ 2)⁻¹) x) (flowDom t) x := fun x hx =>
    (hasDerivAt_mob t x hx).hasDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_flowDom t) hderiv
    (injOn_mob t) g
  rw [image_mob t] at key
  have habs : ∀ x : ℝ, |((1 + t * x) ^ 2)⁻¹| = ((1 + t * x) ^ 2)⁻¹ := fun x =>
    abs_of_nonneg (by positivity)
  simp only [habs] at key
  have hae : ∀ s : ℝ, flowDom s =ᵐ[volume] (Set.univ : Set ℝ) := fun s =>
    ae_eq_univ.mpr (volume_compl_flowDom s)
  have h1 : ∫⁻ y in flowDom (-t), g y = ∫⁻ y, g y := by
    rw [setLIntegral_congr (hae (-t)), setLIntegral_univ]
  have h2 : ∫⁻ x in flowDom t, ENNReal.ofReal ((1 + t * x) ^ 2)⁻¹ * g (mob t x)
      = ∫⁻ x, ENNReal.ofReal ((1 + t * x) ^ 2)⁻¹ * g (mob t x) := by
    rw [setLIntegral_congr (hae t), setLIntegral_univ]
  rw [← h2, ← h1, key]
