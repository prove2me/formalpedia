-- Prove2me | solution 1 for BookProof.OdeUnitaryFlow.lintegral_comp_invMap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:44.131807+00:00
-- url     : https://prove2.me/submissions/c8f6ab93-2200-4254-aed9-222c60d0522f

-- Generated from ChapterOdeUnitaryFlow.lean — solution of BookProof.OdeUnitaryFlow.lintegral_comp_invMap
import Mathlib
import Definitions.Def_ChapterOdeUnitaryFlow
import Theorems.Thm_BookProof_OdeUnitaryFlow_hasDerivAt_invMap
import Theorems.Thm_BookProof_OdeUnitaryFlow_injOn_invMap
import Theorems.Thm_BookProof_OdeUnitaryFlow_image_invMap
open BookProof.OdeUnitaryFlow




open MeasureTheory Filter Set
open scoped Topology ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, ENNReal.ofReal ((x ^ 2)⁻¹) * g (invMap x) = ∫⁻ y, g y := by

  have hmeas : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton (0 : ℝ)).compl
  have hderiv : ∀ x ∈ {x : ℝ | x ≠ 0}, HasDerivWithinAt invMap
      ((fun x : ℝ => (x ^ 2)⁻¹) x) {x : ℝ | x ≠ 0} x := fun x hx =>
    (hasDerivAt_invMap hx).hasDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_deriv_mul hmeas hderiv injOn_invMap g
  rw [image_invMap] at key
  have habs : ∀ x : ℝ, |(x ^ 2)⁻¹| = (x ^ 2)⁻¹ := fun x => abs_of_nonneg (by positivity)
  simp only [habs] at key
  have hae : {x : ℝ | x ≠ 0} =ᵐ[volume] (Set.univ : Set ℝ) := by
    refine ae_eq_univ.mpr ?_
    have : {x : ℝ | x ≠ 0}ᶜ = ({0} : Set ℝ) := by
      ext x; simp
    rw [this]
    simp
  have h1 : ∫⁻ y in {x : ℝ | x ≠ 0}, g y = ∫⁻ y, g y := by
    rw [setLIntegral_congr hae, setLIntegral_univ]
  have h2 : ∫⁻ x in {x : ℝ | x ≠ 0}, ENNReal.ofReal ((x ^ 2)⁻¹) * g (invMap x)
      = ∫⁻ x, ENNReal.ofReal ((x ^ 2)⁻¹) * g (invMap x) := by
    rw [setLIntegral_congr hae, setLIntegral_univ]
  rw [← h2, ← h1, key]
