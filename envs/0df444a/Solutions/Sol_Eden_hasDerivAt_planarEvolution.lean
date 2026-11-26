-- Prove2me | solution 1 for Eden.hasDerivAt_planarEvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:53:49.444431+00:00
-- url     : https://prove2.me/submissions/a4093df9-a7b7-4e6f-bfe2-fce1987fe2e0

import Definitions.Def_Eden_PlanarVectorField
import Definitions.Def_Eden_DerivativeFrames
import Definitions.Def_Eden_PlanarDerivative
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_blockRotation_apply
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_euclidean_of_coord
import Theorems.Thm_Eden_hasDerivAt_planarX
import Theorems.Thm_Eden_hasDerivAt_planarY
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialAmplitude_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.blockRotation_apply
attribute [local simp] Eden.evolution_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialAmplitude_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time



set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (Ω : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PlanarSpace) :
    HasDerivAt (fun τ => planarEvolution Ω τ p)
      (planarVectorField Ω (planarEvolution Ω t p)) t := by
  apply hasDerivAt_euclidean_of_coord
  intro i
  fin_cases i
  · simpa [planarEvolution, planarVectorField] using hasDerivAt_planarX Ω ht (p 0) (p 1)
  · simpa [planarEvolution, planarVectorField] using hasDerivAt_planarY Ω ht (p 0) (p 1)
end Eden
