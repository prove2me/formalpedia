-- Prove2me | solution 1 for Eden.hasDerivAt_evolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:32.268193+00:00
-- url     : https://prove2.me/submissions/bc05413c-4864-4f3f-8a7e-5de1613b3824

import Definitions.Def_Eden_PlanarFlow
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FinCases
import Definitions.Def_Eden_Evolution
import Theorems.Thm_Eden_evolution_zero_time
import Theorems.Thm_Eden_hasDerivAt_euclidean_of_coord
import Theorems.Thm_Eden_amplitudeSq_at_zero
import Theorems.Thm_Eden_amplitudeSq_zero_time
import Theorems.Thm_Eden_hasDerivAt_planarX
import Theorems.Thm_Eden_hasDerivAt_planarY
import Theorems.Thm_Eden_planarAmplitude_zero_time
import Theorems.Thm_Eden_planarX_origin
import Theorems.Thm_Eden_planarX_zero_time
import Theorems.Thm_Eden_planarY_origin
import Theorems.Thm_Eden_planarY_zero_time
import Theorems.Thm_Eden_radialDiscriminant_at_two
import Theorems.Thm_Eden_radialDiscriminant_at_zero
import Theorems.Thm_Eden_radialDiscriminant_zero_time
import Theorems.Thm_Eden_squaredRadiusEvolution_at_one
import Theorems.Thm_Eden_squaredRadiusEvolution_at_two
import Theorems.Thm_Eden_squaredRadiusEvolution_at_zero
import Theorems.Thm_Eden_squaredRadiusEvolution_zero_time
attribute [local simp] Eden.amplitudeSq_at_zero
attribute [local simp] Eden.amplitudeSq_zero_time
attribute [local simp] Eden.planarAmplitude_zero_time
attribute [local simp] Eden.planarX_origin
attribute [local simp] Eden.planarX_zero_time
attribute [local simp] Eden.planarY_origin
attribute [local simp] Eden.planarY_zero_time
attribute [local simp] Eden.radialDiscriminant_at_two
attribute [local simp] Eden.radialDiscriminant_at_zero
attribute [local simp] Eden.radialDiscriminant_zero_time
attribute [local simp] Eden.squaredRadiusEvolution_at_one
attribute [local simp] Eden.squaredRadiusEvolution_at_two
attribute [local simp] Eden.squaredRadiusEvolution_at_zero
attribute [local simp] Eden.squaredRadiusEvolution_zero_time


attribute [local simp] Eden.evolution_zero_time

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {t : ℝ} (ht : 0 ≤ t) (p : PhaseSpace) :
    HasDerivAt (fun τ => evolution c τ p) (vectorField c (evolution c t p)) t := by
  apply hasDerivAt_euclidean_of_coord
  intro i
  fin_cases i
  · simpa [evolution, vectorField, radiusSq₁] using
      hasDerivAt_planarX 1 ht (p 0) (p 1)
  · simpa [evolution, vectorField, radiusSq₁] using
      hasDerivAt_planarY 1 ht (p 0) (p 1)
  · simpa [evolution, vectorField, radiusSq₂] using
      hasDerivAt_planarX (Real.sqrt 2) ht (p 2) (p 3)
  · simpa [evolution, vectorField, radiusSq₂] using
      hasDerivAt_planarY (Real.sqrt 2) ht (p 2) (p 3)
  · have hw := (((hasDerivAt_id t).const_mul (-c)).exp).mul_const (p 4)
    simpa [evolution, vectorField, mul_assoc, mul_comm, mul_left_comm] using hw
end Eden
