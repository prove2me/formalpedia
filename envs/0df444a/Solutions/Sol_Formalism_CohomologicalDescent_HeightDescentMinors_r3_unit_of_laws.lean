-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r3_unit_of_laws
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:31.648802+00:00
-- url     : https://prove2.me/submissions/a3abf1f8-d3be-444d-a557-d3d6835b0277

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_q_padic
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_q0_padic
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_pi0_eq_zero
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_q_dvd_q_zero_of_ne_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (ha : ActLaws) (hm : MuFacts) (hq : QMul) : UnitFactorQ := by
  intro l _ O _ _ hl2
  have hp : l.Prime := Fact.out
  obtain ⟨g, hg⟩ := q_dvd_q_zero_of_ne_two l ha hm hq hl2
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hg0 : constantCoeff g = -1 := by
    have h := congrArg constantCoeff hg
    have hq0 : constantCoeff (q0 l ℤ_[l]) = -(l : ℤ_[l]) := by
      rw [q0, map_sub, constantCoeff_pi0_eq_zero, constantCoeff_C, zero_sub]
    have hqc : constantCoeff (q l ℤ_[l]) = (l : ℤ_[l]) := by
      rw [← coeff_zero_eq_constantCoeff_apply, q, coeff_mk]
      simp
    rw [map_mul, hq0, hqc] at h
    have h2 : (l : ℤ_[l]) * constantCoeff g = (l : ℤ_[l]) * (-1) := by rw [← h]; ring
    exact mul_left_cancel₀ hl0 h2
  have hu : IsUnit g := by
    rw [isUnit_iff_constantCoeff, hg0]
    exact isUnit_one.neg
  refine ⟨Units.map (PowerSeries.map (algebraMap ℤ_[l] O) : ℤ_[l]⟦X⟧ →* O⟦X⟧) hu.unit, ?_, ?_⟩
  · rw [Units.coe_map, IsUnit.unit_spec, ← map_q0_padic, ← map_q_padic, hg, map_mul, mul_comm]
    rfl
  · rw [Units.coe_map, IsUnit.unit_spec]
    change constantCoeff (PowerSeries.map (algebraMap ℤ_[l] O) g) = -1
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hg0]
    simp
end Formalism.CohomologicalDescent.HeightDescentMinors
