-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x8.map_mulVec_volume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:09:54.295917+00:00
-- url     : https://prove2.me/submissions/22d3e2f3-f778-47cb-b286-2f9e13d82e54

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmHalfIntegralGeneratorMemAlgebraicClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace Formalism.FourierDecayAlt.P.B2x8
theorem _root_.solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.det ≠ 0) :
    (volume : Measure (Fin n → ℂ)).map (fun y => A *ᵥ y) = ENNReal.ofReal ((‖A.det‖ ^ 2)⁻¹) • volume := by
  have hdet : LinearMap.det ((Matrix.toLin' A).restrictScalars ℝ) = ‖A.det‖ ^ 2 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, Complex.normSq_eq_norm_sq]
  have hpos : (0 : ℝ) < ‖A.det‖ ^ 2 := by have := norm_pos_iff.2 hA; positivity
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (Fin n → ℂ))
    (f := (Matrix.toLin' A).restrictScalars ℝ) (by rw [hdet]; exact hpos.ne')
  rw [hdet, abs_of_pos (inv_pos.2 hpos)] at h
  exact h
end Formalism.FourierDecayAlt.P.B2x8
