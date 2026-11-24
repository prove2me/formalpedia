-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.curveR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:06:00.517226+00:00
-- url     : https://prove2.me/submissions/9cbaa535-efd7-40cb-a5b4-5f8e7f29650d

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_exp_dilation_generator_eq_aDil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_mul_eq_mul_aDil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hasDerivAt_log_difference_scaled
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_exp_log_ratio
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2_aDil_inv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_aDil_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Mat k r → E) (z : Mat k r) {y : ℝ}
    (hy : 0 < y) {d : E}
    (h : HasDerivAt (fun s : ℝ => f (z * (aDil k r y)⁻¹ * NormedSpace.exp ((s : ℂ) • X0 k r))) d 0) :
    HasDerivAt (fun y' : ℝ => f (z * (aDil k r y')⁻¹)) ((-(rr r / y)) • d) y := by
  have h0 : rr r * (Real.log y - Real.log y) = 0 := by simp
  have hc := HasDerivAt.scomp_of_eq y h (hasDerivAt_log_difference_scaled r hy) h0.symm
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hy] with y' hy'
  simp only [Function.comp]
  rw [exp_dilation_generator_eq_aDil, exp_log_ratio r hy hy', B2.aDil_inv k r y hy.ne', B2.aDil_inv k r y' hy'.ne', Matrix.mul_assoc,
    ← aDil_mul_eq_mul_aDil]
  congr 3
  field_simp
end Formalism.FourierDecayAlt.P.B6
