-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.curveL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:22:28.911804+00:00
-- url     : https://prove2.me/submissions/6ad19c30-ba36-430f-a699-894e242a86d0

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_exp_neg_dilation_generator_eq_aDil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_mul_eq_mul_aDil
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_hasDerivAt_log_difference_scaled
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_exp_log_ratio

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Mat k r → E) (z : Mat k r) {x : ℝ}
    (hx : 0 < x) {d : E}
    (h : HasDerivAt (fun s : ℝ => f (NormedSpace.exp (-((s : ℂ) • X0 k r)) * (aDil k r x * z))) d 0) :
    HasDerivAt (fun x' : ℝ => f (aDil k r x' * z)) ((-(rr r / x)) • d) x := by
  have h0 : rr r * (Real.log x - Real.log x) = 0 := by simp
  have hc := HasDerivAt.scomp_of_eq x h (hasDerivAt_log_difference_scaled r hx) h0.symm
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with x' hx'
  simp only [Function.comp]
  have e : Real.exp (-(rr r * (Real.log x - Real.log x')) / rr r) = x' / x := by
    rw [show -(rr r * (Real.log x - Real.log x')) = rr r * (Real.log x' - Real.log x) by ring]
    exact exp_log_ratio r hx' hx
  rw [exp_neg_dilation_generator_eq_aDil, e, ← Matrix.mul_assoc, ← aDil_mul_eq_mul_aDil]
  congr 3
  field_simp
end Formalism.FourierDecayAlt.P.B6
