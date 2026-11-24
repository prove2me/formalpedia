-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.hasDerivAt_curveL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:06:03.848823+00:00
-- url     : https://prove2.me/submissions/c5eb4e27-4b05-4a93-a09f-362101b40426

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_REAL_tendsto_slope_exp_smul


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
theorem _root_.solution (g : Mat k r) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp (-((s : ℂ) • X0 k r)) * g) (-(X0 k r * g)) 0 := by
  have h := (tendsto_slope_exp_smul (-(X0 k r))).mul_const g
  rw [Matrix.neg_mul] at h
  refine hasDerivAt_iff_tendsto_slope.mpr (h.congr (fun t => ?_))
  simp only [slope_def_module, Matrix.sub_mul, Matrix.smul_mul, smul_neg]
end Formalism.FourierDecayAlt.P.B6
