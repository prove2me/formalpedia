-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.lam_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:53:55.124195+00:00
-- url     : https://prove2.me/submissions/4dbb5b37-f562-439e-bf8f-68600b15f358

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne

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
theorem _root_.solution (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Continuous (fun n : Mat k r => lam k r z n) := by
  unfold lam ell
  refine Complex.continuous_re.comp (continuous_const.mul ?_)
  refine continuous_finsetSum _ fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [h, dif_pos]
    exact continuous_id.matrix_elem _ _
  · simp only [h, dif_neg, not_false_iff]
    have h2 : Continuous fun n : Mat k r => n *ᵥ z := continuous_id.matrix_mulVec continuous_const
    exact (continuous_apply (eI k r a)).comp h2
end Formalism.FourierDecayAlt.P.B6
