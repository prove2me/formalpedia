-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.aDil_inv_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:25:56.424612+00:00
-- url     : https://prove2.me/submissions/c579385f-b52b-455b-b986-689ff9dee1f5

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_aDil_continuousOn
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
theorem _root_.solution (k r : ℕ) : ContinuousOn (fun t : ℝ => (aDil k r t)⁻¹) (Set.Ioi 0) := by
  have h : ContinuousOn (fun t : ℝ => aDil k r t⁻¹) (Set.Ioi 0) := by
    refine (aDil_continuousOn k r).comp (continuousOn_inv₀.mono ?_) ?_
    · intro t ht; exact ne_of_gt ht
    · intro t ht; exact inv_pos.2 (Set.mem_Ioi.1 ht)
  refine h.congr ?_
  intro t ht
  exact B2.aDil_inv k r t (ne_of_gt ht)
end Formalism.FourierDecayAlt.P.B6
