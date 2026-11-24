-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.dilationAction_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:26:34.057636+00:00
-- url     : https://prove2.me/submissions/aa545f69-c2e8-4668-b900-8fc3498e7e77

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_continuousOn_conj_by_dilation

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
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.B6
theorem _root_.solution (k r : ℕ) :
    ContinuousOn (fun q : SS k r × (ℝ × ℝ) => dilation₂ q.2 q.1) (Set.univ ×ˢ Quad) := by
  unfold dilation₂
  refine ContinuousOn.prodMk (ContinuousOn.prodMk ?_ ?_) (ContinuousOn.prodMk ?_ ?_)
  · exact (continuous_fst.comp (continuous_fst.comp continuous_fst)).continuousOn
  · exact continuousOn_conj_by_dilation k r (fun q => q.1.1.2) (continuous_snd.comp (continuous_fst.comp continuous_fst))
      (fun q => q.2.1) (continuous_fst.comp continuous_snd) (fun q hq => hq.2.1)
  · exact (continuous_fst.comp (continuous_snd.comp continuous_fst)).continuousOn
  · exact continuousOn_conj_by_dilation k r (fun q => q.1.2.2) (continuous_snd.comp (continuous_snd.comp continuous_fst))
      (fun q => q.2.2) (continuous_snd.comp continuous_snd) (fun q hq => hq.2.2)
end Formalism.FourierDecayAlt.P.B6
