-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B6.setting_support_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T16:09:39.591799+00:00
-- url     : https://prove2.me/submissions/7173ef36-f991-4a2e-9c1e-9c23c6d6c1c2

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdjointnessPolynomiallyBounded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnitaryEquivHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_isClosed_Nset
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_isClosed_UWset

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
theorem _root_.solution (D : RealPlaceData k r Wp Wq) : IsClosed {p : SS k r | D.inSS p} := by
  have c1 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z} := isClosed_UWset k r D.z
  have c2 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ Nset k r} := isClosed_Nset k r
  have c3 : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z'} := isClosed_UWset k r D.z'
  unfold RealPlaceData.inSS
  refine IsClosed.and (c1.preimage (continuous_fst.comp continuous_fst))
    (IsClosed.and (c2.preimage (continuous_snd.comp continuous_fst))
      (IsClosed.and (c3.preimage (continuous_fst.comp continuous_snd))
        (c2.preimage (continuous_snd.comp continuous_snd))))
end Formalism.FourierDecayAlt.P.B6
