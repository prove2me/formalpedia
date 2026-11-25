-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.rho_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:47:19.066689+00:00
-- url     : https://prove2.me/submissions/1c0f6168-ab81-4396-b2ee-296114d859d9

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_anti_of_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_types_interlace


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.M
variable {P : M.Par}
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution (h : P.OK) (π : Ty P) : ∀ i j, 1 ≤ i → i < j → j ≤ P.k - 1 → rho P π j < rho P π i := by
  apply anti_of_step
  intro i hi hn
  have hI := types_interlace P h π
  have h1 := hI i (Finset.mem_Icc.2 ⟨hi, by omega⟩)
  have h2 := hI (i + 1) (Finset.mem_Icc.2 ⟨by omega, hn⟩)
  linarith [h1.2.2.1, h2.1]
end Formalism.FourierDecayAlt.P.Qx8
