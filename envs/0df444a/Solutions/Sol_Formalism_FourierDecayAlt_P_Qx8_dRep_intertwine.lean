-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.dRep_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:26:13.138106+00:00
-- url     : https://prove2.me/submissions/8ebfb0e0-1d5e-48d7-8d0b-3e57ec562e2d

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
open Topology
variable {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {Wq : Type*} [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (A : Wq →L[ℂ] Wp) {X X' : Mx k r} {v : Wq}
    (h' : HasDerivAt (fun t : ℝ => π' (NormedSpace.exp ((t : ℂ) • X')) v) (dRep π' X' v) 0)
    (hint : ∀ t : ℝ, A (π' (NormedSpace.exp ((t : ℂ) • X')) v) = π (NormedSpace.exp ((t : ℂ) • X)) (A v)) :
    A (dRep π' X' v) = dRep π X (A v) := by
  have h1 : HasDerivAt (fun t : ℝ => A (π' (NormedSpace.exp ((t : ℂ) • X')) v)) (A (dRep π' X' v)) 0 :=
    (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h'
  unfold dRep at h1 ⊢
  rw [← h1.deriv]
  congr 1
  funext t
  exact hint t
end Formalism.FourierDecayAlt.P.Qx8
