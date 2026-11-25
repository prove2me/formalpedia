-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.piL_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T02:03:33.109123+00:00
-- url     : https://prove2.me/submissions/3a27c1b5-a018-47f5-964b-2ee57bc9492c

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_IsLin_map_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_prod
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx8_Ent_prod


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
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {W ι : Type*} [AddCommGroup W] [Module ℂ W] (L : ι → W → W) (hL : ∀ τ, IsLin (L τ)) (c ν : ι → ℂ)
    {x : W} (hx : ∀ τ, L τ x = ν τ • x) (l : List ι) :
    piL L c l x = (l.map fun τ => ν τ - c τ).prod • x := by
  induction l with
  | nil => simp [piL]
  | cons τ l ih =>
    show L τ (piL L c l x) - c τ • piL L c l x = _
    rw [ih, (hL τ).map_smul, hx, List.map_cons, List.prod_cons, smul_smul, smul_smul, ← sub_smul]
    congr 1
    ring
end Formalism.FourierDecayAlt.P.Qx8
