-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.eigen_bessel_from_commuting_operators
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:57:51.076332+00:00
-- url     : https://prove2.me/submissions/1db4b537-ae8d-4a82-aa36-786ba2c5a7b0

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_CCle_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx8_JF_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_ae_mem_good_set_restrict
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_gq_mem


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx8
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.Q.EigenBesselFromCommutes := by
  intro hBC hLin k r Wp Wq _ _ _ _ _ _ D A m F Y PY hm hA hF hE
  have hCV : B.InCC A m (CV k r Y F) := by
    obtain ⟨c, hc⟩ := hF
    exact ⟨_, CCle_congr (f := PY • F) (fun g hg => (hE g hg).symm) (hLin k r _ A m F F c c PY hc hc).2⟩
  obtain ⟨Jt, h1, h2, h3, h4, h5, h6⟩ := hBC k r Wp Wq D A m F Y hm hA hF hCV
  refine ⟨Jt, h1, h2, h3, h4, h5, ?_⟩
  filter_upwards [h5, h6, B7.ae_mem_good_set_restrict D] with q a5 a6 hq
  rw [a6, a5]
  exact JF_congr D hE (B7.gq_mem D hq)
end Formalism.FourierDecayAlt.P
