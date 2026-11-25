-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx8.isRTT_of_entries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:44:04.968803+00:00
-- url     : https://prove2.me/submissions/738640d8-b21a-42cc-b053-8650e7ccd103

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
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_Pf_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_kronecker_E1_E2_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_kronecker_embed_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_mul_Pf_apply


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
namespace Formalism.FourierDecayAlt.P.Qx8
theorem _root_.solution {B : Type} [Ring B] [Algebra ℂ B] (M : ℂ → Matrix (Fin 2) (Fin 2) B)
    (hent : ∀ (u v : ℂ) (i j k l : Fin 2),
      (u - v) • (M u i j * M v k l - M v k l * M u i j) = M u k j * M v i l - M v k j * M u i l) : W.IsRTT M := by
  intro Y Y'
  apply Matrix.ext
  rintro ⟨i, k⟩ ⟨j, l⟩
  rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.smul_apply, Mx6.PC.Pf_mul_apply, Mx6.PC.mul_Pf_apply, Mx6.PC.kronecker_E1_E2_apply, Mx6.PC.kronecker_E1_E2_apply,
    Mx6.PC.kronecker_embed_mul_apply, Mx6.PC.kronecker_embed_mul_apply]
  have h := hent Y' Y i j k l
  rw [smul_sub] at h
  rw [sub_eq_sub_iff_sub_eq_sub]
  exact h
end Formalism.FourierDecayAlt.P.Qx8
