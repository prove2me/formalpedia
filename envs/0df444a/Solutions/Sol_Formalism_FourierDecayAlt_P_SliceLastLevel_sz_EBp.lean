-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SliceLastLevel.sz_EBp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:14:04.343808+00:00
-- url     : https://prove2.me/submissions/090e98f7-36fd-423b-80d0-a9374ad4a6e3

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Pr_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux5_EB_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.Ux5
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
theorem _root_.solution {ι κ : Type*} {m : ℕ} {A : Matrix ι (Fin m) ℂ} {B : Matrix (Fin m) κ ℂ} {Q G : ℝ} (hQ : 0 ≤ Q)
    (hG : 0 ≤ G) {i j i' j' : ℕ} (hA : EB A (Q ^ i * G ^ j)) (hB : EB B (Q ^ i' * G ^ j')) (hm : (m : ℝ) ≤ Q) :
    EB (A * B) (Q ^ (i + i' + 1) * G ^ (j + j')) := by
  refine (EB_mul hA hB).mono ?_
  rw [Fintype.card_fin]
  calc (m : ℝ) * (Q ^ i * G ^ j * (Q ^ i' * G ^ j')) ≤ Q * (Q ^ i * G ^ j * (Q ^ i' * G ^ j')) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
    _ = Q ^ (i + i' + 1) * G ^ (j + j') := by ring
end Formalism.FourierDecayAlt.P.SliceLastLevel
