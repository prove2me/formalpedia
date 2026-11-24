-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.cdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:50:36.126118+00:00
-- url     : https://prove2.me/submissions/7abd509a-d892-43af-b266-34d200fe25f5

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dif
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dx_fd
import Theorems.Thm_PI_UnitaryCorollaryDerivatives_CRH_dif


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution (x : Bool × Mat k r) {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (Dx x f) := by
  rw [dx_fd x (dif hf)]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply (dirL x).contDiff
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
