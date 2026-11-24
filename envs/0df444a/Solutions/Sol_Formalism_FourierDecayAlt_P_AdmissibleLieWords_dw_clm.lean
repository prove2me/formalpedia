-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.dw_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:29:19.599909+00:00
-- url     : https://prove2.me/submissions/d530c0d5-a42f-41b6-906a-606af2b1b85c

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dif
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_cdw
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dx_clm
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
theorem _root_.solution {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (L : E →L[ℝ] E₂) (w : List (Bool × Mat k r))
    {f : Mat k r → E} (hf : ContDiff ℝ ∞ f) : Dw w (fun g => L (f g)) = fun g => L (Dw w f g) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => L (f g)) = fun g => L (Dx x (Dw w f) g)
    rw [ih]
    exact dx_clm L x (dif (cdw w hf))
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
