-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.dw_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:29:25.631022+00:00
-- url     : https://prove2.me/submissions/8ba4f024-917f-493c-9389-51cadfd7d8ab

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dif
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_cdw
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dx_add
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
theorem _root_.solution (w : List (Bool × Mat k r)) {a b : Mat k r → E} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Dw w (fun g => a g + b g) = fun g => Dw w a g + Dw w b g := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w fun g => a g + b g) = fun g => Dx x (Dw w a) g + Dx x (Dw w b) g
    rw [ih]
    exact dx_add x (dif (cdw w ha)) (dif (cdw w hb))
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
