-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.dx_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:42:22.982581+00:00
-- url     : https://prove2.me/submissions/195596fc-298a-43bd-a3b0-78d4409b9ff5

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_dx_fd

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
theorem _root_.solution (x : Bool × Mat k r) {a b : Mat k r → E} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    Dx x (fun g => a g + b g) = fun g => Dx x a g + Dx x b g := by
  rw [dx_fd x (f := fun g => a g + b g) (ha.add hb), dx_fd x ha, dx_fd x hb]
  funext g
  exact congrArg (fun T => T (dirL x g)) (fderiv_add (ha g) (hb g))
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
