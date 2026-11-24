-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.dx_app
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:00.127481+00:00
-- url     : https://prove2.me/submissions/91c8c4a2-5876-48f1-8734-895f6ed55100

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
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution (x : Bool × Mat k r) {a : Mat k r → (F →L[ℝ] E)} {b : Mat k r → F} (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) :
    Dx x (fun g => a g (b g)) = fun g => Dx x a g (b g) + a g (Dx x b g) := by
  rw [dx_fd x (ha.clm_apply hb), dx_fd x ha, dx_fd x hb]
  funext g
  have h2 := congrArg (fun T => T (dirL x g)) (fderiv_clm_apply (ha g) (hb g))
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply] at h2
  exact h2.trans (add_comm _ _)
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
