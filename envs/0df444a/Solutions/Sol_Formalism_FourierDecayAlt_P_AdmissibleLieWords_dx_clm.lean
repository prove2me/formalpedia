-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.dx_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:16.545747+00:00
-- url     : https://prove2.me/submissions/15b01f6f-7089-4625-8d90-2f49d94662af

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
theorem _root_.solution {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℂ E₂] (L : E →L[ℝ] E₂) (x : Bool × Mat k r)
    {f : Mat k r → E} (hf : Differentiable ℝ f) : Dx x (fun g => L (f g)) = fun g => L (Dx x f g) := by
  rw [dx_fd x (f := fun g => L (f g)) (L.differentiable.comp hf), dx_fd x hf]
  funext g
  have h := (L.hasFDerivAt.comp g (hf g).hasFDerivAt).fderiv
  rw [show (fun g => L (f g)) = ⇑L ∘ f from rfl]
  exact congrArg (fun T => T (dirL x g)) h
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
