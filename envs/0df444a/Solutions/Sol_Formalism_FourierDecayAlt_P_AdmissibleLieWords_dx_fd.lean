-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.dx_fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:20:52.868683+00:00
-- url     : https://prove2.me/submissions/749d06f1-e9a3-4209-9da4-a62e0445208f

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdmissibleLieWords_hdx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem dx_eq_deriv_crv (x : Bool × Mat k r) (f : Mat k r → E) (g : Mat k r) :
    Dx x f g = deriv (fun t : ℝ => f (crv x g t)) 0 := by
  rcases x with ⟨b, X⟩
  cases b <;> rfl
private theorem dirL_eq_dirv (x : Bool × Mat k r) (g : Mat k r) : dirL x g = dirv x g := by
  rcases x with ⟨b, X⟩
  cases b <;> first | rfl | simp [dirL, dirv]
section app
variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
end app
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
end
end

set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdmissibleLieWords
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.AdmissibleLieWords
theorem _root_.solution (x : Bool × Mat k r) {f : Mat k r → E} (hf : Differentiable ℝ f) :
    Dx x f = fun g => fderiv ℝ f g (dirL x g) := by
  funext g
  rw [dx_eq_deriv_crv, (hdx x hf g).deriv, dirL_eq_dirv]
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
