-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.dx_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:42:17.171266+00:00
-- url     : https://prove2.me/submissions/6bddca0d-d3b8-4b84-aec1-986b88d9f07c

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
theorem _root_.solution (x : Bool × Mat k r) {ψ : Mat k r → F} {Φ : F → E} (hψ : Differentiable ℝ ψ)
    (hΦ : Differentiable ℝ Φ) : Dx x (fun g => Φ (ψ g)) = fun g => fderiv ℝ Φ (ψ g) (Dx x ψ g) := by
  rw [dx_fd x (f := fun g => Φ (ψ g)) (hΦ.comp hψ), dx_fd x hψ]
  funext g
  rw [show (fun g => Φ (ψ g)) = Φ ∘ ψ from rfl]
  exact congrArg (fun T => T (dirL x g)) (fderiv_comp g (hΦ (ψ g)) (hψ g))
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
