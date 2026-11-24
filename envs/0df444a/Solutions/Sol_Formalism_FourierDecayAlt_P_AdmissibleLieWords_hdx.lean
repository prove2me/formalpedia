-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdmissibleLieWords.hdx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:01:20.633669+00:00
-- url     : https://prove2.me/submissions/7fc0314e-2272-4f35-a7f4-72af3be4e92d

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_CompRB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplLen
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_crv_zero


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
theorem _root_.solution (x : Bool × Mat k r) {f : Mat k r → E} (hf : Differentiable ℝ f) (g : Mat k r) :
    HasDerivAt (fun t : ℝ => f (crv x g t)) (fderiv ℝ f g (dirv x g)) 0 := by
  have hd : HasFDerivAt f (fderiv ℝ f g) (crv x g 0) := by
    rw [crv_zero]
    exact (hf g).hasFDerivAt
  exact hd.comp_hasDerivAt 0 (crv_hasDerivAt x g)
end Formalism.FourierDecayAlt.P.AdmissibleLieWords
