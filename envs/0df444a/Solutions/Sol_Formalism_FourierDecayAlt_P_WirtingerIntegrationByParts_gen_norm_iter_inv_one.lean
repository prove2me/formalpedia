-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.gen_norm_iter_inv_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:33.912327+00:00
-- url     : https://prove2.me/submissions/f04e7aab-cdaf-4bd5-8b5c-b54ac9e31ef9

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution (i : ℕ) :
    ‖iteratedFDerivWithin ℝ i (Inv.inv : ℝ → ℝ) {0}ᶜ 1‖ = (i.factorial : ℝ) := by
  rw [iteratedFDerivWithin_of_isOpen i isOpen_compl_singleton (by simp : (1 : ℝ) ∈ ({0}ᶜ : Set ℝ)),
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  simp
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
