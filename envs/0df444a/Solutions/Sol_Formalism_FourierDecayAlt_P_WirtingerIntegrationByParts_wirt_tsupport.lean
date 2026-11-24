-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.wirt_tsupport
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:55:26.315199+00:00
-- url     : https://prove2.me/submissions/f0cf50fd-ad48-4206-963e-8ce7a5ea9cc2

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_wirt_eq

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {d : ℕ}
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution (k : Fin d) (f : (Fin d → ℂ) → V) : tsupport (wirt k f) ⊆ tsupport f := by
  refine subset_trans ?_ (tsupport_fderiv_subset ℝ (f := f))
  apply closure_mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h; apply hx; rw [wirt_eq]; simp [h]
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
