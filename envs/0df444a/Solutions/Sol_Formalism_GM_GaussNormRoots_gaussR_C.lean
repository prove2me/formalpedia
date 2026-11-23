-- Prove2me | solution 1 for Formalism.GM.GaussNormRoots.gaussR_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:49:50.38905+00:00
-- url     : https://prove2.me/submissions/d2e654fb-62e5-4d6b-99f3-4150d1a899b7

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieRoots
import Theorems.Thm_Formalism_GM_GaussNormRoots_gaussR_eq_sup_of_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
open Formalism.GM.GaussNormRoots
variable {K : Type} [NormedField K]
namespace Formalism.GM.GaussNormRoots
theorem _root_.solution (ρ : NNReal) (a : K) : gaussR ρ (Polynomial.C a) = ‖a‖₊ := by
  rw [gaussR_eq_sup_of_subset ρ _ {0} (Polynomial.support_C_subset a)]
  simp
end Formalism.GM.GaussNormRoots
