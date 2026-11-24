-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.tuningWeight_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:14:49.823071+00:00
-- url     : https://prove2.me/submissions/8b708b8d-2547-4afb-a442-4aa224af59a7

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdealPowers
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_tuningWeight_fun_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution (m : ℕ) (c c' : ℕ → ℕ) (h : ∀ j, c' j ≤ c j) :
    tuningWeight m (fun j => c j - c' j) = tuningWeight m c - tuningWeight m c' := by
  have h2 : (fun j => (c j - c' j) + c' j) = c := funext fun j => Nat.sub_add_cancel (h j)
  have key : tuningWeight m (fun j => c j - c' j) + tuningWeight m c' = tuningWeight m c := by
    rw [← tuningWeight_fun_add m (fun j => c j - c' j) c', h2]
  omega
end FunctorialResolution.EmbeddedResolution
