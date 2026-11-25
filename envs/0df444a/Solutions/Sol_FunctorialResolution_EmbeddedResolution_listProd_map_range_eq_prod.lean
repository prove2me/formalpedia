-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.listProd_map_range_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:23:37.013923+00:00
-- url     : https://prove2.me/submissions/25b47969-9f21-47b3-ba9f-4e8688827210

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdeal
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_MaximalContactHypersurfaces_TunedIdeal

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
theorem _root_.solution {M : Type*} [CommMonoid M] (f : ℕ → M) (m : ℕ) :
    (List.map f (List.range m)).prod = ∏ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.prod_range_succ]
      simp
end FunctorialResolution.EmbeddedResolution
