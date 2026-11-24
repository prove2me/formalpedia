-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.inv_pow_lim
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:55.57125+00:00
-- url     : https://prove2.me/submissions/ff6c2ab3-85ed-4190-bec1-bdbadea7431f

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open Filter Topology Finset
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (t : ℕ) (ht : 1 ≤ t) : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ t) atTop (𝓝 0) := by
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).pow t
  rw [zero_pow (by omega)] at h
  refine h.congr' ?_
  filter_upwards with n
  rw [div_pow, one_pow]
end Formalism.GM.leadingTermLemmas
