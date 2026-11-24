-- Prove2me | solution 1 for Formalism.ZRN.summable_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:13:31.731113+00:00
-- url     : https://prove2.me/submissions/18b5abef-f311-4165-9841-a872b77148a3

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Theorems.Thm_Formalism_ZRN_e_dom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Filter Topology
noncomputable section
open Formalism
open Formalism.ZRN
namespace Formalism.ZRN
theorem _root_.solution (s : ℂ) (h : 0 < s.re) : Summable (fun n => e n s) := by
  obtain ⟨r, hr, u, hu, hb⟩ := e_dom s h
  exact Summable.of_norm_bounded hu (fun n => hb n s (Metric.mem_ball_self hr))
end Formalism.ZRN
