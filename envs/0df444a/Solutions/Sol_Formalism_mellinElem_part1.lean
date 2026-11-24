-- Prove2me | solution 1 for Formalism.mellinElem_part1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:30.199649+00:00
-- url     : https://prove2.me/submissions/a02f2ca2-1d27-4a67-9bc6-fae1891c81a5

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinElem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution (a σ : ℝ) (h : a < σ) :
    IntegrableOn (fun x : ℝ => x ^ a * x ^ (-σ - 1)) (Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (a + (-σ - 1))) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
  refine hi.congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (0:ℝ) < x := lt_trans one_pos hx
  simp only
  rw [Real.rpow_add hx0]
end Formalism
