-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.consGrowth_branchPoint_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:44:20.1748+00:00
-- url     : https://prove2.me/submissions/75689d0f-b440-4420-914e-c247412c3688

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchPoint_first
import Theorems.Thm_BKAR_OrderedSimplexParams_tail


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveExtension
variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}
namespace BKAR.Forest.ActiveExtension
theorem _root_.solution (h : ActiveExtension F e)
    (tail : OrderedGrowth h.forest order G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    (h.consGrowth tail).branchPoint u (t :: ts) e = t :=
  (h.consGrowth tail).branchPoint_first u t ts
end BKAR.Forest.ActiveExtension
