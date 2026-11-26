-- Prove2me | solution 1 for BKAR.Forest.ActiveExtension.consGrowth_params_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:21:19.27075+00:00
-- url     : https://prove2.me/submissions/a686d3b2-5542-4f81-80f0-55f88e36113c

import Definitions.Def_BKAR_OrderedTerminal
import Definitions.Def_BKAR_OrderedRecursion
import Theorems.Thm_BKAR_Forest_OrderedGrowth_mem_edges_of_mem_order
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_first
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
    (h.consGrowth tail).params u (t :: ts)
        ⟨e, (h.consGrowth tail).mem_edges_of_mem_order
          (by rw [List.mem_cons]; exact Or.inl rfl)⟩ = t :=
  (h.consGrowth tail).params_first u t ts
end BKAR.Forest.ActiveExtension
