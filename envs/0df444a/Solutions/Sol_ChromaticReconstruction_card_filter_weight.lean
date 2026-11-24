-- Prove2me | solution 1 for ChromaticReconstruction.card_filter_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:27:55.033559+00:00
-- url     : https://prove2.me/submissions/2e6b6397-ea05-4398-bb0f-5554344cc451

import Definitions.Def_RequestProject_RecoveryThm
import Definitions.Def_RequestProject_WeightedIso

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
variable {K : Type*} [Fintype K]
namespace ChromaticReconstruction
theorem _root_.solution (w : K → ℕ) (a : ℕ) :
    #{x | w x = a} = Multiset.count a (wts w) := by
  rw [wts, Multiset.count_map, card_def, filter_val]
  congr 1
  exact Multiset.filter_congr fun x _ => eq_comm
end ChromaticReconstruction
