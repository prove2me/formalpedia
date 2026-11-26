-- Prove2me | solution 1 for BKAR.Forest.empty_activeDirection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:16:07.897225+00:00
-- url     : https://prove2.me/submissions/f5e5bde9-7dc1-4135-9497-0c1d34610a9d

import Mathlib.Analysis.Calculus.Deriv.Prod
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Differential
import Theorems.Thm_BKAR_Forest_activeDirection_apply_of_mem

set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution :
    (Forest.empty V).activeDirection = oneConfig := by
  funext e
  rw [(Forest.empty V).activeDirection_apply_of_mem]
  · rfl
  · rw [empty_activeEdges]
    exact Finset.mem_univ e
end BKAR.Forest
