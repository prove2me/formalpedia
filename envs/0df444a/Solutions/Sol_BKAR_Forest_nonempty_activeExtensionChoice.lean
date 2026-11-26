-- Prove2me | solution 1 for BKAR.Forest.nonempty_activeExtensionChoice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:21:28.927944+00:00
-- url     : https://prove2.me/submissions/c8299342-5391-4a7a-89e0-493341f0b43a

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_Forest_nonempty_activeExtension_of_mem_activeEdges


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution (V : Type*) [Fintype V] [DecidableEq V] :
    Nonempty (ActiveExtensionChoice V) := by
  classical
  refine ⟨fun F e =>
    Classical.choice (F.nonempty_activeExtension_of_mem_activeEdges e.property)⟩
end BKAR.Forest
