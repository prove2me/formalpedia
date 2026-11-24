-- Prove2me | solution 1 for ChromaticReconstruction.vx_val
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:24:28.231551+00:00
-- url     : https://prove2.me/submissions/d1715e41-e9b6-4283-ab07-b90c37a7ce6d

import Definitions.Def_RequestProject_Forest
import Definitions.Def_RequestProject_PathLeaf

set_option autoImplicit true
open Finset
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (n x : ℕ) : (vx n x).val = min x n := rfl
end ChromaticReconstruction
