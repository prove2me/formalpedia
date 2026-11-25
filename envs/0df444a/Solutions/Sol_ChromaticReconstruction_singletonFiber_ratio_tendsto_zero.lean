-- Prove2me | solution 1 for ChromaticReconstruction.singletonFiber_ratio_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:32:46.447307+00:00
-- url     : https://prove2.me/submissions/28256332-f8e3-425f-be1e-5561d973c2a5

import Definitions.Def_RequestProject_Truncation
import Definitions.Def_RequestProject_Theorem2
import Definitions.Def_RequestProject_ProperTree
import Definitions.Def_RequestProject_CountingLimit
import Definitions.Def_RequestProject_TauBound
import Definitions.Def_RequestProject_MainTheorems
import Theorems.Thm_P2M_ChromaticReconstruction_singletonFiber_ratio_tendsto_zero__c04095204a4d


set_option autoImplicit true
open MvPolynomial Finset Filter Topology
open scoped Classical
noncomputable section
open ChromaticReconstruction
namespace ChromaticReconstruction
theorem _root_.solution (t : ℕ) :
    Tendsto (fun k => (singletonFiberCount k t : ℝ) / Nat.card (TreeClass k)) atTop (𝓝 0) :=
  singletonFiber_ratio_tendsto_zero' t
end ChromaticReconstruction
