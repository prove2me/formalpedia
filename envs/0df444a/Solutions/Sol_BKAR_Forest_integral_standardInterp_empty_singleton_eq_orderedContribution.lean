-- Prove2me | solution 1 for BKAR.Forest.integral_standardInterp_empty_singleton_eq_orderedContribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:59:14.484581+00:00
-- url     : https://prove2.me/submissions/6d04ae52-8ae1-4478-a9b7-070160dc657b

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse
import Theorems.Thm_BKAR_orderedSimplexIntegral_singleton


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (G : Forest V) (e : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    (∫ t in 0..(1 : ℝ),
        mixedPartialList [e].reverse ρ
          (G.standardInterp (G.paramsOfOrder [e] [t]))) =
      G.orderedContribution [e] ρ := by
  rw [orderedContribution, orderedSimplexIntegral_singleton]
end BKAR.Forest
