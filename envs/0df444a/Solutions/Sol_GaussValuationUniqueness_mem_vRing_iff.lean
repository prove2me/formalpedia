-- Prove2me | solution 1 for GaussValuationUniqueness.mem_vRing_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:39.752302+00:00
-- url     : https://prove2.me/submissions/69a95c80-2abd-4f65-8c84-1b535d8bb9ae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtLeafSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_ExistsSmulOfLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GaussValuationUniqueness
open ReciprocityTheory.ChartRestriction.G.T0
namespace GaussValuationUniqueness
theorem _root_.solution {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) (x : Ω) :
    x ∈ vRing v ↔ 0 ≤ v x := by
  rfl
end GaussValuationUniqueness
