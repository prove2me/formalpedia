-- Prove2me | solution 1 for GaussValuationUniqueness.sac_succAbove
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:14.2948+00:00
-- url     : https://prove2.me/submissions/0463845f-365d-43b4-a060-c1cbcd4db0b8

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
theorem _root_.solution {α : Type*} {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α)
    (k : Fin n) : Fin.succAboveCases (α := fun _ => α) i x f (i.succAbove k) = f k := Fin.insertNth_apply_succAbove (α := fun _ => α) i x f k
end GaussValuationUniqueness
