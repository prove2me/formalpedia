-- Prove2me | solution 1 for GaussValuationUniqueness.sac_same
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:14.322029+00:00
-- url     : https://prove2.me/submissions/a4d8ee4c-a560-4059-8e75-92ff5ce8f107

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
theorem _root_.solution {α : Type*} {n : ℕ} (i : Fin (n + 1)) (x : α) (f : Fin n → α) :
    Fin.succAboveCases (α := fun _ => α) i x f i = x := Fin.insertNth_apply_same (α := fun _ => α) i x f
end GaussValuationUniqueness
