-- Prove2me | solution 1 for GaussValuationUniqueness.one_le_of_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:27:54.357799+00:00
-- url     : https://prove2.me/submissions/958fd550-6c44-4ef9-9da7-4b510bc9d968

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
theorem _root_.solution {x : WithTop ℤ} (h : 0 < x) : 1 ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe n =>
    have h0 : (0 : ℤ) < n := by exact_mod_cast h
    exact_mod_cast (show (1 : ℤ) ≤ n by omega)
end GaussValuationUniqueness
