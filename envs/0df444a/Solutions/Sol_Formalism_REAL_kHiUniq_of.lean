-- Prove2me | solution 1 for Formalism.REAL.kHiUniq_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:41.2486+00:00
-- url     : https://prove2.me/submissions/b07791f3-10c6-439c-a8b5-0ecfb843145e

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementKT
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Theorems.Thm_Formalism_REAL_mem_compactSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution (hl : KLow) (_hw : KWtOrth) (ho : KOrth) : KHiUniq := by
  intro V _ _ n ε F μ ν x y hrel hunit hx hyx hy
  by_cases hμν : ν = μ
  · right
    refine ⟨hμν, ?_⟩
    obtain ⟨hspan, huniq⟩ := hl V n ε F μ x hrel hx
    exact huniq y (hspan ▸ hyx) (hμν ▸ hy.1)
  · left
    have h0 := ho V n ε F μ ν x y hrel hunit hx hy (Ne.symm hμν) y hyx y (mem_compactSpan y)
    exact inner_self_eq_zero.1 h0
end Formalism.REAL
