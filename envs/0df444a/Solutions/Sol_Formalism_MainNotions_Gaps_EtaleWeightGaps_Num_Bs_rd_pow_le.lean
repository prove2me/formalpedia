-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs.rd_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:39.080102+00:00
-- url     : https://prove2.me/submissions/80c5751c-5a94-4ead-933d-2ac509e95d06

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LargeConstantLeParamCube

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.EtaleWeightGaps.Num
open Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
variable {A k b sb PP TO rd : ℝ} (h : Bs A k b sb PP TO rd)
include h
namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
theorem _root_.solution {n : ℕ} (hn : n ≤ 8) : rd ^ n ≤ sb :=
  le_trans (pow_le_pow_right₀ h.rd1 hn) h.rd8
end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num.Bs
