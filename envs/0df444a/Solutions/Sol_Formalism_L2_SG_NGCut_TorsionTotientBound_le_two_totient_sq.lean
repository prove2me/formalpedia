-- Prove2me | solution 1 for Formalism.L2.SG.NGCut.TorsionTotientBound.le_two_totient_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:24:59.471658+00:00
-- url     : https://prove2.me/submissions/29a7a2f4-2fbd-4d96-a4ce-c1c8db679993

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_TorsionTotientBound
import Theorems.Thm_Formalism_L2_SG_NGCut_TorsionTotientBound_le_mul_totient_sq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.NGCut Formalism.L2.SG.NGCut.TorsionTotientBound
namespace Formalism.L2.SG.NGCut.TorsionTotientBound
theorem _root_.solution (n : ℕ) : n ≤ 2 * n.totient ^ 2 := by
  have := le_mul_totient_sq n
  split_ifs at this <;> nlinarith [Nat.zero_le (n.totient ^ 2)]
end Formalism.L2.SG.NGCut.TorsionTotientBound
