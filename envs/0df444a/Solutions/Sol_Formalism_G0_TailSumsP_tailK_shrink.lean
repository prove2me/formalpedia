-- Prove2me | solution 1 for Formalism.G0.TailSumsP.tailK_shrink
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:26.510977+00:00
-- url     : https://prove2.me/submissions/5773b8c9-db8d-46e8-ac6a-281e5515baa3

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TailSumsP
namespace Formalism.G0.TailSumsP
theorem _root_.solution {K : ℕ} {α α' : Fin K → ℕ} (h : ShrinkStep α α') (u : ℕ) :
    tailK α' u ≤ tailK α u := by
  unfold tailK
  apply Finset.sum_le_sum
  intro l _
  split_ifs
  · exact h l
  · exact le_rfl
end Formalism.G0.TailSumsP
