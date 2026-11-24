-- Prove2me | solution 1 for Formalism.G0.TailConcavityP.fTail_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:29.66841+00:00
-- url     : https://prove2.me/submissions/460672dd-7ac6-4b62-8f32-d4f8e1f1d2df

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity
import Theorems.Thm_Formalism_G0_TailConcavityP_fTail_eq
import Theorems.Thm_Formalism_G0_TailConcavityP_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.G0
open Formalism.G0.TailConcavityP
namespace Formalism.G0.TailConcavityP
theorem _root_.solution (k a b : ℕ) : fTail k a - fTail k b ≤ g k b * ((a : ℝ) - b) := by
  rw [fTail_eq, fTail_eq, ← sum_sub_distrib, g, sum_mul]
  apply sum_le_sum
  intro i _
  have := term_le a b i
  linarith
end Formalism.G0.TailConcavityP
