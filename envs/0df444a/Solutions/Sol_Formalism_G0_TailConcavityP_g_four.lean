-- Prove2me | solution 1 for Formalism.G0.TailConcavityP.g_four
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:32.977361+00:00
-- url     : https://prove2.me/submissions/7219975e-1789-48ac-a49d-4d1f8733bd4f

import Definitions.Def_Formalism_SubspaceCounting_StatementB
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailConcavity

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
theorem _root_.solution {k : ℕ} {b : ℝ} (hb : (k : ℝ) ≤ b) : g k (4 * b) ≤ g k b / 2 := by
  unfold g
  rw [sum_div]
  apply sum_le_sum
  intro i hi
  have hi' : (i : ℝ) + 1 ≤ k := by
    have : i + 1 ≤ k := mem_range.mp hi
    exact_mod_cast this
  have hi0 : (0 : ℝ) ≤ i := i.cast_nonneg
  have h0 : (0 : ℝ) < b + i + 1 := by linarith
  rw [div_div]
  apply one_div_le_one_div_of_le (by positivity) (by linarith)
end Formalism.G0.TailConcavityP
