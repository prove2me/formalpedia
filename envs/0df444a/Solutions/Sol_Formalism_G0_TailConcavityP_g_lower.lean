-- Prove2me | solution 1 for Formalism.G0.TailConcavityP.g_lower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:11.494811+00:00
-- url     : https://prove2.me/submissions/0f2df0bb-43f2-4a20-a547-e83a0b09a9a7

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
theorem _root_.solution {k : ℕ} {b : ℝ} (hk : (k : ℝ) ≤ b) (hb : 0 < b) : (k : ℝ) / (2 * b) ≤ g k b := by
  have h : ∑ i ∈ range k, (1 : ℝ) / (2 * b) ≤ g k b := by
    unfold g
    apply sum_le_sum
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ k := by
      have : i + 1 ≤ k := mem_range.mp hi
      exact_mod_cast this
    apply one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [sum_const, card_range, nsmul_eq_mul] at h
  calc (k : ℝ) / (2 * b) = k * (1 / (2 * b)) := by ring
    _ ≤ g k b := h
end Formalism.G0.TailConcavityP
