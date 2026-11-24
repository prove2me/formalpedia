-- Prove2me | solution 1 for Formalism.CohomologicalDescent.label_sum_le_filter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:59:05.133164+00:00
-- url     : https://prove2.me/submissions/034275b3-ec7c-42fa-91ea-c2cc483bdd07

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
import Theorems.Thm_Formalism_CohomologicalDescent_label_vl_le_ind

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical
namespace Formalism.CohomologicalDescent
theorem _root_.solution {l : ℕ} (hl : l.Prime) (s : Finset ℤ) (mB : ℤ) (c : ℤ → ℝ)
    (hc : ∀ x ∈ s, 0 ≤ c x) (hr : ∀ x ∈ s, 0 < x - mB ∧ x - mB < (l : ℤ) ^ 2) :
    ∑ x ∈ s, c x * (vl l (x - mB) : ℝ) ≤ ∑ x ∈ s.filter (fun x => (l : ℤ) ∣ x - mB), c x := by
  rw [Finset.sum_filter]
  refine Finset.sum_le_sum fun x hx => ?_
  have h := label_vl_le_ind hl (hr x hx).1 (hr x hx).2
  calc c x * (vl l (x - mB) : ℝ) ≤ c x * (if (l : ℤ) ∣ x - mB then 1 else 0) :=
        mul_le_mul_of_nonneg_left h (hc x hx)
    _ = if (l : ℤ) ∣ x - mB then c x else 0 := by split_ifs <;> simp
end Formalism.CohomologicalDescent
