-- Prove2me | solution 1 for Formalism.QuantumDeterminants.Uof_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:38.139238+00:00
-- url     : https://prove2.me/submissions/f6ef4009-51b1-496f-8017-9348f222411b

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Theorems.Thm_Formalism_QuantumDeterminants_mF_col

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
namespace Formalism.QuantumDeterminants
theorem _root_.solution {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Nset k r)
    (c : Fin (r + 1)) : Uof k r z m c c = 1 := by
  have hm2 := hm.2.1
  by_cases hc : c.val < r
  · simp only [Uof, hc, dif_pos]
    rw [mF_col z m _ c hc, hm2 ⟨c.val, hc⟩ _ (le_refl _), if_pos rfl]
  · simp [Uof, hc]
end Formalism.QuantumDeterminants
