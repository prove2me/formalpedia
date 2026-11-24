-- Prove2me | solution 1 for Formalism.QuantumDeterminants.Uof_lower_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:12:39.2648+00:00
-- url     : https://prove2.me/submissions/a9dad63d-d578-4c7e-9588-8315ec91378e

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
    (c a : Fin (r + 1)) (hac : a < c) : Uof k r z m c a = 0 := by
  have hm2 := hm.2.1
  have hac' : a.val < c.val := hac
  by_cases hc : c.val < r
  · simp only [Uof, hc, dif_pos]
    rw [mF_col z m _ a (by omega), hm2 ⟨a.val, by omega⟩ _ (by show a.val ≤ c.val; omega)]
    rw [if_neg]
    intro h
    have := congrArg Fin.val h
    change c.val = a.val at this
    omega
  · have hne : c ≠ a := fun h => by rw [h] at hac'; omega
    simp [Uof, hc, hne]
end Formalism.QuantumDeterminants
