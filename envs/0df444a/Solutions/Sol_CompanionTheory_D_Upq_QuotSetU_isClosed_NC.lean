-- Prove2me | solution 1 for CompanionTheory.D.Upq.QuotSetU.isClosed_NC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T02:38:14.0912+00:00
-- url     : https://prove2.me/submissions/0a6a6e8b-693f-4f8a-8e39-367edc7d4990

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_UnitaryWeylCompact
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SecondCountableQuotients_SGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.QuotSetU
open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW
variable {k r : ℕ}
local notation "𝕄" => Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ
namespace CompanionTheory.D.Upq.QuotSetU
theorem _root_.solution : IsClosed {g : 𝕄 | NC k r g} := by
  have e : {g : 𝕄 | NC k r g} = ⋂ i : Fin (2 * r + k + 1), ⋂ j : Fin (2 * r + k + 1),
      {g : 𝕄 | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} := by
    ext g; simp only [Set.mem_ofPred_eq, Set.mem_iInter]; rfl
  rw [e]
  refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
  by_cases h : j.val ≤ r + k ∧ min j.val r ≤ i.val
  · have e2 : {g : 𝕄 | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} =
        {g : 𝕄 | g i j = if i = j then 1 else 0} := by
      ext g; simp only [Set.mem_ofPred_eq, h.1, h.2, forall_const]
    rw [e2]
    exact isClosed_eq ((continuous_apply j).comp (continuous_apply i)) continuous_const
  · have e2 : {g : 𝕄 | j.val ≤ r + k → min j.val r ≤ i.val → g i j = if i = j then 1 else 0} =
        Set.univ := by
      ext g; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      intro h1 h2; exact absurd ⟨h1, h2⟩ h
    rw [e2]; exact isClosed_univ
end CompanionTheory.D.Upq.QuotSetU
