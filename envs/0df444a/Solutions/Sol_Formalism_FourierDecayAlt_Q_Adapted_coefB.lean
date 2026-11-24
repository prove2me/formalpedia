-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.Adapted.coefB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:47:58.140882+00:00
-- url     : https://prove2.me/submissions/8e6d031d-b573-4579-9959-ba21e91b676f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.Adapted
open Formalism.REAL
namespace Formalism.FourierDecayAlt.Q.Adapted
theorem _root_.solution {n : ℕ} (γ γ' : Fin (n + 2) → ℂ) (hγ : ∀ j : Fin (n + 2), 2 ≤ j.val → γ j = 0 ∧ γ' j = 0)
    (i i' : Fin (n + 2)) (h : i < i') (hne : ¬ (i = 0 ∧ i' = 1)) :
    γ i * γ' i' - γ i' * γ' i = 0 := by
  have hi' : 2 ≤ i'.val := by
    by_contra hlt
    push_neg at hlt
    apply hne
    have h1 : i.val < i'.val := h
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩ <;> simp only [Fin.val_zero, Fin.val_one] <;> omega
  rw [(hγ i' hi').1, (hγ i' hi').2]
  ring
end Formalism.FourierDecayAlt.Q.Adapted
