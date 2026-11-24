-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.charFacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:55:15.560481+00:00
-- url     : https://prove2.me/submissions/32b34552-35a8-49dc-9352-61e6c862ecbf

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_CharacterLemmas_char_complex
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_CharacterLemmas_trace_repC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open CharacterLemmas
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution : CharFacts := by
  intro K _ _ G _ _ T _ _ _ τ g
  have hmain : ∀ σ : K →+* ℂ, IsIntegral ℤ (σ (charOf τ g)) ∧
      σ (charOf τ g⁻¹) = star (σ (charOf τ g)) ∧ ‖σ (charOf τ g)‖ ≤ (finrank K T : ℝ) := by
    intro σ
    obtain ⟨h1, h2, h3⟩ := char_complex (repC σ τ) g
    rw [trace_repC, trace_repC] at h2
    rw [trace_repC] at h1 h3
    refine ⟨h1, h2, ?_⟩
    simpa using h3
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := by
    first
    | exact inferInstance
    | exact ⟨(IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := K)).toRingHom⟩
  refine ⟨?_, fun σ' => ⟨(hmain σ').2.1, (hmain σ').2.2⟩⟩
  exact (isIntegral_algHom_iff σ.toIntAlgHom σ.injective).1 (hmain σ).1
end Formalism.IndefR.LatticeTransfer
