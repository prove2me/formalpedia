-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.idemE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:11:48.874834+00:00
-- url     : https://prove2.me/submissions/cd774d56-23ee-4016-a069-ebf713df348f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_eS_mul_asAlg
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_asAlg_eAlg
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_schur

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
open IdempotentLemmas
namespace Formalism.IndefR.LatticeTransfer
theorem _root_.solution : IdemE := by
  intro K _ _ G _ _ S T _ _ _ τ hgood V _ _ ρ
  obtain ⟨h1, h2, -⟩ := schur K G S T τ hgood
  have key : ∀ s t, eS (τ s) ρ ∘ₗ eS (τ t) ρ = (charOf (τ s) 1 / (Fintype.card G : K)) •
      ∑ g : G, LinearMap.trace K (T s) (eS (τ t) (τ s) * τ s g⁻¹) • ρ g := by
    intro s t
    rw [← Module.End.mul_eq_comp, ← asAlg_eAlg (τ t) ρ, eS_mul_asAlg, asAlg_eAlg]
  refine ⟨fun s => ?_, fun s t hst => ?_⟩
  · rw [key, h1 s]
    unfold eS
    congr 1
  · rw [key, h2 t s (Ne.symm hst)]
    simp
end Formalism.IndefR.LatticeTransfer
