-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.charOf_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:18.199+00:00
-- url     : https://prove2.me/submissions/15e6c6d0-cbb0-4318-b606-69178e8255ca

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf

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
open Formalism.IndefR.LatticeTransfer.IdempotentLemmas
variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
namespace Formalism.IndefR.LatticeTransfer.IdempotentLemmas
theorem _root_.solution {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    (g h : G) : charOf τ (h * g * h⁻¹) = charOf τ g := by
  unfold charOf
  by_cases hf : Module.Finite K T
  · rw [map_mul τ, map_mul τ, LinearMap.trace_mul_comm K (τ h * τ g), ← mul_assoc, ← map_mul τ,
      inv_mul_cancel, map_one, one_mul]
  · have h0 : LinearMap.trace K T = 0 := by
      first
      | exact LinearMap.trace_eq_zero_of_not_finite hf
      | exact LinearMap.trace_eq_zero_of_not_finite (R := K) (M := T) hf
      | (rw [LinearMap.trace, dif_neg]; rintro ⟨_, ⟨b⟩⟩; exact hf (Module.Finite.of_basis b))
      | (unfold LinearMap.trace; rw [dif_neg]; rintro ⟨_, ⟨b⟩⟩; exact hf (Module.Finite.of_basis b))
    simp [h0]
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
