-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.eS_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:49:16.007278+00:00
-- url     : https://prove2.me/submissions/2889b574-e420-4560-bdf3-ae7243ac4b6d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_FinrankIntSelf
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_charOf_conj
import Theorems.Thm_Formalism_IndefR_LatticeTransfer_IdempotentLemmas_eS_mul_rho

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
theorem _root_.solution {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (g : G) :
    eS τ ρ * ρ g = ρ g * eS τ ρ := by
  rw [eS_mul_rho]
  unfold eS
  rw [mul_smul_comm, Finset.mul_sum]
  congr 1
  simp_rw [mul_smul_comm, ← map_mul]
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun x => ?_)
  simp only [Equiv.coe_mulLeft]
  congr 1
  rw [show g * (g * x)⁻¹ = g * x⁻¹ * g⁻¹ by group, charOf_conj]
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
