-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.eS_mul_rho
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:45:47.777392+00:00
-- url     : https://prove2.me/submissions/9e5c177b-49d1-432d-811e-28d59525fc82

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
theorem _root_.solution {T V : Type} [AddCommGroup T] [Module K T] [AddCommGroup V] [Module K V]
    (τ : Representation K G T) (ρ : Representation K G V) (y : G) :
    eS τ ρ * ρ y = (charOf τ 1 / (Fintype.card G : K)) • ∑ g : G, charOf τ (y * g⁻¹) • ρ g := by
  unfold eS
  rw [smul_mul_assoc, Finset.sum_mul]
  congr 1
  simp_rw [smul_mul_assoc, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight y) _ _ (fun x => by simp [mul_inv_rev])
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
