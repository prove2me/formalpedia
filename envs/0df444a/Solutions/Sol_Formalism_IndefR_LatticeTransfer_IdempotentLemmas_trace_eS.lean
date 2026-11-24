-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.trace_eS
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:04.024636+00:00
-- url     : https://prove2.me/submissions/503d2800-5b45-4b3e-b9fc-1b941eebdc76

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
theorem _root_.solution {T U : Type} [AddCommGroup T] [Module K T] [AddCommGroup U] [Module K U]
    (τ : Representation K G T) (σ : Representation K G U) :
    LinearMap.trace K U (eS τ σ) =
      charOf τ 1 / (Fintype.card G : K) * ∑ x : G, charOf τ x⁻¹ * charOf σ x := by
  unfold eS
  rw [map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
