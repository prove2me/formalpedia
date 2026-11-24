-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.IdempotentLemmas.asAlg_eAlg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:43:16.962927+00:00
-- url     : https://prove2.me/submissions/2c46ebf9-0df6-456e-a61a-f276631ad18a

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
    (τ : Representation K G T) (ρ : Representation K G V) :
    ρ.asAlgebraHom (eAlg τ) = eS τ ρ := by
  unfold eAlg eS
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.asAlgebraHom_single, mul_smul]
end Formalism.IndefR.LatticeTransfer.IdempotentLemmas
