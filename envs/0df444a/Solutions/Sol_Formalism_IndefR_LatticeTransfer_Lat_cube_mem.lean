-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.Lat.cube_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:14.456842+00:00
-- url     : https://prove2.me/submissions/417cc582-4717-40ee-97f6-de53d50ce65f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_MemSpanOfSmulMem
import Definitions.Def_Formalism_BranchSandwichDivisors_DivFromPassageAndNorm
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransferOfFacts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement Formalism.HN _root_.Formalism.IndefR.LatticeTransfer.Lat
namespace Formalism.IndefR.LatticeTransfer
namespace Lat
theorem _root_.solution {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    {B : Submodule (𝓞 K) V} {N : 𝓞 K} {z : V} (h : N • z ∈ B) : N ^ 3 • z ∈ B := by
  have : N ^ 3 • z = N ^ 2 • N • z := by rw [smul_smul]; ring_nf
  rw [this]
  exact B.smul_mem _ h
end Lat
end Formalism.IndefR.LatticeTransfer
