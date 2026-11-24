-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.SubsetSumInvariance.fixed_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:19.995995+00:00
-- url     : https://prove2.me/submissions/8015effc-2fd0-4749-91ea-fb2be73b0c83

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Formalism.GaloisIrreducibility.SubsetSumInvariance
open Equiv Equiv.Perm Finset
variable {α : Type} [Fintype α] [DecidableEq α]
namespace Formalism.GaloisIrreducibility.SubsetSumInvariance
theorem _root_.solution {σ : Perm α} {y : α} (h : y ∉ σ.support) : σ y = y := Perm.notMem_support.1 h
end Formalism.GaloisIrreducibility.SubsetSumInvariance
