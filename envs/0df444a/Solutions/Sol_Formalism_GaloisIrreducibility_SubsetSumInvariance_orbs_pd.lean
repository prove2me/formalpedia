-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_pd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:52.405846+00:00
-- url     : https://prove2.me/submissions/a7dafa3f-c1b1-4ba8-a698-0f1b0ea06580

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_eq

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
theorem _root_.solution (σ : Perm α) : (orbs σ : Set (Finset α)).PairwiseDisjoint id := by
  intro O hO O' hO' hne
  rw [Function.onFun, id, id, Finset.disjoint_left]
  intro x h1 h2
  exact hne (orbs_eq hO hO' h1 h2)
end Formalism.GaloisIrreducibility.SubsetSumInvariance
