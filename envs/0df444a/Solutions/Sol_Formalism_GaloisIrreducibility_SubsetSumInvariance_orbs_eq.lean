-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.SubsetSumInvariance.orbs_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:04:02.860919+00:00
-- url     : https://prove2.me/submissions/88d584a7-12df-4504-9c0d-d4b71a659564

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PermSubSumInv
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_stable
import Theorems.Thm_Formalism_GaloisIrreducibility_SubsetSumInvariance_orbs_sub

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
theorem _root_.solution {σ : Perm α} {O O' : Finset α} (hO : O ∈ orbs σ) (hO' : O' ∈ orbs σ) {x : α}
    (h1 : x ∈ O) (h2 : x ∈ O') : O = O' := by
  have key : ∀ {O O' : Finset α}, O ∈ orbs σ → O' ∈ orbs σ → x ∈ O → x ∈ O' → O ⊆ O' := by
    intro O O' hO hO' h1 h2
    exact orbs_sub (fun y hy => orbs_stable hO' y hy) hO h1 h2
  exact Finset.Subset.antisymm (key hO hO' h1 h2) (key hO' hO h2 h1)
end Formalism.GaloisIrreducibility.SubsetSumInvariance
