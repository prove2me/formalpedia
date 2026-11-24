-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.SubsetSumInvariance.pow_stable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:58:20.654903+00:00
-- url     : https://prove2.me/submissions/696ab9a9-73d8-4f09-8e46-44327b7424b9

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
theorem _root_.solution {σ : Perm α} {A : Finset α} (hA : ∀ x ∈ A, σ x ∈ A) :
    ∀ m : ℕ, ∀ z ∈ A, (σ ^ m) z ∈ A := by
  intro m
  induction m with
  | zero => intro z hz; simpa using hz
  | succ m ih =>
    intro z hz
    rw [pow_succ', Perm.mul_apply]
    exact hA _ (ih z hz)
end Formalism.GaloisIrreducibility.SubsetSumInvariance
