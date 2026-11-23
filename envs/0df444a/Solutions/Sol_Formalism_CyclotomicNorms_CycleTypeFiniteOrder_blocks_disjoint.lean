-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.blocks_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:39.312771+00:00
-- url     : https://prove2.me/submissions/89c7e5c4-04c7-42fc-9160-afcb796cbdf2

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_cyc_eq_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Formalism Formalism.CyclotomicNorms Formalism.CyclotomicNorms.CycleTypeFiniteOrder
variable {α K : Type*} [Fintype α] [DecidableEq α] [DecidableEq K] [Monoid K]
variable (σ : Equiv.Perm α) (L : α → K)
variable {σ L}
namespace Formalism.CyclotomicNorms.CycleTypeFiniteOrder
theorem _root_.solution (hLi : Function.Injective L) {S T : Finset K} (hS : S ∈ blocks σ L)
    (hT : T ∈ blocks σ L) (hST : S ≠ T) : Disjoint S T := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hT
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hx'
  rw [hLi hba] at hb
  exact hST (by rw [cyc_eq_of_mem ha hb])
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
