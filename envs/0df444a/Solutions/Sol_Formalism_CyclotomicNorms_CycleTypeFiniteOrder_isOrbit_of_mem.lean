-- Prove2me | solution 1 for Formalism.CyclotomicNorms.CycleTypeFiniteOrder.isOrbit_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:21.091347+00:00
-- url     : https://prove2.me/submissions/57b92d3e-2156-4004-8ec4-206f4a5355cd

import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Lemmata_GeneralBFactSecondBis_Imports
import Definitions.Def_Formalism_CyclotomicNorms_NonsquarefreeBounds_IrreducibilityOfRestriction
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_mem_cyc
import Theorems.Thm_Formalism_CyclotomicNorms_CycleTypeFiniteOrder_iterate_eq
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans


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
theorem _root_.solution {q : ℕ} (hL : ∀ i, L (σ i) = L i ^ q) {S : Finset K} (hS : S ∈ blocks σ L) :
    Formalism.GaloisIrreducibility.IsOrbit (fun x : K => x ^ q) S := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hS
  constructor
  · intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    show L j ^ q ∈ _
    rw [← hL]
    exact Finset.mem_image_of_mem _ (mem_cyc.mpr (Equiv.Perm.sameCycle_apply_right.mpr (mem_cyc.mp hj)))
  · intro x hx y hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨n, hn⟩ := ((mem_cyc.mp hj).symm.trans (mem_cyc.mp hk)).exists_nat_pow_eq
    exact ⟨n, by rw [iterate_eq hL, hn]⟩
end Formalism.CyclotomicNorms.CycleTypeFiniteOrder
