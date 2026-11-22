-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.prod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:42:56.108745+00:00
-- url     : https://prove2.me/submissions/1b302fcb-22e7-41b3-af86-8db504f6e29a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IsWeightedHomogeneousZeroStripPathWord
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A1_LeadAt_of_hom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
variable {σ R M : Type*} [CommRing R] [AddCommMonoid M] [LinearOrder M] [IsOrderedCancelAddMonoid M]
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
namespace LeadAt
theorem _root_.solution {ι : Type*} {w : σ → M} (s : Finset ι) (γ : ι → M) (f t : ι → MvPolynomial σ R)
    (h : ∀ i ∈ s, LeadAt w (γ i) (f i) (t i)) :
    LeadAt w (∑ i ∈ s, γ i) (∏ i ∈ s, f i) (∏ i ∈ s, t i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    rw [Finset.sum_empty, Finset.prod_empty, Finset.prod_empty]
    apply Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1.LeadAt.of_hom
    apply isWeightedHomogeneous_one
  · intro a s ha ih h
    rw [Finset.sum_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
end LeadAt
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A1
