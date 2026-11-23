-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmE_comp_ne_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:32.157964+00:00
-- url     : https://prove2.me/submissions/9f5f56d6-1ecc-48c7-897d-77f000a94283

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MemBranchRangeOfDefectEq
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_BranchMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R σ B : Type*} [CommRing R] [AddCommMonoid B] [DecidableEq B] (w : σ → B)
    (G : MvPolynomial σ R) (β : B) :
    weightedHomogeneousComponent w β G ≠ 0 ↔ β ∈ G.support.image (Finsupp.weight w) := by
  classical
  constructor
  · intro h
    obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp h
    rw [coeff_weightedHomogeneousComponent] at hd
    split_ifs at hd with hw
    · exact Finset.mem_image.mpr ⟨d, mem_support_iff.mpr hd, hw⟩
    · exact absurd rfl hd
  · intro h
    obtain ⟨d, hd, hw⟩ := Finset.mem_image.mp h
    intro h0
    have := congrArg (coeff d) h0
    rw [coeff_weightedHomogeneousComponent, if_pos hw, coeff_zero] at this
    exact mem_support_iff.mp hd this
end Formalism.BranchingDeterminantCap
