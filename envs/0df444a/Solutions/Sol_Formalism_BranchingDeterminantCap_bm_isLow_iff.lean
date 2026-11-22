-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bm_isLow_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:23:39.458266+00:00
-- url     : https://prove2.me/submissions/5e6a58b7-2179-424f-81f6-a0c3dbccdecb

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
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (D : ℤ) (L : BP R n) :
    IsLow D L ↔ ∀ β, D ≤ omg β → zcomp R n β L = 0 := by
  classical
  constructor
  · intro h β hβ
    ext m
    rw [zcomp, coeff_weightedHomogeneousComponent, coeff_zero]
    split_ifs with hm
    · by_contra hc
      have := h m (mem_support_iff.mpr hc)
      rw [hm] at this
      omega
    · rfl
  · intro h m hm
    by_contra hc
    have h0 := h _ (not_lt.mp hc)
    have := congrArg (coeff m) h0
    rw [zcomp, coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
    exact mem_support_iff.mp hm this
end Formalism.BranchingDeterminantCap
