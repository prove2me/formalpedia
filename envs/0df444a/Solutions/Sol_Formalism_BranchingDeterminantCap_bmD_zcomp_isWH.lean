-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.bmD_zcomp_isWH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:24.504694+00:00
-- url     : https://prove2.me/submissions/6b0def19-bb79-4222-a45c-dfa3df4c9b25

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
section
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
namespace Formalism.BranchingDeterminantCap
private theorem bm_whcWH_lemma_3 {R σ B : Type*} [CommRing R] [AddCommMonoid B] (w : σ → B) (m : B)
    (φ : MvPolynomial σ R) : IsWeightedHomogeneous w (weightedHomogeneousComponent w m φ) m := by
  classical
  intro d hd
  rw [coeff_weightedHomogeneousComponent] at hd
  split_ifs at hd with h
  · exact h
  · exact absurd rfl hd
section bmAList
variable {A : Type*} [Ring A]
end bmAList
section bmACap
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap
section bmACap2
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap2
section bmACap3
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n : ℕ}
end bmACap3
end Formalism.BranchingDeterminantCap
end
end

set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {R : Type*} [CommRing R] {n : ℕ} (β : Fin n → ℤ) (Y : BP R n) :
    IsWeightedHomogeneous (zW n) (zcomp R n β Y) β := by
  exact bm_whcWH_lemma_3 (zW n) β Y
end Formalism.BranchingDeterminantCap
