-- Prove2me | solution 1 for Formalism.CountingSumsFrames.diagLaplacian_commute
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:44:20.866179+00:00
-- url     : https://prove2.me/submissions/4b48510c-8ff9-49a2-b171-9570680dc499

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Theorems.Thm_Formalism_CountingSumsFrames_diagLaplacian_apply

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
open Formalism Formalism.CountingSumsFrames
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (i j : Fin k) : Commute (h3d K i) (h3d K j) := by
  refine LinearMap.ext fun f => ?_
  ext m
  simp only [Module.End.mul_apply, diagLaplacian_apply, coeff_pderiv]
  have e : m + Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1 + Finsupp.single (Sum.inl j) 1 +
      Finsupp.single (Sum.inr j) 1 = m + Finsupp.single (Sum.inl j) 1 + Finsupp.single (Sum.inr j) 1 +
      Finsupp.single (Sum.inl i) 1 + Finsupp.single (Sum.inr i) 1 := by abel
  rw [e]
  by_cases hij : i = j
  · subst hij; rfl
  · have hji : ¬ j = i := fun h => hij h.symm
    simp [hij, hji]
    ring
end Formalism.CountingSumsFrames
