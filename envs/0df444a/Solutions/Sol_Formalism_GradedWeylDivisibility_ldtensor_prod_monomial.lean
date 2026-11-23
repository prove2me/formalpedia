-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_prod_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:10.436243+00:00
-- url     : https://prove2.me/submissions/820e847f-3c9d-43a4-a39f-e04d54be276b

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial PiTensorProduct
open scoped Pointwise
open Module
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
variable (K : Type*) [Field K] {S : Type*} [Fintype S] [DecidableEq S] {k n : ℕ}
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution (α : S → (Fin k × Fin n →₀ ℕ)) :
    ∏ s, blockEmb K s (monomial (α s) (1 : K)) = monomial (∑ t, (α t).mapDomain (Prod.mk t)) 1 := by
  simp only [blockEmb, rename_monomial]
  rw [monomial_sum_one]
end Formalism.GradedWeylDivisibility
