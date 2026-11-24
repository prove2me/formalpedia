-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_glue_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:23.016151+00:00
-- url     : https://prove2.me/submissions/c4ae2012-2a79-4d63-a82f-7d4320d6052d

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
theorem _root_.solution (α : S → (Fin k × Fin n →₀ ℕ)) (s : S) (v : Fin k × Fin n) :
    (∑ t, (α t).mapDomain (Prod.mk t)) (s, v) = α s v := by
  rw [Finsupp.finset_sum_apply, Finset.sum_eq_single s]
  · exact Finsupp.mapDomain_apply (fun x y h => by simpa using h) _ v
  · intro t _ hts
    apply Finsupp.mapDomain_notin_range
    rintro ⟨w, hw⟩
    exact hts (congrArg Prod.fst hw)
  · simp
end Formalism.GradedWeylDivisibility
