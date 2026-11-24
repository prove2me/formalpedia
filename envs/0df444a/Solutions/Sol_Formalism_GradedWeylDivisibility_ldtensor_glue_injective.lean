-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_glue_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:08.328704+00:00
-- url     : https://prove2.me/submissions/19bd0d58-7b06-4dec-a036-0a9cff0d336a

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_glue_apply
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
theorem _root_.solution :
    Function.Injective (fun α : S → (Fin k × Fin n →₀ ℕ) => ∑ t, (α t).mapDomain (Prod.mk t)) := by
  intro α β h
  funext s
  ext v
  have e := congrArg (fun f => f (s, v)) h
  simpa [ldtensor_glue_apply] using e
end Formalism.GradedWeylDivisibility
