-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_psi_tprod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:54:08.007823+00:00
-- url     : https://prove2.me/submissions/a54d368f-6ef9-4ce7-8e6d-822cb035fa3c

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
theorem _root_.solution (F : S → MvPolynomial (Fin k × Fin n) K) :
    ldtensor_psi K (tprod K F) = ∏ s, blockEmb K s (F s) := by
  unfold ldtensor_psi
  rw [PiTensorProduct.lift.tprod]
  simp [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
end Formalism.GradedWeylDivisibility
