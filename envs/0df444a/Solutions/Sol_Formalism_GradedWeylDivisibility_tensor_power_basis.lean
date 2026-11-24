-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.tensor_power_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:21.599036+00:00
-- url     : https://prove2.me/submissions/618a16d3-6d1a-49fb-a322-4fbbede610b3

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_span_prod
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_prod_linInd_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial PiTensorProduct
open scoped Pointwise
open Module
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution : TensorBasis := by
  intro R K _ _ _ _ _ S _ _ k n ι M b hb hM
  have hK : ∀ s, LinearIndependent K (b s) := fun s => (LinearIndependent.iff_fractionRing R K).mp (hb s)
  refine ⟨(LinearIndependent.iff_fractionRing R K).mpr (ldtensor_prod_linInd_field K b hK), ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun s => b s (i s), fun s => ?_, rfl⟩
    rw [← hM s]
    exact Submodule.subset_span ⟨i s, rfl⟩
  · unfold tensorLat
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    exact ldtensor_span_prod R K b F fun s => by rw [hM s]; exact hF s
end Formalism.GradedWeylDivisibility
