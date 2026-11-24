-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.ldtensor_prod_linInd_field
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:20.352813+00:00
-- url     : https://prove2.me/submissions/717937bf-d1fd-4ebd-b27b-2f6126bdc3b5

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementD
import Mathlib.LinearAlgebra.PiTensorProduct.Basis
import Mathlib.RingTheory.Localization.Module
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_TensorBasis
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_psi_tprod
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_psi_injective
import Theorems.Thm_Formalism_GradedWeylDivisibility_ldtensor_tprod_linInd
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
theorem _root_.solution {ι : S → Type*} (b : ∀ s, ι s → MvPolynomial (Fin k × Fin n) K)
    (hb : ∀ s, LinearIndependent K (b s)) :
    LinearIndependent K (fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) := by
  have h := (ldtensor_tprod_linInd K b hb).map' (ldtensor_psi K)
    (LinearMap.ker_eq_bot.mpr (ldtensor_psi_injective K))
  have e : (fun i : (∀ s, ι s) => ∏ s, blockEmb K s (b s (i s))) =
      ldtensor_psi K ∘ (fun i => tprod K fun s => b s (i s)) := by
    funext i
    simp [ldtensor_psi_tprod]
  rw [e]
  exact h
end Formalism.GradedWeylDivisibility
