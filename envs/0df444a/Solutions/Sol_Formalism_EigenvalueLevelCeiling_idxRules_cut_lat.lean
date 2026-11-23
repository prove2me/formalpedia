-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_cut_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:18.529996+00:00
-- url     : https://prove2.me/submissions/82f48e8e-cdab-416a-8866-0f86af2e1323

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_alg_ne
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_denom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues Formalism.HermitianLatticesTheory
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  {V' : Type*} [AddCommGroup V'] [Module K V'] [Module R V'] [IsScalarTower R K V']
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution {W W' : Submodule K V} (hW : W' ≤ W) {A : Submodule R V}
    (hA : A.FG ∧ Submodule.span K (A : Set V) = W) :
    (A ⊓ W'.restrictScalars R).FG ∧
      Submodule.span K ((A ⊓ W'.restrictScalars R : Submodule R V) : Set V) = W' := by
  refine ⟨hA.1.of_le inf_le_left, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    intro x hx
    exact hx.2
  · intro x hx
    obtain ⟨d, hd, hdx⟩ := idxRules_denom A (x := x) (by rw [hA.2]; exact hW hx)
    have hd0 : algebraMap R K d ≠ 0 := idxRules_alg_ne (nonZeroDivisors.ne_zero hd)
    have hm : d • x ∈ (A ⊓ W'.restrictScalars R : Submodule R V) :=
      ⟨hdx, (W'.restrictScalars R).smul_mem d hx⟩
    have e : x = (algebraMap R K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
end Formalism.EigenvalueLevelCeiling
