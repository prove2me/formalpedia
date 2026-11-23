-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxRules_inf_lat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:02:30.088552+00:00
-- url     : https://prove2.me/submissions/2adaed2b-4550-4940-a996-e21e1edec839

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_alg_ne
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_idxRules_denom
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_inf


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
theorem _root_.solution {W : Submodule K V} {A B : Submodule R V}
    (hA : A.FG ∧ Submodule.span K (A : Set V) = W) (hB : B.FG ∧ Submodule.span K (B : Set V) = W) :
    (A ⊓ B).FG ∧ Submodule.span K ((A ⊓ B : Submodule R V) : Set V) = W := by
  refine ⟨hA.1.of_le inf_le_left, le_antisymm ?_ ?_⟩
  · rw [← hA.2]
    exact Submodule.span_mono inf_le_left
  · intro x hx
    have hx' : x ∈ locS R⁰ (A ⊓ B) := by
      rw [locBasic_locS_inf]
      exact ⟨idxRules_denom A (by rw [hA.2]; exact hx), idxRules_denom B (by rw [hB.2]; exact hx)⟩
    obtain ⟨d, hd, hdx⟩ := hx'
    have hd0 : algebraMap R K d ≠ 0 := idxRules_alg_ne (nonZeroDivisors.ne_zero hd)
    have e : x = (algebraMap R K d)⁻¹ • (d • x) := by
      rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hdx)
end Formalism.EigenvalueLevelCeiling
