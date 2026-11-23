-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.localization_cut
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:45.92885+00:00
-- url     : https://prove2.me/submissions/f7e82e44-9a71-482f-8fe7-d0d9d624d0a1

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_localization_inf
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_algebraMap_ne_zero_of_notMem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (p : Ideal (𝓞 K)) [p.IsPrime] (W : Submodule K Z) (X : Submodule (𝓞 K) Z) :
    localization₂ p (cut W X) = cut W (localization₂ p X) := by
  unfold cut
  rw [localization_inf]
  congr 1
  apply le_antisymm
  · rintro x ⟨s, hs, hx⟩
    have hs0 := algebraMap_ne_zero_of_notMem p hs
    have hx' : (algebraMap (𝓞 K) K s) • x ∈ W := by
      rw [algebraMap_smul]
      exact hx
    have := W.smul_mem (algebraMap (𝓞 K) K s)⁻¹ hx'
    rwa [smul_smul, inv_mul_cancel₀ hs0, one_smul] at this
  · exact locBasic_le_locS _ _
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
