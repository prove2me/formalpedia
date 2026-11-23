-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.three_forms_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:20.721432+00:00
-- url     : https://prove2.me/submissions/01c7b712-de36-436a-b8cc-cce1614ac27b

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_congr
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_mono_left
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_le_of_sup
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_qlen_map
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_lidx_of_le
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_sc_eq_map
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_sc_sc_inv
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_localization_sc
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_localization_inf
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ThreeFormsAlt_localization_sup_eq_localization_dnN

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
open ThreeFormsAlt
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : ThreeFormsSum := by
  intro K _ _ _ Z _ _ _ _ _ w A B _ _ _ a ha _
  unfold lix
  rw [lidx_of_le _ (le_sup_right : B ≤ sc a A ⊔ B),
    lidx_of_le _ (inf_le_left : A ⊓ sc a⁻¹ B ≤ A), localization_sup_eq_localization_dnN, localization_sc _ ha, localization_inf,
    localization_sc _ (inv_ne_zero ha)]
  set A' := localization₂ w.asIdeal A
  set B' := localization₂ w.asIdeal B
  have h1 : qlen (sc a A' ⊔ B') B' = qlen (sc a A') B' :=
    le_antisymm (qlen_le_of_sup le_sup_left (sup_le_sup_left (le_inf le_sup_right le_rfl) _))
      (qlen_mono_left le_sup_left _)
  have h2 : qlen (sc a A') B' = qlen A' (sc a⁻¹ B') := by
    conv_lhs => rw [← sc_sc_inv ha B']
    rw [sc_eq_map a ha, sc_eq_map a ha, qlen_map]
  have h3 : qlen A' (A' ⊓ sc a⁻¹ B') = qlen A' (sc a⁻¹ B') :=
    qlen_congr A' (fun x hx => ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩)
  rw [h1, h2, h3]
end Formalism.EigenvalueLevelCeiling
