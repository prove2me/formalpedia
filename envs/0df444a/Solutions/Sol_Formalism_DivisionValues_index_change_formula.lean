-- Prove2me | solution 1 for Formalism.DivisionValues.index_change_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:21:46.83979+00:00
-- url     : https://prove2.me/submissions/54878211-4adc-4d4e-bc4f-e31bd023bfd3

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_det_ne_zero
import Theorems.Thm_Formalism_DivisionValues_idxChange_locS_of_le
import Theorems.Thm_Formalism_DivisionValues_idxChange_hcompl_le_conj
import Theorems.Thm_Formalism_DivisionValues_idxChange_at
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_hcompl_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
open NumberField
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues
theorem _root_.solution : IdxChange := by
  intro K _ _ _ d L _ e he w γ hloc
  obtain ⟨he', hl⟩ := hloc
  have hdet : γ.det ≠ 0 := idxChange_det_ne_zero (e := e) (γ := γ) he'
  unfold loc at hl
  have h1 : localization₂ w.asIdeal (Submodule.span (𝓞 K) (Set.range (idxChangeAct e γ))) =
      localization₂ w.asIdeal L := by
    unfold localization₂
    exact idxChange_locS_of_le (locBasic_hcompl_le (K := K) w.asIdeal) hl
  have h2 : localization₂ (conjPl w).asIdeal (Submodule.span (𝓞 K) (Set.range (idxChangeAct e γ))) =
      localization₂ (conjPl w).asIdeal L := by
    unfold localization₂
    exact idxChange_locS_of_le (idxChange_hcompl_le_conj w) hl
  exact ⟨idxChange_at w L e he γ hdet h1, idxChange_at (conjPl w) L e he γ hdet h2⟩
end Formalism.DivisionValues
