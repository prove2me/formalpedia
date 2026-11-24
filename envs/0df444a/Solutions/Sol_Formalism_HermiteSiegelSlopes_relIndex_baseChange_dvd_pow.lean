-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.relIndex_baseChange_dvd_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:25.553402+00:00
-- url     : https://prove2.me/submissions/49177ffc-a97a-443d-82f8-d17e0841b66d

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_relIndex_baseChange_dvd_pow_finset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution {A B : Submodule (𝓞 F) (ι → F)} (hAB : A ≤ B) (hB : B.FG) :
    (bcLat (E := E) A).toAddSubgroup.relIndex (bcLat (E := E) B).toAddSubgroup ∣
      (A.toAddSubgroup.relIndex B.toAddSubgroup) ^ finrank F E := by
  obtain ⟨s, rfl⟩ := hB
  have h := relIndex_baseChange_dvd_pow_finset (E := E) A s
  rwa [sup_eq_right.2 hAB] at h
end Formalism.HermiteSiegelSlopes
