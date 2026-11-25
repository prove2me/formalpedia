-- Prove2me | solution 1 for Formalism.DivisionValues.lattice_gluing_semilocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:23:09.497221+00:00
-- url     : https://prove2.me/submissions/a30e3dca-b3ea-4f48-8dc3-7e453f8d844e

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_glueLat_spec
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_eq_of_localization_eq
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_loc_eq
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_loc_glueLat
import Theorems.Thm_Formalism_DivisionValues_StepBAux_localization_eq_and_conj_eq_of_semilocalization_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open GluingInclusion Formalism.HermitianLatticesTheory
namespace Formalism.DivisionValues
theorem _root_.solution : LatticeGlueSemi := by
  intro K _ _ _ D
  refine ⟨?_, ?_⟩
  · intro L0 L h0 hL hc hfin
    obtain ⟨hlat, hloc⟩ := glueLat_spec L0 L h0 hL (hfin.subset (fun w hw h => hw
      (StepBAux.localization_eq_and_conj_eq_of_semilocalization_eq w _ _ h).1))
    refine ⟨hlat, loc_glueLat L hc _ hloc, ?_⟩
    apply le_antisymm
    · refine le_iInf (fun w => ?_)
      rw [loc_eq]
      refine le_inf (iInf_le _ w) ?_
      have h := iInf_le (fun w : HeightOneSpectrum (𝓞 K) => localization₂ w.asIdeal (L w)) (conjPl w)
      rw [hc w] at h
      exact h
    · refine le_iInf (fun w => le_trans (iInf_le _ w) ?_)
      rw [loc_eq]
      exact inf_le_left
  · intro R R' h
    exact eq_of_localization_eq R R' (fun w => (StepBAux.localization_eq_and_conj_eq_of_semilocalization_eq w _ _ (h w)).1)
end Formalism.DivisionValues
