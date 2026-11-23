-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.sixth_relation_of_action_and_mu_laws
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:21.272803+00:00
-- url     : https://prove2.me/submissions/bcfa7a27-773a-4e93-837d-d6d3bcb7ea45

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_algHom_C_eq
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_algHom_inc_pi0
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_algHom_act
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_pi0_padicInt_algebraMap
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_q0_padic_alt
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_act_padic
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_algebraMap_pi0Subst
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_act_unit_pi0_eq_mul_padic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (ha : ActLaws) (hm : MuFacts) (hq : QMul) (hi : DivisibilityInvariant) (hf : RootsOfUnityInvariants)
    (h4 : R4) : R6 := by
  intro l _ O _ _ hl u c hu
  obtain ⟨unZ, hA, e, he⟩ := act_unit_pi0_eq_mul_padic ha hm hq hi hf h4 l hl u c hu
  have H1 : act l O u (pi0 l O) =
      pi0 l O * (1 + inc l O (PowerSeries.map (algebraMap ℤ_[l] O) unZ) * q0 l O) := by
    have h0 := congrArg (PowerSeries.map (algebraMap ℤ_[l] O)) hA
    rw [map_act_padic, map_mul, map_add, map_one, map_mul, map_algebraMap_pi0Subst l O hm,
      map_q0_padic_alt, map_pi0_padicInt_algebraMap] at h0
    exact h0
  refine ⟨PowerSeries.map (algebraMap ℤ_[l] O) unZ, H1, ⟨algebraMap ℤ_[l] O e, ?_⟩, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, he,
      map_add, map_mul, map_natCast]
  · obtain ⟨Ψ, hΨ⟩ := exists_algHom_act l O u
    obtain ⟨Φ, hΦ, hΦX⟩ := exists_algHom_inc_pi0 l O hm
    have h0 : act l O u (q0 l O) = act l O u (pi0 l O) - C (l : O) := by
      rw [hΨ, q0, map_sub, algHom_C_eq, ← hΨ]
    rw [h0, H1, hΦ (1 + X * _), map_add, map_one, map_mul, hΦX, ← hΦ, q0]
    ring
  · exact isUnit_iff_constantCoeff.mpr (by simp)
end Formalism.CohomologicalDescent.HeightDescentMinors
