-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.r1_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:15.127583+00:00
-- url     : https://prove2.me/submissions/1d8c3f25-1a4d-4fd1-b147-b24a5baf1a92

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_card_mu_eq_sub_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prod_roots_unity_eq_neg_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_br_eq_X_mul_shift
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_one_br

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
variable (l : ℕ) [Fact l.Prime]
variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution : R1 := by
  intro l _ O _ _ hl
  set w : O⟦X⟧ := ∏ d ∈ mu l, PowerSeries.mk (fun n => coeff (n + 1) (br l O d)) with hw
  have hcc : constantCoeff w = -1 := by
    rw [hw, map_prod]
    have : ∀ d ∈ mu l, constantCoeff (PowerSeries.mk (fun n => coeff (n + 1) (br l O d))) =
        algebraMap ℤ_[l] O d := by
      intro d _
      rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk, zero_add, coeff_one_br]
    rw [Finset.prod_congr rfl this, ← map_prod, prod_roots_unity_eq_neg_one l hl, map_neg, map_one]
  have hu : IsUnit w := by
    rw [isUnit_iff_constantCoeff, hcc]
    exact isUnit_one.neg
  obtain ⟨w', hw'⟩ := hu
  refine ⟨w', ?_, by rw [hw', hcc]⟩
  rw [hw', pi0, Finset.prod_congr rfl (fun d _ => br_eq_X_mul_shift l O d), Finset.prod_mul_distrib,
    Finset.prod_const, card_mu_eq_sub_one, mul_comm]
end Formalism.CohomologicalDescent.HeightDescentMinors
