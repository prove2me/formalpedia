-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_properties_of_inputs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:37:52.679084+00:00
-- url     : https://prove2.me/submissions/f7c15a6e-d01a-493e-99de-93248cbed3f5

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_reduction_algebraMap_unit_ne_zero
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_charpoly_theta_eq_prod
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_minorsDvd_frobenius_of_sum_bound
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_frobenius_diagonal_entry_eq_unit_mul
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_theta_diagonal_entry_eq
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_minors_divide_all_holds


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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : WPropsOfInputs := by
  intro ι _ σ l h t n _ O F _ _ _ _ _ W u c U' bot kap cc hl2 hW hcc
  have hW' := hW
  obtain ⟨⟨⟨hu, hc, hun⟩, hU, hwt, ⟨hinj, hpos⟩, hΦ, hΓ, hcφ, hcγ⟩, hN, hψ⟩ := hW'
  refine ⟨reduction_algebraMap_unit_ne_zero l W.red c hc, hinj, hpos, ?_, ?_, ?_, hΦ, ?_, ?_⟩
  · intro i a b hab
    change coeff 1 (W.Gam i a b) = 0
    rw [hΓ i hab, map_zero]
  · intro i
    exact charpoly_theta_eq_prod l h W u c U' hu hN i
  · intro i s
    exact theta_diagonal_entry_eq l h W σ u c U' _ kap hl2 hW i s
  · intro i s
    exact (frobenius_diagonal_entry_eq_unit_mul l h W σ u c U' _ kap hW i s).2
  · intro i
    exact (minors_divide_all_holds (F⟦X⟧) n n t _ _).1
      (minorsDvd_frobenius_of_sum_bound l h W σ u U' hN i t (cc i) (hcc i)) W.pos W.pos
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
