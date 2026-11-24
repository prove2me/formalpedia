-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.constantCoeff_subst_of_constantCoeff_zero_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:04:59.299984+00:00
-- url     : https://prove2.me/submissions/1bc6aa40-d88c-405d-8277-ab9f1e96fe4b

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_subst_C_eq_C

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
variable {R : Type} [CommRing R]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution {a : R⟦X⟧} (ha : constantCoeff a = 0) (f : R⟦X⟧) :
    constantCoeff (f.subst a) = constantCoeff f := by
  have hs : HasSubst a := by
    first
    | exact HasSubst.of_constantCoeff_zero ha
    | exact PowerSeries.HasSubst.of_constantCoeff_zero ha
    | exact HasSubst.of_constantCoeff_zero' ha
  obtain ⟨g, hg⟩ : X ∣ f - C (constantCoeff f) := by
    rw [X_dvd_iff, map_sub, constantCoeff_C, sub_self]
  have e : f = C (constantCoeff f) + X * g := by
    rw [← hg]; ring
  conv_lhs => rw [e]
  rw [subst_add hs, subst_mul hs, subst_X hs, subst_C_eq_C]
  simp [ha]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
