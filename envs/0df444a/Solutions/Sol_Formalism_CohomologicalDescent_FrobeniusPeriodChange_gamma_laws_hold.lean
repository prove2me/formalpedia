-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamma_laws_hold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:16:07.6336+00:00
-- url     : https://prove2.me/submissions/55f77c70-8459-47ef-b27f-6dc619bad727

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_subst_C_eq_C
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_constantCoeff_subst_of_constantCoeff_zero_alt
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_constantCoeff_gammaSeries
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_hasSubst_gammaSeries

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
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : GamLaws := by
  intro R _ lam un
  have hs : HasSubst (gamSer lam un) := hasSubst_gammaSeries lam un
  have hc : constantCoeff (gamSer lam un) = 0 := constantCoeff_gammaSeries lam un
  have hadd : ∀ f g : R⟦X⟧, gam0 lam un (f + g) = gam0 lam un f + gam0 lam un g := by
    intro f g; exact subst_add hs f g
  have hmul : ∀ f g : R⟦X⟧, gam0 lam un (f * g) = gam0 lam un f * gam0 lam un g := by
    intro f g; exact subst_mul hs f g
  have hC : ∀ a : R, gam0 lam un (C a) = C a := fun a => subst_C_eq_C a
  have hX : gam0 lam un X = X * (1 + un * (X - C lam)) := subst_X hs
  have hcc : ∀ y : R⟦X⟧, constantCoeff (gam0 lam un y) = constantCoeff y :=
    fun y => constantCoeff_subst_of_constantCoeff_zero_alt hc y
  refine ⟨hadd, hmul, hC, ?_, hX, ?_, hcc⟩
  · intro y; rw [X_dvd_iff, map_sub, hcc, sub_self]
  · have e : (X : R⟦X⟧) - C lam = X + C (-lam) := by rw [map_neg, sub_eq_add_neg]
    rw [e, hadd, hC, hX, map_neg]; ring
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
