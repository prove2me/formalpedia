-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.binomialSeries_subst_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:24.000162+00:00
-- url     : https://prove2.me/submissions/ee7b4d23-e012-49d9-8b83-389e88bf1109

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_of_binomial_ode_of_constantCoeff_eq
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialSeries_one_add_X_mul_derivative
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_binomialSeries_sub_one

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
variable {R : Type*} [CommRing R]
variable [BinomialRing R]
attribute [local instance] BinomialRing.toIsAddTorsionFree
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution (d e : R) :
    (binomialSeries R d).subst (binomialSeries R e - 1 : R⟦X⟧) = binomialSeries R (d * e) := by
  have ha := hasSubst_binomialSeries_sub_one (A := R) e
  set a : R⟦X⟧ := binomialSeries R e - 1 with hadef
  have hFe : (1 + X : R⟦X⟧).subst a = binomialSeries R e := by
    rw [subst_add ha, subst_X ha, ← map_one (C (R := R)), subst_C]
    simp [hadef]
  have hda : d⁄dX R a = d⁄dX R (binomialSeries R e) := by
    rw [hadef, map_sub, derivative_one, sub_zero]
  apply eq_of_binomial_ode_of_constantCoeff_eq (d * e)
  · rw [derivative_subst ha, hda]
    calc (1 + X) * ((d⁄dX R (binomialSeries R d)).subst a * d⁄dX R (binomialSeries R e))
        = (d⁄dX R (binomialSeries R d)).subst a * ((1 + X) * d⁄dX R (binomialSeries R e)) := by ring
      _ = (d⁄dX R (binomialSeries R d)).subst a * (C e * (1 + X : R⟦X⟧).subst a) := by
          rw [binomialSeries_one_add_X_mul_derivative, hFe]
      _ = C e * ((1 + X) * d⁄dX R (binomialSeries R d)).subst a := by
          rw [subst_mul ha]; ring
      _ = C e * (C d * (binomialSeries R d).subst a) := by
          rw [binomialSeries_one_add_X_mul_derivative, subst_mul ha, subst_C]; rfl
      _ = C (d * e) * (binomialSeries R d).subst a := by
          rw [map_mul]; ring
  · exact binomialSeries_one_add_X_mul_derivative _
  · have h1 : binomialSeries R d = 1 + (binomialSeries R d - 1) := by ring
    rw [h1, subst_add ha, ← map_one (C (R := R)), subst_C, map_add]
    have h2 : constantCoeff ((binomialSeries R d - C 1 : R⟦X⟧).subst a) = 0 :=
      constantCoeff_subst_eq_zero
        (show constantCoeff a = 0 by rw [hadef]; simp) _ (by simp)
    rw [h2]
    simp
end Formalism.CohomologicalDescent.HeightDescentMinors
