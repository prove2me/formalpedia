-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.binomialSeries_subst_sub_one_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:10.722403+00:00
-- url     : https://prove2.me/submissions/6c2d456d-2279-4361-8cbb-fce1eb3be5e1

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_binomialSeries_sub_one
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialSeries_subst_comp
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_binomialSeries_alt

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
namespace Formalism.CohomologicalDescent.HeightDescentMinors
theorem _root_.solution {A : Type*} [CommRing A] [Algebra R A] (d e : R) :
    (binomialSeries A d).subst (binomialSeries A e - 1 : A⟦X⟧) = binomialSeries A (d * e) := by
  have hs := hasSubst_binomialSeries_sub_one (R := R) (A := R) e
  have hm : PowerSeries.map (algebraMap R A) ((binomialSeries R d).subst (binomialSeries R e - 1 : R⟦X⟧)) =
      (PowerSeries.map (algebraMap R A) (binomialSeries R d)).subst
        (PowerSeries.map (algebraMap R A) (binomialSeries R e - 1 : R⟦X⟧)) := by
    first
      | exact PowerSeries.map_subst hs _
      | exact PowerSeries.map_subst hs (algebraMap R A) _
      | exact PowerSeries.map_subst (h := algebraMap R A) hs _
  rw [map_sub, map_one, map_binomialSeries_alt, map_binomialSeries_alt, binomialSeries_subst_comp, map_binomialSeries_alt] at hm
  exact hm.symm
end Formalism.CohomologicalDescent.HeightDescentMinors
