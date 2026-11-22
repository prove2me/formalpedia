-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.hasSubst_binomialSeries_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:32.295877+00:00
-- url     : https://prove2.me/submissions/df6edda7-43d4-4eac-89f9-ea03e817a82b

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors

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
theorem _root_.solution {A : Type*} [CommRing A] [Algebra R A] (e : R) :
    HasSubst (binomialSeries A e - 1 : A⟦X⟧) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero
  change PowerSeries.constantCoeff (binomialSeries A e - 1 : A⟦X⟧) = 0
  simp
end Formalism.CohomologicalDescent.HeightDescentMinors
