-- Prove2me | solution 1 for Formalism.CohomologicalDescent.HeightDescentMinors.map_binomialSeries_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:29:38.023914+00:00
-- url     : https://prove2.me/submissions/6a72c97e-703e-4cf2-97f1-d15ef0044a9c

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
theorem _root_.solution {A : Type*} [CommRing A] [Algebra R A] (c : R) :
    PowerSeries.map (algebraMap R A) (binomialSeries R c) = binomialSeries A c := by
  ext n
  first
    | simp [PowerSeries.binomialSeries_coeff, Algebra.smul_def]
    | simp [PowerSeries.binomialSeries, Algebra.smul_def]
    | simp [PowerSeries.binomialSeries]
end Formalism.CohomologicalDescent.HeightDescentMinors
