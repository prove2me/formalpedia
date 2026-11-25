-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.map_smul_one_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:24:34.70517+00:00
-- url     : https://prove2.me/submissions/df2e7c59-a712-4098-a703-442a350509b8

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct

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
theorem _root_.solution {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (x : R) :
    ((x • (1 : Matrix (Fin n) (Fin n) R))).map f = f x • (1 : Matrix (Fin n) (Fin n) S) := by
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
