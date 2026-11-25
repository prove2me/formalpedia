-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_exponents_from_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:51:37.788736+00:00
-- url     : https://prove2.me/submissions/75d78f00-b23b-412a-982d-794e60ee690f

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_weight_exponents_from_inputs
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_weight_inputs_of_norm

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
theorem _root_.solution : WEFromLattice := by
  intro ι _ σ k j t q l h _ O F L _ _ _ _ _ _ I _ W u c U U' bot cst kap τ ζ em jj hl2 hlt hN
  exact weight_exponents_from_inputs ι σ k j t q l h O F W u c U U' bot cst kap τ hl2 hlt
    (weight_inputs_of_norm ι σ l h t (k + j + t + q) O F L I W u c U'
      (fun i s => bot i + ((s : ℕ) : ℤ)) kap ζ em jj hl2 hN)
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
