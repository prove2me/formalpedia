-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_inputs_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:48.515782+00:00
-- url     : https://prove2.me/submissions/36e13c48-8271-4c80-b9e1-389810678d2d

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_weight_lattice_of_norm

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
theorem _root_.solution : WInputsOfN := by
  intro ι σ l h t n _ O F L _ _ _ _ _ I _ W u c U' wt kap ζ em jj hl2 hN
  obtain ⟨hF, ⟨hζ, hζI, hem, hloc⟩, hNN, hNpsi⟩ := hN
  exact ⟨hF, weight_lattice_of_norm ι l h n O L I ζ em jj W.N u c U' hl2 hF.1.1 hζ hζI hem hloc
      (fun i a => (hF.2.1 i a).1) hNN,
    fun s => weight_lattice_of_norm ι l h 1 O L I ζ em jj (W.Npsi s) u c _ hl2 hF.1.1 hζ hζI hem hloc
      (fun i _ => (hF.2.2.1 i s).1) (hNpsi s)⟩
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
