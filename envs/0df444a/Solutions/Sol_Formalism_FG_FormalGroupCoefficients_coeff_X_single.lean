-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.coeff_X_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:23.828775+00:00
-- url     : https://prove2.me/submissions/8e290411-ee0b-47b7-b8e6-3d8a019c6c13

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v
open Formalism Formalism.FG Formalism.FG.FormalGroupCoefficients
open MvPowerSeries Formalism.G Formalism.LT
variable {R : Type u} [CommRing R]
namespace Formalism.FG.FormalGroupCoefficients
theorem _root_.solution {σ : Type*} [DecidableEq σ] (i j : σ) :
    coeff (Finsupp.single i 1) (X j : MvPowerSeries σ R) = if i = j then 1 else 0 := by
  rw [coeff_X]
  by_cases h : i = j
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (Finsupp.single_left_injective one_ne_zero h')
end Formalism.FG.FormalGroupCoefficients
