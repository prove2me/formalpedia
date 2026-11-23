-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.cc_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:23.226509+00:00
-- url     : https://prove2.me/submissions/f1011d50-3e3c-439e-bf0e-d6282f083683

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
theorem _root_.solution {σ : Type*} (g : MvPowerSeries σ R) (i : σ) :
    constantCoeff (pderiv R i g) = coeff (Finsupp.single i 1) g := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simp
end Formalism.FG.FormalGroupCoefficients
