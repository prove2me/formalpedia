-- Prove2me | solution 1 for Formalism.FG.FormalGroupCoefficients.cc_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:23.61173+00:00
-- url     : https://prove2.me/submissions/5bf17020-6361-4542-b9dc-61c1873d9a89

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FunctionalEquationHomVector
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_EqSingleOfDegreeEqOne
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_GroupV
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs

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
theorem _root_.solution {σ τ : Type*} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) {g : MvPowerSeries σ R} (hg : constantCoeff g = 0) :
    constantCoeff (subst a g) = 0 :=
  constantCoeff_subst_eq_zero (hs ha) ha hg
end Formalism.FG.FormalGroupCoefficients
