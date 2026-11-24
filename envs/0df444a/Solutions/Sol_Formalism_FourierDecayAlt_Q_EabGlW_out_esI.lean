-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.out_esI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:48:03.020004+00:00
-- url     : https://prove2.me/submissions/4db99e1a-efdd-4554-959c-0050c7fee92e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_ExpMulVecFix
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FormalDegreeBessel_FinalIO
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GeneralLinearLevel_HpartUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.EabGlW
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.EabGlW
theorem _root_.solution {i : Fin (r + 1)} (a : Fin r) (ha : a.val < i.val) : Out k r i (esI k r a) := by
  have := i.isLt
  have := a.isLt
  right
  show 2 * r + k - i.val < 2 * r + k - a.val
  omega
end Formalism.FourierDecayAlt.Q.EabGlW
