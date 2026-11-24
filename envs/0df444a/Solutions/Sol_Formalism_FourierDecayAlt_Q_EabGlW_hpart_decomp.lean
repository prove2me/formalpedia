-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.EabGlW.hpart_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:47:45.580898+00:00
-- url     : https://prove2.me/submissions/f5cb8364-a875-4a24-9bd3-22939974b453

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
theorem _root_.solution (Z : Mx k r) : Z = hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z := by
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    have := Complex.I_ne_zero
    field_simp
    try ring
  unfold hpart1 hpart2
  rw [smul_smul, hI]
  module
end Formalism.FourierDecayAlt.Q.EabGlW
