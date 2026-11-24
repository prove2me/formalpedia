-- Prove2me | solution 1 for Formalism.FourierDecayAlt.Q.TPresLie.hpk_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:47:27.697844+00:00
-- url     : https://prove2.me/submissions/0604f056-e0af-4f4e-a3c2-411de06aff75

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_HasDerivAtExt
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_sq


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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.TPresLie
open Formalism.REAL Formalism.QuantumDeterminants Formalism.QuantumDeterminants.GBasic Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.Q.TPresLie
theorem _root_.solution : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv (Hpk_sq k r)
end Formalism.FourierDecayAlt.Q.TPresLie
