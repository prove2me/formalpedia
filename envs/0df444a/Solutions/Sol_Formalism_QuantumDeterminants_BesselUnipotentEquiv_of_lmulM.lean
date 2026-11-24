-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BesselUnipotentEquiv.of_lmulM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:44.765901+00:00
-- url     : https://prove2.me/submissions/7b676708-f350-48fd-835c-170651c43dc3

import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_BesselUnipotentEquivHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.BesselUnipotentEquiv
variable {k r : ℕ}
namespace Formalism.QuantumDeterminants.BesselUnipotentEquiv
theorem _root_.solution (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) :
    Matrix.of (lmulM a x) = a * Matrix.of x := rfl
end Formalism.QuantumDeterminants.BesselUnipotentEquiv
