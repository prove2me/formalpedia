-- Prove2me | solution 1 for Formalism.QuantumDeterminants.BesselUnipotentEquiv.coe_lmulEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:12:43.527437+00:00
-- url     : https://prove2.me/submissions/7c7dc01c-16b8-43de-93b3-b2822c9b6509

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
theorem _root_.solution (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ha : IsUnit a.det) :
    ⇑(lmulEquiv (k := k) (r := r) a ha) = lmulM a := rfl
end Formalism.QuantumDeterminants.BesselUnipotentEquiv
