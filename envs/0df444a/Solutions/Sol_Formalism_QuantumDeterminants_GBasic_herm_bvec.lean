-- Prove2me | solution 1 for Formalism.QuantumDeterminants.GBasic.herm_bvec
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:46.359127+00:00
-- url     : https://prove2.me/submissions/8e8093d2-abd6-4c70-9b70-60d92a03a30d

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.QuantumDeterminants.GBasic
namespace Formalism.QuantumDeterminants.GBasic
theorem _root_.solution (k r : ℕ) (x y : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec x) (bvec y) = Hpk k r y x := by
  simp [herm, bvec, Matrix.mulVec, dotProduct, Pi.single_apply]
end Formalism.QuantumDeterminants.GBasic
