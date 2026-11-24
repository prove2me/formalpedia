-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_colE_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:42.103944+00:00
-- url     : https://prove2.me/submissions/9ffa770e-44d9-4e5b-b9e7-d326daf99629

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) (ε : ℤ) (c : ↥(TCols mu)) (hc : c.1 + 1 ∈ TCols mu)
    (hc' : (qc_colE mu ε c).1 + 1 ∈ TCols (qc_sh mu ε)) :
    qc_colE mu ε ⟨c.1 + 1, hc⟩ = ⟨(qc_colE mu ε c).1 + 1, hc'⟩ :=
  Subtype.ext (by show c.1 + 1 + ε = c.1 + ε + 1; ring)
end Formalism.InvariantFactorPaths.ColumnFamilies
