-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_idxE_can
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:51:34.282023+00:00
-- url     : https://prove2.me/submissions/b0c04737-71c6-47e9-801c-833a7ad4062e

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColHSuccLe
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcColESymmVal
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_init_congr

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
theorem _root_.solution (mu : Fin n → ℤ) (ε : ℤ) : qc_idxE mu ε (canT (qc_sh mu ε)) = canT mu := by
  funext c
  apply Subtype.ext
  exact qc_init_congr (qc_colH_sh mu ε c.1) _ _
end Formalism.InvariantFactorPaths.ColumnFamilies
