-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qc_evGL_genPt_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:39:20.410637+00:00
-- url     : https://prove2.me/submissions/3fa8748c-02dc-449f-9093-ac5bdf7d3f58

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLDetUZpow
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QcEvGLGenPtInt
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_genPt_val
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_hom_ext
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qc_evGL_alg


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
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (n : ℕ) : evGL (qc_genPt ℤ n) = RingHom.id _ := by
  apply qc_hom_ext
  intro a b
  rw [qc_evGL_alg]
  simp [qc_genPt_val]
end Formalism.InvariantFactorPaths.ColumnFamilies
