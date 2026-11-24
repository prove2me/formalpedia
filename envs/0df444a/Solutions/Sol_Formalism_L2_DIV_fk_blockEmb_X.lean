-- Prove2me | solution 1 for Formalism.L2.DIV.fk_blockEmb_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:46.59773+00:00
-- url     : https://prove2.me/submissions/71b88b18-5060-4874-9cbd-f5c42564d59e

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K] {ι : Type} {n : ℕ}
omit [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution (τ : ι) (v : Fin n × Fin n) :
    Formalism.GradedWeylDivisibility.blockEmb K τ (X v) = (X (τ, v) : MvPolynomial (ι × Fin n × Fin n) K) := by
  simp [Formalism.GradedWeylDivisibility.blockEmb]
end Formalism.L2.DIV
