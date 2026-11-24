-- Prove2me | solution 1 for Formalism.L2.DIV.blockAct_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:50:24.078382+00:00
-- url     : https://prove2.me/submissions/5352ca26-96de-482c-97ba-f04932c358a2

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
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
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] [StarRing K]
variable {ι : Type} [Fintype ι] {n : ℕ}
omit [StarRing K]
namespace Formalism.L2.DIV
theorem _root_.solution (U : ι → Matrix (Fin n) (Fin n) K) (v : ι × Fin n × Fin n) :
    Formalism.GradedWeylDivisibility.blockAct K U (X v) = ∑ b : Fin n, C (U v.1 v.2.1 b) * X (v.1, (b, v.2.2)) := by
  simp [Formalism.GradedWeylDivisibility.blockAct]
end Formalism.L2.DIV
