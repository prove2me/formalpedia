-- Prove2me | solution 1 for Formalism.L2.DIV.bVV_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:55:48.82133+00:00
-- url     : https://prove2.me/submissions/f68f088e-f014-4f96-a111-58cd3cbcde35

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
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
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (K : Type) [Field K] (lam : ι → DomWeight n) (i : VVIdx lam) :
    ((bVV K lam i : VV K lam) : Pol K ι n) = bVVfun K lam i := by
  simp [bVV, Module.Basis.span_apply]
end Formalism.L2.DIV
