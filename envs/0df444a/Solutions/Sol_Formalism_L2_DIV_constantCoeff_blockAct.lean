-- Prove2me | solution 1 for Formalism.L2.DIV.constantCoeff_blockAct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.557306+00:00
-- url     : https://prove2.me/submissions/18d5518b-f6af-450e-abdc-b23c298420fa

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_blockAct_X
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
theorem _root_.solution (U : ι → Matrix (Fin n) (Fin n) K) (g : Pol K ι n) :
    constantCoeff (Formalism.GradedWeylDivisibility.blockAct K U g) = constantCoeff g := by
  have : (constantCoeff : Pol K ι n →+* K).comp (Formalism.GradedWeylDivisibility.blockAct K U).toRingHom = constantCoeff := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp
    · intro i; simp [blockAct_X]
  exact congrArg (fun φ : Pol K ι n →+* K => φ g) this
end Formalism.L2.DIV
