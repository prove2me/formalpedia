-- Prove2me | solution 1 for Formalism.L2.DIV.fk_pderiv_blockEmb_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.591874+00:00
-- url     : https://prove2.me/submissions/09ed1276-f3ac-42b5-af1e-1b92325c80ca

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
theorem _root_.solution {τ τ' : ι} (h : τ ≠ τ') (v : Fin n × Fin n) (g : MvPolynomial (Fin n × Fin n) K) :
    pderiv (τ, v) (Formalism.GradedWeylDivisibility.blockEmb K τ' g) = 0 := by
  classical
  unfold Formalism.GradedWeylDivisibility.blockEmb
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp => simp [Derivation.leibniz, hp, pderiv_X, Pi.single_apply, Prod.ext_iff, Ne.symm h]
end Formalism.L2.DIV
