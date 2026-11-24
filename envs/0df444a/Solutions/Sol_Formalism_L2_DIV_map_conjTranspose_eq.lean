-- Prove2me | solution 1 for Formalism.L2.DIV.map_conjTranspose_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:13.472691+00:00
-- url     : https://prove2.me/submissions/abdb4de7-3a65-463b-af5b-8c342b61c615

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
namespace Formalism.L2.DIV
theorem _root_.solution {E K : Type} [Field E] [Field K] [StarRing K] {n : ℕ} (φ : E →+* K) (cE : E →+* E)
    (h : ∀ x, star (φ x) = φ (cE x)) (A : Matrix (Fin n) (Fin n) E) : (A.map φ)ᴴ = (Formalism.UG.cT cE A).map φ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply, h]
end Formalism.L2.DIV
