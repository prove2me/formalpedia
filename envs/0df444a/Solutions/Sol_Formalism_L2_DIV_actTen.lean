-- Prove2me | solution 1 for Formalism.L2.DIV.actTen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:04:42.539676+00:00
-- url     : https://prove2.me/submissions/413f8488-a3d2-490d-8099-438c341b371c

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_blockActTensor
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
theorem _root_.solution : ActTen := by
  intro K _ ι _ n lam g f
  have h1 : ∀ τ, trAct g (Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) =
      Formalism.GradedWeylDivisibility.blockEmb K τ (Formalism.GradedWeylDivisibility.rowAct K ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ (f τ)) :=
    fun τ => (Formalism.GradedWeylDivisibility.blockActTensor K K ι n n _).1 τ (f τ)
  simp only [actP, ten, LinearMap.smul_apply, AlgHom.toLinearMap_apply, map_prod, h1, sqAct, detTwK,
    smul_eq_C_mul]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_mul]
  simp only [Formalism.GradedWeylDivisibility.blockEmb, rename_C]
end Formalism.L2.DIV
