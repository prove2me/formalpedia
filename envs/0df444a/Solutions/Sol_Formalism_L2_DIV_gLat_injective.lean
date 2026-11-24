-- Prove2me | solution 1 for Formalism.L2.DIV.gLat_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:00.486921+00:00
-- url     : https://prove2.me/submissions/19607e27-284f-4167-a9a8-4b3f4586408d

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
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
namespace Formalism.L2.DIV
theorem _root_.solution (g : GL (Fin n) K) : Function.Injective (gLat (K := K) g) := by
  refine Submodule.map_injective_of_injective ?_
  intro x y hxy
  have h : (g : Matrix (Fin n) (Fin n) K) *ᵥ x = (g : Matrix (Fin n) (Fin n) K) *ᵥ y := hxy
  have := congrArg (fun z => ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ z) h
  simpa [Matrix.mulVec_mulVec] using this
end Formalism.L2.DIV
