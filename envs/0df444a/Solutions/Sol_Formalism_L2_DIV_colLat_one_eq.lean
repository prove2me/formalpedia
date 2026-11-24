-- Prove2me | solution 1 for Formalism.L2.DIV.colLat_one_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:58:41.662745+00:00
-- url     : https://prove2.me/submissions/96c83d23-3a88-4de9-abc5-19a1f3ef9a80

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
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.DIV
theorem _root_.solution (B : GL (Fin 1) K) :
    colLat B = Submodule.span (𝓞 K) {fun _ : Fin 1 => (B : Matrix (Fin 1) (Fin 1) K) 0 0} := by
  unfold colLat
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    funext a
    rw [Subsingleton.elim a 0, Subsingleton.elim j 0]
  · rintro rfl
    refine ⟨0, ?_⟩
    funext a
    rw [Subsingleton.elim a 0]
end Formalism.L2.DIV
