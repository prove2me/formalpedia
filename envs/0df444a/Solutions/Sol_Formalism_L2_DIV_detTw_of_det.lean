-- Prove2me | solution 1 for Formalism.L2.DIV.detTw_of_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:11.934029+00:00
-- url     : https://prove2.me/submissions/ce34137c-ee0a-4c4b-b00a-bdbc854b5f4e

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Theorems.Thm_Formalism_L2_DIV_tilde_norm_quotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution (σ : E →ₐ[F] E) (ξ : Chr F E L) (h : (h90 σ).ker ≤ ξ.ker) {n : ℕ}
    (g : GL (Fin n) (AfE F E)) (x : (AfE F E)ˣ) (hx : h90 σ x = Matrix.GeneralLinearGroup.det g) :
    detTw σ ξ g = ξ x := by
  have hm : Matrix.GeneralLinearGroup.det g ∈ (h90 σ).range := ⟨x, hx⟩
  rw [detTw, dif_pos hm, ← tilde_norm_quotient σ ξ h x]
  congr 1
  exact Subtype.ext hx.symm
end Formalism.L2.DIV
