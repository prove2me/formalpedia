-- Prove2me | solution 1 for Formalism.L2.DIV.fk_gramTw_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:55:29.651233+00:00
-- url     : https://prove2.me/submissions/c06c32ad-71e9-43d7-9fe7-149898e66104

import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkMapInitMinor
import Definitions.Def_Formalism_LocalToGlobal_Columns_CoefficientsModP_FkPderivBlockEmbNe
import Theorems.Thm_Formalism_L2_DIV_fk_det_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open scoped Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
variable {K : Type} [Field K] (K0 : Subfield K)
namespace Formalism.L2.DIV
theorem _root_.solution {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K)
    (hG : ∀ τ a b, G τ a b ∈ K0) : gramTw lam G ∈ K0 := by
  unfold gramTw
  exact prod_mem fun τ _ => zpow_mem (fk_det_mem K0 _ (hG τ)) _
end Formalism.L2.DIV
