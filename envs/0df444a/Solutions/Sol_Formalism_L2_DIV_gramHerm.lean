-- Prove2me | solution 1 for Formalism.L2.DIV.gramHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:41:52.45657+00:00
-- url     : https://prove2.me/submissions/8fd0dbfb-93ab-4f9d-b1db-55504009f70a

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_L2_DIV_map_conjTranspose_eq
import Theorems.Thm_P2M_Formalism_L2_DIV_conjTranspose_transpose__09b67af54be3

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : GramHerm := by
  intro E K _ _ _ ι n emb cE τ h J hJ
  have h1 : (gramK emb J τ)ᴴ = gramK emb J τ := by
    unfold gramK
    rw [map_conjTranspose_eq (emb τ) cE h, hJ]
  refine ⟨h1, ?_⟩
  unfold gramKd
  unfold gramK at h1
  rw [conjTranspose_transpose', Matrix.conjTranspose_nonsing_inv, h1]
end Formalism.L2.DIV
