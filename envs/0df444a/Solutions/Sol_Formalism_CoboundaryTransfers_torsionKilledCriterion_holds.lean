-- Prove2me | solution 1 for Formalism.CoboundaryTransfers.torsionKilledCriterion_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:47:16.510111+00:00
-- url     : https://prove2.me/submissions/a362be3f-179a-45b4-b0ae-d35de586ef80

import Definitions.Def_Formalism_CoboundaryTransfers_StatementAPI
import Definitions.Def_Formalism_CoboundaryTransfers_GammaStableTransfers_TorsionKilledCriterionHolds
import Theorems.Thm_Formalism_CoboundaryTransfers_aeval_stable
import Theorems.Thm_P2M_Formalism_CoboundaryTransfers___QInv_fa44b24c21bd
import Theorems.Thm_Formalism_CoboundaryTransfers_claim_key
import Theorems.Thm_Formalism_CoboundaryTransfers_claim_fin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CoboundaryTransfers
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]
namespace Formalism.CoboundaryTransfers
theorem _root_.solution : CoboundaryTransfer := by
  intro O A _ _ _ B M D _ _ _ _ W δ R a k cΓ h1 h1' h2 h3 h4 h5 h6 h7
    ω ⟨w, hw, hωw⟩ ⟨j, y, z, hyz, hj⟩
  subst hωw
  have hk := claim_key W δ R a k cΓ h1 h1' h2 h3 h4 h6 w hw j y z hyz hj
  rw [LinearMap.map_smul] at hk
  have RQ : W.QInv (Polynomial.aeval δ R w) :=
    aeval_stable δ (QS W) (δ_QInv W δ h2) R w hw
  exact claim_fin W δ R a cΓ h2 h6 h7 w hw (h5 _ RQ hk)
end Formalism.CoboundaryTransfers
