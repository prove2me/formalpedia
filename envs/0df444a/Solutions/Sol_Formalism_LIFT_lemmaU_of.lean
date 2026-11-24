-- Prove2me | solution 1 for Formalism.LIFT.lemmaU_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:56:36.394255+00:00
-- url     : https://prove2.me/submissions/1fef2f4d-911f-40d3-b875-9113976b8b0f

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
import Theorems.Thm_Formalism_LIFT_uc_cocycle_smul
import Theorems.Thm_Formalism_LIFT_uc_hom_tsmul
import Theorems.Thm_Formalism_LIFT_uc_val_factor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
namespace Formalism.LIFT
theorem _root_.solution (hC : UClaim) (hS : UChase) : LemmaU := by
  intro ℓ _ A _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S e s J hs h2 hv hJ h1 h3 h4 h5 hK hR
  have hT := hC ℓ A B M D₀ W₀ s J hs h2 hv hJ h1 h3 h4 h5
  have hL := hS ℓ A B M D₀ D₁ D₂ W₀ W₁ W₂ S e _ hK hR hT
  obtain ⟨ν, hν⟩ := uc_val_factor ℓ B.u M s J hs h2 hv hJ
  rw [pow_add, hν, ← mul_assoc]
  intro y z hyz
  obtain ⟨y₁, z₁, hc, hy, hz⟩ := hL y z hyz
  refine ⟨ν • y₁, ν • z₁, uc_cocycle_smul W₁ ν hc, ?_, ?_⟩
  · rw [uc_hom_tsmul, hy, smul_smul, mul_comm]
  · rw [uc_hom_tsmul, hz, smul_smul, mul_comm]
end Formalism.LIFT
