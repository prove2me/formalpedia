-- Prove2me | solution 1 for Formalism.LIFT.uc_cocycle_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:02.021034+00:00
-- url     : https://prove2.me/submissions/b0e3f9ed-7e5f-4a4f-ab59-7d1193fd8657

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
import Theorems.Thm_Formalism_LIFT_uc_qinv_smul
import Theorems.Thm_Formalism_LIFT_uc_smul
import Theorems.Thm_Formalism_LIFT_uc_xn_smul

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
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
namespace Formalism.LIFT
theorem _root_.solution (W : WD B M D) (r : ℤ_[ℓ]) {y z : D} (h : W.Cocycle y z) :
    W.Cocycle (r • y) (r • z) := by
  obtain ⟨⟨hq, hx⟩, hd⟩ := h
  exact ⟨⟨uc_qinv_smul W r hq, uc_xn_smul W r hx⟩, by rw [uc_smul, hd, smul_zero]⟩
end Formalism.LIFT
