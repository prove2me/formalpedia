-- Prove2me | solution 1 for Formalism.LIFT.uc_qinv_phi_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:31:58.650022+00:00
-- url     : https://prove2.me/submissions/848d304b-914e-4da8-b280-1178e4d29c3b

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase

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
theorem _root_.solution (W : WD B M D) {x : D} (hx : x ∈ W.N) : W.QInv (W.φ x - x) := by
  unfold WD.QInv
  rw [smul_sub]
  exact W.N.sub_mem (W.φ_N x hx) (W.N.smul_mem _ hx)
end Formalism.LIFT
