-- Prove2me | solution 1 for Formalism.LIFT.uc_qinv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:31:57.96166+00:00
-- url     : https://prove2.me/submissions/2a6b576f-d7eb-4034-b013-a3c1fed437fa

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
theorem _root_.solution (W : WD B M D) {x y : D} (hx : W.QInv x) (hy : W.QInv y) : W.QInv (x + y) := by
  unfold WD.QInv at *
  rw [smul_add]
  exact W.N.add_mem hx hy
end Formalism.LIFT
