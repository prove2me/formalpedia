-- Prove2me | solution 1 for Formalism.LIFT.CocyclePolynomialSubmodules.N_le_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:55.652827+00:00
-- url     : https://prove2.me/submissions/1bf7ebcc-d784-42d3-8a65-d94b1129a07d

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_mem_QS

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
open Formalism.LIFT.CocyclePolynomialSubmodules
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)
namespace Formalism.LIFT.CocyclePolynomialSubmodules
theorem _root_.solution : W.N ≤ QS W := by
  intro y hy
  refine (mem_QS W).mpr ?_
  unfold WD.QInv
  exact W.N.smul_mem _ hy
end Formalism.LIFT.CocyclePolynomialSubmodules
