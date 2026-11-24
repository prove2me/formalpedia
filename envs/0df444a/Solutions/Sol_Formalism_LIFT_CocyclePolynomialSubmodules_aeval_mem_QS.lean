-- Prove2me | solution 1 for Formalism.LIFT.CocyclePolynomialSubmodules.aeval_mem_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:57.10781+00:00
-- url     : https://prove2.me/submissions/e93ab9eb-9a61-4b2a-963d-9d155c273c66

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_aeval_pres
import Theorems.Thm_P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_QS_a25536efd750

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
theorem _root_.solution (p : Polynomial ℤ_[ℓ]) {y : D} (hy : y ∈ QS W) :
    Polynomial.aeval W.γ p y ∈ QS W := aeval_pres W.γ ((QS W).restrictScalars ℤ_[ℓ]) (fun _ h => γ_mem_QS W h) p y hy
end Formalism.LIFT.CocyclePolynomialSubmodules
