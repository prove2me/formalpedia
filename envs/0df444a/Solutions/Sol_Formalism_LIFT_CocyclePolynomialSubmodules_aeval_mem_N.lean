-- Prove2me | solution 1 for Formalism.LIFT.CocyclePolynomialSubmodules.aeval_mem_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:31:56.44181+00:00
-- url     : https://prove2.me/submissions/61b4e980-9737-43f5-932b-93b80ad2ad55

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_aeval_pres
import Theorems.Thm_P2M_Formalism_LIFT_CocyclePolynomialSubmodules___mem_N_4814b9af5558

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
theorem _root_.solution (p : Polynomial ℤ_[ℓ]) {y : D} (hy : y ∈ W.N) :
    Polynomial.aeval W.γ p y ∈ W.N := aeval_pres W.γ (W.N.restrictScalars ℤ_[ℓ]) (fun _ h => γ_mem_N W h) p y hy
end Formalism.LIFT.CocyclePolynomialSubmodules
