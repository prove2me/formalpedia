-- Prove2me | solution 1 for Formalism.LIFT.uc_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:03.555185+00:00
-- url     : https://prove2.me/submissions/805dc6cc-6854-49b7-b775-a1c46c8422e5

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
variable {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
  [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D'] [IsScalarTower ℤ_[ℓ] A D']
  {W : WD B M D} {W' : WD B M D'}
namespace Formalism.LIFT
theorem _root_.solution (f : Hom W W') (y z : D) : f.f (W.d1 y z) = W'.d1 (f.f y) (f.f z) := by
  unfold WD.d1
  rw [map_sub, map_sub, map_sub, f.γ_comm, f.φ_comm]
end Formalism.LIFT
