-- Prove2me | solution 1 for Formalism.LIFT.uc_hom_xn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:05.423047+00:00
-- url     : https://prove2.me/submissions/1ba20787-545e-4a29-acb5-fc951e2e28b6

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
theorem _root_.solution (f : Hom W W') {x : D} (hx : W.XN x) : W'.XN (f.f x) := by
  obtain ⟨n, hn, rfl⟩ := hx
  exact ⟨f.f n, f.N_le n hn, map_smul _ _ _⟩
end Formalism.LIFT
