-- Prove2me | solution 1 for Formalism.LIFT.uc_xn_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:32:00.275007+00:00
-- url     : https://prove2.me/submissions/6ad0df11-647b-4eaa-b189-50a0b8aeecd7

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
theorem _root_.solution (W : WD B M D) {x y : D} (hx : W.XN x) (hy : W.XN y) : W.XN (x - y) := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨n', hn', rfl⟩ := hy
  exact ⟨n - n', W.N.sub_mem hn hn', by rw [smul_sub]⟩
end Formalism.LIFT
