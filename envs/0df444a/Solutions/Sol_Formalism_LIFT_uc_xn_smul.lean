-- Prove2me | solution 1 for Formalism.LIFT.uc_xn_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:22.185536+00:00
-- url     : https://prove2.me/submissions/9d3c84d3-6754-49f2-bd76-2baef3158908

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
import Theorems.Thm_Formalism_LIFT_uc_smul_comm_A

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
theorem _root_.solution (W : WD B M D) (r : ℤ_[ℓ]) {x : D} (hx : W.XN x) : W.XN (r • x) := by
  obtain ⟨n, hn, rfl⟩ := hx
  refine ⟨r • n, ?_, ?_⟩
  · rw [← algebraMap_smul A r n]
    exact W.N.smul_mem _ hn
  · rw [← algebraMap_smul A r, ← algebraMap_smul A r n, uc_smul_comm_A]
end Formalism.LIFT
